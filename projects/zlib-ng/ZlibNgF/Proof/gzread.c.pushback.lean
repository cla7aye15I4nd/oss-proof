import ZlibNgF.Proof.«gzread.c.getc»
import ZlibNgF.Proof.«gzread.c.idlespec»

/-!
# `gzungetc` on a read handle (`ZlibNgF`)

`gzungetc` first calls `gz_look` when it is looking with no output (to learn the kind of input before bytes are
pushed), then stops on a pending error, does a pending skip (`gz_skip`) and pushes `c` in front of the output: at the
end of `out` when there is no output, after sliding the output to the end of `out` when it starts at `out`, else just
before `x.next`. With patch 0023 a push at `x.pos <= -GZ_OFF_MAX` is refused, so `x.pos - 1` does not overflow and
`x.pos` stays at or above `-GZ_OFF_MAX`. A push keeps `x.pos + x.have` (and `x.pos + skip + x.have`), so the position
clauses of a read handle stay true; every pointer it forms lies inside `[out, out + 2 * size]`.

`gzungetc` keeps the read invariant with `LookIdle` (`ungetc_keepsRI`), given the specification of `gz_skip`
(`GzSkipSpec`) and that `gz_skip` keeps `LookIdle` (`GzSkipIdle`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzDecomp
open ZlibNg.Inflate (Z_OK Z_BUF_ERROR Z_DATA_ERROR)

/-! ## The parts of `gzungetc` -/

/-- The end of a push: store `c` at `nx`, the new `x.next` (copied from the translation). -/
def pushEnd (c : Int32) (state : GzPtr) (nx : BPtr) : G Int32 := do
  wrG state fun s => { s with next := .val nx }
  lm (store8 (← lm ((← (← ldGz state).next.get).add 0)) c.toUInt32.toUInt8)
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt - 1))
  wrG state fun s => { s with pos := np }
  wrG state fun s => { s with past := 0 }
  return c

/-- A push in front of output that does not start at `out` (copied from the translation). -/
def ungetcEnd (c : Int32) (state : GzPtr) : G Int32 := do
  wrG state fun s => { s with «have» := s.«have» + 1 }
  let nx ← lm ((← (← ldGz state).next.get).add (-1))
  pushEnd c state nx

/-- The push of `gzungetc` after the bound checks (copied from the translation, with the code after the slide written
out in both branches; `gzungetc_eq` checks it). -/
def ungetcPush (c : Int32) (state : GzPtr) : G Int32 := do
  if (← rdG state (·.«have»)) == 0 then
    wrG state fun s => { s with «have» := 1 }
    let e ← lm ((← (← ldGz state).out.get).add (Int.ofNat ((← rdG state (·.size)) <<< 1).toNat))
    let nx ← lm (e.add (-1))
    pushEnd c state nx
  else
  if (← rdG state (·.«have»)) == ((← rdG state (·.size)) <<< 1) then
    gz_error state Z_DATA_ERROR (← (gzLit "out of room to push characters"))
    return -1
  if (← (← ldGz state).next.get) == (← (← ldGz state).out.get) then
    let src ← lm ((← (← ldGz state).out.get).add (Int.ofNat (← rdG state (·.«have»)).toNat))
    let dest ← lm ((← (← ldGz state).out.get).add (Int.ofNat ((← rdG state (·.size)) <<< 1).toNat))
    let lp ← gwhile (slideCond state) slideBody ⟨src, dest⟩
    wrG state fun s => { s with next := .val lp.dest }
    ungetcEnd c state
  else
    ungetcEnd c state

/-- `gzungetc` after the pending skip (copied from the translation). -/
def ungetcRest (c : Int32) (state : GzPtr) : G Int32 := do
  if c < 0 then
    return -1
  if (← rdG state (·.pos)) ≤ -GZ_OFF_MAX then
    return -1
  ungetcPush c state

/-- `gzungetc` after `gz_look` (copied from the translation, with the code after the skip written out in both
branches; `gzungetc_eq` checks it). -/
def ungetcTail (c : Int32) (state : GzPtr) : G Int32 := do
  if (← rdG state (·.mode)) != GZ_READ ||
      ((← rdG state (·.err)) != Z_OK && (← rdG state (·.err)) != Z_BUF_ERROR) then
    return -1
  if (← rdG state (·.skip)) != 0 then
    if (← gz_skip state) == -1 then
      return -1
    ungetcRest c state
  else
    ungetcRest c state

/-- `gzungetc` is its parts (by `rfl`). -/
theorem gzungetc_eq (c : Int32) (b : Nat) : gzungetc c (some b) = (do
    if (← rdG (some b) (·.mode)) == GZ_READ then
      if (← rdG (some b) (·.how)) == LOOK then
        if (← rdG (some b) (·.«have»)) == 0 then
          let _ ← gz_look (some b)
          ungetcTail c (some b)
        else ungetcTail c (some b)
      else ungetcTail c (some b)
    else ungetcTail c (some b)) := rfl

/-! ## Arithmetic and small facts -/

theorem shl1_toNat (x : UInt32) (hx : x.toNat < 2 ^ 31) : (x <<< 1).toNat = 2 * x.toNat := by
  rw [UInt32.toNat_shiftLeft]
  simp [Nat.shiftLeft_eq]
  omega

theorem lit_room : gzLits.findIdx? (· == "out of room to push characters") = some 7 := by
  simp [gzLits, List.findIdx?_cons]

theorem neg_max : (-GZ_OFF_MAX).toInt = -GZ_OFF_MAX.toInt := by decide

theorem next_self {s : GzState} {n : Ival BPtr} (h : s.next = n) : ({ s with next := n } : GzState) = s := by
  cases s; simp only at h; subst h; rfl

/-- What a call of `gzungetc` leaves: a read handle with `LookIdle`, and a step of the call. -/
def UPost (w : World) (h : Heap) (b : Nat) : Int32 → World → Heap → Prop :=
  fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b []

/-! ## The push -/

/-- **The end of a push.** From a read handle `s0` (world `W0`, heap `H0`) whose `out` bytes may have changed (heap
`H`), with `x.have` raised by one: storing at `out + k` with the new output inside `out` keeps a read handle. -/
theorem pushEnd_spec {W0 : World} {H0 H : Heap} {b c base k : Nat} {s0 : GzState} {hv1 : UInt32} {nx0 : Ival BPtr}
    (hv : GzInvR W0 H0 (some b)) (hi : LookIdle W0 H0 (some b)) (hs0 : W0.gz H0 b = some s0)
    (hsz : s0.size ≠ 0) (hB : GzBufs H0 s0 c base)
    (x : HBuf H0 H c (base + inSize s0) (base + inSize s0 + outSize s0))
    (hh : hv1.toNat = s0.«have».toNat + 1)
    (hk1 : inSize s0 ≤ k) (hk2 : k + hv1.toNat ≤ inSize s0 + outSize s0)
    (hpl : -GZ_OFF_MAX.toInt < s0.pos.toInt) (v : Int32) :
    GSat { W0 with gzs := upd W0.gzs b (some { s0 with «have» := hv1, next := nx0 }) } H
      (pushEnd v (some b) (.ref (.heap c) (base + k))) (UPost W0 H0 b) := by
  obtain ⟨sh, hn⟩ := inv_of hs0 hv.1
  have hr := modeOf hs0 hv.2.1
  have R := sh.read hr
  have P := sh.pos
  have hmx := gzmax
  obtain ⟨hbc, hcp, hcst, hown⟩ := buf_facts hs0 hn hsz hB
  obtain ⟨d0, hd0, hds⟩ := hB.fits
  obtain ⟨d, hd, hdsz⟩ := x.size hd0
  obtain ⟨db, hdb⟩ := gz_live hs0
  have hdbH : H.bytes b = some db := by rw [x.bytes_ne hbc]; exact hdb
  unfold pushEnd
  refine GSat.bind (GSat.of_eq (wrG_upd hdbH W0 _ _) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_upd hdbH W0 _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, rfl, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, H, addH hd (off := base + k) 0 (by omega), ?_⟩)
  obtain ⟨H2, e8, x1⟩ : ∃ H2, store8 (.ref (.heap c) (base + k + 0)) v.toUInt32.toUInt8 H = .ok ((), H2) ∧
      HBuf H H2 c (base + inSize s0) (base + inSize s0 + outSize s0) :=
    ⟨_, store8_heap hd (by omega) _, HBuf.store8 hd (by omega) (by omega) _⟩
  refine GSat.bind (GSat.lm ⟨(), H2, e8, ?_⟩)
  have xx := x.trans x1 (Nat.le_refl _) (Nat.le_refl _)
  have hdb2 : H2.bytes b = some db := (xx.bytes_ne hbc).trans hdb
  have hb1 : -(2 ^ 63 : Int) ≤ s0.pos.toInt - 1 ∧ s0.pos.toInt - 1 < 2 ^ 63 := by
    have := P.2; have := P.1; constructor <;> omega
  refine GSat.bind (GSat.of_eq (rdG_upd hdb2 W0 _ _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H2, chkI64_ok hb1.1 hb1.2 H2, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb2 W0 _ _) ?_)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb2 W0 _ _) ?_)
  refine GSat.pure ?_
  have e2 := toInt_ofInt' hb1.1 hb1.2
  have hs2 : W0.gz H2 b = some s0 := by rw [xx.gz hbc]; exact hs0
  have hv2 := invR_hbuf hv hs0 xx hbc hcp hcst (FsRd.refl _)
  let sF : GzState := { s0 with «have» := hv1, next := .val (.ref (.heap c) (base + k)), pos := Int64.ofInt (s0.pos.toInt - 1), past := 0 }
  have hst : ({ W0 with gzs := upd W0.gzs b (some sF) } : World).gz H2 b = some sF := gz_upd_same hs2 sF
  refine ⟨?_, ?_, gstep_hbuf hs0 xx hbc hown W0.fs sF rfl rfl rfl rfl⟩
  · refine (invR_hp hv2 hs2 (s' := sF) rfl ?_ ?_ ?_ ?_ ?_ ?_).1
    · show -GZ_OFF_MAX.toInt ≤ (Int64.ofInt (s0.pos.toInt - 1)).toInt
      rw [e2]; omega
    · show (Int64.ofInt (s0.pos.toInt - 1)).toInt + s0.skip.toInt ≤ GZ_OFF_MAX.toInt
      rw [e2]; have := P.2; omega
    · refine Or.inr ⟨hsz, fun c' base' hb' => ?_⟩
      have e1 := hb'.buffers; rw [hB.buffers] at e1; cases e1
      exact ⟨_, rfl, k, rfl, hk1, hk2⟩
    · intro hk
      show (Int64.ofInt (s0.pos.toInt - 1)).toInt + s0.skip.toInt + (hv1.toNat : Int) ≤ GZ_OFF_MAX.toInt
      rw [e2, hh]; have := R.skip_have hk; push_cast; omega
    · show (Int64.ofInt (s0.pos.toInt - 1)).toInt + (hv1.toNat : Int) ≤ GZ_OFF_MAX.toInt
      rw [e2, hh]; have := R.pos_have; push_cast; omega
    · intro hL hD
      show (Int64.ofInt (s0.pos.toInt - 1)).toInt + (hv1.toNat : Int) ≤ 0
      rw [e2, hh]; have := R.look_pos hL hD; push_cast; omega
  · obtain ⟨t, et, -⟩ := xx
    exact idle_same hi hs0 hst rfl rfl rfl (by rw [et])

/-- **A push in front of output that starts after `out`** (`x.next == out + j + 1`), from a read handle `s0` whose
`out` bytes may have changed. -/
theorem ungetcEnd_spec {W0 W1 : World} {H0 H : Heap} {b c base j : Nat} {s0 s1 : GzState}
    (hv : GzInvR W0 H0 (some b)) (hi : LookIdle W0 H0 (some b)) (hs0 : W0.gz H0 b = some s0)
    (hsz : s0.size ≠ 0) (hB : GzBufs H0 s0 c base)
    (x : HBuf H0 H c (base + inSize s0) (base + inSize s0 + outSize s0))
    (hW : W1 = { W0 with gzs := upd W0.gzs b (some s1) })
    (es : s1 = { s0 with next := .val (.ref (.heap c) (base + j + 1)) })
    (hj1 : inSize s0 ≤ j) (hj2 : j + 1 + s0.«have».toNat ≤ inSize s0 + outSize s0)
    (hpl : -GZ_OFF_MAX.toInt < s0.pos.toInt) (v : Int32) :
    GSat W1 H (ungetcEnd v (some b)) (UPost W0 H0 b) := by
  subst hW es
  obtain ⟨sh, hn⟩ := inv_of hs0 hv.1
  have hr := modeOf hs0 hv.2.1
  have hwh := sh.want_hi
  have hosz : outSize s0 = 2 * s0.want.toNat := by simp [outSize, hr, read_ne_write]
  obtain ⟨hbc, -, -, -⟩ := buf_facts hs0 hn hsz hB
  obtain ⟨d0, hd0, hds⟩ := hB.fits
  obtain ⟨d, hd, hdsz⟩ := x.size hd0
  obtain ⟨db, hdb⟩ := gz_live hs0
  have hdbH : H.bytes b = some db := by rw [x.bytes_ne hbc]; exact hdb
  have hh : (s0.«have» + 1).toNat = s0.«have».toNat + 1 := by
    rw [UInt32.toNat_add]; simp; omega
  unfold ungetcEnd
  refine GSat.bind (GSat.of_eq (wrG_upd hdbH W0 _ _) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_upd hdbH W0 _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, rfl, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, H, subH hd (off := base + j) (by omega), ?_⟩)
  exact pushEnd_spec hv hi hs0 hsz hB x hh hj1 (by omega) hpl v

/-- **The push** on a read handle with buffers and `x.pos > -GZ_OFF_MAX`. -/
theorem ungetcPush_spec {W : World} {H : Heap} {b : Nat} {s : GzState}
    (hv : GzInvR W H (some b)) (hi : LookIdle W H (some b)) (hs : W.gz H b = some s) (hsz : s.size ≠ 0)
    (hpl : -GZ_OFF_MAX.toInt < s.pos.toInt) (v : Int32) :
    GSat W H (ungetcPush v (some b)) (UPost W H b) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  obtain ⟨c, base, z, hB, -, -, hhv, -, -⟩ := R.bufs hsz
  obtain ⟨hbc, -, -, -⟩ := buf_facts hs hn hsz hB
  obtain ⟨d, hd, hds⟩ := hB.fits
  obtain ⟨db, hdb⟩ := gz_live hs
  have hwl := sh.want_lo
  have hwh := sh.want_hi
  have hosz : outSize s = 2 * s.want.toNat := by simp [outSize, hr, read_ne_write]
  have hshl : (s.size <<< 1).toNat = outSize s := by
    rw [hB.size, hosz]; exact shl1_toNat _ (by omega)
  have hout : s.out = .val (.ref (.heap c) (base + inSize s)) := hB.out (by omega)
  unfold ungetcPush
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro h0
    have h0' : s.«have» = 0 := by simpa using h0
    refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
    refine GSat.bind (GSat.of_eq (ldGz_upd hdb W _) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, by show Ival.get s.out H = _; rw [hout]; rfl, ?_⟩)
    refine GSat.bind (GSat.of_eq (rdG_upd hdb W _ _) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, addH hd (off := base + inSize s) (s.size <<< 1).toNat (by omega), ?_⟩)
    rw [hshl, show base + inSize s + outSize s = base + (inSize s + outSize s - 1) + 1 by omega]
    refine GSat.bind (GSat.lm ⟨_, H, subH hd (off := base + (inSize s + outSize s - 1)) (by omega), ?_⟩)
    exact pushEnd_spec (hv1 := 1) hv hi hs hsz hB (HBuf.refl _ _ _ _) (by rw [h0']; rfl) (by omega)
      (by simp; omega) hpl v
  intro h0
  have hh0 : s.«have» ≠ 0 := by simpa using h0
  obtain ⟨p, hp, k, hpk, hk1, hk2⟩ := hhv.resolve_left hh0
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.mono (errlit_strm hv hs Z_DATA_ERROR "out of room to push characters" 7 lit_room
      (by decide)) fun p W2 H2 q => GSat.bind (GSat.mono q fun _ W3 H3 q3 => ?_))
    obtain ⟨s', hs', he, hv', -, g', hst⟩ := q3
    refine GSat.pure ⟨hv', idle_same hi hs hs' (by rw [he.1]; rfl) (by rw [he.1]; rfl) (by rw [he.1]; rfl)
      (by rw [hst]), g'⟩
  intro hfull
  have hfull' : s.«have».toNat ≠ outSize s := by
    intro e; apply hfull; rw [← hshl] at e; simp [UInt32.toNat_inj.mp e]
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  refine GSat.bind (GSat.lm ⟨p, H, by show Ival.get s.next H = _; rw [hp]; rfl, ?_⟩)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, by show Ival.get s.out H = _; rw [hout]; rfl, ?_⟩)
  have hpl' := hpl
  apply GSat.ite
  · intro he
    have hk : k = inSize s := by
      rw [hpk] at he; simp at he; omega
    subst hk
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, by show Ival.get s.out H = _; rw [hout]; rfl, ?_⟩)
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, addH hd (off := base + inSize s) s.«have».toNat (by omega), ?_⟩)
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, by show Ival.get s.out H = _; rw [hout]; rfl, ?_⟩)
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, addH hd (off := base + inSize s) (s.size <<< 1).toNat (by omega), ?_⟩)
    have hvb := s.«have».toNat_lt
    refine GSat.bind (GSat.mono (slide_spec hs hout (Ne.symm hbc) hd (by omega) (by omega) hvb)
      fun lp W' H' q => ?_)
    obtain ⟨eW, hdst, x⟩ := q
    have hsH : W'.gz H' b = some s := by rw [eW, x.gz hbc]; exact hs
    refine GSat.bind (GSat.of_eq (wrG_app hsH _) ?_)
    rw [hdst, hshl, show base + inSize s + (outSize s - s.«have».toNat) =
      base + (inSize s + (outSize s - s.«have».toNat) - 1) + 1 by omega]
    exact ungetcEnd_spec hv hi hs hsz hB (by rw [← hshl]; exact x) (by rw [eW]) rfl (by omega) (by omega) hpl v
  · intro hne
    have hk : k ≠ inSize s := by
      intro e; apply hne; rw [hpk, e]; simp
    refine ungetcEnd_spec (j := k - 1) hv hi hs hsz hB (HBuf.refl _ _ _ _)
      (by rw [DeflateReset.upd_self W.gzs b s (gzs_of hs)]) (next_self (by rw [hp, hpk,
        show base + (k - 1) + 1 = base + k by omega])).symm (by omega) (by omega) hpl v

/-! ## `gzungetc` -/

/-- After the pending skip: the tests of `c` and of `x.pos`, then the push. -/
theorem ungetcRest_spec {W : World} {H : Heap} {b : Nat} {s : GzState}
    (hv : GzInvR W H (some b)) (hi : LookIdle W H (some b)) (hs : W.gz H b = some s) (hsz : s.size ≠ 0)
    (v : Int32) : GSat W H (ungetcRest v (some b)) (UPost W H b) := by
  unfold ungetcRest
  apply GSat.ite
  · intro _; exact GSat.pure ⟨hv, hi, GStep.refl W H b []⟩
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact GSat.pure ⟨hv, hi, GStep.refl W H b []⟩
  intro hle
  have hpl : -GZ_OFF_MAX.toInt < s.pos.toInt := by
    have := mt Int64.le_iff_toInt_le.mpr (by simpa using hle)
    rw [neg_max] at this; omega
  exact ungetcPush_spec hv hi hs hsz hpl v

/-- After `gz_look`: the mid-call state `s1`, `LookIdle`, a step of the call so far, a read handle when an error is
pending, and buffers when none is. -/
theorem ungetcTail_spec (SS : GzSkipSpec) (SI : GzSkipIdle) {w W1 : World} {h H1 : Heap} {b : Nat} {s1 : GzState}
    (hm : GzMid W1 H1 b s1) (hi1 : LookIdle W1 H1 (some b)) (g1 : GStep w h W1 H1 b [])
    (hw0 : ∃ s, w.gz h b = some s)
    (hbad : ¬ ErrOk s1 → GzInvR W1 H1 (some b)) (hsz : ErrOk s1 → s1.size ≠ 0) (v : Int32) :
    GSat W1 H1 (ungetcTail v (some b)) (UPost w h b) := by
  obtain ⟨hs1, hv0, hout, hph⟩ := hm
  have hmode : s1.mode = GZ_READ := by
    have := modeOf (gz_upd_same hs1 { s1 with «have» := 0 }) hv0.2.1
    exact this
  have K : ∀ W2 H2 s2, GzInvR W2 H2 (some b) → LookIdle W2 H2 (some b) → GStep w h W2 H2 b [] →
      W2.gz H2 b = some s2 → s2.size ≠ 0 → GSat W2 H2 (ungetcRest v (some b)) (UPost w h b) :=
    fun W2 H2 s2 hv2 hi2 g2 hs2 hsz2 => (ungetcRest_spec hv2 hi2 hs2 hsz2 v).mono fun _ W3 H3 q =>
      ⟨q.1, q.2.1, g2.trans q.2.2 hw0 ⟨s2, hs2⟩⟩
  unfold ungetcTail
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  apply GSat.ite
  · intro hc
    have hbad' : ¬ ErrOk s1 := by
      rintro (e | e) <;> simp [hmode, e] at hc
    exact GSat.pure ⟨hbad hbad', hi1, g1⟩
  intro hc
  have hok : ErrOk s1 := by
    by_cases e1 : s1.err = Z_OK
    · exact Or.inl e1
    · exact Or.inr (Classical.byContradiction fun e2 => hc (by simp [hmode, e1, e2]))
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  apply GSat.ite
  · intro hk
    have hk' : s1.skip ≠ 0 := by simpa using hk
    refine GSat.bind (GSat.mono (GSat.withRun (SS W1 H1 b s1 ⟨hs1, hv0, hout, hph⟩ hk')) fun r W2 H2 q => ?_)
    obtain ⟨⟨-, hv2, g2, -, s2, hs2, -, hsz2, -⟩, run⟩ := q
    have hi2 := SI W1 H1 b s1 r W2 H2 ⟨hs1, hv0, hout, hph⟩ hi1 hk' run
    have g := g1.trans g2 hw0 ⟨s1, hs1⟩
    apply GSat.ite
    · intro _; exact GSat.pure ⟨hv2, hi2, g⟩
    · intro _; exact K W2 H2 s2 hv2 hi2 g hs2 (hsz2 (hsz hok))
  · intro hk
    have hk' : s1.skip = 0 := by simpa using hk
    exact K W1 H1 s1 (invR_restore hv0 hs1 hout (fun e => absurd hk' e) hph) hi1 g1 hs1 (hsz hok)

/-- **`gzungetc`** on a read handle with `LookIdle`: a read handle with `LookIdle` again, and a step of the call that
writes no caller memory. -/
theorem gzungetc_read (SS : GzSkipSpec) (SI : GzSkipIdle) {w : World} {h : Heap} {b : Nat}
    (hv : GzInvR w h (some b)) (hi : LookIdle w h (some b)) (v : Int32) :
    GSat w h (gzungetc v (some b)) (UPost w h b) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  have direct : s.size ≠ 0 → GSat w h (ungetcTail v (some b)) (UPost w h b) := fun hsz =>
    ungetcTail_spec SS SI (mid_of hv hs) hi (GStep.refl w h b []) ⟨s, hs⟩ (fun _ => hv) (fun _ => hsz) v
  rw [gzungetc_eq]
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro hlk
      have hlk' : s.how = LOOK := by simpa using hlk
      refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
      apply GSat.ite
      · intro h0
        have h0' : s.«have» = 0 := by simpa using h0
        refine GSat.bind (GSat.mono (gz_look_specI hv hs h0' hlk') fun r W1 H1 q => ?_)
        obtain ⟨⟨hr1, g1, -, s1, hs1, -, -, hsz1, -, hv0, hout, hph, -⟩, hi1, hok, hneg⟩ := q
        refine ungetcTail_spec SS SI ⟨hs1, hv0, hout, hph⟩ hi1 g1 ⟨s, hs⟩ (fun hbad => ?_) (fun he => ?_) v
        · have h01 : s1.«have» = 0 := Classical.byContradiction fun hh => hbad (hok hi s1 hs1 hh)
          exact invR_restore hv0 hs1 hout (fun _ => h01) hph
        · rcases hr1 with e | e
          · exact absurd he (hneg e s1 hs1)
          · exact hsz1 e
      · intro h0
        have hh : s.«have» ≠ 0 := by simpa using h0
        exact direct fun e => hh (R.nobuf e)
    · intro hlk
      have hlk' : s.how ≠ LOOK := by simpa using hlk
      exact direct fun e => hlk' (R.look e)
  · intro hm
    have : s.mode ≠ GZ_READ := by simpa using hm
    exact absurd hr this

theorem ungetc_keepsRI (SS : GzSkipSpec) (SI : GzSkipIdle) : KeepsRI SUngetc := by
  intro w h w' h' f hv hi ⟨v, r, e⟩
  obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
  obtain ⟨r2, W, H, e2, q⟩ := (gzungetc_read SS SI hv hi v).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact ⟨q.1, q.2.1⟩

end ZlibNgF.Proof.GzMode
