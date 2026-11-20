import ZlibNgF.Proof.«gzread.c.init»
import ZlibNgF.Proof.«inflate.c.reset»
import ZlibNgF.Proof.«gzlib.c.seek64»
import ZlibNgF.Proof.«gzread.c.decomp»

/-!
# `gz_look` on a read handle (`ZlibNgF`)

`gz_look` runs with `x.have == 0` (every caller checks it). It makes the buffers and the inflate state when the handle
has none (`gz_read_init`), resets the inflate state for a gzip stream (`inflateReset`), fills the input buffer when it
holds fewer than two bytes (`gz_avail`), reads the two magic bytes inside the `in` buffer, and otherwise copies the
input to the `out` buffer for a transparent read (`memcpy` between the two disjoint parts of the buffer block).

After the call `x.have` may be the number of bytes copied while a skip is pending, which `GzRead.skip_have` does not
allow between calls: the post-condition is the invariant of the world with `x.have` cleared, and the bytes `x.have`
from `x.next` inside `out`. The callers consume `min(x.have, skip)` before they return.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzDecomp

/-! ## A new stream record and inflate state on a read handle -/

/-- A read handle with buffers stays one when its stream record and the inflate state of its block get new values
(`setZS`) that keep the inflate invariant, the state block, the input inside `in`, and no registered header. -/
theorem invR_setZS {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (hsz : s.size ≠ 0) {z z' : ZStream} {sb : Nat} {st' : InflateState}
    (hz : h.streams s.strm = some z) (hzs : z.state = some sb) (hz's : z'.state = some sb)
    (hinv : InflateInv.Inv (InflateInv.setZS h s.strm z' sb st') (some s.strm)) (hhd : st'.head = .val none)
    (hin : ∀ c base, GzBufs h s c base → z'.avail_in = 0 ∨ Inside c base 0 (inSize s) z'.next_in z'.avail_in.toNat)
    (hmsg : z'.msg = .null ∨ ∃ k, z'.msg = .ref (.str k) 0 ∧ k < strTable.size)
    (hcp : s.how = ZlibNg.Gz.COPY → z'.avail_in = 0) :
    GzInvR w (InflateInv.setZS h s.strm z' sb st') (some b) ∧ GStep w h w (InflateInv.setZS h s.strm z' sb st') b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  let H := InflateInv.setZS h s.strm z' sb st'
  have hsH : w.gz H b = some s := hs
  have hzH : H.streams s.strm = some z' := by simp [H, InflateInv.setZS]
  have hst : stBlk H s = stBlk h s := by simp [stBlk, hzH, hz, hzs, hz's]
  have hown : ownL H b s = ownL h b s := by simp only [ownL, hst]
  have shH : GzShape H s := by
    refine ⟨sh.mode, sh.path, ⟨z', hzH⟩, sh.want_lo, sh.want_hi, sh.size, sh.pos, ⟨sh.msg.1, sh.msg.2⟩,
      fun _ => ⟨R.how, fun _ => ?_, R.nobuf, R.skip_have, fun e => absurd e hsz, fun e => absurd e hsz, R.pos_have, R.look_pos,
        R.gzip_direct, fun e z2 hz2 => by rw [hzH] at hz2; cases hz2; exact hcp e⟩,
      fun e => absurd (hr.symm.trans e) read_ne_write, fun e => absurd e hsz⟩
    obtain ⟨c, base, z0, hB, -, hz0, hhv, -, -⟩ := R.bufs hsz
    refine ⟨c, base, z', ⟨hB.size, hB.buffers, hB.inp, hB.out, hB.fits, hB.hdr⟩, hinv, hzH, hhv, hin c base hB, fun hp hrg => ?_, hmsg⟩
    obtain ⟨sb', st1, ⟨z1, ⟨i', e', hz1⟩, hsb1⟩, hst1, hhd1⟩ := hrg
    cases e'
    change H.streams s.strm = some z1 at hz1
    rw [hzH] at hz1; cases hz1
    rw [hz's] at hsb1; cases hsb1
    have : H.istate sb = some st' := by
      obtain ⟨i, zz, bb, stt, al, e, hzz, hbb, hstt, -⟩ := hinv
      cases e; rw [hzH] at hzz; cases hzz; rw [hz's] at hbb; cases hbb
      have hb' : ∃ d, H.bytes sb = some d := by
        unfold Heap.istate at hstt; split at hstt
        · next d hd => exact ⟨d, hd⟩
        · cases hstt
      obtain ⟨d, hd⟩ := hb'
      have hd' : h.bytes sb = some d := hd
      simp [Heap.istate, hd', H, InflateInv.setZS]
    rw [this] at hst1; cases hst1
    rw [hhd] at hhd1; cases hhd1; rfl
  have hnH : (ownL H b s).Nodup := by rw [hown]; exact hn
  obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hstr, hbud, hnod, hlk, hlit⟩ := hv.2.2
  have fr : FreshBlocks h := hfr
  have hsbl : sb < h.nextBlk := by
    obtain ⟨_, _, _, _, _, e, hzz, hbb, hstt, -⟩ := hinv
    cases e; rw [hzH] at hzz; cases hzz; rw [hz's] at hbb; cases hbb
    unfold Heap.istate at hstt; split at hstt
    · next d hd => exact live_lt fr ⟨d, hd⟩
    · cases hstt
  have wfH : GzWFr w H := by
    refine ⟨hc, ⟨fun c e => ?_, hdf⟩, hgz, fun c s2 e => ?_, hbud, hnod, hlk, hlit⟩
    · have hne : c ≠ sb := by have : H.nextBlk = h.nextBlk := rfl; omega
      refine ⟨?_, (hfr c e).2.1, (hfr c e).2.2⟩
      simp [H, InflateInv.setZS, upd_ne _ _ _ _ hne, (hfr c e).1]
    · obtain ⟨z2, hz2⟩ := hstr c s2 e
      by_cases hj : s2.strm = s.strm
      · rw [hj]; exact ⟨z', hzH⟩
      · exact ⟨z2, by simp [H, InflateInv.setZS, upd_ne _ _ _ _ hj, hz2]⟩
  refine ⟨⟨⟨b, s, rfl, hsH, shH, hnH⟩, ⟨b, s, rfl, hsH, hr⟩, wfH⟩, ?_⟩
  have hsbO : sb ∈ GzOwned w h (some b) := by
    simp only [GzOwned, hs, hz, hzs]; simp
  refine gstep_mk hs hsH rfl (fun _ _ _ => rfl) (fun i hi => by simp [H, InflateInv.setZS, upd_ne _ _ _ _ hi]) rfl
    (fun c _ hno => ?_) (fun _ _ e => e) rfl rfl rfl (Nat.le_refl _) (fun c hc _ => ?_)
  · have hne : c ≠ sb := fun e => hno (e ▸ hsbO)
    exact ⟨rfl, by simp [H, InflateInv.setZS, upd_ne _ _ _ _ hne], rfl, rfl, rfl⟩
  · have e : GzOwned w H (some b) = GzOwned w h (some b) := by
      simp only [GzOwned, hsH, hs, hzH, hz, hz's, hzs]
    have hc' : c ∈ GzOwned w H (some b) := hc
    rwa [e] at hc'

/-! ## `gz_look` in parts (copied from the translation) -/

open ZlibNg.Inflate in
/-- From `if (magic)` of `gz_look` to the end. -/
def lookTail (state : GzPtr) (strm : StreamPtr) (magic : Bool) : G Int32 := do
  if magic then
    let _ ← lm (inflateReset strm)
    wrG state fun s => { s with how := GZIP }
    wrG state fun s => { s with direct := 0 }
    return 0
  if (← rdG state (·.direct)) == 0 then
    lm (wrZ strm fun z => { z with avail_in := 0 })
    wrG state fun s => { s with eof := 1 }
    wrG state fun s => { s with «have» := 0 }
    return 0
  let o ← (← ldGz state).out.get
  wrG state fun s => { s with next := .val o }
  lm (Ptr.memcpy (← (← ldGz state).next.get) (← lm (rdZ strm (·.next_in))) (← lm (rdZ strm (·.avail_in))).toNat)
  let ai ← lm (rdZ strm (·.avail_in))
  wrG state fun s => { s with «have» := ai }
  lm (wrZ strm fun z => { z with avail_in := 0 })
  wrG state fun s => { s with how := COPY }
  wrG state fun s => { s with direct := 1 }
  return 0

open ZlibNg.Inflate in
/-- The magic-number test of `gz_look` and what follows. -/
def lookMagic (state : GzPtr) (strm : StreamPtr) : G Int32 := do
  let magic ← if (← lm (rdZ strm (·.avail_in))) > 1 then do
      if (← lm (index8 (← lm (rdZ strm (·.next_in))) 0)) == 31 then do
        pure ((← lm (index8 (← lm (rdZ strm (·.next_in))) 1)) == 139)
      else pure false
    else pure false
  lookTail state strm magic

open ZlibNg.Inflate in
/-- `gz_look` after the buffers exist. -/
def lookRest (state : GzPtr) (strm : StreamPtr) : G Int32 := do
  if (← rdG state (·.direct)) == -1 then
    let _ ← lm (inflateReset strm)
    wrG state fun s => { s with how := GZIP }
    wrG state fun s => { s with direct := 0 }
    return 0
  if (← lm (rdZ strm (·.avail_in))) < 2 then
    if (← gz_avail state) == -1 then
      return -1
    if (← lm (rdZ strm (·.avail_in))) == 0 then
      return 0
  lookMagic state strm

theorem gz_look_eq (state : GzPtr) : gz_look state = (do
    let strm ← strmOf state
    if (← rdG state (·.size)) == 0 then
      if (← gz_read_init state) == -1 then
        return -1
    lookRest state strm) := rfl

/-! ## The post-condition -/

/-- The inflate state of the stream of `s` is the one `inflateReset` leaves: mode `HEAD`, no bits, not the last
block. -/
def HeadState (H : Heap) (s : GzState) : Prop :=
  ∃ z sb st, H.streams s.strm = some z ∧ z.state = some sb ∧ H.istate sb = some st ∧
    st.mode = ZlibNg.Inflate.HEAD ∧ st.bits = 0 ∧ st.last = 0

/-- The position clauses of `GzRead` for the output `x.have` (patch 0016: what the `gzgetc()` macro may take). -/
def PosHave (s : GzState) : Prop :=
  s.pos.toInt + s.«have».toNat ≤ GZ_OFF_MAX.toInt ∧
    (s.how = LOOK → s.direct ≠ 0 → s.pos.toInt + s.«have».toNat ≤ 0)

/-- What `gz_look` leaves on a read handle with `x.have == 0`: `-1` or `0`; a step of the call that only reads the file
system; a state with the same `x.pos` and `skip`, with buffers when the result is `0`; when it switched to `GZIP`, the
inflate state just reset (`HeadState`), and the reset came from input in the buffer (the magic bytes) or from a
`direct == -1` request; the read invariant of the world with `x.have` cleared; `x.have` bytes from `x.next` inside the
`out` buffer; and on `0`, the read measure `rdLeft + avail_in` did not grow. -/
def LookPost (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  (r = -1 ∨ r = 0) ∧ GStep w h W H b [] ∧ FsRd w.fs W.fs ∧
  ∃ s', W.gz H b = some s' ∧ s'.pos = s.pos ∧ s'.skip = s.skip ∧ (r = 0 → s'.size ≠ 0) ∧
    (r = 0 → s'.how = GZIP → s.how = GZIP ∨ (HeadState H s' ∧
      ((∀ z', H.streams s.strm = some z' → z'.avail_in ≠ 0) ∨ s.direct = -1))) ∧
    GzInvR { W with gzs := upd W.gzs b (some { s' with «have» := 0 }) } H (some b) ∧
    (s'.«have» = 0 ∨ (s'.size ≠ 0 ∧ ∀ c base, GzBufs H s' c base →
      ∃ p, s'.next = .val p ∧ Inside c base (inSize s') (inSize s' + outSize s') p s'.«have».toNat)) ∧
    PosHave s' ∧
    (r = 0 → ∀ z z', h.streams s.strm = some z → H.streams s.strm = some z' →
      rdLeft W.fs s.fd + z'.avail_in.toNat ≤ rdLeft w.fs s.fd + z.avail_in.toNat)

/-- No error is pending (the test of `gz_avail`). -/
def ErrOk (s : GzState) : Prop := s.err = ZlibNg.Inflate.Z_OK ∨ s.err = ZlibNg.Inflate.Z_BUF_ERROR

/-- `LookPost`, `LookIdle` after the call, and, when `P` holds, output only with no error pending (`gz_look` copies
input to the output only after a `gz_avail` that found no error, or with two bytes of input at entry). -/
def LookPostP (P : Prop) (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  LookPost w h b s r W H ∧ LookIdle W H (some b) ∧
    (P → ∀ s', W.gz H b = some s' → s'.«have» ≠ 0 → ErrOk s')

/-- **What `gz_look` leaves, with `LookIdle`**: `LookPost`; `LookIdle` after the call; and when `LookIdle` held at
entry, output only with no error pending. -/
abbrev LookPostI (w : World) (h : Heap) (b : Nat) (s : GzState) : Int32 → World → Heap → Prop :=
  LookPostP (LookIdle w h (some b)) w h b s

theorem rd_same {w W : World} (fd : Int32) (e : W.fs = w.fs) {a a' : Nat} (hle : a' ≤ a) :
    rdLeft W.fs fd + a' ≤ rdLeft w.fs fd + a := by rw [e]; omega

/-- A read handle whose `x.have` is already 0 gives the post-condition. -/
theorem lookPost_of {P : Prop} {w : World} {h : Heap} {b : Nat} {s : GzState} {r : Int32} {W : World} {H : Heap}
    {s' : GzState} (hr : r = -1 ∨ r = 0) (g : GStep w h W H b []) (hf : FsRd w.fs W.fs) (hv : GzInvR W H (some b))
    (hs' : W.gz H b = some s') (hp : s'.pos = s.pos) (hk : s'.skip = s.skip) (hz : r = 0 → s'.size ≠ 0)
    (hg : r = 0 → s'.how = GZIP → s.how = GZIP ∨ (HeadState H s' ∧
      ((∀ z', H.streams s.strm = some z' → z'.avail_in ≠ 0) ∨ s.direct = -1)))
    (hrd : r = 0 → ∀ z z', h.streams s.strm = some z → H.streams s.strm = some z' →
      rdLeft W.fs s.fd + z'.avail_in.toNat ≤ rdLeft w.fs s.fd + z.avail_in.toNat)
    (hi : LookIdle W H (some b)) (h0 : s'.«have» = 0) : LookPostP P w h b s r W H := by
  have R := ((inv_of hs' hv.1).1.read (modeOf hs' hv.2.1))
  refine ⟨⟨hr, g, hf, s', hs', hp, hk, hz, hg, ?_, Or.inl h0, ⟨R.pos_have, R.look_pos⟩, hrd⟩, hi,
    fun _ s2 hs2 hh => ?_⟩
  · rw [have0_self h0, DeflateReset.upd_self W.gzs b s' (gzs_of hs')]
    exact hv
  · rw [hs'] at hs2; cases hs2; exact absurd h0 hh

theorem outSize_read {s : GzState} (hr : s.mode = GZ_READ) (d : Int32) :
    outSize { s with direct := d } = outSize s := by
  simp [outSize, hr, read_ne_write]

/-- A store of no output, another `x.next`, `how`, `direct` and `eof` keeps a read handle. -/
theorem invR_look {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (nx : Ival BPtr) (hw : Int32) (hhow : hw = LOOK ∨ hw = ZlibNg.Gz.COPY ∨ hw = GZIP)
    (d e : Int32) (hlook : s.size = 0 → hw = LOOK) (hlk : hw = LOOK → d ≠ 0 → s.pos.toInt ≤ 0)
    (hgd : hw = GZIP → d = 0) (hcp : hw = ZlibNg.Gz.COPY → ∀ z, h.streams s.strm = some z → z.avail_in = 0) :
    GzInvR { w with gzs := upd w.gzs b (some { s with «have» := 0, next := nx, how := hw, direct := d, eof := e }) } h
      (some b) ∧
    GStep w h { w with gzs := upd w.gzs b (some { s with «have» := 0, next := nx, how := hw, direct := d, eof := e }) }
      h b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  have P := sh.pos
  let s' : GzState := { s with «have» := 0, next := nx, how := hw, direct := d, eof := e }
  have hio : outSize s' = outSize s := by
    simp [outSize, s', hr, read_ne_write]
  have sh' : GzShape h s' := by
    refine ⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, sh.size, ⟨P.1, P.2, P.3, P.4⟩,
      ⟨sh.msg.1, sh.msg.2⟩, fun _ => ⟨hhow, fun hsz => ?_, fun _ => rfl, fun _ => ?_,
        fun hz => (R.fresh hz).of_strm rfl, hlook, ?_, fun h1 h2 => ?_, hgd, hcp⟩, fun e' => absurd (hr.symm.trans e') read_ne_write,
        fun hz => sh.dead hz⟩
    · obtain ⟨c, base, z, hB, hi, hz, -, hai, hreg, hmsg⟩ := R.bufs hsz
      refine ⟨c, base, z, ⟨hB.size, hB.buffers, hB.inp, fun e' => ?_, ?_, hB.hdr⟩, hi, hz, Or.inl rfl, hai, hreg, hmsg⟩
      · rw [hio] at e'; exact hB.out e'
      · rw [hio]; exact hB.fits
    · show s.pos.toInt + s.skip.toInt + ((0 : UInt32).toNat : Int) ≤ GZ_OFF_MAX.toInt
      simpa using P.2
    · show s.pos.toInt + ((0 : UInt32).toNat : Int) ≤ GZ_OFF_MAX.toInt
      have := P.1; have := P.2; simp; omega
    · show s.pos.toInt + ((0 : UInt32).toNat : Int) ≤ 0
      have := hlk h1 h2; simpa using this
  have hn' : (ownL h b s').Nodup := hn
  refine ⟨(keeps_store hs (HLess.refl h) (fun _ e' => e') sh' hn' rfl rfl).1 hv, ?_⟩
  exact gstep_st hs w.fs rfl rfl rfl rfl

open ZlibNg.Inflate in
/-- `inflateReset(strm); state->how = GZIP; state->direct = 0; return 0;` on a read handle with buffers, with input
in the buffer or `direct == -1`. -/
theorem resetTail_spec {P : Prop} {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0)
    (hx : (∀ z, h.streams s.strm = some z → z.avail_in ≠ 0) ∨ s.direct = -1) :
    GSat w h (do
      let _ ← lm (inflateReset (some s.strm))
      wrG (some b) fun s => { s with how := GZIP }
      wrG (some b) fun s => { s with direct := 0 }
      return (0 : Int32)) (LookPostP P w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  obtain ⟨c, base, z, hB, hinv, hz, -, hai, -⟩ := R.bufs hsz
  obtain ⟨i, z1, sb, st, al, e, L, -, -⟩ := InflateInv.live hinv
  cases e
  have ez : z1 = z := by have := L.hz; rw [hz] at this; cases this; rfl
  subst ez
  have er := InflateReset.reset_run L
  obtain ⟨i2, z2, b2, st2, e2, run2, inv2⟩ := InflateReset.reset_inv hinv
  have run2' : inflateReset (some s.strm) h = _ := run2
  rw [er] at run2'
  injection run2' with run3
  injection run3 with _ run4
  rw [← run4] at inv2
  obtain ⟨hv1, g1⟩ := invR_setZS hv hs hsz hz L.hb (show (InflateReset.rkZ z1 st.wrap).state = some sb from L.hb) inv2
    rfl (fun c' base' hB' => by
      have e1 := hB'.buffers; rw [hB.buffers] at e1; cases e1; exact hai) (Or.inl rfl)
    (fun e => (R.copy_in e _ hz : z1.avail_in = 0))
  generalize hH : InflateInv.setZS h s.strm (InflateReset.rkZ z1 st.wrap) sb (InflateReset.rkS sb (InflateReset.rS st)) = H at hv1 g1 er
  have hsH : w.gz H b = some s := by rw [← hH]; exact hs
  have hzH : H.streams s.strm = some (InflateReset.rkZ z1 st.wrap) := by rw [← hH]; simp [InflateInv.setZS]
  refine GSat.bind (GSat.lm ⟨_, H, er, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_app hsH _) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same hsH _) _) ?_)
  refine GSat.pure ?_
  obtain ⟨hv2, g2⟩ := invR_look hv1 hsH s.next GZIP (Or.inr (Or.inr rfl)) 0 s.eof (fun e => absurd e hsz)
    (fun e => absurd e (by decide)) (fun _ => rfl) (fun e => absurd e (by decide))
  simp only [InflateInv.upd_upd]
  have es : ({ ({ s with how := GZIP } : GzState) with direct := 0 } : GzState) =
      { s with «have» := 0, next := s.next, how := GZIP, direct := 0, eof := s.eof } := by
    cases s; simp only at h0 ⊢; rw [h0]
  rw [es]
  have hHS : HeadState H s := by
    obtain ⟨d, hd⟩ := L.hd
    refine ⟨InflateReset.rkZ z1 st.wrap, sb, InflateReset.rkS sb (InflateReset.rS st), hzH, L.hb, ?_, rfl, rfl, rfl⟩
    · rw [← hH]; simp [Heap.istate, InflateInv.setZS, hd]
  have hsF := gz_upd_same hsH { s with «have» := 0, next := s.next, how := GZIP, direct := 0, eof := s.eof }
  refine lookPost_of (Or.inr rfl) (g1.trans g2 ⟨s, hs⟩ ⟨s, hsH⟩) (FsRd.refl _) hv2 hsF rfl rfl
    (fun _ => hsz) (fun _ _ => Or.inr ⟨hHS, ?_⟩) ?_ ?_ rfl
  · refine hx.imp_left fun f z' hz' => ?_
    rw [hzH] at hz'; cases hz'; exact f z1 hz
  · intro _ z0 z' hz0 hz'
    rw [hzH] at hz'; cases hz'; rw [hz] at hz0; cases hz0
    exact rd_same s.fd rfl (Nat.le_refl _)
  · exact idle_mk hsF fun _ _ h1 _ => absurd (show GZIP = LOOK from h1) (by decide)

/-! ## The magic bytes and the copy of a transparent file -/

/-- `memcpy` from below `od` to `od` inside one heap block: only the bytes `[od, od + n)` of that block change. -/
theorem memcpy_below {H : Heap} {c od os n : Nat} {a : Array UInt8} (ha : H.bytes c = some a)
    (h1 : od + n ≤ a.size) (hdis : os + n ≤ od) :
    ∃ H', Ptr.memcpy (Ptr.ref (BRef.heap c) od : BPtr) (Ptr.ref (BRef.heap c) os) n H = .ok ((), H') ∧ HBuf H H' c od (od + n) := by
  have h2 : os + n ≤ a.size := by omega
  have hno : ¬ (n > 0 ∧ ¬ (od + n ≤ os ∨ os + n ≤ od)) := fun h => h.2 (Or.inr hdis)
  refine ⟨{ H with bytes := upd H.bytes c (some (InflateDict.copyFold a od os (List.range' 0 n) a)) }, ?_, ?_⟩
  · simp only [Ptr.memcpy, InflateDict.space_get_heap, ha, Space.ro, Heap.isRo, Bool.false_eq_true,
      ↓reduceIte, h1, h2, and_self, true_and, hno]
    rw [ChunkMem.modify_heap _ _ a ha, InflateDict.memcpy_loop]
  · refine ⟨_, rfl, ?_, ?_, ?_⟩
    · intro c' hc'; simp [upd_ne _ _ _ _ hc']
    · intro e; rw [ha] at e; cases e
    intro a' ha'
    rw [ha] at ha'; cases ha'
    refine ⟨InflateDict.copyFold a od os (List.range' 0 n) a, by simp, InflateDict.copyFold_size _ _ _ _ _, fun j hj => ?_⟩
    exact InflateDict.copyFold_get _ _ _ _ _ j fun i hi => ChunkMem.mem_range'_bound hi hj

theorem index8_heap {H : Heap} {c off : Nat} (i : Nat) {a : Array UInt8} (ha : H.bytes c = some a)
    (hi : off + i < a.size) : index8 (.ref (.heap c) off) (Int.ofNat i) H = .ok (a[off + i]!, H) :=
  Inftrees.index_nat (r := BRef.heap c) ha hi

open ZlibNg.Inflate in
/-- The `if (magic)` tail of `gz_look` on a read handle with buffers and input; the copy to the output only with no error pending, when `P` holds. -/
theorem lookTail_spec {P : Prop} {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) {z : ZStream} (hz : h.streams s.strm = some z)
    (hai : z.avail_in ≠ 0) (hlook : s.how = LOOK) (hok : P → s.direct ≠ 0 → ErrOk s) (magic : Bool) :
    GSat w h (lookTail (some b) (some s.strm) magic) (LookPostP P w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  unfold lookTail
  apply GSat.ite
  · intro _
    refine resetTail_spec hv hs h0 hsz (Or.inl fun z' hz' => ?_)
    rw [hz] at hz'; cases hz'; exact hai
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    -- not a gzip stream and not transparent: no input, end of file
    let z' : ZStream := { z with avail_in := 0 }
    refine GSat.bind (GSat.lm ⟨(), { h with streams := upd h.streams s.strm (some z') }, wrZ_app hz _, ?_⟩)
    have hv1 := invR_strm (z' := z') hv hs hsz hz rfl (fun _ _ _ => Or.inl rfl) (fun _ => rfl)
    have g1 := gstep_strm hs z' hz rfl
    have hs1 : w.gz { h with streams := upd h.streams s.strm (some z') } b = some s := hs
    refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
    refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same hs1 _) _) ?_)
    refine GSat.pure ?_
    obtain ⟨hv2, g2⟩ := invR_look hv1 hs1 s.next s.how R.how s.direct 1 R.look
      (fun h1 h2 => by have := R.look_pos h1 h2; rw [h0] at this; simpa using this) R.gzip_direct
      (fun _ z2 hz2 => by simp at hz2; rw [← hz2])
    simp only [InflateInv.upd_upd]
    have es : ({ ({ s with eof := 1 } : GzState) with «have» := 0 } : GzState) =
        { s with «have» := 0, next := s.next, how := s.how, direct := s.direct, eof := 1 } := rfl
    rw [es]
    have hsF := gz_upd_same hs1 { s with «have» := 0, next := s.next, how := s.how, direct := s.direct, eof := 1 }
    have hzF : ∀ z2, ({ h with streams := upd h.streams s.strm (some z') } : Heap).streams s.strm = some z2 →
        z2.avail_in = 0 := fun z2 hz2 => by simp at hz2; rw [← hz2]
    refine lookPost_of (Or.inr rfl) (g1.trans g2 ⟨s, hs⟩ ⟨s, hs1⟩) (FsRd.refl _) hv2 hsF rfl rfl
      (fun _ => hsz) (fun _ e => Or.inl e) (fun _ z0 z2 _ hz2 => ?_) (idle_zero hsF hzF) rfl
    rw [hzF z2 hz2]; exact rd_same s.fd rfl (by simp)
  intro hd0
  have hdir : s.direct ≠ 0 := by simpa using hd0
  have hpos0 : s.pos.toInt ≤ 0 := by have := R.look_pos hlook hdir; rw [h0] at this; simpa using this
  -- transparent: copy the input to the output buffer
  obtain ⟨c, base, z0, hB, -, hz0, -, hin, -⟩ := R.bufs hsz
  rw [hz] at hz0; cases hz0
  obtain ⟨k, hnx, -, hkn⟩ := hin.resolve_left hai
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  obtain ⟨d, hd, hds⟩ := hB.fits
  have hin' : inSize s = s.want.toNat := by simp [inSize, hr, read_ne_write]
  have hout' : outSize s = 2 * s.want.toNat := by simp [outSize, hr, read_ne_write]
  have hwl := sh.want_lo
  have hO : s.out = .val (.ref (.heap c) (base + inSize s)) := hB.out (by rw [hout']; omega)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  refine GSat.bind (GSat.lm ⟨_, h, (by rw [hO]; rfl), ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
  let s1 : GzState := { s with next := .val (.ref (.heap c) (base + inSize s)) }
  have hs1 := gz_upd_same hs s1
  refine GSat.bind (GSat.of_eq (ldGz_app hs1) ?_)
  refine GSat.bind (GSat.lm ⟨_, h, rfl, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
  rw [hnx]
  obtain ⟨H1, em, x⟩ := memcpy_below (od := base + inSize s) (os := base + k) (n := z.avail_in.toNat) hd
    (by omega) (by omega)
  refine GSat.bind (GSat.lm ⟨(), H1, em, ?_⟩)
  have hz1 : H1.streams s.strm = some z := by obtain ⟨t, rfl, -⟩ := x; exact hz
  refine GSat.bind (GSat.lm ⟨_, H1, rdZ_app hz1 _, ?_⟩)
  have hsH1 : ({ w with gzs := upd w.gzs b (some s1) } : World).gz H1 b = some s1 := by
    rw [x.gz hcb]; exact hs1
  refine GSat.bind (GSat.of_eq (wrG_app hsH1 _) ?_)
  let z' : ZStream := { z with avail_in := 0 }
  refine GSat.bind (GSat.lm ⟨(), { H1 with streams := upd H1.streams s.strm (some z') }, wrZ_app hz1 _, ?_⟩)
  let H2 : Heap := { H1 with streams := upd H1.streams s.strm (some z') }
  have hsH2 : ({ w with gzs := upd w.gzs b (some s1) } : World).gz H2 b = some s1 := hsH1
  refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same hsH2 _) _) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same (gz_upd_same hsH2 _) _) _) ?_)
  refine GSat.pure ?_
  -- the invariant through the copy, the stream and the state
  have hx : HBuf h H1 c base (base + inSize s + outSize s) := by
    obtain ⟨t, rfl, hne, hnone, hsz'⟩ := x
    refine ⟨t, rfl, hne, hnone, fun a ha => ?_⟩
    obtain ⟨a', e1, e2, e3⟩ := hsz' a ha
    exact ⟨a', e1, e2, fun j hj => e3 j (by omega)⟩
  have hvA : GzInvR { w with fs := w.fs } H1 (some b) := invR_hbuf hv hs hx hcb hpath hst (FsRd.refl _)
  have hvA' : GzInvR w H1 (some b) := hvA
  have hsA : w.gz H1 b = some s := by rw [x.gz hcb]; exact hs
  have hvB := invR_strm (z' := z') hvA' hsA hsz hz1 rfl (fun _ _ _ => Or.inl rfl) (fun _ => rfl)
  have hsB : w.gz H2 b = some s := hsA
  obtain ⟨hvC, gC⟩ := invR_look hvB hsB (.val (.ref (.heap c) (base + inSize s))) ZlibNg.Gz.COPY
    (Or.inr (Or.inl rfl)) 1 s.eof (fun e => absurd e hsz) (fun e => absurd e (by decide)) (fun e => absurd e (by decide))
    (fun _ z2 hz2 => by simp [H2] at hz2; rw [← hz2])
  have gA : GStep w h w H1 b [] := by
    have := gstep_hbuf hs hx hcb hown w.fs s rfl rfl rfl rfl
    rw [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this
    exact this
  have gB := gstep_strm hsA z' hz1 rfl
  simp only [InflateInv.upd_upd]
  let o3 : BPtr := .ref (.heap c) (base + inSize s)
  let s3 : GzState := { s with «have» := z.avail_in, next := .val o3, how := ZlibNg.Gz.COPY, direct := 1 }
  have hsW := gz_upd_same hsB s3
  refine ⟨⟨Or.inr rfl, ?_, FsRd.refl _, s3, hsW, rfl, rfl, fun _ => hsz,
    fun _ e => absurd e (by decide : ZlibNg.Gz.COPY ≠ GZIP), ?_, ?_, ?_, ?_⟩,
    idle_mk hsW fun _ _ h1 _ => absurd (show ZlibNg.Gz.COPY = LOOK from h1) (by decide),
    fun p s2 hs2 _ => ?_⟩
  · have g3 := gstep_st hsB w.fs (s' := s3) rfl rfl rfl rfl
    exact (gA.trans gB ⟨s, hs⟩ ⟨s, hsA⟩).trans g3 ⟨s, hs⟩ ⟨s, hsB⟩
  · simp only [InflateInv.upd_upd]; exact hvC
  · refine Or.inr ⟨hsz, fun c' base' hB' => ?_⟩
    have e1 := hB'.buffers; rw [show s3.buffers = s.buffers from rfl, hB.buffers] at e1; cases e1
    have hi3 : inSize s3 = inSize s := rfl
    have ho3 : outSize s3 = outSize s := by simp [outSize, s3, hr, read_ne_write]
    refine ⟨_, rfl, inSize s, rfl, Nat.le_refl _, ?_⟩
    rw [hi3, ho3]; show inSize s + z.avail_in.toNat ≤ _; omega
  · have hmx' := gzmax
    have hw := sh.want_hi
    refine ⟨?_, fun e => absurd e (by decide : ZlibNg.Gz.COPY ≠ LOOK)⟩
    show s.pos.toInt + (z.avail_in.toNat : Int) ≤ _
    rw [hin'] at hkn; omega
  · intro _ z0 z2 hz0 hz2
    have : z2.avail_in = 0 := by simp [H2] at hz2; rw [← hz2]
    rw [this]; exact rd_same s.fd rfl (by simp)
  · rw [hsW] at hs2; cases hs2; exact hok p hdir

open ZlibNg.Inflate in
/-- The magic-number test reads `next_in[0]` and `next_in[1]` inside the `in` buffer. -/
theorem lookMagic_spec {P : Prop} {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) {z : ZStream} (hz : h.streams s.strm = some z)
    (hai : z.avail_in ≠ 0) (hlook : s.how = LOOK) (hok : P → s.direct ≠ 0 → ErrOk s) :
    GSat w h (lookMagic (some b) (some s.strm)) (LookPostP P w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  obtain ⟨c, base, z0, hB, -, hz0, -, hin, -⟩ := R.bufs hsz
  rw [hz] at hz0; cases hz0
  obtain ⟨k, hnx, -, hkn⟩ := hin.resolve_left hai
  obtain ⟨d, hd, hds⟩ := hB.fits
  unfold lookMagic
  have T : ∀ m : Bool,
      GSat w h (lookTail (some b) (some s.strm) m) (LookPostP P w h b s) :=
    lookTail_spec hv hs h0 hsz hz hai hlook hok
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
  dsimp only
  apply GSat.ite
  · intro hgt
    have hgt' : 1 < z.avail_in.toNat := UInt32.lt_iff_toNat_lt.mp hgt
    refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
    rw [hnx]
    refine GSat.bind (GSat.lm ⟨_, h, index8_heap 0 hd (by omega), ?_⟩)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
      rw [hnx]
      refine GSat.bind (GSat.lm ⟨_, h, index8_heap 1 hd (by omega), ?_⟩)
      exact GSat.bind (GSat.pure (T _))
    · intro _; exact GSat.bind (GSat.pure (T _))
  · intro _; exact GSat.bind (GSat.pure (T _))

/-- The post-condition of a later part of the call gives the post-condition of the whole. -/
theorem LookPost.pre {P : Prop} {w W1 W : World} {h H1 H : Heap} {b : Nat} {s s1 : GzState} {r : Int32}
    (hs : w.gz h b = some s) (g : GStep w h W1 H1 b []) (hf : FsRd w.fs W1.fs) (hs1 : W1.gz H1 b = some s1)
    (hp : s1.pos = s.pos) (hk : s1.skip = s.skip) (hw : s1.how = s.how) (hd : s1.direct = s.direct)
    (hst : s1.strm = s.strm) (hfd : s1.fd = s.fd) {z1 : ZStream} (hz1 : H1.streams s.strm = some z1)
    (hrd : ∀ z, h.streams s.strm = some z → rdLeft W1.fs s.fd + z1.avail_in.toNat ≤ rdLeft w.fs s.fd + z.avail_in.toNat)
    (q : LookPostP P W1 H1 b s1 r W H) : LookPostP P w h b s r W H := by
  obtain ⟨⟨hr, g2, hf2, s', hs', hp', hk', hz, hG, hv, hh, hph, hrd2⟩, hi, he⟩ := q
  refine ⟨⟨hr, g.trans g2 ⟨s, hs⟩ ⟨s1, hs1⟩, hf.trans hf2, s', hs', hp'.trans hp, hk'.trans hk, hz, ?_, hv, hh, hph,
    ?_⟩, hi, he⟩
  · intro h1 h2
    rcases hG h1 h2 with e | ⟨hH, e⟩
    · left; rw [← hw]; exact e
    · right; refine ⟨hH, ?_⟩
      rw [hst, hd] at e; exact e
  · intro h1 z z' hz hz'
    have e1 := hrd2 h1 z1 z' (by rw [hst]; exact hz1) (by rw [hst]; exact hz')
    rw [hfd] at e1
    have e2 := hrd z hz
    omega

open ZlibNg.Inflate in
/-- `gz_look` once the buffers exist. When `P` holds, a transparent-capable handle has fewer than two bytes of
input at entry. -/
theorem lookRest_spec {P : Prop} {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) (hlook : s.how = LOOK)
    (hP : P → ∀ z, h.streams s.strm = some z → s.direct ≠ 0 → z.avail_in.toNat < 2) :
    GSat w h (lookRest (some b) (some s.strm)) (LookPostP P w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  obtain ⟨c, base, z, hB, -, hz, -, -, -⟩ := R.bufs hsz
  unfold lookRest
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hd1; exact resetTail_spec hv hs h0 hsz (Or.inr (by simpa using hd1))
  intro _
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
  apply GSat.ite
  · intro hlt
    have hlt' : z.avail_in.toNat < 2 := UInt32.lt_iff_toNat_lt.mp hlt
    refine GSat.bind (GSat.mono (gz_avail_budget hv hs h0 hsz (by rw [hlook]; decide) (z0 := z) hz) fun r W H q => ?_)
    obtain ⟨⟨hr1, hv1, g1, hf1, s1, hs1, e1⟩, hB1, hB2, hB3⟩ := q
    have h01 : s1.«have» = 0 := by rw [e1]; exact h0
    have hsz1 : s1.size ≠ 0 := by rw [e1]; exact hsz
    have hp1 : s1.pos = s.pos := by rw [e1]
    have hk1 : s1.skip = s.skip := by rw [e1]
    have hst1 : s1.strm = s.strm := by rw [e1]
    have hw1 : s1.how = s.how := by rw [e1]
    have hd1 : s1.direct = s.direct := by rw [e1]
    have hfd1 : s1.fd = s.fd := by rw [e1]
    apply GSat.ite
    · intro hm1
      have hrm : r = -1 := by simpa using hm1
      refine GSat.pure (lookPost_of (Or.inl rfl) g1 hf1 hv1 hs1 hp1 hk1 (fun e => absurd e (by decide))
        (fun e => absurd e (by decide)) (fun e => absurd e (by decide)) ?_ h01)
      refine idle_mk hs1 fun z2 hz2 _ _ => ?_
      rw [hst1, hB2 hrm] at hz2; cases hz2; exact hlt'
    intro hm1
    have hr0 : r = 0 := hr1.resolve_left fun e => hm1 (by rw [e]; rfl)
    obtain ⟨s2, z1, hs2, hz1, -, hbud, -⟩ := hB1 hr0
    have hrd : ∀ z0, h.streams s.strm = some z0 →
        rdLeft W.fs s.fd + z1.avail_in.toNat ≤ rdLeft w.fs s.fd + z0.avail_in.toNat := by
      intro z0 hz0; rw [hz] at hz0; cases hz0; exact hbud
    have hz1' : H.streams s1.strm = some z1 := by rw [hst1]; exact hz1
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz1 _, ?_⟩)
    apply GSat.ite
    · intro ha0
      have ha0' : z1.avail_in = 0 := by simpa using ha0
      refine GSat.pure (lookPost_of (Or.inr rfl) g1 hf1 hv1 hs1 hp1 hk1 (fun _ => hsz1)
        (fun _ e => Or.inl (hw1 ▸ e)) (fun _ z0 z' hz0 hz' => ?_) (idle_zero hs1 fun z2 hz2 => ?_) h01)
      · rw [hz1] at hz'; cases hz'; exact hrd z0 hz0
      · rw [hz1'] at hz2; cases hz2; exact ha0'
    · intro hne
      have hai : z1.avail_in ≠ 0 := by simpa using hne
      have hok1 : ErrOk s1 := by
        obtain ⟨hok, hs'⟩ := hB3 hr0
        unfold ErrOk; rw [hs' s1 hs1]; exact hok
      rw [← hst1]
      exact (lookMagic_spec hv1 hs1 h01 hsz1 hz1' hai (hw1.trans hlook) (fun _ _ => hok1)).mono fun r W' H' q =>
        LookPost.pre hs g1 hf1 hs1 hp1 hk1 hw1 hd1 hst1 hfd1 hz1 hrd q
  · intro hlt
    have hai : z.avail_in ≠ 0 := by
      intro e; rw [e] at hlt; exact hlt (by decide)
    have hge : ¬ z.avail_in.toNat < 2 := fun e => hlt (UInt32.lt_iff_toNat_lt.mpr e)
    exact lookMagic_spec hv hs h0 hsz hz hai hlook fun p hd => absurd (hP p z hz hd) hge

/-- **`gz_look`** on a read handle with `x.have == 0`, with `LookIdle`. -/
theorem gz_look_specI {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hlook : s.how = LOOK) :
    GSat w h (gz_look (some b)) (LookPostI w h b s) := by
  rw [gz_look_eq]
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hsz0
    have hsz : s.size = 0 := by simpa using hsz0
    have hav0 := fresh_avail hv hs hsz
    refine GSat.bind (GSat.mono (gz_read_init_spec hv hs hsz) fun r W H q => ?_)
    obtain ⟨hv1, g1, hf1, s1, hs1, e1, hres, hav⟩ := q
    have h01 : s1.«have» = 0 := by rw [e1]; exact h0
    have hp1 : s1.pos = s.pos := by rw [e1]
    have hk1 : s1.skip = s.skip := by rw [e1]
    have hst1 : s1.strm = s.strm := by rw [e1]
    have hw1 : s1.how = s.how := by rw [e1]
    have hd1 : s1.direct = s.direct := by rw [e1]
    have hfd1 : s1.fd = s.fd := by rw [e1]
    have hf1' : FsRd w.fs W.fs := by rw [hf1]; exact FsRd.refl _
    have hi1 : LookIdle W H (some b) := idle_zero hs1 fun z' hz' => hav z' (by rw [← hst1]; exact hz')
    apply GSat.ite
    · intro hr1
      have : r = -1 := by simpa using hr1
      subst this
      exact GSat.pure (lookPost_of (Or.inl rfl) g1 hf1' hv1 hs1 hp1 hk1 (fun e => absurd e (by decide))
        (fun e => absurd e (by decide)) (fun e => absurd e (by decide)) hi1 h01)
    · intro hr1
      have hne : r ≠ -1 := by simpa using hr1
      obtain ⟨-, hsz1, -⟩ := hres.resolve_right hne
      obtain ⟨z1, hz1⟩ := (inv_of hs1 hv1.1).1.strm
      rw [hst1] at hz1
      rw [← hst1]
      refine (lookRest_spec hv1 hs1 h01 hsz1 (hw1.trans hlook) (P := LookIdle w h (some b))
        fun _ z hz _ => by rw [hav z (by rw [← hst1]; exact hz)]; decide).mono fun r W' H' q => ?_
      refine LookPost.pre hs g1 hf1' hs1 hp1 hk1 hw1 hd1 hst1 hfd1 hz1 (fun z hz => ?_) q
      rw [hav z1 hz1, hf1]; simp
  · intro hsz0
    have hsz : s.size ≠ 0 := by simpa using hsz0
    exact lookRest_spec hv hs h0 hsz hlook fun hi z hz hd => idle_get hi hs hz hlook hd

/-- **`gz_look`** on a read handle with `x.have == 0`. -/
theorem gz_look_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hlook : s.how = LOOK) :
    GSat w h (gz_look (some b)) (LookPost w h b s) :=
  (gz_look_specI hv hs h0 hlook).mono fun _ _ _ q => q.1

/-! ## Consuming a pending skip from the output buffer -/

/-- `n = min(x.have, skip)` bytes of the output buffer are skipped (`gzdirect` with patch 0020, and the loop of
`gz_skip`), then `k` runs (copied from the translation). -/
def consumeThen {α : Type} (state : GzPtr) (k : Unit → G α) : G α := do
  let hv ← rdG state (·.«have»)
  let sk ← rdG state (·.skip)
  let n : UInt32 := if GT_OFF hv || Int64.ofNat hv.toNat > sk then sk.toUInt64.toUInt32 else hv
  wrG state fun s => { s with «have» := s.«have» - n }
  let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
  wrG state fun s => { s with next := .val nx }
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
  wrG state fun s => { s with pos := np }
  let sk ← lm (chkI64 ((← rdG state (·.skip)).toInt - n.toNat))
  let r ← wrG state fun s => { s with skip := sk }
  k r

/-- **The consume step.** After `gz_look` (`LookPost`) with a pending skip and output: `min(x.have, skip)` bytes are
skipped; the handle is a read handle again, `x.pos + skip` is unchanged, and when a skip is still pending there is no
output left. -/
theorem consume_spec {α : Type} {W : World} {H : Heap} {b : Nat} {s' : GzState} {k : Unit → G α}
    {Q : α → World → Heap → Prop}
    (hv0 : GzInvR { W with gzs := upd W.gzs b (some { s' with «have» := 0 }) } H (some b))
    (hs' : W.gz H b = some s')
    (hout : s'.«have» = 0 ∨ (s'.size ≠ 0 ∧ ∀ c base, GzBufs H s' c base →
      ∃ p, s'.next = .val p ∧ Inside c base (inSize s') (inSize s' + outSize s') p s'.«have».toNat))
    (hh : s'.«have» ≠ 0) (hph : PosHave s')
    (hk : ∀ W2 s2, W2.gz H b = some s2 → GzInvR W2 H (some b) → GStep W H W2 H b [] → W2.fs = W.fs →
      s2.pos.toInt + s2.skip.toInt = s'.pos.toInt + s'.skip.toInt → (s2.skip ≠ 0 → s2.«have» = 0) →
      GSat W2 H (k ()) Q) :
    GSat W H (consumeThen (some b) k) Q := by
  let s0 : GzState := { s' with «have» := 0 }
  have hs0 : ({ W with gzs := upd W.gzs b (some s0) } : World).gz H b = some s0 := gz_upd_same hs' s0
  obtain ⟨sh, hn⟩ := inv_of hs0 hv0.1
  have hr : s0.mode = GZ_READ := modeOf hs0 hv0.2.1
  have R := sh.read hr
  have P := sh.pos
  have P2 : s'.pos.toInt + s'.skip.toInt ≤ GZ_OFF_MAX.toInt := P.2
  have P3 : -GZ_OFF_MAX.toInt ≤ s'.pos.toInt := P.3
  obtain ⟨db, hdb⟩ := gz_live hs'
  have h0 : 0 ≤ s'.skip.toInt := P.1
  have hN := nOf_toNat s'.«have» s'.skip h0
  generalize hn' : (if (GT_OFF s'.«have» || decide (Int64.ofNat s'.«have».toNat > s'.skip)) = true then
    s'.skip.toUInt64.toUInt32 else s'.«have») = n at hN
  have hmx' := gzmax
  have hsz : s'.size ≠ 0 := (hout.resolve_left hh).1
  obtain ⟨c, base, z, hb, -, -, -, -, -⟩ := R.bufs hsz
  have hb' : GzBufs H s' c base := ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩
  obtain ⟨q, hq, kk, hqk, hlo, hhi⟩ := (hout.resolve_left hh).2 c base hb'
  obtain ⟨d, hd, hds⟩ := hb.fits
  have hiS : inSize s0 = inSize s' := rfl
  have hoS : outSize s0 = outSize s' := rfl
  rw [hiS, hoS] at hds
  have hh' : s'.«have».toNat ≠ 0 := fun e => hh (UInt32.toNat_inj.mp (by simpa using e))
  have hnl : n.toNat ≤ s'.«have».toNat := by omega
  have hno : n.toNat ≤ s'.skip.toInt.toNat := by omega
  unfold consumeThen
  refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
  simp only [hn']
  let s1 : GzState := { s' with «have» := s'.«have» - n }
  refine GSat.bind (GSat.of_eq (wrG_app hs' _) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_upd hdb W s1) ?_)
  refine GSat.bind (GSat.lm ⟨q, H, by show Ival.get s'.next H = _; rw [hq]; rfl, ?_⟩)
  rw [hqk]
  refine GSat.bind (GSat.lm ⟨_, H, addH hd (off := base + kk) n.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb W s1 _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_upd hdb W _ _) ?_)
  have hpn : -(2 ^ 63 : Int) ≤ s'.pos.toInt + (n.toNat : Int) ∧ s'.pos.toInt + (n.toNat : Int) < 2 ^ 63 := by
    have := P3; have := P2; constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, H, chkI64_ok hpn.1 hpn.2 H, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb W _ _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_upd hdb W _ _) ?_)
  have hon : -(2 ^ 63 : Int) ≤ s'.skip.toInt - (n.toNat : Int) ∧ s'.skip.toInt - (n.toNat : Int) < 2 ^ 63 := by
    have := s'.skip.toInt_lt; constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, H, chkI64_ok hon.1 hon.2 H, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb W _ _) ?_)
  have e2 := toInt_ofInt' hpn.1 hpn.2
  have e3 := toInt_ofInt' hon.1 hon.2
  have hm1 : (s'.«have» - n).toNat = s'.«have».toNat - n.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hnl)]
  let nxF : BPtr := .ref (.heap c) (base + kk + n.toNat)
  let pF : Int64 := Int64.ofInt (s'.pos.toInt + (n.toNat : Int))
  let kF : Int64 := Int64.ofInt (s'.skip.toInt - (n.toNat : Int))
  let sF : GzState := { s' with «have» := s'.«have» - n, next := .val nxF, pos := pF, skip := kF }
  have hkh : sF.skip ≠ 0 → sF.«have» = 0 := by
    intro hk'
    have hk2 : s'.skip.toInt - (n.toNat : Int) ≠ 0 := by
      intro e; apply hk'; show Int64.ofInt _ = 0; rw [e]; rfl
    apply UInt32.toNat_inj.mp
    show (s'.«have» - n).toNat = _
    rw [hm1]; simp; omega
  have hvF := invR_seek hv0 hs0 (s'.«have» - n) (.val (.ref (.heap c) (base + kk + n.toNat)))
    (Int64.ofInt (s'.pos.toInt + (n.toNat : Int))) (Int64.ofInt (s'.skip.toInt - (n.toNat : Int))) s'.how R.how
    (by rw [e3]; omega) (by rw [e2, e3]; have := P2; omega) (by rw [e2]; have := P3; omega) (hlook := (sh.read hr).look) (by
      by_cases hz2 : s'.«have» - n = 0
      · exact Or.inl hz2
      · refine Or.inr ⟨hsz, fun c' base' hb2 => ?_⟩
        have e1 := hb2.buffers; rw [hb.buffers] at e1; cases e1
        exact ⟨_, rfl, kk + n.toNat, by rw [Nat.add_assoc], by omega, by rw [hm1]; omega⟩) hkh
    (by rw [e2, hm1]; have := hph.1; omega) (fun h1 h2 => by rw [e2, hm1]; have := hph.2 h1 h2; omega) R.gzip_direct R.copy_in
  simp only [InflateInv.upd_upd] at hvF ⊢
  have hsF : ({ W with gzs := upd W.gzs b (some sF) } : World).gz H b = some sF := gz_upd_same hs' sF
  exact hk _ sF hsF hvF (gstep_st hs' W.fs rfl rfl rfl rfl) rfl
    (by show (Int64.ofInt _).toInt + (Int64.ofInt _).toInt = _; rw [e2, e3]; omega) hkh

/-- Without a pending skip, or without output, the post-condition of `gz_look` gives the read invariant itself. -/
theorem invR_restore {W : World} {H : Heap} {b : Nat} {s' : GzState}
    (hv0 : GzInvR { W with gzs := upd W.gzs b (some { s' with «have» := 0 }) } H (some b))
    (hs' : W.gz H b = some s')
    (hout : s'.«have» = 0 ∨ (s'.size ≠ 0 ∧ ∀ c base, GzBufs H s' c base →
      ∃ p, s'.next = .val p ∧ Inside c base (inSize s') (inSize s' + outSize s') p s'.«have».toNat))
    (hkh : s'.skip ≠ 0 → s'.«have» = 0) (hph : PosHave s') : GzInvR W H (some b) := by
  let s0 : GzState := { s' with «have» := 0 }
  have hs0 : ({ W with gzs := upd W.gzs b (some s0) } : World).gz H b = some s0 := gz_upd_same hs' s0
  obtain ⟨sh, -⟩ := inv_of hs0 hv0.1
  have hr : s0.mode = GZ_READ := modeOf hs0 hv0.2.1
  have P := sh.pos
  have hout' : s'.«have» = 0 ∨ (s0.size ≠ 0 ∧ ∀ c base, GzBufs H s0 c base →
      ∃ q, s'.next = .val q ∧ Inside c base (inSize s0) (inSize s0 + outSize s0) q s'.«have».toNat) := by
    rcases hout with e | ⟨hsz, f⟩
    · exact Or.inl e
    · exact Or.inr ⟨hsz, fun c base hb => f c base ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩⟩
  have hv := invR_seek hv0 hs0 s'.«have» s'.next s'.pos s'.skip s'.how (sh.read hr).how P.1 P.2 P.3 hout' hkh
    (sh.read hr).look hph.1 hph.2 (sh.read hr).gzip_direct (sh.read hr).copy_in
  simp only [InflateInv.upd_upd] at hv
  have es : ({ s0 with «have» := s'.«have», next := s'.next, pos := s'.pos, skip := s'.skip, how := s'.how } :
      GzState) = s' := by cases s'; rfl
  rw [es, DeflateReset.upd_self W.gzs b s' (gzs_of hs')] at hv
  exact hv

/-! ## `gzdirect` -/

/-- `gzdirect` (with patch 0020) on a read handle: a read handle again, and a step of the call. -/
theorem gzdirect_read {w : World} {h : Heap} {b : Nat} (hv : GzInvR w h (some b)) :
    GSat w h (gzdirect (some b)) (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b []) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  have hr := modeOf hs hv.2.1
  -- the end: `return state->direct == 1`
  have J : ∀ W H, GzInvR W H (some b) → GStep w h W H b [] →
      GSat W H (do let d ← rdG (some b) (·.direct); pure (if (d == 1) = true then (1 : Int32) else 0))
        (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b []) := by
    intro W H hvW g
    obtain ⟨b1, s1, e1, hs1, -, -⟩ := hvW.1
    cases e1
    exact GSat.bind (GSat.of_eq (rdG_app' hs1 _) (GSat.pure ⟨hvW, g⟩))
  have J0 := J w h hv (GStep.refl w h b [])
  unfold gzdirect
  apply GSat.ite
  · intro e; simp at e
  intro _
  dsimp only
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro hlk0
      refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
      apply GSat.ite
      · intro h0
        have h0' : s.«have» = 0 := by simpa using h0
        refine GSat.bind (GSat.mono (gz_look_spec hv hs h0' (by simpa using hlk0)) fun r W H q => ?_)
        obtain ⟨-, g1, -, s', hs', -, -, -, -, hv0, hout, hph, -⟩ := q
        refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
        refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
        apply GSat.ite
        · intro hc
          have hh : s'.«have» ≠ 0 := by
            intro e; rw [e] at hc; simp at hc
          exact consume_spec hv0 hs' hout hh hph fun W2 s2 hs2 hv2 g2 _ _ _ =>
            J W2 H hv2 (g1.trans g2 ⟨s, hs⟩ ⟨s', hs'⟩)
        · intro hc
          have hkh : s'.skip ≠ 0 → s'.«have» = 0 := by
            intro hk
            by_cases hh : s'.«have» = 0
            · exact hh
            · exact absurd (by simp [hk, hh]) hc
          exact J W H (invR_restore hv0 hs' hout hkh hph) g1
      · intro _; exact J0
    · intro _; exact J0
  · intro _; exact J0

theorem direct_keepsR : KeepsR SDirect := by
  intro w h w' h' f hv ⟨r, e⟩
  obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
  obtain ⟨r2, W, H, e2, q⟩ := (gzdirect_read hv).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact q.1

end ZlibNgF.Proof.GzMode
