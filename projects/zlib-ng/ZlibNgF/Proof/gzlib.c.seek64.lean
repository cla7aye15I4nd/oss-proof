import ZlibNgF.Proof.«gzread.c.close»
import ZlibNgF.Proof.«gzread.c.load»

/-!
# `gzseek64` and `gzseek` (`ZlibNgF`)

Patch 0002 (madler's form with two extra commits): `gzseek64` computes the target `pos` (`0` for `SEEK_SET`,
`x.pos + skip` or `x.pos` after the end for `SEEK_CUR`), refuses a target past `GZ_OFF_MAX` (testing `offset >
GZ_OFF_MAX - pos` only when `pos > 0`), before the start, or (at a negative position, after `gzungetc` at the start)
more than `GZ_OFF_MAX` past `x.pos`. Every refusal comes before any store, so a refused seek leaves the state
unchanged. Then `0 <= pos <= GZ_OFF_MAX` and `pos - x.pos <= GZ_OFF_MAX`: a read handle in copy mode seeks inside the
raw data (`lseek` by `pos - x.pos - x.have`, which fits since `x.pos + x.have <= GZ_OFF_MAX`, and the stores of
`gzlib.c:428-434`); otherwise a read handle rewinds when `pos < x.pos`, a write handle refuses, and the skip `pos -
x.pos` is recorded after taking what it can from the output buffer (only when there is output and something to skip:
`x.next` is not set before the first read). The new skip, together with the output left (`x.have` is 0 when the skip
is not), keeps `x.pos + skip <= GZ_OFF_MAX`. The tails of `gzseek64` are copies of its source text (`seekPos`,
`seekNeg`, `seekTail`, `seekRaw`, `seekRest`, `seekOff`, `seekSkip`); each copy in `gzseek64` is the corresponding
definition.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

open ZlibNg.Inflate in
/-- From `if (state->mode == GZ_READ && state->x.have && offset != 0)` to the end (`gzlib.c:450-460` with patch
0002), copied from the translation. -/
def seekSkip (file : GzPtr) (offset pos : Int64) : G Int64 := do
  let state := file
  let mut offset := offset
  if (← rdG state (·.mode)) == GZ_READ then
    if (← rdG state (·.«have»)) != 0 then
      if offset != 0 then
        let hv ← rdG state (·.«have»)
        let n : UInt32 := if GT_OFF hv || (Int64.ofNat hv.toNat) > offset then offset.toUInt64.toUInt32 else hv
        wrG state fun s => { s with «have» := s.«have» - n }
        let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
        wrG state fun s => { s with next := .val nx }
        let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
        wrG state fun s => { s with pos := np }
        offset ← lm (chkI64 (offset.toInt - n.toNat))
  wrG state fun s => { s with skip := offset }
  return pos

/-- From `offset = pos - state->x.pos` to the end (`gzlib.c:445-460`), copied from the translation. -/
def seekOff (file : GzPtr) (offset pos : Int64) : G Int64 := do
  let state := file
  let mut offset := offset
  offset ← lm (chkI64 (pos.toInt - (← rdG state (·.pos)).toInt))
  seekSkip file offset pos

open ZlibNg.Inflate in
/-- From `if (pos < state->x.pos)` to the end (`gzlib.c:439-460`), copied from the translation. -/
def seekRest (file : GzPtr) (offset pos : Int64) : G Int64 := do
  let state := file
  let mut offset := offset
  if pos < (← rdG state (·.pos)) then
    if (← rdG state (·.mode)) != GZ_READ then
      return -1
    if (← gzrewind file) == -1 then
      return -1
  offset ← lm (chkI64 (pos.toInt - (← rdG state (·.pos)).toInt))
  seekSkip file offset pos

open ZlibNg.Inflate in
/-- The seek inside the raw data (`gzlib.c:424-435`), copied from the translation. -/
def seekRaw (file : GzPtr) (pos : Int64) : G Int64 := do
  let state := file
  let ret ← lseekG (← rdG state (·.fd))
    (← lm (chkI64 ((← lm (chkI64 (pos.toInt - (← rdG state (·.pos)).toInt))).toInt -
      Int.ofNat (← rdG state (·.«have»)).toNat))) SEEK_CUR
  if ret == -1 then
    return -1
  wrG state fun s => { s with «have» := 0 }
  wrG state fun s => { s with eof := 0 }
  wrG state fun s => { s with past := 0 }
  wrG state fun s => { s with skip := 0 }
  gz_error state Z_OK .null
  lm (wrZ (← strmOf state) fun z => { z with avail_in := 0 })
  wrG state fun s => { s with pos := pos }
  return pos

open ZlibNg.Inflate in
/-- From the test of the raw area (`if (state->mode == GZ_READ && state->how == COPY)`) to the end (`gzlib.c:423-460`
with patch 0002), copied from the translation. -/
def seekTail (file : GzPtr) (offset pos : Int64) : G Int64 := do
  let state := file
  let mut offset := offset
  if (← rdG state (·.mode)) == GZ_READ then
    if (← rdG state (·.how)) == ZlibNg.Gz.COPY then
      let ret ← lseekG (← rdG state (·.fd))
        (← lm (chkI64 ((← lm (chkI64 (pos.toInt - (← rdG state (·.pos)).toInt))).toInt -
          Int.ofNat (← rdG state (·.«have»)).toNat))) SEEK_CUR
      if ret == -1 then
        return -1
      wrG state fun s => { s with «have» := 0 }
      wrG state fun s => { s with eof := 0 }
      wrG state fun s => { s with past := 0 }
      wrG state fun s => { s with skip := 0 }
      gz_error state Z_OK .null
      lm (wrZ (← strmOf state) fun z => { z with avail_in := 0 })
      wrG state fun s => { s with pos := pos }
      return pos
  if pos < (← rdG state (·.pos)) then
    if (← rdG state (·.mode)) != GZ_READ then
      return -1
    if (← gzrewind file) == -1 then
      return -1
  offset ← lm (chkI64 (pos.toInt - (← rdG state (·.pos)).toInt))
  seekSkip file offset pos

/-- The refusal at a negative position (`gzlib.c:419-420` with patch 0002, then `seekTail`), copied from the
translation. -/
def seekNeg (file : GzPtr) (offset pos : Int64) : G Int64 := do
  let state := file
  if (← rdG state (·.pos)) < 0 then
    if pos > (← lm (chkI64 (GZ_OFF_MAX.toInt + (← rdG state (·.pos)).toInt))) then
      return -1
  seekTail file offset pos

/-- From the first refusal on (`gzlib.c:411-415` with patch 0002, then `seekNeg`), copied from the translation; `pos`
is the position the offset is taken from. -/
def seekPos (file : GzPtr) (offset pos : Int64) : G Int64 := do
  let mut pos := pos
  if pos > 0 then
    if offset > (← lm (chkI64 (GZ_OFF_MAX.toInt - pos.toInt))) then
      return -1
  if offset < (← lm (chkI64 (-pos.toInt))) then
    return -1
  pos ← lm (chkI64 (pos.toInt + offset.toInt))
  seekNeg file offset pos

/-! ## Arithmetic -/

theorem chkI64_ok {v : Int} (h1 : -(2 ^ 63 : Int) ≤ v) (h2 : v < 2 ^ 63) (H : Heap) :
    chkI64 v H = .ok (Int64.ofInt v, H) := by
  unfold chkI64
  split
  · rfl
  · next hn => exact absurd ⟨h1, h2⟩ hn

theorem toInt_ofInt' {v : Int} (h1 : -(2 ^ 63 : Int) ≤ v) (h2 : v < 2 ^ 63) : (Int64.ofInt v).toInt = v :=
  Int64.toInt_ofInt_of_le h1 h2

theorem gzmax : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide

/-- The count `n` of the skip of the output buffer: `min(x.have, offset)`. -/
theorem nOf_toNat (hv : UInt32) (off : Int64) (h0 : 0 ≤ off.toInt) :
    (if (GT_OFF hv || decide (Int64.ofNat hv.toNat > off)) = true then off.toUInt64.toUInt32 else hv).toNat =
      min hv.toNat off.toInt.toNat := by
  have hH := hv.toNat_lt
  have e1 : (Int64.ofNat hv.toNat).toInt = hv.toNat := Int64.toInt_ofNat_of_lt (by omega)
  have h0' : (0 : Int64) ≤ off := Int64.le_iff_toInt_le.mpr (by simpa using h0)
  by_cases hc : off < Int64.ofNat hv.toNat
  · have hc' : off.toInt < hv.toNat := by rw [← e1]; exact Int64.lt_iff_toInt_lt.mp hc
    simp only [GT_OFF, Bool.false_or, gt_iff_lt, hc, decide_true, ite_true]
    rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0', ← Int64.toNat_toInt]
    omega
  · have hc' : ¬ off.toInt < hv.toNat := by rw [← e1]; exact fun e => hc (Int64.lt_iff_toInt_lt.mpr e)
    simp only [GT_OFF, Bool.false_or, gt_iff_lt, hc, decide_false, Bool.false_eq_true, ite_false]
    omega

/-! ## Steps of a call that change only the state -/

/-- A store of a new state that keeps the owned pointers and the stream of the file is a step of a call on it. -/
theorem gstep_st {w : World} {h : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s) (fs : Fs)
    (hp : s'.path = s.path) (hm : s'.msg = s.msg) (hb : s'.buffers = s.buffers) (ht : s'.strm = s.strm) :
    GStep w h { w with fs := fs, gzs := upd w.gzs b (some s') } h b [] := by
  have hs' : ({ w with fs := fs, gzs := upd w.gzs b (some s') } : World).gz h b = some s' :=
    gz_upd_same (w := { w with fs := fs }) hs s'
  refine gstep_mk hs hs' ht (fun c hc _ => by simp [upd_ne _ _ _ _ hc]) (fun _ _ => rfl) rfl
    (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) (fun _ _ e => e) rfl rfl rfl (Nat.le_refl _) (fun c hc _ => ?_)
  simp only [GzOwned, hs', hs, hp, hm, hb, ht] at hc ⊢
  exact hc

/-- New output count, next pointer, position and skip keep the fields of a read handle when the positions stay in
range, the output stays inside the `out` buffer, and a pending skip has no output before it. -/
theorem shape_seek {h : Heap} {s : GzState} (sh : GzShape h s) (hr : s.mode = GZ_READ) (hv : UInt32)
    (nx : Ival BPtr) (p k : Int64) (hw : Int32) (hhow : hw = LOOK ∨ hw = ZlibNg.Gz.COPY ∨ hw = GZIP)
    (hk0 : 0 ≤ k.toInt) (hpk : p.toInt + k.toInt ≤ GZ_OFF_MAX.toInt)
    (hp : -GZ_OFF_MAX.toInt ≤ p.toInt)
    (hout : hv = 0 ∨ (s.size ≠ 0 ∧ ∀ c base, GzBufs h s c base →
      ∃ q, nx = .val q ∧ Inside c base (inSize s) (inSize s + outSize s) q hv.toNat))
    (hkh : k ≠ 0 → hv = 0) (hlook : s.size = 0 → hw = LOOK) (hph : p.toInt + hv.toNat ≤ GZ_OFF_MAX.toInt)
    (hlk : hw = LOOK → s.direct ≠ 0 → p.toInt + hv.toNat ≤ 0) (hgd : hw = GZIP → s.direct = 0)
    (hcp : hw = ZlibNg.Gz.COPY → ∀ z, h.streams s.strm = some z → z.avail_in = 0) :
    GzShape h { s with «have» := hv, next := nx, pos := p, skip := k, how := hw } := by
  have R := sh.read hr
  refine ⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, sh.size,
    ⟨hk0, hpk, hp, fun e => absurd (hr.symm.trans e) read_ne_write⟩, ⟨sh.msg.msg, sh.msg.mem⟩,
    fun _ => ⟨hhow, fun hsz => ?_, fun hsz => ?_, fun hk => ?_, fun hz => (R.fresh hz).of_strm rfl, hlook, hph, hlk, hgd, hcp⟩,
    fun e => absurd (hr.symm.trans e) read_ne_write,
    fun hz => sh.dead hz⟩
  · obtain ⟨c, base, z, hb, hi, hz, -, hai, hreg, hmsg⟩ := R.bufs hsz
    refine ⟨c, base, z, ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩, hi, hz, ?_, hai, hreg, hmsg⟩
    rcases hout with e | ⟨-, hq⟩
    · exact Or.inl e
    · exact Or.inr (hq c base hb)
  · rcases hout with e | ⟨e, -⟩
    · exact e
    · exact absurd hsz e
  · show p.toInt + k.toInt + (hv.toNat : Int) ≤ GZ_OFF_MAX.toInt
    rw [hkh hk]; simpa using hpk

/-- A read handle stays one after such a store. -/
theorem invR_seek {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (hvv : UInt32) (nx : Ival BPtr) (p k : Int64) (hw : Int32)
    (hhow : hw = LOOK ∨ hw = ZlibNg.Gz.COPY ∨ hw = GZIP) (hk0 : 0 ≤ k.toInt)
    (hpk : p.toInt + k.toInt ≤ GZ_OFF_MAX.toInt) (hp : -GZ_OFF_MAX.toInt ≤ p.toInt)
    (hout : hvv = 0 ∨ (s.size ≠ 0 ∧ ∀ c base, GzBufs h s c base →
      ∃ q, nx = .val q ∧ Inside c base (inSize s) (inSize s + outSize s) q hvv.toNat))
    (hkh : k ≠ 0 → hvv = 0) (hlook : s.size = 0 → hw = LOOK) (hph : p.toInt + hvv.toNat ≤ GZ_OFF_MAX.toInt)
    (hlk : hw = LOOK → s.direct ≠ 0 → p.toInt + hvv.toNat ≤ 0) (hgd : hw = GZIP → s.direct = 0)
    (hcp : hw = ZlibNg.Gz.COPY → ∀ z, h.streams s.strm = some z → z.avail_in = 0) :
    GzInvR { w with gzs := upd w.gzs b (some { s with «have» := hvv, next := nx, pos := p, skip := k, how := hw }) } h
      (some b) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  exact (keeps_store hs (HLess.refl h) (fun _ e => e)
    (shape_seek sh (modeOf hs hv.2.1) hvv nx p k hw hhow hk0 hpk hp hout hkh hlook hph hlk hgd hcp) hn rfl rfl).1 hv

/-- The stream of `avail0` has no input. -/
theorem avail0_zero {h : Heap} {i : Nat} {z z' : ZStream} (hz : (avail0 h i z).streams i = some z') :
    z'.avail_in = 0 := by
  simp [avail0] at hz; rw [← hz]

/-! ## `seekSkip` -/

theorem ival_get_val {α : Type} (p : α) (H : Heap) : Ival.get (.val p) H = .ok (p, H) := rfl


theorem lseekG_app (w : World) (h : Heap) (fd : Int32) (off : Int64) (wh : Int32) :
    lseekG fd off wh w h = .ok (((w.fs.lseekCall fd off wh).1, { w with fs := (w.fs.lseekCall fd off wh).2 }), h) := by
  simp [lseekG, modifyFs]

theorem errSt_ok (t : GzState) : errSt t ZlibNg.Inflate.Z_OK = { t with msg := .val .null, err := ZlibNg.Inflate.Z_OK } := by
  simp [errSt]

/-- The output left in a read handle lies in its `out` buffer. -/
theorem hout_self {h : Heap} {s : GzState} (R : GzRead h s) :
    s.«have» = 0 ∨ (s.size ≠ 0 ∧ ∀ c base, GzBufs h s c base →
      ∃ q, s.next = .val q ∧ Inside c base (inSize s) (inSize s + outSize s) q s.«have».toNat) := by
  by_cases hz : s.«have» = 0
  · exact Or.inl hz
  · have hsz : s.size ≠ 0 := fun e => hz (R.nobuf e)
    refine Or.inr ⟨hsz, fun c base hb => ?_⟩
    obtain ⟨c', base', z, hb', -, -, hhv, -, -⟩ := R.bufs hsz
    have e1 := hb.buffers; rw [hb'.buffers] at e1; cases e1
    exact hhv.resolve_left hz


/-- `seekSkip` on a read handle with an offset `off ≥ 0` whose target `x.pos + off` is at most `GZ_OFF_MAX`. -/
theorem seekSkip_read {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (off pos : Int64) (h0 : 0 ≤ off.toInt)
    (hmx : s.pos.toInt + off.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekSkip (some b) off pos) (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b [] ∧ (LookIdle w h (some b) → LookIdle W H (some b))) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  have P := sh.pos
  obtain ⟨db, hdb⟩ := gz_live hs
  have hN := nOf_toNat s.«have» off h0
  generalize hn' : (if (GT_OFF s.«have» || decide (Int64.ofNat s.«have».toNat > off)) = true then off.toUInt64.toUInt32
    else s.«have») = n at hN
  have hmx' := gzmax
  -- no output skipped: `skip = off`, with no output left or nothing to skip
  have none : (off ≠ 0 → s.«have» = 0) →
      GSat w h (do wrG (some b) fun s => { s with skip := off }; pure pos)
        (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b [] ∧ (LookIdle w h (some b) → LookIdle W H (some b))) := by
    intro hkh
    refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
    refine GSat.pure ?_
    have e : ({ s with skip := off } : GzState) =
        { s with «have» := s.«have», next := s.next, pos := s.pos, skip := off, how := s.how } := rfl
    refine ⟨?_, gstep_st hs w.fs rfl rfl rfl rfl, fun hi => idle_same hi hs (gz_upd_same hs _) rfl rfl rfl rfl⟩
    rw [e]
    exact invR_seek hv hs s.«have» s.next s.pos off s.how R.how h0 hmx P.3 (hout_self R) hkh R.look R.pos_have
      R.look_pos R.gzip_direct R.copy_in
  unfold seekSkip
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => ?_) fun hc => by simp [hr] at hc
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hz0
    have hz : s.«have» ≠ 0 := by simpa using hz0
    apply GSat.ite
    · intro ho0
      have ho : off.toInt ≠ 0 := fun e => (by simpa using ho0 : off ≠ 0) (Int64.toInt_inj.mp (by simpa using e))
      refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
      simp only [hn']
      have hn0 : n.toNat ≠ 0 := by
        rw [hN]; have : s.«have».toNat ≠ 0 := fun e => hz (UInt32.toNat_inj.mp (by simpa using e)); omega
      have hsz : s.size ≠ 0 := fun e => hz (R.nobuf e)
      obtain ⟨c, base, z, hb, -, -, hhv, -, -⟩ := R.bufs hsz
      obtain ⟨q, hq, k, hqk, hlo, hhi⟩ := hhv.resolve_left hz
      obtain ⟨d, hd, hds⟩ := hb.fits
      have hnl : n.toNat ≤ s.«have».toNat := by omega
      have hno : n.toNat ≤ off.toInt.toNat := by omega
      have hdc : h.bytes c = some d := hd
      let s1 : GzState := { s with «have» := s.«have» - n }
      refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
      refine GSat.bind (GSat.of_eq (ldGz_upd hdb w s1) ?_)
      refine GSat.bind (GSat.lm ⟨q, h, by show Ival.get s.next h = _; rw [hq]; rfl, ?_⟩)
      rw [hqk]
      refine GSat.bind (GSat.lm ⟨_, h, addH hdc (off := base + k) n.toNat (by omega), ?_⟩)
      refine GSat.bind (GSat.of_eq (wrG_upd hdb w s1 _) ?_)
      refine GSat.bind (GSat.of_eq (rdG_upd hdb w _ _) ?_)
      have hpn : -(2 ^ 63 : Int) ≤ s.pos.toInt + (n.toNat : Int) ∧ s.pos.toInt + (n.toNat : Int) < 2 ^ 63 := by
        have := P.3; constructor <;> omega
      refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hpn.1 hpn.2 h, ?_⟩)
      refine GSat.bind (GSat.of_eq (wrG_upd hdb w _ _) ?_)
      have hon : -(2 ^ 63 : Int) ≤ off.toInt - (n.toNat : Int) ∧ off.toInt - (n.toNat : Int) < 2 ^ 63 := by
        have := off.toInt_lt; constructor <;> omega
      refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hon.1 hon.2 h, ?_⟩)
      refine GSat.bind (GSat.of_eq (wrG_upd hdb w _ _) ?_)
      refine GSat.pure ?_
      have e2 := toInt_ofInt' hpn.1 hpn.2
      have e3 := toInt_ofInt' hon.1 hon.2
      have hm1 : (s.«have» - n).toNat = s.«have».toNat - n.toNat := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hnl)]
      refine ⟨?_, gstep_st hs w.fs rfl rfl rfl rfl, fun hi => idle_same hi hs (gz_upd_same hs _) rfl rfl rfl rfl⟩
      refine invR_seek hv hs (s.«have» - n) (.val (.ref (.heap c) (base + k + n.toNat)))
        (Int64.ofInt (s.pos.toInt + (n.toNat : Int))) (Int64.ofInt (off.toInt - (n.toNat : Int))) s.how R.how
        (by rw [e3]; omega) (by rw [e2, e3]; omega) (by rw [e2]; have := P.3; omega) ?_ ?_ R.look
        (by rw [e2, hm1]; have := R.pos_have; omega) (fun h1 h2 => by rw [e2, hm1]; have := R.look_pos h1 h2; omega)
        R.gzip_direct R.copy_in
      · by_cases hz2 : s.«have» - n = 0
        · exact Or.inl hz2
        · refine Or.inr ⟨hsz, fun c' base' hb' => ?_⟩
          have e1 := hb'.buffers; rw [hb.buffers] at e1; cases e1
          exact ⟨_, rfl, k + n.toNat, by rw [Nat.add_assoc], by omega, by rw [hm1]; omega⟩
      · intro hk
        have hk' : off.toInt - (n.toNat : Int) ≠ 0 := by
          intro e; apply hk; rw [e]; rfl
        apply UInt32.toNat_inj.mp
        rw [hm1]; simp; omega
    · intro ho0
      exact none fun hk => absurd (by simpa using ho0) hk
  · intro hz0
    exact none fun _ => by simpa using hz0

/-- `seekSkip` on a write handle: only the skip is recorded. -/
theorem seekSkip_write {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (off pos : Int64) (h0 : 0 ≤ off.toInt)
    (hmx : s.pos.toInt + off.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekSkip (some b) off pos) (fun _ W H => GzInvWS W H (some b) ∧ GStep w h W H b []) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hw := modeOf hs hv.2.1
  have P := sh.pos
  unfold seekSkip
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hc; simp [hw, GZ_READ, GZ_WRITE] at hc
  intro _
  refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
  refine GSat.pure ?_
  refine ⟨?_, gstep_st hs w.fs rfl rfl rfl rfl⟩
  have sh' : GzShape h { s with skip := off } := by
    refine ⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, sh.size, ⟨h0, hmx, P.3, P.4⟩,
      ⟨sh.msg.msg, sh.msg.mem⟩, fun hr => absurd (hr.symm.trans hw) read_ne_write,
      fun hw' => ⟨fun hsz => ?_, (sh.write hw').nobuf, (sh.write hw').have0⟩, fun hz => sh.dead hz⟩
    obtain ⟨c, base, z, hb, hz, W⟩ := (sh.write hw').bufs hsz
    exact ⟨c, base, z, ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩, hz, ⟨W.1, W.2, W.3, W.4, W.5⟩⟩
  exact ⟨⟨b, _, rfl, gz_upd_same hs _, sh', hn⟩, ⟨b, _, rfl, gz_upd_same hs _, hw⟩, wfw_store hv.2.2 hs _ rfl⟩

/-- A change of the file system only is a step of a call. -/
theorem gstep_fs {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (fs : Fs) :
    GStep w h { w with fs := fs } h b [] := by
  have := gstep_st (s' := s) hs fs rfl rfl rfl rfl
  rwa [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this

/-- A step that frees blocks of the file (`HLess`), changes only its stream (keeping the stream's state) and its
`gz_state` (keeping its path, buffers and stream, and its message or clearing it). -/
theorem gstep_less {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hs' : W.gz H b = some s') (hl : HLess h H) (hst : ∀ i, i ≠ s.strm → H.streams i = h.streams i)
    {z z' : ZStream} (hz : h.streams s.strm = some z) (hz' : H.streams s.strm = some z') (hzs : z'.state = z.state)
    (hby : ∀ c, c ∉ GzOwned w h (some b) → H.bytes c = h.bytes c) (hg : ∀ c, c ≠ b → W.gzs c = w.gzs c)
    (hp : s'.path = s.path) (hm : s'.msg = s.msg ∨ s'.msg = .val .null) (hb : s'.buffers = s.buffers)
    (ht : s'.strm = s.strm) : GStep w h W H b [] := by
  refine gstep_mk hs hs' ht (fun c hc _ => hg c hc) hst hl.hdr
    (fun c _ hno => ⟨hby c hno, by rw [hl.istates], by rw [hl.iallocs], by rw [hl.dstates], by rw [hl.dallocs]⟩)
    hl.consts hl.crc hl.x2n hl.base (by rw [hl.next]; exact Nat.le_refl _) (fun c hc _ => ?_)
  rcases hm with hm | hm
  · simp only [GzOwned, hs', hs, hp, hm, hb, ht, hz, hz', hzs] at hc ⊢
    exact hc
  · simp only [GzOwned, hs', hs, hp, hm, hb, ht, hz, hz', hzs, List.mem_append] at hc ⊢
    simp at hc
    rcases hc with ((h1 | h2) | h3) | h4
    · exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_singleton.mpr h1))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
    · exact Or.inl (Or.inr h3)
    · exact Or.inr h4

theorem freeMsg_bytes_own {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (c : Nat)
    (hc : c ∉ GzOwned w h (some b)) : (freeMsg h s).bytes c = h.bytes c := by
  refine freeMsg_bytes h s c fun hm => hc (ownL_owned hs c ?_)
  unfold ownL; simp only [List.mem_append]; exact Or.inl (Or.inr hm)


/-! ## `seekOff`, `seekRest` -/

/-- `seekOff` on a read handle with a target `pos` in `[x.pos, GZ_OFF_MAX]` at most `GZ_OFF_MAX` past `x.pos`. -/
theorem seekOff_read {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (off pos : Int64) (h0 : s.pos.toInt ≤ pos.toInt) (hmx : pos.toInt ≤ GZ_OFF_MAX.toInt)
    (hd : pos.toInt - s.pos.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekOff (some b) off pos) (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b [] ∧ (LookIdle w h (some b) → LookIdle W H (some b))) := by
  have hmx' := gzmax
  unfold seekOff
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  have hb : -(2 ^ 63 : Int) ≤ pos.toInt - s.pos.toInt ∧ pos.toInt - s.pos.toInt < 2 ^ 63 := by
    constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb.1 hb.2 h, ?_⟩)
  have e := toInt_ofInt' hb.1 hb.2
  exact seekSkip_read hv hs _ pos (by rw [e]; omega) (by rw [e]; omega)

/-- `seekOff` on a write handle with a target `pos` in `[x.pos, GZ_OFF_MAX]`. -/
theorem seekOff_write {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (off pos : Int64) (h0 : s.pos.toInt ≤ pos.toInt) (hmx : pos.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekOff (some b) off pos) (fun _ W H => GzInvWS W H (some b) ∧ GStep w h W H b []) := by
  have hmx' := gzmax
  have P := (inv_of hs hv.1).1.pos
  have P4 := P.4 (modeOf hs hv.2.1)
  unfold seekOff
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  have hb : -(2 ^ 63 : Int) ≤ pos.toInt - s.pos.toInt ∧ pos.toInt - s.pos.toInt < 2 ^ 63 := by
    constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb.1 hb.2 h, ?_⟩)
  have e := toInt_ofInt' hb.1 hb.2
  exact seekSkip_write hv hs _ pos (by rw [e]; omega) (by rw [e]; omega)

/-- `seekRest` on a read handle with a target `pos` in `[0, GZ_OFF_MAX]` at most `GZ_OFF_MAX` past `x.pos`. -/
theorem seekRest_read {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (off pos : Int64) (h0 : 0 ≤ pos.toInt) (hmx : pos.toInt ≤ GZ_OFF_MAX.toInt)
    (hd : pos.toInt - s.pos.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekRest (some b) off pos) (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b [] ∧ (LookIdle w h (some b) → LookIdle W H (some b))) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨z, hz⟩ := sh.strm
  unfold seekRest
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro hc; simp [hr] at hc
    intro _
    rcases gzrewind_read hs hr sh.msg hn hz with e | ⟨fs', hle, e⟩ | ⟨fs', hle, e⟩
    · exact GSat.bind (GSat.of_eq e (GSat.pure ⟨hv, GStep.refl w h b [], id⟩))
    · exact GSat.bind (GSat.of_eq e (GSat.pure ⟨keepsR_fs hv hle, gstep_fs hs fs',
        fun hi => idle_same hi hs (show ({ w with fs := fs' } : World).gz h b = some s from hs) rfl rfl rfl rfl⟩))
    · refine GSat.bind (GSat.of_eq e ?_)
      apply GSat.ite
      · intro hc; simp at hc
      intro _
      obtain ⟨sh', hn'⟩ := reset_keep sh hr hn hz
      obtain ⟨db, hdb⟩ := gz_live hs
      have hv1 : GzInvR { w with fs := fs', gzs := upd w.gzs b (some (rstSt s)) } (avail0 (freeMsg h s) s.strm z)
          (some b) :=
        (keeps_store (w := { w with fs := fs' }) hs ((HLess.free h s).trans (HLess.av0 _ _ _))
          (freeMsg_av0_bytes hn _ _) sh' hn' rfl rfl).1 (keepsR_fs hv hle)
      have hs1 : ({ w with fs := fs', gzs := upd w.gzs b (some (rstSt s)) } : World).gz
          (avail0 (freeMsg h s) s.strm z) b = some (rstSt s) := by
        unfold World.gz; rw [freeMsg_av0_bytes hn _ _ db hdb]; simp
      have g1 : GStep w h { w with fs := fs', gzs := upd w.gzs b (some (rstSt s)) } (avail0 (freeMsg h s) s.strm z) b [] :=
        gstep_less hs hs1 ((HLess.free h s).trans (HLess.av0 _ _ _))
          (fun i hi => by simp only [avail0]; rw [upd_ne _ _ _ _ hi, freeMsg_streams]) hz
          (z' := { z with avail_in := 0 }) (by simp [avail0]) rfl
          (fun c hc => freeMsg_bytes_own hs c hc) (fun c hc => by simp [upd_ne _ _ _ _ hc]) rfl (Or.inr rfl) rfl rfl
      have hpos0 : (rstSt s).pos.toInt = 0 := rfl
      refine (seekOff_read hv1 hs1 off pos (by rw [hpos0]; omega) hmx (by rw [hpos0]; omega)).mono fun _ W H q => ?_
      exact ⟨q.1, g1.trans q.2.1 ⟨s, hs⟩ ⟨_, hs1⟩,
        fun _ => q.2.2 (idle_zero hs1 fun z' hz' => avail0_zero hz')⟩
  · intro hnn
    have hnn' : s.pos.toInt ≤ pos.toInt := by
      have := mt Int64.lt_iff_toInt_lt.mpr hnn; omega
    exact seekOff_read hv hs off pos hnn' hmx hd

/-- `seekRest` on a write handle with a target `pos` at most `GZ_OFF_MAX`. -/
theorem seekRest_write {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (off pos : Int64) (hmx : pos.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekRest (some b) off pos) (fun _ W H => GzInvWS W H (some b) ∧ GStep w h W H b []) := by
  have hw := modeOf hs hv.2.1
  unfold seekRest
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro _; exact GSat.pure ⟨hv, GStep.refl w h b []⟩
    · intro hc; simp [hw, GZ_READ, GZ_WRITE] at hc
  · intro hnn
    have hnn' : s.pos.toInt ≤ pos.toInt := by
      have := mt Int64.lt_iff_toInt_lt.mpr hnn; omega
    exact seekOff_write hv hs off pos hnn' hmx

/-! ## `seekRaw`, `seekTail` -/

/-- `seekRaw` on a read handle in copy mode with a target `pos` in `[0, GZ_OFF_MAX]` at most `GZ_OFF_MAX` past
`x.pos`: the `lseek` offset `pos - x.pos - x.have` fits since `x.pos + x.have <= GZ_OFF_MAX`. -/
theorem seekRaw_read {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (pos : Int64) (h0 : 0 ≤ pos.toInt) (hmx : pos.toInt ≤ GZ_OFF_MAX.toInt)
    (hd : pos.toInt - s.pos.toInt ≤ GZ_OFF_MAX.toInt) (hcopy : s.how = ZlibNg.Gz.COPY) :
    GSat w h (seekRaw (some b) pos) (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b [] ∧ (LookIdle w h (some b) → LookIdle W H (some b))) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have P := sh.pos
  have P1 := P.1
  have P2 := P.2
  have R := sh.read hr
  have Rph := R.pos_have
  obtain ⟨z, hz⟩ := sh.strm
  obtain ⟨db, hdb⟩ := gz_live hs
  have hmx' := gzmax
  have hH := s.«have».toNat_lt
  unfold seekRaw
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  have hb1 : -(2 ^ 63 : Int) ≤ pos.toInt - s.pos.toInt ∧ pos.toInt - s.pos.toInt < 2 ^ 63 := by
    constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb1.1 hb1.2 h, ?_⟩)
  have e1 := toInt_ofInt' hb1.1 hb1.2
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  have hb2 : -(2 ^ 63 : Int) ≤ (Int64.ofInt (pos.toInt - s.pos.toInt)).toInt - Int.ofNat s.«have».toNat ∧
      (Int64.ofInt (pos.toInt - s.pos.toInt)).toInt - Int.ofNat s.«have».toNat < 2 ^ 63 := by
    rw [e1]; simp only [Int.ofNat_eq_natCast]; constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb2.1 hb2.2 h, ?_⟩)
  refine GSat.bind (GSat.of_eq (lseekG_app w h _ _ _) ?_)
  generalize Int64.ofInt ((Int64.ofInt (pos.toInt - s.pos.toInt)).toInt - Int.ofNat s.«have».toNat) = L0
  have hle := GzOpen.lseekCall_le w.fs s.fd L0 SEEK_CUR
  generalize w.fs.lseekCall s.fd L0 SEEK_CUR = L at hle ⊢
  obtain ⟨ret, fs1⟩ := L
  apply GSat.ite
  · intro _; exact GSat.pure ⟨keepsR_fs hv hle, gstep_fs hs fs1,
      fun hi => idle_same hi hs (show ({ w with fs := fs1 } : World).gz h b = some s from hs) rfl rfl rfl rfl⟩
  intro _
  have hs1 : ({ w with fs := fs1 } : World).gz h b = some s := hs
  let s1 : GzState := { s with «have» := 0, eof := 0, past := 0, skip := 0 }
  refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb _ _ _) ?_)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb _ _ _) ?_)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb _ _ _) ?_)
  have e := gz_error_null_app (s := s1) (gz_upd_same hs1 s1) ⟨sh.msg.msg, sh.msg.mem⟩ (msg_ne_b hn) ZlibNg.Inflate.Z_OK
  rw [errSt_ok] at e
  refine GSat.bind (GSat.of_eq e ?_)
  have hdb1 : (freeMsg h s1).bytes b = some db := freeMsg_bytes_b hn hdb
  refine GSat.bind (GSat.of_eq (strmOf_upd hdb1 _ _) ?_)
  have hz1 : (freeMsg h s1).streams s.strm = some z := by rw [freeMsg_streams]; exact hz
  refine GSat.bind (GSat.lm ⟨(), _, wrZ_app hz1 _, ?_⟩)
  have hdb2 : (avail0 (freeMsg h s) s.strm z).bytes b = some db := hdb1
  refine GSat.bind (GSat.of_eq (wrG_upd hdb2 _ _ _) ?_)
  refine GSat.pure ?_
  simp only [InflateInv.upd_upd]
  obtain ⟨sh', hn'⟩ := reset_keep sh hr hn hz
  have shG := shape_seek sh' hr 0 s.next pos 0 s.how R.how (by simp)
    (by simp; omega) (by omega) (Or.inl rfl) (fun _ => rfl) R.look (by simp; omega)
    (fun e => absurd (hcopy.symm.trans e) (by decide)) (fun e => absurd (hcopy.symm.trans e) (by decide))
    (fun _ z' hz' => by
      change (upd (freeMsg h s).streams s.strm (some { z with avail_in := 0 })) s.strm = some z' at hz'
      simp only [upd_same, Option.some.injEq] at hz'; rw [← hz'])
  have hl : HLess h (avail0 (freeMsg h s) s.strm z) := (HLess.free h s).trans (HLess.av0 _ _ _)
  have hsG := gz_upd_same (w := { w with fs := fs1 }) (h := avail0 (freeMsg h s) s.strm z) (s := s)
    (by unfold World.gz; rw [hdb2]; unfold World.gz at hs; rw [hdb] at hs; exact hs)
    { rstSt s with «have» := 0, next := s.next, pos := pos, skip := 0, how := s.how }
  refine ⟨(keeps_store (w := { w with fs := fs1 }) hs hl (freeMsg_av0_bytes hn _ _) shG hn' rfl rfl).1
    (keepsR_fs hv hle), ?_⟩
  refine ⟨gstep_less hs hsG hl (fun i hi => by simp only [avail0]; rw [upd_ne _ _ _ _ hi, freeMsg_streams]) hz
    (z' := { z with avail_in := 0 }) (by simp [avail0]) rfl (fun c hc => freeMsg_bytes_own hs c hc)
    (fun c hc => by simp [upd_ne _ _ _ _ hc]) rfl (Or.inr rfl) rfl rfl, fun _ => ?_⟩
  exact idle_zero hsG fun z' hz' => avail0_zero hz'

/-- `seekTail` on a read handle with a target `pos` in `[0, GZ_OFF_MAX]` at most `GZ_OFF_MAX` past `x.pos`. -/
theorem seekTail_read {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (off pos : Int64) (h0 : 0 ≤ pos.toInt) (hmx : pos.toInt ≤ GZ_OFF_MAX.toInt)
    (hd : pos.toInt - s.pos.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekTail (some b) off pos) (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b [] ∧ (LookIdle w h (some b) → LookIdle W H (some b))) := by
  have rest := seekRest_read hv hs off pos h0 hmx hd
  unfold seekTail
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro hcp0
      exact seekRaw_read hv hs pos h0 hmx hd (by simpa using hcp0)
    · intro _; exact rest
  · intro _; exact rest

/-- `seekTail` on a write handle with a target `pos` at most `GZ_OFF_MAX`. -/
theorem seekTail_write {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (off pos : Int64) (hmx : pos.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekTail (some b) off pos) (fun _ W H => GzInvWS W H (some b) ∧ GStep w h W H b []) := by
  have hw := modeOf hs hv.2.1
  unfold seekTail
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hc; simp [hw, GZ_READ, GZ_WRITE] at hc
  intro _
  exact seekRest_write hv hs off pos hmx

/-- The post of the parts of `gzseek64`: the invariant `I` and a step of the call. -/
abbrev SPost (I : World → Heap → Prop) (w : World) (h : Heap) (b : Nat) : Int64 → World → Heap → Prop :=
  fun _ W H => I W H ∧ GStep w h W H b []

/-! ## `seekNeg`, `seekPos`, `gzseek64` -/

/-- `seekNeg` with a target `pos` in `[0, GZ_OFF_MAX]`: a refusal, or `seekTail` with `pos` at most `GZ_OFF_MAX` past
`x.pos`. -/
theorem seekNeg_gen {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (P : GzPos s)
    (I : World → Heap → Prop) (hI : I w h)
    (hT : ∀ off pos : Int64, 0 ≤ pos.toInt → pos.toInt ≤ GZ_OFF_MAX.toInt →
      pos.toInt - s.pos.toInt ≤ GZ_OFF_MAX.toInt → GSat w h (seekTail (some b) off pos) (SPost I w h b))
    (off pos : Int64) (h0 : 0 ≤ pos.toInt) (hmx : pos.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekNeg (some b) off pos) (SPost I w h b) := by
  have hmx' := gzmax
  have P3 := P.3
  have hpl := s.pos.toInt_lt
  unfold seekNeg
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hneg
    have hneg' : s.pos.toInt < 0 := by rw [Int64.lt_iff_toInt_lt] at hneg; simpa using hneg
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    have hb : -(2 ^ 63 : Int) ≤ GZ_OFF_MAX.toInt + s.pos.toInt ∧ GZ_OFF_MAX.toInt + s.pos.toInt < 2 ^ 63 := by
      constructor <;> omega
    refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb.1 hb.2 h, ?_⟩)
    apply GSat.ite
    · intro _; exact GSat.pure ⟨hI, GStep.refl w h b []⟩
    · intro hc
      rw [gt_iff_lt, Int64.lt_iff_toInt_lt, toInt_ofInt' hb.1 hb.2] at hc
      exact hT off pos h0 hmx (by omega)
  · intro hnn
    have hnn' : 0 ≤ s.pos.toInt := by
      have := mt Int64.lt_iff_toInt_lt.mpr hnn; simp at this; omega
    exact hT off pos h0 hmx (by omega)

/-- `seekPos` from a position `p` in `[-GZ_OFF_MAX, GZ_OFF_MAX]`: a refusal, or `seekNeg` with a target in
`[0, GZ_OFF_MAX]`. -/
theorem seekPos_gen {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (P : GzPos s)
    (I : World → Heap → Prop) (hI : I w h)
    (hT : ∀ off pos : Int64, 0 ≤ pos.toInt → pos.toInt ≤ GZ_OFF_MAX.toInt →
      pos.toInt - s.pos.toInt ≤ GZ_OFF_MAX.toInt → GSat w h (seekTail (some b) off pos) (SPost I w h b))
    (off p : Int64) (hp0 : -GZ_OFF_MAX.toInt ≤ p.toInt) (hp1 : p.toInt ≤ GZ_OFF_MAX.toInt) :
    GSat w h (seekPos (some b) off p) (SPost I w h b) := by
  have hmx' := gzmax
  have hol := off.toInt_lt
  have hog := off.le_toInt
  have hmin : (Int64.minValue).toInt = -9223372036854775808 := by decide
  have done : GSat w h (pure (-1)) (SPost I w h b) := GSat.pure ⟨hI, GStep.refl w h b []⟩
  -- the refusal before the start, then the target
  have tail : (0 < p.toInt → off.toInt ≤ GZ_OFF_MAX.toInt - p.toInt) → GSat w h (do
      if off < (← lm (chkI64 (-p.toInt))) then
        return -1
      let pos ← lm (chkI64 (p.toInt + off.toInt))
      seekNeg (some b) off pos) (SPost I w h b) := by
    intro hup
    have hb : -(2 ^ 63 : Int) ≤ -p.toInt ∧ -p.toInt < 2 ^ 63 := by constructor <;> omega
    refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb.1 hb.2 h, ?_⟩)
    apply GSat.ite
    · intro _; exact done
    · intro hc
      have hc' : -p.toInt ≤ off.toInt := by
        have := mt Int64.lt_iff_toInt_lt.mpr hc; rw [toInt_ofInt' hb.1 hb.2] at this; omega
      have hupp : p.toInt + off.toInt ≤ GZ_OFF_MAX.toInt := by
        by_cases hpp : 0 < p.toInt
        · have := hup hpp; omega
        · omega
      have hb2 : -(2 ^ 63 : Int) ≤ p.toInt + off.toInt ∧ p.toInt + off.toInt < 2 ^ 63 := by
        constructor <;> omega
      refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb2.1 hb2.2 h, ?_⟩)
      have e := toInt_ofInt' hb2.1 hb2.2
      exact seekNeg_gen hs P I hI hT off _ (by rw [e]; omega) (by rw [e]; omega)
  unfold seekPos
  apply GSat.ite
  · intro hpos
    have hpos' : 0 < p.toInt := by rw [gt_iff_lt, Int64.lt_iff_toInt_lt] at hpos; simpa using hpos
    have hb : -(2 ^ 63 : Int) ≤ GZ_OFF_MAX.toInt - p.toInt ∧ GZ_OFF_MAX.toInt - p.toInt < 2 ^ 63 := by
      constructor <;> omega
    refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb.1 hb.2 h, ?_⟩)
    apply GSat.ite
    · intro _; exact done
    · intro hc
      rw [gt_iff_lt, Int64.lt_iff_toInt_lt, toInt_ofInt' hb.1 hb.2] at hc
      exact tail fun _ => by omega
  · intro hnp
    have hnp' : p.toInt ≤ 0 := by
      have := mt Int64.lt_iff_toInt_lt.mpr hnp; simp at this; omega
    exact tail fun e => absurd e (by omega)

/-- **`gzseek64`** on an open file, from the parts: the invariant `I` holds before, and after each `seekTail` with a
target in `[0, GZ_OFF_MAX]` at most `GZ_OFF_MAX` past `x.pos`. Nothing is stored before `seekTail`. -/
theorem gzseek64_gen {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hmode : s.mode = GZ_READ ∨ s.mode = GZ_WRITE) (P : GzPos s) (I : World → Heap → Prop) (hI : I w h)
    (hT : ∀ off pos : Int64, 0 ≤ pos.toInt → pos.toInt ≤ GZ_OFF_MAX.toInt →
      pos.toInt - s.pos.toInt ≤ GZ_OFF_MAX.toInt → GSat w h (seekTail (some b) off pos) (SPost I w h b))
    (off : Int64) (wh : Int32) :
    GSat w h (gzseek64 (some b) off wh) (SPost I w h b) := by
  have hmx' := gzmax
  have P1 := P.1
  have P2 := P.2
  have P3 := P.3
  have hpl := s.pos.toInt_lt
  have hsl := s.skip.toInt_lt
  have done : GSat w h (pure (-1)) (SPost I w h b) := GSat.pure ⟨hI, GStep.refl w h b []⟩
  unfold gzseek64
  simp only [show (some b == none) = false from rfl, Bool.false_eq_true, ite_false]
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hc; rcases hmode with hm | hm <;> simp [hm, GZ_READ, GZ_WRITE] at hc
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact done
  intro _
  apply GSat.ite
  · intro _; exact done
  intro _
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.pure ?_)
    exact seekPos_gen hs P I hI hT off 0 (by simp; omega) (by simp; omega)
  · intro _
    have K : ∀ add : Int64, 0 ≤ add.toInt → s.pos.toInt + add.toInt ≤ GZ_OFF_MAX.toInt →
        GSat w h (do
          let __do_lift ← rdG (some b) (·.pos)
          let pos ← lm (chkI64 (__do_lift.toInt + add.toInt))
          seekPos (some b) off pos) (SPost I w h b) := by
      intro add ha0 ha1
      refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
      have hb : -(2 ^ 63 : Int) ≤ s.pos.toInt + add.toInt ∧ s.pos.toInt + add.toInt < 2 ^ 63 := by
        constructor <;> omega
      refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb.1 hb.2 h, ?_⟩)
      have e := toInt_ofInt' hb.1 hb.2
      exact seekPos_gen hs P I hI hT off _ (by rw [e]; omega) (by rw [e]; omega)
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.pure ?_)
      exact K 0 (by simp) (by simp; omega)
    · intro _
      refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
      exact K s.skip P1 P2

/-! ## Read handles and write handles -/

/-- **`gzseek64` on a read handle**: returns, keeps the read invariant, and is a step of a call. -/
theorem gzseek64_read {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (off : Int64) (wh : Int32) :
    GSat w h (gzseek64 (some b) off wh)
      (SPost (fun W H => GzInvR W H (some b) ∧ (LookIdle w h (some b) → LookIdle W H (some b))) w h b) :=
  gzseek64_gen hs (Or.inl (modeOf hs hv.2.1)) (inv_of hs hv.1).1.pos _ ⟨hv, id⟩
    (fun off pos h0 h1 h2 => (seekTail_read hv hs off pos h0 h1 h2).mono fun _ _ _ q => ⟨⟨q.1, q.2.2⟩, q.2.1⟩) off wh

/-- **`gzseek64` on a write handle**: returns, keeps the write invariant, and is a step of a call. -/
theorem gzseek64_write {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (off : Int64) (wh : Int32) :
    GSat w h (gzseek64 (some b) off wh) (SPost (fun W H => GzInvWS W H (some b)) w h b) :=
  gzseek64_gen hs (Or.inr (modeOf hs hv.2.1)) (inv_of hs hv.1).1.pos _ hv
    (fun off pos _ h1 _ => seekTail_write hv hs off pos h1) off wh

theorem gzseek_eq (f : GzPtr) (off : Int64) (wh : Int32) : gzseek f off wh = gzseek64 f off wh := rfl

/-- `gzseek` on a read or write handle, with the invariant `I` of `gzseek64`. -/
theorem gzseek_of {w : World} {h : Heap} {b : Nat} {I : World → Heap → Prop} {off : Int64} {wh : Int32}
    (hm : GSat w h (gzseek64 (some b) off wh) (SPost I w h b)) :
    GSat w h (gzseek (some b) off wh) (SPost I w h b) := by
  rw [gzseek_eq]; exact hm

theorem seek64R_keeps : KeepsR SSeek64 := by
  intro w h w' h' f hv ⟨off, wh, r, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  obtain ⟨r2, w2, h2, e2, q, -⟩ := gzseek64_read hv hs off wh
  obtain ⟨-, rfl, rfl⟩ := gdet e e2
  exact q.1

theorem seekR_keeps : KeepsR SSeek := by
  intro w h w' h' f hv ⟨off, wh, r, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  obtain ⟨r2, w2, h2, e2, q, -⟩ := gzseek_of (gzseek64_read hv hs off wh)
  obtain ⟨-, rfl, rfl⟩ := gdet e e2
  exact q.1

theorem seek64W_keeps : KeepsW SSeek64 := by
  intro w h w' h' f hv ⟨off, wh, r, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  obtain ⟨r2, w2, h2, e2, q, -⟩ := gzseek64_write hv hs off wh
  obtain ⟨-, rfl, rfl⟩ := gdet e e2
  exact q

theorem seekW_keeps : KeepsW SSeek := by
  intro w h w' h' f hv ⟨off, wh, r, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  obtain ⟨r2, w2, h2, e2, q, -⟩ := gzseek_of (gzseek64_write hv hs off wh)
  obtain ⟨-, rfl, rfl⟩ := gdet e e2
  exact q

theorem seek64R_keepsI : KeepsRI SSeek64 := by
  intro w h w' h' f hv hi ⟨off, wh, r, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  obtain ⟨r2, w2, h2, e2, q, -⟩ := gzseek64_read hv hs off wh
  obtain ⟨-, rfl, rfl⟩ := gdet e e2
  exact ⟨q.1, q.2 hi⟩

theorem seekR_keepsI : KeepsRI SSeek := by
  intro w h w' h' f hv hi ⟨off, wh, r, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  obtain ⟨r2, w2, h2, e2, q, -⟩ := gzseek_of (gzseek64_read hv hs off wh)
  obtain ⟨-, rfl, rfl⟩ := gdet e e2
  exact ⟨q.1, q.2 hi⟩

theorem rewind_keepsRI : KeepsRI SRewind := by
  intro w h w' h' f hv hi ⟨r, e⟩
  refine ⟨rewind_keepsR w h w' h' f hv ⟨r, e⟩, ?_⟩
  obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨z, hz⟩ := sh.strm
  rcases gzrewind_read hs hr sh.msg hn hz with e' | ⟨fs', hle, e'⟩ | ⟨fs', hle, e'⟩ <;>
    obtain ⟨-, e1, e2⟩ := gdet e e' <;> rw [e1, e2]
  · exact hi
  · exact idle_same hi hs (show ({ w with fs := fs' } : World).gz h b = some s from hs) rfl rfl rfl rfl
  · obtain ⟨d, hd⟩ := gz_live hs
    refine idle_zero (s := rstSt s) ?_ fun z' hz' => avail0_zero hz'
    unfold World.gz; rw [freeMsg_av0_bytes hn _ _ d hd]; simp

end ZlibNgF.Proof.GzMode
