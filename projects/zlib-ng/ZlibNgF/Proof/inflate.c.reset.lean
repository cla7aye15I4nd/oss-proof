import ZlibNgF.Proof.«inflate.c.invariant»

/-!
# `inflateResetKeep`, `inflateReset`, `inflateReset2`, `inflatePrime` (`ZlibNgF`)

Exact runs on a live state (`Live`: what `inflateStateCheck` asks), and the invariant after each call. `inflateInit2`
uses `reset2_run` on the state it has just set up.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateReset
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Live setZS upd_upd ldState_app ldStream_app Shape Core Inv view CodeTarget)

theorem i32_shr4_toInt (w : Int32) : (w >>> 4).toInt = w.toInt / 16 := by
  have h1 : (w >>> 4).toInt = (w.toBitVec.sshiftRight 4).toInt := by
    show (w >>> 4).toBitVec.toInt = _
    rw [Int32.toBitVec_shiftRight]
    rfl
  rw [h1, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  rfl

theorem wrap_ok (w : Int32) : chkI32 ((w >>> 4).toInt + 5) = pure (Int32.ofInt ((w >>> 4).toInt + 5)) := by
  have a := Int32.le_toInt w
  have b := Int32.toInt_lt w
  rw [i32_shr4_toInt]
  unfold chkI32
  split
  · rfl
  · rename_i hh; exact absurd ⟨by omega, by omega⟩ hh

theorem wb_ok (v : Int32) (hv : ¬ (v != 0 && (decide (v < MIN_WBITS) || decide (v > MAX_WBITS))) = true) :
    v.toUInt32 ≤ 15 := by
  by_cases h0 : v = 0
  · subst h0; decide
  · have h1 : ¬ v < MIN_WBITS := by intro x; apply hv; simp [h0, x]
    have h2 : ¬ v > MAX_WBITS := by intro x; apply hv; simp [h0, x]
    simp only [gt_iff_lt, Int32.lt_iff_toInt_lt] at h1 h2
    have e1 : (MIN_WBITS).toInt = 8 := rfl
    have e2 : (MAX_WBITS).toInt = 15 := rfl
    rw [e1] at h1; rw [e2] at h2
    have hnn : 0 ≤ v := by rw [Int32.le_iff_toInt_le]; simp; omega
    rw [UInt32.le_iff_toNat_le, Int32.toNat_toUInt32_of_le hnn]
    rw [← Int32.toNat_toInt]
    have : (15 : UInt32).toNat = 15 := rfl
    rw [this]
    omega

/-! ## Exact runs -/

/-- `inflateResetKeep`'s change of the `z_stream`. -/
def rkZ (z : ZStream) (wrap : Int32) : ZStream :=
  { z with total_out := 0, total_in := 0, msg := .null, data_type := 0,
           adler := if wrap != 0 then (wrap &&& 1).toInt64.toUInt64 else z.adler }

/-- `inflateResetKeep`'s change of the state of block `b`. -/
def rkS (b : Nat) (st : InflateState) : InflateState :=
  { st with total := 0, mode := HEAD, check := ADLER32_INITIAL_VALUE, last := 0, havedict := 0, flags := -1,
            head := .val none, hold := 0, bits := 0, next := .val (.ref (.codes b) 0),
            distcode := .val (.ref (.codes b) 0), lencode := .val (.ref (.codes b) 0), back := -1 }

/-- `inflateReset`'s change of the state before it calls `inflateResetKeep`. -/
def rS (st : InflateState) : InflateState := { st with wbits := st.reqbits, wsize := 0, whave := 0, wnext := 0 }

theorem resetKeep_run {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st) :
    inflateResetKeep (some i) h = .ok (Z_OK, setZS h i (rkZ z st.wrap) b (rkS b st)) := by
  obtain ⟨d, hd⟩ := L.hd
  by_cases hw : st.wrap = 0 <;>
  simp [inflateResetKeep, bind_app, L.check, stateOf, rdZ, wrS, wrZ, L.hb, ldState, stState, ldStream, stStream,
      Heap.istate, hd, L.hst, L.hz, codesP, upd_upd, hw, rkZ, rkS, setZS]

theorem reset_run {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st) :
    inflateReset (some i) h = .ok (Z_OK, setZS h i (rkZ z st.wrap) b (rkS b (rS st))) := by
  have L1 := L.setS (rS st) rfl rfl L.lo L.hi
  have e := resetKeep_run L1
  simp only [rS] at e
  simp only [inflateReset, bind_app, L.check, L.stateOf, wrS, ldState_app L.istate, stState, L.istate,
    Bool.false_eq_true, ↓reduceIte, e]
  simp [setZS, upd_upd, rS]

/-- `inflateReset2`'s change of the state before it calls `inflateReset`. -/
def r2S (st : InflateState) (wrap : Int32) (wb : UInt32) : InflateState :=
  { st with wrap := wrap, wbits := wb, reqbits := wb }

/-- The end of `inflateReset2` after the checks. -/
theorem reset2_tail {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st)
    (wrap : Int32) (v : Int32) :
    (do
      wrS (some b) fun s => { s with wrap := wrap }
      wrS (some b) fun s => { s with wbits := v.toUInt32 }
      wrS (some b) fun s => { s with reqbits := v.toUInt32 }
      inflateReset (some i) : M Int32) h =
      .ok (Z_OK, setZS h i (rkZ z wrap) b (rkS b (rS (r2S st wrap v.toUInt32)))) := by
  have e := reset_run (L.setS (r2S st wrap v.toUInt32) rfl rfl L.lo L.hi)
  simp only [r2S, rS] at e
  obtain ⟨d, hd⟩ := L.hd
  simp only [bind_app, wrS, stState, ldState, Heap.istate, hd, L.hst, upd_same, upd_upd, e]
  simp only [setZS, upd_upd, rkS, rS, r2S]

theorem reset2_run {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st)
    (w : Int32) :
    inflateReset2 (some i) w h = .ok (Z_STREAM_ERROR, h) ∨
    ∃ wrap wb, wb ≤ 15 ∧
      inflateReset2 (some i) w h = .ok (Z_OK, setZS h i (rkZ z wrap) b (rkS b (rS (r2S st wrap wb)))) := by
  simp only [inflateReset2, bind_app, L.check, L.stateOf, Bool.false_eq_true, ↓reduceIte]
  by_cases hneg : w < 0
  · simp only [hneg, ↓reduceIte]
    by_cases h15 : w < -MAX_WBITS
    · left; simp [h15]
    · by_cases hc : (-w != 0 && (decide (-w < MIN_WBITS) || decide (-w > MAX_WBITS))) = true
      · left; simp only [h15, hc, ↓reduceIte]; rfl
      · right
        refine ⟨0, (-w).toUInt32, wb_ok _ hc, ?_⟩
        simp only [h15, hc, ↓reduceIte, Bool.false_eq_true]
        exact reset2_tail L 0 (-w)
  · simp only [hneg, ↓reduceIte, wrap_ok, bind_app, pure_app]
    by_cases h48 : w < 48
    · simp only [h48, ↓reduceIte]
      by_cases hc : ((w &&& MAX_WBITS) != 0 && (decide ((w &&& MAX_WBITS) < MIN_WBITS) ||
          decide ((w &&& MAX_WBITS) > MAX_WBITS))) = true
      · left; simp only [hc, ↓reduceIte]; rfl
      · right
        refine ⟨Int32.ofInt ((w >>> 4).toInt + 5), (w &&& MAX_WBITS).toUInt32, wb_ok _ hc, ?_⟩
        simp only [hc, ↓reduceIte, Bool.false_eq_true]
        exact reset2_tail L _ _
    · simp only [h48, ↓reduceIte]
      by_cases hc : (w != 0 && (decide (w < MIN_WBITS) || decide (w > MAX_WBITS))) = true
      · left; simp only [hc, ↓reduceIte]; rfl
      · right
        refine ⟨Int32.ofInt ((w >>> 4).toInt + 5), w.toUInt32, wb_ok _ hc, ?_⟩
        simp only [hc, ↓reduceIte, Bool.false_eq_true]
        exact reset2_tail L _ _

/-- `inflateReset2` with the default `windowBits` (15) succeeds. -/
theorem reset2_15 {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st) :
    ∃ H, inflateReset2 (some i) 15 h = .ok (Z_OK, H) := by
  have h1 : ¬ (15 : Int32) < 0 := by decide
  have h2 : (15 : Int32) < 48 := by decide
  have h3 : ¬ (((15 : Int32) &&& MAX_WBITS) != 0 && (decide (((15 : Int32) &&& MAX_WBITS) < MIN_WBITS) ||
      decide (((15 : Int32) &&& MAX_WBITS) > MAX_WBITS))) = true := by decide
  simp only [inflateReset2, bind_app, L.check, L.stateOf, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, wrap_ok,
    pure_app]
  exact ⟨_, reset2_tail L _ _⟩

/-! ## The invariant after a reset -/

/-- The state after `inflateResetKeep` has the invariant when the window fields are in range. -/
theorem core_rkS {h : Heap} {s : StreamPtr} {z z' : ZStream} {b : Nat} {st : InflateState} {al : InflateAllocs}
    (sh : Shape h s z b (view st) al) (hza : z'.zalloc = z.zalloc) (hzf : z'.zfree = z.zfree)
    (hw : st.wbits ≤ 15) (hr : st.reqbits ≤ 15) (hs : st.wsize = 0 ∨ st.wsize = (1 : UInt32) <<< st.wbits)
    (hh : st.whave ≤ st.wsize) (hn : st.wnext = 0 ∨ st.wnext < st.wsize) :
    Core h s z' b (view (rkS b st)) al where
  toShape := { sh with zalloc := hza.trans sh.zalloc, zfree := hzf.trans sh.zfree,
                       mode_lo := by show HEAD ≤ HEAD; decide, mode_hi := by show HEAD ≤ SYNC; decide }
  wbits := hw
  reqbits := hr
  wsize := hs
  whave := hh
  wnext := hn
  bits := by show (0 : UInt32) ≤ 64; decide
  lencode := ⟨_, rfl, Or.inl ⟨0, rfl, Nat.zero_le _⟩⟩
  distcode := ⟨_, rfl, Or.inl ⟨0, rfl, Nat.zero_le _⟩⟩
  next := ⟨0, rfl, Nat.zero_le _⟩
  head := Or.inl rfl

/-- The invariant of a heap made by `setZS`. -/
theorem inv_setZS {h : Heap} {i : Nat} {z' : ZStream} {b : Nat} {st' : InflateState} {al : InflateAllocs}
    (hb : z'.state = some b) (hd : ∃ d, h.bytes b = some d) (hal : h.iallocsOf b = some al)
    (c : Core (setZS h i z' b st') (some i) z' b (view st') al) : Inv (setZS h i z' b st') (some i) := by
  obtain ⟨d, hd⟩ := hd
  refine ⟨i, z', b, st', al, rfl, by simp [setZS], hb, by simp [setZS, Heap.istate, hd], ?_, c⟩
  simpa [setZS, Heap.iallocsOf] using hal

theorem resetKeep_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ i z b st, s = some i ∧ C.run (inflateResetKeep s) h = .ok (Z_OK, setZS h i (rkZ z st.wrap) b (rkS b st)) ∧
      Inv (setZS h i (rkZ z st.wrap) b (rkS b st)) s := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  refine ⟨i, z, b, st, rfl, resetKeep_run L, inv_setZS L.hb L.hd hal ?_⟩
  exact core_rkS (z := z) { c.toShape with } rfl rfl c.wbits c.reqbits c.wsize c.whave c.wnext

theorem reset_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ i z b st, s = some i ∧
      C.run (inflateReset s) h = .ok (Z_OK, setZS h i (rkZ z st.wrap) b (rkS b (rS st))) ∧
      Inv (setZS h i (rkZ z st.wrap) b (rkS b (rS st))) s := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  refine ⟨i, z, b, st, rfl, reset_run L, inv_setZS L.hb L.hd hal ?_⟩
  exact core_rkS (z := z) (st := rS st) { c.toShape with } rfl rfl c.reqbits c.reqbits (Or.inl rfl)
    (UInt32.le_refl _) (Or.inl rfl)

theorem reset2_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) (w : Int32) :
    C.run (inflateReset2 s w) h = .ok (Z_STREAM_ERROR, h) ∨
    ∃ i z b st wrap wb, s = some i ∧
      C.run (inflateReset2 s w) h = .ok (Z_OK, setZS h i (rkZ z wrap) b (rkS b (rS (r2S st wrap wb)))) ∧
      Inv (setZS h i (rkZ z wrap) b (rkS b (rS (r2S st wrap wb)))) s := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  rcases reset2_run L w with e | ⟨wrap, wb, hwb, e⟩
  · exact Or.inl e
  · refine Or.inr ⟨i, z, b, st, wrap, wb, rfl, e, inv_setZS L.hb L.hd hal ?_⟩
    exact core_rkS (z := z) (st := rS (r2S st wrap wb)) { c.toShape with } rfl rfl hwb hwb (Or.inl rfl)
      (UInt32.le_refl _) (Or.inl rfl)

/-! ## `inflatePrime` -/

private theorem prime_bits {sb : UInt32} {bits : Int32}
    (hc : ¬ (bits > 16 || sb.toUInt64 + bits.toUInt32.toUInt64 > 32) = true) :
    sb < 64 ∧ sb + bits.toUInt32 ≤ 64 := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, gt_iff_lt, UInt64.not_lt] at hc
  obtain ⟨h16, h32⟩ := hc
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add] at h32
  simp only [UInt32.toNat_toUInt64] at h32
  have e32 : (32 : UInt64).toNat = 32 := rfl
  rw [e32] at h32
  have hb := UInt32.toNat_lt sb
  have hb2 := UInt32.toNat_lt bits.toUInt32
  constructor
  · rw [UInt32.lt_iff_toNat_lt]; show sb.toNat < 64; omega
  · rw [UInt32.le_iff_toNat_le, UInt32.toNat_add]; show _ ≤ 64; omega

/-- `inflatePrime` on an invariant stream: no fault; the heap is unchanged or only the state record changes; the
invariant holds after. -/
theorem prime_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) (bits value : Int32) :
    ∃ r h', C.run (inflatePrime s bits value) h = .ok (r, h') ∧ Inv h' s ∧
      (h' = h ∨ ∃ b st', StateBlock h s b ∧ h' = { h with istates := upd h.istates b (some st') }) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  have hsb : StateBlock h (some i) b := ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩
  by_cases h0 : bits = 0
  · exact ⟨Z_OK, h, by simp [C.run, inflatePrime, bind_app, L.check, h0], hv, Or.inl rfl⟩
  by_cases hneg : bits < 0
  · obtain ⟨hr, hi⟩ := InflateInv.wrS hv (fun s => { s with hold := 0, bits := 0 }) hsb L.istate
      (fun _ _ c => { c with bits := by show (0 : UInt32) ≤ 64; decide })
    refine ⟨Z_OK, _, ?_, hi, Or.inr ⟨b, _, hsb, rfl⟩⟩
    simp only [C.run] at hr
    simp [C.run, inflatePrime, bind_app, L.check, h0, hneg, L.stateOf, hr]
  by_cases hc : (bits > 16 || st.bits.toUInt64 + bits.toUInt32.toUInt64 > 32) = true
  · refine ⟨Z_STREAM_ERROR, h, ?_, hv, Or.inl rfl⟩
    simp only [C.run, inflatePrime, bind_app, L.check, L.stateOf, ldState_app L.istate, Bool.false_eq_true,
      ↓reduceIte, beq_iff_eq, h0, hneg]
    simp only [hc, ↓reduceIte]
    rfl
  · obtain ⟨hlt, hle⟩ := prime_bits hc
    obtain ⟨hr, hi⟩ := InflateInv.wrS hv (fun s => { s with
        hold := s.hold + (((value.toInt64 &&& (((1 : Int64) <<< bits.toInt64) - 1)).toInt32).toInt64.toUInt64 <<<
          st.bits.toUInt64), bits := s.bits + bits.toUInt32 })
      hsb L.istate (fun _ _ c => { c with bits := hle })
    refine ⟨Z_OK, _, ?_, hi, Or.inr ⟨b, _, hsb, rfl⟩⟩
    simp only [C.run] at hr
    simp only [C.run, inflatePrime, bind_app, L.check, L.stateOf, ldState_app L.istate, Bool.false_eq_true,
      ↓reduceIte, beq_iff_eq, h0, hneg]
    simp only [hc, ↓reduceIte, Bool.false_eq_true, shl64, hlt, pure_app, bind_app]
    rw [hr]

end ZlibNgF.Proof.InflateReset
