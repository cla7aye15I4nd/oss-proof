import ZlibNgF.Proof.«infback.c.init»
import ZlibNgF.Proof.«infback.c.reach»

/-!
# The shape after `inflateBackInit_` (`ZlibNgF`)

A successful `inflateBackInit_` (`Z_OK`) leaves the stream with a state of the call-back shape (`InitShape`): the
state is the new block of `alloc_inflate`, its window is the caller's window of `2^windowBits` bytes (a block that
existed before, so not the new one), `wnext` is 0, and the arrays have their sizes.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackInit
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNg.Infback ZlibNgF.Proof.InflateAlloc
open ZlibNgF.Proof.InflateInit (frame_refl checkVer_ok)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.InfbackLoop (BackShape shapeEnv InitShape)

theorem backInit_shape {h h' : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree)
    (hfr : FreshBlocks h) (wb : Int32) (w : BPtr) (hws : WriteSlice h w (2 ^ wb.toInt.toNat))
    (e : inflateBackInit (some i) wb w h = .ok (Z_OK, h')) : BackShape h' (some i) w (2 ^ wb.toInt.toNat) := by
  obtain ⟨wbk, woff, d, rfl, hd, hsz⟩ := hws
  by_cases hc1 : ((Ptr.ref (BRef.heap wbk) woff : BPtr) == .null || wb < MIN_WBITS || wb > MAX_WBITS) = true
  · have hc := hc1
    have hc' : (some i == (none : StreamPtr) || (Ptr.ref (BRef.heap wbk) woff : BPtr) == .null || wb < MIN_WBITS ||
        wb > MAX_WBITS) = true := by simpa using hc
    simp only [inflateBackInit, hc', ↓reduceIte] at e
    simp [Z_STREAM_ERROR, Z_OK] at e
  have hc : ((Ptr.ref (BRef.heap wbk) woff : BPtr) == .null || wb < MIN_WBITS || wb > MAX_WBITS) = false := by
    simpa using hc1
  have h8 : (8 : Int32) ≤ wb := by
    have : ¬ wb < 8 := by intro x; simp [MIN_WBITS, x] at hc
    exact Int32.not_lt.mp this
  have h15 : wb ≤ 15 := by
    have : ¬ 15 < wb := by intro x; simp [MAX_WBITS, x] at hc
    exact Int32.not_lt.mp this
  rw [backInit_pre hz hza hzf wb _ hc] at e
  have hza0 : (({ h with streams := upd h.streams i (some (initZ z)) } : Heap).streams i).map ZStream.zalloc =
      some .zcalloc := by simp [initZ]
  have hfs := (hfr _ (Nat.le_refl _)).1
  have hfa := (hfr _ (Nat.le_refl _)).2.1
  cases hok : h.allocOk h.nalloc
  · simp only [bind_app, alloc_fail hza0 hok] at e
    simp [Z_MEM_ERROR, Z_OK] at e
  simp only [bind_app, alloc_ok hza0 hfs hfa hok] at e
  simp [-Nat.reducePow, ldAllocs, Heap.iallocsOf, Ival.get, wrS, ldState, stState, Heap.istate, wrZ, ldStream,
    stStream, upd_upd, initZ, shl_ok wb _ h8 h15] at e
  subst e
  have hwb : wbk < h.nextBlk := by
    apply Classical.byContradiction
    intro hlt
    have := (hfr wbk (by omega)).2.2
    rw [this] at hd; cases hd
  have hne : wbk ≠ h.nextBlk := Nat.ne_of_lt hwb
  have h0 : (0 : Int32) ≤ wb := by rw [Int32.le_iff_toInt_le] at h8 ⊢; simp at h8 ⊢; omega
  have hwn : ((1 : UInt32) <<< wb.toUInt32).toNat = 2 ^ wb.toInt.toNat := by
    have ec : wb.toNatClampNeg = wb.toInt.toNat := rfl
    have hlt : wb.toInt.toNat < 32 := by rw [Int32.le_iff_toInt_le] at h15; simp at h15; omega
    rw [ZlibNgF.Proof.Inftrees.u32_shl_one (by rw [Int32.toNat_toUInt32_of_le h0, ec]; exact hlt),
      Int32.toNat_toUInt32_of_le h0, ec]
  have hw8 : 8 ≤ wb.toInt.toNat := by rw [Int32.le_iff_toInt_le] at h8; simp at h8; omega
  have hw15 : wb.toInt.toNat ≤ 15 := by rw [Int32.le_iff_toInt_le] at h15; simp at h15; omega
  have hp1 : 1 ≤ 2 ^ wb.toInt.toNat := Nat.one_le_two_pow
  have hp2 : 2 ^ wb.toInt.toNat ≤ 32768 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hw15) (by decide)
  refine ⟨i, h.nextBlk, wbk, woff, _, _, rfl, rfl, ⟨upd_same _ _ _, rfl, rfl, ⟨_, upd_same _ _ _⟩, upd_same _ _ _,
    ⟨_, upd_same _ _ _, rfl, rfl⟩, by dsimp only; rfl, by dsimp only; rfl, hne,
    ⟨d, by dsimp only; refine (allocHeap_bytes_ne _ _ wbk ?_).trans ?_; exact hne; exact hd, hsz⟩, by dsimp only; exact hwn, hp1, hp2,
    by dsimp only, by dsimp only; simp [InflateState.garbage], by dsimp only; simp [InflateState.garbage],
    by dsimp only; simp [InflateState.garbage]⟩⟩

/-- The shape after a successful `inflateBackInit_`. -/
theorem initShape : InitShape := by
  intro h h' s wb w version size hfr hir hv hws hrun
  obtain ⟨c, hc⟩ := checkVer_ok h version size hv
  cases c
  · have e : inflateBackInit s wb w h = .ok (Z_OK, h') := by
      simpa [C.run, inflateBackInit_, bind_app, hc] using hrun
    rcases hir with rfl | ⟨z, ⟨i, rfl, hz⟩, hza, hzf⟩
    · simp [inflateBackInit, Z_STREAM_ERROR, Z_OK] at e
    · exact backInit_shape hz hza hzf hfr wb w hws e
  · simp [C.run, inflateBackInit_, bind_app, hc, Z_VERSION_ERROR, Z_OK] at hrun

end ZlibNgF.Proof.InfbackInit
