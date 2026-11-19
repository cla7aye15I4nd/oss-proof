import ZlibNgF.Proof.«public-inflate-init»
import ZlibNgF.Spec.Safety.Infback

/-!
# `inflateBackInit_` (`ZlibNgF`)

The run of `inflateBackInit`: the argument test, the allocator set-up (as in `inflateInit2`), `alloc_inflate`
(`Proof/inflate.c.alloc.lean`: one `zcalloc`, or its failure) and the state set-up on the new block. Every call changes
only the stream record and the fresh block (`Fr`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackInit
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNg.Infback ZlibNgF.Proof.InflateAlloc
open ZlibNgF.Proof.InflateInit (frame_refl checkVer_ok)
open ZlibNgF.Proof.InflateInv (upd_upd)

/-- `inflateBackInit` after the argument test and the allocator set-up. -/
theorem backInit_pre {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree) (wb : Int32)
    (w : BPtr) (hc : (w == .null || wb < MIN_WBITS || wb > MAX_WBITS) = false) :
    inflateBackInit (some i) wb w h = (do
      let alloc_bufs ← alloc_inflate (some i)
      if alloc_bufs == none then return Z_MEM_ERROR
      let st ← (← ldAllocs alloc_bufs).state.get
      wrS st fun s => { s with alloc_bufs := .val alloc_bufs }
      wrZ (some i) fun z => { z with state := st }
      wrS st fun s => { s with wbits := wb.toUInt32 }
      let w1 ← shl32 1 wb.toUInt32
      wrS st fun s => { s with wsize := w1 }
      let w2 ← shl32 1 wb.toUInt32
      wrS st fun s => { s with wbufsize := w2 }
      wrS st fun s => { s with window := .val w }
      wrS st fun s => { s with wnext := 0 }
      wrS st fun s => { s with whave := 0 }
      return Z_OK : M Int32) { h with streams := upd h.streams i (some (initZ z)) } := by
  have hc' : (some i == (none : StreamPtr) || w == .null || wb < MIN_WBITS || wb > MAX_WBITS) = false := by
    simpa using hc
  simp only [inflateBackInit, hc', Bool.false_eq_true, ↓reduceIte]
  rcases hza with ha | ha <;> rcases hzf with hf | hf <;>
  simp [bind_app, wrZ, rdZ, ldStream, stStream, hz, ha, hf, upd_upd, initZ]

theorem shl_ok (wb : Int32) (h : Heap) (h8 : (8 : Int32) ≤ wb) (h15 : wb ≤ 15) :
    shl32 1 wb.toUInt32 h = .ok ((1 : UInt32) <<< wb.toUInt32, h) := by
  have : wb.toUInt32 < 32 := by
    rw [Int32.le_iff_toInt_le] at h8 h15
    rw [UInt32.lt_iff_toNat_lt]
    have h0 : (0 : Int32) ≤ wb := by rw [Int32.le_iff_toInt_le]; simp at h8 ⊢; omega
    have ec : wb.toNatClampNeg = wb.toInt.toNat := rfl
    rw [Int32.toNat_toUInt32_of_le h0, ec]
    simp at h8 h15 ⊢; omega
  simp [shl32, this]

/-- A successful run: valid arguments and a successful allocation. The stream's state is the new block, and the input
fields stay. -/
theorem backInit_ok {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree)
    (hfr : FreshBlocks h) (hok : h.allocOk h.nalloc = true) (wb : Int32) (w : BPtr)
    (hw : w ≠ .null) (h8 : (8 : Int32) ≤ wb) (h15 : wb ≤ 15) :
    ∃ h', inflateBackInit (some i) wb w h = .ok (Z_OK, h') ∧ Frame h h' [i] [] [] [] ∧
      ∃ z', h'.streams i = some z' ∧ z'.state = some h.nextBlk ∧ z'.next_in = z.next_in ∧
        z'.avail_in = z.avail_in := by
  have hc : (w == .null || wb < MIN_WBITS || wb > MAX_WBITS) = false := by
    have a : (w == .null) = false := by simpa using hw
    have b : ¬ wb < MIN_WBITS := Int32.not_lt.mpr h8
    have c : ¬ wb > MAX_WBITS := Int32.not_lt.mpr h15
    simp [a, b, c]
  have hza0 : (({ h with streams := upd h.streams i (some (initZ z)) } : Heap).streams i).map ZStream.zalloc =
      some .zcalloc := by simp [initZ]
  have hfs := (hfr _ (Nat.le_refl _)).1
  have hfa := (hfr _ (Nat.le_refl _)).2.1
  obtain ⟨H, eH⟩ : ∃ H, inflateBackInit (some i) wb w h = .ok (Z_OK, H) := by
    rw [backInit_pre hz hza hzf wb w hc]
    simp only [bind_app, alloc_ok hza0 hfs hfa hok]
    simp [-Nat.reducePow, ldAllocs, Heap.iallocsOf, Ival.get, wrS, ldState, stState, Heap.istate, wrZ, ldStream,
      stStream, upd_upd, initZ, shl_ok wb _ h8 h15]
  refine ⟨H, eH, ?_⟩
  rw [backInit_pre hz hza hzf wb w hc] at eH
  simp only [bind_app, alloc_ok hza0 hfs hfa hok] at eH
  simp [-Nat.reducePow, ldAllocs, Heap.iallocsOf, Ival.get, wrS, ldState, stState, Heap.istate, wrZ, ldStream,
    stStream, upd_upd, initZ, shl_ok wb _ h8 h15] at eH
  subst eH
  refine ⟨Fr.frame ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, by simp⟩, by simp⟩
  · intro j hj; simp [hj]
  · intro b' hb'
    have ne : b' ≠ h.nextBlk := Nat.ne_of_lt hb'
    simp [-Nat.reducePow, ne, allocHeap_bytes_ne]

/-- `inflateBackInit` on a stream ready for initialisation: no fault, and only the stream record and fresh blocks
change. -/
theorem backInit_safe (h : Heap) (s : StreamPtr) (wb : Int32) (w : BPtr) (hfr : FreshBlocks h)
    (hi : InitReady h s) :
    ∃ r h', inflateBackInit s wb w h = .ok (r, h') ∧ Frame h h' (streamIds s) [] [] [] := by
  rcases hi with rfl | ⟨z, ⟨i, rfl, hz⟩, hza, hzf⟩
  · exact ⟨Z_STREAM_ERROR, h, rfl, frame_refl h _ _ _ _⟩
  cases hc : (w == .null || wb < MIN_WBITS || wb > MAX_WBITS)
  · have h8 : (8 : Int32) ≤ wb := by
      have : ¬ wb < 8 := by intro x; simp [MIN_WBITS, x] at hc
      exact Int32.not_lt.mp this
    have h15 : wb ≤ 15 := by
      have : ¬ 15 < wb := by intro x; simp [MAX_WBITS, x] at hc
      exact Int32.not_lt.mp this
    rw [backInit_pre hz hza hzf wb w hc]
    have hza0 : (({ h with streams := upd h.streams i (some (initZ z)) } : Heap).streams i).map ZStream.zalloc =
        some .zcalloc := by simp [initZ]
    have hfs := (hfr _ (Nat.le_refl _)).1
    have hfa := (hfr _ (Nat.le_refl _)).2.1
    cases hok : h.allocOk h.nalloc
    · refine ⟨Z_MEM_ERROR, { h with streams := upd h.streams i (some (initZ z)), nalloc := h.nalloc + 1 }, ?_, ?_⟩
      · simp only [bind_app, alloc_fail hza0 hok]; rfl
      · exact Fr.frame ⟨fun j hj => by simp [hj], rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl,
          Nat.le_refl _⟩
    · simp only [bind_app, alloc_ok hza0 hfs hfa hok]
      simp [-Nat.reducePow, ldAllocs, Heap.iallocsOf, Ival.get, wrS, ldState, stState, Heap.istate, wrZ, ldStream,
        stStream, upd_upd, initZ, shl_ok wb _ h8 h15]
      refine ⟨_, _, ⟨rfl, rfl⟩, Fr.frame ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, by simp⟩⟩
      · intro j hj; simp [hj]
      · intro b' hb'
        have ne : b' ≠ h.nextBlk := Nat.ne_of_lt hb'
        simp [-Nat.reducePow, ne, allocHeap_bytes_ne]
  · refine ⟨Z_STREAM_ERROR, h, ?_, frame_refl h _ _ _ _⟩
    have hc' : (some i == (none : StreamPtr) || w == .null || wb < MIN_WBITS || wb > MAX_WBITS) = true := by
      simpa using hc
    simp only [inflateBackInit, hc', ↓reduceIte]; rfl

theorem inflateBackInit__safety : Goal.inflateBackInit__safety := by
  intro h s wb w version size hfr hi hv
  obtain ⟨c, hc⟩ := checkVer_ok h version size hv
  cases c
  · obtain ⟨r, h', e, f⟩ := backInit_safe h s wb w hfr hi
    exact ⟨r, h', by simp [C.run, inflateBackInit_, bind_app, hc, e], f⟩
  · exact ⟨Z_VERSION_ERROR, h, by simp [C.run, inflateBackInit_, bind_app, hc], frame_refl h _ _ _ _⟩

end ZlibNgF.Proof.InfbackInit
