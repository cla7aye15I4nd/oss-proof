import ZlibNgF.Proof.«inflate.c.alloc»

/-!
# `inflateInit_`, `inflateInit2_` (`ZlibNgF`)

The safety goals, from the run of `inflateInit2` in `Proof/inflate.c.alloc.lean`; and the structural invariant after
a successful call (the `init` / `init2` cases of `InflateReachable`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateInit
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNgF.Proof.InflateAlloc

theorem frame_refl (h : Heap) (a b c : List Nat) (w : List (BPtr × Nat)) : Frame h h a b c w :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ data hd => ⟨data, hd, rfl, fun _ _ _ => rfl⟩, fun _ _ _ hn => hn, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

/-- `CHECK_VER_STSIZE` reads the first byte of a valid `version` and changes nothing. -/
theorem checkVer_ok (h : Heap) (version : BPtr) (size : Int32) (hv : VersionOk h version) :
    ∃ c, CHECK_VER_STSIZE version size h = .ok (c, h) := by
  rcases hv with rfl | ⟨r, off, data, rfl, hget, hle⟩
  · exact ⟨true, rfl⟩
  · have h1 : off ≤ data.size := by omega
    have h2 : (off : Int) + 0 ≤ (data.size : Int) := by omega
    have h3 : off < data.size := by omega
    have e : index8 (.ref r off) 0 h = .ok (data[off], h) := by
      simp [index8, Ptr.index, bind_app, Ptr.add, Ptr.load, hget, h1, h3]
    have hn : (Ptr.ref r off == (Ptr.null : BPtr)) = false := rfl
    simp only [CHECK_VER_STSIZE, hn, Bool.false_eq_true, ↓reduceIte]
    rw [bind_app, e]
    dsimp only
    split <;> exact ⟨_, rfl⟩

/-- `inflateInit2` on a stream ready for initialisation: no fault, only the stream record and fresh blocks change, and
the invariant holds after success. -/
theorem init2_safe (h : Heap) (s : StreamPtr) (wb : Int32) (hfr : FreshBlocks h)
    (hi : InitReady h s) :
    ∃ r h', inflateInit2 s wb h = .ok (r, h') ∧ Frame h h' (streamIds s) [] [] [] ∧
      (r = Z_OK → InflateInv.Inv h' s) := by
  rcases hi with rfl | ⟨z, ⟨i, rfl, hz⟩, hza, hzf⟩
  · exact ⟨Z_STREAM_ERROR, h, rfl, frame_refl h _ _ _ _, fun e => absurd e (by decide)⟩
  · obtain ⟨r, h', e, f, hinv, _⟩ := init2_ok hz hza hzf (hfr _ (Nat.le_refl _)).1 (hfr _ (Nat.le_refl _)).2 wb
    exact ⟨r, h', e, f.frame, hinv⟩

theorem inflateInit__safety : Goal.inflateInit__safety := by
  intro h s version size _ hfr hi hv
  obtain ⟨c, hc⟩ := checkVer_ok h version size hv
  cases c
  · obtain ⟨r, h', e, f, _⟩ := init2_safe h s DEF_WBITS hfr hi
    exact ⟨r, h', by simp [C.run, inflateInit_, bind_app, hc, e], f⟩
  · exact ⟨Z_VERSION_ERROR, h, by simp [C.run, inflateInit_, bind_app, hc], frame_refl h _ _ _ _⟩

theorem inflateInit2__safety : Goal.inflateInit2__safety := by
  intro h s wb version size _ hfr hi hv
  obtain ⟨c, hc⟩ := checkVer_ok h version size hv
  cases c
  · obtain ⟨r, h', e, f, _⟩ := init2_safe h s wb hfr hi
    exact ⟨r, h', by simp [C.run, inflateInit2_, bind_app, hc, e], f⟩
  · exact ⟨Z_VERSION_ERROR, h, by simp [C.run, inflateInit2_, bind_app, hc], frame_refl h _ _ _ _⟩

/-- `inflateInit_` with the library's version string succeeds on a zero `z_stream` when the allocation succeeds. -/
theorem init_ok_gen (h : Heap) (hfr : FreshBlocks h) (hz : h.streams 0 = some {})
    (hok : h.allocOk h.nalloc = true) :
    ∃ h', C.run (do let v ← strLitRef "1.3.2.zlib-ng"; inflateInit_ (some 0) v 112) h = .ok (Z_OK, h') ∧
      InflateReachable h' (some 0) := by
  obtain ⟨r, h', e, _, _, hr⟩ := init2_ok hz (Or.inl rfl) (Or.inl rfl) (hfr _ (Nat.le_refl _)).1
    (hfr _ (Nat.le_refl _)).2
    DEF_WBITS
  have hr : r = Z_OK := hr hok rfl
  subst hr
  have hf : strTable.findIdx? (· == "1.3.2.zlib-ng") = some 0 :=
    Array.findIdx?_eq_some_iff_getElem.mpr ⟨by decide, by decide, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  have hs : strLitRef "1.3.2.zlib-ng" h = .ok (.ref (.str 0) 0, h) := by
    simp only [strLitRef, hf]
  have hc : CHECK_VER_STSIZE (.ref (.str 0) 0) 112 h = .ok (false, h) := rfl
  have hrun : C.run (inflateInit_ (some 0) (.ref (.str 0) 0) 112) h = .ok (Z_OK, h') := by
    simp only [C.run, inflateInit_, bind_app, hc, Bool.false_eq_true, ↓reduceIte]
    exact e
  refine ⟨h', ?_, ?_⟩
  · simp only [C.run, bind_app, hs]; exact hrun
  · refine InflateReachable.init h h' (some 0) (.ref (.str 0) 0) 112
      (Or.inr ⟨{}, ⟨0, rfl, hz⟩, Or.inl rfl, Or.inl rfl⟩) (Or.inr ⟨.str 0, 0, _, rfl, rfl, ?_⟩) hrun
    simp [Heap.litBytes]

/-- A heap with the CRC tables and one zero `z_stream`. -/
def initHeap : Heap :=
  { crcTable := ZlibNg.Crc32Tbl.crc_table, x2nTable := ZlibNg.Crc32Tbl.x2n_table,
    streams := upd .empty 0 (some {}) }

theorem inflateInit_nonvacuous : Goal.inflateInit_nonvacuous := by
  have hfr : FreshBlocks initHeap := fun b _ => ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b⟩
  obtain ⟨h', e, hr⟩ := init_ok_gen initHeap hfr (upd_same _ _ _) rfl
  exact ⟨initHeap, h', some 0, ⟨rfl, rfl⟩, Or.inr ⟨{}, ⟨0, rfl, upd_same _ _ _⟩, Or.inl rfl, Or.inl rfl⟩,
    e, hr⟩

end ZlibNgF.Proof.InflateInit
