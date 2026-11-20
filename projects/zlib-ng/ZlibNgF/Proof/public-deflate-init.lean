import ZlibNgF.Proof.«deflate.c.init»

/-!
# `deflateInit_`, `deflateInit2_` (`ZlibNgF`)

The safety goals and their non-vacuity, from the run of `deflateInit2` in `Proof/deflate.c.init.lean`; and the
structural invariant after a successful call on any heap (the `init` / `init2` obligations of `DPending`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateInitPublic
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNg.Deflate
open ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat)

theorem dframe_refl (h : Heap) (a b c : List Nat) (w : List (BPtr × Nat)) : DFrame h h a b c w :=
  ⟨InflateInit.frame_refl h a b c w, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem init2_none (level method wb ml strat : Int32) (h : Heap) :
    deflateInit2 none level method wb ml strat h = .ok (Z_STREAM_ERROR, h) := by
  rw [init2_eq]; rfl

/-- `deflateInit2` on a stream ready for initialisation and a heap with fresh blocks: no fault, only the stream
record and fresh blocks change. -/
theorem init2_safe (h : Heap) (s : StreamPtr) (level method wb ml strat : Int32) (hfr : DFreshBlocks h)
    (hi : DInitReady h s) :
    ∃ r h', deflateInit2 s level method wb ml strat h = .ok (r, h') ∧ DFrame h h' (streamIds s) [] [] [] := by
  rcases hi with rfl | ⟨z, ⟨i, rfl, hz⟩, hza, hzf⟩
  · exact ⟨Z_STREAM_ERROR, h, init2_none .., dframe_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, ⟨fr, _⟩, _⟩ := (init2_sat hz hza hzf level method wb ml strat).sat
      (hfr.2 _ (Nat.le_refl _))
    exact ⟨r, h', e, fr⟩

theorem deflateInit__safety : Goal.deflateInit__safety := by
  intro h s level version size hfr hi hv
  obtain ⟨c, hc⟩ := InflateInit.checkVer_ok h version size hv
  cases c
  · obtain ⟨r, h', e, f⟩ := init2_safe h s level Z_DEFLATED.toUInt32.toInt32 MAX_WBITS DEF_MEM_LEVEL
      Z_DEFAULT_STRATEGY hfr hi
    exact ⟨r, h', by simp [C.run, deflateInit_, bind_app, hc, e], f⟩
  · exact ⟨Z_VERSION_ERROR, h, by simp [C.run, deflateInit_, bind_app, hc], dframe_refl h _ _ _ _⟩

theorem deflateInit2__safety : Goal.deflateInit2__safety := by
  intro h s level method wb ml strat version size hfr hi hv
  obtain ⟨c, hc⟩ := InflateInit.checkVer_ok h version size hv
  cases c
  · obtain ⟨r, h', e, f⟩ := init2_safe h s level method wb ml strat hfr hi
    exact ⟨r, h', by simp [C.run, deflateInit2_, bind_app, hc, e], f⟩
  · exact ⟨Z_VERSION_ERROR, h, by simp [C.run, deflateInit2_, bind_app, hc], dframe_refl h _ _ _ _⟩

/-- A successful `deflateInit2` leaves the structural invariant, on every heap. -/
theorem init2_inv {h h' : Heap} {s : StreamPtr} (hi : DInitReady h s) (level method wb ml strat : Int32)
    (e : deflateInit2 s level method wb ml strat h = .ok (Z_OK, h')) : DeflateInv.DInv h' s ∧ DFreshOf h' s := by
  rcases hi with rfl | ⟨z, ⟨i, rfl, hz⟩, hza, hzf⟩
  · rw [init2_none] at e; cases e
  · rcases init2_sat hz hza hzf level method wb ml strat with ⟨r, h'', e', ⟨_, hinv⟩, _⟩ | ⟨_, err, ef⟩
    · rw [e'] at e
      obtain ⟨rfl, rfl⟩ : r = Z_OK ∧ h'' = h' := by simpa using e
      obtain ⟨hv, z, b, st, hz', hb, hst, hf⟩ := hinv rfl
      exact ⟨hv, i, z, b, st, rfl, hz', hb, hst, hf⟩
    · rw [ef] at e; cases e

theorem init_inv (h h' : Heap) (s : StreamPtr) (level : Int32) (version : BPtr) (size : Int32)
    (hi : DInitReady h s) (hv : VersionOk h version)
    (e : C.run (deflateInit_ s level version size) h = .ok (Z_OK, h')) : DeflateInv.DInv h' s ∧ DFreshOf h' s := by
  obtain ⟨c, hc⟩ := InflateInit.checkVer_ok h version size hv
  simp only [C.run, deflateInit_, bind_app, hc] at e
  cases c
  · exact init2_inv hi _ _ _ _ _ e
  · simp at e; exact absurd e.1 (by decide)

theorem init2__inv (h h' : Heap) (s : StreamPtr) (level method wb ml strat : Int32) (version : BPtr) (size : Int32)
    (hi : DInitReady h s) (hv : VersionOk h version)
    (e : C.run (deflateInit2_ s level method wb ml strat version size) h = .ok (Z_OK, h')) :
    DeflateInv.DInv h' s ∧ DFreshOf h' s := by
  obtain ⟨c, hc⟩ := InflateInit.checkVer_ok h version size hv
  simp only [C.run, deflateInit2_, bind_app, hc] at e
  cases c
  · exact init2_inv hi _ _ _ _ _ e
  · simp at e; exact absurd e.1 (by decide)

/-- A heap with the CRC tables and one zero `z_stream`. -/
def initHeap : Heap :=
  { crcTable := ZlibNg.Crc32Tbl.crc_table, x2nTable := ZlibNg.Crc32Tbl.x2n_table,
    streams := upd .empty 0 (some {}) }

theorem deflateInit_nonvacuous : Goal.deflateInit_nonvacuous := by
  have hfr : DFreshBlocks initHeap :=
    ⟨fun b _ => ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b, Tbl.get_empty_opt b⟩,
      fun b _ => ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b⟩⟩
  have hz : initHeap.streams 0 = some {} := upd_same _ _ _
  obtain ⟨r, h', e, ⟨_, _⟩, nv⟩ := (init2_sat hz (Or.inl rfl) (Or.inl rfl) 6 Z_DEFLATED.toUInt32.toInt32 MAX_WBITS
    DEF_MEM_LEVEL Z_DEFAULT_STRATEGY).sat (hfr.2 _ (Nat.le_refl _))
  have hr : r = Z_OK := nv rfl rfl (by decide) rfl rfl rfl
  subst hr
  have hf : strTable.findIdx? (· == "1.3.2.zlib-ng") = some 0 :=
    Array.findIdx?_eq_some_iff_getElem.mpr ⟨by decide, by decide, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  have hs : strLitRef "1.3.2.zlib-ng" initHeap = .ok (.ref (.str 0) 0, initHeap) := by
    simp only [strLitRef, hf]
  have hc : CHECK_VER_STSIZE (.ref (.str 0) 0) 112 initHeap = .ok (false, initHeap) := rfl
  have hrun : C.run (deflateInit_ (some 0) 6 (.ref (.str 0) 0) 112) initHeap = .ok (Z_OK, h') := by
    simp only [C.run, deflateInit_, bind_app, hc, Bool.false_eq_true, ↓reduceIte]
    exact e
  have hready : DInitReady initHeap (some 0) := Or.inr ⟨{}, ⟨0, rfl, hz⟩, Or.inl rfl, Or.inl rfl⟩
  refine ⟨initHeap, h', some 0, hfr, hready, ?_, ?_⟩
  · simp only [C.run, bind_app, hs]; exact hrun
  · refine DeflateReachable.init initHeap h' (some 0) 6 (.ref (.str 0) 0) 112 hready
      (Or.inr ⟨.str 0, 0, _, rfl, rfl, ?_⟩) hrun
    simp [Heap.litBytes]

end ZlibNgF.Proof.DeflateInitPublic
