import MozjpegF.Spec.Safety.Goals

/-!
# Proofs of `jdmarker.c` safety specifications (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.Jdmarker
open C MozjpegF.Spec MozjpegF.Spec.Safety Mozjpeg.Jdmarker Mozjpeg.JerrorH

theorem jpeg_save_markers_safety : Goal.jpeg_save_markers_safety := by
  intro h cinfo markerCode limit hvalid _hchunk
  obtain ⟨rc, dcs, dc, rm, mems, _rmas, _masters, _ric, _ics, rmrk, mrks,
    hc, hgetdc, hszdc, hdc, herrValid, hmem, hgetmem, hszmem, _hmas, _hgetmas, _hszmas,
    _hin, _hgetin, _hszin, hmrk, hgetmrk, hszmrk⟩ := hvalid
  subst hc
  obtain ⟨rerr, errs, herr, hgeterr, hszerr⟩ := herrValid
  unfold jpeg_save_markers errexit1
  cases rc with | decomp bdc =>
  cases rm with | mem bmem =>
  cases rmrk with | marker bmrk =>
  cases rerr with | err berr =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hmrk]
  rw [Ptr.load_bind h _ 0 mrks _ hgetmrk hszmrk, hmem]
  rw [Ptr.load_bind h _ 0 mems _ hgetmem hszmem]
  dsimp only
  have hro_mrk : C.Space.ro h (C.MarkerRef.marker bmrk) = false := rfl
  have hro_err : C.Space.ro h (C.ErrRef.err berr) = false := rfl
  by_cases hcom : (markerCode == M_COM) = true
  · simp only [hcom, ↓reduceIte]
    rw [Ptr.store_bind h _ 0 _ mrks _ hgetmrk hro_mrk hszmrk]
    exact ⟨_, _, rfl⟩
  · have hcomF : (markerCode == M_COM) = false := Bool.eq_false_iff.mpr hcom
    simp only [hcomF, Bool.false_eq_true, ↓reduceIte]
    by_cases happ : (markerCode ≥ M_APP0 && markerCode ≤ M_APP15) = true
    · simp only [happ, ↓reduceIte]
      rw [Ptr.store_bind h _ 0 _ mrks _ hgetmrk hro_mrk hszmrk]
      exact ⟨_, _, rfl⟩
    · have happF : (markerCode ≥ M_APP0 && markerCode ≤ M_APP15) = false := Bool.eq_false_iff.mpr happ
      simp only [happF, Bool.false_eq_true, ↓reduceIte, herr, bind_assoc_m, pure_bind_m]
      rw [Ptr.load_bind h _ 0 errs _ hgeterr hszerr]
      rw [Ptr.store_bind h _ 0 _ errs _ hgeterr hro_err hszerr]
      exact ⟨_, _, rfl⟩

end MozjpegF.Proof.Jdmarker
