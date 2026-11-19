import MozjpegF.Spec.Safety.Goals

/-!
# Proofs of `jcomapi.c` and `jdapimin.c` safety specifications (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.Jdapimin
open C MozjpegF.Spec MozjpegF.Spec.Safety Mozjpeg.Jcomapi Mozjpeg.Jdapimin

theorem jpeg_abort_safety : Goal.jpeg_abort_safety := by
  intro h cinfo hvalid
  obtain ⟨rc, dcs, dc, rm, mems, rmas, masters, _ric, _ics, _rmrk, _mrks,
    hc, hgetdc, hszdc, hdc, _herr, hmem, hgetmem, hszmem, hmas, hgetmas, hszmas,
    _hin, _hgetin, _hszin, _hmrk, _hgetmrk, _hszmrk⟩ := hvalid
  subst hc
  unfold jpeg_abort
  cases rc with | decomp bdc =>
  cases rm with | mem bmem =>
  cases rmas with | master bmas =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have hmemne : (Ptr.ref (C.MemRef.mem bmem) 0 == Ptr.null) = false := rfl
  simp only [hmem, hmemne, Bool.false_eq_true, ↓reduceIte]
  rw [Ptr.load_bind h _ 0 mems _ hgetmem hszmem]
  have hro_mem : C.Space.ro h (C.MemRef.mem bmem) = false := rfl
  rw [Ptr.store_bind h _ 0 _ mems _ hgetmem hro_mem hszmem]
  let h1 := C.Space.put h (C.MemRef.mem bmem) (mems.set! 0 { mems[0] with livePools := mems[0].livePools.set! 1 false })
  have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcs := hgetdc
  change ∃ h', C.run _ h1 = .ok ((), h')
  rw [Ptr.load_bind h1 _ 0 dcs _ hgetdc1 hszdc, hdc0]
  by_cases his : (dc.isDecompressor != 0) = true
  · simp only [his, ↓reduceIte]
    have hro_dc1 : C.Space.ro h1 (C.DecompRef.decomp bdc) = false := rfl
    rw [Ptr.store_bind h1 _ 0 _ dcs _ hgetdc1 hro_dc1 hszdc]
    let h2 := C.Space.put h1 (C.DecompRef.decomp bdc) (dcs.set! 0 { dc with globalState := Mozjpeg.JpeglibH.DSTATE_START, markerList := .null })
    have hgetmas2 : C.Space.get h2 (C.MasterRef.master bmas) = some masters := hgetmas
    change ∃ h', C.run _ h2 = .ok ((), h')
    rw [hmas, Ptr.load_bind h2 _ 0 masters _ hgetmas2 hszmas]
    have hro_mas2 : C.Space.ro h2 (C.MasterRef.master bmas) = false := rfl
    simp [C.run, Ptr.store, hgetmas2, hro_mas2, hszmas]
  · have hisF : (dc.isDecompressor != 0) = false := Bool.eq_false_iff.mpr his
    simp only [hisF, Bool.false_eq_true, ↓reduceIte]
    have hro_dc1 : C.Space.ro h1 (C.DecompRef.decomp bdc) = false := rfl
    simp [C.run, Ptr.store, hgetdc1, hro_dc1, hszdc]

theorem jpeg_destroy_safety : Goal.jpeg_destroy_safety := by
  intro h cinfo hvalid
  obtain ⟨rc, dcs, dc, rm, mems, _rmas, _masters, _ric, _ics, _rmrk, _mrks,
    hc, hgetdc, hszdc, hdc, _herr, hmem, hgetmem, hszmem, _⟩ := hvalid
  subst hc
  unfold jpeg_destroy
  cases rc with | decomp bdc =>
  cases rm with | mem bmem =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have hmemne : (Ptr.ref (C.MemRef.mem bmem) 0 != Ptr.null) = true := rfl
  simp only [hmem, hmemne, ↓reduceIte]
  rw [Ptr.load_bind h _ 0 mems _ hgetmem hszmem]
  have hro_mem : C.Space.ro h (C.MemRef.mem bmem) = false := rfl
  rw [Ptr.store_bind h _ 0 _ mems _ hgetmem hro_mem hszmem]
  let h1 := C.Space.put h (C.MemRef.mem bmem) (mems.set! 0 { mems[0] with livePools := #[false, false] })
  have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcs := hgetdc
  change ∃ h', C.run _ h1 = .ok ((), h')
  rw [Ptr.load_bind h1 _ 0 dcs _ hgetdc1 hszdc, hdc0]
  have hro_dc1 : C.Space.ro h1 (C.DecompRef.decomp bdc) = false := rfl
  simp [C.run, Ptr.store, hgetdc1, hro_dc1, hszdc]

theorem jpeg_abort_decompress_safety : Goal.jpeg_abort_decompress_safety :=
  jpeg_abort_safety

theorem jpeg_destroy_decompress_safety : Goal.jpeg_destroy_decompress_safety :=
  jpeg_destroy_safety

theorem jpeg_input_complete_safety : Goal.jpeg_input_complete_safety := by
  intro h cinfo hvalid
  obtain ⟨rc, dcs, dc, _rm, _mems, _rmas, _masters, ric, ics, _rmrk, _mrks,
    hc, hgetdc, hszdc, hdc, herrValid, _hmem, _hgetmem, _hszmem, _hmas, _hgetmas, _hszmas,
    hin, hgetin, hszin, _⟩ := hvalid
  subst hc
  obtain ⟨rerr, errs, herr, hgeterr, hszerr⟩ := herrValid
  unfold jpeg_input_complete Mozjpeg.JerrorH.errexit1
  cases rc with | decomp bdc =>
  cases ric with | inputctl bic =>
  cases rerr with | err berr =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  by_cases hbad : (dc.globalState < Mozjpeg.JpeglibH.DSTATE_START ||
                   dc.globalState > Mozjpeg.JpeglibH.DSTATE_STOPPING) = true
  · simp only [hbad, ↓reduceIte, herr, bind_assoc_m, pure_bind_m]
    rw [Ptr.load_bind h _ 0 errs _ hgeterr hszerr]
    have hro_err : C.Space.ro h (C.ErrRef.err berr) = false := rfl
    rw [Ptr.store_bind h _ 0 _ errs _ hgeterr hro_err hszerr]
    exact ⟨_, _, rfl⟩
  · have hbadF : (dc.globalState < Mozjpeg.JpeglibH.DSTATE_START ||
                  dc.globalState > Mozjpeg.JpeglibH.DSTATE_STOPPING) = false :=
      Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte, hin]
    rw [Ptr.load_bind h _ 0 ics _ hgetin hszin]
    exact ⟨_, _, rfl⟩

theorem jpeg_has_multiple_scans_safety : Goal.jpeg_has_multiple_scans_safety := by
  intro h cinfo hvalid
  obtain ⟨rc, dcs, dc, _rm, _mems, _rmas, _masters, ric, ics, _rmrk, _mrks,
    hc, hgetdc, hszdc, hdc, herrValid, _hmem, _hgetmem, _hszmem, _hmas, _hgetmas, _hszmas,
    hin, hgetin, hszin, _⟩ := hvalid
  subst hc
  obtain ⟨rerr, errs, herr, hgeterr, hszerr⟩ := herrValid
  unfold jpeg_has_multiple_scans Mozjpeg.JerrorH.errexit1
  cases rc with | decomp bdc =>
  cases ric with | inputctl bic =>
  cases rerr with | err berr =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  by_cases hbad : (dc.globalState < Mozjpeg.JpeglibH.DSTATE_READY ||
                   dc.globalState > Mozjpeg.JpeglibH.DSTATE_STOPPING) = true
  · simp only [hbad, ↓reduceIte, herr, bind_assoc_m, pure_bind_m]
    rw [Ptr.load_bind h _ 0 errs _ hgeterr hszerr]
    have hro_err : C.Space.ro h (C.ErrRef.err berr) = false := rfl
    rw [Ptr.store_bind h _ 0 _ errs _ hgeterr hro_err hszerr]
    exact ⟨_, _, rfl⟩
  · have hbadF : (dc.globalState < Mozjpeg.JpeglibH.DSTATE_READY ||
                  dc.globalState > Mozjpeg.JpeglibH.DSTATE_STOPPING) = false :=
      Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte, hin]
    rw [Ptr.load_bind h _ 0 ics _ hgetin hszin]
    exact ⟨_, _, rfl⟩

end MozjpegF.Proof.Jdapimin
