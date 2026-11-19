import MozjpegF.Spec.Safety.Goals
import MozjpegF.Spec.Functional.Goals

/-!
# Proofs of `jerror.c` safety and functional specifications (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.Jerror
open C MozjpegF.Spec MozjpegF.Spec.Safety MozjpegF.Spec.Functional Mozjpeg.JerrorH

theorem jpeg_std_error_functional : Goal.jpeg_std_error_functional := by
  intro h err ⟨r, a, herr, hget, hsz⟩
  subst herr
  unfold Mozjpeg.Jerror.jpeg_std_error
  cases r with | err b =>
  have hget' : h.errMgrs b = some a := hget
  let zeroMgr : JpegErrorMgr := { msgParmI := Array.replicate 8 0 }
  let nextMgr : JpegErrorMgr := {
    zeroMgr with
    errorExit := .fn "error_exit"
    emitMessage := .fn "emit_message"
    outputMessage := .fn "output_message"
    formatMessage := .fn "format_message"
    resetErrorMgr := .fn "reset_error_mgr"
    jpegMessageTable := .ref .stdTable 0
    lastJpegMessage := JMSG_LASTMSGCODE - 1
  }
  let h1 := C.Space.put h (ErrRef.err b) (a.set! 0 zeroMgr)
  let a' := (a.set! 0 zeroMgr).set! 0 nextMgr
  let h' := C.Space.put h1 (ErrRef.err b) a'
  refine ⟨h', ErrRef.err b, a', rfl, ?_, ?_⟩
  · have hstep1 : ∀ f : Unit → M ErrPtr,
        C.run (memsetZeroErrMgr (.ref (ErrRef.err b) 0) >>= f) h = C.run (f ()) h1 := by
      intro f
      simp [C.run, bind, memsetZeroErrMgr, C.Space.get, C.Space.ro, hget', hsz,
        C.Space.modify_eq]
      rfl
    rw [hstep1]
    have hget1 : C.Space.get h1 (ErrRef.err b) = some (a.set! 0 zeroMgr) := by
      simp [h1, C.Space.get, C.Space.put]
    have hsz1 : 0 < (a.set! 0 zeroMgr).size := by rw [Array.size_set!]; exact hsz
    rw [Ptr.load_bind h1 (ErrRef.err b) 0 (a.set! 0 zeroMgr) _ hget1 hsz1]
    have hcur : (a.set! 0 zeroMgr)[0] = zeroMgr := by
      simp [Array.set!_eq_setIfInBounds]
    rw [hcur]
    have hro1 : C.Space.ro h1 (ErrRef.err b) = false := rfl
    change C.run (Ptr.store (Ptr.ref (ErrRef.err b) 0) nextMgr >>= fun () => pure (Ptr.ref (ErrRef.err b) 0)) h1 =
      .ok (Ptr.ref (ErrRef.err b) 0, h')
    rw [Ptr.store_bind h1 (ErrRef.err b) 0 nextMgr (a.set! 0 zeroMgr)
      (fun () => pure (Ptr.ref (ErrRef.err b) 0)) hget1 hro1 hsz1]
    rfl
  · have ha'_sz : 0 < a'.size := by simp [a']; exact hsz
    have ha'_0 : a'[0]! = nextMgr := by
      rw [getElem!_pos a' 0 ha'_sz]
      simp [a', Array.set!_eq_setIfInBounds]
    refine ⟨?_, ha'_sz, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h', C.Space.get, C.Space.put]
    · simp [ha'_0, nextMgr, zeroMgr]
    · simp [ha'_0, nextMgr, zeroMgr]
    · simp [ha'_0, nextMgr, zeroMgr]
    · simp [ha'_0, nextMgr]
    · simp [ha'_0, nextMgr]
    · simp [ha'_0, nextMgr]

theorem jpeg_std_error_safety : Goal.jpeg_std_error_safety := by
  intro h err herr
  obtain ⟨h', _, a', _, hr, _, _⟩ := jpeg_std_error_functional h err herr
  exact ⟨h', hr⟩

theorem jpeg_std_error_nonvacuous : Goal.jpeg_std_error_nonvacuous := by
  exact ⟨_, rfl⟩

end MozjpegF.Proof.Jerror
