import MozjpegF.Spec.Common.Types

/-!
# Functional goals (`MozjpegF`)

Exact mathematical specifications for `jdiv_round_up`, `jpeg_std_error`, and Sharp's
shrink-on-load (`scale_num = 1`, `scale_denom ∈ {2, 4, 8}`) in `jpeg_calc_output_dimensions`.
-/

set_option autoImplicit false

namespace MozjpegF.Spec.Functional
open C MozjpegF.Spec Mozjpeg.JpeglibH Mozjpeg.JerrorH

/-- `jdiv_round_up(a, b)` computes exact `⌈a / b⌉ = (a + b - 1) / b` for `a ≥ 0, b > 0` without overflow. -/
def Goal.jdiv_round_up_functional : Prop :=
  ∀ (h : C.Heap) (a b : Int64),
    0 ≤ a.toInt → 0 < b.toInt → a.toInt + b.toInt < 2 ^ 63 →
    ∃ r,
      C.run (Mozjpeg.Jutils.jdiv_round_up a b) h = .ok (r, h) ∧
      r.toInt = (a.toInt + b.toInt - 1) / b.toInt

/-- `jpeg_std_error(err)` sets `last_jpeg_message = JMSG_LASTMSGCODE - 1`, `msg_code = 0`,
`num_warnings = 0`, `trace_level = 0`, `jpeg_message_table = .ref .stdTable 0`, and standard methods. -/
def Goal.jpeg_std_error_functional : Prop :=
  ∀ (h : C.Heap) (err : C.ErrPtr),
    ValidErrMgr h err →
    ∃ h' r a',
      err = .ref r 0 ∧
      C.run (Mozjpeg.Jerror.jpeg_std_error err) h = .ok (err, h') ∧
      C.Space.get h' r = some a' ∧ 0 < a'.size ∧
      (a'[0]!).msgCode = 0 ∧
      (a'[0]!).numWarnings = 0 ∧
      (a'[0]!).traceLevel = 0 ∧
      (a'[0]!).lastJpegMessage = JMSG_LASTMSGCODE - 1 ∧
      (a'[0]!).jpegMessageTable = .ref .stdTable 0 ∧
      (a'[0]!).errorExit = .fn "error_exit"

/-- On `DSTATE_READY`, non-lossless images with `scale_num = 1` and `scale_denom ∈ {1, 2, 4, 8}`,
`jpeg_core_output_dimensions(cinfo)` selects `_min_DCT_h_scaled_size = 8 / scale_denom` and sets
`output_width = ceil(image_width / scale_denom)` and `output_height = ceil(image_height / scale_denom)`. -/
def Goal.jpeg_core_output_dimensions_shrink_functional : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr) (denom : UInt32),
    denom = 1 ∨ denom = 2 ∨ denom = 4 ∨ denom = 8 →
    ValidDecompDimsInput h cinfo false →
    (∀ rc dcs dc rmas masters,
      cinfo = .ref rc 0 → C.Space.get h rc = some dcs → 0 < dcs.size →
      dc = dcs[0]! → dc.master = .ref rmas 0 → C.Space.get h rmas = some masters →
      0 < masters.size →
      dc.scaleNum = 1 ∧ dc.scaleDenom = denom ∧ (masters[0]!).lossless = 0) →
    ∃ h' rc dcs',
      cinfo = .ref rc 0 ∧
      C.run (Mozjpeg.Jdmaster.jpeg_core_output_dimensions cinfo) h = .ok ((), h') ∧
      C.Space.get h' rc = some dcs' ∧ 0 < dcs'.size ∧
      (dcs'[0]!).minDctHScaledSize.toInt = 8 / denom.toNat ∧
      (∀ d0, C.Space.get h rc = some d0 → 0 < d0.size →
        (dcs'[0]!).outputWidth.toNat = ((d0[0]!).imageWidth.toNat + denom.toNat - 1) / denom.toNat ∧
        (dcs'[0]!).outputHeight.toNat = ((d0[0]!).imageHeight.toNat + denom.toNat - 1) / denom.toNat)

end MozjpegF.Spec.Functional
