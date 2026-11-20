import MozjpegF.Spec.Common.Types

/-!
# Safety goals (`MozjpegF`)

Strict ISO C17 runtime UB policy goals, proved safety & non-vacuity goals for Tier 0 decompression
infrastructure (`jutils.c`, `jerror.c`, `jcomapi.c`, `jdapimin.c`, `jdmarker.c`, `jdmaster.c`), and
explicit not-done goals for the remaining full-stream Tier 0 decompression APIs.
-/

set_option autoImplicit false

namespace MozjpegF.Spec.Safety
open C MozjpegF.Spec

/-! ## Strict ISO C17 runtime UB policy goals -/

/-- `NULL + 0` raises `Fault.ub` (ISO C17 §6.5.6p8). -/
def Goal.null_ptr_add_zero_ub : Prop :=
  ∀ (h : C.Heap), FaultsWithUb (C.Ptr.add (.null : C.BPtr) 0) h

/-- Adding `0` to a freed/dangling pointer raises `Fault.ub` (ISO C17 §6.5.6p8, §6.2.4p2). -/
def Goal.dangling_ptr_add_zero_ub : Prop :=
  ∀ (h : C.Heap) (r : C.BRef) (off : Nat),
    C.Space.get h r = (none : Option (Array UInt8)) →
    FaultsWithUb (C.Ptr.add (.ref r off) 0) h

/-- `NULL - NULL` raises `Fault.ub` (ISO C17 §6.5.6p9). -/
def Goal.null_ptr_diff_null_ub : Prop :=
  ∀ (h : C.Heap), FaultsWithUb (C.Ptr.diff (.null : C.BPtr) .null) h

/-- Subtracting pointers into distinct allocations raises `Fault.ub` (ISO C17 §6.5.6p9). -/
def Goal.cross_object_ptr_diff_ub : Prop :=
  ∀ (h : C.Heap) (r1 r2 : C.BRef) (o1 o2 : Nat),
    r1 ≠ r2 →
    FaultsWithUb (C.Ptr.diff (.ref r1 o1) (.ref r2 o2)) h

/-- `memset(NULL, b, 0)` raises `Fault.ub` even when `n = 0` (ISO C17 §7.24.1p2). -/
def Goal.null_memset_zero_ub : Prop :=
  ∀ (h : C.Heap) (b : UInt8), FaultsWithUb (C.Ptr.memset (.null : C.BPtr) b 0) h

/-! ## Proved `jutils.c` safety goals -/

/-- `jdiv_round_up(a, b)` never faults when `b > 0` and `0 ≤ a` with `a + b < 2^63`. -/
def Goal.jdiv_round_up_safety : Prop :=
  ∀ (h : C.Heap) (a b : Int64),
    0 ≤ a.toInt → 0 < b.toInt → a.toInt + b.toInt < 2 ^ 63 →
    ∃ r, C.run (Mozjpeg.Jutils.jdiv_round_up a b) h = .ok (r, h)

/-- `jround_up(a, b)` never faults when `b > 0` and `0 ≤ a` with `a + b - 1 < 2^63`. -/
def Goal.jround_up_safety : Prop :=
  ∀ (h : C.Heap) (a b : Int64),
    0 ≤ a.toInt → 0 < b.toInt → a.toInt + b.toInt - 1 < 2 ^ 63 →
    ∃ r, C.run (Mozjpeg.Jutils.jround_up a b) h = .ok (r, h)

/-- `jzero_far(target, n)` never faults on any live writable slice of length `n` (including `n = 0`
on a live non-null pointer). -/
def Goal.jzero_far_safety : Prop :=
  ∀ (h : C.Heap) (target : C.BPtr) (n : UInt64),
    WritableBytes h target n.toNat →
    ∃ h', C.run (Mozjpeg.Jutils.jzero_far target n) h = .ok ((), h')

/-! ## Proved `jerror.c` safety & non-vacuity goals -/

/-- `jpeg_std_error(err)` never faults on a live `struct jpeg_error_mgr` object and returns `err`. -/
def Goal.jpeg_std_error_safety : Prop :=
  ∀ (h : C.Heap) (err : C.ErrPtr),
    ValidErrMgr h err →
    ∃ h', C.run (Mozjpeg.Jerror.jpeg_std_error err) h = .ok (err, h')

/-- Non-vacuity witness for `jpeg_std_error` starting from uninitialized struct data. -/
def Goal.jpeg_std_error_nonvacuous : Prop :=
  let h : C.Heap := { errMgrs := C.upd C.Tbl.empty 0 (some #[{ msgCode := 999, numWarnings := -1 }]) }
  ∃ h', C.run (Mozjpeg.Jerror.jpeg_std_error (.ref (.err 0) 0)) h = .ok (.ref (.err 0) 0, h')

/-! ## Proved `jcomapi.c`, `jdapimin.c`, `jdmarker.c` safety goals -/

/-- `jpeg_abort` never faults on any `ValidDecompCore` object (including when `mem == NULL` or live). -/
def Goal.jpeg_abort_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr),
    ValidDecompCore h cinfo →
    ∃ h', C.run (Mozjpeg.Jcomapi.jpeg_abort cinfo) h = .ok ((), h')

/-- `jpeg_destroy` never faults on any `ValidDecompCore` object. -/
def Goal.jpeg_destroy_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr),
    ValidDecompCore h cinfo →
    ∃ h', C.run (Mozjpeg.Jcomapi.jpeg_destroy cinfo) h = .ok ((), h')

/-- `jpeg_abort_decompress` never faults on any `ValidDecompCore` object. -/
def Goal.jpeg_abort_decompress_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr),
    ValidDecompCore h cinfo →
    ∃ h', C.run (Mozjpeg.Jdapimin.jpeg_abort_decompress cinfo) h = .ok ((), h')

/-- `jpeg_destroy_decompress` never faults on any `ValidDecompCore` object. -/
def Goal.jpeg_destroy_decompress_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr),
    ValidDecompCore h cinfo →
    ∃ h', C.run (Mozjpeg.Jdapimin.jpeg_destroy_decompress cinfo) h = .ok ((), h')

/-- `jpeg_input_complete` never faults on any `ValidDecompCore` object (either returns `eoi_reached`
or cleanly triggers `ERREXIT1(JERR_BAD_STATE)`). -/
def Goal.jpeg_input_complete_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr),
    ValidDecompCore h cinfo →
    ∃ res h', C.run (Mozjpeg.Jdapimin.jpeg_input_complete cinfo) h = .ok (res, h')

/-- `jpeg_has_multiple_scans` never faults on any `ValidDecompCore` object. -/
def Goal.jpeg_has_multiple_scans_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr),
    ValidDecompCore h cinfo →
    ∃ res h', C.run (Mozjpeg.Jdapimin.jpeg_has_multiple_scans cinfo) h = .ok (res, h')

/-- `jpeg_save_markers` never faults on any `ValidDecompCore` object with non-negative `max_alloc_chunk`
exceeding `sizeof(struct jpeg_marker_struct)` (handles `COM`, `APP0..APP15`, and invalid markers via
`ERREXIT1(JERR_UNKNOWN_MARKER)`). -/
def Goal.jpeg_save_markers_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr) (markerCode : Int32) (limit : UInt32),
    ValidDecompCore h cinfo →
    (∀ rm mems,
      (∃ rc dcs dc, cinfo = .ref rc 0 ∧ C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧
        dc = dcs[0]! ∧ dc.mem = .ref rm 0) →
      C.Space.get h rm = some mems → 0 < mems.size →
      Mozjpeg.JpeglibH.sizeof_jpeg_marker_struct.toInt ≤ (mems[0]!).maxAllocChunk.toInt) →
    ∃ res h', C.run (Mozjpeg.Jdmarker.jpeg_save_markers cinfo markerCode limit) h = .ok (res, h')

/-! ## Proved `jdmaster.c` output dimension & Sharp shrink-on-load safety goals -/

/-- `jpeg_core_output_dimensions(cinfo)` never faults for any `scale_num`, `scale_denom` on a
`ValidDecompDimsInput h cinfo false` object. -/
def Goal.jpeg_core_output_dimensions_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr),
    ValidDecompDimsInput h cinfo false →
    ∃ h', C.run (Mozjpeg.Jdmaster.jpeg_core_output_dimensions cinfo) h = .ok ((), h')

/-- `jpeg_calc_output_dimensions(cinfo)` never faults for any `scale_num`, `scale_denom` on a
`ValidDecompDimsInput h cinfo false` object (cleanly unwinding `ERREXIT1(JERR_BAD_STATE)` if not in
`DSTATE_READY`, and adapting component DCT scales + downsampled dimensions when in `DSTATE_READY`). -/
def Goal.jpeg_calc_output_dimensions_safety : Prop :=
  ∀ (h : C.Heap) (cinfo : C.DecompPtr),
    ValidDecompDimsInput h cinfo false →
    ∃ res h', C.run (Mozjpeg.Jdmaster.jpeg_calc_output_dimensions cinfo) h = .ok (res, h')

/-- Concrete non-vacuity witness: Sharp's shrink-on-load `scale_num = 1, scale_denom = 4`
on a 1001×753 3-component YCbCr 4:2:0 JPEG produces `output_width = 251`, `output_height = 189`. -/
def Goal.jpeg_calc_output_dimensions_shrink_nonvacuous : Prop :=
  let comp0 : C.JpegCompInfo := { componentId := 1, componentIndex := 0, hSampFactor := 2, vSampFactor := 2 }
  let comp1 : C.JpegCompInfo := { componentId := 2, componentIndex := 1, hSampFactor := 1, vSampFactor := 1 }
  let comp2 : C.JpegCompInfo := { componentId := 3, componentIndex := 2, hSampFactor := 1, vSampFactor := 1 }
  let dc : C.JpegDecompressStruct := {
    err := .ref (.err 0) 0
    mem := .ref (.mem 0) 0
    globalState := Mozjpeg.JpeglibH.DSTATE_READY
    imageWidth := 1001
    imageHeight := 753
    numComponents := 3
    jpegColorSpace := Mozjpeg.JpeglibH.JCS_YCbCr
    outColorSpace := Mozjpeg.JpeglibH.JCS_RGB
    scaleNum := 1
    scaleDenom := 4
    maxHSampFactor := 2
    maxVSampFactor := 2
    compInfo := .ref (.comp 0) 0
    master := .ref (.master 0) 0
    inputctl := .ref (.inputctl 0) 0
    marker := .ref (.marker 0) 0
  }
  let h : C.Heap := {
    errMgrs := C.upd C.Tbl.empty 0 (some #[{}])
    mems := C.upd C.Tbl.empty 0 (some #[{}])
    masters := C.upd C.Tbl.empty 0 (some #[{}])
    inputctls := C.upd C.Tbl.empty 0 (some #[{}])
    markers := C.upd C.Tbl.empty 0 (some #[{}])
    comps := C.upd C.Tbl.empty 0 (some #[comp0, comp1, comp2])
    decomps := C.upd C.Tbl.empty 0 (some #[dc])
  }
  ∃ h' dcs',
    C.run (Mozjpeg.Jdmaster.jpeg_calc_output_dimensions (.ref (.decomp 0) 0)) h = .ok (.ok (), h') ∧
    h'.decomps 0 = some dcs' ∧
    (dcs'[0]!).outputWidth = 251 ∧
    (dcs'[0]!).outputHeight = 189

/-! ## Remaining Tier 0 decompression goals (not done yet) -/

/-- `jpeg_CreateDecompress`: not done yet (`jdapimin.c`, `jmemmgr.c`, `jmemnobs.c`). -/
def Goal.jpeg_CreateDecompress_safety : Prop := True
/-- `jpeg_mem_src`: not done yet (`jdatasrc.c`). -/
def Goal.jpeg_mem_src_safety : Prop := True
/-- `jpeg_read_header`: not done yet (`jdapimin.c`, `jdinput.c`, `jdmarker.c`). -/
def Goal.jpeg_read_header_safety : Prop := True
/-- `jpeg_consume_input`: not done yet (`jdapimin.c`, `jdinput.c`, `jdmarker.c`). -/
def Goal.jpeg_consume_input_safety : Prop := True
/-- `jpeg_resync_to_restart`: not done yet (`jdmarker.c`). -/
def Goal.jpeg_resync_to_restart_safety : Prop := True
/-- `jpeg_start_decompress`: not done yet (`jdapistd.c`, `jdmaster.c`, entropy/IDCT/upsample/color). -/
def Goal.jpeg_start_decompress_safety : Prop := True
/-- `jpeg_read_scanlines`: not done yet (`jdapistd.c`, `jdmainct.c`, `jdcoefct.c`, `jdhuff.c`, `jidct*.c`, `jdcolor.c`). -/
def Goal.jpeg_read_scanlines_safety : Prop := True
/-- `jpeg_read_raw_data`: not done yet (`jdapistd.c`). -/
def Goal.jpeg_read_raw_data_safety : Prop := True
/-- `jpeg_finish_decompress`: not done yet (`jdapimin.c`). -/
def Goal.jpeg_finish_decompress_safety : Prop := True

end MozjpegF.Spec.Safety
