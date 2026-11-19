import MozjpegF
import MozjpegF.ResultsCheck

namespace MozjpegF.Results
open Lean Elab Command

def proved : List (Name × Name) := [
  (``MozjpegF.Spec.Safety.Goal.null_ptr_add_zero_ub, ``MozjpegF.Proof.RuntimeUb.null_ptr_add_zero_ub),
  (``MozjpegF.Spec.Safety.Goal.dangling_ptr_add_zero_ub, ``MozjpegF.Proof.RuntimeUb.dangling_ptr_add_zero_ub),
  (``MozjpegF.Spec.Safety.Goal.null_ptr_diff_null_ub, ``MozjpegF.Proof.RuntimeUb.null_ptr_diff_null_ub),
  (``MozjpegF.Spec.Safety.Goal.cross_object_ptr_diff_ub, ``MozjpegF.Proof.RuntimeUb.cross_object_ptr_diff_ub),
  (``MozjpegF.Spec.Safety.Goal.null_memset_zero_ub, ``MozjpegF.Proof.RuntimeUb.null_memset_zero_ub),
  (``MozjpegF.Spec.Safety.Goal.jdiv_round_up_safety, ``MozjpegF.Proof.Jutils.jdiv_round_up_safety),
  (``MozjpegF.Spec.Safety.Goal.jround_up_safety, ``MozjpegF.Proof.Jutils.jround_up_safety),
  (``MozjpegF.Spec.Safety.Goal.jzero_far_safety, ``MozjpegF.Proof.Jutils.jzero_far_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_std_error_safety, ``MozjpegF.Proof.Jerror.jpeg_std_error_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_std_error_nonvacuous, ``MozjpegF.Proof.Jerror.jpeg_std_error_nonvacuous),
  (``MozjpegF.Spec.Safety.Goal.jpeg_abort_safety, ``MozjpegF.Proof.Jdapimin.jpeg_abort_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_destroy_safety, ``MozjpegF.Proof.Jdapimin.jpeg_destroy_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_abort_decompress_safety, ``MozjpegF.Proof.Jdapimin.jpeg_abort_decompress_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_destroy_decompress_safety, ``MozjpegF.Proof.Jdapimin.jpeg_destroy_decompress_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_input_complete_safety, ``MozjpegF.Proof.Jdapimin.jpeg_input_complete_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_has_multiple_scans_safety, ``MozjpegF.Proof.Jdapimin.jpeg_has_multiple_scans_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_save_markers_safety, ``MozjpegF.Proof.Jdmarker.jpeg_save_markers_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_core_output_dimensions_safety, ``MozjpegF.Proof.Jdmaster.jpeg_core_output_dimensions_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_calc_output_dimensions_safety, ``MozjpegF.Proof.Jdmaster.jpeg_calc_output_dimensions_safety),
  (``MozjpegF.Spec.Safety.Goal.jpeg_calc_output_dimensions_shrink_nonvacuous, ``MozjpegF.Proof.Jdmaster.jpeg_calc_output_dimensions_shrink_nonvacuous),
  (``MozjpegF.Spec.Functional.Goal.jdiv_round_up_functional, ``MozjpegF.Proof.Jutils.jdiv_round_up_functional),
  (``MozjpegF.Spec.Functional.Goal.jpeg_std_error_functional, ``MozjpegF.Proof.Jerror.jpeg_std_error_functional),
  (``MozjpegF.Spec.Functional.Goal.jpeg_core_output_dimensions_shrink_functional, ``MozjpegF.Proof.Jdmaster.jpeg_core_output_dimensions_shrink_functional)
]

def notDone : List Name := [
  ``MozjpegF.Spec.Safety.Goal.jpeg_CreateDecompress_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_mem_src_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_read_header_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_consume_input_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_resync_to_restart_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_start_decompress_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_read_scanlines_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_read_raw_data_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_finish_decompress_safety
]

def required : List Name := [
  ``MozjpegF.Spec.Safety.Goal.null_ptr_add_zero_ub,
  ``MozjpegF.Spec.Safety.Goal.dangling_ptr_add_zero_ub,
  ``MozjpegF.Spec.Safety.Goal.null_ptr_diff_null_ub,
  ``MozjpegF.Spec.Safety.Goal.cross_object_ptr_diff_ub,
  ``MozjpegF.Spec.Safety.Goal.null_memset_zero_ub,
  ``MozjpegF.Spec.Safety.Goal.jdiv_round_up_safety,
  ``MozjpegF.Spec.Safety.Goal.jround_up_safety,
  ``MozjpegF.Spec.Safety.Goal.jzero_far_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_std_error_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_std_error_nonvacuous,
  ``MozjpegF.Spec.Safety.Goal.jpeg_abort_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_destroy_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_abort_decompress_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_destroy_decompress_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_input_complete_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_has_multiple_scans_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_save_markers_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_core_output_dimensions_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_calc_output_dimensions_safety,
  ``MozjpegF.Spec.Safety.Goal.jpeg_calc_output_dimensions_shrink_nonvacuous,
  ``MozjpegF.Spec.Functional.Goal.jdiv_round_up_functional,
  ``MozjpegF.Spec.Functional.Goal.jpeg_std_error_functional,
  ``MozjpegF.Spec.Functional.Goal.jpeg_core_output_dimensions_shrink_functional
]

#eval checkWith proved notDone required inLibrary

end MozjpegF.Results
