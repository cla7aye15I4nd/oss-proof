import LibarchiveF
import LibarchiveF.ResultsCheck

namespace LibarchiveF.Results
open Lean Elab Command

def proved : List (Name × Name) := [
  (``LibarchiveF.Spec.Safety.Goal.null_ptr_add_zero_ub, ``LibarchiveF.Proof.RuntimeUb.null_ptr_add_zero_ub),
  (``LibarchiveF.Spec.Safety.Goal.dangling_ptr_add_zero_ub, ``LibarchiveF.Proof.RuntimeUb.dangling_ptr_add_zero_ub),
  (``LibarchiveF.Spec.Safety.Goal.null_ptr_diff_null_ub, ``LibarchiveF.Proof.RuntimeUb.null_ptr_diff_null_ub),
  (``LibarchiveF.Spec.Safety.Goal.cross_object_ptr_diff_ub, ``LibarchiveF.Proof.RuntimeUb.cross_object_ptr_diff_ub),
  (``LibarchiveF.Spec.Safety.Goal.null_memset_zero_ub, ``LibarchiveF.Proof.RuntimeUb.null_memset_zero_ub),
  (``LibarchiveF.Model.Goal.model_rar5_init_inv, ``LibarchiveF.Model.model_rar5_init_inv_proved),
  (``LibarchiveF.Model.Goal.model_rar5_cleanup_preserves_inv, ``LibarchiveF.Model.model_rar5_cleanup_preserves_inv_proved),
  (``LibarchiveF.Model.Goal.model_rar5_skip_preserves_inv, ``LibarchiveF.Model.model_rar5_skip_preserves_inv_proved),
  (``LibarchiveF.Model.Goal.model_rar5_throttle_no_deadlock, ``LibarchiveF.Model.model_rar5_throttle_no_deadlock_proved),
  (``LibarchiveF.Model.Goal.model_rar5_bitreader_progress, ``LibarchiveF.Model.model_rar5_bitreader_progress_proved),
  (``LibarchiveF.Model.Goal.model_7zip_folder_port_conservation, ``LibarchiveF.Model.model_7zip_folder_port_conservation_proved),
  (``LibarchiveF.Model.Goal.model_7zip_substream_le_folder, ``LibarchiveF.Model.model_7zip_substream_le_folder_proved),
  (``LibarchiveF.Model.Goal.model_7zip_ppmd_restart_safe, ``LibarchiveF.Model.model_7zip_ppmd_restart_safe_proved)
]

def notDone : List Name := [
  ``LibarchiveF.Spec.Safety.Goal.c_rar5_format_safety,
  ``LibarchiveF.Spec.Safety.Goal.c_sevenZip_format_safety,
  ``LibarchiveF.Spec.Safety.Goal.c_ppmd7_allocator_safety
]

def required : List Name := []

#eval checkWith proved notDone required inLibrary

end LibarchiveF.Results
