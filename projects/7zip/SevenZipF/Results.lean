import SevenZipF
import SevenZipF.ResultsCheck

namespace SevenZipF.Results
open Lean Elab Command

def proved : List (Name × Name) := [
  (``SevenZipF.Spec.Safety.Goal.null_ptr_add_zero_ub, ``SevenZipF.Proof.RuntimeUb.null_ptr_add_zero_ub),
  (``SevenZipF.Spec.Safety.Goal.dangling_ptr_add_zero_ub, ``SevenZipF.Proof.RuntimeUb.dangling_ptr_add_zero_ub),
  (``SevenZipF.Spec.Safety.Goal.null_ptr_diff_null_ub, ``SevenZipF.Proof.RuntimeUb.null_ptr_diff_null_ub),
  (``SevenZipF.Spec.Safety.Goal.cross_object_ptr_diff_ub, ``SevenZipF.Proof.RuntimeUb.cross_object_ptr_diff_ub),
  (``SevenZipF.Spec.Safety.Goal.null_memset_zero_ub, ``SevenZipF.Proof.RuntimeUb.null_memset_zero_ub),
  (``SevenZipF.Model.Goal.model_folder_dag_acyclic, ``SevenZipF.Model.model_folder_dag_acyclic_proved),
  (``SevenZipF.Model.Goal.model_extract_cache_coherence, ``SevenZipF.Model.model_extract_cache_coherence_proved),
  (``SevenZipF.Model.Goal.model_bcj2_overlap_init, ``SevenZipF.Model.model_bcj2_overlap_init_proved),
  (``SevenZipF.Model.Goal.model_ppmd7_arena_init, ``SevenZipF.Model.model_ppmd7_arena_init_proved),
  (``SevenZipF.Model.Goal.model_ppmd7_splitBlock_conservation, ``SevenZipF.Model.model_ppmd7_splitBlock_conservation_proved),
  (``SevenZipF.Model.Goal.model_lzma_fast_lookahead_bounds, ``SevenZipF.Model.model_lzma_fast_lookahead_bounds_proved),
  (``SevenZipF.Model.Goal.model_lzma2_control_guards, ``SevenZipF.Model.model_lzma2_control_guards_proved)
]

def notDone : List Name := [
  ``SevenZipF.Spec.Safety.Goal.c_szArEx_extract_safety,
  ``SevenZipF.Spec.Safety.Goal.c_bcj2Dec_decode_safety,
  ``SevenZipF.Spec.Safety.Goal.c_ppmd7_decode_safety,
  ``SevenZipF.Spec.Safety.Goal.c_lzma2Dec_decode_safety
]

def required : List Name := []

#eval checkWith proved notDone required inLibrary

end SevenZipF.Results
