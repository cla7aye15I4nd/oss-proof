import ZstdF
import ZstdF.ResultsCheck

namespace ZstdF.Results
open Lean Elab Command

def proved : List (Name × Name) := [
  (``ZstdF.Spec.Safety.Goal.null_ptr_add_zero_ub, ``ZstdF.Proof.RuntimeUb.null_ptr_add_zero_ub),
  (``ZstdF.Spec.Safety.Goal.dangling_ptr_add_zero_ub, ``ZstdF.Proof.RuntimeUb.dangling_ptr_add_zero_ub),
  (``ZstdF.Spec.Safety.Goal.null_ptr_diff_null_ub, ``ZstdF.Proof.RuntimeUb.null_ptr_diff_null_ub),
  (``ZstdF.Spec.Safety.Goal.cross_object_ptr_diff_ub, ``ZstdF.Proof.RuntimeUb.cross_object_ptr_diff_ub),
  (``ZstdF.Spec.Safety.Goal.null_memset_zero_ub, ``ZstdF.Proof.RuntimeUb.null_memset_zero_ub)
]

def notDone : List Name := [
  ``ZstdF.Spec.Safety.Goal.c_decompressStream_safety,
  ``ZstdF.Spec.Safety.Goal.c_decompress_oneshot_safety,
  ``ZstdF.Spec.Safety.Goal.c_ddict_lifecycle_safety,
  ``ZstdF.Spec.Safety.Goal.c_frame_query_safety
]

def required : List Name := []

#eval checkWith proved notDone required inLibrary

end ZstdF.Results
