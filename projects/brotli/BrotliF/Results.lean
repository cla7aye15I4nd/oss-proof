import BrotliF
import BrotliF.ResultsCheck

namespace BrotliF.Results
open Lean Elab Command

def proved : List (Name × Name) := [
  (``BrotliF.Spec.Safety.Goal.null_ptr_add_zero_ub, ``BrotliF.Proof.RuntimeUb.null_ptr_add_zero_ub),
  (``BrotliF.Spec.Safety.Goal.dangling_ptr_add_zero_ub, ``BrotliF.Proof.RuntimeUb.dangling_ptr_add_zero_ub),
  (``BrotliF.Spec.Safety.Goal.null_ptr_diff_null_ub, ``BrotliF.Proof.RuntimeUb.null_ptr_diff_null_ub),
  (``BrotliF.Spec.Safety.Goal.cross_object_ptr_diff_ub, ``BrotliF.Proof.RuntimeUb.cross_object_ptr_diff_ub),
  (``BrotliF.Spec.Safety.Goal.null_memset_zero_ub, ``BrotliF.Proof.RuntimeUb.null_memset_zero_ub)
]

def notDone : List Name := [
  ``BrotliF.Spec.Safety.Goal.c_decompressStream_safety,
  ``BrotliF.Spec.Safety.Goal.c_decompress_oneshot_safety,
  ``BrotliF.Spec.Safety.Goal.c_takeOutput_borrow_safety,
  ``BrotliF.Spec.Safety.Goal.c_attachDictionary_safety
]

def required : List Name := []

#eval checkWith proved notDone required inLibrary

end BrotliF.Results
