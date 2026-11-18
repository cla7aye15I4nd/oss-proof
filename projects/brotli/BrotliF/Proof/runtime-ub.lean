import BrotliF.Spec.Safety.Goals

/-!
# Proofs of strict ISO C17 runtime UB rejection (`BrotliF`)
-/

namespace BrotliF.Proof.RuntimeUb
open BrotliF.Spec BrotliF.Spec.Safety

theorem null_ptr_add_zero_ub : Goal.null_ptr_add_zero_ub := by
  intro h
  exact ⟨"arithmetic on a null pointer", rfl⟩

theorem dangling_ptr_add_zero_ub : Goal.dangling_ptr_add_zero_ub := by
  intro h r off hnone
  refine ⟨"arithmetic on a dangling pointer", ?_⟩
  simp [C.Ptr.add, hnone]

theorem null_ptr_diff_null_ub : Goal.null_ptr_diff_null_ub := by
  intro h
  exact ⟨"difference involving a null pointer", rfl⟩

theorem cross_object_ptr_diff_ub : Goal.cross_object_ptr_diff_ub := by
  intro h r1 r2 o1 o2 hne
  refine ⟨"difference of pointers into different objects", ?_⟩
  simp [C.Ptr.diff, hne]

theorem null_memset_zero_ub : Goal.null_memset_zero_ub := by
  intro h b
  exact ⟨"memset on a null pointer", rfl⟩

end BrotliF.Proof.RuntimeUb
