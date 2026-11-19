import ZlibNgF.Spec.Safety.Goals
import ZlibNgF.Spec.Functional.Goals

/-!
# Proofs of `compressBound` safety and functional specifications (`ZlibNgF`)
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.CompressBound
open ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNgF.Spec.Functional

private theorem u64_eq_of_toNat {a b : UInt64} (h : a.toNat = b.toNat) : a = b := by
  cases a with | ofBitVec va =>
  cases b with | ofBitVec vb =>
  congr 1
  exact BitVec.eq_of_toNat_eq h

theorem compressBound_safety : Goal.compressBound_safety := by
  intro h sourceLen
  unfold ZlibNg.Compress.compressBound ZlibNg.Compress.DEFLATE_BOUND_COMPLEN
  exact ⟨_, rfl⟩

theorem compressBound_functional : Goal.compressBound_functional := by
  intro h sourceLen hbound
  unfold ZlibNg.Compress.compressBound ZlibNg.Compress.DEFLATE_BOUND_COMPLEN
    ZlibNg.Compress.DEFLATE_QUICK_OVERHEAD ZlibNg.Compress.DEFLATE_BLOCK_OVERHEAD
    ZlibNg.Compress.ZLIB_WRAPLEN
  have hfalse : ¬ ((0 : UInt64) > 0) := by decide
  simp only [C.run, hfalse, ↓reduceIte, pure]
  refine ⟨_, rfl, ?_⟩
  have h_mul1 : sourceLen * 1 = sourceLen := UInt64.mul_one sourceLen
  rw [h_mul1]
  have hs_lt : sourceLen.toNat + 7 < 2 ^ 64 := by omega
  have h_add7 : (sourceLen + 7).toNat = sourceLen.toNat + 7 := by
    rw [UInt64.toNat_add]
    have h7 : (7 : UInt64).toNat = 7 := rfl
    rw [h7]
    exact Nat.mod_eq_of_lt hs_lt
  have h_shr3 : ((sourceLen + 7) >>> 3).toNat = (sourceLen.toNat + 7) / 8 := by
    rw [UInt64.toNat_shiftRight]
    have h3 : (3 : UInt64).toNat % 64 = 3 := rfl
    rw [h3, h_add7, Nat.shiftRight_eq_div_pow]
  let c0 : UInt64 := if sourceLen == 0 then 1 else 0
  let c9 : UInt64 := if sourceLen < 9 then 1 else 0
  let q : UInt64 := (sourceLen + 7) >>> 3
  have hc0 : c0.toNat = (if sourceLen.toNat = 0 then 1 else 0) := by
    dsimp [c0]
    by_cases hz : sourceLen = 0
    · subst hz; rfl
    · have hzn : sourceLen.toNat ≠ 0 := fun h0 => hz (u64_eq_of_toNat h0)
      have hbeq : (sourceLen == 0) = false := beq_false_of_ne hz
      simp [hbeq, hzn]
  have hc9 : c9.toNat = (if sourceLen.toNat < 9 then 1 else 0) := by
    dsimp [c9]
    by_cases h9 : sourceLen < 9
    · have h9n : sourceLen.toNat < 9 := h9
      simp [h9, h9n]
    · have h9n : ¬ sourceLen.toNat < 9 := h9
      simp [h9, h9n]
  have hb3 : (((3 : UInt64) + 15 + 6) >>> 3) = (3 : UInt64) := rfl
  rw [hb3]
  change (sourceLen + c0 + c9 + q + 3 + 6).toNat =
      sourceLen.toNat + (if sourceLen.toNat = 0 then 1 else 0) +
        (if sourceLen.toNat < 9 then 1 else 0) + (sourceLen.toNat + 7) / 8 + 9 ∧
    sourceLen.toNat < (sourceLen + c0 + c9 + q + 3 + 6).toNat
  have hc0_le : c0.toNat ≤ 1 := by rw [hc0]; split <;> omega
  have hc9_le : c9.toNat ≤ 1 := by rw [hc9]; split <;> omega
  have hq_eq : q.toNat = (sourceLen.toNat + 7) / 8 := h_shr3
  have hn3 : (3 : UInt64).toNat = 3 := rfl
  have hn6 : (6 : UInt64).toNat = 6 := rfl
  have hsum_lt : sourceLen.toNat + c0.toNat + c9.toNat + q.toNat + 3 + 6 < 2 ^ 64 := by omega
  have ha1 : (sourceLen + c0).toNat = sourceLen.toNat + c0.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have ha2 : (sourceLen + c0 + c9).toNat = sourceLen.toNat + c0.toNat + c9.toNat := by
    rw [UInt64.toNat_add, ha1]; exact Nat.mod_eq_of_lt (by omega)
  have ha3 : (sourceLen + c0 + c9 + q).toNat = sourceLen.toNat + c0.toNat + c9.toNat + q.toNat := by
    rw [UInt64.toNat_add, ha2]; exact Nat.mod_eq_of_lt (by omega)
  have ha4 : (sourceLen + c0 + c9 + q + 3).toNat = sourceLen.toNat + c0.toNat + c9.toNat + q.toNat + 3 := by
    rw [UInt64.toNat_add, ha3, hn3]; exact Nat.mod_eq_of_lt (by omega)
  have ha5 : (sourceLen + c0 + c9 + q + 3 + 6).toNat =
      sourceLen.toNat + c0.toNat + c9.toNat + q.toNat + 3 + 6 := by
    rw [UInt64.toNat_add, ha4, hn6]; exact Nat.mod_eq_of_lt hsum_lt
  rw [ha5, hc0, hc9, hq_eq]
  omega

end ZlibNgF.Proof.CompressBound
