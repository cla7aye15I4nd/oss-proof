import ZlibNgF.Spec.Safety.Goals
import ZlibNgF.Spec.Functional.Goals

/-!
# Proofs of `compressBound` and `compressBound_z` safety and functional specifications (`ZlibNgF`)
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.CompressBound
open ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNgF.Spec.Functional

private theorem u64_eq_of_toNat {a b : UInt64} (h : a.toNat = b.toNat) : a = b := by
  cases a with | ofBitVec va =>
  cases b with | ofBitVec vb =>
  congr 1
  exact BitVec.eq_of_toNat_eq h

/-- The run of `compressBound`: the saturated sum of `compressBound_z`, capped at `ULONG_MAX`. -/
private theorem compressBound_run (h : C.Heap) (sourceLen : UInt64) :
    let b : UInt64 := sourceLen
      + (if sourceLen == 0 then 1 else 0)
      + (if sourceLen < 9 then 1 else 0)
      + ZlibNg.Compress.DEFLATE_QUICK_OVERHEAD sourceLen
      + ZlibNg.Compress.DEFLATE_BLOCK_OVERHEAD
      + ZlibNg.Compress.ZLIB_WRAPLEN
    C.run (ZlibNg.Compress.compressBound sourceLen) h =
      .ok (ZlibNg.Zbuild.MIN ZlibNg.Compress.ULONG_MAX (if b < sourceLen then (-1 : Int64).toUInt64 else b), h) := by
  intro b
  unfold ZlibNg.Compress.compressBound ZlibNg.Compress.compressBound_z ZlibNg.Compress.DEFLATE_BOUND_COMPLEN
  have hfalse : ¬ ((0 : UInt64) > 0) := by decide
  simp only [C.run, hfalse, ↓reduceIte]
  rfl

theorem compressBound_safety : Goal.compressBound_safety := by
  intro h sourceLen
  exact ⟨_, compressBound_run h sourceLen⟩

theorem compressBound_functional : Goal.compressBound_functional := by
  intro h sourceLen hbound
  refine ⟨_, compressBound_run h sourceLen, ?_⟩
  unfold ZlibNg.Compress.DEFLATE_QUICK_OVERHEAD ZlibNg.Compress.DEFLATE_BLOCK_OVERHEAD
    ZlibNg.Compress.ZLIB_WRAPLEN
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
  change (ZlibNg.Zbuild.MIN ZlibNg.Compress.ULONG_MAX
      (if sourceLen + c0 + c9 + q + 3 + 6 < sourceLen then (-1 : Int64).toUInt64
        else sourceLen + c0 + c9 + q + 3 + 6)).toNat =
      sourceLen.toNat + (if sourceLen.toNat = 0 then 1 else 0) +
        (if sourceLen.toNat < 9 then 1 else 0) + (sourceLen.toNat + 7) / 8 + 9 ∧
    sourceLen.toNat < (ZlibNg.Zbuild.MIN ZlibNg.Compress.ULONG_MAX
      (if sourceLen + c0 + c9 + q + 3 + 6 < sourceLen then (-1 : Int64).toUInt64
        else sourceLen + c0 + c9 + q + 3 + 6)).toNat
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
  have hnlt : ¬ (sourceLen + c0 + c9 + q + 3 + 6 < sourceLen) := by
    show ¬ ((sourceLen + c0 + c9 + q + 3 + 6).toNat < sourceLen.toNat)
    rw [ha5]; omega
  have hmin : ZlibNg.Zbuild.MIN ZlibNg.Compress.ULONG_MAX (sourceLen + c0 + c9 + q + 3 + 6) =
      sourceLen + c0 + c9 + q + 3 + 6 := by
    unfold ZlibNg.Zbuild.MIN
    split
    · rfl
    · rename_i hng
      have hle : (sourceLen + c0 + c9 + q + 3 + 6).toNat ≥ ZlibNg.Compress.ULONG_MAX.toNat := by
        have : ¬ ((sourceLen + c0 + c9 + q + 3 + 6).toNat < ZlibNg.Compress.ULONG_MAX.toNat) := hng
        omega
      have hmax : ZlibNg.Compress.ULONG_MAX.toNat = 2 ^ 64 - 1 := rfl
      apply u64_eq_of_toNat
      have : (sourceLen + c0 + c9 + q + 3 + 6).toNat < 2 ^ 64 := UInt64.toNat_lt _
      omega
  simp only [hnlt, ↓reduceIte]
  rw [hmin, ha5, hc0, hc9, hq_eq]
  omega

/-- The run of `compressBound_z`: the `deflate_quick` sum, or `(z_size_t)-1` when it wraps. -/
private theorem compressBound_z_run (h : C.Heap) (sourceLen : UInt64) :
    let b : UInt64 := sourceLen
      + (if sourceLen == 0 then 1 else 0)
      + (if sourceLen < 9 then 1 else 0)
      + ZlibNg.Compress.DEFLATE_QUICK_OVERHEAD sourceLen
      + ZlibNg.Compress.DEFLATE_BLOCK_OVERHEAD
      + ZlibNg.Compress.ZLIB_WRAPLEN
    C.run (ZlibNg.Compress.compressBound_z sourceLen) h =
      .ok (if b < sourceLen then (-1 : Int64).toUInt64 else b, h) := by
  intro b
  unfold ZlibNg.Compress.compressBound_z ZlibNg.Compress.DEFLATE_BOUND_COMPLEN
  have hfalse : ¬ ((0 : UInt64) > 0) := by decide
  simp only [C.run, hfalse, ↓reduceIte]
  rfl

theorem compressBound_z_safety : Goal.compressBound_z_safety := by
  intro h sourceLen
  exact ⟨_, compressBound_z_run h sourceLen⟩

theorem compressBound_z_functional : Goal.compressBound_z_functional := by
  intro h sourceLen hbound
  refine ⟨_, compressBound_z_run h sourceLen, ?_⟩
  unfold ZlibNg.Compress.DEFLATE_QUICK_OVERHEAD ZlibNg.Compress.DEFLATE_BLOCK_OVERHEAD
    ZlibNg.Compress.ZLIB_WRAPLEN
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
  change (if sourceLen + c0 + c9 + q + 3 + 6 < sourceLen then (-1 : Int64).toUInt64
        else sourceLen + c0 + c9 + q + 3 + 6).toNat =
      sourceLen.toNat + (if sourceLen.toNat = 0 then 1 else 0) +
        (if sourceLen.toNat < 9 then 1 else 0) + (sourceLen.toNat + 7) / 8 + 9 ∧
    sourceLen.toNat < (if sourceLen + c0 + c9 + q + 3 + 6 < sourceLen then (-1 : Int64).toUInt64
        else sourceLen + c0 + c9 + q + 3 + 6).toNat
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
  have hnlt : ¬ (sourceLen + c0 + c9 + q + 3 + 6 < sourceLen) := by
    show ¬ ((sourceLen + c0 + c9 + q + 3 + 6).toNat < sourceLen.toNat)
    rw [ha5]; omega
  simp only [hnlt, ↓reduceIte]
  rw [ha5, hc0, hc9, hq_eq]
  omega

end ZlibNgF.Proof.CompressBound
