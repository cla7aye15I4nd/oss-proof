import MozjpegF.Spec.Safety.Goals
import MozjpegF.Spec.Functional.Goals

/-!
# Proofs of `jutils.c` safety and functional specifications (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.Jutils
open C MozjpegF.Spec MozjpegF.Spec.Safety MozjpegF.Spec.Functional

theorem jdiv_round_up_functional : Goal.jdiv_round_up_functional := by
  intro h a b ha hb hsum
  unfold Mozjpeg.Jutils.jdiv_round_up
  have h1 : -(2 ^ 63 : Int) ≤ a.toInt + b.toInt := by omega
  rw [i64Add_eq a b h1 hsum, pure_bind_m]
  have hab : (Int64.ofInt (a.toInt + b.toInt)).toInt = a.toInt + b.toInt :=
    toInt_ofInt64 h1 hsum
  have hone : (1 : Int64).toInt = 1 := rfl
  have hsub1 : -(2 ^ 63 : Int) ≤ (Int64.ofInt (a.toInt + b.toInt)).toInt - (1 : Int64).toInt := by
    rw [hab, hone]; omega
  have hsub2 : (Int64.ofInt (a.toInt + b.toInt)).toInt - (1 : Int64).toInt < 2 ^ 63 := by
    rw [hab, hone]; omega
  rw [i64Sub_eq _ 1 hsub1 hsub2, pure_bind_m]
  have hnum : (Int64.ofInt ((Int64.ofInt (a.toInt + b.toInt)).toInt - (1 : Int64).toInt)).toInt =
      a.toInt + b.toInt - 1 := by
    rw [toInt_ofInt64 hsub1 hsub2, hab, hone]
  rw [i64Div_nonneg_eq _ b (by rw [hnum]; omega) hb]
  refine ⟨_, rfl, ?_⟩
  have hdiv_lt : Int.tdiv (a.toInt + b.toInt - 1) b.toInt < 2 ^ 63 := by
    have := Int.tdiv_le_self b.toInt (by omega : 0 ≤ a.toInt + b.toInt - 1)
    omega
  have hdiv_ge : 0 ≤ Int.tdiv (a.toInt + b.toInt - 1) b.toInt :=
    Int.tdiv_nonneg (by omega) (by omega)
  rw [hnum, toInt_ofInt64 (by omega) hdiv_lt, Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem jdiv_round_up_safety : Goal.jdiv_round_up_safety := by
  intro h a b ha hb hsum
  obtain ⟨r, hr, _⟩ := jdiv_round_up_functional h a b ha hb hsum
  exact ⟨r, hr⟩

theorem jround_up_safety : Goal.jround_up_safety := by
  intro h a b ha hb hsum
  unfold Mozjpeg.Jutils.jround_up
  have hblt := Int64.toInt_lt b
  have hone : (1 : Int64).toInt = 1 := rfl
  have hb1_lo : -(2 ^ 63 : Int) ≤ b.toInt - (1 : Int64).toInt := by rw [hone]; omega
  have hb1_hi : b.toInt - (1 : Int64).toInt < 2 ^ 63 := by rw [hone]; omega
  rw [i64Sub_eq b 1 hb1_lo hb1_hi, pure_bind_m]
  have hbm1 : (Int64.ofInt (b.toInt - (1 : Int64).toInt)).toInt = b.toInt - 1 := by
    rw [toInt_ofInt64 hb1_lo hb1_hi, hone]
  have ha1_lo : -(2 ^ 63 : Int) ≤ a.toInt + (Int64.ofInt (b.toInt - (1 : Int64).toInt)).toInt := by
    rw [hbm1]; omega
  have ha1_hi : a.toInt + (Int64.ofInt (b.toInt - (1 : Int64).toInt)).toInt < 2 ^ 63 := by
    rw [hbm1]; omega
  rw [i64Add_eq a _ ha1_lo ha1_hi, pure_bind_m]
  have ha1 : (Int64.ofInt (a.toInt + (Int64.ofInt (b.toInt - (1 : Int64).toInt)).toInt)).toInt =
      a.toInt + b.toInt - 1 := by
    rw [toInt_ofInt64 ha1_lo ha1_hi, hbm1]; omega
  rw [i64Mod_nonneg_eq _ b (by rw [ha1]; omega) hb, pure_bind_m]
  have hmod_ge : 0 ≤ Int.tmod (a.toInt + b.toInt - 1) b.toInt := Int.tmod_nonneg b.toInt (by omega)
  have hmod_lt : Int.tmod (a.toInt + b.toInt - 1) b.toInt < b.toInt := by
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    exact Int.emod_lt_of_pos (a.toInt + b.toInt - 1) hb
  have hrem : (Int64.ofInt (Int.tmod (a.toInt + b.toInt - 1) b.toInt)).toInt =
      Int.tmod (a.toInt + b.toInt - 1) b.toInt :=
    toInt_ofInt64 (by omega) (by omega)
  rw [i64Sub_eq _ _ (by rw [ha1, hrem]; omega) (by rw [ha1, hrem]; omega)]
  exact ⟨_, rfl⟩

theorem jzero_far_safety : Goal.jzero_far_safety := by
  intro h target n ⟨b, off, data, hp, hget, hle⟩
  subst hp
  unfold Mozjpeg.Jutils.jzero_far C.run C.Ptr.memset
  have hsp : C.Space.get h (C.BRef.heap b) = some data := hget
  have hro : C.Space.ro h (C.BRef.heap b) = false := rfl
  simp only [hsp, hro, Bool.false_eq_true, ↓reduceIte, hle]
  exact ⟨_, rfl⟩

end MozjpegF.Proof.Jutils
