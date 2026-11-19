import ZlibNgF.Proof.«inftrees.c.base»
import ZlibNgF.Math.BitReverse

/-!
# `zng_bitreverse16` is the reversal of the 16 bits (`ZlibNgF`)
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNgF.Math.BitReverse

/-- One trip of the loop of `zng_bitreverse16`. -/
def revStep (v : UInt16) (i : Nat) (r : UInt16) : UInt16 :=
  if ((v >>> i.toUInt16) &&& 1 != 0) = true then r ||| ((1 : UInt16) <<< (15 - i).toUInt16) else r

theorem ite_yield {c : Prop} [Decidable c] (a b : UInt16) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep UInt16)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem bitreverse16_unroll (v : UInt16) : zng_bitreverse16 v =
    revStep v 15 (revStep v 14 (revStep v 13 (revStep v 12 (revStep v 11 (revStep v 10 (revStep v 9
      (revStep v 8 (revStep v 7 (revStep v 6 (revStep v 5 (revStep v 4 (revStep v 3 (revStep v 2
      (revStep v 1 (revStep v 0 0))))))))))))))) := by
  unfold zng_bitreverse16
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range', List.forIn_cons,
    List.forIn_nil, ite_yield, revStep, pure_bind, Id.run_pure]

theorem revStep_testBit (v : UInt16) (i : Nat) (hi : i < 16) (r : UInt16) (j : Nat) :
    (revStep v i r).toNat.testBit j = (r.toNat.testBit j || (v.toNat.testBit i && decide (i + j = 15))) := by
  have hc : (((v >>> i.toUInt16) &&& 1 != 0) = true) ↔ v.toNat.testBit i = true := by
    have e : ((v >>> i.toUInt16) &&& 1).toNat = (v.toNat >>> i) &&& 1 := by
      rw [UInt16.toNat_and, UInt16.toNat_shiftRight]
      have : i.toUInt16.toNat % 16 = i := by
        rw [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega
      rw [this]
      rfl
    have e2 : ((v >>> i.toUInt16) &&& 1 != 0) = true ↔ ((v >>> i.toUInt16) &&& 1).toNat ≠ 0 := by
      rw [bne_iff_ne, ne_eq, ne_eq, ← UInt16.toNat_inj]
      rfl
    rw [e2, e, Nat.testBit, Nat.and_comm]
    simp
  have hm : ((1 : UInt16) <<< (15 - i).toUInt16).toNat = 2 ^ (15 - i) := by
    rw [UInt16.toNat_shiftLeft]
    have : (15 - i).toUInt16.toNat % 16 = 15 - i := by
      rw [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega
    rw [this]
    have : (1 : UInt16).toNat = 1 := rfl
    rw [this, Nat.shiftLeft_eq, Nat.one_mul]
    apply Nat.mod_eq_of_lt
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  unfold revStep
  by_cases hb : v.toNat.testBit i = true
  · rw [ite_eq_left (hc.2 hb), UInt16.toNat_or, Nat.testBit_or, hm, Nat.testBit_two_pow, hb]
    simp only [Bool.true_and]
    congr 1
    simp only [decide_eq_decide]
    omega
  · rw [ite_eq_right (fun x => hb (hc.1 x))]
    simp at hb
    simp [hb]

theorem bitreverse16_toNat (v : UInt16) : (zng_bitreverse16 v).toNat = rev 16 v.toNat := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [bitreverse16_unroll, testBit_rev]
  simp only [revStep_testBit v _ (by decide : (15 : Nat) < 16), revStep_testBit v _ (by decide : (14 : Nat) < 16),
    revStep_testBit v _ (by decide : (13 : Nat) < 16), revStep_testBit v _ (by decide : (12 : Nat) < 16),
    revStep_testBit v _ (by decide : (11 : Nat) < 16), revStep_testBit v _ (by decide : (10 : Nat) < 16),
    revStep_testBit v _ (by decide : (9 : Nat) < 16), revStep_testBit v _ (by decide : (8 : Nat) < 16),
    revStep_testBit v _ (by decide : (7 : Nat) < 16), revStep_testBit v _ (by decide : (6 : Nat) < 16),
    revStep_testBit v _ (by decide : (5 : Nat) < 16), revStep_testBit v _ (by decide : (4 : Nat) < 16),
    revStep_testBit v _ (by decide : (3 : Nat) < 16), revStep_testBit v _ (by decide : (2 : Nat) < 16),
    revStep_testBit v _ (by decide : (1 : Nat) < 16), revStep_testBit v _ (by decide : (0 : Nat) < 16)]
  have z : (0 : UInt16).toNat = 0 := rfl
  rw [z, Nat.zero_testBit]
  by_cases hj : j < 16
  · have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
        j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · have e : ∀ i, decide (i + j = 15) = false := fun i => by simp; omega
    simp only [e, hj, Bool.and_false, Bool.or_false, decide_false, Bool.false_and]

end ZlibNgF.Proof.Inftrees
