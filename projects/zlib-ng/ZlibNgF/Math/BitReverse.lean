/-!
# Bit reversal of the low `n` bits (`ZlibNgF`)

`rev n x` is the number whose bit `j < n` is bit `n - 1 - j` of `x`. `zng_inflate_table` keeps the next canonical
code reversed (`huff`); these lemmas place its table entries.
-/

set_option autoImplicit false

namespace ZlibNgF.Math.BitReverse

/-- The low `n` bits of `x` in reverse order. -/
noncomputable def rev : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 * 2 ^ n + rev n (x / 2)

@[simp] theorem rev_zero (x : Nat) : rev 0 x = 0 := rfl

theorem rev_succ (n x : Nat) : rev (n + 1) x = x % 2 * 2 ^ n + rev n (x / 2) := rfl

@[simp] theorem rev_of_zero (n : Nat) : rev n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rev_succ]; simp [ih]

theorem rev_lt (n x : Nat) : rev n x < 2 ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [rev_succ, Nat.pow_succ]
    have := ih (x / 2)
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> omega

theorem testBit_rev (n x j : Nat) : (rev n x).testBit j = (decide (j < n) && x.testBit (n - 1 - j)) := by
  induction n generalizing x j with
  | zero => simp
  | succ n ih =>
    rw [rev_succ, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (rev_lt n (x / 2))]
    by_cases hj : j < n
    · rw [ite_eq_left hj, ih, Nat.testBit_div_two]
      simp only [hj, decide_true, Bool.true_and, show j < n + 1 from by omega]
      congr 1
      omega
    · rw [ite_eq_right hj]
      by_cases he : j = n
      · subst he
        simp only [Nat.sub_self, Nat.testBit_zero, Nat.lt_succ_self, decide_true, Bool.true_and,
          show j + 1 - 1 - j = 0 from by omega]
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
      · have hgt : n < j := by omega
        have : x % 2 < 2 ^ (j - n) := by
          have := Nat.mod_lt x (show 2 > 0 by omega)
          have : 2 ≤ 2 ^ (j - n) := by
            have : 1 ≤ j - n := by omega
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [Nat.testBit_lt_two_pow this]
        simp only [show ¬ j < n + 1 from by omega, decide_false, Bool.false_and]

theorem rev_rev (n x : Nat) : rev n (rev n x) = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rev, testBit_rev, Nat.testBit_mod_two_pow]
  by_cases hj : j < n
  · simp only [hj, decide_true, Bool.true_and, show n - 1 - j < n from by omega]
    congr 1
    omega
  · simp [hj]

theorem rev_mod (n x : Nat) : rev n (x % 2 ^ n) = rev n x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rev, testBit_rev, Nat.testBit_mod_two_pow]
  by_cases hj : j < n
  · simp only [hj, decide_true, Bool.true_and, show n - 1 - j < n from by omega]
  · simp [hj]

theorem rev_inj {n x y : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) (e : rev n x = rev n y) : x = y := by
  have := congrArg (rev n) e
  rw [rev_rev, rev_rev, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  exact this

theorem rev_add_mul (a b x y : Nat) (hx : x < 2 ^ a) :
    rev (a + b) (x + y * 2 ^ a) = rev a x * 2 ^ b + rev b y := by
  induction a generalizing x with
  | zero =>
    have : x = 0 := by simp at hx; omega
    subst this
    simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, rev_succ, rev_succ]
    have e1 : (x + y * 2 ^ (a + 1)) % 2 = x % 2 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
    have e2 : (x + y * 2 ^ (a + 1)) / 2 = x / 2 + y * 2 ^ a := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (by omega : 0 < 2)]
    have hx2 : x / 2 < 2 ^ a := by rw [Nat.pow_succ] at hx; omega
    rw [e1, e2, ih _ hx2, Nat.pow_add, Nat.add_mul, Nat.mul_assoc]
    omega

theorem rev_mul_pow (a b x : Nat) : rev (a + b) (x * 2 ^ a) = rev b x := by
  have := rev_add_mul a b 0 x (Nat.two_pow_pos a)
  simpa [rev_lt] using this

end ZlibNgF.Math.BitReverse
