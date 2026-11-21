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

/-- A slot `j0` of a table of `c` index bits after `d` dropped bits, for the block `P` of the top `d` bits: its code
interval starts at `P * 2 ^ (16 - d) + rev c j0 * 2 ^ (16 - d - c)` (left-aligned in 16 bits). If that start lies in
the interval `[K, K + 2 ^ (16 - L))` of a length-`L` code `K` of block `P`, then `j0` is one of the slots
`rev 16 K / 2 ^ d + j * 2 ^ (L - d)` that the replication loop fills. -/
theorem slot_of_pos {d c L P K j0 : Nat} (hdc : d + c ≤ 16) (hdL : d < L) (hLc : L ≤ d + c)
    (hdvd : 2 ^ (16 - L) ∣ K) (hP : K / 2 ^ (16 - d) = P) (hj0 : j0 < 2 ^ c)
    (h1 : K ≤ P * 2 ^ (16 - d) + rev c j0 * 2 ^ (16 - d - c))
    (h2 : P * 2 ^ (16 - d) + rev c j0 * 2 ^ (16 - d - c) < K + 2 ^ (16 - L)) :
    ∃ j, j < 2 ^ (c - (L - d)) ∧ j0 = rev 16 K / 2 ^ d + j * 2 ^ (L - d) := by
  have hB' := Nat.two_pow_pos (16 - d - c)
  have hDa : 2 ^ (16 - L) = 2 ^ (16 - d - c) * 2 ^ (c - (L - d)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hG : 2 ^ (16 - d) = 2 ^ (16 - L) * 2 ^ (L - d) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hKd := Nat.div_add_mod K (2 ^ (16 - d))
  rw [hP] at hKd
  have hDG : 2 ^ (16 - L) ∣ 2 ^ (16 - d) := Nat.pow_dvd_pow 2 (by omega)
  have hDR : 2 ^ (16 - L) ∣ K % 2 ^ (16 - d) := (Nat.dvd_mod_iff hDG).2 hdvd
  obtain ⟨x, hx⟩ := hDR
  have hRlt := Nat.mod_lt K (Nat.two_pow_pos (16 - d))
  have hxlt : x < 2 ^ (L - d) := by
    rw [hx, hG] at hRlt
    exact Nat.lt_of_mul_lt_mul_left hRlt
  -- the slot's position relative to the block
  have hK : K = 2 ^ (16 - d) * P + 2 ^ (16 - L) * x := by omega
  have e1 : 2 ^ (16 - L) * x ≤ rev c j0 * 2 ^ (16 - d - c) := by
    rw [hK, Nat.mul_comm (2 ^ (16 - d)) P] at h1; omega
  have e2 : rev c j0 * 2 ^ (16 - d - c) < 2 ^ (16 - L) * (x + 1) := by
    rw [hK, Nat.mul_comm (2 ^ (16 - d)) P] at h2; rw [Nat.mul_add, Nat.mul_one]; omega
  rw [hDa] at e1 e2
  have f1 : 2 ^ (c - (L - d)) * x ≤ rev c j0 := by
    rw [Nat.mul_assoc, Nat.mul_comm (rev c j0)] at e1
    exact Nat.le_of_mul_le_mul_left e1 hB'
  have f2 : rev c j0 < 2 ^ (c - (L - d)) * (x + 1) := by
    rw [Nat.mul_assoc, Nat.mul_comm (rev c j0)] at e2
    exact Nat.lt_of_mul_lt_mul_left e2
  have f2' : rev c j0 < 2 ^ (c - (L - d)) * x + 2 ^ (c - (L - d)) := by rw [Nat.mul_add, Nat.mul_one] at f2; exact f2
  have hy : rev c j0 - 2 ^ (c - (L - d)) * x < 2 ^ (c - (L - d)) := by omega
  have hr : rev c j0 = (rev c j0 - 2 ^ (c - (L - d)) * x) + x * 2 ^ (c - (L - d)) := by
    rw [Nat.mul_comm x]; omega
  have hj : j0 = rev c (rev c j0) := by rw [rev_rev, Nat.mod_eq_of_lt hj0]
  have hc : c = (c - (L - d)) + (L - d) := by omega
  have key := rev_add_mul (c - (L - d)) (L - d) _ x hy
  rw [← hc, ← hr] at key
  have hj' : j0 = rev (c - (L - d)) (rev c j0 - 2 ^ (c - (L - d)) * x) * 2 ^ (L - d) + rev (L - d) x := by
    calc j0 = rev c (rev c j0) := hj
      _ = _ := key
  -- the reversed code
  have hK2 : K = (x + P * 2 ^ (L - d)) * 2 ^ (16 - L) := by
    rw [hK, hG]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm]; omega
  have hrev : rev 16 K = rev (L - d) x * 2 ^ d + rev d P := by
    have e := rev_mul_pow (16 - L) L (x + P * 2 ^ (L - d))
    rw [show 16 - L + L = 16 by omega] at e
    rw [hK2, e]
    have e2 := rev_add_mul (L - d) d x P hxlt
    rw [show L - d + d = L by omega] at e2
    exact e2
  have hdiv : rev 16 K / 2 ^ d = rev (L - d) x := by
    rw [hrev, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos d), Nat.div_eq_of_lt (rev_lt d P), Nat.add_zero]
  exact ⟨_, rev_lt _ _, by rw [hdiv, hj', Nat.add_comm]⟩

/-- A multiple of `D` below a multiple `M` of `D` leaves room for `D`. -/
theorem dvd_add_le {D K M : Nat} (hK : D ∣ K) (hM : D ∣ M) (hlt : K < M) : K + D ≤ M := by
  obtain ⟨k, rfl⟩ := hK
  obtain ⟨m, rfl⟩ := hM
  have : k < m := by
    apply Classical.byContradiction; intro h
    have := Nat.mul_le_mul_left D (show m ≤ k by omega); omega
  have := Nat.mul_le_mul_left D (show k + 1 ≤ m by omega)
  rw [Nat.mul_add, Nat.mul_one] at this; exact this

end ZlibNgF.Math.BitReverse
