/-!
# Length counts of a canonical code (`ZlibNgF`)

For a count function `c` (`c L` codes of length `L`, `1 ≤ L ≤ 15`): `nsum c m` is the number of codes of length at
most `m`, `wsum c m` their Kraft weight in units of `2 ^ -16` (a code of length `L` weighs `2 ^ (16 - L)`).
-/

set_option autoImplicit false

namespace ZlibNgF.Math.InftreesCount

/-- `f 0 + ... + f (n - 1)`. -/
noncomputable def ssum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ssum f n + f n

@[simp] theorem ssum_zero (f : Nat → Nat) : ssum f 0 = 0 := rfl

theorem ssum_succ (f : Nat → Nat) (n : Nat) : ssum f (n + 1) = ssum f n + f n := rfl

theorem ssum_congr {f g : Nat → Nat} {n : Nat} (e : ∀ i, i < n → f i = g i) : ssum f n = ssum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ssum_succ, ssum_succ, ih (fun i hi => e i (by omega)), e n (by omega)]

theorem ssum_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : ssum f m ≤ ssum f n := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    by_cases e : m = n + 1
    · subst e; exact Nat.le_refl _
    · rw [ssum_succ]; have := ih (by omega); omega

theorem ssum_le_of_le (f : Nat → Nat) (i n : Nat) (hi : i < n) : f i ≤ ssum f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [ssum_succ]
    by_cases e : i = n
    · subst e; omega
    · have := ih (by omega); omega

theorem ssum_eq_zero {f : Nat → Nat} {n : Nat} (h : ∀ i, i < n → f i = 0) : ssum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ssum_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Changing one term changes the sum by the same amount. -/
theorem ssum_update {f g : Nat → Nat} {k n : Nat} (hk : k < n) (e : ∀ i, i ≠ k → f i = g i) :
    ssum f n + g k = ssum g n + f k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [ssum_succ, ssum_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [ssum_congr (fun i hi => e i (by omega))]
      omega
    · have := ih (by omega)
      rw [e n (fun x => hkn x.symm)]
      omega

theorem ssum_sub_le (f : Nat → Nat) {m n : Nat} (h : m ≤ n) (i : Nat) (hm : m ≤ i) (hi : i < n) :
    ssum f m + f i ≤ ssum f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [ssum_succ]
    by_cases e : i = n
    · subst e; have := ssum_mono f (show m ≤ i from hm); omega
    · have := ih (by omega) (by omega); omega

theorem ssum_add (f g : Nat → Nat) (n : Nat) : ssum (fun i => f i + g i) n = ssum f n + ssum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ssum_succ, ssum_succ, ssum_succ, ih]; omega

/-- The number of codes of length `1 .. m`. -/
noncomputable def nsum (c : Nat → Nat) (m : Nat) : Nat := ssum (fun i => c (i + 1)) m

/-- The Kraft weight (units of `2 ^ -16`) of the codes of length `1 .. m`. -/
noncomputable def wsum (c : Nat → Nat) (m : Nat) : Nat := ssum (fun i => c (i + 1) * 2 ^ (15 - i)) m

@[simp] theorem nsum_zero (c : Nat → Nat) : nsum c 0 = 0 := rfl
@[simp] theorem wsum_zero (c : Nat → Nat) : wsum c 0 = 0 := rfl

theorem nsum_succ (c : Nat → Nat) (m : Nat) : nsum c (m + 1) = nsum c m + c (m + 1) := rfl

theorem wsum_succ (c : Nat → Nat) (m : Nat) : wsum c (m + 1) = wsum c m + c (m + 1) * 2 ^ (15 - m) := rfl

theorem nsum_congr {c d : Nat → Nat} {m : Nat} (e : ∀ L, 1 ≤ L → L ≤ m → c L = d L) : nsum c m = nsum d m :=
  ssum_congr (fun i hi => e (i + 1) (by omega) (by omega))

theorem wsum_congr {c d : Nat → Nat} {m : Nat} (e : ∀ L, 1 ≤ L → L ≤ m → c L = d L) : wsum c m = wsum d m :=
  ssum_congr (fun i hi => by rw [e (i + 1) (by omega) (by omega)])

theorem nsum_mono (c : Nat → Nat) {m n : Nat} (h : m ≤ n) : nsum c m ≤ nsum c n := ssum_mono _ h

theorem wsum_mono (c : Nat → Nat) {m n : Nat} (h : m ≤ n) : wsum c m ≤ wsum c n := ssum_mono _ h

theorem nsum_eq_zero {c : Nat → Nat} {m : Nat} (h : ∀ L, 1 ≤ L → L ≤ m → c L = 0) : nsum c m = 0 :=
  ssum_eq_zero (fun i hi => h (i + 1) (by omega) (by omega))

theorem wsum_eq_zero {c : Nat → Nat} {m : Nat} (h : ∀ L, 1 ≤ L → L ≤ m → c L = 0) : wsum c m = 0 :=
  ssum_eq_zero (fun i hi => by rw [h (i + 1) (by omega) (by omega)]; simp)

/-- One code of length `k` less: the counts drop by one, the weight by `2 ^ (16 - k)`. -/
theorem nsum_dec {c d : Nat → Nat} {k m : Nat} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hd : d k + 1 = c k)
    (e : ∀ L, L ≠ k → c L = d L) : nsum d m + 1 = nsum c m := by
  have := ssum_update (f := fun i => c (i + 1)) (g := fun i => d (i + 1)) (k := k - 1) (n := m) (by omega)
    (fun i hi => e (i + 1) (by omega))
  simp only [show k - 1 + 1 = k by omega] at this
  unfold nsum
  omega

theorem wsum_dec {c d : Nat → Nat} {k m : Nat} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hd : d k + 1 = c k)
    (e : ∀ L, L ≠ k → c L = d L) : wsum d m + 2 ^ (16 - k) = wsum c m := by
  have := ssum_update (f := fun i => c (i + 1) * 2 ^ (15 - i)) (g := fun i => d (i + 1) * 2 ^ (15 - i))
    (k := k - 1) (n := m) (by omega) (fun i hi => by rw [e (i + 1) (by omega)])
  simp only [show k - 1 + 1 = k by omega, show 15 - (k - 1) = 16 - k by omega] at this
  unfold wsum
  rw [← hd, Nat.add_mul, Nat.one_mul] at this
  omega

theorem nsum_le_of (c : Nat → Nat) {k m : Nat} (hk1 : 1 ≤ k) (hkm : k ≤ m) : c k ≤ nsum c m := by
  have := ssum_le_of_le (fun i => c (i + 1)) (k - 1) m (by omega)
  simp only [show k - 1 + 1 = k by omega] at this
  exact this

theorem wsum_le_of (c : Nat → Nat) {k m : Nat} (hk1 : 1 ≤ k) (hkm : k ≤ m) : c k * 2 ^ (16 - k) ≤ wsum c m := by
  have := ssum_le_of_le (fun i => c (i + 1) * 2 ^ (15 - i)) (k - 1) m (by omega)
  simp only [show k - 1 + 1 = k by omega, show 15 - (k - 1) = 16 - k by omega] at this
  exact this

/-- Every index below the number of codes falls in exactly one length class. -/
theorem class_exists (c : Nat → Nat) (m j : Nat) (hj : j < nsum c m) :
    ∃ L, 1 ≤ L ∧ L ≤ m ∧ nsum c (L - 1) ≤ j ∧ j < nsum c L := by
  induction m with
  | zero => simp at hj
  | succ m ih =>
    by_cases h : j < nsum c m
    · obtain ⟨L, h1, h2, h3, h4⟩ := ih h
      exact ⟨L, h1, by omega, h3, h4⟩
    · exact ⟨m + 1, by omega, by omega, by simp; omega, hj⟩

/-- Index classes are ordered: an index in class `L` and one in class `L'` with a smaller index have
`L' ≤ L`. -/
theorem class_le {c : Nat → Nat} {L L' j j' : Nat} (hL : 1 ≤ L) (h1 : nsum c (L - 1) ≤ j)
    (h2 : j' < nsum c L') (hjj : j ≤ j') : L ≤ L' := by
  apply Classical.byContradiction
  intro hc
  have := nsum_mono c (show L' ≤ L - 1 by omega)
  omega

/-- The weight of codes of lengths `1 .. m` is a multiple of `2 ^ (16 - m)`. -/
theorem wsum_dvd (c : Nat → Nat) (m : Nat) (hm : m ≤ 16) : 2 ^ (16 - m) ∣ wsum c m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [wsum_succ]
    apply Nat.dvd_add
    · exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (ih (by omega))
    · exact Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega)) _

theorem nsum_ind (v m : Nat) : nsum (fun L => if v = L then 1 else 0) m = if 1 ≤ v ∧ v ≤ m then 1 else 0 := by
  induction m with
  | zero => simp; omega
  | succ m ih =>
    rw [nsum_succ, ih]
    by_cases h1 : 1 ≤ v ∧ v ≤ m
    · simp only [h1, and_self, ite_true, show ¬ v = m + 1 by omega, ite_false, show v ≤ m + 1 by omega]
    · simp only [h1, ite_false]
      by_cases h2 : v = m + 1
      · simp only [h2, ite_true]; simp
      · simp only [h2, ite_false]; rw [ite_eq_right (by omega)]

end ZlibNgF.Math.InftreesCount
