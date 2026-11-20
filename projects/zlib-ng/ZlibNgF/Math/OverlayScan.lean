import ZlibNgF.Math.OverlayHeader

noncomputable section

/-!
# The bit-length symbols of `scan_tree`, charged per entry by region (heap-free)

Re-proved for zlib-ng's `scan_tree` / `send_tree` loop (`scanTokens`) from the sibling project's region charging
(`trees.c.overlay-scan-region`). Every bit-length symbol `t` costs `wt t`; the entries of the scanned tree pay:

* a nonzero entry of length `x` at position `i`: `P x + A i` (`A i` is a credit for the run of zeros before it);
* a zero at position `i`: `B i`.

A group of `c` equal nonzero lengths costs at most `c · P x` (`count < min_count`: `c` copies; otherwise `x, 16`
with `c ≥ 4` when `x` differs from the previous length, or `16` with `c ≥ 3`). A run of `c` zeros costs at most
`A + c · B` with the credit `A` of the entry after it (or the credit `A m` after the last entry), and at most
`c · B` when it stops at 138 zeros. `A` and `B` stay constant along a run of zeros (`keep`).

`tree_region`: `Σ_{t ∈ treeTokens len m} wt t ≤ Σ_{i < m} charge i + A m`.

Also: every token is a length of the tree or one of 16, 17, 18 (`tokens_le`); a tree of `m` entries gives at most
`m` tokens (`tokens_length`); a token sum is a sum over the 19 bit-length symbols of their counts (`tokens_mass`).
-/

namespace ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

/-- The conditions on the charges for the bit-length symbol weights `wt`. -/
structure ScanCharges (wt P A B : Nat → Nat) : Prop where
  short : ∀ x, 1 ≤ x → x ≤ 15 → wt x ≤ P x
  rep : ∀ x, 1 ≤ x → x ≤ 15 → wt 16 ≤ 3 * P x
  zero1 : ∀ i, wt 0 ≤ A i + B i
  zero2 : ∀ i, 2 * wt 0 ≤ A i + 2 * B i
  zero3 : ∀ i, wt 17 ≤ A i + 3 * B i
  zero11 : ∀ i, wt 18 ≤ A i + 11 * B i
  full : ∀ i, wt 18 ≤ 138 * B i

/-- The cost of a list of bit-length symbols. -/
def tcost (wt : Nat → Nat) (l : List Nat) : Nat := (l.map wt).sum

theorem tcost_append (wt : Nat → Nat) (a b : List Nat) : tcost wt (a ++ b) = tcost wt a + tcost wt b := by
  simp [tcost]

theorem group_nonzero (wt P A B : Nat → Nat) (ch : ScanCharges wt P A B) (prev : Int) (c minc cur : Nat)
    (nz : cur ≠ 0) (le : cur ≤ 15) (one : 1 ≤ c)
    (shape : (minc = 3 ∧ prev = cur) ∨ (minc = 4 ∧ prev ≠ cur)) :
    tcost wt (groupTokens prev c minc cur) ≤ c * P cur := by
  have s := ch.short cur (by omega) le
  have r := ch.rep cur (by omega) le
  unfold groupTokens tcost
  by_cases few : c < minc
  · simp only [few, ite_true]
    rw [List.map_replicate, sum_rep]; exact Nat.mul_le_mul_left _ s
  · simp only [few, ite_false, ne_eq, nz, not_false_eq_true, ite_true]
    rcases shape with ⟨m3, pe⟩ | ⟨m4, pn⟩
    · have : ¬ ((cur : Int) ≠ prev) := by rw [pe]; simp
      simp only [ne_eq] at this
      simp only [this, ite_false, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have : 3 * P cur ≤ c * P cur := Nat.mul_le_mul_right _ (by omega)
      omega
    · have : ¬ ((cur : Int) = prev) := fun h => pn h.symm
      simp only [this, not_false_eq_true, ite_true, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil]
      have : 4 * P cur ≤ c * P cur := Nat.mul_le_mul_right _ (by omega)
      omega

theorem group_zero (wt P A B : Nat → Nat) (ch : ScanCharges wt P A B) (prev : Int) (c i : Nat) (one : 1 ≤ c) :
    tcost wt (groupTokens prev c 3 0) ≤ A i + c * B i ∧
      (138 ≤ c → tcost wt (groupTokens prev c 3 0) ≤ c * B i) := by
  have z1 := ch.zero1 i
  have z2 := ch.zero2 i
  have z3 := ch.zero3 i
  have z11 := ch.zero11 i
  have zf := ch.full i
  unfold groupTokens tcost
  by_cases few : c < 3
  · rw [ite_eq_left few, List.map_replicate, sum_rep]
    refine ⟨?_, fun h => by omega⟩
    rcases (show c = 1 ∨ c = 2 by omega) with e | e <;> subst e <;> omega
  · rw [ite_eq_right few]
    simp only [ne_eq, not_true_eq_false, ite_false]
    by_cases ten : c ≤ 10
    · simp only [ten, ite_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have : 3 * B i ≤ c * B i := Nat.mul_le_mul_right _ (by omega)
      exact ⟨by omega, fun h => by omega⟩
    · simp only [ten, ite_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have : 11 * B i ≤ c * B i := Nat.mul_le_mul_right _ (by omega)
      exact ⟨by omega, fun h => by have : 138 * B i ≤ c * B i := Nat.mul_le_mul_right _ h; omega⟩

/-- `g n + g (n + 1) + … + g (n + k - 1)`. -/
noncomputable def rsum (g : Nat → Nat) (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => g n + rsum g (n + 1) k

theorem rsum_mass (g : Nat → Nat) : ∀ k n, mass g n + rsum g n k = mass g (n + k)
  | 0, n => by simp [rsum]
  | k + 1, n => by
    have := rsum_mass g k (n + 1)
    show mass g n + (g n + rsum g (n + 1) k) = mass g (n + (k + 1))
    rw [show n + (k + 1) = n + 1 + k by omega, ← this]
    show _ = (mass g n + g n) + _
    omega

/-- The charge of a nonzero entry without its credit, or of a zero. -/
def chargeX (len P B : Nat → Nat) (i : Nat) : Nat := if len i = 0 then B i else P (len i)

/-- The credit of a nonzero entry. -/
def creditX (len A : Nat → Nat) (i : Nat) : Nat := if len i = 0 then 0 else A i

/-- The charge of entry `i`. -/
def regionCharge (len P A B : Nat → Nat) (i : Nat) : Nat := if len i = 0 then B i else P (len i) + A i

/-- **The scan from position `n`**, with `count` pending entries of length `cur = len n` before it. -/
theorem scan_region (len wt P A B : Nat → Nat) (ch : ScanCharges wt P A B) (m : Nat)
    (small : ∀ i, i < m → len i ≤ 15)
    (keep : ∀ i, i < m → len i = 0 → A (i + 1) = A i ∧ B (i + 1) = B i) :
    ∀ k n (prev : Int) (count maxc minc cur : Nat), n + k = m → 1 ≤ k → cur = len n → count < maxc →
      (cur = 0 → maxc = 138 ∧ minc = 3) →
      (cur ≠ 0 → (minc = 3 ∧ prev = cur) ∨ (minc = 4 ∧ prev ≠ cur)) →
      tcost wt (scanTokens len m k n prev count maxc minc cur) ≤
        count * chargeX len P B n + rsum (chargeX len P B) n k + rsum (creditX len A) (n + 1) (k - 1) + A m
  | 0, _, _, _, _, _, _, _, h, _, _, _, _ => absurd h (by omega)
  | k + 1, n, prev, count, maxc, minc, cur, hk, _, hc, hcm, hz, hnz => by
    have hn : n < m := by omega
    have curle : cur ≤ 15 := by rw [hc]; exact small n hn
    simp only [scanTokens]
    by_cases cont : count + 1 < maxc ∧ cur = nextLen len m n
    · rw [ite_eq_left cont]
      have k1 : 1 ≤ k := by
        refine Classical.byContradiction fun h => ?_
        have : nextLen len m n = 65535 := by simp [nextLen, show ¬ (n + 1 < m) by omega]
        omega
      have nx : nextLen len m n = len (n + 1) := by simp [nextLen, show n + 1 < m by omega]
      have ih := scan_region len wt P A B ch m small keep k (n + 1) prev (count + 1) maxc minc (nextLen len m n)
        (by omega) k1 nx cont.1 (fun h => hz (by omega)) (fun h => by rw [← cont.2]; exact hnz (by omega))
      have same : chargeX len P B (n + 1) = chargeX len P B n := by
        unfold chargeX
        rw [← nx, ← cont.2, ← hc]
        by_cases z : cur = 0
        · simp only [z, ite_true]; exact (keep n hn (by omega)).2
        · simp [z]
      have rk : rsum (creditX len A) (n + 1) k = creditX len A (n + 1) + rsum (creditX len A) (n + 1 + 1) (k - 1) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp [rsum]
      simp only [rsum, Nat.add_sub_cancel]
      rw [same] at ih
      rw [rk]
      simp only [Nat.add_mul, Nat.one_mul] at ih
      omega
    · rw [ite_eq_right cont, tcost_append]
      have cx : chargeX len P B n = if cur = 0 then B n else P cur := by simp [chargeX, hc]
      -- the group
      have groupB : ∀ (credit : Nat), (cur = 0 → nextLen len m n ≠ 0 → A n ≤ credit) →
          tcost wt (groupTokens prev (count + 1) minc cur) ≤ (count + 1) * chargeX len P B n + credit := by
        intro credit hcr
        by_cases z : cur = 0
        · obtain ⟨mx, mn⟩ := hz z
          subst mn
          rw [cx, ite_eq_left z, z]
          have g := group_zero wt P A B ch prev (count + 1) n (by omega)
          by_cases nz : nextLen len m n = 0
          · have full : 138 ≤ count + 1 := by
              refine Classical.byContradiction fun h => cont ⟨by omega, by omega⟩
            have := g.2 full; omega
          · have := hcr z nz; omega
        · rw [cx, ite_eq_right z]
          have := group_nonzero wt P A B ch prev (count + 1) minc cur z curle (by omega) (hnz z)
          omega
      by_cases k0 : k = 0
      · subst k0
        have rest : scanTokens len m 0 (n + 1) (cur : Int) 0
            (if nextLen len m n = 0 then 138 else if cur = nextLen len m n then 6 else 7)
            (if nextLen len m n = 0 then 3 else if cur = nextLen len m n then 3 else 4) (nextLen len m n) = [] := rfl
        rw [rest]
        have g := groupB (A m) (fun z _ => by
          have := (keep n hn (by omega)).1
          rw [show m = n + 1 by omega, this]; exact Nat.le_refl _)
        simp only [tcost, List.map_nil, List.sum_nil, rsum, Nat.zero_add, Nat.sub_self]
        simp only [tcost, Nat.add_mul, Nat.one_mul] at g
        omega
      · have nx : nextLen len m n = len (n + 1) := by simp [nextLen, show n + 1 < m by omega]
        generalize hnl : nextLen len m n = nl at *
        have ih := scan_region len wt P A B ch m small keep k (n + 1) (cur : Int) 0
          (if nl = 0 then 138 else if cur = nl then 6 else 7) (if nl = 0 then 3 else if cur = nl then 3 else 4) nl
          (by omega) (by omega) nx (by split <;> (try split) <;> omega) (fun h => by simp [h])
          (fun h => by
            simp only [h, ite_false]
            by_cases e : cur = nl
            · exact Or.inl ⟨by simp [e], by simp [e]⟩
            · exact Or.inr ⟨by simp [e], by intro h'; exact e (by exact_mod_cast h')⟩)
        have g := groupB (creditX len A (n + 1)) (fun z nz => by
          have := (keep n hn (by omega)).1
          simp only [creditX, ← nx, nz, ite_false]
          omega)
        have rk : rsum (creditX len A) (n + 1) k = creditX len A (n + 1) + rsum (creditX len A) (n + 1 + 1) (k - 1) := by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          simp [rsum]
        simp only [rsum, Nat.add_sub_cancel]
        rw [rk]
        simp only [Nat.zero_mul, Nat.zero_add] at ih
        simp only [Nat.add_mul, Nat.one_mul] at g
        omega

/-- **The cost of one tree's bit-length symbols, charged per entry by region.** -/
theorem tree_region (len wt P A B : Nat → Nat) (ch : ScanCharges wt P A B) (m : Nat)
    (small : ∀ i, i < m → len i ≤ 15)
    (keep : ∀ i, i < m → len i = 0 → A (i + 1) = A i ∧ B (i + 1) = B i) :
    tcost wt (treeTokens len m) ≤ mass (regionCharge len P A B) m + A m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [treeTokens, scanTokens, tcost]
  have s := scan_region len wt P A B ch m small keep m 0 (-1) 0 (if len 0 = 0 then 138 else 7)
    (if len 0 = 0 then 3 else 4) (len 0) (by omega) h rfl (by split <;> omega) (fun z => by simp [z])
    (fun nz => Or.inr ⟨by simp [nz], by omega⟩)
  have split : mass (regionCharge len P A B) m = rsum (chargeX len P B) 0 m + rsum (creditX len A) 0 m := by
    have e1 := rsum_mass (regionCharge len P A B) m 0
    have e2 := rsum_mass (chargeX len P B) m 0
    have e3 := rsum_mass (creditX len A) m 0
    have add : ∀ k n, rsum (regionCharge len P A B) n k = rsum (chargeX len P B) n k + rsum (creditX len A) n k := by
      intro k
      induction k with
      | zero => intro n; rfl
      | succ k ih =>
        intro n
        simp only [rsum, ih (n + 1), regionCharge, chargeX, creditX]
        split <;> omega
    simp only [mass, Nat.zero_add] at e1
    rw [← e1, add]
  have first : rsum (creditX len A) 1 (m - 1) ≤ rsum (creditX len A) 0 m := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp [rsum]
  unfold treeTokens
  simp only [Nat.zero_mul, Nat.zero_add] at s
  omega

/-! ## Token facts -/

theorem tokens_le (len : Nat → Nat) (m D : Nat) (hD : D ≤ 15) (hl : ∀ i, i < m → len i ≤ D) :
    ∀ k n (prev : Int) (count maxc minc cur : Nat), n + k = m → (1 ≤ k → cur ≤ D) →
      ∀ t ∈ scanTokens len m k n prev count maxc minc cur, t ≤ D ∨ (16 ≤ t ∧ t ≤ 18)
  | 0, _, _, _, _, _, _, _, _ => by simp [scanTokens]
  | k + 1, n, prev, count, maxc, minc, cur, hk, hc => by
    have nl : 1 ≤ k → nextLen len m n ≤ D := fun h => by
      simp only [nextLen, show n + 1 < m by omega, ite_true]; exact hl _ (by omega)
    intro t ht
    simp only [scanTokens] at ht
    split at ht
    · exact tokens_le len m D hD hl k (n + 1) prev (count + 1) maxc minc _ (by omega) nl t ht
    · rcases List.mem_append.mp ht with h | h
      · have cD := hc (by omega)
        unfold groupTokens at h
        split at h
        · exact Or.inl ((List.eq_of_mem_replicate h) ▸ cD)
        · split at h
          · simp only [List.mem_append, List.mem_singleton] at h
            rcases h with h | h
            · split at h
              · simp only [List.mem_singleton] at h; exact Or.inl (h ▸ cD)
              · simp at h
            · subst h; right; omega
          · split at h
            · simp only [List.mem_singleton] at h; subst h; right; omega
            · simp only [List.mem_singleton] at h; subst h; right; omega
      · exact tokens_le len m D hD hl k (n + 1) _ 0 _ _ _ (by omega) nl t h

theorem tokens_length (len : Nat → Nat) (m : Nat) :
    ∀ k n (prev : Int) (count maxc minc cur : Nat), 3 ≤ minc →
      (scanTokens len m k n prev count maxc minc cur).length ≤ count + k
  | 0, _, _, _, _, _, _, _ => by simp [scanTokens]
  | k + 1, n, prev, count, maxc, minc, cur, hm => by
    simp only [scanTokens]
    split
    · have := tokens_length len m k (n + 1) prev (count + 1) maxc minc (nextLen len m n) hm; omega
    · rw [List.length_append]
      have r := tokens_length len m k (n + 1) (cur : Int) 0
        (if nextLen len m n = 0 then 138 else if cur = nextLen len m n then 6 else 7)
        (if nextLen len m n = 0 then 3 else if cur = nextLen len m n then 3 else 4) (nextLen len m n)
        (by split <;> (try split) <;> omega)
      have g : (groupTokens prev (count + 1) minc cur).length ≤ count + 1 := by
        unfold groupTokens
        split
        · simp
        · split
          · split <;> simp <;> omega
          · split <;> simp
      omega

theorem treeTokens_length (len : Nat → Nat) (m : Nat) : (treeTokens len m).length ≤ m := by
  have := tokens_length len m m 0 (-1) 0 (if len 0 = 0 then 138 else 7) (if len 0 = 0 then 3 else 4) (len 0)
    (by split <;> omega)
  unfold treeTokens; omega

theorem treeTokens_le (len : Nat → Nat) (m D : Nat) (hD : D ≤ 15) (hl : ∀ i, i < m → len i ≤ D) :
    ∀ t ∈ treeTokens len m, t ≤ D ∨ (16 ≤ t ∧ t ≤ 18) :=
  tokens_le len m D hD hl m 0 (-1) 0 (if len 0 = 0 then 138 else 7) (if len 0 = 0 then 3 else 4) (len 0) (by omega) (fun h => hl 0 (by omega))

/-- A token sum is a sum over the symbols `0 .. 18` of their counts. -/
theorem tokens_mass (g : Nat → Nat) : ∀ (toks : List Nat), (∀ t ∈ toks, t < 19) →
    (toks.map g).sum = mass (fun k => toks.count k * g k) 19
  | [], _ => by simp only [List.map_nil, List.sum_nil, List.count_nil, Nat.zero_mul]; exact (mass_zero 19).symm
  | t :: l, h => by
    have ih := tokens_mass g l (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have ht := h t (List.mem_cons_self ..)
    have split : mass (fun k => (t :: l).count k * g k) 19 =
        mass (fun k => if k = t then g t else 0) 19 + mass (fun k => l.count k * g k) 19 := by
      rw [← mass_add]
      apply mass_congr
      intro k _
      rw [List.count_cons]
      by_cases e : k = t
      · subst e; simp [Nat.add_mul]; omega
      · simp [e, Ne.symm e]
    rw [split, mass_single_value, ite_eq_left ht]
    simp only [List.map_cons, List.sum_cons, ih]

end ZlibNgF.Math.Huff
