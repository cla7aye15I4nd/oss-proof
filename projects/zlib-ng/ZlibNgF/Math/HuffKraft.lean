import ZlibNgF.Math.HuffModel

noncomputable section


/-!
# Clamped Kraft sum and overflow of a binary tree (heap-free)

For any tree with its root at depth 0 and a length limit `L` (Lemma 3 of the sibling project's overlay analysis,
re-proved on `HTree`): with `overflow` the number of nodes deeper than `L` (`overflowCount`),

* `kraft_overflow`: `2 * Σ_leaves 2^(L - min d L) = 2 * 2^L + overflow`, so `overflow` is even and the clamped
  Kraft sum (of `bl_count` after `gen_bitlen`'s first pass) is `2^L + overflow / 2`;
* `deep_leaves`: when `overflow ≠ 0`, at least `overflow / 2 + 1` leaves have depth `≥ L`
  (`bl_count[max_length] ≥ overflow / 2 + 1`);
* `overflow_zero`: no leaf deeper than `L` means no overflow.
-/

namespace ZlibNgF.Math.Huff
set_option autoImplicit false

/-- Clamped Kraft sum of `t` when its root is at depth `k`. -/
def krT (L k : Nat) (t : HTree) : Nat := (t.leaves.map fun x => 2 ^ (L - min (x.d + k) L)).sum

/-- Leaves of `t` at depth `≥ L` when its root is at depth `k`. -/
def deepT (L k : Nat) (t : HTree) : Nat := (t.leaves.filter fun x => decide (L ≤ x.d + k)).length

theorem krT_node (L k : Nat) (a b : HTree) : krT L k (.node a b) = krT L (k + 1) a + krT L (k + 1) b := by
  simp only [krT, HTree.leaves, List.map_map, List.map_append, List.sum_append]
  congr 2 <;> (congr 1; funext x; simp only [Function.comp]; rw [show x.d + 1 + k = x.d + (k + 1) by omega])

theorem deepT_node (L k : Nat) (a b : HTree) : deepT L k (.node a b) = deepT L (k + 1) a + deepT L (k + 1) b := by
  simp only [deepT, HTree.leaves, List.filter_map, List.length_map, List.filter_append, List.length_append]
  congr 3 <;> (funext x; simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 k])

theorem below_all (L : Nat) : ∀ (t : HTree) (k : Nat), L < k →
    ovfAux L k t + 1 = 2 * krT L k t ∧ deepT L k t = krT L k t
  | .leaf s w, k, h => by
    simp [ovfAux, krT, deepT, HTree.leaves, h, show L ≤ k by omega, show min k L = L by omega]
  | .node a b, k, h => by
    have ha := below_all L a (k + 1) (by omega)
    have hb := below_all L b (k + 1) (by omega)
    rw [krT_node, deepT_node]
    simp only [ovfAux, h, ite_true]
    omega

theorem kraft_aux (L : Nat) : ∀ (t : HTree) (k : Nat), k ≤ L →
    2 * krT L k t = 2 * 2 ^ (L - k) + ovfAux L k t ∧ ovfAux L k t ≤ 2 * deepT L k t ∧
      (ovfAux L k t = 0 ∨ ovfAux L k t + 2 ≤ 2 * deepT L k t)
  | .leaf s w, k, h => by
    simp only [ovfAux, krT, deepT, HTree.leaves, show ¬ L < k by omega, ite_false]
    simp [show min k L = k by omega]
  | .node a b, k, h => by
    rw [krT_node, deepT_node]
    simp only [ovfAux, show ¬ L < k by omega, ite_false, Nat.zero_add]
    by_cases hk : k = L
    · subst hk
      have ha := below_all k a (k + 1) (by omega)
      have hb := below_all k b (k + 1) (by omega)
      simp only [Nat.sub_self, Nat.pow_zero]
      omega
    · have ha := kraft_aux L a (k + 1) (by omega)
      have hb := kraft_aux L b (k + 1) (by omega)
      have hp : 2 ^ (L - k) = 2 * 2 ^ (L - (k + 1)) := by
        rw [show L - k = (L - (k + 1)) + 1 by omega, Nat.pow_succ]; omega
      omega

/-- **Clamped Kraft equality.** -/
theorem kraft_overflow (L : Nat) (T : HTree) :
    2 * (T.leaves.map fun x => 2 ^ (L - min x.d L)).sum = 2 * 2 ^ L + overflowCount L T := by
  have := (kraft_aux L T 0 (Nat.zero_le _)).1
  simpa [krT, overflowCount] using this

/-- `overflow` is even. -/
theorem overflow_even (L : Nat) (T : HTree) : overflowCount L T % 2 = 0 := by
  have := kraft_overflow L T; omega

/-- **Deep leaves.** With an overflow, at least `overflow / 2 + 1` leaves are at depth `≥ L`. -/
theorem deep_leaves (L : Nat) (T : HTree) (h : overflowCount L T ≠ 0) :
    overflowCount L T / 2 + 1 ≤ (T.leaves.filter fun x => decide (L ≤ x.d)).length := by
  have := (kraft_aux L T 0 (Nat.zero_le _)).2.2
  simp only [deepT, Nat.add_zero] at this
  unfold overflowCount at h ⊢
  omega

theorem ovfAux_zero (L : Nat) : ∀ (t : HTree) (k : Nat), (∀ x ∈ t.leaves, x.d + k ≤ L) → ovfAux L k t = 0
  | .leaf s w, k, h => by
    have := h ⟨s, w, 0⟩ (by simp [HTree.leaves])
    simp only [ovfAux]; split <;> omega
  | .node a b, k, h => by
    have ha : ∀ x ∈ a.leaves, x.d + (k + 1) ≤ L := fun x hx => by
      have := h ⟨x.sym, x.w, x.d + 1⟩ (by simp only [HTree.leaves, List.mem_map, List.mem_append]; exact ⟨x, Or.inl hx, rfl⟩)
      simp only at this; omega
    have hb : ∀ x ∈ b.leaves, x.d + (k + 1) ≤ L := fun x hx => by
      have := h ⟨x.sym, x.w, x.d + 1⟩ (by simp only [HTree.leaves, List.mem_map, List.mem_append]; exact ⟨x, Or.inr hx, rfl⟩)
      simp only at this; omega
    have hk : ¬ L < k := by
      cases a with
      | leaf s w => have := ha ⟨s, w, 0⟩ (by simp [HTree.leaves]); simp only at this; omega
      | node a1 a2 =>
        cases hl : (HTree.node a1 a2).leaves with
        | nil =>
          exfalso
          have : ∀ t : HTree, t.leaves ≠ [] := by
            intro t; induction t with
            | leaf => simp [HTree.leaves]
            | node p q ihp _ => simp [HTree.leaves, ihp]
          exact this _ hl
        | cons x xs => have := ha x (by rw [hl]; simp); omega
    simp only [ovfAux, hk, ite_false, ovfAux_zero L a (k + 1) ha, ovfAux_zero L b (k + 1) hb]

/-- No leaf deeper than `L`: no overflow. -/
theorem overflow_zero (L : Nat) (T : HTree) (h : ∀ x ∈ T.leaves, x.d ≤ L) : overflowCount L T = 0 :=
  ovfAux_zero L T 0 (fun x hx => by have := h x hx; omega)

end ZlibNgF.Math.Huff
