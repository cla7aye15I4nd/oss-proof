import ZlibNgF.Math.HuffMerge
import ZlibNgF.Math.HuffKraft
import ZlibNgF.Math.HuffSymbols

noncomputable section


/-!
# Facts about `buildTree` (heap-free)

The leaves of `buildTree elems freq` (`elems ≥ 3`): at least two, at most `elems`, distinct nodes, sorted
ascending by frequency, each a used symbol with its frequency or a forced node of frequency 1 whose own
frequency is 0; every used symbol is a leaf. The tree `root` is a Huffman merge of these leaves
(`built_merges`), its leaves are exactly them (`built_pairs`), and its weight is their total (`built_weight`).
-/

namespace ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

/-- A leaf entry of `build_tree`: a used symbol with its frequency, or a forced node (frequency 1, own frequency
0). -/
def LeafOK (elems : Nat) (freq : Nat → Nat) (e : Nat × Nat) : Prop :=
  e.2 < elems ∧ 1 ≤ e.1 ∧ ((e.1 = freq e.2 ∧ freq e.2 ≠ 0) ∨ (e.1 = 1 ∧ freq e.2 = 0))

theorem perm_sum {l₁ l₂ : List Nat} (p : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Scan -/

theorem scan_mem {freq : Nat → Nat} : ∀ {n : Nat} {e : Nat × Nat}, e ∈ scanLeaves freq n →
    e.2 < n ∧ e.1 = freq e.2 ∧ freq e.2 ≠ 0
  | 0, e, h => by simp [scanLeaves] at h
  | n + 1, e, h => by
    simp only [scanLeaves, List.mem_append] at h
    rcases h with h | h
    · have := scan_mem h; exact ⟨by omega, this.2⟩
    · split at h
      · simp only [List.mem_singleton] at h; subst h; exact ⟨by simp, rfl, by assumption⟩
      · simp at h

theorem scan_complete {freq : Nat → Nat} : ∀ {n v : Nat}, v < n → freq v ≠ 0 → (freq v, v) ∈ scanLeaves freq n
  | 0, v, h, _ => by omega
  | n + 1, v, h, hv => by
    simp only [scanLeaves, List.mem_append]
    by_cases e : v = n
    · subst e; right; simp [hv]
    · left; exact scan_complete (by omega) hv

theorem scan_nodup (freq : Nat → Nat) : ∀ n, ((scanLeaves freq n).map Prod.snd).Nodup
  | 0 => by simp [scanLeaves]
  | n + 1 => by
    simp only [scanLeaves, List.map_append]
    rw [List.nodup_append]
    refine ⟨scan_nodup freq n, by split <;> simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha
    obtain ⟨e, he, rfl⟩ := ha
    have := (scan_mem he).1
    split at hb
    · simp at hb; omega
    · simp at hb

theorem scan_length (freq : Nat → Nat) : ∀ n, (scanLeaves freq n).length ≤ n
  | 0 => by simp [scanLeaves]
  | n + 1 => by
    have := scan_length freq n
    simp only [scanLeaves, List.length_append]; split <;> simp <;> omega

theorem scan_sum (freq : Nat → Nat) : ∀ n, ((scanLeaves freq n).map Prod.fst).sum = mass freq n
  | 0 => by simp [scanLeaves, mass]
  | n + 1 => by
    have := scan_sum freq n
    simp only [scanLeaves, List.map_append, List.sum_append, mass]
    split <;> simp_all

theorem maxCode1_above (freq : Nat → Nat) : ∀ n v, maxCode1 freq n ≤ v → v < n → freq v = 0
  | 0, v, _, h => by omega
  | n + 1, v, h1, h2 => by
    simp only [maxCode1] at h1
    split at h1
    · omega
    · by_cases e : v = n
      · subst e; simp_all
      · exact maxCode1_above freq n v h1 (by omega)

theorem maxCode1_le (freq : Nat → Nat) : ∀ n, maxCode1 freq n ≤ n
  | 0 => Nat.le_refl _
  | n + 1 => by have := maxCode1_le freq n; simp only [maxCode1]; split <;> omega

theorem maxCode1_mem (freq : Nat → Nat) : ∀ n, maxCode1 freq n ≠ 0 →
    ∃ e ∈ scanLeaves freq n, e.2 + 1 = maxCode1 freq n
  | 0, h => by simp [maxCode1] at h
  | n + 1, h => by
    simp only [maxCode1] at h ⊢
    by_cases hn : freq n = 0
    · simp only [hn, ne_eq, not_true_eq_false, ite_false] at h ⊢
      obtain ⟨e, he, h2⟩ := maxCode1_mem freq n h
      exact ⟨e, by simp [scanLeaves, he], h2⟩
    · simp only [hn, ne_eq, not_false_eq_true, ite_true]
      exact ⟨(freq n, n), by simp [scanLeaves, hn], rfl⟩

theorem maxCode1_ge (freq : Nat → Nat) : ∀ n, ∀ e ∈ scanLeaves freq n, e.2 + 1 ≤ maxCode1 freq n
  | 0, e, h => by simp [scanLeaves] at h
  | n + 1, e, h => by
    have hm := scan_mem h
    simp only [scanLeaves, List.mem_append] at h
    simp only [maxCode1]
    by_cases hn : freq n = 0
    · simp only [hn, ne_eq, not_true_eq_false, ite_false] at h ⊢
      rcases h with h | h
      · exact maxCode1_ge freq n e h
      · simp at h
    · simp only [hn, ne_eq, not_false_eq_true, ite_true]; omega

/-! ## Forcing -/

theorem forced_ok {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems) :
    let f := forced (scanLeaves freq elems) (maxCode1 freq elems)
    (∀ e ∈ f.1, LeafOK elems freq e) ∧ (f.1.map Prod.snd).Nodup ∧ 2 ≤ f.1.length ∧ f.1.length ≤ elems ∧
      (∀ v, v < elems → freq v ≠ 0 → (freq v, v) ∈ f.1) ∧ (f.1.map Prod.fst).sum ≤ mass freq elems + 2 := by
  intro f
  have scanOK : ∀ e ∈ scanLeaves freq elems, LeafOK elems freq e := fun e he => by
    have := scan_mem he; exact ⟨this.1, by omega, Or.inl this.2⟩
  have nd := scan_nodup freq elems
  have len := scan_length freq elems
  have sum := scan_sum freq elems
  have above := maxCode1_above freq elems
  have mem := maxCode1_mem freq elems
  have ge := maxCode1_ge freq elems
  have comp : ∀ v, v < elems → freq v ≠ 0 → (freq v, v) ∈ scanLeaves freq elems :=
    fun v h hv => scan_complete h hv
  have mcle := maxCode1_le freq elems
  simp only [f]
  generalize scanLeaves freq elems = s at *
  generalize maxCode1 freq elems = mc1 at *
  match s with
  | [] =>
    have z : ∀ v, v < elems → freq v = 0 := fun v hv => Classical.byContradiction fun h => by
      simpa using comp v hv h
    have hz : mc1 = 0 := Classical.byContradiction fun h => by
      obtain ⟨e, he, _⟩ := mem h; simp at he
    subst hz
    simp only [forced, forceNode, forceNext]
    refine ⟨?_, by simp, by simp, by simp <;> omega, ?_, by simp <;> omega⟩
    · intro e he
      simp at he
      rcases he with rfl | rfl <;> exact ⟨by simp <;> omega, by simp, Or.inr ⟨rfl, z _ (by simp <;> omega)⟩⟩
    · intro v hv hv'; exact absurd (z v hv) hv'
  | [l] =>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at sum
    have hl := scanOK l (by simp)
    have hmc : l.2 + 1 = mc1 := by
      have h1 := ge l (by simp)
      obtain ⟨e, he, h2⟩ := mem (by omega)
      simp at he; subst he; exact h2
    have only : ∀ v, v < elems → v ≠ l.2 → freq v = 0 := fun v hv hne => Classical.byContradiction fun h => by
      have := comp v hv h; simp at this; exact hne (by simp [← this])
    simp only [forced, forceNode, forceNext]
    by_cases h3 : mc1 < 3
    · simp only [h3, ite_true]
      refine ⟨?_, ?_, by simp, by simp <;> omega, ?_, ?_⟩
      · intro e he
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl
        · exact hl
        · exact ⟨by simp <;> omega, by simp, Or.inr ⟨rfl, above _ (by simp) (by simp <;> omega)⟩⟩
      · simp; omega
      · intro v hv hv'; have := comp v hv hv'; simp at this; simp [this]
      · simp; omega
    · simp only [h3, ite_false]
      refine ⟨?_, ?_, by simp, by simp <;> omega, ?_, ?_⟩
      · intro e he
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl
        · exact hl
        · exact ⟨by simp <;> omega, by simp, Or.inr ⟨rfl, only 0 (by omega) (by omega)⟩⟩
      · simp; omega
      · intro v hv hv'; have := comp v hv hv'; simp at this; simp [this]
      · simp; omega
  | a :: b :: rest =>
    simp only [forced]
    exact ⟨scanOK, nd, by simp, len, comp, by omega⟩

/-! ## Sort -/

theorem insKey_perm (e : Nat × Nat) : ∀ l, (insKey e l).Perm (e :: l)
  | [] => by simp [insKey]
  | x :: xs => by
    simp only [insKey]; split
    · exact List.Perm.refl _
    · exact ((insKey_perm e xs).cons x).trans (List.Perm.swap e x xs)

theorem sortKeys_perm : ∀ l, (sortKeys l).Perm l
  | [] => by simp [sortKeys]
  | x :: xs => by
    simp only [sortKeys]
    exact (insKey_perm x _).trans ((sortKeys_perm xs).cons x)

theorem insKey_sorted (e : Nat × Nat) : ∀ l, l.Pairwise (fun a b => a.1 ≤ b.1) →
    (insKey e l).Pairwise (fun a b => a.1 ≤ b.1)
  | [], _ => by simp [insKey]
  | x :: xs, h => by
    have h' := List.pairwise_cons.mp h
    simp only [insKey]; split
    · rename_i k
      have ex : e.1 ≤ x.1 := by
        simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at k; omega
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ex
      · exact Nat.le_trans ex (h'.1 y hy)
    · rename_i k
      have xe : x.1 ≤ e.1 := by
        simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at k; omega
      refine List.pairwise_cons.mpr ⟨?_, insKey_sorted e xs h'.2⟩
      intro y hy
      have := (insKey_perm e xs).mem_iff.mp hy
      simp only [List.mem_cons] at this
      rcases this with rfl | hy
      · exact xe
      · exact h'.1 y hy

theorem sortKeys_sorted : ∀ l, (sortKeys l).Pairwise (fun a b => a.1 ≤ b.1)
  | [] => by simp [sortKeys]
  | x :: xs => insKey_sorted x _ (sortKeys_sorted xs)

/-! ## Leaves of a merge -/

/-- The `(symbol, weight)` pairs of a tree's leaves. -/
def leafPairs (t : HTree) : List (Nat × Nat) := t.leaves.map fun x => (x.sym, x.w)

theorem leafPairs_node (a b : HTree) : leafPairs (.node a b) = leafPairs a ++ leafPairs b := by
  simp only [leafPairs, HTree.leaves, List.map_map, List.map_append]; rfl

theorem Merges.pairs {s tr : List HTree} {T : HTree} (h : Merges s tr T) :
    (s.flatMap leafPairs).Perm (leafPairs T) := by
  induction h with
  | done t => simp
  | step hst _ ih =>
    obtain ⟨r, hp, _, _, rfl⟩ := hst
    refine (List.Perm.flatMap_right leafPairs hp).trans ?_
    refine List.Perm.trans ?_ ih
    simp [leafPairs_node, List.append_assoc]

theorem weight_eq_sum : ∀ t : HTree, t.weight = (t.leaves.map (·.w)).sum
  | .leaf s w => by simp [HTree.weight, HTree.leaves]
  | .node a b => by
    simp only [HTree.weight, HTree.leaves, List.map_map, List.map_append, List.sum_append]
    rw [weight_eq_sum a, weight_eq_sum b]
    rfl

/-! ## The built tree -/

theorem built_facts {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems) :
    let b := buildTree elems freq
    (∀ e ∈ b.sorted, LeafOK elems freq e) ∧ (b.sorted.map Prod.snd).Nodup ∧ 2 ≤ b.sorted.length ∧
      b.sorted.length ≤ elems ∧ (∀ v, v < elems → freq v ≠ 0 → (freq v, v) ∈ b.sorted) ∧
      (b.sorted.map Prod.fst).sum ≤ mass freq elems + 2 ∧ b.sorted.Pairwise (fun a b => a.1 ≤ b.1) ∧
      ∃ tr, Merges (initForest (b.sorted.map fun e => (e.2, e.1))) tr b.root := by
  intro b
  obtain ⟨ok, nd, two, le, comp, sum⟩ := forced_ok (freq := freq) hE
  have p := sortKeys_perm (forced (scanLeaves freq elems) (maxCode1 freq elems)).1
  have hs : b.sorted = sortKeys (forced (scanLeaves freq elems) (maxCode1 freq elems)).1 := rfl
  have hr : b.root = ((mergeLoop (b.sorted.length - 1) b.sorted [] elems).headD ⟨0, 0, .leaf 0 0⟩).tree := rfl
  rw [← hs] at p
  have ok' : ∀ e ∈ b.sorted, LeafOK elems freq e := fun e he => ok e (p.mem_iff.mp he)
  have len := p.length_eq
  refine ⟨ok', (p.map Prod.snd).nodup_iff.mpr nd, by omega, by omega,
    fun v hv hv' => p.mem_iff.mpr (comp v hv hv'), by rw [perm_sum (p.map Prod.fst)]; exact sum,
    by rw [hs]; exact sortKeys_sorted _, ?_⟩
  have inv : MInv 0 b.sorted [] :=
    ⟨by rw [hs]; exact sortKeys_sorted _, by simp, fun e _ => Nat.zero_le _, by simp, by simp, by simp,
      fun e he => (ok' e he).2.1, by simp⟩
  obtain ⟨q, tr, run, merges, _⟩ := mergeLoop_merges (b.sorted.length - 1) 0 b.sorted [] elems inv
    (by simp; omega) (Or.inl (by omega))
  refine ⟨tr, ?_⟩
  rw [hr, run]
  simp only [forestOf, List.map_nil, List.append_nil] at merges
  simp only [initForest, List.map_map]
  exact merges

end ZlibNgF.Math.Huff
