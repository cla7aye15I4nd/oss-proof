import ZlibNgF.Math.HuffClasses

noncomputable section

/-!
# Huffman optimality against any Kraft-feasible code (heap-free)

For a run of merges (`Merges`, each step merges two roots of least weight) from an initial forest of leaves with
distinct symbols to a tree `T`, the cost of `T` (`ext T = Σ_leaves w · depth`) is at most the cost `Σ w · ℓ` of the
leaves under every code `ℓ` with `ℓ ≤ K` and `Σ 2^(K - ℓ) ≤ 2^K` (`huffman_opt`).

The proof is the exchange argument, by induction over the merges on forests with a length per tree: the lightest
root `n` takes the longest length (swap), the second lightest `m` the longest length among the other roots (swap),
and the merged node `node n m` takes that length minus one. Kraft stays feasible because every other length is at
most `ℓ m`, so every other Kraft term is a multiple of `2^(K - ℓ m)`; the cost drops by at least the merged weight,
which is exactly what `ext (node n m)` adds.
-/

namespace ZlibNgF.Math.Huff
open Classical
set_option autoImplicit false

/-- The cost of a tree: `Σ_leaves w · depth`. -/
def ext (t : HTree) : Nat := (t.leaves.map fun x => x.w * x.d).sum

theorem sum_map_add {α : Type} (f g : α → Nat) : ∀ l : List α,
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add f g l]; omega

theorem ext_node (a b : HTree) : ext (.node a b) = ext a + ext b + a.weight + b.weight := by
  have hw := weight_eq_sum a
  have hw' := weight_eq_sum b
  simp only [ext, HTree.leaves, List.map_map, List.map_append, List.sum_append]
  have e : ∀ l : List LeafInfo, (l.map ((fun x : LeafInfo => x.w * x.d) ∘ fun x => { x with d := x.d + 1 })).sum =
      (l.map fun x => x.w * x.d).sum + (l.map (·.w)).sum := by
    intro l
    rw [← sum_map_add]
    congr 1
  rw [e, e]
  omega

/-- Swap the lengths of `x` and `y`. -/
def swapL (ℓ : HTree → Nat) (x y : HTree) : HTree → Nat :=
  fun t => if t = x then ℓ y else if t = y then ℓ x else ℓ t

theorem swap_sum (G : HTree → Nat → Nat) (ℓ : HTree → Nat) {s : List HTree} (nd : s.Nodup) {x y : HTree}
    (hx : x ∈ s) (hy : y ∈ s) :
    (s.map fun t => G t (swapL ℓ x y t)).sum + G x (ℓ x) + G y (ℓ y) =
      (s.map fun t => G t (ℓ t)).sum + G x (ℓ y) + G y (ℓ x) := by
  by_cases e : x = y
  · subst e
    have : (s.map fun t => G t (swapL ℓ x x t)) = (s.map fun t => G t (ℓ t)) := by
      apply List.map_congr_left; intro t _; unfold swapL; by_cases h : t = x <;> simp [h]
    rw [this]
  · have p1 := List.perm_cons_erase hx
    have hy' : y ∈ s.erase x := (List.mem_erase_of_ne (Ne.symm e)).mpr hy
    have p2 := List.perm_cons_erase hy'
    have p := p1.trans (List.Perm.cons x p2)
    have ndr : (x :: y :: (s.erase x).erase y).Nodup := p.nodup_iff.mp nd
    have nx : x ∉ (s.erase x).erase y := by
      intro h; simp only [List.nodup_cons, List.mem_cons, not_or] at ndr; exact ndr.1.2 h
    have ny : y ∉ (s.erase x).erase y := by
      intro h; simp only [List.nodup_cons] at ndr; exact ndr.2.1 h
    have q : ∀ g : HTree → Nat, (s.map g).sum = g x + g y + (((s.erase x).erase y).map g).sum := by
      intro g
      rw [perm_sum (p.map g)]
      simp only [List.map_cons, List.sum_cons]; omega
    rw [q, q]
    have rest : (((s.erase x).erase y).map fun t => G t (swapL ℓ x y t)) =
        (((s.erase x).erase y).map fun t => G t (ℓ t)) := by
      apply List.map_congr_left
      intro t ht
      have h1 : t ≠ x := fun h => nx (h ▸ ht)
      have h2 : t ≠ y := fun h => ny (h ▸ ht)
      simp [swapL, h1, h2]
    rw [rest]
    simp only [swapL, ite_true, e, ite_false, show y ≠ x from Ne.symm e]
    omega

theorem exists_max (ℓ : HTree → Nat) : ∀ (s : List HTree), s ≠ [] → ∃ a ∈ s, ∀ t ∈ s, ℓ t ≤ ℓ a
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨c, hc, hmax⟩ := exists_max ℓ (b :: l) (by simp)
    by_cases h : ℓ a ≤ ℓ c
    · exact ⟨c, List.mem_cons_of_mem _ hc, fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · exact h
        · exact hmax t ht⟩
    · exact ⟨a, List.mem_cons_self .., fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Nat.le_refl _
        · have := hmax t ht; omega⟩

theorem exch {wa wb la lb : Nat} (hw : wa ≤ wb) (hl : la ≤ lb) : wa * lb + wb * la ≤ wa * la + wb * lb := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hw
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hl
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem leafPairs_ne (t : HTree) : leafPairs t ≠ [] := by
  induction t with
  | leaf => simp [leafPairs, HTree.leaves]
  | node a b iha _ =>
    rw [leafPairs_node]; intro h; exact iha (List.append_eq_nil_iff.mp h).1

theorem nodup_of_flat : ∀ (s : List HTree), ((s.flatMap leafPairs).map Prod.fst).Nodup → s.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [List.flatMap_cons, List.map_append] at h
    have h' := List.nodup_append.mp h
    refine List.nodup_cons.mpr ⟨fun ha => ?_, nodup_of_flat l h'.2.1⟩
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (leafPairs_ne a)
    have m1 : p.1 ∈ (leafPairs a).map Prod.fst := List.mem_map_of_mem hp
    have m2 : p.1 ∈ (l.flatMap leafPairs).map Prod.fst :=
      List.mem_map_of_mem (List.mem_flatMap.mpr ⟨a, ha, hp⟩)
    exact h'.2.2 _ m1 _ m2 rfl

theorem dvd_sum_pow (K D : Nat) (ℓ : HTree → Nat) : ∀ (r : List HTree), (∀ t ∈ r, ℓ t ≤ D) →
    2 ^ (K - D) ∣ (r.map fun t => 2 ^ (K - ℓ t)).sum
  | [], _ => by simp
  | t :: r, h => by
    simp only [List.map_cons, List.sum_cons]
    refine Nat.dvd_add ?_ (dvd_sum_pow K D ℓ r fun u hu => h u (List.mem_cons_of_mem _ hu))
    exact Nat.pow_dvd_pow 2 (by have := h t (List.mem_cons_self ..); omega)

theorem add_le_of_dvd {D X Y : Nat} (hX : D ∣ X) (hY : D ∣ Y) (lt : X < Y) : X + D ≤ Y := by
  have h := Nat.dvd_sub hY hX
  have pos : 0 < Y - X := by omega
  have := Nat.le_of_dvd pos h
  omega

/-- **Optimality over a run of merges**, for every length per root. -/
theorem opt_merges {s tr : List HTree} {T : HTree} (h : Merges s tr T) :
    ((s.flatMap leafPairs).map Prod.fst).Nodup → ∀ (K : Nat) (ℓ : HTree → Nat), (∀ t ∈ s, ℓ t ≤ K) →
      (s.map fun t => 2 ^ (K - ℓ t)).sum ≤ 2 ^ K →
      ext T ≤ (s.map fun t => t.weight * ℓ t + ext t).sum := by
  induction h with
  | done t =>
    intro _ K ℓ _ _
    simp
  | @step s s' n m tr T hst _ ih =>
    intro nd K ℓ hK kraft
    obtain ⟨r, hp, hn, hm, rfl⟩ := hst
    have ndS := nodup_of_flat s nd
    have ndP : (n :: m :: r).Nodup := hp.nodup_iff.mp ndS
    simp only [List.nodup_cons, List.mem_cons, not_or] at ndP
    obtain ⟨⟨nm, nr⟩, mr, ndr⟩ := ndP
    have memN : n ∈ s := hp.mem_iff.mpr (List.mem_cons_self ..)
    have memM : m ∈ s := hp.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have split : ∀ g : HTree → Nat, (s.map g).sum = g n + g m + (r.map g).sum := by
      intro g; rw [perm_sum (hp.map g)]; simp only [List.map_cons, List.sum_cons]; omega
    -- the longest length goes to `n`
    obtain ⟨a, ha, amax⟩ := exists_max ℓ s (List.ne_nil_of_mem memN)
    obtain ⟨ℓ1, hℓ1⟩ : ∃ f, f = swapL ℓ n a := ⟨_, rfl⟩
    have c1 := swap_sum (fun t l => t.weight * l + ext t) ℓ ndS memN ha
    have k1 := swap_sum (fun t l => 2 ^ (K - l)) ℓ ndS memN ha
    have wna : n.weight ≤ a.weight := by
      by_cases e : a = n
      · rw [e]; exact Nat.le_refl _
      · have : a ∈ m :: r := by
          have := hp.mem_iff.mp ha
          rcases List.mem_cons.mp this with h | h
          · exact absurd h e
          · exact h
        exact hn a this
    have ex1 := exch wna (amax n memN)
    rw [← hℓ1] at c1 k1
    have ℓ1n : ℓ1 n = ℓ a := by simp [hℓ1, swapL]
    have ℓ1le : ∀ t ∈ s, ℓ1 t ≤ ℓ a := by
      intro t ht; rw [hℓ1]; simp only [swapL]; split
      · exact Nat.le_refl _
      · split
        · exact amax n memN
        · exact amax t ht
    -- the longest of the others goes to `m`
    have memMr : m ∈ m :: r := List.mem_cons_self ..
    obtain ⟨b, hb, bmax⟩ := exists_max ℓ1 (m :: r) (List.ne_nil_of_mem memMr)
    have bs : b ∈ s := hp.mem_iff.mpr (List.mem_cons_of_mem _ hb)
    have bn : b ≠ n := by
      intro e; subst e
      rcases List.mem_cons.mp hb with h | h
      · exact nm h
      · exact nr h
    obtain ⟨ℓ2, hℓ2⟩ : ∃ f, f = swapL ℓ1 m b := ⟨_, rfl⟩
    have c2 := swap_sum (fun t l => t.weight * l + ext t) ℓ1 ndS memM bs
    have k2 := swap_sum (fun t l => 2 ^ (K - l)) ℓ1 ndS memM bs
    have wmb : m.weight ≤ b.weight := by
      rcases List.mem_cons.mp hb with h | h
      · rw [h]; exact Nat.le_refl _
      · exact hm b h
    have ex2 := exch wmb (bmax m memMr)
    rw [← hℓ2] at c2 k2
    have ℓ2n : ℓ2 n = ℓ a := by rw [hℓ2]; simp [swapL, nm, bn.symm, ℓ1n]
    have ℓ2m : ℓ2 m = ℓ1 b := by simp [hℓ2, swapL]
    have ℓ2r : ∀ t ∈ r, ℓ2 t ≤ ℓ1 b := by
      intro t ht; rw [hℓ2]; simp only [swapL]; split
      · exact Nat.le_refl _
      · split
        · exact bmax m memMr
        · exact bmax t (List.mem_cons_of_mem _ ht)
    have ℓ2K : ∀ t ∈ s, ℓ2 t ≤ K := by
      intro t ht
      have := hK a ha
      rw [hℓ2]; simp only [swapL]; split
      · have := ℓ1le b bs; omega
      · split
        · have := ℓ1le m memM; omega
        · have := ℓ1le t ht; omega
    have L2le : ℓ1 b ≤ ℓ a := ℓ1le b bs
    -- Kraft and cost of `ℓ2` over `s`
    have kraft2 : (s.map fun t => 2 ^ (K - ℓ2 t)).sum ≤ 2 ^ K := by
      have : (s.map fun t => 2 ^ (K - ℓ2 t)).sum = (s.map fun t => 2 ^ (K - ℓ t)).sum := by omega
      omega
    have cost2 : (s.map fun t => t.weight * ℓ2 t + ext t).sum ≤ (s.map fun t => t.weight * ℓ t + ext t).sum := by
      omega
    rw [split] at kraft2 cost2
    rw [ℓ2n, ℓ2m] at kraft2 cost2
    -- the merged node
    have L2pos : 1 ≤ ℓ1 b := by
      refine Classical.byContradiction fun h0 => ?_
      have : ℓ1 b = 0 := by omega
      rw [this] at kraft2
      have := Nat.one_le_two_pow (n := K - ℓ a)
      simp at kraft2; omega
    let ℓ' : HTree → Nat := fun t => if t = .node n m then ℓ1 b - 1 else ℓ2 t
    have nd' : (((HTree.node n m :: r).flatMap leafPairs).map Prod.fst).Nodup := by
      refine (List.Perm.map Prod.fst ?_).nodup_iff.mp nd
      refine (List.Perm.flatMap_right leafPairs hp).trans ?_
      simp [leafPairs_node, List.append_assoc]
    have ndS' := nodup_of_flat _ nd'
    have nodeR : HTree.node n m ∉ r := (List.nodup_cons.mp ndS').1
    have onR : ∀ t ∈ r, ℓ' t = ℓ2 t := by
      intro t ht
      have : t ≠ .node n m := fun e => nodeR (e ▸ ht)
      simp [ℓ', this]
    have mapR : ∀ g : HTree → Nat → Nat, (r.map fun t => g t (ℓ' t)) = (r.map fun t => g t (ℓ2 t)) := by
      intro g; apply List.map_congr_left; intro t ht; rw [onR t ht]
    have ℓ'node : ℓ' (.node n m) = ℓ1 b - 1 := by simp [ℓ']
    have dv := dvd_sum_pow K (ℓ1 b) ℓ2 r ℓ2r
    have bK : ℓ1 b ≤ K := by have := ℓ2K m memM; rw [ℓ2m] at this; exact this
    have dK : 2 ^ (K - ℓ1 b) ∣ 2 ^ K := Nat.pow_dvd_pow 2 (Nat.sub_le _ _)
    have dX : 2 ^ (K - ℓ1 b) ∣ (r.map fun t => 2 ^ (K - ℓ2 t)).sum + 2 ^ (K - ℓ1 b) :=
      Nat.dvd_add dv (Nat.dvd_refl _)
    have pa := Nat.one_le_two_pow (n := K - ℓ a)
    have fit := add_le_of_dvd dX dK (by omega)
    have two : 2 ^ (K - (ℓ1 b - 1)) = 2 * 2 ^ (K - ℓ1 b) := by
      rw [show K - (ℓ1 b - 1) = (K - ℓ1 b) + 1 by omega, Nat.pow_succ]; omega
    have hK' : ∀ t ∈ HTree.node n m :: r, ℓ' t ≤ K := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rw [ℓ'node]; omega
      · rw [onR t ht]; exact ℓ2K t (hp.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))
    have kraft' : ((HTree.node n m :: r).map fun t => 2 ^ (K - ℓ' t)).sum ≤ 2 ^ K := by
      simp only [List.map_cons, List.sum_cons]
      rw [ℓ'node, two, mapR (fun _ l => 2 ^ (K - l))]
      omega
    have step := ih nd' K ℓ' hK' kraft'
    simp only [List.map_cons, List.sum_cons] at step
    rw [ℓ'node, mapR (fun t l => t.weight * l + ext t), ext_node, HTree.weight] at step
    obtain ⟨L2, hL2⟩ : ∃ L2, ℓ1 b = L2 + 1 := ⟨ℓ1 b - 1, by omega⟩
    rw [hL2, Nat.add_sub_cancel] at step
    rw [hL2] at cost2 L2le
    have mono : n.weight * (L2 + 1) ≤ n.weight * ℓ a := Nat.mul_le_mul_left _ L2le
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at step cost2 mono
    omega

/-- **Huffman optimality**: the merged tree of leaves with distinct symbols costs at most any code of Kraft sum at
most one. -/
theorem huffman_opt (syms : List (Nat × Nat)) {tr : List HTree} {T : HTree} (h : Merges (initForest syms) tr T)
    (nd : (syms.map Prod.fst).Nodup) (K : Nat) (ref : Nat → Nat) (hK : ∀ p ∈ syms, ref p.1 ≤ K)
    (kraft : (syms.map fun p => 2 ^ (K - ref p.1)).sum ≤ 2 ^ K) :
    ext T ≤ (syms.map fun p => p.2 * ref p.1).sum := by
  let ℓ : HTree → Nat := fun t => match t with | .leaf s _ => ref s | .node _ _ => 0
  have flat : (initForest syms).flatMap leafPairs = syms := flatMap_initForest syms
  have k : ((initForest syms).map fun t => 2 ^ (K - ℓ t)).sum = (syms.map fun p => 2 ^ (K - ref p.1)).sum := by
    simp [initForest, List.map_map, Function.comp_def, ℓ]
  have c : ((initForest syms).map fun t => t.weight * ℓ t + ext t).sum = (syms.map fun p => p.2 * ref p.1).sum := by
    simp [initForest, List.map_map, Function.comp_def, ℓ, ext, HTree.leaves, HTree.weight]
  have := opt_merges h (by rw [flat]; exact nd) K ℓ
    (by intro t ht; simp only [initForest, List.mem_map] at ht; obtain ⟨p, hp, rfl⟩ := ht; exact hK p hp)
    (by rw [k]; exact kraft)
  rw [c] at this
  exact this

end ZlibNgF.Math.Huff
