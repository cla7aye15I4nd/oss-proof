import ZlibNgF.Math.OverlayTiny
import ZlibNgF.Math.HuffBlCost

noncomputable section

/-!
# The data trees of a small block (heap-free)

For a literal/length or distance tree whose weight is below `2584` (so `gen_bitlen` keeps every depth, as at
`lit_bufsize ≤ 256`), the facts the small-buffer certificate (`OverlayTiny.tiny_header_excess`) takes:

* `data_kraft`: the code lengths have Kraft sum `Σ 2^(15 - len) ≤ 2^15` over the used and forced symbols;
* `data_leaf`: every symbol satisfies `LeafBound W` for any `W` at least the tree weight: an unused symbol has length
  at most 1 (a forced leaf is one of two leaves, both at depth 1), a used one has length at least 1 and the
  Fibonacci bound `f · F(len + 1) + F(len) ≤ W`.
-/

namespace ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

theorem leaves_ne : ∀ t : HTree, 1 ≤ t.leaves.length
  | .leaf _ _ => by simp [HTree.leaves]
  | .node a b => by
    have := leaves_ne a
    simp [HTree.leaves]; omega

theorem one_leaf_depth : ∀ t : HTree, t.leaves.length = 1 → ∀ x ∈ t.leaves, x.d = 0
  | .leaf _ _, _, x, hx => by simp [HTree.leaves] at hx; rw [hx]
  | .node a b, h, _, _ => by
    have := leaves_ne a; have := leaves_ne b
    simp [HTree.leaves] at h; omega

theorem two_leaves_depth : ∀ t : HTree, t.leaves.length = 2 → ∀ x ∈ t.leaves, x.d = 1
  | .leaf _ _, h, _, _ => by simp [HTree.leaves] at h
  | .node a b, h, x, hx => by
    have ha := leaves_ne a; have hb := leaves_ne b
    simp only [HTree.leaves, List.length_map, List.length_append] at h
    simp only [HTree.leaves, List.mem_map, List.mem_append] at hx
    obtain ⟨y, hy | hy, rfl⟩ := hx
    · simp [one_leaf_depth a (by omega) y hy]
    · simp [one_leaf_depth b (by omega) y hy]

theorem leaves_depth_pos : ∀ t : HTree, 2 ≤ t.leaves.length → ∀ x ∈ t.leaves, 1 ≤ x.d
  | .leaf _ _, h, _, _ => by simp [HTree.leaves] at h
  | .node _ _, _, x, hx => by
    simp only [HTree.leaves, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    simp

/-- The leaves of the built tree are its sorted leaf entries, with their depths. -/
theorem built_leaves {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems) :
    (buildTree elems freq).root.leaves.length = (buildTree elems freq).sorted.length ∧
    ∀ e ∈ (buildTree elems freq).sorted, ∃ x ∈ (buildTree elems freq).root.leaves,
      x.w = e.1 ∧ depthIn (buildTree elems freq).root e.2 = x.d := by
  generalize hb : buildTree elems freq = b
  obtain ⟨_ok, nd, _two, _le, _comp, _sum, _sorted, tr, merges⟩ := hb ▸ built_facts (freq := freq) hE
  generalize hsrt : b.sorted = srt at *
  generalize hT : b.root = T at *
  have pairs : (leafPairs T).Perm (srt.map fun e => (e.2, e.1)) := by
    have h := merges.pairs
    rw [flatMap_initForest] at h; exact h.symm
  have symPerm : (T.leaves.map (·.sym)).Perm (srt.map Prod.snd) := by
    have := pairs.map Prod.fst; simpa [leafPairs, List.map_map, Function.comp_def] using this
  have ndT : (T.leaves.map (·.sym)).Nodup := symPerm.nodup_iff.mpr nd
  refine ⟨by simpa using symPerm.length_eq, fun e he => ?_⟩
  have h : (e.2, e.1) ∈ leafPairs T := pairs.mem_iff.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
  simp only [leafPairs, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨x, hx, h1, h2⟩ := h
  exact ⟨x, hx, h2, by rw [← h1]; exact depthIn_of_mem ndT hx⟩

/-- Sums over the sorted leaf entries are sums over the leaves. -/
theorem built_transfer {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems) (g : Nat → Nat → Nat) :
    ((buildTree elems freq).sorted.map fun e => g e.1 (depthIn (buildTree elems freq).root e.2)).sum =
      ((buildTree elems freq).root.leaves.map fun x => g x.w x.d).sum := by
  generalize hb : buildTree elems freq = b
  obtain ⟨_ok, nd, _two, _le, _comp, _sum, _sorted, tr, merges⟩ := hb ▸ built_facts (freq := freq) hE
  generalize hsrt : b.sorted = srt at *
  generalize hT : b.root = T at *
  have pairs : (leafPairs T).Perm (srt.map fun e => (e.2, e.1)) := by
    have h := merges.pairs
    rw [flatMap_initForest] at h; exact h.symm
  have symPerm : (T.leaves.map (·.sym)).Perm (srt.map Prod.snd) := by
    have := pairs.map Prod.fst; simpa [leafPairs, List.map_map, Function.comp_def] using this
  have ndT : (T.leaves.map (·.sym)).Nodup := symPerm.nodup_iff.mpr nd
  have h1 : (srt.map fun e => g e.1 (depthIn T e.2)) =
      (srt.map fun e => (e.2, e.1)).map (fun p => g p.2 (depthIn T p.1)) := by
    simp [List.map_map, Function.comp_def]
  rw [h1, ← perm_sum (pairs.map (fun p => g p.2 (depthIn T p.1)))]
  simp only [leafPairs, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp [depthIn_of_mem ndT hx]

/-- **Kraft** of a tree without overflow at 15. -/
theorem data_kraft {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems)
    (hO : overflowCount 15 (buildTree elems freq).root = 0) :
    mass (fun v => OverlayTiny.kraftTerm (treeLengths elems 15 freq v)) elems ≤ 2 ^ 15 := by
  obtain ⟨ok, nd, two, _le, _comp, _sum, _sorted, _⟩ := built_facts (freq := freq) hE
  obtain ⟨lenT, leafOf⟩ := built_leaves (freq := freq) hE
  have tr := built_transfer (freq := freq) hE (fun _ d => 2 ^ (15 - min d 15))
  have kov := kraft_overflow 15 (buildTree elems freq).root
  rw [hO] at kov
  have dpos := leaves_depth_pos (buildTree elems freq).root (by omega)
  generalize hb : buildTree elems freq = b at *
  have tl : treeLengths elems 15 freq = genBitlen 15 b := by rw [← hb]; rfl
  rw [tl]
  have keys : ∀ v, v < elems → OverlayTiny.kraftTerm (genBitlen 15 b v) ≠ 0 → v ∈ b.sorted.map Prod.snd := by
    intro v _ hk
    unfold genBitlen at hk
    split at hk
    · simp [OverlayTiny.kraftTerm] at hk
    · rename_i i hi
      have := posOf_get (0, 0) b.sorted v i hi
      exact List.mem_map.mpr ⟨_, getD_mem (0, 0) b.sorted i this.1, this.2⟩
  have h1 := mass_le_list _ elems _ keys
  rw [List.map_map] at h1
  have each : ∀ e ∈ b.sorted, ((fun v => OverlayTiny.kraftTerm (genBitlen 15 b v)) ∘ Prod.snd) e =
      2 ^ (15 - min (depthIn b.root e.2) 15) := by
    intro e he
    obtain ⟨i, hi, _, _⟩ := posOf_spec (0, 0) b.sorted e nd he
    obtain ⟨x, hx, _, hd⟩ := leafOf e he
    have := dpos x hx
    simp only [Function.comp_def, genBitlen, hi, hO, ite_true, OverlayTiny.kraftTerm, hd]
    rw [ite_eq_right (by omega)]
  rw [List.map_congr_left each, tr] at h1
  omega

/-- **The leaf bound** of every symbol of a tree without overflow at 15, for any `W` at least its weight. -/
theorem data_leaf {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems)
    (hO : overflowCount 15 (buildTree elems freq).root = 0) {W : Nat}
    (hW : (buildTree elems freq).root.weight ≤ W) (v : Nat) (hv : v < elems) :
    OverlayTiny.LeafBound W (treeLengths elems 15 freq v) (freq v) := by
  obtain ⟨ok, nd, two, _le, _comp, _sum, _sorted, _⟩ := built_facts (freq := freq) hE
  obtain ⟨lenT, leafOf⟩ := built_leaves (freq := freq) hE
  have dpos := leaves_depth_pos (buildTree elems freq).root (by omega)
  have fp := ZlibNgF.Math.OverlayDynamic.fib_plus_of_no_overflow hE hO v hv
  have genuine := sorted_genuine (elems := elems) (freq := freq)
  have tl : treeLengths elems 15 freq = genBitlen 15 (buildTree elems freq) := rfl
  rw [tl]
  by_cases hf : freq v = 0
  · left
    refine ⟨hf, ?_⟩
    unfold genBitlen
    split
    · omega
    · rename_i i hi
      have g := posOf_get (0, 0) _ v i hi
      have mem := getD_mem (0, 0) _ i g.1
      have forcedLeaf := ok _ mem
      have short : (buildTree elems freq).sorted.length ≤ 2 := by
        refine Classical.byContradiction fun h => ?_
        have := (genuine (by omega) _ mem).2
        rw [g.2] at this; exact this hf
      obtain ⟨x, hx, _, hd⟩ := leafOf _ mem
      have d1 := two_leaves_depth _ (by omega) x hx
      simp only [hO, ite_true]
      rw [g.2] at hd
      rw [hd, d1]; omega
  · right
    obtain ⟨_, used⟩ := fp hf
    obtain ⟨x, hx, _, hd, _⟩ := ZlibNgF.Math.OverlayDynamic.used_leaf hE v hv hf
    have eq := (fp hf).1
    refine ⟨by omega, ?_, by omega⟩
    rw [eq, hd]; exact dpos x hx

end ZlibNgF.Math.Huff

namespace ZlibNgF.Math.Huff
set_option autoImplicit false

theorem repairStep_zero (L : Nat) (hL : 1 ≤ L) (c : Nat → Nat) (h : c 0 = 0) : repairStep L c 0 = 0 := by
  simp only [repairStep, updC]
  split
  · omega
  · split
    · omega
    · split
      · rename_i e; rw [← e, h]
      · exact h

theorem repairIter_zero (L : Nat) (hL : 1 ≤ L) : ∀ (M : Nat) (c : Nat → Nat), c 0 = 0 → repairIter L M c 0 = 0
  | 0, _, h => h
  | M + 1, c, h => repairIter_zero L hL M _ (repairStep_zero L hL c h)

theorem lenOfRank_pos (L : Nat) (hL : 1 ≤ L) (c : Nat → Nat) (r : Nat) (hr : 1 ≤ r) (h0 : c 0 = 0) :
    lenOfRank L c r ≠ 0 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have g := lenSearch_ge c r L' 1
  have e : lenOfRank (L' + 1) c r = if r ≤ c 0 then 0 else lenSearch c r 1 L' := rfl
  rw [e, h0]
  split
  · omega
  · omega

/-- **Every used symbol gets a nonzero code length.** -/
theorem treeLengths_pos : ∀ (elems L : Nat) (freq : Nat → Nat) (v : Nat), 3 ≤ elems → 1 ≤ L → v < elems →
    freq v ≠ 0 → treeLengths elems L freq v ≠ 0 := by
  intro elems L freq v hE hL hv hf
  obtain ⟨_ok, nd, two, _le, comp, _sum, _sorted, _⟩ := built_facts (freq := freq) hE
  obtain ⟨lenT, leafOf⟩ := built_leaves (freq := freq) hE
  have dpos := leaves_depth_pos (buildTree elems freq).root (by omega)
  obtain ⟨i, hi, hil, hg⟩ := posOf_spec (0, 0) _ (freq v, v) nd (comp v hv hf)
  have tl : treeLengths elems L freq = genBitlen L (buildTree elems freq) := rfl
  rw [tl]
  unfold genBitlen
  simp only at hi
  rw [hi]
  simp only
  split
  · obtain ⟨x, hx, _, hd⟩ := leafOf _ (comp v hv hf)
    simp only at hd
    rw [hd]; have := dpos x hx; omega
  · have c0 : blCount L (buildTree elems freq).sorted (buildTree elems freq).root 0 = 0 := by
      unfold blCount
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro e he
      obtain ⟨x, hx, _, hd⟩ := leafOf e he
      have := dpos x hx
      simp only [beq_iff_eq]; rw [hd]; omega
    have z := repairIter_zero L hL ((overflowCount L (buildTree elems freq).root + 1) / 2) _ c0
    exact lenOfRank_pos L hL _ _ (by omega) z

end ZlibNgF.Math.Huff
