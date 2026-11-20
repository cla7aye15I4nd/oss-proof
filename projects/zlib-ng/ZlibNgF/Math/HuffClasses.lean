import ZlibNgF.Math.HuffBuilt
import ZlibNgF.Math.HuffPushCost

noncomputable section


/-!
# Code classes of the lengths zlib-ng assigns (heap-free)

For a literal/length or distance tree (`max_length = 15`) built by the model (`treeLengths elems 15 freq`),
every used symbol `v` falls in a `CodeClass` of `HuffPushCost` with the tree weight `W` (at most the total
frequency plus 2 forced leaves), and the push budget of the classes is below the alphabet size
(`tree_classes`). Without an overflow (in particular when `W < 2584 = F(17) + F(16)`) every class is 0.

The proof applies the rank-form results of the sibling project (`fibPush_rank`, `fibPush_of_fibPlus`) to the
leaves in `sorted` order (rank `r` = index `N - r`): weights are nonincreasing in rank because `sorted` is
ascending, the Fibonacci depth bound holds because the merge is a Huffman merge (`built_facts`,
`fibPlus_of_merges`), and the clamped Kraft facts come from `HuffKraft`.
-/

namespace ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

/-! ## List and rank-sum helpers -/

theorem find_nodup : ∀ (l : List LeafInfo) (x : LeafInfo), (l.map (·.sym)).Nodup → x ∈ l →
    l.find? (fun y => y.sym == x.sym) = some x
  | [], x, _, h => by simp at h
  | y :: l, x, nd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nd
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have hne : y.sym ≠ x.sym := fun e => nd.1 ⟨x, h, e.symm⟩
      simp [hne, find_nodup l x nd.2 h]

theorem depthIn_of_mem {T : HTree} {x : LeafInfo} (nd : (T.leaves.map (·.sym)).Nodup) (h : x ∈ T.leaves) :
    depthIn T x.sym = x.d := by
  simp [depthIn, find_nodup T.leaves x nd h]

theorem sumR_getD {α : Type} (g : α → Nat) (d : α) : ∀ l : List α,
    sumR (fun r => g (l.getD (l.length - r) d)) l.length = (l.map g).sum
  | [] => rfl
  | x :: xs => by
    have ih := sumR_getD g d xs
    simp only [List.length_cons, sumR, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [sumR_congr xs.length (g := fun r => g (xs.getD (xs.length - r) d)) (fun r h1 h2 => by
      rw [show xs.length + 1 - r = (xs.length - r) + 1 by omega, List.getD_cons_succ]), ih]
    omega

theorem length_filter_sum {α : Type} (p : α → Bool) : ∀ l : List α,
    (l.filter p).length = (l.map fun a => if p a then 1 else 0).sum
  | [] => rfl
  | x :: xs => by
    have := length_filter_sum p xs
    by_cases h : p x <;> simp [h, this] <;> omega

theorem countR_mul (p : Nat → Bool) (c : Nat) : ∀ N,
    countR p N * c = sumR (fun r => if p r then c else 0) N
  | 0 => by simp [countR, sumR]
  | N + 1 => by
    have := countR_mul p c N
    simp only [countR, sumR] at this ⊢
    rw [Nat.add_mul, this]; by_cases h : p (N + 1) <;> simp [h]

theorem wsum_hist (wt m : Nat → Nat) (N : Nat) : ∀ J,
    wsum wt (fun j => countR (fun r => m r == j) N) J = sumR (fun r => if m r ≤ J then wt (m r) else 0) N
  | 0 => by
    simp only [wsum]
    rw [countR_mul]
    exact sumR_congr N fun r _ _ => by by_cases h : m r = 0 <;> simp [h]
  | J + 1 => by
    simp only [wsum]
    rw [wsum_hist wt m N J, countR_mul, ← sumR_add]
    exact sumR_congr N fun r _ _ => by
      by_cases h1 : m r ≤ J
      · simp [h1, show m r ≤ J + 1 by omega, show m r ≠ J + 1 by omega]
      · by_cases h2 : m r = J + 1
        · simp [h2] <;> (intro h; omega)
        · simp [h1, h2, show ¬ m r ≤ J + 1 by omega]

theorem posOf_spec (d : Nat × Nat) : ∀ (l : List (Nat × Nat)) (e : Nat × Nat), (l.map Prod.snd).Nodup → e ∈ l →
    ∃ i, posOf e.2 l = some i ∧ i < l.length ∧ l.getD i d = e
  | [], e, _, h => by simp at h
  | y :: l, e, nd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nd
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp [posOf], by simp, by simp⟩
    · have hne : y.2 ≠ e.2 := fun q => nd.1 ⟨e, h, q.symm⟩
      obtain ⟨i, hi, hl, hg⟩ := posOf_spec d l e nd.2 h
      exact ⟨i + 1, by simp [posOf, hne, hi], by simp; omega, by simpa using hg⟩

theorem posOf_get (d : Nat × Nat) : ∀ (l : List (Nat × Nat)) (v i : Nat), posOf v l = some i →
    i < l.length ∧ (l.getD i d).2 = v
  | [], v, i, h => by simp [posOf] at h
  | y :: l, v, i, h => by
    simp only [posOf] at h
    split at h
    · simp at h; subst h; simp_all
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      have := posOf_get d l v j hj
      exact ⟨by simp; omega, by simpa using this.2⟩

/-- Sums over an injective rank map. -/
theorem mass_inj_le (U : Nat → Prop) [DecidablePred U] (ρ : Nat → Nat) (N : Nat) :
    ∀ (n : Nat) (P : Nat → Nat), (∀ v, v < n → U v → 1 ≤ ρ v ∧ ρ v ≤ N) →
      (∀ v v', v < n → v' < n → U v → U v' → ρ v = ρ v' → v = v') →
      mass (fun v => if U v then P (ρ v) else 0) n ≤ sumR P N
  | 0, P, _, _ => Nat.zero_le _
  | n + 1, P, hr, hi => by
    simp only [mass]
    by_cases hu : U n
    · simp only [hu, ite_true]
      let P' := fun r => if r = ρ n then 0 else P r
      have h1 := mass_inj_le U ρ N n P' (fun v hv hu => hr v (by omega) hu)
        (fun v v' hv hv' => hi v v' (by omega) (by omega))
      have h2 : mass (fun v => if U v then P (ρ v) else 0) n = mass (fun v => if U v then P' (ρ v) else 0) n :=
        mass_congr fun v hv => by
          by_cases huv : U v
          · have : ρ v ≠ ρ n := fun e => by have := hi v n (by omega) (by omega) huv hu e; omega
            simp [huv, P', this]
          · simp [huv]
      have hb := hr n (by omega) hu
      have hs : ∀ M, sumR P M = sumR P' M + (if ρ n ≤ M then P (ρ n) else 0) := by
        intro M
        induction M with
        | zero => simp [sumR]; omega
        | succ M ih =>
          simp only [sumR, ih, P']
          by_cases e : M + 1 = ρ n
          · simp [e] <;> (intro h; omega)
          · have : (ρ n ≤ M + 1) = (ρ n ≤ M) := by apply propext; omega
            simp [e, this]; omega
      have h3 := hs N
      simp only [hb.2, ite_true] at h3
      omega
    · simp only [hu, ite_false, Nat.add_zero]
      exact mass_inj_le U ρ N n P (fun v hv hu => hr v (by omega) hu) (fun v v' hv hv' => hi v v' (by omega) (by omega))

theorem lenSearch_le (c : Nat → Nat) (r : Nat) : ∀ fuel k, lenSearch c r k fuel ≤ k + fuel
  | 0, k => by simp [lenSearch]
  | fuel + 1, k => by
    simp only [lenSearch]; split
    · omega
    · have := lenSearch_le c r fuel (k + 1); omega

/-- `gen_bitlen`'s lengths never exceed `max_length`. -/
theorem genBitlen_le (L : Nat) (b : Built) (v : Nat) : genBitlen L b v ≤ L := by
  unfold genBitlen
  split
  · exact Nat.zero_le _
  · rename_i i _
    split
    · exact Nat.min_le_right _ _
    · have := lenSearch_le (repairIter L ((overflowCount L b.root + 1) / 2) (blCount L b.sorted b.root))
        (b.sorted.length - i) L 0
      unfold lenOfRank; omega

theorem getD_mem {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i < l.length → l.getD i d ∈ l
  | [], i, h => by simp at h
  | x :: xs, 0, _ => by simp
  | x :: xs, i + 1, h => by
    simp only [List.getD_cons_succ, List.mem_cons]
    exact Or.inr (getD_mem d xs i (by simp at h; omega))

theorem sorted_getD (d : Nat × Nat) : ∀ (l : List (Nat × Nat)) (i j : Nat),
    l.Pairwise (fun a b => a.1 ≤ b.1) → i ≤ j → j < l.length → (l.getD i d).1 ≤ (l.getD j d).1
  | [], i, j, _, _, h => by simp at h
  | x :: xs, 0, 0, _, _, _ => Nat.le_refl _
  | x :: xs, 0, j + 1, hp, _, h => by
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact (List.pairwise_cons.mp hp).1 _ (getD_mem d xs j (by simp at h; omega))
  | x :: xs, i + 1, 0, _, hij, _ => by omega
  | x :: xs, i + 1, j + 1, hp, hij, h => by
    simp only [List.getD_cons_succ]
    exact sorted_getD d xs i j (List.pairwise_cons.mp hp).2 (by omega) (by simp at h; omega)

theorem flatMap_initForest : ∀ (syms : List (Nat × Nat)), (initForest syms).flatMap leafPairs = syms
  | [] => rfl
  | p :: ps => by
    have ih := flatMap_initForest ps
    simp only [initForest] at ih ⊢
    simp only [List.map_cons, List.flatMap_cons, ih]
    rfl

theorem fib_16_17 : fib 16 = 987 ∧ fib 17 = 1597 := by decide

/-- **Code classes of a literal/length or distance tree** (`max_length = 15`). -/
theorem tree_classes {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems) (hE2 : elems ≤ 2 ^ 15) :
    (buildTree elems freq).root.weight ≤ mass freq elems + 2 ∧
    ∃ cls org : Nat → Nat,
      (∀ v, v < elems → freq v ≠ 0 →
        CodeClass (buildTree elems freq).root.weight (freq v) (genBitlen 15 (buildTree elems freq) v) (cls v) (org v)) ∧
      mass (fun v => if freq v = 0 then 0 else pushCostA (cls v) (org v)) elems + 1 ≤ elems ∧
      ((buildTree elems freq).root.weight < 2584 →
        mass (fun v => if freq v = 0 then 0 else pushCostA (cls v) (org v)) elems = 0) := by
  generalize hb : buildTree elems freq = b
  obtain ⟨ok, nd, two, le, comp, sum, sorted, tr, merges⟩ := hb ▸ built_facts (freq := freq) hE
  generalize hsrt : b.sorted = srt at *
  generalize hT : b.root = T at *
  have pairs : (leafPairs T).Perm (srt.map fun e => (e.2, e.1)) := by
    have h := merges.pairs
    rw [flatMap_initForest] at h; exact h.symm
  have fibT := fibPlus_of_merges merges (by
    intro p hp; simp only [List.mem_map] at hp; obtain ⟨e, he, rfl⟩ := hp; exact (ok e he).2.1)
  have symPerm : (T.leaves.map (·.sym)).Perm (srt.map Prod.snd) := by
    have := pairs.map Prod.fst; simpa [leafPairs, List.map_map, Function.comp_def] using this
  have ndT : (T.leaves.map (·.sym)).Nodup := symPerm.nodup_iff.mpr nd
  have lenT : T.leaves.length = srt.length := by simpa using symPerm.length_eq
  have transfer : ∀ g : Nat → Nat,
      (srt.map fun e => g (depthIn T e.2)).sum = (T.leaves.map fun x => g x.d).sum := by
    intro g
    have h1 : (srt.map fun e => g (depthIn T e.2)) = (srt.map Prod.snd).map (fun v => g (depthIn T v)) := by
      simp [List.map_map, Function.comp_def]
    rw [h1, ← perm_sum (symPerm.map (fun v => g (depthIn T v))), List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    simp [depthIn_of_mem ndT hx]
  have match_ : ∀ e ∈ srt, ∃ x ∈ T.leaves, x.sym = e.2 ∧ x.w = e.1 ∧ depthIn T e.2 = x.d := by
    intro e he
    have h : (e.2, e.1) ∈ leafPairs T := pairs.mem_iff.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
    simp only [leafPairs, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨x, hx, h1, h2⟩ := h
    exact ⟨x, hx, h1, h2, by rw [← h1]; exact depthIn_of_mem ndT hx⟩
  have hW : T.weight ≤ mass freq elems + 2 := by
    rw [weight_eq_sum]
    have := perm_sum (pairs.map Prod.snd)
    simp only [leafPairs, List.map_map] at this
    have e2 : (List.map (Prod.snd ∘ fun e : Nat × Nat => (e.2, e.1)) srt) = srt.map Prod.fst := by
      simp [Function.comp_def]
    have e1 : (List.map (Prod.snd ∘ fun x : LeafInfo => (x.sym, x.w)) T.leaves) = T.leaves.map (·.w) := by
      simp [Function.comp_def]
    rw [e1, e2] at this
    omega
  have dpos : ∀ x ∈ T.leaves, 1 ≤ x.d := by
    cases T with
    | leaf s w => simp [HTree.leaves] at lenT; omega
    | node a c =>
      intro x hx
      simp only [HTree.leaves, List.mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      simp
  refine ⟨hW, ?_⟩
  let N := srt.length
  let d0 : Nat × Nat := (0, 0)
  by_cases hov : overflowCount 15 T = 0
  · -- no overflow: every class is 0
    refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, fun _ => ?_⟩
    · intro v hv hfv
      obtain ⟨i, hi, _, hg⟩ := posOf_spec d0 srt (freq v, v) nd (comp v hv hfv)
      obtain ⟨x, hx, h1, h2, h3⟩ := match_ _ (comp v hv hfv)
      have gl : genBitlen 15 b v = min x.d 15 := by
        unfold genBitlen; rw [hsrt, hT]; simp only at hi; rw [hi]; simp only [hov, ite_true]
        simp only at h3; rw [h3]
      rw [gl]
      left
      refine ⟨rfl, ?_⟩
      have := fibT x hx
      simp only at h2
      rw [← h2]
      have fm : fib (min x.d 15 + 1) ≤ fib (x.d + 1) := fib_mono (by omega)
      have := Nat.mul_le_mul_left x.w fm
      omega
    · have : mass (fun v => if freq v = 0 then 0 else pushCostA ((fun _ => 0) v) ((fun _ => 0) v)) elems = 0 := by
        rw [mass_congr (g := fun _ => 0) (fun v _ => by simp [pushCostA])]; exact mass_zero _
      omega
    · rw [mass_congr (g := fun _ => 0) (fun v _ => by simp [pushCostA])]; exact mass_zero _
  · -- overflow: the repair
    have big : 2584 ≤ T.weight := by
      have : ∃ x ∈ T.leaves, 16 ≤ x.d := Classical.byContradiction fun h => by
        apply hov; apply overflow_zero; intro x hx
        exact Classical.byContradiction fun h' => h ⟨x, hx, by omega⟩
      obtain ⟨x, hx, hd⟩ := this
      have hf := fibT x hx
      have w1 : 1 ≤ x.w := by
        have h := pairs.mem_iff.mp (by unfold leafPairs; exact List.mem_map.mpr ⟨x, hx, rfl⟩)
        simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨e, he, _, h2⟩ := h
        have := (ok e he).2.1; omega
      have f1 := fib_mono (show 17 ≤ x.d + 1 by omega)
      have f2 := fib_mono (show 16 ≤ x.d by omega)
      have := Nat.mul_le_mul w1 f1
      rw [fib_16_17.1] at f2; rw [fib_16_17.2] at this
      omega
    let e := fun r => srt.getD (N - r) d0
    let wR := fun r => (e r).1
    let δR := fun r => depthIn T (e r).2
    have eMem : ∀ r, 1 ≤ r → r ≤ N → e r ∈ srt := fun r h1 h2 => getD_mem d0 srt (N - r) (by omega)
    have leafOf : ∀ r, 1 ≤ r → r ≤ N → ∃ x ∈ T.leaves, x.w = wR r ∧ δR r = x.d := by
      intro r h1 h2
      obtain ⟨x, hx, _, hw, hd⟩ := match_ (e r) (eMem r h1 h2)
      exact ⟨x, hx, hw, hd⟩
    have hδ : ∀ r, 1 ≤ r → r ≤ N → 1 ≤ δR r := by
      intro r h1 h2; obtain ⟨x, hx, _, hd⟩ := leafOf r h1 h2; rw [hd]; exact dpos x hx
    have hw : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → wR r ≤ wR y := by
      intro y r h1 h2 h3
      exact sorted_getD d0 srt (N - r) (N - y) sorted (by omega) (by omega)
    have hL2 : ∀ y, 1 ≤ y → y ≤ N → wR y * fib (δR y + 1) ≤ T.weight := by
      intro y h1 h2; obtain ⟨x, hx, hwx, hd⟩ := leafOf y h1 h2
      rw [← hwx, hd]; have := fibT x hx; omega
    have hN : N ≤ 2 ^ 15 := by omega
    have hist : ∀ j, blCount 15 srt T j = histR δR N j := by
      intro j
      unfold blCount histR countR
      rw [length_filter_sum, ← sumR_getD _ d0 srt]
    have hkr : krS (histR δR N) 15 = 2 ^ 15 + overflowCount 15 T / 2 := by
      unfold krS histR
      rw [wsum_hist]
      have e1 : sumR (fun r => if min (δR r) 15 ≤ 15 then 2 ^ (15 - min (δR r) 15) else 0) N =
          (srt.map fun e => 2 ^ (15 - min (depthIn T e.2) 15)).sum := by
        rw [← sumR_getD _ d0 srt]
        exact sumR_congr N fun r _ _ => by simp [Nat.min_le_right]; rfl
      rw [e1, transfer (fun d => 2 ^ (15 - min d 15))]
      have := kraft_overflow 15 T
      have := overflow_even 15 T
      omega
    have h15 : overflowCount 15 T / 2 + 1 ≤ histR δR N 15 := by
      have hd := deep_leaves 15 T hov
      have e1 : histR δR N 15 = (srt.map fun e => if min (depthIn T e.2) 15 == 15 then 1 else 0).sum := by
        unfold histR countR; rw [← sumR_getD _ d0 srt]
      have e2 : (T.leaves.filter fun x => decide (15 ≤ x.d)).length =
          (T.leaves.map fun x => if min x.d 15 == 15 then 1 else 0).sum := by
        rw [length_filter_sum]; congr 1; apply List.map_congr_left; intro x _
        by_cases h : 15 ≤ x.d
        · simp [h, show min x.d 15 = 15 by omega]
        · simp [h, show min x.d 15 = x.d by omega]; omega
      rw [e1, transfer (fun d => if min d 15 == 15 then 1 else 0)]
      omega
    obtain ⟨clsR, orgR, classified, budget⟩ :=
      fibPush_rank N T.weight (overflowCount 15 T / 2) wR δR hδ hw hL2 hN hkr h15
    let ρ := fun v => N - (posOf v srt).getD 0
    refine ⟨fun v => clsR (ρ v), fun v => orgR (ρ v), ?_, ?_, fun h => absurd h (by omega)⟩
    · intro v hv hfv
      obtain ⟨i, hi, hil, hg⟩ := posOf_spec d0 srt (freq v, v) nd (comp v hv hfv)
      simp only at hi
      have hρ : ρ v = N - i := by simp [ρ, hi]
      have c := classified (N - i) (by omega) (by omega)
      have hwi : wR (N - i) = freq v := by
        show (srt.getD (N - (N - i)) d0).1 = freq v
        rw [show N - (N - i) = i by omega, hg]
      have gl : genBitlen 15 b v =
          lenOfRank 15 (repairIter 15 (overflowCount 15 T / 2) (histR δR N)) (N - i) := by
        unfold genBitlen; rw [hsrt, hT, hi]; simp only [hov, ite_false]
        have ev := overflow_even 15 T
        rw [show (overflowCount 15 T + 1) / 2 = overflowCount 15 T / 2 by omega]
        rw [show blCount 15 srt T = histR δR N from funext hist]
      simp only [hρ, gl, ← hwi]
      exact c
    · have hm := mass_inj_le (fun v => freq v ≠ 0) ρ N elems (fun r => pushCostA (clsR r) (orgR r)) ?_ ?_
      · have e1 : mass (fun v => if freq v = 0 then 0 else pushCostA (clsR (ρ v)) (orgR (ρ v))) elems =
            mass (fun v => if freq v ≠ 0 then pushCostA (clsR (ρ v)) (orgR (ρ v)) else 0) elems :=
          mass_congr fun v _ => by by_cases h : freq v = 0 <;> simp [h]
        simp only at e1 hm ⊢
        rw [e1]; omega
      · intro v hv hu
        obtain ⟨i, hi, hil, _⟩ := posOf_spec d0 srt (freq v, v) nd (comp v hv hu)
        simp only at hi; simp only [ρ, hi, Option.getD_some]; omega
      · intro v v' hv hv' hu hu' heq
        obtain ⟨i, hi, hil, hg⟩ := posOf_spec d0 srt (freq v, v) nd (comp v hv hu)
        obtain ⟨i', hi', hil', hg'⟩ := posOf_spec d0 srt (freq v', v') nd (comp v' hv' hu')
        simp only at hi hi'
        simp only [ρ, hi, hi', Option.getD_some] at heq
        have : i = i' := by omega
        subst this
        rw [hg] at hg'
        exact (Prod.mk.inj hg').2

end ZlibNgF.Math.Huff
