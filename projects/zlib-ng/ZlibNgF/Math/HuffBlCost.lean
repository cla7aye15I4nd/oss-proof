import ZlibNgF.Math.HuffOptimal
import ZlibNgF.Math.RepairCap15.Tree
import ZlibNgF.Math.RepairCap13.Tree

noncomputable section

/-!
# The cost of the bit-length tree against a reference code (heap-free)

`bl_cost_le`: for the bit-length tree that zlib-ng builds (`treeLengths 19 7 f`, `max_length = 7`) on frequencies
`f` of total at most 316, whose used symbols lie in a set `allowed` with a reference code `ref` (lengths `1 .. K`,
Kraft sum at most one over `allowed`), `Σ f · len ≤ Σ f · ref + Δ W` where `W = Σ f` and `Δ` bounds the repair term
of `gen_bitlen` on every histogram of the shape the first pass leaves (`RepairShape`) under the per-rank Fibonacci
caps (`RankCaps`):

* the true depths cost at most `Σ f · ref` (`huffman_opt`);
* the repaired lengths cost at most the true depths plus `repairExtra` (`repair_cost_le`; the lengths `gen_bitlen`
  hands out by rank, `lenOfRank 7`, are at most `lenOfRank 15` of the same counts);
* the first-pass histogram has `RepairShape` (`kraft_overflow`, `deep_leaves`) and the ranks obey the Fibonacci
  caps (`fibPlus_of_merges`, `rank_cap`).

`bl_cost_le_15` (at most 15 allowed symbols, `Δ = 245`) and `bl_cost_le_13` (at most 13, `Δ = 29 + W / 2`)
instantiate it with the generated case analyses `repairExtra_cap15` / `repairExtra_cap13`.
-/

namespace ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

theorem lenSearch_ge (c : Nat → Nat) (r : Nat) : ∀ fuel k, k ≤ lenSearch c r k fuel
  | 0, k => by simp [lenSearch]
  | fuel + 1, k => by
    simp only [lenSearch]; split
    · exact Nat.le_refl _
    · have := lenSearch_ge c r fuel (k + 1); omega

theorem lenSearch_fuel (c : Nat → Nat) (r : Nat) : ∀ a b k, lenSearch c r k a ≤ lenSearch c r k (a + b)
  | 0, b, k => by rw [Nat.zero_add]; simp only [lenSearch]; exact lenSearch_ge c r b k
  | a + 1, b, k => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [lenSearch]; split
    · exact Nat.le_refl _
    · exact lenSearch_fuel c r a b (k + 1)

theorem lenOfRank_7_le (c : Nat → Nat) (r : Nat) : lenOfRank 7 c r ≤ lenOfRank 15 c r :=
  lenSearch_fuel c r 7 8 0

theorem list_le_mass (h : Nat → Nat) : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ v ∈ l, v < n) →
    (l.map h).sum ≤ mass h n
  | 0, l, _, hl => by
    cases l with
    | nil => simp [mass]
    | cons v _ => exact absurd (hl v (List.mem_cons_self ..)) (by omega)
  | n + 1, l, nd, hl => by
    show _ ≤ mass h n + h n
    by_cases hn : n ∈ l
    · have p := List.perm_cons_erase hn
      rw [perm_sum (p.map h)]
      simp only [List.map_cons, List.sum_cons]
      have nd' := p.nodup_iff.mp nd
      have ih := list_le_mass h n (l.erase n) (List.nodup_cons.mp nd').2 (fun v hv => by
        have := hl v (List.mem_of_mem_erase hv)
        have ne : v ≠ n := fun e => (List.nodup_cons.mp nd').1 (e ▸ hv)
        omega)
      omega
    · have ih := list_le_mass h n l nd (fun v hv => by
        have := hl v hv; have : v ≠ n := fun e => hn (e ▸ hv); omega)
      omega

theorem mass_le_list (h : Nat → Nat) : ∀ (n : Nat) (l : List Nat), (∀ v, v < n → h v ≠ 0 → v ∈ l) →
    mass h n ≤ (l.map h).sum
  | 0, l, _ => by simp [mass]
  | n + 1, l, hl => by
    show mass h n + h n ≤ _
    by_cases hn : h n = 0
    · have := mass_le_list h n l (fun v hv => hl v (by omega)); omega
    · have mem := hl n (by omega) hn
      have p := List.perm_cons_erase mem
      rw [perm_sum (p.map h)]
      simp only [List.map_cons, List.sum_cons]
      have := mass_le_list h n (l.erase n) (fun v hv hv' =>
        (List.mem_erase_of_ne (by omega)).mpr (hl v (by omega) hv'))
      omega

theorem map_sum_le {α : Type} (g h : α → Nat) : ∀ l : List α, (∀ x ∈ l, g x ≤ h x) →
    (l.map g).sum ≤ (l.map h).sum
  | [], _ => Nat.le_refl _
  | x :: l, hl => by
    simp only [List.map_cons, List.sum_cons]
    have := hl x (List.mem_cons_self ..)
    have := map_sum_le g h l (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    omega

theorem getD_inj (d : Nat × Nat) : ∀ (l : List (Nat × Nat)) (i j : Nat), (l.map Prod.snd).Nodup →
    i < l.length → j < l.length → l.getD i d = l.getD j d → i = j
  | [], _, _, _, h, _, _ => by simp at h
  | x :: xs, 0, 0, _, _, _, _ => rfl
  | x :: xs, 0, j + 1, nd, _, hj, e => by
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e
    simp only [List.map_cons, List.nodup_cons] at nd
    exact absurd (List.mem_map.mpr ⟨_, getD_mem d xs j (by simp at hj; omega), by rw [← e]⟩) nd.1
  | x :: xs, i + 1, 0, nd, hi, _, e => by
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e
    simp only [List.map_cons, List.nodup_cons] at nd
    exact absurd (List.mem_map.mpr ⟨_, getD_mem d xs i (by simp at hi; omega), by rw [e]⟩) nd.1
  | x :: xs, i + 1, j + 1, nd, hi, hj, e => by
    simp only [List.getD_cons_succ] at e
    simp only [List.map_cons, List.nodup_cons] at nd
    have := getD_inj d xs i j nd.2 (by simp at hi; omega) (by simp at hj; omega) e
    omega

theorem sum_ones {α : Type} : ∀ l : List α, (l.map fun _ => (1 : Nat)).sum = l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, List.length_cons, sum_ones l]; omega

theorem len_two {α : Type} : ∀ l : List α, l.length = 2 → ∃ x y, l = [x, y]
  | [], h => by simp at h
  | [_], h => by simp at h
  | [x, y], _ => ⟨x, y, rfl⟩
  | _ :: _ :: _ :: _, h => by simp at h

/-- With at least three leaves, `build_tree` forced none: every leaf is a used symbol with its frequency. -/
theorem sorted_genuine {elems : Nat} {freq : Nat → Nat} (h3 : 3 ≤ (buildTree elems freq).sorted.length) :
    ∀ e ∈ (buildTree elems freq).sorted, e.1 = freq e.2 ∧ freq e.2 ≠ 0 := by
  have p := sortKeys_perm (forced (scanLeaves freq elems) (maxCode1 freq elems)).1
  have hs : (buildTree elems freq).sorted = sortKeys (forced (scanLeaves freq elems) (maxCode1 freq elems)).1 := rfl
  rw [hs] at h3 ⊢
  rw [p.length_eq] at h3
  intro e he
  have he' := p.mem_iff.mp he
  have scan : ∀ e ∈ scanLeaves freq elems, e.1 = freq e.2 ∧ freq e.2 ≠ 0 := fun e he => (scan_mem he).2
  generalize scanLeaves freq elems = s at *
  match s with
  | [] => simp [forced] at h3
  | [l] => simp [forced] at h3
  | a :: b :: rest => exact scan e (by simpa [forced] using he')

/-- **The bit-length tree against a reference code**, for a repair bound `Δ`. -/
theorem bl_cost_le (f : Nat → Nat) (allowed : Nat → Bool) (K : Nat) (ref : Nat → Nat) (Nmax : Nat) (Δ : Nat → Nat)
    (used : ∀ v, v < 19 → f v ≠ 0 → allowed v = true)
    (bound : ∀ v, v < 19 → allowed v = true → 1 ≤ ref v ∧ ref v ≤ K)
    (kraft : mass (fun v => if allowed v then 2 ^ (K - ref v) else 0) 19 ≤ 2 ^ K)
    (count : mass (fun v => if allowed v then 1 else 0) 19 ≤ Nmax)
    (weight : mass f 19 ≤ 316)
    (cap : ∀ (c w : Nat → Nat) (W N M : Nat), RepairShape c N M → N ≤ Nmax → 1 ≤ M → RankCaps c w W N →
      W ≤ 316 → repairExtra 7 w M c ≤ Δ W) :
    mass (fun v => f v * treeLengths 19 7 f v) 19 ≤ mass (fun v => f v * ref v) 19 + Δ (mass f 19) := by
  have genuine := sorted_genuine (elems := 19) (freq := f)
  generalize hb : buildTree 19 f = b at genuine
  obtain ⟨ok, nd, two, _le, comp, _sum, sorted, tr, merges⟩ := hb ▸ built_facts (freq := f) (elems := 19) (by omega)
  have tl : treeLengths 19 7 f = genBitlen 7 b := by rw [← hb]; rfl
  rw [tl]
  have gb : ∀ v, genBitlen 7 b v = match posOf v b.sorted with
      | none => 0
      | some i => if overflowCount 7 b.root = 0 then min (depthIn b.root v) 7
        else lenOfRank 7 (repairIter 7 ((overflowCount 7 b.root + 1) / 2) (blCount 7 b.sorted b.root))
          (b.sorted.length - i) := fun v => rfl
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
  have transfer : ∀ g : Nat → Nat → Nat,
      (srt.map fun e => g e.1 (depthIn T e.2)).sum = (T.leaves.map fun x => g x.w x.d).sum := by
    intro g
    have h1 : (srt.map fun e => g e.1 (depthIn T e.2)) =
        (srt.map fun e => (e.2, e.1)).map (fun p => g p.2 (depthIn T p.1)) := by
      simp [List.map_map, Function.comp_def]
    rw [h1, ← perm_sum (pairs.map (fun p => g p.2 (depthIn T p.1)))]
    simp only [leafPairs, List.map_map]
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
  have dpos : ∀ x ∈ T.leaves, 1 ≤ x.d := by
    cases T with
    | leaf s w => simp [HTree.leaves] at lenT; omega
    | node a c =>
      intro x hx
      simp only [HTree.leaves, List.mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      simp
  let d0 : Nat × Nat := (0, 0)
  have kov := kraft_overflow 7 T
  have even := overflow_even 7 T
  -- the cost side, over `srt`
  have costSrt : mass (fun v => f v * genBitlen 7 b v) 19 ≤ (srt.map fun e => e.1 * genBitlen 7 b e.2).sum := by
    have h1 := mass_le_list (fun v => f v * genBitlen 7 b v) 19 (srt.map Prod.snd) (by
      intro v hv hne
      have : f v ≠ 0 := fun z => hne (by simp [z])
      exact List.mem_map.mpr ⟨_, comp v hv this, rfl⟩)
    rw [List.map_map] at h1
    refine Nat.le_trans h1 (map_sum_le _ _ srt fun e he => ?_)
    have := ok e he
    simp only [Function.comp_def]
    rcases this.2.2 with ⟨h, _⟩ | ⟨_, h⟩
    · rw [h]; exact Nat.le_refl _
    · rw [h]; simp
  by_cases hN : srt.length ≤ 2
  · -- two leaves, both at depth 1
    have two' : srt.length = 2 := by omega
    obtain ⟨x, y, hxy⟩ := len_two T.leaves (lenT.trans two')
    have hx := dpos x (by rw [hxy]; simp)
    have hy := dpos y (by rw [hxy]; simp)
    rw [hxy] at kov
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at kov
    have p6 : (2 : Nat) ^ 6 = 64 := rfl
    have p5 : (2 : Nat) ^ 5 = 32 := rfl
    have px : 2 ^ (7 - min x.d 7) ≤ 64 ∧ (2 ≤ x.d → 2 ^ (7 - min x.d 7) ≤ 32) :=
      ⟨p6 ▸ Nat.pow_le_pow_right (by omega) (by omega), fun h => p5 ▸ Nat.pow_le_pow_right (by omega) (by omega)⟩
    have py : 2 ^ (7 - min y.d 7) ≤ 64 ∧ (2 ≤ y.d → 2 ^ (7 - min y.d 7) ≤ 32) :=
      ⟨p6 ▸ Nat.pow_le_pow_right (by omega) (by omega), fun h => p5 ▸ Nat.pow_le_pow_right (by omega) (by omega)⟩
    have ov0 : overflowCount 7 T = 0 := by omega
    have d1 : ∀ z ∈ T.leaves, z.d = 1 := by
      intro z hz
      rw [hxy] at hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl
      · rcases Nat.lt_or_ge z.d 2 with h | h
        · omega
        · have := px.2 h; omega
      · rcases Nat.lt_or_ge z.d 2 with h | h
        · omega
        · have := py.2 h; omega
    have point : ∀ v, v < 19 → f v * genBitlen 7 b v ≤ f v * ref v := by
      intro v hv
      by_cases hf : f v = 0
      · simp [hf]
      · apply Nat.mul_le_mul_left
        obtain ⟨i, hi, _, _⟩ := posOf_spec d0 srt (f v, v) nd (comp v hv hf)
        obtain ⟨z, hz, _, _, hd⟩ := match_ _ (comp v hv hf)
        rw [gb v]; simp only at hi; rw [hi]; simp only [ov0, ite_true]
        simp only at hd
        rw [hd, d1 z hz]
        have := bound v hv (used v hv hf)
        omega
    have := mass_mono point
    omega
  -- at least three leaves: no forced leaf
  have gen : ∀ e ∈ srt, e.1 = f e.2 ∧ f e.2 ≠ 0 := genuine (by omega)
  let N := srt.length
  have keys : ∀ v ∈ srt.map Prod.snd, v < 19 := by
    intro v hv; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv; exact (ok e he).1
  have srtMass : ∀ g : Nat → Nat, (srt.map fun e => e.1 * g e.2).sum ≤ mass (fun v => f v * g v) 19 := by
    intro g
    have h := list_le_mass (fun v => f v * g v) 19 (srt.map Prod.snd) nd keys
    rw [List.map_map] at h
    refine Nat.le_trans (Nat.le_of_eq ?_) h
    congr 1
    apply List.map_congr_left
    intro e he
    simp [(gen e he).1]
  have massSrt : mass f 19 ≤ (srt.map Prod.fst).sum := by
    have h := mass_le_list f 19 (srt.map Prod.snd) (fun v hv hne =>
      List.mem_map.mpr ⟨_, comp v hv hne, rfl⟩)
    rw [List.map_map] at h
    refine Nat.le_trans h (Nat.le_of_eq ?_)
    congr 1
    apply List.map_congr_left
    intro e he
    simp [(gen e he).1]
  have hW : T.weight = mass f 19 := by
    have e1 : T.weight = (srt.map Prod.fst).sum := by
      rw [weight_eq_sum]
      have := perm_sum (pairs.map Prod.snd)
      simp only [leafPairs, List.map_map] at this
      have e2 : (List.map (Prod.snd ∘ fun e : Nat × Nat => (e.2, e.1)) srt) = srt.map Prod.fst := by
        simp [Function.comp_def]
      have e3 : (List.map (Prod.snd ∘ fun x : LeafInfo => (x.sym, x.w)) T.leaves) = T.leaves.map (·.w) := by
        simp [Function.comp_def]
      rw [e2, e3] at this
      exact this
    have le1 := list_le_mass f 19 (srt.map Prod.snd) nd keys
    rw [List.map_map] at le1
    have e4 : (srt.map (f ∘ Prod.snd)).sum = (srt.map Prod.fst).sum := by
      congr 1; apply List.map_congr_left; intro e he; simp [(gen e he).1]
    omega
  have hNmax : N ≤ Nmax := by
    have h := list_le_mass (fun v => if allowed v then 1 else 0) 19 (srt.map Prod.snd) nd keys
    rw [List.map_map] at h
    have e1 : (srt.map ((fun v => if allowed v then 1 else 0) ∘ Prod.snd)).sum = (srt.map fun _ => 1).sum := by
      congr 1
      apply List.map_congr_left
      intro e he
      have := used e.2 (ok e he).1 (gen e he).2
      simp [this]
    have e2 : (srt.map fun _ => (1 : Nat)).sum = N := sum_ones srt
    omega
  -- the reference side
  have opt := huffman_opt (srt.map fun e => (e.2, e.1)) merges
    (by simpa [List.map_map, Function.comp_def] using nd) K ref
    (by
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      exact (bound e.2 (ok e he).1 (used e.2 (ok e he).1 (gen e he).2)).2)
    (by
      have h := list_le_mass (fun v => if allowed v then 2 ^ (K - ref v) else 0) 19 (srt.map Prod.snd) nd keys
      simp only [List.map_map] at h ⊢
      refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans h kraft)
      congr 1
      apply List.map_congr_left
      intro e he
      have := used e.2 (ok e he).1 (gen e he).2
      simp [this])
  simp only [List.map_map] at opt
  have refSide : ext T ≤ mass (fun v => f v * ref v) 19 := by
    refine Nat.le_trans opt (Nat.le_trans (Nat.le_of_eq ?_) (srtMass ref))
    congr 1
  have extEq : ext T = (srt.map fun e => e.1 * depthIn T e.2).sum := by
    rw [transfer (fun w d => w * d)]; rfl
  -- ranks
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
  have hfib : ∀ y, 1 ≤ y → y ≤ N → wR y * fib (δR y + 1) + fib (δR y) ≤ T.weight := by
    intro y h1 h2; obtain ⟨x, hx, hwx, hd⟩ := leafOf y h1 h2
    rw [← hwx, hd]; exact fibT x hx
  have rankSum : ∀ g : Nat × Nat → Nat, (srt.map g).sum = sumR (fun r => g (e r)) N := by
    intro g; exact (sumR_getD g d0 srt).symm
  have hist : ∀ j, blCount 7 srt T j = histL 7 δR N j := by
    intro j
    unfold blCount histL countR
    rw [length_filter_sum, ← sumR_getD _ d0 srt]
  have posR : ∀ r, 1 ≤ r → r ≤ N → posOf (e r).2 srt = some (N - r) := by
    intro r h1 h2
    obtain ⟨i, hi, hil, hg⟩ := posOf_spec d0 srt (e r) nd (eMem r h1 h2)
    have := getD_inj d0 srt i (N - r) nd hil (by omega) hg
    rw [hi, this]
  have depthSum : (srt.map fun e => e.1 * depthIn T e.2).sum = sumR (fun r => wR r * δR r) N :=
    rankSum (fun e => e.1 * depthIn T e.2)
  have lenSum : (srt.map fun e => e.1 * genBitlen 7 b e.2).sum = sumR (fun r => wR r * genBitlen 7 b (e r).2) N :=
    rankSum (fun e => e.1 * genBitlen 7 b e.2)
  by_cases ov : overflowCount 7 T = 0
  · have each : ∀ r, 1 ≤ r → r ≤ N → wR r * genBitlen 7 b (e r).2 ≤ wR r * δR r := by
      intro r h1 h2
      apply Nat.mul_le_mul_left
      rw [gb, posR r h1 h2]; simp only [ov, ite_true]
      exact Nat.min_le_left _ _
    have := sumR_le N each
    omega
  · let M := overflowCount 7 T / 2
    have hM : 1 ≤ M := by simp only [M]; omega
    have each : ∀ r, 1 ≤ r → r ≤ N → wR r * genBitlen 7 b (e r).2 ≤
        wR r * lenOfRank 15 (repairIter 7 M (histL 7 δR N)) r := by
      intro r h1 h2
      apply Nat.mul_le_mul_left
      rw [gb, posR r h1 h2]; simp only [ov, ite_false]
      rw [show (overflowCount 7 T + 1) / 2 = M by simp only [M]; omega, show blCount 7 srt T = histL 7 δR N from
        funext hist, show N - (N - r) = r by omega]
      exact lenOfRank_7_le _ r
    have s1 := sumR_le N each
    have s2 := repair_cost_le 7 (by omega) (by omega) wR δR N M hw
    -- the shape of the first-pass histogram
    have hdeg : ∀ r, 1 ≤ r → r ≤ N → (min (δR r) 7 == 0) = false := by
      intro r h1 h2; have := hδ r h1 h2; simp; omega
    have kr : sumR (fun r => 2 ^ (7 - min (δR r) 7)) N = 128 + M := by
      have e1 : sumR (fun r => 2 ^ (7 - min (δR r) 7)) N = (srt.map fun e => 2 ^ (7 - min (depthIn T e.2) 7)).sum :=
        (rankSum (fun e => 2 ^ (7 - min (depthIn T e.2) 7))).symm
      rw [e1, transfer (fun _ d => 2 ^ (7 - min d 7))]
      simp only [M]
      omega
    have top : M + 1 ≤ histL 7 δR N 7 := by
      have hd := deep_leaves 7 T ov
      have e1 : histL 7 δR N 7 = (srt.map fun e => if min (depthIn T e.2) 7 == 7 then 1 else 0).sum := by
        unfold histL countR; rw [← sumR_getD _ d0 srt]
      have e2 : (T.leaves.filter fun x => decide (7 ≤ x.d)).length =
          (T.leaves.map fun x => if min x.d 7 == 7 then 1 else 0).sum := by
        rw [length_filter_sum]; congr 1; apply List.map_congr_left; intro x _
        by_cases h : 7 ≤ x.d
        · simp [h, show min x.d 7 = 7 by omega]
        · simp [h, show min x.d 7 = x.d by omega]; omega
      rw [e1, transfer (fun _ d => if min d 7 == 7 then 1 else 0)]
      simp only [M]
      omega
    have shape : RepairShape (histL 7 δR N) N M := by
      have zero : histL 7 δR N 0 = 0 := countR_none _ _ hdeg
      have cum := cumC_hist (fun r => min (δR r) 7) N 7
      have all : countR (fun r => decide (min (δR r) 7 ≤ 7)) N = N :=
        countR_all _ _ fun r _ _ => by simp [Nat.min_le_right]
      have ws := wsum_hist (fun i => 2 ^ (7 - i)) (fun r => min (δR r) 7) N 7
      have wsEq : sumR (fun r => if min (δR r) 7 ≤ 7 then 2 ^ (7 - min (δR r) 7) else 0) N =
          sumR (fun r => 2 ^ (7 - min (δR r) 7)) N := sumR_congr N fun r _ _ => by
        rw [ite_eq_left (Nat.min_le_right _ _)]
      rw [wsEq, kr] at ws
      rw [all] at cum
      simp only [cumC, Nat.reduceAdd] at cum
      simp only [wsum, Nat.reduceAdd] at ws
      refine ⟨zero, ?_, ?_, ?_, top⟩
      · intro j hj
        exact countR_none _ _ fun r _ _ => by simp; omega
      · unfold histL at zero top ⊢; omega
      · unfold histL at zero top ⊢; simp only [Nat.reducePow, Nat.reduceSub] at ws; omega
    have caps := rank_cap 7 N T.weight wR δR hw hfib
    have hcap := cap (histL 7 δR N) wR T.weight N M shape hNmax hM caps (by omega)
    rw [hW] at hcap
    omega

/-- **At most 15 allowed symbols**: the repair adds at most 245. -/
theorem bl_cost_le_15 (f : Nat → Nat) (allowed : Nat → Bool) (K : Nat) (ref : Nat → Nat)
    (used : ∀ v, v < 19 → f v ≠ 0 → allowed v = true)
    (bound : ∀ v, v < 19 → allowed v = true → 1 ≤ ref v ∧ ref v ≤ K)
    (kraft : mass (fun v => if allowed v then 2 ^ (K - ref v) else 0) 19 ≤ 2 ^ K)
    (count : mass (fun v => if allowed v then 1 else 0) 19 ≤ 15)
    (weight : mass f 19 ≤ 316) :
    mass (fun v => f v * treeLengths 19 7 f v) 19 ≤ mass (fun v => f v * ref v) 19 + 245 :=
  bl_cost_le f allowed K ref 15 (fun _ => 245) used bound kraft count weight
    fun c w W N M shape hN hM caps hW => repairExtra_cap15 c w W N M shape hN hM caps hW

/-- **At most 13 allowed symbols**: the repair adds at most `29 + W / 2`. -/
theorem bl_cost_le_13 (f : Nat → Nat) (allowed : Nat → Bool) (K : Nat) (ref : Nat → Nat)
    (used : ∀ v, v < 19 → f v ≠ 0 → allowed v = true)
    (bound : ∀ v, v < 19 → allowed v = true → 1 ≤ ref v ∧ ref v ≤ K)
    (kraft : mass (fun v => if allowed v then 2 ^ (K - ref v) else 0) 19 ≤ 2 ^ K)
    (count : mass (fun v => if allowed v then 1 else 0) 19 ≤ 13)
    (weight : mass f 19 ≤ 316) :
    mass (fun v => f v * treeLengths 19 7 f v) 19 ≤ mass (fun v => f v * ref v) 19 + (29 + mass f 19 / 2) :=
  bl_cost_le f allowed K ref 13 (fun W => 29 + W / 2) used bound kraft count weight
    fun c w W N M shape hN hM caps hW => repairExtra_cap13 c w W N M shape hN hM caps hW

end ZlibNgF.Math.Huff
