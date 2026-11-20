import ZlibNgF.Math.HuffRank
import ZlibNgF.Math.HuffKraft
import ZlibNgF.Math.TreesLabeled

/-!
# The overflow repair and the length re-assignment of `gen_bitlen` for any `max_length` (heap-free)

`HuffRank` states `lenOfRank` for `max_length = 15` only; the bit-length tree uses 7. This file has

* `lenOfRank_eqL`: the characterization of `lenOfRank L` for any `L`;
* `RInv`: what holds of the counts `c` (`bl_count`) while the repair loop has `m` moves left: `c 0 = 0`, the total
  is the number of leaves `N`, the clamped Kraft sum is `2^L + m`, `c L ≥ m + 1`, nothing above `L`. With
  `N ≤ 2^L`, a move is possible (`rstep`: some level `1 .. L - 1` is nonempty, so the scan `while (bl_count[bits] ==
  0) bits--` stops at `deepest c (L - 1) ≥ 1`), its decrements do not wrap, and it keeps `RInv` with `m - 1`;
* `init_inv`: the counts of the clamped depths of a tree with an overflow satisfy `RInv` with `m = overflow / 2`
  (from the clamped Kraft equality `kraft_overflow` and `deep_leaves`).
-/

set_option autoImplicit false

noncomputable section

namespace ZlibNgF.Math.TreesRank
open ZlibNgF.Math.Huff

/-! ## `lenOfRank` for any maximum length -/

theorem lenOfRank_leL (L : Nat) (c : Nat → Nat) (r : Nat) : lenOfRank L c r ≤ L := by
  have := (lenSearch_spec c r L 0).2.1; simpa [lenOfRank] using this

/-- **Characterization of `lenOfRank L`.** -/
theorem lenOfRank_eqL (L : Nat) (c : Nat → Nat) (r ℓ : Nat) (hℓ : ℓ ≤ L) (hb : ∀ j, j < ℓ → cumC c j < r)
    (hf : r ≤ cumC c ℓ) : lenOfRank L c r = ℓ := by
  unfold lenOfRank
  obtain ⟨_, _, h3, h4⟩ := lenSearch_spec c r L 0
  simp only [Nat.zero_add] at h4
  have hfound := h4 (Nat.le_trans hf (cumC_mono c hℓ))
  refine Nat.le_antisymm (Nat.le_of_not_lt fun hlt => ?_) (Nat.le_of_not_lt fun hlt => ?_)
  · have := h3 ℓ (Nat.zero_le _) hlt; omega
  · have := hb _ hlt; omega

/-! ## Weighted sums under point updates -/

theorem wsum_upd (wt c : Nat → Nat) (a v : Nat) :
    ∀ n, a ≤ n → wsum wt (updC c a v) n + c a * wt a = wsum wt c n + v * wt a
  | 0, h => by
    have : a = 0 := by omega
    subst this; simp only [wsum, updC, ↓reduceIte]; omega
  | n + 1, h => by
    rcases Nat.lt_or_ge a (n + 1) with h' | h'
    · have ih := wsum_upd wt c a v n (by omega)
      simp only [wsum, updC, show ¬ (n + 1 = a) by omega, ↓reduceIte] at ih ⊢
      omega
    · have : a = n + 1 := by omega
      subst this
      have hc : wsum wt (updC c (n + 1) v) n = wsum wt c n :=
        wsum_congr n (fun i hi => by simp only [updC, show ¬ (i = n + 1) by omega, ↓reduceIte])
      simp only [wsum, hc]
      simp only [updC, ↓reduceIte]
      omega

theorem wsum_upd_gt (wt c : Nat → Nat) (a v n : Nat) (h : n < a) : wsum wt (updC c a v) n = wsum wt c n :=
  wsum_congr n (fun i hi => by simp only [updC, show ¬ (i = a) by omega, ↓reduceIte])

theorem wsum_zero_of (wt c : Nat → Nat) : ∀ n, (∀ i, i ≤ n → c i = 0) → wsum wt c n = 0
  | 0, h => by simp [wsum, h 0 (Nat.le_refl _)]
  | n + 1, h => by
    simp only [wsum, h (n + 1) (Nat.le_refl _), Nat.zero_mul, Nat.add_zero]
    exact wsum_zero_of wt c n (fun i hi => h i (by omega))

theorem le_cumC (c : Nat → Nat) : ∀ n j, j ≤ n → c j ≤ cumC c n
  | 0, j, h => by have : j = 0 := by omega
                  subst this; simp [cumC]
  | n + 1, j, h => by
    simp only [cumC]
    rcases Nat.lt_or_ge j (n + 1) with h' | h'
    · have := le_cumC c n j (by omega); omega
    · have : j = n + 1 := by omega
      subst this; omega

/-! ## The scan for a nonempty level -/

theorem deepest_spec (c : Nat → Nat) : ∀ n, (∃ j, 1 ≤ j ∧ j ≤ n ∧ c j ≠ 0) →
    1 ≤ deepest c n ∧ deepest c n ≤ n ∧ c (deepest c n) ≠ 0 ∧ ∀ j, deepest c n < j → j ≤ n → c j = 0
  | 0, ⟨j, h1, h2, _⟩ => by omega
  | n + 1, h => by
    simp only [deepest]
    by_cases hc : c (n + 1) ≠ 0
    · rw [show (if c (n + 1) ≠ 0 then n + 1 else deepest c n) = n + 1 by simp [hc]]
      exact ⟨by omega, Nat.le_refl _, hc, fun j h1 h2 => by omega⟩
    · simp only [hc, ↓reduceIte]
      have h' : ∃ j, 1 ≤ j ∧ j ≤ n ∧ c j ≠ 0 := by
        obtain ⟨j, h1, h2, h3⟩ := h
        refine ⟨j, h1, ?_, h3⟩
        refine Nat.le_of_not_lt fun hlt => ?_
        have : j = n + 1 := by omega
        subst this; exact hc h3
      obtain ⟨a1, a2, a3, a4⟩ := deepest_spec c n h'
      refine ⟨a1, by omega, a3, fun j h1 h2 => ?_⟩
      by_cases hj : j = n + 1
      · subst hj; exact Decidable.not_not.mp hc
      · exact a4 j h1 (by omega)

/-! ## The repair loop -/

/-- The counts `c` while the repair loop has `m` moves left (`N` leaves, `max_length = L`). -/
structure RInv (L N m : Nat) (c : Nat → Nat) : Prop where
  z : c 0 = 0
  hi : ∀ j, L < j → c j = 0
  tot : cumC c L = N
  kr : wsum (fun i => 2 ^ (L - i)) c L = 2 ^ L + m
  top : m + 1 ≤ c L

theorem two_pow_pred (L b : Nat) (h : b + 1 ≤ L) : 2 ^ (L - b) = 2 * 2 ^ (L - (b + 1)) := by
  rw [show L - b = (L - (b + 1)) + 1 by omega, Nat.pow_succ]; omega

/-- **One move of the repair loop.** The scan stops at `b = deepest c (L - 1)`, with `1 ≤ b ≤ L - 1`, `c b ≠ 0` and
the levels `b + 1 .. L - 1` empty; `c L ≥ 2`; the move keeps the invariant with one move less. -/
theorem rstep (L N m : Nat) (c : Nat → Nat) (hN : N ≤ 2 ^ L) (h : RInv L N (m + 1) c) :
    1 ≤ deepest c (L - 1) ∧ deepest c (L - 1) ≤ L - 1 ∧ c (deepest c (L - 1)) ≠ 0 ∧
      (∀ j, deepest c (L - 1) < j → j ≤ L - 1 → c j = 0) ∧ 2 ≤ c L ∧ RInv L N m (repairStep L c) := by
  have hex : ∃ j, 1 ≤ j ∧ j ≤ L - 1 ∧ c j ≠ 0 := by
    refine Classical.byContradiction fun hne => ?_
    have hz : ∀ j, j < L → c j = 0 := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; exact h.z
      · exact Classical.byContradiction fun hc => hne ⟨j, h0, by omega, hc⟩
    have hL : 1 ≤ L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · have k := h.kr; have z := h.z; subst h0
        simp only [wsum, Nat.sub_self, Nat.pow_zero, Nat.mul_one, z] at k; omega
      · exact h0
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have t := h.tot
    have k := h.kr
    simp only [cumC] at t
    simp only [wsum, Nat.sub_self, Nat.pow_zero, Nat.mul_one] at k
    rw [cumC_eq_wsum c L', wsum_zero_of (fun _ => 1) c L' (fun i hi => hz i (by omega))] at t
    rw [wsum_zero_of _ c L' (fun i hi => hz i (by omega))] at k
    omega
  obtain ⟨b1, b2, b3, b4⟩ := deepest_spec c (L - 1) hex
  refine ⟨b1, b2, b3, b4, by have := h.top; omega, ?_⟩
  generalize hb : deepest c (L - 1) = b at b1 b2 b3 b4
  have hL : b + 1 ≤ L := by omega
  have top := h.top
  have tot := h.tot
  have kr := h.kr
  have z := h.z
  have hi := h.hi
  -- the three updates
  have e1 : repairStep L c = updC (updC (updC c b (c b - 1)) (b + 1) (updC c b (c b - 1) (b + 1) + 2)) L
      (updC (updC c b (c b - 1)) (b + 1) (updC c b (c b - 1) (b + 1) + 2) L - 1) := by
    simp only [repairStep, hb]
  rw [e1]
  generalize hc1 : updC c b (c b - 1) = c1
  generalize hc2 : updC c1 (b + 1) (c1 (b + 1) + 2) = c2
  have c1b1 : c1 (b + 1) = c (b + 1) := by rw [← hc1]; simp only [updC, show ¬ (b + 1 = b) by omega, ↓reduceIte]
  have c1L : c1 L = c L := by rw [← hc1]; simp only [updC, show ¬ (L = b) by omega, ↓reduceIte]
  have c2L : c2 L = if L = b + 1 then c (b + 1) + 2 else c L := by
    rw [← hc2]; simp only [updC]; split <;> simp_all
  have c2Lpos : 1 ≤ c2 L := by rw [c2L]; split <;> omega
  -- sums
  have s1 := wsum_upd (fun _ => 1) c b (c b - 1) L (by omega)
  have s2 := wsum_upd (fun _ => 1) c1 (b + 1) (c1 (b + 1) + 2) L hL
  have s3 := wsum_upd (fun _ => 1) c2 L (c2 L - 1) L (Nat.le_refl _)
  rw [hc1] at s1
  rw [hc2] at s2
  have w1 := wsum_upd (fun i => 2 ^ (L - i)) c b (c b - 1) L (by omega)
  have w2 := wsum_upd (fun i => 2 ^ (L - i)) c1 (b + 1) (c1 (b + 1) + 2) L hL
  have w3 := wsum_upd (fun i => 2 ^ (L - i)) c2 L (c2 L - 1) L (Nat.le_refl _)
  rw [hc1] at w1
  rw [hc2] at w2
  simp only [Nat.mul_one, Nat.sub_self, Nat.pow_zero] at s1 s2 s3 w3
  have hp := two_pow_pred L b hL
  generalize 2 ^ (L - (b + 1)) = W at hp w2
  rw [hp] at w1
  have m1 : (c b - 1) * (2 * W) + 2 * W = c b * (2 * W) := by
    rw [← Nat.succ_mul]; congr 1; omega
  have m2 : (c1 (b + 1) + 2) * W = c1 (b + 1) * W + 2 * W := by rw [Nat.add_mul]
  rw [cumC_eq_wsum] at tot
  refine ⟨?_, fun j hj => ?_, ?_, ?_, ?_⟩
  · simp only [updC, show ¬ ((0 : Nat) = L) by omega, ↓reduceIte]
    rw [← hc2]; simp only [updC, show ¬ ((0 : Nat) = b + 1) by omega, ↓reduceIte]
    rw [← hc1]; simp only [updC, show ¬ ((0 : Nat) = b) by omega, ↓reduceIte]; exact z
  · simp only [updC, show ¬ (j = L) by omega, ↓reduceIte]
    rw [← hc2]; simp only [updC, show ¬ (j = b + 1) by omega, ↓reduceIte]
    rw [← hc1]; simp only [updC, show ¬ (j = b) by omega, ↓reduceIte]; exact hi j hj
  · rw [cumC_eq_wsum]; omega
  · omega
  · simp only [updC, ↓reduceIte]
    rw [c2L]; split <;> (try subst_vars) <;> omega

/-- `M` moves keep the invariant down to no move left. -/
theorem riter_inv (L N : Nat) (hN : N ≤ 2 ^ L) : ∀ (M : Nat) (c : Nat → Nat), RInv L N M c → RInv L N 0 (repairIter L M c)
  | 0, _, h => h
  | M + 1, c, h => riter_inv L N hN M (repairStep L c) (rstep L N M c hN h).2.2.2.2.2

theorem repairIter_succ' (L k : Nat) (c : Nat → Nat) : repairIter L (k + 1) c = repairStep L (repairIter L k c) := by
  rw [repairIter_add]; rfl

/-- The leaf of rank `r` with `cumC c (B - 1) < r ≤ cumC c B` gets length `B`. -/
theorem lenOfRank_band (L : Nat) (c : Nat → Nat) (B r : Nat) (hB : 1 ≤ B) (hBL : B ≤ L) (h1 : cumC c (B - 1) < r)
    (h2 : r ≤ cumC c B) : lenOfRank L c r = B :=
  lenOfRank_eqL L c r B hBL (fun j hj => Nat.lt_of_le_of_lt (cumC_mono c (by omega)) h1) h2

theorem cumC_pred (c : Nat → Nat) (B : Nat) (hB : 1 ≤ B) : cumC c B = cumC c (B - 1) + c B := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  rfl


/-! ## Counts of a list of lengths -/

/-- The number of entries `j` of `l`. -/
def cntOf (l : List Nat) (j : Nat) : Nat := l.countP (· == j)

theorem cntOf_cons (x : Nat) (l : List Nat) : cntOf (x :: l) = updC (cntOf l) x (cntOf l x + 1) := by
  funext j
  simp only [cntOf, List.countP_cons, updC]
  by_cases h : j = x
  · subst h; simp
  · simp only [h, ↓reduceIte, beq_iff_eq, show ¬ (x = j) from fun e => h e.symm,
      Nat.add_zero]

theorem cntOf_sums (L : Nat) (wt : Nat → Nat) :
    ∀ l : List Nat, (∀ x ∈ l, x ≤ L) → wsum wt (cntOf l) L = (l.map wt).sum
  | [], _ => wsum_zero_of wt _ L (fun i _ => by simp [cntOf])
  | x :: l, h => by
    rw [cntOf_cons]
    have ih := cntOf_sums L wt l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := wsum_upd wt (cntOf l) x (cntOf l x + 1) L (h x (by simp))
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [List.map_cons, List.sum_cons]
    omega

theorem cntOf_hi (L : Nat) (l : List Nat) (h : ∀ x ∈ l, x ≤ L) (j : Nat) (hj : L < j) : cntOf l j = 0 := by
  simp only [cntOf, List.countP_eq_zero, beq_iff_eq]
  intro x hx e; have := h x hx; omega

/-! ## The counts of the clamped depths of a tree -/

theorem find_self {l : List LeafInfo} (nd : (l.map (·.sym)).Nodup) {x : LeafInfo} (hx : x ∈ l) :
    l.find? (fun y => y.sym == x.sym) = some x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nd
    rw [List.find?_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp
    · have hne : y.sym ≠ x.sym := fun e => nd.1 ⟨x, hx', e.symm⟩
      have hb : (y.sym == x.sym) = false := by simp [hne]
      simp only [hb]
      exact ih nd.2 hx'

theorem depthIn_leaf {T : HTree} (nd : (T.leaves.map (·.sym)).Nodup) {x : LeafInfo} (hx : x ∈ T.leaves) :
    depthIn T x.sym = x.d := by
  unfold depthIn; rw [find_self nd hx]

theorem leaves_ne : ∀ t : HTree, t.leaves ≠ []
  | .leaf _ _ => by simp [HTree.leaves]
  | .node a _ => by simp [HTree.leaves, leaves_ne a]

/-- The clamped depths of the leaves in `srt` order are a permutation of those in tree order. -/
theorem clamped_perm (L : Nat) (srt : List (Nat × Nat)) (T : HTree) (nd : (T.leaves.map (·.sym)).Nodup)
    (hp : (T.leaves.map (·.sym)).Perm (srt.map Prod.snd)) :
    (srt.map fun e => min (depthIn T e.2) L).Perm (T.leaves.map fun x => min x.d L) := by
  have e1 : T.leaves.map (fun x => min x.d L) = (T.leaves.map (·.sym)).map (fun v => min (depthIn T v) L) := by
    rw [List.map_map]
    exact List.map_congr_left (fun x hx => by simp [depthIn_leaf nd hx])
  have e2 : srt.map (fun e => min (depthIn T e.2) L) = (srt.map Prod.snd).map (fun v => min (depthIn T v) L) := by
    rw [List.map_map]; rfl
  rw [e1, e2]
  exact (hp.map _).symm

theorem blCount_eq (L : Nat) (srt : List (Nat × Nat)) (T : HTree) :
    blCount L srt T = cntOf (srt.map fun e => min (depthIn T e.2) L) := by
  funext j
  simp only [blCount, cntOf, List.countP_map, ← List.countP_eq_length_filter]
  rfl

/-- **The counts after the first pass satisfy the repair invariant** with `m = overflow / 2`. -/
theorem sum_ones : ∀ l : List Nat, (l.map fun _ => 1).sum = l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_ones l, List.length_cons]; omega

theorem init_inv (L : Nat) (hL : 1 ≤ L) (srt : List (Nat × Nat)) (T : HTree) (nd : (T.leaves.map (·.sym)).Nodup)
    (hp : (T.leaves.map (·.sym)).Perm (srt.map Prod.snd)) (hpos : ∀ x ∈ T.leaves, 1 ≤ x.d)
    (hov : overflowCount L T ≠ 0) :
    RInv L srt.length (overflowCount L T / 2) (blCount L srt T) := by
  have pm := clamped_perm L srt T nd hp
  rw [blCount_eq]
  generalize hl : srt.map (fun e => min (depthIn T e.2) L) = l at pm
  have hle : ∀ x ∈ l, x ≤ L := by
    intro x hx; rw [← hl] at hx; obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx; omega
  have hlen : l.length = srt.length := by rw [← hl, List.length_map]
  have kr := kraft_overflow L T
  have dp := deep_leaves L T hov
  have ev := overflow_even L T
  refine ⟨?_, cntOf_hi L l hle, ?_, ?_, ?_⟩
  · simp only [cntOf, pm.countP_eq, List.countP_eq_zero, List.mem_map, beq_iff_eq]
    rintro _ ⟨x, hx, rfl⟩; have := hpos x hx; omega
  · rw [cumC_eq_wsum, cntOf_sums L _ l hle, sum_ones, hlen]
  · rw [cntOf_sums L _ l hle, perm_sum (pm.map _), List.map_map]
    have : (T.leaves.map ((fun x => 2 ^ (L - x)) ∘ fun x => min x.d L)) =
        T.leaves.map (fun x => 2 ^ (L - min x.d L)) := rfl
    rw [this]; omega
  · have e : cntOf l L = (T.leaves.filter fun x => decide (L ≤ x.d)).length := by
      simp only [cntOf, pm.countP_eq, List.countP_map, ← List.countP_eq_length_filter]
      exact List.countP_congr (fun x _ => by simp only [Function.comp, beq_iff_eq, decide_eq_true_eq]; omega)
    rw [e]; omega

/-- The leaves of a node are below its root. -/
theorem leaves_pos (a c : HTree) : ∀ x ∈ (HTree.node a c).leaves, 1 ≤ x.d := by
  intro x hx
  simp only [HTree.leaves, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx; show 1 ≤ y.d + 1; omega

end ZlibNgF.Math.TreesRank

end
