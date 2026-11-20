import ZlibNgF.Math.OverlayDynamic

noncomputable section

/-!
# The dynamic-block overlay budget at `lit_bufsize = 512` (heap-free)

Re-proved from the sibling project (`ZlibF.Math.DeflateOverlaySmall`, `DeflateOverlayFibActual`).

* `fib_plus_15`: a literal/length or distance tree of weight `W < 2584` has no node below depth 15, so
  `gen_bitlen` keeps every depth, and every used symbol of frequency `f` and length `l` satisfies the unclamped
  Fibonacci bound `f * F(l + 1) + F(l) ≤ W` (`fibPlus_of_merges`).
* `symbol_excess_le_mass`: the block excess is at most the per-occurrence excess of the length codes over 9 bits
  and of the distance codes over 15 bits (a literal never exceeds the 24 bits it frees).
* `length_cap514`, `distance_cap514`: for a weight at most 514 one code with `e` extra bits contributes at most a
  constant to the excess, whatever its frequency; the constants sum to `749 + 1028 = 1777`.

`dynamic_budget_512`: with at most 511 symbols both trees weigh at most 514, so the excess is at most 1777 bits,
and with the header bound of 2283 bits the budget `8 * 512 + 7` holds for every block (no block-choice fact is
needed).
-/

namespace ZlibNgF.Math.OverlayDynamic
open ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
open ZlibNgF.Math.TreesOverlay
set_option autoImplicit false

/-- A used symbol is a leaf of the built tree with its own frequency, and keeps its Fibonacci bound. -/
theorem used_leaf {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems) (v : Nat) (hv : v < elems)
    (hf : freq v ≠ 0) :
    ∃ x ∈ (buildTree elems freq).root.leaves, x.w = freq v ∧ depthIn (buildTree elems freq).root v = x.d ∧
      x.w * fib (x.d + 1) + fib x.d ≤ (buildTree elems freq).root.weight := by
  generalize hb : buildTree elems freq = b
  obtain ⟨ok, nd, _two, _le, comp, _sum, _sorted, tr, merges⟩ := hb ▸ built_facts (freq := freq) hE
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
  have h : (v, freq v) ∈ leafPairs T := pairs.mem_iff.mpr (List.mem_map.mpr ⟨(freq v, v), comp v hv hf, rfl⟩)
  simp only [leafPairs, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨x, hx, h1, h2⟩ := h
  exact ⟨x, hx, h2, by rw [← h1]; exact depthIn_of_mem ndT hx, fibT x hx⟩

/-- Every leaf of the built tree is a leaf entry (`LeafOK`) of positive weight, with its Fibonacci bound. -/
theorem all_leaves_fib {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems) :
    ∀ x ∈ (buildTree elems freq).root.leaves,
      1 ≤ x.w ∧ x.w * fib (x.d + 1) + fib x.d ≤ (buildTree elems freq).root.weight := by
  generalize hb : buildTree elems freq = b
  obtain ⟨ok, _nd, _two, _le, _comp, _sum, _sorted, tr, merges⟩ := hb ▸ built_facts (freq := freq) hE
  generalize hsrt : b.sorted = srt at *
  generalize hT : b.root = T at *
  have pairs : (leafPairs T).Perm (srt.map fun e => (e.2, e.1)) := by
    have h := merges.pairs
    rw [flatMap_initForest] at h; exact h.symm
  have fibT := fibPlus_of_merges merges (by
    intro p hp; simp only [List.mem_map] at hp; obtain ⟨e, he, rfl⟩ := hp; exact (ok e he).2.1)
  intro x hx
  refine ⟨?_, fibT x hx⟩
  have h := pairs.mem_iff.mp (by unfold leafPairs; exact List.mem_map.mpr ⟨x, hx, rfl⟩)
  simp only [List.mem_map, Prod.mk.injEq] at h
  obtain ⟨e, he, _, h2⟩ := h
  have := (ok e he).2.1; omega

/-- A leaf below depth `L` is counted by the overflow. -/
theorem ovfAux_pos (L : Nat) : ∀ (t : HTree) (k : Nat) (x : LeafInfo), x ∈ t.leaves → L < x.d + k →
    1 ≤ ovfAux L k t
  | .leaf s w, k, x, hx, h => by
    simp only [HTree.leaves, List.mem_singleton] at hx; subst hx
    simp only [ovfAux] at h ⊢; simp only [Nat.zero_add] at h; simp [h]
  | .node a b, k, x, hx, h => by
    simp only [HTree.leaves, List.mem_map, List.mem_append] at hx
    obtain ⟨y, hy | hy, rfl⟩ := hx
    · have := ovfAux_pos L a (k + 1) y hy (by simp only at h; omega)
      simp only [ovfAux]; omega
    · have := ovfAux_pos L b (k + 1) y hy (by simp only at h; omega)
      simp only [ovfAux]; omega

/-- A tree of weight below `2584 = F(17) + F(16)` has no node deeper than 15. -/
theorem no_overflow_15 {elems : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems)
    (hW : (buildTree elems freq).root.weight < 2584) : overflowCount 15 (buildTree elems freq).root = 0 := by
  apply overflow_zero
  intro x hx
  obtain ⟨w1, hf⟩ := all_leaves_fib hE x hx
  refine Classical.byContradiction fun h => ?_
  have f1 := fib_mono (show 17 ≤ x.d + 1 by omega)
  have f2 := fib_mono (show 16 ≤ x.d by omega)
  have := Nat.mul_le_mul w1 f1
  rw [fib_16_17.1] at f2; rw [fib_16_17.2] at this
  omega

/-- **The unclamped Fibonacci bound of a tree without overflow**: `gen_bitlen` keeps the depth of every used
symbol, so `f * F(l + 1) + F(l) ≤ W`, and `1 ≤ l`. -/
theorem fib_plus_of_no_overflow {elems L : Nat} {freq : Nat → Nat} (hE : 3 ≤ elems)
    (hO : overflowCount L (buildTree elems freq).root = 0) (v : Nat) (hv : v < elems) (hf : freq v ≠ 0) :
    genBitlen L (buildTree elems freq) v = depthIn (buildTree elems freq).root v ∧
    freq v * fib (genBitlen L (buildTree elems freq) v + 1) + fib (genBitlen L (buildTree elems freq) v) ≤
      (buildTree elems freq).root.weight := by
  obtain ⟨x, hx, hw, hd, hfib⟩ := used_leaf hE v hv hf
  obtain ⟨ok, nd, _two, _le, comp, _⟩ := built_facts (freq := freq) hE
  obtain ⟨i, hi, _, _⟩ := posOf_spec (0, 0) _ (freq v, v) nd (comp v hv hf)
  have deep : x.d ≤ L := by
    refine Classical.byContradiction fun h => ?_
    have z := ovfAux_pos L (buildTree elems freq).root 0 x hx (by omega)
    unfold overflowCount at hO; omega
  have gl : genBitlen L (buildTree elems freq) v = x.d := by
    unfold genBitlen
    simp only at hi
    rw [hi]
    simp only [hO, ite_true, hd]
    omega
  refine ⟨by rw [gl, hd], ?_⟩
  rw [gl, ← hw]; exact hfib

/-! ## The excess at the actual lengths -/

/-- **The block excess is at most the per-occurrence excess** of the length codes and distance codes. -/
theorem symbol_excess_le_mass (xs : List Symbol)
    (literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode : Nat → Nat)
    (valid : ∀ s ∈ xs, s.Valid)
    (literalKeys : ∀ s ∈ xs, s.literalKey lengthCode < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey distanceCode = some k → k < 30)
    (literalLengths : ∀ v, v < 286 → literalFrequency lengthCode xs v ≠ 0 → literalLength v ≤ 15) :
    bitExcess (xs.map (symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode)) ≤
      mass (fun v => literalFrequency lengthCode xs v * literalExcess literalLength literalExtra v) 286 +
        mass (fun v => distanceFrequency distanceCode xs v * distanceExcess distanceLength distanceExtra v) 30 := by
  let GL := literalExcess literalLength literalExtra
  let GD := distanceExcess distanceLength distanceExtra
  let DC := fun s : Symbol => match s.distanceKey distanceCode with | none => 0 | some k => GD k
  have literalCosts : mass (fun v => literalFrequency lengthCode xs v * GL v) 286 =
      (xs.map (fun s => GL (s.literalKey lengthCode))).sum := by
    have point : mass (fun v => literalFrequency lengthCode xs v * GL v) 286 =
        mass (fun v => countKey (fun s => some (s.literalKey lengthCode)) xs v * GL v) 286 := by
      apply mass_congr
      intro v _bound
      by_cases endMarker : v = 256
      · subst v
        have zero : GL 256 = 0 := rfl
        simp only [zero, Nat.mul_zero]
      · simp only [literalFrequency, endMarker, ite_false, Nat.zero_add]
    rw [point]
    exact weighted_count_key (Symbol.literalKey lengthCode) 286 GL literalKeys
  have distanceCosts : mass (fun v => distanceFrequency distanceCode xs v * GD v) 30 = (xs.map DC).sum :=
    weighted_optional_key (Symbol.distanceKey distanceCode) 30 GD distanceKeys
  have split : ∀ s ∈ xs,
      symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode s - 24 ≤
        GL (s.literalKey lengthCode) + DC s := by
    intro s member
    have value := (valid s member).2
    by_cases literal : s.distance = 0
    · have key : s.literalKey lengthCode = s.value := by simp only [Symbol.literalKey, literal, ite_true]
      have positive : literalFrequency lengthCode xs s.value ≠ 0 := by
        have count := count_key_positive (fun s => some (s.literalKey lengthCode)) member
          (show some (s.literalKey lengthCode) = some s.value by rw [key])
        unfold literalFrequency
        omega
      have length := literalLengths s.value (by omega) positive
      simp only [symbolCost, literal, ite_true, GL, literalExcess, key,
        show s.value < 257 by omega, DC, Symbol.distanceKey, ite_true, Nat.zero_add]
      omega
    · simp only [symbolCost, literal, ite_false, GL, literalExcess, Symbol.literalKey,
        show ¬ lengthCode s.value + 257 < 257 by omega, DC, Symbol.distanceKey,
        Nat.add_sub_cancel, GD, distanceExcess]
      change literalLength (lengthCode s.value + 257) + literalExtra (lengthCode s.value) +
        distanceLength (distanceCode (s.distance - 1)) + distanceExtra (distanceCode (s.distance - 1)) - 24 ≤
        (literalLength (lengthCode s.value + 257) + literalExtra (lengthCode s.value) - 9) +
        (distanceLength (distanceCode (s.distance - 1)) + distanceExtra (distanceCode (s.distance - 1)) - 15)
      omega
  have summed := list_sum_le_split xs
    (fun s => symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode s - 24)
    (fun s => GL (s.literalKey lengthCode)) DC split
  unfold bitExcess
  rw [List.map_map]
  change (xs.map (fun s => symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode
    distanceCode s - 24)).sum ≤ mass (fun v => literalFrequency lengthCode xs v * GL v) 286 +
      mass (fun v => distanceFrequency distanceCode xs v * GD v) 30
  rw [literalCosts, distanceCosts]
  exact summed

/-! ## Per-code caps for a weight of at most 514 -/

theorem fib_values : fib 0 = 0 ∧ fib 1 = 1 ∧ fib 2 = 1 ∧ fib 3 = 2 ∧ fib 4 = 3 ∧ fib 5 = 5 ∧
    fib 6 = 8 ∧ fib 7 = 13 ∧ fib 8 = 21 ∧ fib 9 = 34 ∧ fib 10 = 55 ∧ fib 11 = 89 ∧ fib 12 = 144 ∧
    fib 13 = 233 ∧ fib 14 = 377 ∧ fib 15 = 610 ∧ fib 16 = 987 ∧ fib 17 = 1597 := by decide

/-- Per-code excess cap of a length code with `e` extra bits, tree weight at most 514. -/
def lengthCap514 : Nat → Nat
  | 0 => 5 | 1 => 10 | 2 => 16 | 3 => 28 | 4 => 46 | _ => 76

/-- Per-code excess cap of a distance code with `e` extra bits, tree weight at most 514. -/
def distanceCap514 : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 5 | 7 => 10 | 8 => 16 | 9 => 28
  | 10 => 46 | 11 => 76 | 12 => 126 | _ => 204

theorem length_cap514 (f l e : Nat) (length : l ≤ 15) (extra : e < 6)
    (weight : f * fib (l + 1) + fib l ≤ 514) : f * (l + e - 9) ≤ lengthCap514 e := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, _⟩ := fib_values
  rcases e with _ | _ | _ | _ | _ | _ | e <;>
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
  simp only [lengthCap514, Nat.reduceAdd, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13,
    f14, f15, f16] at weight ⊢ <;> omega

theorem distance_cap514 (f l e : Nat) (length : l ≤ 15) (extra : e < 14)
    (weight : f * fib (l + 1) + fib l ≤ 514) : f * (l + e - 15) ≤ distanceCap514 e := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, _⟩ := fib_values
  rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | e <;>
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
  simp only [distanceCap514, Nat.reduceAdd, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13,
    f14, f15, f16] at weight ⊢ <;> omega

set_option maxRecDepth 10000 in
theorem cap_sums_514 :
    mass (fun v => if v < 257 then 0 else lengthCap514 (lengthExtra (v - 257))) 286 = 749 ∧
    mass (fun v => distanceCap514 (distanceExtra v)) 30 = 1028 := by decide +kernel

/-- **The excess of a block of at most 511 symbols**: at most `749 + 1028` bits. -/
theorem excess_le_511 (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) (hn : xs.length ≤ 511) :
    bitExcess (blockCosts xs) ≤ 1777 := by
  have literalKeys : ∀ s ∈ xs, s.literalKey lengthCode < 286 := by
    intro s hs
    have := (valid s hs).2
    have := lengthCode_lt s.value
    unfold Symbol.literalKey; split <;> omega
  have distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey distanceCode = some k → k < 30 := by
    intro s _ k hk
    unfold Symbol.distanceKey at hk
    split at hk
    · simp at hk
    · simp only [Option.some.injEq] at hk; rw [← hk]; exact distanceCode_lt _
  have mL : mass (litFreq xs) 286 = xs.length + 1 := literal_frequency_mass lengthCode literalKeys
  have mD : mass (distFreq xs) 30 ≤ xs.length := distance_frequency_mass distanceCode distanceKeys
  have wL := (tree_classes (elems := 286) (freq := litFreq xs) (by omega) (by omega)).1
  have wD := (tree_classes (elems := 30) (freq := distFreq xs) (by omega) (by omega)).1
  have oL := no_overflow_15 (elems := 286) (freq := litFreq xs) (by omega) (by omega)
  have oD := no_overflow_15 (elems := 30) (freq := distFreq xs) (by omega) (by omega)
  have data := table_data
  have base := symbol_excess_le_mass xs (litLens xs) (distLens xs) lengthExtra distanceExtra lengthCode
    distanceCode valid literalKeys distanceKeys (fun v _ _ => litLens_le xs v)
  have bL : mass (fun v => litFreq xs v * literalExcess (litLens xs) lengthExtra v) 286 ≤ 749 := by
    rw [← cap_sums_514.1]
    apply mass_mono
    intro v hv
    by_cases z : litFreq xs v = 0
    · simp [z]
    · by_cases low : v < 257
      · simp [literalExcess, low]
      · have fp := (fib_plus_of_no_overflow (by omega) oL v hv z).2
        have c := length_cap514 (litFreq xs v) (litLens xs v) (lengthExtra (v - 257)) (litLens_le xs v)
          (data.1 ⟨v - 257, by omega⟩) (by unfold litLens treeLengths; omega)
        simpa [literalExcess, low] using c
  have bD : mass (fun v => distFreq xs v * distanceExcess (distLens xs) distanceExtra v) 30 ≤ 1028 := by
    rw [← cap_sums_514.2]
    apply mass_mono
    intro v hv
    by_cases z : distFreq xs v = 0
    · simp [z]
    · have fp := (fib_plus_of_no_overflow (by omega) oD v hv z).2
      exact distance_cap514 (distFreq xs v) (distLens xs v) (distanceExtra v) (distLens_le xs v)
        (data.2.1 ⟨v, hv⟩) (by unfold distLens treeLengths; omega)
  unfold blockCosts
  unfold litFreq at bL
  unfold distFreq at bD
  omega

/-- **The dynamic-block overlay budget for `lit_bufsize = 512`** (`memLevel` 3), for every block. -/
theorem dynamic_budget_512 {b0 : Nat} (xs : List Symbol) (hb0 : b0 ≤ 7) (hn : xs.length + 1 ≤ 512)
    (valid : ∀ s ∈ xs, s.Valid) : Budget 512 (b0 + 3 + blockHeader xs) (blockCosts xs) := by
  have hH := header_bound xs
  have hE := excess_le_511 xs valid (by omega)
  unfold Budget
  omega

end ZlibNgF.Math.OverlayDynamic
