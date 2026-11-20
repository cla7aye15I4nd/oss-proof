import ZlibNgF.Math.OverlaySmall

noncomputable section

/-!
# The block choice of `zng_tr_flush_block` (heap-free)

`zng_tr_flush_block` (trees.c) sends a block with dynamic trees only when

* `s->sym_next != 0` and `s->level > 0` (the trees are built),
* `!(static_lenb <= opt_lenb || s->strategy == Z_FIXED)`, where `opt_lenb = (s->opt_len + 3 + 7) >> 3` and
  `static_lenb = (s->static_len + 3 + 7) >> 3`,
* `!(stored_len + 4 <= opt_lenb && buf != NULL)` and `static_lenb != opt_lenb`.

So a dynamic block always has `opt_lenb < static_lenb` (`Chosen`), whatever `strategy`, `level`, `buf` and
`stored_len` are; the other conditions only remove more blocks.

The two sums at that point, in terms of the model of `OverlayDynamic`:

* `s->opt_len` (`optLen`): `gen_bitlen` adds `f * (bits + xbits)` for every leaf of the literal/length and distance
  trees at its final length (a repaired length replaces its first-pass length; a forced leaf of frequency 1 adds
  its length 1 and `build_tree` subtracts 1, so it adds nothing). That is the cost of every symbol of the block
  under the dynamic trees (`blockCosts`) plus `END_BLOCK` (`litLens xs 256`). `build_bl_tree` then adds the
  bit-length tree's `Σ f * (Len + extra_blbits)` (one term per symbol `scan_tree` counted) and
  `3 * (max_blindex + 1) + 5 + 5 + 4`: that is `blockHeader xs` (`headerBits`).
* `s->static_len` (`staticLen`): the same frequencies at the static lengths (`static_ltree`: 8 for 0..143, 9 for
  144..255, 7 for 256..279, 8 for 280..287; `static_dtree`: 5) with the same extra bits; a forced leaf adds
  `stree[node].Len` and has it subtracted. With `END_BLOCK` (7 bits) that is `Σ staticCost + 7`.

`chosen_bits`: `Chosen` gives `opt_len < static_len` in bits (the rounding of both sums by the same `+ 10 >> 3`
cannot reverse a non-strict order). `choice_row`: the extra bits cancel and the choice reads
`H + Σ f·len_dyn + Σ fd·dlen_dyn + 1 ≤ Σ f·len_static + 5 Σ fd` over the frequencies of the two trees (with
`END_BLOCK` in the literal/length frequencies).
-/

namespace ZlibNgF.Math.OverlayDynamic
open ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
open ZlibNgF.Math.TreesOverlay
set_option autoImplicit false

/-- `static_ltree[v].Len`. -/
def staticLitLen (v : Nat) : Nat := if v < 144 then 8 else if v < 256 then 9 else if v < 280 then 7 else 8

/-- The cost of a symbol under the static trees (`static_dtree[*].Len = 5`). -/
def staticCost (s : Symbol) : Nat :=
  if s.distance = 0 then staticLitLen s.value else
    staticLitLen (lengthCode s.value + 257) + lengthExtra (lengthCode s.value) + 5 +
      distanceExtra (distanceCode (s.distance - 1))

/-- `s->opt_len` after `build_bl_tree`: the block's symbols and `END_BLOCK` under the dynamic trees, and the tree
header. -/
def optLen (xs : List Symbol) : Nat := (blockCosts xs).sum + litLens xs 256 + blockHeader xs

/-- `s->static_len` after both `build_tree` calls: the block's symbols and `END_BLOCK` under the static trees. -/
def staticLen (xs : List Symbol) : Nat := (xs.map staticCost).sum + 7

/-- **The block choice of a dynamic block**: `opt_lenb < static_lenb`. -/
def Chosen (xs : List Symbol) : Prop := (optLen xs + 3 + 7) / 8 < (staticLen xs + 3 + 7) / 8

theorem chosen_bits {xs : List Symbol} (h : Chosen xs) : optLen xs + 1 ≤ staticLen xs := by
  unfold Chosen at h
  refine Classical.byContradiction fun c => ?_
  have := Nat.div_le_div_right (c := 8) (show staticLen xs + 3 + 7 ≤ optLen xs + 3 + 7 by omega)
  omega

theorem sum_map_add3 {α : Type} (f g k : α → Nat) : ∀ l : List α,
    (l.map fun x => f x + g x + k x).sum = (l.map f).sum + (l.map g).sum + (l.map k).sum
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_add3 f g k l]
    omega

/-- **The choice row**: from `Chosen`, over the frequencies of the two trees. -/
theorem choice_row (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) (h : Chosen xs) :
    blockHeader xs + mass (fun v => litFreq xs v * litLens xs v) 286 +
      mass (fun v => distFreq xs v * distLens xs v) 30 + 1 ≤
      mass (fun v => litFreq xs v * staticLitLen v) 286 + 5 * mass (distFreq xs) 30 := by
  have bits := chosen_bits h
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
  let A := fun s : Symbol => litLens xs (s.literalKey lengthCode)
  let S := fun s : Symbol => staticLitLen (s.literalKey lengthCode)
  let X := fun s : Symbol => if s.distance = 0 then 0 else
    lengthExtra (lengthCode s.value) + distanceExtra (distanceCode (s.distance - 1))
  let D := fun s : Symbol => match s.distanceKey distanceCode with | none => 0 | some k => distLens xs k
  let M := fun s : Symbol => match s.distanceKey distanceCode with | none => 0 | some _ => 5
  have dyn : (blockCosts xs).sum = (xs.map A).sum + (xs.map X).sum + (xs.map D).sum := by
    rw [← sum_map_add3]
    unfold blockCosts
    congr 1
    apply List.map_congr_left
    intro s _
    simp only [symbolCost, A, X, D, Symbol.literalKey, Symbol.distanceKey]
    by_cases d : s.distance = 0 <;> simp [d] <;> omega
  have sta : (xs.map staticCost).sum = (xs.map S).sum + (xs.map X).sum + (xs.map M).sum := by
    rw [← sum_map_add3]
    congr 1
    apply List.map_congr_left
    intro s _
    simp only [staticCost, S, X, M, Symbol.literalKey, Symbol.distanceKey]
    by_cases d : s.distance = 0 <;> simp [d] <;> omega
  have litMass : ∀ g : Nat → Nat, mass (fun v => litFreq xs v * g v) 286 = (xs.map fun s => g (s.literalKey lengthCode)).sum + g 256 := by
    intro g
    have split : mass (fun v => litFreq xs v * g v) 286 =
        mass (fun v => countKey (fun s => some (s.literalKey lengthCode)) xs v * g v) 286 +
          mass (fun v => if v = 256 then g 256 else 0) 286 := by
      rw [← mass_add]
      apply mass_congr
      intro v _
      unfold litFreq literalFrequency
      by_cases e : v = 256
      · subst e; simp [Nat.add_mul]; omega
      · simp [e]
    rw [split, weighted_count_key (Symbol.literalKey lengthCode) 286 g literalKeys, mass_single_value]
    simp
  have dA : mass (fun v => litFreq xs v * litLens xs v) 286 = (xs.map A).sum + litLens xs 256 :=
    litMass (litLens xs)
  have dS : mass (fun v => litFreq xs v * staticLitLen v) 286 = (xs.map S).sum + staticLitLen 256 :=
    litMass staticLitLen
  have dD : mass (fun v => distFreq xs v * distLens xs v) 30 = (xs.map D).sum :=
    weighted_optional_key (Symbol.distanceKey distanceCode) 30 (distLens xs) distanceKeys
  have dM : mass (fun v => distFreq xs v * 5) 30 = (xs.map M).sum :=
    weighted_optional_key (Symbol.distanceKey distanceCode) 30 (fun _ => 5) distanceKeys
  rw [mass_mul_right] at dM
  have s256 : staticLitLen 256 = 7 := rfl
  unfold optLen at bits
  unfold staticLen at bits
  rw [s256] at dS
  omega

/-! ## Symbol count and match balance (for the small-buffer certificates) -/

/-- No symbol has the end-of-block key. -/
theorem literal_end_frequency (lc : Nat → Nat) (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) :
    literalFrequency lc xs 256 = 1 := by
  unfold literalFrequency
  simp only [ite_true]
  have zero : countKey (fun s => some (s.literalKey lc)) xs 256 = 0 := by
    induction xs with
    | nil => rfl
    | cons s rest ih =>
      simp only [countKey]
      have v := (valid s (List.mem_cons_self ..)).2
      have ne : s.literalKey lc ≠ 256 := by
        unfold Symbol.literalKey; split <;> omega
      rw [ih (fun t m => valid t (List.mem_cons_of_mem _ m))]
      simp [ne]
  omega

/-- One literal/length symbol per entry of `xs`, besides the end of block. -/
theorem literal_symbol_count (lc : Nat → Nat) (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid)
    (keys : ∀ s ∈ xs, s.literalKey lc < 286) :
    mass (fun v => if v = 256 then 0 else literalFrequency lc xs v) 286 = xs.length := by
  have total := literal_frequency_mass lc keys
  have endOne := literal_end_frequency lc xs valid
  have parts : mass (literalFrequency lc xs) 286 =
      mass (fun v => if v = 256 then 0 else literalFrequency lc xs v) 286 +
        mass (fun v => if v = 256 then literalFrequency lc xs 256 else 0) 286 := by
    rw [← mass_add]
    apply mass_congr
    intro v _
    by_cases e : v = 256
    · subst e; simp
    · simp [e]
  rw [mass_single_value] at parts
  simp only [show (256 : Nat) < 286 by omega, ite_true, endOne] at parts
  omega

/-- As many length codes as distance codes. -/
theorem match_balance (lc dc : Nat → Nat) (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid)
    (literalKeys : ∀ s ∈ xs, s.literalKey lc < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey dc = some k → k < 30) :
    mass (fun v => if v < 257 then 0 else literalFrequency lc xs v) 286 = mass (distanceFrequency dc xs) 30 := by
  have left : mass (fun v => if v < 257 then 0 else literalFrequency lc xs v) 286 =
      mass (fun v => countKey (fun s => some (s.literalKey lc)) xs v * (if v < 257 then 0 else 1)) 286 := by
    apply mass_congr
    intro v _
    by_cases low : v < 257
    · simp [low]
    · simp [low, literalFrequency, show v ≠ 256 by omega]
  have right : mass (distanceFrequency dc xs) 30 = mass (fun v => countKey (Symbol.distanceKey dc) xs v * 1) 30 := by
    apply mass_congr
    intro v _
    simp [distanceFrequency]
  rw [left, right, weighted_count_key (Symbol.literalKey lc) 286 _ literalKeys,
    weighted_optional_key (Symbol.distanceKey dc) 30 _ distanceKeys]
  congr 1
  apply List.map_congr_left
  intro s member
  have v := (valid s member).2
  unfold Symbol.literalKey Symbol.distanceKey
  by_cases d : s.distance = 0
  · simp [d, show s.value < 257 by omega]
  · simp [d]

/-- **The dynamic-block overlay budget for the covered `lit_bufsize`**: `512` and `1024 .. 32768` (`memLevel` 3 to
9), for every block, with no block-choice fact. `lit_bufsize` 128 and 256 (`memLevel` 1 and 2) are not covered. -/
theorem dynamic_budget_covered {B b0 : Nat} (xs : List Symbol) (hB : B = 512 ∨ (1024 ≤ B ∧ B ≤ 32768))
    (hb0 : b0 ≤ 7) (hn : xs.length + 1 ≤ B) (valid : ∀ s ∈ xs, s.Valid) :
    Budget B (b0 + 3 + blockHeader xs) (blockCosts xs) := by
  rcases hB with rfl | ⟨lo, hi⟩
  · exact dynamic_budget_512 xs hb0 hn valid
  · exact dynamic_budget_ge_1024 xs lo hi hb0 hn valid

end ZlibNgF.Math.OverlayDynamic
