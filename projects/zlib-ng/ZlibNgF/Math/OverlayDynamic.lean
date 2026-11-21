import ZlibNgF.Math.HuffExcess
import ZlibNgF.Math.OverlayHeader

noncomputable section

/-!
# The `sym_buf` overlay budget of a dynamic block (heap-free)

The budget `TreesOverlay.Budget B (b0 + 3 + H) costs` of a block sent with dynamic trees: `b0 ≤ 7` bits waiting in
the bit buffer, 3 block-type bits, the tree header `H` (`headerBits`, the bits of `send_all_trees`), and the symbol
costs under the code lengths zlib-ng assigns (`treeLengths`, the model of `build_tree` + `gen_bitlen` in
`HuffModel`, with `max_length` 15 for the literal/length and distance trees and 7 for the bit-length tree).

* Symbols (`HuffSymbols.Symbol`): `distance = 0` is a literal (`value` the byte), otherwise a match of length
  `value + 3` (`value < 256`) at distance `distance ≤ 32768`. The frequencies are those of `zng_tr_tally_*`
  with `END_BLOCK` counted once (`literalFrequency`, `distanceFrequency`).
* The length and distance codes and their extra bits are the tables of RFC 1951 (`lengthCode`, `distanceCode`,
  `lengthExtra`, `distanceExtra`; zlib-ng's `zng_length_code`, `zng_dist_code`, `extra_lbits`, `extra_dbits`).
* A symbol costs its code length plus extra bits (`symbolCost`): a literal `ltree[c].Len`, a match
  `ltree[257 + lc].Len + extra_lbits[lc] + dtree[dc].Len + extra_dbits[dc]`.

`dynamic_budget_ge_1024`: for every `1024 ≤ B ≤ 32768` (`lit_bufsize` of memLevel 4 to 9) and every block of at
most `B` valid symbols, the budget holds, whatever the block choice: the header has at most 2283 bits
(`header_le`) and the excess is at most `5.315` bits per symbol (`W < 2584`, no length overflow) or
`6.257` bits per symbol (with the overflow repair) plus a constant.

Not covered here: `B ∈ {128, 256, 512}` (memLevel 1 to 3), where the bound needs the block-choice inequality of
`zng_tr_flush_block` (`opt_lenb < static_lenb`).
-/

namespace ZlibNgF.Math.OverlayDynamic
open ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
open ZlibNgF.Math.TreesOverlay
set_option autoImplicit false

/-- Base lengths of the length codes 257..285. -/
def lenBase : List Nat :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

/-- `extra_lbits`. -/
def lenExtraTab : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

/-- Base distances of the distance codes 0..29. -/
def distBase : List Nat :=
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097,
    6145, 8193, 12289, 16385, 24577]

/-- `extra_dbits`. -/
def distExtraTab : List Nat :=
  [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

/-- `zng_length_code[v]`: the length code (0..28) of match length `v + 3`. -/
def lengthCode (v : Nat) : Nat := (lenBase.filter (· ≤ v + 3)).length - 1

/-- `zng_dist_code` of `d = distance - 1`: the distance code (0..29). -/
def distanceCode (d : Nat) : Nat := (distBase.filter (· ≤ d + 1)).length - 1

/-- `extra_lbits[c]`. -/
def lengthExtra (c : Nat) : Nat := lenExtraTab.getD c 0

/-- `extra_dbits[c]`. -/
def distanceExtra (c : Nat) : Nat := distExtraTab.getD c 0

/-- `dyn_ltree[*].Freq` at the flush: symbol counts with `END_BLOCK` once. -/
def litFreq (xs : List Symbol) : Nat → Nat := literalFrequency lengthCode xs

/-- `dyn_dtree[*].Freq` at the flush. -/
def distFreq (xs : List Symbol) : Nat → Nat := distanceFrequency distanceCode xs

/-- Literal/length code lengths (`build_tree(s, &s->l_desc)`). -/
def litLens (xs : List Symbol) : Nat → Nat := treeLengths 286 15 (litFreq xs)

/-- Distance code lengths (`build_tree(s, &s->d_desc)`). -/
def distLens (xs : List Symbol) : Nat → Nat := treeLengths 30 15 (distFreq xs)

/-- The costs of the block's symbols under the dynamic trees. -/
def blockCosts (xs : List Symbol) : List Nat :=
  xs.map (symbolCost (litLens xs) (distLens xs) lengthExtra distanceExtra lengthCode distanceCode)

/-- The bits of `send_all_trees(s, l_desc.max_code + 1, d_desc.max_code + 1, max_blindex + 1)`. -/
def blockHeader (xs : List Symbol) : Nat :=
  headerBits (litLens xs) (buildTree 286 (litFreq xs)).maxCode1 (distLens xs) (buildTree 30 (distFreq xs)).maxCode1

theorem built_maxCode1_le {elems : Nat} (freq : Nat → Nat) (hE : 3 ≤ elems) :
    (buildTree elems freq).maxCode1 ≤ elems := by
  show (forced (scanLeaves freq elems) (maxCode1 freq elems)).2 ≤ elems
  have := maxCode1_le freq elems
  unfold forced
  split <;> (simp only [forceNext]; repeat' split) <;> omega

theorem litLens_le (xs : List Symbol) (v : Nat) : litLens xs v ≤ 15 := by
  unfold litLens treeLengths; exact genBitlen_le 15 _ v

theorem distLens_le (xs : List Symbol) (v : Nat) : distLens xs v ≤ 15 := by
  unfold distLens treeLengths; exact genBitlen_le 15 _ v

theorem header_bound (xs : List Symbol) : blockHeader xs ≤ 2283 := by
  unfold blockHeader
  exact header_le (litLens xs) (distLens xs) _ _ (built_maxCode1_le (elems := 286) (litFreq xs) (by omega))
    (built_maxCode1_le (elems := 30) (distFreq xs) (by omega)) (litLens_le xs) (distLens_le xs)

set_option maxRecDepth 10000 in
theorem table_data :
    (∀ c : Fin 29, lengthExtra c.val < 6) ∧ (∀ c : Fin 30, distanceExtra c.val < 14) ∧
    mass (fun v => if v < 257 then 0 else lengthCoefficient (lengthExtra (v - 257))) 286 = 1921 ∧
    mass (fun v => distanceCoefficient (distanceExtra v)) 30 = 1660 := by decide +kernel

theorem lengthCode_lt (v : Nat) : lengthCode v < 29 := by
  have := List.length_filter_le (· ≤ v + 3) lenBase
  have h : lenBase.length = 29 := rfl
  unfold lengthCode; omega

theorem distanceCode_lt (d : Nat) : distanceCode d < 30 := by
  have := List.length_filter_le (· ≤ d + 1) distBase
  have h : distBase.length = 30 := rfl
  unfold distanceCode; omega

/-- The whole-block excess bound with explicit push budgets. -/
theorem block_excess (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) :
    let WL := (buildTree 286 (litFreq xs)).root.weight
    let WD := (buildTree 30 (distFreq xs)).root.weight
    WL ≤ xs.length + 3 ∧ WD ≤ xs.length + 2 ∧
    1000 * bitExcess (blockCosts xs) ≤ 400 * (xs.length + 1) + (1921 + 3 * 285) * WL + 1334 * xs.length +
      (1660 + 3 * 29) * WD ∧
    (WL < 2584 → WD < 2584 →
      1000 * bitExcess (blockCosts xs) ≤ 400 * (xs.length + 1) + 1921 * WL + 1334 * xs.length + 1660 * WD) := by
  intro WL WD
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
  obtain ⟨wL, cL, oL, classL, budL, zeroL⟩ := tree_classes (elems := 286) (freq := litFreq xs) (by omega) (by omega)
  obtain ⟨wD, cD, oD, classD, budD, zeroD⟩ := tree_classes (elems := 30) (freq := distFreq xs) (by omega) (by omega)
  have mL : mass (litFreq xs) 286 = xs.length + 1 := literal_frequency_mass lengthCode literalKeys
  have mD : mass (distFreq xs) 30 ≤ xs.length := distance_frequency_mass distanceCode distanceKeys
  have data := table_data
  have run := fun (PL PD : Nat) (fL : SymbolFibPushB 286 PL WL (litFreq xs) (litLens xs))
      (fD : SymbolFibPushB 30 PD WD (distFreq xs) (distLens xs)) =>
    symbol_excess_from_fib PL PD xs (litLens xs) (distLens xs) lengthExtra distanceExtra lengthCode distanceCode
      WL WD valid literalKeys distanceKeys (fun c h => data.1 ⟨c, h⟩) (fun c h => data.2.1 ⟨c, h⟩)
      (fun v _ _ => litLens_le xs v) (fun v _ _ => distLens_le xs v) fL fD data.2.2.1 data.2.2.2
  refine ⟨by omega, by omega, ?_, ?_⟩
  · exact run 285 29 ⟨cL, oL, classL, by omega⟩ ⟨cD, oD, classD, by omega⟩
  · intro hL hD
    have := run 0 0 ⟨cL, oL, classL, by have := zeroL hL; omega⟩ ⟨cD, oD, classD, by have := zeroD hD; omega⟩
    simp only [Nat.mul_zero, Nat.add_zero] at this
    exact this

/-- **The dynamic-block overlay budget for `1024 ≤ B ≤ 32768`.** -/
theorem dynamic_budget_ge_1024 {B b0 : Nat} (xs : List Symbol) (hB : 1024 ≤ B) (hB2 : B ≤ 32768) (hb0 : b0 ≤ 7)
    (hn : xs.length ≤ B) (valid : ∀ s ∈ xs, s.Valid) :
    Budget B (b0 + 3 + blockHeader xs) (blockCosts xs) := by
  have hH := header_bound xs
  obtain ⟨wL, wD, big, small⟩ := block_excess xs valid
  unfold Budget
  by_cases hs : B ≤ 2048
  · have := small (by omega) (by omega)
    omega
  · omega

end ZlibNgF.Math.OverlayDynamic
