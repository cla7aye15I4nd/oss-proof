import ZlibNgF.Math.OverlayChoice
import ZlibNgF.Math.OverlayTinyTrees
import ZlibNgF.Math.TreesHdr

noncomputable section

/-!
# `opt_len` and `static_len` as sums over symbols (heap-free)

`gen_bitlen` adds `freq(k) * (len(k) + extra(k))` over the codes `k` of the literal/length and distance trees, and
`build_tree` adds `freq(k) * (stree[k].Len + extra(k))` to `static_len`. Over the frequencies of a block
(`litFreq` / `distFreq`) these code sums are symbol sums: the cost of every symbol under the code lengths, plus the
length of `END_BLOCK` (`freq_cost`). So the literal/length and distance parts of `opt_len` are `blockCosts xs` plus
`litLens xs 256` (`opt_codes`), and `static_len` is `staticLen xs` (`static_codes`).
-/

namespace ZlibNgF.Math.OverlayDynamic
open ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

/-- `extra_lbits[k - LITERALS - 1]` for a length code `k`, 0 for a literal or `END_BLOCK`. -/
def xbL (k : Nat) : Nat := if 257 ≤ k then lengthExtra (k - 257) else 0

theorem sum_map_add {α : Type} (f g : α → Nat) : ∀ l : List α,
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_add f g l]
    omega

/-- **Code sums are symbol sums**: the frequencies of the block weighted by code lengths `g` / `D` and the extra
bits are the costs of the symbols under `g` / `D`, plus `END_BLOCK`. -/
theorem freq_cost (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) (g D : Nat → Nat) :
    mass (fun k => litFreq xs k * (g k + xbL k)) 286 + mass (fun k => distFreq xs k * (D k + distanceExtra k)) 30 =
      (xs.map (symbolCost g D lengthExtra distanceExtra lengthCode distanceCode)).sum + g 256 := by
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
  have split : mass (fun k => litFreq xs k * (g k + xbL k)) 286 =
      mass (fun v => countKey (fun s => some (s.literalKey lengthCode)) xs v * (g v + xbL v)) 286 +
        mass (fun v => if v = 256 then g 256 + xbL 256 else 0) 286 := by
    rw [← mass_add]
    apply mass_congr
    intro v _
    unfold litFreq literalFrequency
    by_cases e : v = 256
    · subst e; simp [Nat.add_mul]; omega
    · simp [e]
  rw [split, weighted_count_key (Symbol.literalKey lengthCode) 286 _ literalKeys, mass_single_value]
  have dD : mass (fun k => distFreq xs k * (D k + distanceExtra k)) 30 =
      (xs.map fun s => match s.distanceKey distanceCode with | none => 0 | some k => D k + distanceExtra k).sum :=
    weighted_optional_key (Symbol.distanceKey distanceCode) 30 (fun k => D k + distanceExtra k) distanceKeys
  rw [dD]
  have x256 : xbL 256 = 0 := rfl
  simp only [show (256 : Nat) < 286 by omega, ite_true, x256, Nat.add_zero]
  have e : (xs.map fun s => g (s.literalKey lengthCode) + xbL (s.literalKey lengthCode)).sum +
      (xs.map fun s => match s.distanceKey distanceCode with | none => 0 | some k => D k + distanceExtra k).sum =
      (xs.map (symbolCost g D lengthExtra distanceExtra lengthCode distanceCode)).sum := by
    rw [← sum_map_add]
    congr 1
    apply List.map_congr_left
    intro s hs
    simp only [symbolCost, Symbol.literalKey, Symbol.distanceKey, xbL]
    by_cases d : s.distance = 0
    · have := (valid s hs).2
      simp [d, show ¬ 257 ≤ s.value by omega]
    · simp only [d, ↓reduceIte, show 257 ≤ lengthCode s.value + 257 by omega, Nat.add_sub_cancel]
      simp only [Nat.add_assoc]
  omega

/-- The literal/length and distance parts of `opt_len`. -/
theorem opt_codes (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) :
    mass (fun k => litFreq xs k * (litLens xs k + xbL k)) 286 +
      mass (fun k => distFreq xs k * (distLens xs k + distanceExtra k)) 30 = (blockCosts xs).sum + litLens xs 256 :=
  freq_cost xs valid _ _

/-- `static_len` after both `build_tree` calls. -/
theorem static_codes (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) :
    mass (fun k => litFreq xs k * (staticLitLen k + xbL k)) 286 +
      mass (fun k => distFreq xs k * (5 + distanceExtra k)) 30 = staticLen xs := by
  rw [freq_cost xs valid staticLitLen (fun _ => 5)]
  unfold staticLen
  congr 2

/-- A symbol costs at most 48 bits under code lengths at most 15. -/
theorem symbolCost_le (xs : List Symbol) (s : Symbol) :
    symbolCost (litLens xs) (distLens xs) lengthExtra distanceExtra lengthCode distanceCode s ≤ 48 := by
  have h1 := litLens_le xs s.value
  have h2 := litLens_le xs (lengthCode s.value + 257)
  have h3 := distLens_le xs (distanceCode (s.distance - 1))
  have h4 : lengthExtra (lengthCode s.value) ≤ 5 := by
    have := lengthCode_lt s.value
    generalize lengthCode s.value = c at this
    have : ∀ c : Fin 29, lengthExtra c.val ≤ 5 := by decide
    exact this ⟨c, by assumption⟩
  have h5 : distanceExtra (distanceCode (s.distance - 1)) ≤ 13 := by
    have := distanceCode_lt (s.distance - 1)
    generalize distanceCode (s.distance - 1) = c at this
    have : ∀ c : Fin 30, distanceExtra c.val ≤ 13 := by decide
    exact this ⟨c, by assumption⟩
  unfold symbolCost; split <;> omega

theorem sum_le_mul (k : Nat) : ∀ l : List Nat, (∀ c ∈ l, c ≤ k) → l.sum ≤ k * l.length
  | [], _ => by simp
  | c :: l, h => by
    have := sum_le_mul k l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h c (List.mem_cons_self ..)
    simp only [List.sum_cons, List.length_cons, Nat.mul_succ]; omega

theorem blockCosts_sum_le (xs : List Symbol) : (blockCosts xs).sum ≤ 48 * xs.length := by
  have := sum_le_mul 48 (blockCosts xs) (fun c hc => by
    simp only [blockCosts, List.mem_map] at hc
    obtain ⟨s, -, rfl⟩ := hc
    exact symbolCost_le xs s)
  simpa [blockCosts] using this

/-- A symbol costs at most 32 bits under the static trees. -/
theorem staticCost_le (s : Symbol) : staticCost s ≤ 32 := by
  have h4 : lengthExtra (lengthCode s.value) ≤ 5 := by
    have := lengthCode_lt s.value
    generalize lengthCode s.value = c at this
    have : ∀ c : Fin 29, lengthExtra c.val ≤ 5 := by decide
    exact this ⟨c, by assumption⟩
  have h5 : distanceExtra (distanceCode (s.distance - 1)) ≤ 13 := by
    have := distanceCode_lt (s.distance - 1)
    generalize distanceCode (s.distance - 1) = c at this
    have : ∀ c : Fin 30, distanceExtra c.val ≤ 13 := by decide
    exact this ⟨c, by assumption⟩
  have h1 : ∀ v, staticLitLen v ≤ 9 := fun v => by
    unfold staticLitLen; split
    · omega
    · split
      · omega
      · split <;> omega
  have := h1 s.value; have := h1 (lengthCode s.value + 257)
  unfold staticCost; split <;> omega

theorem staticLen_le (xs : List Symbol) : staticLen xs ≤ 32 * xs.length + 7 := by
  have := sum_le_mul 32 (xs.map staticCost) (fun c hc => by
    simp only [List.mem_map] at hc
    obtain ⟨s, -, rfl⟩ := hc
    exact staticCost_le s)
  unfold staticLen; simp only [List.length_map] at this; omega


/-! ## `max_code` and the bit-length codes -/

theorem forceNext_ge (x : Nat) : x ≤ forceNext x ∧ 1 ≤ forceNext x := by
  unfold forceNext; split <;> omega

theorem maxCode1_gt (f : Nat → Nat) : ∀ n v, v < n → f v ≠ 0 → v < maxCode1 f n
  | 0, v, h, _ => by omega
  | n + 1, v, h, hf => by
    simp only [maxCode1]
    split
    · omega
    · rename_i hn
      have : v ≠ n := fun e => by subst e; exact hn hf
      exact maxCode1_gt f n v (by omega) hf

theorem scan_nil_of (f : Nat → Nat) : ∀ n, maxCode1 f n = 0 → scanLeaves f n = []
  | 0, _ => rfl
  | n + 1, h => by
    simp only [maxCode1] at h
    split at h
    · omega
    · rename_i hn
      simp only [scanLeaves, scan_nil_of f n h, hn, ↓reduceIte, List.append_nil]

theorem forced_ge (ls : List (Nat × Nat)) (mc1 : Nat) : mc1 ≤ (forced ls mc1).2 := by
  have a := forceNext_ge mc1; have b := forceNext_ge (forceNext mc1)
  unfold forced; split <;> simp only <;> omega

/-- A used code lies below `max_code + 1`. -/
theorem built_gt (e : Nat) (f : Nat → Nat) (v : Nat) (hv : v < e) (hf : f v ≠ 0) :
    v < (buildTree e f).maxCode1 :=
  Nat.lt_of_lt_of_le (maxCode1_gt f e v hv hf) (forced_ge _ _)

/-- `max_code + 1` is at least 1 (the forcing loop adds codes to an empty tree). -/
theorem built_pos (e : Nat) (f : Nat → Nat) : 1 ≤ (buildTree e f).maxCode1 := by
  show 1 ≤ (forced (scanLeaves f e) (maxCode1 f e)).2
  by_cases h : maxCode1 f e = 0
  · rw [scan_nil_of f e h]
    have := forceNext_ge (forceNext (maxCode1 f e)); simp only [forced]; omega
  · have := forced_ge (scanLeaves f e) (maxCode1 f e); omega

/-- From a state with `prevlen ≤ 0`, the scan of a tree with a nonzero length emits a code length (a token at most
15) before any repeat of a nonzero length. -/
theorem scan_small (len : Nat → Nat) (m : Nat) (hl : ∀ i, i < m → len i ≤ 15) :
    ∀ k n (p : Int) c mx mn, n + k = m → p ≤ 0 → (∃ j, n ≤ j ∧ j < m ∧ len j ≠ 0) →
      ∃ t ∈ scanTokens len m k n p c mx mn (len n), t ≤ 15
  | 0, n, p, c, mx, mn, hk, _, ⟨j, h1, h2, _⟩ => by omega
  | k + 1, n, p, c, mx, mn, hk, hp, ⟨j, h1, h2, h3⟩ => by
    have hn15 := hl n (by omega)
    simp only [scanTokens]
    split
    · rename_i hc
      have hnx : n + 1 < m := by
        refine Classical.byContradiction fun c => ?_
        have : nextLen len m n = 65535 := by unfold nextLen; rw [itF c]
        omega
      have e1 : nextLen len m n = len (n + 1) := by unfold nextLen; rw [itT hnx]
      rw [e1]
      refine scan_small len m hl k (n + 1) p (c + 1) mx mn (by omega) hp ?_
      by_cases hj : j = n
      · subst hj; exact ⟨j + 1, by omega, hnx, by rw [← e1]; omega⟩
      · exact ⟨j, by omega, h2, h3⟩
    · by_cases h0 : len n = 0
      · by_cases hm : c + 1 < mn
        · exact ⟨0, List.mem_append_left _ (by simp [groupTokens, hm, h0]), by omega⟩
        · have hj : n < j := by
            rcases Nat.lt_or_ge n j with h | h
            · exact h
            · obtain rfl : j = n := by omega
              exact absurd h0 h3
          have hnx : n + 1 < m := by omega
          have e1 : nextLen len m n = len (n + 1) := by unfold nextLen; rw [itT hnx]
          obtain ⟨t, ht, ht15⟩ := scan_small len m hl k (n + 1) (len n : Int) 0
            (if nextLen len m n = 0 then 138 else if len n = nextLen len m n then 6 else 7)
            (if nextLen len m n = 0 then 3 else if len n = nextLen len m n then 3 else 4) (by omega) (by omega)
            ⟨j, by omega, h2, h3⟩
          rw [e1] at ht ⊢
          exact ⟨t, List.mem_append_right _ ht, ht15⟩
      · refine ⟨len n, List.mem_append_left _ ?_, hn15⟩
        unfold groupTokens
        split
        · simp
        · have : ((len n : Nat) : Int) ≠ p := by omega
          simp [this]

theorem treeTokens_small (len : Nat → Nat) (m : Nat) (hl : ∀ i, i < m → len i ≤ 15) (j : Nat) (hj : j < m)
    (h0 : len j ≠ 0) : ∃ t ∈ treeTokens len m, t ≤ 15 :=
  scan_small len m hl m 0 (-1) 0 _ _ (by omega) (by omega) ⟨j, by omega, hj, h0⟩

theorem blOrder_pos : ∀ t : Fin 16, ∃ j : Fin 19, 3 ≤ j.val ∧ blOrder.getD j.val 0 = t.val := by decide

/-- `max_blindex` of the C loop is the model's `blMaxIndex` when a code length is among the bit-length symbols. -/
theorem blMaxC_of_tok (toks : List Nat) (t : Nat) (ht : t ∈ toks) (h15 : t ≤ 15) :
    blMaxC (treeLengths 19 7 (blFreq toks)) 18 = blMaxIndex (treeLengths 19 7 (blFreq toks)) 18 := by
  refine blMaxC_eq _ 18 ?_
  obtain ⟨j, hj3, hj⟩ := blOrder_pos ⟨t, by omega⟩
  refine ⟨j.val, hj3, by omega, ?_⟩
  simp only at hj
  rw [hj]
  refine treeLengths_pos 19 7 _ t (by omega) (by omega) (by omega) ?_
  unfold blFreq
  exact Nat.pos_iff_ne_zero.mp (List.count_pos_iff.mpr ht)

end ZlibNgF.Math.OverlayDynamic
