import ZlibNgF.Math.OverlayTinyHeader
import ZlibNgF.Math.OverlayChoice

noncomputable section

/-!
# The dynamic-block overlay budget at `lit_bufsize` 128 and 256 (heap-free)

At `lit_bufsize = 128` and `256` (memLevel 1 and 2) the header bound of 2283 bits alone exceeds the room, so the
budget uses the block at hand: the header against a reference bit-length code (`header_128`, `header_256`), the
block choice of `zng_tr_flush_block` (`choice_row`, from `Chosen`), Kraft and the Fibonacci leaf bounds of the
two data trees (`data_kraft`, `data_leaf`; with at most `B` symbols both trees weigh at most `B + 3`, so no
length exceeds 9 resp. 11 and no repair happens), the symbol count and the match balance. The certificate of
`OverlayTiny` then gives `H + E ≤ 989` at `B = 128` and `H + E ≤ 1910` at `B = 256`, below the `1014` and `2038`
bits the budget allows with `b0 ≤ 7`.

`dynamic_budget_tiny`: the budget at `B = 128` and `256` for every dynamic block (`Chosen`).
`dynamic_budget`: the budget for every `lit_bufsize` zlib-ng uses (`128`, `256`, `512`, `1024 .. 32768`).
-/

namespace ZlibNgF.Math.OverlayDynamic
open ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
open ZlibNgF.Math.TreesOverlay
set_option autoImplicit false

set_option maxRecDepth 10000 in
theorem extra_bridge : (∀ c, c < 29 → lengthExtra c = OverlayTiny.lengthExtra c) ∧
    (∀ c, c < 30 → distanceExtra c = OverlayTiny.distanceExtra c) := by decide +kernel

/-- `max_code + 1` of the literal/length tree is at least `257` (the end-of-block code is used). -/
theorem lit_codes_ge (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) :
    257 ≤ (buildTree 286 (litFreq xs)).maxCode1 := by
  have e := literal_end_frequency lengthCode xs valid
  have mem := scan_complete (freq := litFreq xs) (n := 286) (v := 256) (by omega) (by unfold litFreq; omega)
  have ge := maxCode1_ge (litFreq xs) 286 _ mem
  have up : ∀ (ls : List (Nat × Nat)) (mc : Nat), mc ≤ (forced ls mc).2 := by
    intro ls mc
    unfold forced
    split <;> (simp only [forceNext]; repeat' split) <;> omega
  have mc : ∀ (e : Nat) (g : Nat → Nat), (buildTree e g).maxCode1 = (forced (scanLeaves g e) (maxCode1 g e)).2 :=
    fun _ _ => rfl
  have := up (scanLeaves (litFreq xs) 286) (maxCode1 (litFreq xs) 286)
  rw [mc]
  simp only at ge
  omega

/-- **The small-buffer facts of a block** with at most `B ≤ 256` symbols. -/
theorem tiny_facts (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) {W : Nat} (hW : xs.length + 3 ≤ W)
    (hW2 : W < 2584) :
    mass (fun v => OverlayTiny.kraftTerm (litLens xs v)) 286 ≤ 2 ^ 15 ∧
    mass (fun v => OverlayTiny.kraftTerm (distLens xs v)) 30 ≤ 2 ^ 15 ∧
    (∀ v, v < 286 → OverlayTiny.LeafBound W (litLens xs v) (litFreq xs v)) ∧
    (∀ v, v < 30 → OverlayTiny.LeafBound W (distLens xs v) (distFreq xs v)) := by
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
  exact ⟨data_kraft (by omega) oL, data_kraft (by omega) oD,
    fun v hv => data_leaf (by omega) oL (by omega) v hv, fun v hv => data_leaf (by omega) oD (by omega) v hv⟩

/-- **Header plus excess** of a small block, from the certificate of `OverlayTiny`. -/
theorem tiny_header_excess_block {B : Nat} (xs : List Symbol) (hB : B = 128 ∨ B = 256) (hn : xs.length ≤ B)
    (valid : ∀ s ∈ xs, s.Valid) (hc : Chosen xs) :
    blockHeader xs + bitExcess (blockCosts xs) ≤ (if B = 128 then 989 else 1910) := by
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
  have lcLo := lit_codes_ge xs valid
  have lcHi := built_maxCode1_le (elems := 286) (litFreq xs) (by omega)
  have dcHi := built_maxCode1_le (elems := 30) (distFreq xs) (by omega)
  have endF : litFreq xs 256 = 1 := literal_end_frequency lengthCode xs valid
  have symbols : mass (fun v => if v = 256 then 0 else litFreq xs v) 286 = xs.length :=
    literal_symbol_count lengthCode xs valid literalKeys
  have balance : mass (fun v => if v < 257 then 0 else litFreq xs v) 286 = mass (distFreq xs) 30 :=
    match_balance lengthCode distanceCode xs valid literalKeys distanceKeys
  have choice := choice_row xs valid hc
  have stEq : (fun v => litFreq xs v * staticLitLen v) = (fun v => litFreq xs v * OverlayTiny.staticLen v) := rfl
  rw [stEq] at choice
  -- the excess at the actual lengths
  have base := symbol_excess_le_mass xs (litLens xs) (distLens xs) lengthExtra distanceExtra lengthCode
    distanceCode valid literalKeys distanceKeys (fun v _ _ => litLens_le xs v)
  have exL : mass (fun v => literalFrequency lengthCode xs v * literalExcess (litLens xs) lengthExtra v) 286 =
      mass (fun v => litFreq xs v * OverlayTiny.literalExcess v (litLens xs v)) 286 := by
    apply mass_congr; intro v hv
    simp only [literalExcess, OverlayTiny.literalExcess, litFreq]
    split
    · rfl
    · rw [extra_bridge.1 (v - 257) (by omega)]
  have exD : mass (fun v => distanceFrequency distanceCode xs v * distanceExcess (distLens xs) distanceExtra v) 30 =
      mass (fun v => distFreq xs v * OverlayTiny.distanceExcess v (distLens xs v)) 30 := by
    apply mass_congr; intro v hv
    simp only [distanceExcess, OverlayTiny.distanceExcess, distFreq]
    rw [extra_bridge.2 v hv]
  have hE : bitExcess (blockCosts xs) ≤ mass (fun v => litFreq xs v * OverlayTiny.literalExcess v (litLens xs v)) 286 +
      mass (fun v => distFreq xs v * OverlayTiny.distanceExcess v (distLens xs v)) 30 := by
    unfold blockCosts; rw [← exL, ← exD]; exact base
  have hdr : blockHeader xs = headerBits (litLens xs) (buildTree 286 (litFreq xs)).maxCode1 (distLens xs)
      (buildTree 30 (distFreq xs)).maxCode1 := rfl
  rcases hB with rfl | rfl
  · obtain ⟨kL, kD, leafL, leafD⟩ := tiny_facts xs valid (W := 131) (by omega) (by omega)
    have lenL : ∀ v, v < 286 → litLens xs v ≤ 9 := fun v hv => OverlayTiny.leaf_len_le_9 (leafL v hv)
    have lenD : ∀ v, v < 30 → distLens xs v ≤ 9 := fun v hv => OverlayTiny.leaf_len_le_9 (leafD v hv)
    have eobL := leafL 256 (by omega)
    rw [endF] at eobL
    have eob : litFreq xs 256 = 1 ∧ 1 ≤ litLens xs 256 ∧ fib (litLens xs 256 + 1) + fib (litLens xs 256) ≤ 131 := by
      rcases eobL with ⟨h, _⟩ | ⟨_, h1, h2⟩
      · omega
      · exact ⟨endF, h1, by simpa using h2⟩
    have header := header_128 (litLens xs) (distLens xs) _ _ lcLo lcHi dcHi (fun i hi => lenL i (by omega))
      (fun i hi => lenD i (by omega)) (by omega)
    rw [← hdr] at header
    have cert := OverlayTiny.header_excess_cert_128 (litLens xs) (litFreq xs) (distLens xs) (distFreq xs)
      (blockHeader xs) 30 (Nat.le_refl _) kL kD (fun v hv _ => leafL v hv) eob leafD (by omega) balance header choice
    simp only [ite_true]
    omega
  · obtain ⟨kL, kD, leafL, leafD⟩ := tiny_facts xs valid (W := 259) (by omega) (by omega)
    have lenL : ∀ v, v < 286 → litLens xs v ≤ 11 := fun v hv => OverlayTiny.leaf_len_le_11 (leafL v hv)
    have lenD : ∀ v, v < 30 → distLens xs v ≤ 11 := fun v hv => OverlayTiny.leaf_len_le_11 (leafD v hv)
    have eobL := leafL 256 (by omega)
    rw [endF] at eobL
    have eob : litFreq xs 256 = 1 ∧ 1 ≤ litLens xs 256 ∧ fib (litLens xs 256 + 1) + fib (litLens xs 256) ≤ 259 := by
      rcases eobL with ⟨h, _⟩ | ⟨_, h1, h2⟩
      · omega
      · exact ⟨endF, h1, by simpa using h2⟩
    have header := header_256 (litLens xs) (distLens xs) _ _ lcLo lcHi dcHi (fun i hi => lenL i (by omega))
      (fun i hi => lenD i (by omega)) (by omega)
    rw [← hdr] at header
    have cert := OverlayTiny.header_excess_cert_256 (litLens xs) (litFreq xs) (distLens xs) (distFreq xs)
      (blockHeader xs) 245 (Nat.le_refl _) kL kD (fun v hv _ => leafL v hv) eob leafD (by omega) balance header choice
    simp only [show (256 : Nat) ≠ 128 by omega, ite_false]
    omega

/-- **The dynamic-block overlay budget for `lit_bufsize` 128 and 256** (memLevel 1 and 2), for every block that
`zng_tr_flush_block` sends with dynamic trees. -/
theorem dynamic_budget_tiny {B b0 : Nat} (xs : List Symbol) (hB : B = 128 ∨ B = 256) (hb0 : b0 ≤ 7)
    (hn : xs.length ≤ B) (valid : ∀ s ∈ xs, s.Valid) (hc : Chosen xs) :
    Budget B (b0 + 3 + blockHeader xs) (blockCosts xs) := by
  have h := tiny_header_excess_block xs hB hn valid hc
  unfold Budget
  rcases hB with rfl | rfl
  · simp only [ite_true] at h; omega
  · simp only [show (256 : Nat) ≠ 128 by omega, ite_false] at h; omega

/-- **The dynamic-block overlay budget for every `lit_bufsize` of zlib-ng** (`128`, `256`, `512`,
`1024 .. 32768`), for every block that `zng_tr_flush_block` sends with dynamic trees. -/
theorem dynamic_budget {B b0 : Nat} (xs : List Symbol)
    (hB : B = 128 ∨ B = 256 ∨ B = 512 ∨ (1024 ≤ B ∧ B ≤ 32768)) (hb0 : b0 ≤ 7)
    (hn : xs.length ≤ B) (valid : ∀ s ∈ xs, s.Valid) (hc : Chosen xs) :
    Budget B (b0 + 3 + blockHeader xs) (blockCosts xs) := by
  rcases hB with h | h | h
  · exact dynamic_budget_tiny xs (Or.inl h) hb0 hn valid hc
  · exact dynamic_budget_tiny xs (Or.inr h) hb0 hn valid hc
  · exact dynamic_budget_covered xs h hb0 hn valid

end ZlibNgF.Math.OverlayDynamic
