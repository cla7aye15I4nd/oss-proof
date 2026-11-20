import ZlibNgF.Math.OverlayTinyTrees
import ZlibNgF.Math.OverlayScan

noncomputable section

/-!
# The dynamic header of a small block against a reference bit-length code (heap-free)

`send_all_trees` writes `14 + 3 * (max_blindex + 1) ≤ 71` bits of counts and the bit-length symbols of
`scan_tree` (`allTokens`) at their lengths in the bit-length tree plus extra bits. With the data-tree lengths at
most 11 (`lit_bufsize = 256`) or 9 (`lit_bufsize = 128`), the bit-length symbols 12 .. 15 (resp. 10 .. 15) do not
occur, so at most 15 (resp. 13) symbols are used, and `bl_cost_le_15` / `bl_cost_le_13` bound the bit-length tree's
cost by the reference code `κ0` (resp. `κ1`) of `OverlayTiny`. The reference cost is then charged per entry of
the two data trees by region (`tree_region`):

* `header_256`: `2 H ≤ 2 (71 + 245) + Σ_v literalCharge256 v (ll v) + Σ_v otherRegionCharge256 (dl v)`;
* `header_128`: `2 H ≤ 2 (71 + 30) + Σ_v literalCharge128 v (ll v) + Σ_v distanceRegionCharge128 (dl v)`
  (the repair term `29 + W / 2` is paid one bit per bit-length symbol, `W` being their number).
-/

namespace ZlibNgF.Math.Huff
open ZlibNgF.Math.HuffSymbols
open ZlibNgF.Math.OverlayTiny (refLen refLen1 literalCharge256 otherRegionCharge256 literalRegionCharge256
  literalCharge128 lengthRegionCharge128 distanceRegionCharge128 literalRegionCharge128)
set_option autoImplicit false

theorem mass_le_of_le (g : Nat → Nat) {n n' : Nat} (h : n ≤ n') : mass g n ≤ mass g n' := by
  have := rsum_mass g (n' - n) n
  rw [show n + (n' - n) = n' by omega] at this
  omega

theorem blExtra_zero {x : Nat} (h : x ≤ 15) : blExtra x = 0 := by
  simp [blExtra, show x ≠ 16 by omega, show x ≠ 17 by omega, show x ≠ 18 by omega]

/-- The facts on the bit-length symbols of two trees with lengths at most `D`. -/
theorem tokens_facts (litLen distLen : Nat → Nat) (lc dc D : Nat) (hD : D ≤ 15)
    (hl : ∀ i, i < lc → litLen i ≤ D) (hd : ∀ i, i < dc → distLen i ≤ D) :
    let toks := allTokens litLen lc distLen dc
    (∀ t ∈ toks, t ≤ D ∨ (16 ≤ t ∧ t ≤ 18)) ∧ mass (blFreq toks) 19 = toks.length ∧ toks.length ≤ lc + dc ∧
      ∀ g : Nat → Nat, (toks.map g).sum = mass (fun k => blFreq toks k * g k) 19 := by
  intro toks
  have le : ∀ t ∈ toks, t ≤ D ∨ (16 ≤ t ∧ t ≤ 18) := by
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact treeTokens_le litLen lc D hD hl t h
    · exact treeTokens_le distLen dc D hD hd t h
  have lt : ∀ t ∈ toks, t < 19 := fun t ht => by rcases le t ht with h | h <;> omega
  have gm : ∀ g : Nat → Nat, (toks.map g).sum = mass (fun k => blFreq toks k * g k) 19 :=
    fun g => tokens_mass g toks lt
  refine ⟨le, ?_, ?_, gm⟩
  · have := gm (fun _ => 1)
    rw [sum_ones] at this
    rw [this]
    exact mass_congr fun k _ => by simp
  · have a := treeTokens_length litLen lc
    have b := treeTokens_length distLen dc
    simp only [toks, allTokens, List.length_append]
    omega

theorem tcost_two (a b : Nat → Nat) : ∀ l : List Nat,
    tcost (fun k => 2 * (a k + b k)) l = 2 * ((l.map a).sum + (l.map b).sum)
  | [] => rfl
  | t :: l => by
    have := tcost_two a b l
    simp only [tcost, List.map_cons, List.sum_cons] at this ⊢
    omega

theorem tcost_two_one (a b : Nat → Nat) : ∀ l : List Nat,
    tcost (fun k => 2 * (a k + b k) + 1) l = 2 * ((l.map a).sum + (l.map b).sum) + l.length
  | [] => rfl
  | t :: l => by
    have := tcost_two_one a b l
    simp only [tcost, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    omega

theorem header_tokens (litLen distLen : Nat → Nat) (lc dc : Nat) :
    headerBits litLen lc distLen dc ≤ 71 +
      ((allTokens litLen lc distLen dc).map (treeLengths 19 7 (blFreq (allTokens litLen lc distLen dc)))).sum +
      ((allTokens litLen lc distLen dc).map blExtra).sum := by
  dsimp only [headerBits]
  have := blMaxIndex_le (treeLengths 19 7 (blFreq (allTokens litLen lc distLen dc))) 18
  have := sum_map_add (treeLengths 19 7 (blFreq (allTokens litLen lc distLen dc))) blExtra
    (allTokens litLen lc distLen dc)
  omega

/-! ## `lit_bufsize = 256` -/

def litA256 (i : Nat) : Nat := if i ≤ 256 then 6 else 0
def litB256 (i : Nat) : Nat := if i ≤ 256 then 2 else 4

/-- The bit-length symbols that can occur at `lit_bufsize = 256`: lengths up to 11 and 16..18. -/
def allowed256 (v : Nat) : Bool := decide (v ≤ 11 ∨ 16 ≤ v)

theorem charges_256 :
    ScanCharges (fun k => 2 * (refLen k + blExtra k)) otherRegionCharge256 litA256 litB256 ∧
    ScanCharges (fun k => 2 * (refLen k + blExtra k)) otherRegionCharge256 (fun _ => 0) (fun _ => 4) := by
  have short : ∀ x, 1 ≤ x → x ≤ 15 → 2 * (refLen x + blExtra x) ≤ otherRegionCharge256 x := by
    intro x h1 h2
    simp [blExtra_zero h2, otherRegionCharge256, show x ≠ 0 by omega]
  have rep : ∀ x, 1 ≤ x → x ≤ 15 → 2 * (refLen 16 + blExtra 16) ≤ 3 * otherRegionCharge256 x := by
    intro x h1 h2
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
      simp [refLen, otherRegionCharge256, blExtra] at h1 h2 ⊢
  have w0 : 2 * (refLen 0 + blExtra 0) = 4 := rfl
  have w17 : 2 * (refLen 17 + blExtra 17) = 12 := rfl
  have w18 : 2 * (refLen 18 + blExtra 18) = 28 := rfl
  refine ⟨⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩, ⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> intro i <;>
    simp only [litA256, litB256, w0, w17, w18] <;> (try split) <;> omega

/-- **The header at `lit_bufsize = 256`.** -/
theorem header_256 (litLen distLen : Nat → Nat) (lc dc : Nat) (hlc : 257 ≤ lc) (hlc2 : lc ≤ 286) (hdc : dc ≤ 30)
    (hl : ∀ i, i < lc → litLen i ≤ 11) (hd : ∀ i, i < dc → distLen i ≤ 11) (h256 : litLen 256 ≠ 0) :
    2 * headerBits litLen lc distLen dc ≤ 2 * (71 + 245) + mass (fun v => literalCharge256 v (litLen v)) 286 +
      mass (fun v => otherRegionCharge256 (distLen v)) 30 := by
  have hdr := header_tokens litLen distLen lc dc
  obtain ⟨le, wEq, lenLe, gm⟩ := tokens_facts litLen distLen lc dc 11 (by omega) hl hd
  generalize hT : allTokens litLen lc distLen dc = toks at *
  have bl := bl_cost_le_15 (blFreq toks) allowed256 7 refLen
    (fun v _ hv => by
      have : v ∈ toks := List.count_pos_iff.mp (Nat.pos_of_ne_zero hv)
      simp only [allowed256, decide_eq_true_eq]; rcases le v this with h | h <;> omega)
    (by decide) (by decide +kernel) (by decide +kernel) (by omega)
  rw [← gm, ← gm] at bl
  have scanL := tree_region litLen _ _ _ _ charges_256.1 lc (fun i hi => by have := hl i hi; omega)
    (fun i _ z => by
      have : i ≠ 256 := fun e => h256 (e ▸ z)
      simp only [litA256, litB256]
      by_cases r : i ≤ 255
      · simp [show i + 1 ≤ 256 by omega, show i ≤ 256 by omega]
      · simp [show ¬ (i + 1 ≤ 256) by omega, show ¬ (i ≤ 256) by omega])
  have scanD := tree_region distLen _ _ _ _ charges_256.2 dc (fun i hi => by have := hd i hi; omega)
    (fun _ _ _ => ⟨rfl, rfl⟩)
  have endA : litA256 lc = 0 := by simp [litA256, show ¬ (lc ≤ 256) by omega]
  have chL : mass (regionCharge litLen otherRegionCharge256 litA256 litB256) lc ≤
      mass (fun v => literalCharge256 v (litLen v)) 286 := by
    refine Nat.le_trans (Nat.le_of_eq (mass_congr fun i _ => ?_)) (mass_le_of_le _ hlc2)
    unfold regionCharge literalCharge256 literalRegionCharge256 otherRegionCharge256 litA256 litB256
    by_cases r : i ≤ 256 <;> by_cases z : litLen i = 0 <;> simp [r, z]
  have chD : mass (regionCharge distLen otherRegionCharge256 (fun _ => 0) (fun _ => 4)) dc ≤
      mass (fun v => otherRegionCharge256 (distLen v)) 30 := by
    refine Nat.le_trans (Nat.le_of_eq (mass_congr fun i _ => ?_)) (mass_le_of_le _ hdc)
    unfold regionCharge otherRegionCharge256
    by_cases z : distLen i = 0 <;> simp [z]
  have split := tcost_two refLen blExtra toks
  have both : tcost (fun k => 2 * (refLen k + blExtra k)) toks =
      tcost (fun k => 2 * (refLen k + blExtra k)) (treeTokens litLen lc) +
        tcost (fun k => 2 * (refLen k + blExtra k)) (treeTokens distLen dc) := by
    rw [← hT]; exact tcost_append _ _ _
  rw [endA] at scanL
  omega

/-! ## `lit_bufsize = 128` -/

def litA128 (i : Nat) : Nat := if i ≤ 256 then 10 else 2
def litB128 (i : Nat) : Nat := if i ≤ 256 then 1 else 4

/-- The bit-length symbols that can occur at `lit_bufsize = 128`: lengths up to 9 and 16..18. -/
def allowed128 (v : Nat) : Bool := decide (v ≤ 9 ∨ 16 ≤ v)

theorem charges_128 :
    ScanCharges (fun k => 2 * (refLen1 k + blExtra k) + 1) distanceRegionCharge128 litA128 litB128 ∧
    ScanCharges (fun k => 2 * (refLen1 k + blExtra k) + 1) distanceRegionCharge128 (fun _ => 0) (fun _ => 5) := by
  have short : ∀ x, 1 ≤ x → x ≤ 15 → 2 * (refLen1 x + blExtra x) + 1 ≤ distanceRegionCharge128 x := by
    intro x h1 h2
    simp [blExtra_zero h2, distanceRegionCharge128, show x ≠ 0 by omega]
  have rep : ∀ x, 1 ≤ x → x ≤ 15 → 2 * (refLen1 16 + blExtra 16) + 1 ≤ 3 * distanceRegionCharge128 x := by
    intro x h1 h2
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
      simp [refLen1, distanceRegionCharge128, blExtra] at h1 h2 ⊢
  have w0 : 2 * (refLen1 0 + blExtra 0) + 1 = 5 := rfl
  have w17 : 2 * (refLen1 17 + blExtra 17) + 1 = 13 := rfl
  have w18 : 2 * (refLen1 18 + blExtra 18) + 1 = 21 := rfl
  refine ⟨⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩, ⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> intro i <;>
    simp only [litA128, litB128, w0, w17, w18] <;> (try split) <;> omega

/-- **The header at `lit_bufsize = 128`.** -/
theorem header_128 (litLen distLen : Nat → Nat) (lc dc : Nat) (hlc : 257 ≤ lc) (hlc2 : lc ≤ 286) (hdc : dc ≤ 30)
    (hl : ∀ i, i < lc → litLen i ≤ 9) (hd : ∀ i, i < dc → distLen i ≤ 9) (h256 : litLen 256 ≠ 0) :
    2 * headerBits litLen lc distLen dc ≤ 2 * (71 + 30) + mass (fun v => literalCharge128 v (litLen v)) 286 +
      mass (fun v => distanceRegionCharge128 (distLen v)) 30 := by
  have hdr := header_tokens litLen distLen lc dc
  obtain ⟨le, wEq, lenLe, gm⟩ := tokens_facts litLen distLen lc dc 9 (by omega) hl hd
  generalize hT : allTokens litLen lc distLen dc = toks at *
  have bl := bl_cost_le_13 (blFreq toks) allowed128 8 refLen1
    (fun v _ hv => by
      have : v ∈ toks := List.count_pos_iff.mp (Nat.pos_of_ne_zero hv)
      simp only [allowed128, decide_eq_true_eq]; rcases le v this with h | h <;> omega)
    (by decide) (by decide +kernel) (by decide +kernel) (by omega)
  rw [← gm, ← gm, wEq] at bl
  have scanL := tree_region litLen _ _ _ _ charges_128.1 lc (fun i hi => by have := hl i hi; omega)
    (fun i _ z => by
      have : i ≠ 256 := fun e => h256 (e ▸ z)
      simp only [litA128, litB128]
      by_cases r : i ≤ 255
      · simp [show i + 1 ≤ 256 by omega, show i ≤ 256 by omega]
      · simp [show ¬ (i + 1 ≤ 256) by omega, show ¬ (i ≤ 256) by omega])
  have scanD := tree_region distLen _ _ _ _ charges_128.2 dc (fun i hi => by have := hd i hi; omega)
    (fun _ _ _ => ⟨rfl, rfl⟩)
  have endA : litA128 lc = 2 := by simp [litA128, show ¬ (lc ≤ 256) by omega]
  have chL : mass (regionCharge litLen distanceRegionCharge128 litA128 litB128) lc ≤
      mass (fun v => literalCharge128 v (litLen v)) 286 := by
    refine Nat.le_trans (Nat.le_of_eq (mass_congr fun i _ => ?_)) (mass_le_of_le _ hlc2)
    unfold regionCharge literalCharge128 literalRegionCharge128 lengthRegionCharge128 distanceRegionCharge128
      litA128 litB128
    by_cases r : i ≤ 256 <;> by_cases z : litLen i = 0 <;> simp [r, z] <;> omega
  have chD : mass (regionCharge distLen distanceRegionCharge128 (fun _ => 0) (fun _ => 5)) dc ≤
      mass (fun v => distanceRegionCharge128 (distLen v)) 30 := by
    refine Nat.le_trans (Nat.le_of_eq (mass_congr fun i _ => ?_)) (mass_le_of_le _ hdc)
    unfold regionCharge distanceRegionCharge128
    by_cases z : distLen i = 0 <;> simp [z]
  have split := tcost_two_one refLen1 blExtra toks
  have both : tcost (fun k => 2 * (refLen1 k + blExtra k) + 1) toks =
      tcost (fun k => 2 * (refLen1 k + blExtra k) + 1) (treeTokens litLen lc) +
        tcost (fun k => 2 * (refLen1 k + blExtra k) + 1) (treeTokens distLen dc) := by
    rw [← hT]; exact tcost_append _ _ _
  rw [endA] at scanL
  have half : 2 * (toks.length / 2) ≤ toks.length := Nat.mul_div_le _ _
  omega

end ZlibNgF.Math.Huff
