import ZlibF.Math.DeflateOverlaySmall

/-!
# Small-block dynamic overlay bounds (`lit_bufsize` 128 and 256)

At `lit_bufsize = 128` (`memLevel` 1) and `lit_bufsize = 256` (`memLevel` 2) the general header
bound of 2283 bits exceeds `8 * lit_bufsize`, so the order-free budget `H + bitExcess + 25 ≤ 8B`
(`H + bitExcess ≤ 999` and `≤ 2023`) uses the header and block-selection inequalities of the block
at hand:

* the **header bound** under a fixed reference bit-length code (`κ1` at `B = 128`, `κ0` at
  `B = 256`), charged per source-tree entry by region;
* the **choice inequality**: because `_tr_flush_block` chose the dynamic block over the fixed one,
  `H + Σ fl·ll + Σ fd·dl + 1 ≤ Σ fl·staticLen + 5·Σ fd`;
* **Kraft** on both data trees (`Σ 2^(15 − l) ≤ 2^15`), and the unclamped **Fibonacci depth bound**
  `f · F(l + 1) + F(l) ≤ W` on used symbols (while any forced leaf has `f = 0` and `l = 1`);
* the **symbol count** (`≤ B − 1` non-EOB symbols) and **match balance** (`Σ_{v≥257} fl = Σ fd`).

One parametric combination (`tiny_header_excess`) adds the header bound once and `b` copies of the
choice inequality, cancelling the dynamic and fixed symbol-length sums:

* at `B = 128`: `b = 2` (scale `2 + b = 4`), Kraft divisors `256` and `512`, symbol rates
  `14 + 8 = 22`;
* at `B = 256`: `b = 1` (scale `2 + b = 3`), Kraft divisors `64` and `256`, symbol rates
  `7 + 4 = 11`.
-/

namespace ZlibF.Math.DeflateOverlayTiny
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.HuffmanAbstract (fib fib_add_two fib_mono)
open ZlibF.Math.DeflateOverlaySmall (fib_values)
set_option autoImplicit false

/-- The 7-bit reference bit-length code `κ0` (symbols 0..18; 12..15 unused at `B = 256`). -/
def refLen : Nat → Nat
  | 0 => 2 | 1 => 7 | 2 => 7 | 3 => 5 | 4 => 5 | 5 => 4 | 6 => 4 | 7 => 4 | 8 => 4 | 9 => 3
  | 10 => 4 | 11 => 4 | 12 => 7 | 13 => 7 | 14 => 7 | 15 => 7 | 16 => 7 | 17 => 3 | 18 => 7
  | _ => 0

/-- The 8-bit reference bit-length code `κ1` (symbols 0..18; 10..15 unused at `B = 128`). -/
def refLen1 : Nat → Nat
  | 0 => 2 | 1 => 8 | 2 => 8 | 3 => 6 | 4 => 5 | 5 => 4 | 6 => 3 | 7 => 4 | 8 => 4 | 9 => 3
  | 10 => 7 | 11 => 7 | 12 => 7 | 13 => 7 | 14 => 7 | 15 => 7 | 16 => 7 | 17 => 3 | 18 => 3
  | _ => 0

/-- Extra bits of length code `c` (symbol `257 + c`). -/
def lengthExtra : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 8 => 1 | 9 => 1 | 10 => 1 | 11 => 1 | 12 => 2 | 13 => 2 | 14 => 2 | 15 => 2
  | 16 => 3 | 17 => 3 | 18 => 3 | 19 => 3 | 20 => 4 | 21 => 4 | 22 => 4 | 23 => 4
  | 24 => 5 | 25 => 5 | 26 => 5 | 27 => 5 | _ => 0

/-- Extra bits of distance code `c`. -/
def distanceExtra : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 2
  | 8 => 3 | 9 => 3 | 10 => 4 | 11 => 4 | 12 => 5 | 13 => 5 | 14 => 6 | 15 => 6
  | 16 => 7 | 17 => 7 | 18 => 8 | 19 => 8 | 20 => 9 | 21 => 9 | 22 => 10 | 23 => 10
  | 24 => 11 | 25 => 11 | 26 => 12 | 27 => 12 | 28 => 13 | 29 => 13 | _ => 0

/-- The Kraft share of a code length: `2^(15 − x)` for `x > 0`, `0` for `0`. -/
def kraftTerm (x : Nat) : Nat := if x = 0 then 0 else 2 ^ (15 - x)

/-- The fixed-block code length of literal/length symbol `v`. -/
def staticLen (v : Nat) : Nat := if v < 144 then 8 else if v < 256 then 9 else if v < 280 then 7 else 8

/-- Indicator of a nonzero code length. -/
def isUsed (x : Nat) : Nat := if x = 0 then 0 else 1

/-- Per-occurrence excess of literal/length symbol `v` at length `x`. -/
def literalExcess (v x : Nat) : Nat := if v < 257 then 0 else x + lengthExtra (v - 257) - 9

/-- Per-occurrence excess of distance code `v` at length `x`. -/
def distanceExcess (v x : Nat) : Nat := x + distanceExtra v - 15

/-- Region charges at `B = 256` (scaled by 2, under `κ0`). -/
def literalRegionCharge256 (x : Nat) : Nat := if x = 0 then 2 else 2 * refLen x + 6
def otherRegionCharge256 (x : Nat) : Nat := if x = 0 then 4 else 2 * refLen x
def literalCharge256 (v x : Nat) : Nat :=
  if v ≤ 256 then literalRegionCharge256 x else otherRegionCharge256 x

/-- Region charges at `B = 128` (scaled by 2, paying 1 per bit-length symbol, under `κ1`). -/
def literalRegionCharge128 (x : Nat) : Nat := if x = 0 then 1 else 2 * refLen1 x + 11
def lengthRegionCharge128 (x : Nat) : Nat := if x = 0 then 4 else 2 * refLen1 x + 3
def distanceRegionCharge128 (x : Nat) : Nat := if x = 0 then 5 else 2 * refLen1 x + 1
def literalCharge128 (v x : Nat) : Nat :=
  if v ≤ 256 then literalRegionCharge128 x else lengthRegionCharge128 x

/-- Unified leaf constraint in a tree of weight bound `W`: either unused/forced (`f = 0, x ≤ 1`) or
used (`1 ≤ f, 1 ≤ x, f · F(x + 1) + F(x) ≤ W`). -/
def LeafBound (W x f : Nat) : Prop :=
  (f = 0 ∧ x ≤ 1) ∨ (1 ≤ f ∧ 1 ≤ x ∧ f * fib (x + 1) + fib x ≤ W)

theorem mass_split (f : Nat → Nat) (a b : Nat) :
    mass f (a + b) = mass f a + mass (fun k => f (a + k)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show mass f (a + b) + f (a + b) = mass f a + (mass (fun k => f (a + k)) b + f (a + b))
    rw [ih]; omega

theorem mass_const (c n : Nat) : mass (fun _ => c) n = n * c := by
  induction n with
  | zero => simp [mass]
  | succ n ih => simp only [mass, ih, Nat.succ_mul]

theorem mass_div_le (f : Nat → Nat) {n d B : Nat} (hd : 0 < d) (h : mass f n ≤ B) :
    mass (fun v => f v / d) n ≤ B / d := by
  have step : mass (fun v => d * (f v / d)) n ≤ mass f n :=
    mass_mono fun v _ => Nat.mul_div_le (f v) d
  rw [mass_mul_left] at step
  exact (Nat.le_div_iff_mul_le hd).mpr (by rw [Nat.mul_comm]; omega)

theorem lengthExtra_lt (c : Nat) : lengthExtra c < 6 := by
  unfold lengthExtra; split <;> omega

theorem distanceExtra_lt (c : Nat) : distanceExtra c < 14 := by
  unfold distanceExtra; split <;> omega

theorem staticLen_lit {v : Nat} (_hv : v < 256) : staticLen v ≤ 9 := by
  unfold staticLen; repeat (first | split | omega)

theorem staticLen_len {v : Nat} (hv : 257 ≤ v) : staticLen v ≤ 8 := by
  unfold staticLen
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  split <;> omega

theorem leaf_len_le_9 {x f : Nat} (h : LeafBound 130 x f) : x ≤ 9 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, f12, _, _, _, _, _⟩ := fib_values
  rcases h with ⟨_, hx⟩ | ⟨hf, _, hfib⟩
  · omega
  · rcases Nat.lt_or_ge x 10 with lt | ge
    · omega
    · have mono : fib 12 ≤ fib (x + 2) := fib_mono (by omega)
      have step : fib (x + 2) = fib x + fib (x + 1) := fib_add_two x
      have mul : fib (x + 1) ≤ f * fib (x + 1) := Nat.le_mul_of_pos_left _ hf
      omega

theorem leaf_len_le_11 {x f : Nat} (h : LeafBound 258 x f) : x ≤ 11 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, f14, _, _, _⟩ := fib_values
  rcases h with ⟨_, hx⟩ | ⟨hf, _, hfib⟩
  · omega
  · rcases Nat.lt_or_ge x 12 with lt | ge
    · omega
    · have mono : fib 14 ≤ fib (x + 2) := fib_mono (by omega)
      have step : fib (x + 2) = fib x + fib (x + 1) := fib_add_two x
      have mul : fib (x + 1) ≤ f * fib (x + 1) := Nat.le_mul_of_pos_left _ hf
      omega

/-- **Parametric header-plus-excess bound.** Combining the region-charged header bound (`weight 1`)
with `b` copies of the dynamic-vs-fixed choice inequality cancels the dynamic and fixed length sums
and bounds `(2 + b) * (H + E_L + E_D) + b` by the Kraft budgets, symbol count, and per-entry caps. -/
theorem tiny_header_excess
    (cLit cLen cDist : Nat → Nat)
    (W N b divL divD rM rD capLit capEob : Nat) (capLen capDist : Nat → Nat)
    (hdL : 0 < divL) (hdD : 0 < divD)
    (entryLit : ∀ x f, LeafBound W x f →
      cLit x + b * (f * 9) ≤ kraftTerm x / divL + capLit + (rM + rD) * f + b * (f * x))
    (entryEob : ∀ x, 1 ≤ x → fib (x + 1) + fib x ≤ W →
      cLit x + b * 7 ≤ kraftTerm x / divL + capEob + b * x)
    (entryLen : ∀ x f e, e < 6 → LeafBound W x f →
      cLen x + b * (f * 8) + (2 + b) * (f * (x + e - 9)) ≤
        kraftTerm x / divL + capLen e + rM * f + b * (f * x))
    (entryDist : ∀ x f e, e < 14 → LeafBound W x f →
      cDist x + b * (f * 5) + (2 + b) * (f * (x + e - 15)) ≤
        kraftTerm x / divD + capDist e + rD * f + b * (f * x))
    (ll fl dl fd : Nat → Nat) (H H0 M : Nat)
    (kraftL : mass (fun v => kraftTerm (ll v)) 286 ≤ 2 ^ 15)
    (kraftD : mass (fun v => kraftTerm (dl v)) 30 ≤ 2 ^ 15)
    (leafL : ∀ v, v < 286 → v ≠ 256 → LeafBound W (ll v) (fl v))
    (eob : fl 256 = 1 ∧ 1 ≤ ll 256 ∧ fib (ll 256 + 1) + fib (ll 256) ≤ W)
    (leafD : ∀ v, v < 30 → LeafBound W (dl v) (fd v))
    (symbols : mass (fun v => if v = 256 then 0 else fl v) 286 ≤ N)
    (balance : mass (fun v => if v < 257 then 0 else fl v) 286 = mass fd 30)
    (header : 2 * H ≤ H0 + mass (fun v => if v ≤ 256 then cLit (ll v) else cLen (ll v)) 286 +
      mass (fun v => cDist (dl v)) 30)
    (choice : H + mass (fun v => fl v * ll v) 286 + mass (fun v => fd v * dl v) 30 + 1 ≤
      mass (fun v => fl v * staticLen v) 286 + 5 * mass fd 30)
    (budget : H0 + 2 ^ 15 / divL + 2 ^ 15 / divD + (rM + rD) * N +
      256 * capLit + capEob +
      mass (fun c => capLen (lengthExtra c)) 29 +
      mass (fun v => capDist (distanceExtra v)) 30 ≤ (2 + b) * M + 2 * b + 1) :
    H + mass (fun v => fl v * literalExcess v (ll v)) 286 +
      mass (fun v => fd v * distanceExcess v (dl v)) 30 ≤ M := by
  let allowL : Nat → Nat := fun v =>
    if v < 256 then capLit else if v = 256 then capEob else capLen (lengthExtra (v - 257))
  let rateL : Nat → Nat := fun v =>
    if v < 256 then rM + rD else if v = 256 then 0 else rM
  have pointL : ∀ v, v < 286 →
      (if v ≤ 256 then cLit (ll v) else cLen (ll v)) +
        b * (fl v * staticLen v) + (2 + b) * (fl v * literalExcess v (ll v)) ≤
      kraftTerm (ll v) / divL + allowL v + rateL v * fl v + b * (fl v * ll v) := by
    intro v hv
    by_cases h256 : v < 256
    · have ex0 : literalExcess v (ll v) = 0 := by simp [literalExcess, show v < 257 by omega]
      have sl : b * (fl v * staticLen v) ≤ b * (fl v * 9) :=
        Nat.mul_le_mul_left b (Nat.mul_le_mul_left (fl v) (staticLen_lit h256))
      have q := entryLit (ll v) (fl v) (leafL v hv (by omega))
      simp only [allowL, rateL, h256, show v ≤ 256 by omega, ite_true, ex0, Nat.mul_zero, Nat.add_zero]
      omega
    · by_cases heob : v = 256
      · subst heob
        have ex0 : literalExcess 256 (ll 256) = 0 := by simp [literalExcess]
        have sl7 : staticLen 256 = 7 := rfl
        have q := entryEob (ll 256) eob.2.1 eob.2.2
        simp only [allowL, rateL, show ¬ (256 < 256) by omega, Nat.le_refl, ite_true, ite_false,
          ex0, eob.1, sl7, Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
        omega
      · have exLen : literalExcess v (ll v) = ll v + lengthExtra (v - 257) - 9 := by
          simp [literalExcess, show ¬ v < 257 by omega]
        have sl : b * (fl v * staticLen v) ≤ b * (fl v * 8) :=
          Nat.mul_le_mul_left b (Nat.mul_le_mul_left (fl v) (staticLen_len (by omega)))
        have q := entryLen (ll v) (fl v) (lengthExtra (v - 257)) (lengthExtra_lt _) (leafL v hv heob)
        simp only [allowL, rateL, h256, heob, show ¬ v ≤ 256 by omega, ite_false, exLen]
        omega
  have pointD : ∀ v, v < 30 →
      cDist (dl v) + b * (fd v * 5) + (2 + b) * (fd v * distanceExcess v (dl v)) ≤
      kraftTerm (dl v) / divD + capDist (distanceExtra v) + rD * fd v + b * (fd v * dl v) := by
    intro v hv
    exact entryDist (dl v) (fd v) (distanceExtra v) (distanceExtra_lt v) (leafD v hv)
  have sumL := mass_mono pointL
  have sumD := mass_mono pointD
  simp only [mass_add, mass_mul_left] at sumL sumD
  have kL := mass_div_le (fun v => kraftTerm (ll v)) hdL kraftL
  have kD := mass_div_le (fun v => kraftTerm (dl v)) hdD kraftD
  have allowSum : mass allowL 286 =
      256 * capLit + capEob + mass (fun c => capLen (lengthExtra c)) 29 := by
    rw [show 286 = 256 + 30 from rfl, mass_split, show 30 = 1 + 29 from rfl, mass_split]
    have p1 : mass allowL 256 = 256 * capLit := by
      rw [← mass_const]; exact mass_congr fun v hv => by simp [allowL, hv]
    have p2 : mass (fun k => allowL (256 + k)) 1 = capEob := by
      simp [mass, allowL]
    have p3 : mass (fun k => allowL (256 + (1 + k))) 29 = mass (fun c => capLen (lengthExtra c)) 29 := by
      apply mass_congr; intro c _hc
      simp [allowL, show ¬ (256 + (1 + c) < 256) by omega, show 256 + (1 + c) - 257 = c by omega]
    rw [p1, p2, p3]; omega
  have rateSum : mass (fun v => rateL v * fl v) 286 =
      (rM + rD) * mass (fun v => if v < 256 then fl v else 0) 286 +
        rM * mass (fun v => if v < 257 then 0 else fl v) 286 := by
    rw [← mass_mul_left, ← mass_mul_left, ← mass_add]
    apply mass_congr; intro v _
    simp only [rateL]
    by_cases a : v < 256
    · simp [a, show v < 257 by omega]
    · by_cases e : v = 256
      · subst e; simp
      · simp [a, e, show ¬ v < 257 by omega]
  have symSplit : mass (fun v => if v = 256 then 0 else fl v) 286 =
      mass (fun v => if v < 256 then fl v else 0) 286 +
        mass (fun v => if v < 257 then 0 else fl v) 286 := by
    rw [← mass_add]
    apply mass_congr; intro v _
    by_cases a : v < 256
    · simp [a, show v ≠ 256 by omega, show v < 257 by omega]
    · by_cases e : v = 256
      · subst e; simp
      · simp [a, e, show ¬ v < 257 by omega]
  have fd5 : mass (fun v => fd v * 5) 30 = 5 * mass fd 30 := by
    rw [mass_mul_right, Nat.mul_comm]
  rw [allowSum, rateSum] at sumL
  rw [fd5, ← balance] at sumD
  have freqBound : (rM + rD) * mass (fun v => if v < 256 then fl v else 0) 286 +
      rM * mass (fun v => if v < 257 then 0 else fl v) 286 +
      rD * mass (fun v => if v < 257 then 0 else fl v) 286 ≤ (rM + rD) * N := by
    have eq : (rM + rD) * mass (fun v => if v < 256 then fl v else 0) 286 +
        rM * mass (fun v => if v < 257 then 0 else fl v) 286 +
        rD * mass (fun v => if v < 257 then 0 else fl v) 286 =
        (rM + rD) * mass (fun v => if v = 256 then 0 else fl v) 286 := by
      rw [symSplit, Nat.mul_add, Nat.add_assoc, ← Nat.add_mul]
    rw [eq]
    exact Nat.mul_le_mul_left (rM + rD) symbols
  have choiceB := Nat.mul_le_mul_left b choice
  rw [← balance] at choiceB
  simp only [Nat.mul_add, Nat.mul_one] at choiceB
  have hbH : 2 * H + b * H = (2 + b) * H := (Nat.add_mul 2 b H).symm
  let X := H + mass (fun v => fl v * literalExcess v (ll v)) 286 +
    mass (fun v => fd v * distanceExcess v (dl v)) 30
  have hX : (2 + b) * X = (2 + b) * H +
      (2 + b) * mass (fun v => fl v * literalExcess v (ll v)) 286 +
      (2 + b) * mass (fun v => fd v * distanceExcess v (dl v)) 30 := by
    simp only [X, Nat.mul_add]
  have scaled : (2 + b) * X + b ≤ (2 + b) * M + 2 * b + 1 := by omega
  by_cases le : X ≤ M
  · exact le
  · have lo : (2 + b) * (M + 1) ≤ (2 + b) * X := Nat.mul_le_mul_left (2 + b) (by omega)
    rw [Nat.mul_add, Nat.mul_one] at lo
    omega

/-! ## Instantiation at `lit_bufsize = 128` (`memLevel` 1) -/

/-- Per-code cap of a length code with `e` extra bits at `B = 128` (`b = 2`, scale `4`). -/
def capLen128 : Nat → Nat
  | 3 => 5 | 4 => 9 | 5 => 17 | _ => 4

/-- Per-code cap of a distance code with `e` extra bits at `B = 128` (`b = 2`, scale `4`). -/
def capDist128 : Nat → Nat
  | 10 => 7 | 11 => 15 | 12 => 29 | 13 => 67 | _ => 5

theorem entry_lit_128 (x f : Nat) (h : LeafBound 130 x f) :
    literalRegionCharge128 x + 2 * (f * 9) ≤ kraftTerm x / 256 + 1 + 22 * f + 2 * (f * x) := by
  have hx := leaf_len_le_9 h
  rcases h with ⟨rfl, hx1⟩ | ⟨hf, hx1, _⟩ <;>
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
    simp [literalRegionCharge128, refLen1, kraftTerm] at hx hx1 ⊢ <;> omega

theorem entry_eob_128 (x : Nat) (hx1 : 1 ≤ x) (hfib : fib (x + 1) + fib x ≤ 130) :
    literalRegionCharge128 x + 2 * 7 ≤ kraftTerm x / 256 + 19 + 2 * x := by
  have hx := leaf_len_le_9 (Or.inr ⟨Nat.le_refl 1, hx1, by simpa using hfib⟩)
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
    simp [literalRegionCharge128, refLen1, kraftTerm] at hx hx1 ⊢ <;> omega

theorem entry_len_128 (x f e : Nat) (he : e < 6) (h : LeafBound 130 x f) :
    lengthRegionCharge128 x + 2 * (f * 8) + 4 * (f * (x + e - 9)) ≤
      kraftTerm x / 256 + capLen128 e + 14 * f + 2 * (f * x) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, _, _, _, _, _, _, _⟩ := fib_values
  have hx := leaf_len_le_9 h
  have capLo : 4 ≤ capLen128 e := by unfold capLen128; split <;> omega
  rcases h with ⟨rfl, hx1⟩ | ⟨hf, hx1, hfib⟩
  · rcases x with _ | _ | x <;>
      simp [lengthRegionCharge128, refLen1, kraftTerm] at hx1 ⊢ <;> omega
  · by_cases h4 : x ≤ 4
    · have ex0 : x + e - 9 = 0 := by omega
      rw [ex0, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      rcases x with _ | _ | _ | _ | _ | x <;>
        simp [lengthRegionCharge128, refLen1, kraftTerm] at hx1 h4 ⊢ <;> omega
    · rcases e with _ | _ | _ | _ | _ | _ | e <;>
        rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
        simp only [lengthRegionCharge128, refLen1, kraftTerm, capLen128, reduceIte,
          Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceDiv,
          f5, f6, f7, f8, f9, f10] at he hx h4 hfib ⊢ <;> omega

theorem entry_dist_128 (x f e : Nat) (he : e < 14) (h : LeafBound 130 x f) :
    distanceRegionCharge128 x + 2 * (f * 5) + 4 * (f * (x + e - 15)) ≤
      kraftTerm x / 512 + capDist128 e + 8 * f + 2 * (f * x) := by
  obtain ⟨_, _, _, _, _, f5, f6, f7, f8, f9, f10, _, _, _, _, _, _, _⟩ := fib_values
  have hx := leaf_len_le_9 h
  have capLo : 5 ≤ capDist128 e := by unfold capDist128; split <;> omega
  rcases h with ⟨rfl, hx1⟩ | ⟨hf, hx1, hfib⟩
  · rcases x with _ | _ | x <;>
      simp [distanceRegionCharge128, refLen1, kraftTerm] at hx1 ⊢ <;> omega
  · by_cases he9 : e ≤ 9
    · have fSlope : (if 4 ≤ x then 4 else 0) + 2 * (f * 5) + 4 * (f * (x + e - 15)) ≤ 8 * f + 2 * (f * x) := by
        have base : f * ((if 4 ≤ x then 4 else 0) + 10 + 4 * (x + e - 15)) ≤ f * (8 + 2 * x) :=
          Nat.mul_le_mul_left f (by split <;> omega)
        have lo : (if 4 ≤ x then 4 else 0) ≤ f * (if 4 ≤ x then 4 else 0) := Nat.le_mul_of_pos_left _ hf
        simp only [Nat.mul_add] at base
        have m1 : f * 10 = 2 * (f * 5) := by omega
        have m2 : f * (4 * (x + e - 15)) = 4 * (f * (x + e - 15)) := by rw [← Nat.mul_assoc, Nat.mul_comm f 4, Nat.mul_assoc]
        have m3 : f * (2 * x) = 2 * (f * x) := by rw [← Nat.mul_assoc, Nat.mul_comm f 2, Nat.mul_assoc]
        omega
      rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
        simp [distanceRegionCharge128, refLen1, kraftTerm] at hx hx1 fSlope ⊢ <;> omega
    · have eCases : e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13 := by omega
      rcases eCases with rfl | rfl | rfl | rfl <;>
        rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
        simp only [distanceRegionCharge128, refLen1, kraftTerm, capDist128, reduceIte,
          Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceDiv,
          f5, f6, f7, f8, f9, f10] at hx hx1 hfib ⊢ <;> omega

theorem cap_sums_128 :
    mass (fun c => capLen128 (lengthExtra c)) 29 = 192 ∧
    mass (fun v => capDist128 (distanceExtra v)) 30 = 346 := ⟨rfl, rfl⟩

/-- **The `memLevel` 1 bound (`lit_bufsize = 128`)**: `H + E ≤ 999` for `Δ ≤ 30`. -/
theorem header_excess_cert_128 (ll fl dl fd : Nat → Nat) (H Δ : Nat) (small : Δ ≤ 30)
    (kraftL : mass (fun v => kraftTerm (ll v)) 286 ≤ 2 ^ 15)
    (kraftD : mass (fun v => kraftTerm (dl v)) 30 ≤ 2 ^ 15)
    (leafL : ∀ v, v < 286 → v ≠ 256 → LeafBound 130 (ll v) (fl v))
    (eob : fl 256 = 1 ∧ 1 ≤ ll 256 ∧ fib (ll 256 + 1) + fib (ll 256) ≤ 130)
    (leafD : ∀ v, v < 30 → LeafBound 130 (dl v) (fd v))
    (symbols : mass (fun v => if v = 256 then 0 else fl v) 286 ≤ 127)
    (balance : mass (fun v => if v < 257 then 0 else fl v) 286 = mass fd 30)
    (header : 2 * H ≤ 2 * (71 + Δ) + mass (fun v => literalCharge128 v (ll v)) 286 +
      mass (fun v => distanceRegionCharge128 (dl v)) 30)
    (choice : H + mass (fun v => fl v * ll v) 286 + mass (fun v => fd v * dl v) 30 + 1 ≤
      mass (fun v => fl v * staticLen v) 286 + 5 * mass fd 30) :
    H + mass (fun v => fl v * literalExcess v (ll v)) 286 +
      mass (fun v => fd v * distanceExcess v (dl v)) 30 ≤ 999 := by
  exact tiny_header_excess literalRegionCharge128 lengthRegionCharge128 distanceRegionCharge128
    130 127 2 256 512 14 8 1 19 capLen128 capDist128 (by omega) (by omega)
    entry_lit_128 entry_eob_128 entry_len_128 entry_dist_128
    ll fl dl fd H (2 * (71 + Δ)) 999 kraftL kraftD leafL eob leafD symbols balance header choice
    (by rw [cap_sums_128.1, cap_sums_128.2]; omega)

/-! ## Instantiation at `lit_bufsize = 256` (`memLevel` 2) -/

/-- Per-code cap of a length code with `e` extra bits at `B = 256` (`b = 1`, scale `3`). -/
def capLen256 : Nat → Nat
  | 0 => 4 | 1 => 7 | 2 => 10 | 3 => 14 | 4 => 21 | _ => 37

/-- Per-code cap of a distance code with `e` extra bits at `B = 256` (`b = 1`, scale `3`). -/
def capDist256 : Nat → Nat
  | 7 => 7 | 8 => 10 | 9 => 14 | 10 => 22 | 11 => 40 | 12 => 82 | 13 => 159 | _ => 4

theorem entry_lit_256 (x f : Nat) (h : LeafBound 258 x f) :
    literalRegionCharge256 x + 1 * (f * 9) ≤ kraftTerm x / 64 + 2 + 11 * f + 1 * (f * x) := by
  have hx := leaf_len_le_11 h
  rcases h with ⟨rfl, hx1⟩ | ⟨hf, hx1, _⟩ <;>
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
    simp [literalRegionCharge256, refLen, kraftTerm] at hx hx1 ⊢ <;> omega

theorem entry_eob_256 (x : Nat) (hx1 : 1 ≤ x) (hfib : fib (x + 1) + fib x ≤ 258) :
    literalRegionCharge256 x + 1 * 7 ≤ kraftTerm x / 64 + 11 + 1 * x := by
  have hx := leaf_len_le_11 (Or.inr ⟨Nat.le_refl 1, hx1, by simpa using hfib⟩)
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
    simp [literalRegionCharge256, refLen, kraftTerm] at hx hx1 ⊢ <;> omega

theorem entry_len_256 (x f e : Nat) (he : e < 6) (h : LeafBound 258 x f) :
    otherRegionCharge256 x + 1 * (f * 8) + 3 * (f * (x + e - 9)) ≤
      kraftTerm x / 64 + capLen256 e + 7 * f + 1 * (f * x) := by
  obtain ⟨_, _, _, _, _, f5, f6, f7, f8, f9, f10, f11, f12, _, _, _, _, _⟩ := fib_values
  have hx := leaf_len_le_11 h
  have capLo : 4 ≤ capLen256 e := by unfold capLen256; split <;> omega
  rcases h with ⟨rfl, hx1⟩ | ⟨hf, hx1, hfib⟩
  · rcases x with _ | _ | x <;>
      simp [otherRegionCharge256, refLen, kraftTerm] at hx1 ⊢ <;> omega
  · by_cases h4 : x ≤ 4
    · have ex0 : x + e - 9 = 0 := by omega
      rw [ex0, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      rcases x with _ | _ | _ | _ | _ | x <;>
        simp [otherRegionCharge256, refLen, kraftTerm] at hx1 h4 ⊢ <;> omega
    · rcases e with _ | _ | _ | _ | _ | _ | e <;>
        rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
        simp only [otherRegionCharge256, refLen, kraftTerm, capLen256, reduceIte,
          Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceDiv,
          f5, f6, f7, f8, f9, f10, f11, f12] at he hx h4 hfib ⊢ <;> omega

theorem entry_dist_256 (x f e : Nat) (he : e < 14) (h : LeafBound 258 x f) :
    otherRegionCharge256 x + 1 * (f * 5) + 3 * (f * (x + e - 15)) ≤
      kraftTerm x / 256 + capDist256 e + 4 * f + 1 * (f * x) := by
  obtain ⟨_, _, _, _, f4, f5, f6, f7, f8, f9, f10, f11, f12, _, _, _, _, _⟩ := fib_values
  have hx := leaf_len_le_11 h
  have capLo : 4 ≤ capDist256 e := by unfold capDist256; split <;> omega
  rcases h with ⟨rfl, hx1⟩ | ⟨hf, hx1, hfib⟩
  · rcases x with _ | _ | x <;>
      simp [otherRegionCharge256, refLen, kraftTerm] at hx1 ⊢ <;> omega
  · by_cases he6 : e ≤ 6
    · have fSlope : (if 6 ≤ x then 4 else 0) + 1 * (f * 5) + 3 * (f * (x + e - 15)) ≤ 4 * f + 1 * (f * x) := by
        have base : f * ((if 6 ≤ x then 4 else 0) + 5 + 3 * (x + e - 15)) ≤ f * (4 + x) :=
          Nat.mul_le_mul_left f (by split <;> omega)
        have lo : (if 6 ≤ x then 4 else 0) ≤ f * (if 6 ≤ x then 4 else 0) := Nat.le_mul_of_pos_left _ hf
        simp only [Nat.mul_add] at base
        have m2 : f * (3 * (x + e - 15)) = 3 * (f * (x + e - 15)) := by rw [← Nat.mul_assoc, Nat.mul_comm f 3, Nat.mul_assoc]
        omega
      rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
        simp [otherRegionCharge256, refLen, kraftTerm] at hx hx1 fSlope ⊢ <;> omega
    · have eCases : e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13 := by omega
      rcases eCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
        simp only [otherRegionCharge256, refLen, kraftTerm, capDist256, reduceIte,
          Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceDiv,
          f4, f5, f6, f7, f8, f9, f10, f11, f12] at hx hx1 hfib ⊢ <;> omega

theorem cap_sums_256 :
    mass (fun c => capLen256 (lengthExtra c)) 29 = 392 ∧
    mass (fun v => capDist256 (distanceExtra v)) 30 = 732 := ⟨rfl, rfl⟩

/-- **The `memLevel` 2 bound (`lit_bufsize = 256`)**: `H + E ≤ 2023` for `Δ ≤ 419`. -/
theorem header_excess_cert_256 (ll fl dl fd : Nat → Nat) (H Δ : Nat) (small : Δ ≤ 419)
    (kraftL : mass (fun v => kraftTerm (ll v)) 286 ≤ 2 ^ 15)
    (kraftD : mass (fun v => kraftTerm (dl v)) 30 ≤ 2 ^ 15)
    (leafL : ∀ v, v < 286 → v ≠ 256 → LeafBound 258 (ll v) (fl v))
    (eob : fl 256 = 1 ∧ 1 ≤ ll 256 ∧ fib (ll 256 + 1) + fib (ll 256) ≤ 258)
    (leafD : ∀ v, v < 30 → LeafBound 258 (dl v) (fd v))
    (symbols : mass (fun v => if v = 256 then 0 else fl v) 286 ≤ 255)
    (balance : mass (fun v => if v < 257 then 0 else fl v) 286 = mass fd 30)
    (header : 2 * H ≤ 2 * (71 + Δ) + mass (fun v => literalCharge256 v (ll v)) 286 +
      mass (fun v => otherRegionCharge256 (dl v)) 30)
    (choice : H + mass (fun v => fl v * ll v) 286 + mass (fun v => fd v * dl v) 30 + 1 ≤
      mass (fun v => fl v * staticLen v) 286 + 5 * mass fd 30) :
    H + mass (fun v => fl v * literalExcess v (ll v)) 286 +
      mass (fun v => fd v * distanceExcess v (dl v)) 30 ≤ 2023 := by
  exact tiny_header_excess literalRegionCharge256 otherRegionCharge256 otherRegionCharge256
    258 255 1 64 256 7 4 2 11 capLen256 capDist256 (by omega) (by omega)
    entry_lit_256 entry_eob_256 entry_len_256 entry_dist_256
    ll fl dl fd H (2 * (71 + Δ)) 2023 kraftL kraftD leafL eob leafD symbols balance header choice
    (by rw [cap_sums_256.1, cap_sums_256.2]; omega)

#print axioms header_excess_cert_128
#print axioms header_excess_cert_256

end ZlibF.Math.DeflateOverlayTiny
