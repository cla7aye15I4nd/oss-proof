import ZlibNgF.Proof.«trees.c.alltrees»
import ZlibNgF.Math.OverlayChoice

/-!
# Model and code of a dynamic block: tables, symbols, costs (`ZlibNgF`)

* The code tables of `trees_tbl.h` / `deflate.h` against the RFC 1951 tables of the model (`decide +kernel`):
  `zng_length_code` is `lengthCode`, `zng_dist_code` (through `d_code`, `dCodeOf`) is `distanceCode`, the extra bits
  `extra_lbits` / `extra_dbits` / `extra_blbits` and those packed in `lmask_extra` / `dmask_extra` are `lengthExtra` /
  `distanceExtra` / `blExtra`, `bl_order` is `blOrder`, `static_ltree[v].Len` is `staticLitLen v` and
  `static_dtree[c].Len` is 5.
* The tallied symbols of `sym_buf` as the model's `Symbol` list (`symsOf`): valid, and (`SymOk`) the frequencies of
  `dyn_ltree` / `dyn_dtree` are the model's `litFreq` / `distFreq`.
* The heap cost of a symbol (`symCost`, the bits `compress_block` sends) is the model's `symbolCost` under the code
  lengths of the trees, so the heap `blockCosts` is the model's `blockCosts`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesDyn
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv
open ZlibNgF.Math.Huff ZlibNgF.Math.HuffSymbols ZlibNgF.Math.OverlayDynamic

/-! ## Tables -/

theorem lc_eq : ∀ v : Fin 256, (zng_length_code[v.val]!).toNat = lengthCode v.val := by decide +kernel

theorem dc_lo : ∀ x : Fin 256, (zng_dist_code[x.val]!).toNat = distanceCode x.val := by decide +kernel

theorem dc_hi : ∀ x : Fin 256, x.val < 2 ∨ (zng_dist_code[256 + x.val]!).toNat = distanceCode (x.val * 128) := by
  decide +kernel

theorem distBase_form : ∀ b ∈ distBase, b ≤ 257 ∨ b % 128 = 1 := by decide +kernel

/-- Above 256 the distance code is constant on blocks of 128 distances. -/
theorem distanceCode_blk (q r : Nat) (hq : 2 ≤ q) (hr : r < 128) :
    distanceCode (q * 128 + r) = distanceCode (q * 128) := by
  unfold distanceCode
  congr 2
  refine List.filter_congr fun x hx => ?_
  rcases distBase_form x hx with h | h
  · simp only [decide_eq_decide]; omega
  · simp only [decide_eq_decide]; omega

theorem lx_eq : ∀ c : Fin 29, (lmask_extra[c.val]!.toUInt32 >>> 8).toNat = lengthExtra c.val := by decide +kernel

theorem dx_eq : ∀ c : Fin 30, (dmask_extra[c.val]! >>> 16).toNat = distanceExtra c.val := by decide +kernel

theorem elb_eq : ∀ c : Fin 29, (extra_lbits[c.val]!).toInt = lengthExtra c.val := by decide +kernel

theorem edb_eq : ∀ c : Fin 30, (extra_dbits[c.val]!).toInt = distanceExtra c.val := by decide +kernel

theorem eblb_eq : ∀ c : Fin 19, (extra_blbits[c.val]!).toInt = blExtra c.val := by decide +kernel

theorem sl_eq : ∀ v : Fin 288, (static_ltree[v.val]!).dl.toNat = staticLitLen v.val := by decide +kernel

theorem sd_eq : ∀ c : Fin 30, (static_dtree[c.val]!).dl.toNat = 5 := by decide +kernel

theorem dCodeOf_eq (x : Nat) (hx : x < 32768) : dCodeOf x = distanceCode x := by
  unfold dCodeOf
  split
  · exact dc_lo ⟨x, by omega⟩
  · rename_i h
    have := dc_hi ⟨x / 128, by omega⟩
    dsimp only at this
    rcases this with h2 | h2
    · omega
    · rw [h2, ← distanceCode_blk (x / 128) (x % 128) (by omega) (by omega), Nat.div_add_mod']

theorem lengthCode_eq (v : Nat) (hv : v < 256) : (zng_length_code[v]!).toNat = lengthCode v := lc_eq ⟨v, hv⟩

/-! ## The tallied symbols -/

/-- Tallied symbol `j` (bytes `d` from `sym_buf` offset `sbo`) as a model symbol: its distance and its byte 2 (the
literal, or the match length minus 3). -/
def symAt (d : Array UInt8) (sbo j : Nat) : Symbol := ⟨symDist d sbo j, d[sbo + 3 * j + 2]!.toNat⟩

/-- The first `n` tallied symbols. -/
def symsOf (d : Array UInt8) (sbo n : Nat) : List Symbol := (List.range n).map (symAt d sbo)

theorem symsOf_length (d : Array UInt8) (sbo n : Nat) : (symsOf d sbo n).length = n := by simp [symsOf]

theorem symsOf_valid {d : Array UInt8} {sbo n : Nat} (hd : ∀ j, j < n → symDist d sbo j ≤ 32768) :
    ∀ s ∈ symsOf d sbo n, s.Valid := by
  intro s hs
  simp only [symsOf, List.mem_map, List.mem_range] at hs
  obtain ⟨j, hj, rfl⟩ := hs
  exact ⟨hd j hj, (d[sbo + 3 * j + 2]!).toNat_lt⟩

theorem countKey_map {α β : Type} (key : β → Option Nat) (f : α → β) (k : Nat) :
    ∀ l : List α, countKey key (l.map f) k = l.countP (fun x => key (f x) = some k)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, countKey, List.countP_cons, countKey_map key f k l]
    by_cases h : key (f x) = some k <;> simp [h] <;> omega

theorem literalKey_eq (d : Array UInt8) (sbo j : Nat) :
    (symAt d sbo j).literalKey lengthCode = symLCode d sbo j := by
  unfold Symbol.literalKey symAt symLCode
  dsimp only
  split
  · rfl
  · rw [lengthCode_eq _ (d[sbo + 3 * j + 2]!).toNat_lt]

/-- `dyn_ltree[c].Freq` is the model's `litFreq` of the tallied symbols. -/
theorem litFreq_eq (d : Array UInt8) (sbo n c : Nat) :
    litFreq (symsOf d sbo n) c = lCount d sbo n c + (if c = 256 then 1 else 0) := by
  unfold litFreq literalFrequency symsOf lCount
  rw [countKey_map]
  have : (List.range n).countP (fun x => (some ((symAt d sbo x).literalKey lengthCode) = some c)) =
      (List.range n).countP (fun j => symLCode d sbo j = c) :=
    List.countP_congr fun j _ => by rw [literalKey_eq]; simp
  rw [this]; omega

/-- `dyn_dtree[c].Freq` is the model's `distFreq` of the tallied symbols (distances at most 32768). -/
theorem distFreq_eq {d : Array UInt8} {sbo n : Nat} (hd : ∀ j, j < n → symDist d sbo j ≤ 32768) (c : Nat) :
    distFreq (symsOf d sbo n) c = dCount d sbo n c := by
  unfold distFreq distanceFrequency symsOf dCount
  rw [countKey_map]
  refine List.countP_congr fun j hj => ?_
  have hj' := hd j (List.mem_range.mp hj)
  unfold Symbol.distanceKey symAt
  dsimp only
  by_cases h0 : symDist d sbo j = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, Option.some.injEq, ne_eq, not_false_eq_true, true_and]
    rw [dCodeOf_eq _ (by omega)]

/-! ## Symbol costs -/

/-- The bits `compress_block` sends for tallied symbol `j` (`symCost`, heap side) are the model's `symbolCost` under
code lengths `fL` / `fD` that the trees `LT` / `DT` hold. -/
theorem symCost_model (LT DT : Array Ct) (d : Array UInt8) (sbo j : Nat) (hdist : symDist d sbo j ≤ 32768)
    (fL fD : Nat → Nat) (hL : ∀ k, k < 286 → (LT[k]!).dl.toNat = fL k)
    (hD : ∀ k, k < 30 → (DT[k]!).dl.toNat = fD k) :
    TreesCompress.symCost LT DT d sbo j =
      symbolCost fL fD lengthExtra distanceExtra lengthCode distanceCode (symAt d sbo j) := by
  have hv := (d[sbo + 3 * j + 2]!).toNat_lt
  unfold TreesCompress.symCost symbolCost symAt TreesCompress.matchCost
  dsimp only
  split
  · exact hL _ (by omega)
  · rename_i h0
    have hc := lengthCode_lt (d[sbo + 3 * j + 2]!).toNat
    have hdc := distanceCode_lt (symDist d sbo j - 1)
    rw [lengthCode_eq _ hv, dCodeOf_eq _ (by omega), hL _ (by omega), hD _ hdc, lx_eq ⟨_, hc⟩, dx_eq ⟨_, hdc⟩]

/-- The heap `blockCosts` of `compress_block` is the model's `blockCosts` of the tallied symbols when the trees hold
the model's code lengths. -/
theorem blockCosts_model (LT DT : Array Ct) (d : Array UInt8) (sbo n : Nat)
    (hd : ∀ j, j < n → symDist d sbo j ≤ 32768)
    (hL : ∀ k, k < 286 → (LT[k]!).dl.toNat = litLens (symsOf d sbo n) k)
    (hD : ∀ k, k < 30 → (DT[k]!).dl.toNat = distLens (symsOf d sbo n) k) :
    TreesCompress.blockCosts LT DT d sbo n = blockCosts (symsOf d sbo n) := by
  unfold TreesCompress.blockCosts blockCosts
  conv => rhs; unfold symsOf
  rw [List.map_map]
  refine List.map_congr_left fun j hj => ?_
  exact symCost_model LT DT d sbo j (hd j (List.mem_range.mp hj)) _ _ hL hD

end ZlibNgF.Proof.TreesDyn
