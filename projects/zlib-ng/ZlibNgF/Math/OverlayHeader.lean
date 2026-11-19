import ZlibNgF.Math.HuffClasses

noncomputable section

/-!
# The dynamic tree header of zlib-ng (heap-free)

`send_all_trees` writes `5 + 5 + 4` bits of counts, `3` bits per transmitted bit-length code length
(`blcodes = max_blindex + 1` of `build_bl_tree`), and the run-length coded code lengths of the literal/length and
distance trees with the codes of the bit-length tree (`send_tree`). `scan_tree` and `send_tree` share one loop;
`scanTokens` is that loop and returns the bit-length symbols in emission order:

* `curlen = nextlen; nextlen = tree[n + 1].Len` (`65535`, the `0xffff` guard, after `max_code`);
* `if (++count < max_count && curlen == nextlen) continue;`
* `count < min_count`: `count` copies of `curlen`; `curlen != 0`: `curlen` (when `curlen != prevlen`) then
  `REP_3_6` (16, 2 extra bits); `count <= 10`: `REPZ_3_10` (17, 3 extra bits); otherwise `REPZ_11_138`
  (18, 7 extra bits);
* `count = 0; prevlen = curlen;` and `(max_count, min_count)` = `(138, 3)` if `nextlen == 0`, `(6, 3)` if
  `curlen == nextlen`, else `(7, 4)`; the initial values are `(138, 3)` when `tree[0].Len == 0`, else `(7, 4)`.

`scan_tree` adds one to `bl_tree[t].Freq` per emitted symbol `t` (`blFreq`); `build_bl_tree` builds the bit-length
tree with the same model (`treeLengths 19 7`) and finds `max_blindex` (`blMaxIndex`, at least 3) by scanning
`bl_order` down. `headerBits` is the number of bits `send_all_trees` writes.

`header_le`: with code lengths at most 15, at most 286 literal/length and 30 distance codes, the header has at most
`14 + 3 * 19 + 7 * (286 + 30) = 2283` bits: every emitted group costs at most 7 bits per code length it covers
(bit-length codes are at most 7 bits long).
-/

namespace ZlibNgF.Math.Huff
set_option autoImplicit false

/-- `tree[n + 1].Len`, or the `0xffff` guard after the last code (`m = max_code + 1`). -/
def nextLen (len : Nat → Nat) (m n : Nat) : Nat := if n + 1 < m then len (n + 1) else 65535

/-- The bit-length symbols one group of `scan_tree` / `send_tree` emits. -/
def groupTokens (prevlen : Int) (count minc curlen : Nat) : List Nat :=
  if count < minc then List.replicate count curlen
  else if curlen ≠ 0 then (if (curlen : Int) ≠ prevlen then [curlen] else []) ++ [16]
  else if count ≤ 10 then [17] else [18]

/-- The loop of `scan_tree` / `send_tree` from position `n` with `k` positions left. -/
noncomputable def scanTokens (len : Nat → Nat) (m : Nat) : Nat → Nat → Int → Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _, _, _, _ => []
  | k + 1, n, prevlen, count, maxc, minc, nextlen =>
    if count + 1 < maxc ∧ nextlen = nextLen len m n then
      scanTokens len m k (n + 1) prevlen (count + 1) maxc minc (nextLen len m n)
    else
      groupTokens prevlen (count + 1) minc nextlen ++
        scanTokens len m k (n + 1) nextlen 0
          (if nextLen len m n = 0 then 138 else if nextlen = nextLen len m n then 6 else 7)
          (if nextLen len m n = 0 then 3 else if nextlen = nextLen len m n then 3 else 4)
          (nextLen len m n)

/-- The bit-length symbols for one tree with `m = max_code + 1` codes. -/
def treeTokens (len : Nat → Nat) (m : Nat) : List Nat :=
  scanTokens len m m 0 (-1) 0 (if len 0 = 0 then 138 else 7) (if len 0 = 0 then 3 else 4) (len 0)

/-- `extra_blbits`. -/
def blExtra (t : Nat) : Nat := if t = 16 then 2 else if t = 17 then 3 else if t = 18 then 7 else 0

/-- `bl_order`. -/
def blOrder : List Nat := [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- `for (max_blindex = BL_CODES-1; max_blindex >= 3; max_blindex--) if (bl_tree[bl_order[max_blindex]].Len != 0)
break;`, from index `k` down. -/
noncomputable def blMaxIndex (blLen : Nat → Nat) : Nat → Nat
  | 0 => 3
  | k + 1 => if k + 1 ≤ 3 then 3 else if blLen (blOrder.getD (k + 1) 0) ≠ 0 then k + 1 else blMaxIndex blLen k

/-- The bit-length symbols of both trees (`scan_tree` of `dyn_ltree`, then of `dyn_dtree`). -/
def allTokens (litLen : Nat → Nat) (lcodes : Nat) (distLen : Nat → Nat) (dcodes : Nat) : List Nat :=
  treeTokens litLen lcodes ++ treeTokens distLen dcodes

/-- `bl_tree[t].Freq` after the two `scan_tree` calls. -/
def blFreq (toks : List Nat) (t : Nat) : Nat := toks.count t

/-- Bits written by `send_all_trees(s, lcodes, dcodes, max_blindex + 1)`. -/
def headerBits (litLen : Nat → Nat) (lcodes : Nat) (distLen : Nat → Nat) (dcodes : Nat) : Nat :=
  let toks := allTokens litLen lcodes distLen dcodes
  let blLen := treeLengths 19 7 (blFreq toks)
  5 + 5 + 4 + 3 * (blMaxIndex blLen 18 + 1) + (toks.map fun t => blLen t + blExtra t).sum

theorem blMaxIndex_le (blLen : Nat → Nat) : ∀ k, blMaxIndex blLen k ≤ max k 3
  | 0 => by simp [blMaxIndex]
  | k + 1 => by
    have := blMaxIndex_le blLen k
    simp only [blMaxIndex]; split
    · omega
    · split <;> omega

theorem sum_rep (n x : Nat) : (List.replicate n x).sum = n * x := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

theorem groupTokens_cost (blLen : Nat → Nat) (hb : ∀ t, blLen t ≤ 7) (prevlen : Int) (count minc curlen : Nat)
    (hm : 3 ≤ minc) (hc : curlen ≤ 15) :
    ((groupTokens prevlen count minc curlen).map fun t => blLen t + blExtra t).sum ≤ 7 * count := by
  unfold groupTokens
  have e0 : blExtra curlen = 0 := by unfold blExtra; split <;> (try split) <;> (try split) <;> omega
  have e0' : (if curlen = 16 then 2 else if curlen = 17 then 3 else if curlen = 18 then 7 else 0) = 0 := e0
  have b0 := hb curlen
  have b16 := hb 16
  have b17 := hb 17
  have b18 := hb 18
  split
  · rw [List.map_replicate, sum_rep, e0, Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
  · split
    · split <;> simp [blExtra] <;> omega
    · split <;> simp [blExtra] <;> omega

theorem scanTokens_cost (len blLen : Nat → Nat) (m : Nat) (hb : ∀ t, blLen t ≤ 7) (hl : ∀ n, n < m → len n ≤ 15) :
    ∀ k n (prevlen : Int) (count maxc minc nextlen : Nat), n + k = m → 3 ≤ minc → (1 ≤ k → nextlen ≤ 15) →
      ((scanTokens len m k n prevlen count maxc minc nextlen).map fun t => blLen t + blExtra t).sum ≤
        7 * (count + k)
  | 0, _, _, _, _, _, _, _, _, _ => by simp [scanTokens]
  | k + 1, n, prevlen, count, maxc, minc, nextlen, hk, hm, hn => by
    have nl : 1 ≤ k → nextLen len m n ≤ 15 := fun h => by
      unfold nextLen; simp only [show n + 1 < m by omega, ↓reduceIte]; exact hl _ (by omega)
    simp only [scanTokens]
    split
    · have := scanTokens_cost len blLen m hb hl k (n + 1) prevlen (count + 1) maxc minc (nextLen len m n)
        (by omega) hm nl
      omega
    · rw [List.map_append, List.sum_append]
      have g := groupTokens_cost blLen hb prevlen (count + 1) minc nextlen hm (hn (by omega))
      have r := scanTokens_cost len blLen m hb hl k (n + 1) nextlen 0
        (if nextLen len m n = 0 then 138 else if nextlen = nextLen len m n then 6 else 7)
        (if nextLen len m n = 0 then 3 else if nextlen = nextLen len m n then 3 else 4) (nextLen len m n) (by omega)
        (by split <;> (try split) <;> omega) nl
      omega

theorem treeTokens_cost (len blLen : Nat → Nat) (m : Nat) (hb : ∀ t, blLen t ≤ 7) (hl : ∀ n, n < m → len n ≤ 15) :
    ((treeTokens len m).map fun t => blLen t + blExtra t).sum ≤ 7 * m := by
  have := scanTokens_cost len blLen m hb hl m 0 (-1) 0 (if len 0 = 0 then 138 else 7) (if len 0 = 0 then 3 else 4)
    (len 0) (by omega) (by split <;> omega)
    (fun h => hl 0 (by omega))
  unfold treeTokens; omega

/-- **Header bound**: at most 2283 bits. -/
theorem header_le (litLen distLen : Nat → Nat) (lcodes dcodes : Nat) (hlc : lcodes ≤ 286) (hdc : dcodes ≤ 30)
    (hl : ∀ n, litLen n ≤ 15) (hd : ∀ n, distLen n ≤ 15) :
    headerBits litLen lcodes distLen dcodes ≤ 2283 := by
  unfold headerBits allTokens
  have hb : ∀ t, treeLengths 19 7 (blFreq (treeTokens litLen lcodes ++ treeTokens distLen dcodes)) t ≤ 7 :=
    fun t => genBitlen_le 7 _ t
  have a := treeTokens_cost litLen _ lcodes hb (fun n _ => hl n)
  have b := treeTokens_cost distLen _ dcodes hb (fun n _ => hd n)
  have c := blMaxIndex_le (treeLengths 19 7 (blFreq (treeTokens litLen lcodes ++ treeTokens distLen dcodes))) 18
  simp only [List.map_append, List.sum_append]
  omega

end ZlibNgF.Math.Huff
