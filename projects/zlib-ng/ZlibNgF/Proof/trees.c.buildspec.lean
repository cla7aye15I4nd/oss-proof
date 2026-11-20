import ZlibNgF.Proof.«trees.c.force»
import ZlibNgF.Math.OverlayDynamic

/-!
# What `build_tree` does on `SH` heaps: the statement (`ZlibNgF`)

`BuildTreeSpec` states the effect of `build_tree(s, desc)` (`trees.c:165-271`, with `gen_bitlen` and `gen_codes`) for
each of the three descriptors, in terms of the heap-free model of `Math/HuffModel.lean`. It is the interface between
the proof of `build_tree` and its callers (`zng_tr_flush_block`, `build_bl_tree`).

Descriptor `t` (`tElems t` codes, maximum length `tMaxLen t`), tree `F = tArr t s` before the call, model lengths
`len = treeLengths elems L (frq F)`:

* the call does not fault and changes only the state record, in these fields:
* the tree array (size kept): for every code `k < elems`, `Len = len k`; `Code` (the `Freq` member of the union)
  is `F[k].Freq` when `len k = 0` and otherwise the canonical code of `k` bit-reversed in `len k` bits (`treeCode`:
  `next_code[len]` from the final `bl_count` (`blFinal`), plus the codes `m < k` of the same length). Entries
  `k ≥ elems` (internal nodes) are arbitrary;
* `desc->max_code`, with `max_code + 1 = (buildTree elems (frq F)).maxCode1`;
* `opt_len` increased (modulo `2^32`) by `Σ_{k < elems} freq(k) * (len k + extra(k))` over the frequencies of `F`
  (`optAdd`). The forcing loop's `opt_len--` (which can wrap transiently) and the forced leaf's `1 * (1 + 0)` cancel:
  this is the net effect;
* `static_len` increased by `Σ_{k < elems} freq(k) * (stree[k].Len + extra(k))` (`statAdd`) for the literal/length and
  distance trees, unchanged for the bit-length tree (no static tree);
* `bl_count`, `pq_leaves`, `pq_scratch`: arbitrary, sizes kept.

Precondition: the descriptor points at its tree and static descriptor (`zng_tr_init`), the arrays have their C sizes
(`DCore.trees`, `DCore.scratch`), and the total frequency is below `65534`, so no `uint16_t` node frequency wraps
(at most `lit_bufsize ≤ 32768` for the literal/length and distance trees, at most `L_CODES + D_CODES` for the
bit-length tree).
-/

set_option autoImplicit false

noncomputable section

namespace ZlibNgF.Proof.TreesBuildSpec
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesScan (frq)
open ZlibNgF.Proof.TreesForce (sdl)
open ZlibNgF.Math.Huff (Built buildTree treeLengths overflowCount blCount repairIter)
open ZlibNgF.Math.HuffSymbols (mass)
open ZlibNgF.Math.OverlayDynamic (lengthExtra distanceExtra)
open ZlibNgF.Proof.InflateSync (Sat)

/-- `elems` of the static descriptor of `t`. -/
def tElems : DescSel → Nat
  | .l_desc => 286
  | .d_desc => 30
  | .bl_desc => 19

/-- `max_length` of the static descriptor of `t`. -/
def tMaxLen : DescSel → Nat
  | .l_desc => 15
  | .d_desc => 15
  | .bl_desc => 7

/-- The size of the tree array of `t` (`HEAP_SIZE`, `2 * D_CODES + 1`, `2 * BL_CODES + 1`). -/
def tSize : DescSel → Nat
  | .l_desc => HEAP_SIZE
  | .d_desc => 2 * 30 + 1
  | .bl_desc => 2 * 19 + 1

/-- The extra bits of code `k` of tree `t` (`extra_lbits[k - 257]`, `extra_dbits[k]`, `extra_blbits[k]`). -/
def xb (t : DescSel) (k : Nat) : Nat :=
  match t with
  | .l_desc => if 257 ≤ k then lengthExtra (k - 257) else 0
  | .d_desc => distanceExtra k
  | .bl_desc => ZlibNgF.Math.Huff.blExtra k

/-- The model lengths of the tree `F` of descriptor `t`. -/
def tLen (t : DescSel) (F : Array Ct) : Nat → Nat := treeLengths (tElems t) (tMaxLen t) (frq F)

/-- `bl_count` when `gen_bitlen` returns: the clamped depths' counts, repaired when there was an overflow. -/
def blFinal (L : Nat) (bt : Built) : Nat → Nat :=
  if overflowCount L bt.root = 0 then blCount L bt.sorted bt.root
  else repairIter L ((overflowCount L bt.root + 1) / 2) (blCount L bt.sorted bt.root)

/-- `next_code[j]` of `gen_codes`: `next_code[1] = (0 + bl_count[0]) << 1`, `next_code[j + 1] = (next_code[j] +
bl_count[j]) << 1` (taken modulo `2^16` by the C; only the low `j` bits matter). -/
noncomputable def nextCode (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (nextCode c j + c j) * 2

/-- The low `l` bits of `x`, reversed (`bi_reverse(x, l)` for `1 ≤ l ≤ 15`). -/
noncomputable def revBits : Nat → Nat → Nat
  | 0, _ => 0
  | l + 1, x => x % 2 * 2 ^ l + revBits l (x / 2)

/-- The code `gen_codes` stores in `tree[k].Code` when `len k ≠ 0`: `next_code[len k]` plus the number of codes
`m < k` of the same length, bit-reversed in `len k` bits. -/
def treeCode (len : Nat → Nat) (c : Nat → Nat) (k : Nat) : Nat :=
  revBits (len k) (nextCode c (len k) + (List.range k).countP (fun m => len m = len k))

/-- The `Code` of tree `t` at `k` after `build_tree`. -/
def tCode (t : DescSel) (F : Array Ct) (k : Nat) : Nat :=
  treeCode (tLen t F) (blFinal (tMaxLen t) (buildTree (tElems t) (frq F))) k

/-- The increase of `opt_len`: `Σ_{k < elems} freq(k) * (len k + extra(k))`. -/
def optAdd (t : DescSel) (F : Array Ct) : Nat := mass (fun k => frq F k * (tLen t F k + xb t k)) (tElems t)

/-- The increase of `static_len`: `Σ_{k < elems} freq(k) * (stree[k].Len + extra(k))`; none for the bit-length tree. -/
def statAdd (t : DescSel) (F : Array Ct) : Nat :=
  match t with
  | .bl_desc => 0
  | _ => mass (fun k => frq F k * ((sdl t k).toNat + xb t k)) (tElems t)

/-- What `build_tree` needs of the state: the descriptor of `zng_tr_init`, the C sizes of the arrays, no `uint16_t`
wrap of a node frequency. -/
structure BuildPre (t : DescSel) (b : Nat) (s : DeflateState) : Prop where
  dyn : (t.get s).dyn_tree = .val (.ref (tRef t b) 0)
  stat : (t.get s).stat_desc = .val (tSD t)
  tsize : (tArr t s).size = tSize t
  pql : s.pq_leaves.size = 287
  pqs : s.pq_scratch.size = 287
  blc : s.bl_count.size = 16
  mass : mass (frq (tArr t s)) (tElems t) < 65534

/-- The state after `build_tree` on descriptor `t` from state `s`. -/
structure BuildPost (t : DescSel) (s s' : DeflateState) : Prop where
  shape : ∃ (A : Array Ct) (blc : Array UInt16) (lv sc : Array UInt32) (mc : Int32),
    s' = t.set { tPut t s A with
        bl_count := blc
        pq_leaves := lv
        pq_scratch := sc
        opt_len := s.opt_len + (optAdd t (tArr t s)).toUInt32
        static_len := s.static_len + (statAdd t (tArr t s)).toUInt32 }
      { t.get s with max_code := mc } ∧
    A.size = (tArr t s).size ∧ blc.size = s.bl_count.size ∧ lv.size = s.pq_leaves.size ∧
    sc.size = s.pq_scratch.size ∧
    mc.toInt + 1 = (buildTree (tElems t) (frq (tArr t s))).maxCode1 ∧
    (∀ k, k < tElems t → (A[k]!).dl.toNat = tLen t (tArr t s) k) ∧
    (∀ k, k < tElems t → (A[k]!).fc.toNat =
      if tLen t (tArr t s) k = 0 then ((tArr t s)[k]!).fc.toNat else tCode t (tArr t s) k)

/-- **`build_tree`** on each descriptor of an `SH` heap does not fault and ends in `BuildPost`. -/
def BuildTreeSpec : Prop :=
  ∀ (t : DescSel) (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (s : DeflateState) (d : Array UInt8),
    BuildPre t b s →
    Sat (SH H i z b s d) (build_tree (some b) t) (fun _ H' => ∃ s', H' = SH H i z b s' d ∧ BuildPost t s s')

end ZlibNgF.Proof.TreesBuildSpec

end
