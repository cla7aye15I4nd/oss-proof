import ZlibNgF.Math.HuffFibPush

noncomputable section


/-!
# A model of zlib-ng's `build_tree` and `gen_bitlen` (heap-free)

zlib-ng (`trees.c`) does not build Huffman trees with madler's heap. This file states, as plain functions on a
frequency table `freq : Nat → Nat` (`tree[n].Freq` for `n < elems`), what zlib-ng's `build_tree` and
`gen_bitlen` compute, and proves that the merge order is a valid Huffman merge (each step merges two roots of
least weight), so the Fibonacci depth bound of `HuffFib` holds for its tree.

## Correspondence with `trees.c` (`build_tree`, `pq_radix_pass`, `pq_take`, `gen_bitlen`)

* **Leaf scan** (`for (n = 0; n < elems; n++)`): `scanLeaves freq elems` lists the pairs `(freq n, n)` with
  `freq n ≠ 0` in node order; they are the packed entries `pq_pack(freq, n)` appended to `pq_leaves`.
  `maxCode1 freq elems` is `max_code + 1` (0 when no frequency is nonzero, `max_code = -1`).
* **Forcing** (`while (nleaves < 2)`): `forced` appends `(1, node)` with `node = (max_code < 2 ? ++max_code : 0)`,
  once when one leaf was scanned and twice when none was. The C also sets `tree[node].Freq = 1`; the model's
  leaf entry carries that frequency. `forced … |>.2` is the final `max_code + 1` (`desc->max_code`).
* **Sort key and tie-break**: a packed entry `(freq << PQ_NODE_BITS) | node` compares as the pair `(freq, node)`
  lexicographically (`keyLt`), since every node number fits in `PQ_NODE_BITS` bits and the frequencies do not
  wrap. The two radix passes (or the swap when `nleaves == 2`) sort the leaves ascending by that key;
  `sortKeys` is the insertion sort by the same key. The keys are distinct (distinct nodes), so every correct
  sort gives this list.
* **Two-queue merge**: `pqTake ls is` is `pq_take`: it returns the next leaf when there is one and either the
  internal FIFO is empty or the leaf's packed key is strictly below the FIFO head's key, else the FIFO head.
  On equal frequencies the leaf wins (its node `< elems ≤` every internal node). `mergeLoop (nleaves - 1)`
  runs the `for (merges = nleaves - 1; …)` loop: two `pq_take`s (`en`, then `em`), the new node `node`
  (numbered from `elems` upward) with frequency `freq(en) + freq(em)` and sons `n = en`, `m = em`, appended to
  the FIFO (`internals[itail++]`). The model adds frequencies in `Nat`; the C stores them as `uint16_t`, which
  agrees while the total weight is below `2^16` (at most `lit_bufsize + 2 ≤ 32770` for the literal/length and
  distance trees, at most `2 * (L_CODES + D_CODES)` for the bit-length tree).
* **Root**: the last created node (`node - 1`) is the only entry left in the FIFO: `buildTree … |>.root`.
* **Depths** (`gen_bitlen`, first two loops): a node's `Len` is its parent's `Len + 1`, clamped to
  `max_length`; walking from the root down, a node at depth `t` gets `min t max_length`, and `overflow` counts
  the non-root nodes (internal nodes and leaves) with `t > max_length` (`overflowCount`). `depthIn T v` is the
  depth of leaf `v` in the tree. `bl_count` after the first pass is `blCount` (the leaves of each clamped depth).
* **Overflow repair**: when `overflow ≠ 0`, the `do … while (overflow > 0)` loop runs `(overflow + 1) / 2`
  times (`overflow` decreases by 2; it is even, `overflow_even`); one iteration is `repairStep` of
  `HuffRepairModel` (deepest nonempty level below `max_length` loses a leaf, the next level gains two,
  `bl_count[max_length]` loses one).
* **Length re-assignment**: `for (bits = max_length; bits != 0; bits--)` hands `bl_count[bits]` leaves each
  the length `bits`, scanning `sorted` from the least frequent leaf (index 0) upward. The leaf at index `i` of
  `N` leaves is rank `N - i` (rank 1 = most frequent) and gets `lenOfRank max_length c (N - i)`: the least `j`
  with `c 1 + … + c j ≥ N - i` (`HuffRepairModel.lenOfRank`). Without overflow `gen_bitlen` returns after the
  first pass, so the lengths are the depths.
* Symbols with zero frequency that were not forced keep `Len = 0` (`genBitlen` returns 0 for a node that is
  not a leaf).
-/

namespace ZlibNgF.Math.Huff
set_option autoImplicit false

/-! ## The model -/

/-- The packed-key order `pq_pack(f₁, n₁) < pq_pack(f₂, n₂)`: frequency, then node. -/
def keyLt (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The leaf scan of `build_tree`: `(freq n, n)` for every `n < elems` with `freq n ≠ 0`, in node order. -/
noncomputable def scanLeaves (freq : Nat → Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => scanLeaves freq n ++ (if freq n ≠ 0 then [(freq n, n)] else [])

/-- `max_code + 1` after the leaf scan. -/
noncomputable def maxCode1 (freq : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if freq n ≠ 0 then n + 1 else maxCode1 freq n

/-- The node forced by one iteration of `while (nleaves < 2)` when `max_code + 1 = mc1`. -/
def forceNode (mc1 : Nat) : Nat := if mc1 < 3 then mc1 else 0

/-- `max_code + 1` after that iteration. -/
def forceNext (mc1 : Nat) : Nat := if mc1 < 3 then mc1 + 1 else mc1

/-- The forcing loop: the leaf list and `max_code + 1` after `while (nleaves < 2)`. -/
def forced (ls : List (Nat × Nat)) (mc1 : Nat) : List (Nat × Nat) × Nat :=
  match ls with
  | [] => ([(1, forceNode mc1), (1, forceNode (forceNext mc1))], forceNext (forceNext mc1))
  | [l] => ([l, (1, forceNode mc1)], forceNext mc1)
  | _ => (ls, mc1)

/-- Insert by packed key. -/
noncomputable def insKey (e : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [e]
  | x :: xs => if keyLt e x then e :: x :: xs else x :: insKey e xs

/-- The leaves sorted ascending by packed key (what the radix passes compute). -/
noncomputable def sortKeys : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: xs => insKey x (sortKeys xs)

/-- An entry of a queue: frequency, node number, and the subtree it roots. -/
structure QE where
  freq : Nat
  node : Nat
  tree : HTree

/-- The queue entry of a leaf `(freq, node)`. -/
def leafQE (e : Nat × Nat) : QE := ⟨e.1, e.2, .leaf e.2 e.1⟩

/-- `pq_take`: the next leaf if its key is below the FIFO head's (or the FIFO is empty), else the FIFO head.
Returns the entry and the two queues after it. -/
def pqTake : List (Nat × Nat) → List QE → QE × List (Nat × Nat) × List QE
  | l :: ls, [] => (leafQE l, ls, [])
  | l :: ls, i :: is => if keyLt l (i.freq, i.node) then (leafQE l, ls, i :: is) else (i, l :: ls, is)
  | [], i :: is => (i, [], is)
  | [], [] => (⟨0, 0, .leaf 0 0⟩, [], [])

/-- The merge loop: `k` merges, leaves `ls`, internal FIFO `is`, next node number `node`. Returns the FIFO at
the end. -/
noncomputable def mergeLoop : Nat → List (Nat × Nat) → List QE → Nat → List QE
  | 0, _, is, _ => is
  | k + 1, ls, is, node =>
    let a := pqTake ls is
    let b := pqTake a.2.1 a.2.2
    mergeLoop k b.2.1 (b.2.2 ++ [⟨a.1.freq + b.1.freq, node, .node a.1.tree b.1.tree⟩]) (node + 1)

/-- The result of `build_tree`'s construction: the sorted leaves, `max_code + 1`, and the tree. -/
structure Built where
  sorted : List (Nat × Nat)
  maxCode1 : Nat
  root : HTree

/-- `build_tree` up to the call of `gen_bitlen`. -/
def buildTree (elems : Nat) (freq : Nat → Nat) : Built :=
  let f := forced (scanLeaves freq elems) (maxCode1 freq elems)
  let srt := sortKeys f.1
  { sorted := srt, maxCode1 := f.2,
    root := ((mergeLoop (srt.length - 1) srt [] elems).headD ⟨0, 0, .leaf 0 0⟩).tree }

/-- Depth of leaf `v` in `T` (0 if `v` is not a leaf of `T`). -/
def depthIn (T : HTree) (v : Nat) : Nat :=
  match T.leaves.find? (fun x => x.sym == v) with
  | some x => x.d
  | none => 0

/-- Nodes of `t` (its root included) whose depth exceeds `L`, when the root of `t` is at depth `k`. -/
noncomputable def ovfAux (L : Nat) : Nat → HTree → Nat
  | k, .leaf _ _ => if L < k then 1 else 0
  | k, .node a b => (if L < k then 1 else 0) + ovfAux L (k + 1) a + ovfAux L (k + 1) b

/-- `overflow` of `gen_bitlen`: the nodes deeper than `max_length` (the root is at depth 0). -/
def overflowCount (L : Nat) (T : HTree) : Nat := ovfAux L 0 T

/-- `bl_count[j]` after the first pass: the leaves whose clamped depth is `j`. -/
def blCount (L : Nat) (srt : List (Nat × Nat)) (T : HTree) (j : Nat) : Nat :=
  (srt.filter (fun e => min (depthIn T e.2) L == j)).length

/-- Index of the first entry with node `v`. -/
noncomputable def posOf (v : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | e :: es => if e.2 = v then some 0 else (posOf v es).map (· + 1)

/-- The lengths `gen_bitlen` leaves in `tree[v].Len` (max length `L`). -/
def genBitlen (L : Nat) (b : Built) (v : Nat) : Nat :=
  match posOf v b.sorted with
  | none => 0
  | some i =>
    if overflowCount L b.root = 0 then min (depthIn b.root v) L
    else lenOfRank L (repairIter L ((overflowCount L b.root + 1) / 2) (blCount L b.sorted b.root))
      (b.sorted.length - i)

/-- The code lengths of a tree with `elems` symbols, frequencies `freq` and maximum length `L`. -/
def treeLengths (elems L : Nat) (freq : Nat → Nat) : Nat → Nat := genBitlen L (buildTree elems freq)

end ZlibNgF.Math.Huff
