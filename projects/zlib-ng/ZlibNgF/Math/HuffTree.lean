noncomputable section

/-!
# Abstract Huffman merges (heap-free)

Pure Huffman mathematics re-proved from the sibling `zlib` project (`ZlibF.Math.HuffmanTree`), with the tie-break
removed from the merge relation: zlib-ng's `build_tree` breaks frequency ties by node number, not by subtree
height, so the relation here only asks that each merge takes two roots of least weight.

* A **forest** `List HTree` is the multiset of roots not merged yet (the unused leaves of `pq_leaves` and the
  internal nodes of the `pq_scratch` FIFO). The list order carries no meaning.
* `HTree.leaf j w` is symbol `j` with `tree[j].Freq = w`; `HTree.node a b` is the node `build_tree` creates with
  sons `n = a` (taken first) and `m = b`. Its weight is the sum of the sons' weights (no `uint16_t` wrap: the
  callers keep the total weight below `2^16`).
* `Step s s' n m`: one merge. `n` weighs at most every other root, `m` at most every root left after `n`.
* `Merges s tr T`: repeated steps from forest `s` end with the single tree `T`; `tr` lists the merged roots in
  order.
* `LeafInfo.d` is a leaf's depth below the root: the length `gen_bitlen` assigns when it is at most
  `max_length` (otherwise the overflow repair changes the lengths, `HuffRepairModel`).
-/

namespace ZlibNgF.Math.Huff

/-- A Huffman (sub)tree: a symbol leaf with its weight, or an internal node with its two sons. -/
inductive HTree where
  | leaf (sym w : Nat)
  | node (a b : HTree)
  deriving Inhabited

/-- One leaf of a tree, with its depth below the root. -/
structure LeafInfo where
  sym : Nat
  w : Nat
  d : Nat
  deriving DecidableEq, Repr

namespace HTree

/-- `tree[node].Freq`: the sum of the leaf weights. -/
noncomputable def weight : HTree → Nat
  | leaf _ w => w
  | node a b => a.weight + b.weight

/-- The leaves, each with its depth below this tree's root. -/
noncomputable def leaves : HTree → List LeafInfo
  | leaf s w => [⟨s, w, 0⟩]
  | node a b => (a.leaves ++ b.leaves).map fun x => { x with d := x.d + 1 }

/-- The sons of a node, `[]` for a leaf. -/
noncomputable def sons : HTree → List HTree
  | leaf _ _ => []
  | node a b => [a, b]

end HTree

/-- The order of the merge: weight only. -/
def smaller (a b : HTree) : Prop := a.weight ≤ b.weight

instance (a b : HTree) : Decidable (smaller a b) := by unfold smaller; infer_instance

/-- **One merge.** `n` is least in the forest `s`, `m` is least among the rest `r`, and the new node `node n m`
takes their place. -/
def Step (s s' : List HTree) (n m : HTree) : Prop :=
  ∃ r, s.Perm (n :: m :: r) ∧ (∀ x ∈ m :: r, smaller n x) ∧ (∀ x ∈ r, smaller m x) ∧
    s' = HTree.node n m :: r

/-- **A complete run of merges** from forest `s` to the single tree `T`; `tr` lists the merged roots in order. -/
inductive Merges : List HTree → List HTree → HTree → Prop
  | done (t : HTree) : Merges [t] [] t
  | step {s s' : List HTree} {n m : HTree} {tr : List HTree} {T : HTree} :
      Step s s' n m → Merges s' tr T → Merges s (n :: m :: tr) T

/-- The initial forest: one leaf per `(symbol, weight)` pair. -/
def initForest (syms : List (Nat × Nat)) : List HTree := syms.map fun p => .leaf p.1 p.2

/-- Fibonacci pairs `(F n, F (n+1))`. -/
noncomputable def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)

/-- Fibonacci numbers: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib (n : Nat) : Nat := (fibPair n).1

end ZlibNgF.Math.Huff
