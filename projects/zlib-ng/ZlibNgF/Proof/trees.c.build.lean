import ZlibNgF.Proof.«trees.c.sort»

/-!
# `build_tree` cut into its phases (`ZlibNgF`)

`build_tree` (`trees.c:165-271`) is the leaf scan (`scanBody`), the forcing loop (`forceBody`), the store of
`desc->max_code`, the sort (`sortBlock`), the merge loop (`mergeBody`), `gen_bitlen` and `gen_codes`. `build_tree_eq`
states that the translation is that sequence.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesBuild
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesScan ZlibNgF.Proof.TreesForce
open ZlibNg.Inftrees (aget aset)

/-- The sort of the leaves: the swap of two leaves, or one or two radix passes. Returns `(sorted, internals)`. -/
def sortBlock (leaves scratch : DWPtr) (nleaves : Int32) (count_lo count_hi : Array UInt16) : M (DWPtr × DWPtr) := do
  if nleaves == 2 then
    let l0 ← dwGet leaves 0
    let l1 ← dwGet leaves 1
    if l0 > l1 then
      let t := l0
      dwSet leaves 0 l1
      dwSet leaves 1 t
      pure (leaves, scratch)
    else pure (leaves, scratch)
  else if (← aget count_hi 1).toUInt32.toInt32 == nleaves then
    let _ ← pq_radix_pass leaves scratch nleaves PQ_NODE_BITS.toInt32 count_lo
    pure (scratch, leaves)
  else
    let _ ← pq_radix_pass leaves scratch nleaves PQ_NODE_BITS.toInt32 count_lo
    let _ ← pq_radix_pass scratch leaves nleaves (PQ_NODE_BITS + 8).toInt32 count_hi
    pure (leaves, scratch)

/-- The condition of the merge loop. -/
def mergeCond : Int32 × Int32 × Int32 × Int32 × Int32 → M (Bool × (Int32 × Int32 × Int32 × Int32 × Int32)) :=
  fun ((merges, li, ihead, itail, node) : Int32 × Int32 × Int32 × Int32 × Int32) =>
    pure (merges > 0, (merges, li, ihead, itail, node))

/-- The body of the merge loop. -/
def mergeBody (tree : CtPtr) (sorted internals : DWPtr) (nleaves : Int32) :
    Int32 × Int32 × Int32 × Int32 × Int32 → M (Int32 × Int32 × Int32 × Int32 × Int32) :=
  fun ((merges, li, ihead, itail, node) : Int32 × Int32 × Int32 × Int32 × Int32) => do
    let (en, li, ihead) ← pq_take sorted li nleaves internals ihead itail
    let (em, li, ihead) ← pq_take sorted li nleaves internals ihead itail
    let n := pq_node en
    let m := pq_node em
    let f : UInt16 := (pq_freq en + pq_freq em).toUInt16
    ctSetFc tree node.toInt f
    ctSetDl tree m.toInt node.toUInt32.toUInt16
    ctSetDl tree n.toInt node.toUInt32.toUInt16
    dwSet internals itail.toInt (pq_pack f.toUInt32 node)
    let itail ← chkI32 (itail.toInt + 1)
    let node ← chkI32 (node.toInt + 1)
    pure (merges - 1, li, ihead, itail, node)

theorem M_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f) >>= g = m >>= fun a => f a >>= g := by
  funext h; simp only [bind_app]; cases m h <;> rfl

/-- What follows the sort. -/
def buildTail (st : StatePtr) (desc : DescSel) (tree : CtPtr) (elems nleaves max_code : Int32)
    (sorted internals : DWPtr) : M Unit := do
  let (_, _, _, _, nd) ← cwhile mergeCond (mergeBody tree sorted internals nleaves)
    (nleaves - 1, (0 : Int32), (0 : Int32), (0 : Int32), elems)
  gen_bitlen st desc sorted nleaves (← chkI32 (nd.toInt - 1))
  gen_codes tree max_code (← blCountP st)

theorem build_tree_eq (st : StatePtr) (desc : DescSel) :
    build_tree st desc = (do
      let tree ← descDynTree st desc
      let stree := (← descStat st desc).static_tree
      let elems := (← descStat st desc).elems
      let leaves ← pqLeavesP st
      let scratch ← pqScratchP st
      let (_, nl, mc, clo, chi) ← cwhile (scanCond elems) (scanBody tree leaves)
        ((0 : Int32), (0 : Int32), (-1 : Int32), Array.replicate 257 (0 : UInt16), Array.replicate 257 (0 : UInt16))
      let (nl, mc, _) ← cwhile forceCond (forceBody st tree stree leaves) (nl, mc, (0 : Int32))
      wrD st fun s => desc.set s { desc.get s with max_code := mc }
      let (sorted, internals) ← sortBlock leaves scratch nl clo chi
      buildTail st desc tree elems nl mc sorted internals) := by
  unfold build_tree
  refine congrArg (descDynTree st desc >>= ·) (funext fun tree => ?_)
  refine congrArg (descStat st desc >>= ·) (funext fun sd1 => ?_)
  refine congrArg (descStat st desc >>= ·) (funext fun sd2 => ?_)
  refine congrArg (pqLeavesP st >>= ·) (funext fun leaves => ?_)
  refine congrArg (pqScratchP st >>= ·) (funext fun scratch => ?_)
  refine congrArg (_ >>= ·) (funext fun x1 => ?_)
  obtain ⟨_, nl, mc, clo, chi⟩ := x1
  refine congrArg (_ >>= ·) (funext fun x2 => ?_)
  obtain ⟨nl2, mc2, nd2⟩ := x2
  refine congrArg (_ >>= ·) (funext fun u => ?_)
  simp only [sortBlock]
  by_cases h2 : (nl2 == 2) = true
  · simp only [h2, ↓reduceIte, M_bind_assoc]
    refine congrArg (_ >>= ·) (funext fun l0 => ?_)
    refine congrArg (_ >>= ·) (funext fun l1 => ?_)
    by_cases h3 : l0 > l1
    · simp only [h3, ↓reduceIte, M_bind_assoc]; rfl
    · simp only [h3, ↓reduceIte]; rfl
  · simp only [h2, Bool.false_eq_true, ↓reduceIte, M_bind_assoc]
    refine congrArg (_ >>= ·) (funext fun c1 => ?_)
    by_cases h3 : (c1.toUInt32.toInt32 == nl2) = true
    · simp only [h3, ↓reduceIte, M_bind_assoc]; rfl
    · simp only [h3, Bool.false_eq_true, ↓reduceIte, M_bind_assoc]; rfl

end ZlibNgF.Proof.TreesBuild
