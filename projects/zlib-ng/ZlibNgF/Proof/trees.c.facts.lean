import ZlibNgF.Proof.«trees_emit.h.static»

/-!
# `TreesFacts` from its `flush_block` field (`ZlibNgF`)

Every field of `TreesFacts` (`Proof/deflate.c.facts.lean`) except `flush_block` is proved in
`Proof/trees_emit.h.static.lean`; `treesFacts_of_flush` assembles the structure from a proof of `flush_block`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesFactsP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.TreesEmitP

/-- `TreesFacts`, given its `flush_block` field. -/
theorem treesFacts_of_flush
    (hf : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32),
      EmitOk s b (fun st => st.pending = 0 ∧ (buf = .null ∨ WindowBuf b st buf len)) (fun _ => 0)
        (fun st => 4 * st.lit_bufsize.toNat + 9) (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last)) :
    TreesFacts where
  flush_block := hf
  stored_block := stored_block_ok
  align := align_ok
  emit_lit := emit_lit_ok
  emit_dist := emit_dist_ok
  emit_tree := emit_tree_ok
  emit_end_block := emit_end_block_ok
  emit_align := emit_align_ok

end ZlibNgF.Proof.TreesFactsP
