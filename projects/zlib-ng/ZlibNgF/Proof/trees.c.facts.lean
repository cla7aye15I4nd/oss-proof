import ZlibNgF.Proof.«trees_emit.h.static»
import ZlibNgF.Math.OverlayTinyBudget

/-!
# `TreesFacts` from its `flush_block` field (`ZlibNgF`)

Every field of `TreesFacts` (`Proof/deflate.c.facts.lean`) except `flush_block` and `flush_block_clears` is proved
in `Proof/trees_emit.h.static.lean`; `treesFacts_of_flush` assembles the structure from proofs of those two.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesFactsP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.TreesEmitP

/-- `TreesFacts`, given its `flush_block` and `flush_block_clears` fields. -/
theorem treesFacts_of_flush
    (hf : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32), 0 ≤ last → last ≤ 1 →
      EmitOk s b (FlushBlockPre b buf len) (fun _ => 0) (fun st => 4 * st.lit_bufsize.toNat + 9)
        (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last))
    (hc : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32), 0 ≤ last → last ≤ 1 →
      EmitClears s b (FlushBlockPre b buf len) (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last)) :
    TreesFacts where
  flush_block := hf
  flush_block_clears := hc
  stored_block := stored_block_ok
  align := align_ok
  emit_lit := emit_lit_ok
  emit_dist := emit_dist_ok
  emit_tree := emit_tree_ok
  emit_end_block := emit_end_block_ok
  emit_align := emit_align_ok

/-! ## The overlay budget of a dynamic block -/

open ZlibNgF.Math.HuffSymbols (Symbol)
open ZlibNgF.Math.TreesOverlay (Budget)
open ZlibNgF.Math.OverlayDynamic (blockHeader blockCosts Chosen dynamic_budget)

/-- **The dynamic-block budget.** For every `lit_bufsize` `B` that `deflateInit2` can set (`1 << (memLevel + 6)`,
`DCore.lpow`), at most 7 bits waiting before the block (`FlushBlockPre`), and every block of at most `B - 1` valid
symbols that `zng_tr_flush_block` sends with dynamic trees (`Chosen xs`: `opt_lenb < static_lenb`, with `opt_len` and
`static_len` the model sums `optLen xs` / `staticLen xs`), the bits before the first symbol (the waiting bits, the 3
block-type bits and the tree header `blockHeader xs`) and the excess of the symbol costs fit the `sym_buf` overlay. -/
def DynBudget : Prop :=
  ∀ (B b0 : Nat) (xs : List Symbol), (∃ k, 7 ≤ k ∧ k ≤ 15 ∧ B = 2 ^ k) → b0 ≤ 7 → xs.length + 1 ≤ B →
    (∀ s ∈ xs, s.Valid) → Chosen xs → Budget B (b0 + 3 + blockHeader xs) (blockCosts xs)

/-- `DynBudget` holds: `dynamic_budget` (`Math/OverlayTinyBudget.lean`) for each power of two. -/
theorem dynBudget : DynBudget := by
  intro B b0 xs ⟨k, h7, h15, hB⟩ hb0 hn hv hc
  refine dynamic_budget xs ?_ hb0 hn hv hc
  subst hB
  by_cases a7 : k = 7
  · subst a7; left; rfl
  by_cases a8 : k = 8
  · subst a8; right; left; rfl
  by_cases a9 : k = 9
  · subst a9; right; right; left; rfl
  right; right; right
  refine ⟨?_, ?_⟩
  · have : 2 ^ 10 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    exact this
  · have : 2 ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) h15
    exact this

end ZlibNgF.Proof.TreesFactsP
