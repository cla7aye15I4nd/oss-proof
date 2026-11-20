import ZlibNgF.Proof.«trees_emit.h.emit»
import ZlibNgF.Math.TreesOverlay

/-!
# The `sym_buf` overlay with static trees (`ZlibNgF`)

The bit cost of one symbol of `compress_block` with the static trees, read off the tables of `trees_tbl.h`: a literal
costs `static_ltree[lc].Len ≤ 9` bits; a match costs the length code (`static_ltree[257 + code].Len ≤ 8`) and its
extra bits (`≤ 5`, at most 13 together), the distance code (`static_dtree[d].Len = 5`) and its extra bits (`≤ 13`):
at most 31 bits. With `Math/TreesOverlay.lean` (`static_budget`) a static block of at most `lit_bufsize - 1`
symbols never overtakes its unread symbols.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesOverlayP
open C ZlibNg.Deflate ZlibNgF.Math.TreesOverlay

/-- Length code and length extra bits of the static literal tree: at most 13 bits. -/
theorem static_len_cost : ∀ k : Fin 29,
    (static_ltree[k.val + 257]!).dl.toNat + (lmask_extra[k.val]!.toUInt32 >>> 8).toNat ≤ 13 := by
  decide +kernel

/-- Distance code and distance extra bits of the static distance tree: at most 18 bits. -/
theorem static_dist_cost : ∀ k : Fin 30,
    (static_dtree[k.val]!).dl.toNat + (dmask_extra[k.val]! >>> 16).toNat ≤ 18 := by
  decide +kernel

/-- A literal of the static literal tree: at most 9 bits. -/
theorem static_lit_cost : ∀ k : Fin 256, (static_ltree[k.val]!).dl.toNat ≤ 9 := by
  decide +kernel

/-- The static cost of a match with length symbol `lc ≤ 255` and distance code `d < 30`. -/
def staticMatchCost (lc d : Nat) : Nat :=
  (static_ltree[(zng_length_code[lc]!).toNat + 257]!).dl.toNat +
    (lmask_extra[(zng_length_code[lc]!).toNat]!.toUInt32 >>> 8).toNat +
    (static_dtree[d]!).dl.toNat + (dmask_extra[d]! >>> 16).toNat

theorem staticMatchCost_le (lc d : Nat) (hlc : lc < 256) (hd : d < 30) : staticMatchCost lc d ≤ 31 := by
  have hc : (zng_length_code[lc]!).toNat < 29 :=
    UInt8.lt_iff_toNat_lt.mp (ZlibNgF.Proof.TreesEmitP.lc_lt ⟨lc, hlc⟩)
  have h1 := static_len_cost ⟨_, hc⟩
  have h2 := static_dist_cost ⟨d, hd⟩
  rw [Fin.val_mk] at h1 h2
  unfold staticMatchCost
  omega

/-- A static block of at most `B - 1` symbols whose costs are static literal or match costs fits the overlay
budget, with up to 63 bits waiting before it, for every `lit_bufsize = B ≥ 52`. -/
theorem static_block_budget {B b0 : Nat} {costs : List Nat} (hB : 52 ≤ B) (hb0 : b0 < 64)
    (hn : costs.length + 1 ≤ B)
    (hc : ∀ c ∈ costs, (∃ lc, lc < 256 ∧ c = (static_ltree[lc]!).dl.toNat) ∨
      (∃ lc d, lc < 256 ∧ d < 30 ∧ c = staticMatchCost lc d)) :
    Budget B (b0 + 3) costs := by
  refine static_budget hB hb0 hn (fun c hm => ?_)
  rcases hc c hm with ⟨lc, hlc, e⟩ | ⟨lc, d, hlc, hd, e⟩
  · have h := static_lit_cost ⟨lc, hlc⟩
    rw [Fin.val_mk, ← e] at h
    omega
  · have h := staticMatchCost_le lc d hlc hd
    rw [← e] at h
    omega

end ZlibNgF.Proof.TreesOverlayP
