import ZlibNgF.Proof.«trees.c.compress»

/-!
# The static branch of `zng_tr_flush_block` (`ZlibNgF`)

On `SH` heaps: `zng_tr_emit_tree(s, STATIC_TREES, last)` followed by `compress_block` with the static trees and the
read of `static_len`, from a state with no pending bytes and fewer than 8 bits waiting (`FlushBlockPre`). The overlay
budget of the static block holds unconditionally (`compress_static_SH`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesFlush
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateBits ZlibNgF.Proof.TreesEmitP ZlibNgF.Proof.TreesCompress
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- What a block body leaves: new pending count and bit buffer, the bytes changed only in `pending_buf` after the
pending bytes, the last store inside `pending_buf`, fewer than 64 bits waiting. -/
def BlkPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo : Nat)
    (H' : Heap) : Prop :=
  ∃ (np : UInt32) (bb : UInt64) (bv : UInt32) (d' : Array UInt8),
    H' = SH H i z b { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + 4 * st.lit_bufsize.toNat + 9) d' ∧ bv.toNat < 64 ∧
    st.pending.toNat ≤ np.toNat ∧ np.toNat + 8 ≤ 4 * st.lit_bufsize.toNat + 9

/-- The static branch of `zng_tr_flush_block`: the 3 header bits, `compress_block` with the static trees, the read
of `static_len`. -/
theorem static_branch_SH {pbo sbo n : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hsb : st.sym_buf = .val (.ref (.heap b) sbo)) (hsn : st.sym_next.toNat = 3 * n)
    (hsbo : sbo = pbo + st.lit_bufsize.toNat + 8) (hend : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size)
    (hn : n ≤ st.lit_bufsize.toNat) (hB : 128 ≤ st.lit_bufsize.toNat) (hlb : st.lit_bufsize.toNat ≤ 32768)
    (hdist : ∀ j, j < n → symDist d sbo j ≤ 32768) (v0 : 0 ≤ st.bi_valid.toInt) (v8 : st.bi_valid.toInt < 8)
    (hp0 : st.pending.toNat = 0) (last : Int32) (hl0 : 0 ≤ last.toInt) (hl1 : last.toInt ≤ 1) :
    Sat (SH H i z b st d) (do
      ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STATIC_TREES last
      ZlibNg.Trees.compress_block (some b) (.ref .static_ltree 0) (.ref .static_dtree 0)
      let _ ← rdD (some b) (·.static_len))
      (fun _ H' => BlkPost H i z b st d pbo H') := by
  refine Sat.bind (Sat.mono (emit_tree_SH hpb v0 (by omega) (by omega) (by omega) _ last (by decide) (by decide)
    (by show 2 * (1 : Int32).toInt + last.toInt < _; simp; omega)) ?_)
  rintro _ _ ⟨np, bb, bv, d1, rfl, w1, hacc1, hbv1, hle1, hge1⟩
  have e1 := toInt32_toInt bv hbv1
  have hsz1 : d1.size = d.size := w1.1
  have hdist1 : ∀ j, j < n → symDist d1 sbo j ≤ 32768 := fun j hj => by
    have a0 := w1.2 (sbo + 3 * j) (Or.inr (by omega))
    have a1 := w1.2 (sbo + 3 * j + 1) (Or.inr (by omega))
    unfold symDist; rw [a0, a1]; exact hdist j hj
  refine Sat.bind (Sat.mono (compress_static_SH (st := { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 })
    (d := d1) (n := n) hpb hsb hsn hsbo (by dsimp only; omega) hn (by dsimp only; omega) hlb hdist1
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)) ?_)
  rintro _ _ ⟨np2, bb2, bv2, d2, rfl, w2, -, hbv2, hle2, hge2⟩
  dsimp only at w2 hle2 hge2
  refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.pure ⟨np2, bb2, bv2, d2, rfl, ?_, hbv2, by omega, hge2⟩))
  exact WrIn.cat w1 w2 (by omega) (by omega)

end

end ZlibNgF.Proof.TreesFlush
