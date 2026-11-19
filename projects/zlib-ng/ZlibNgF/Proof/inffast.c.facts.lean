import ZlibNgF.Proof.«chunkset.copy»
import ZlibNgF.Proof.«inflate.c.facts»

/-!
# The `CopyFacts` statement for `chunkmemset_safe_c` (`ZlibNgF`)

`copyFacts_small` is the body of `InflateFacts.CopyFacts.memset` with one more hypothesis: the output block has fewer
than `2 ^ 63` bytes. Without it the statement is false in the model: `CHUNKMEMSET` computes `out - from`
(`chunkset_tpl.h:118`), which faults (ISO C17 §6.5.6p9, the difference is not a `ptrdiff_t`) when `d ≥ 2 ^ 63`; the
statement allows `d ≤ p` for any `p`. On LP64 Linux no object exceeds `PTRDIFF_MAX` bytes, so the hypothesis is the
platform's, not a narrowing of the caller's input; a bound `d < 2 ^ 63` would serve as well.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastFacts
open C
open ZlibNgF.Proof.InflateSync (Sat)
open ZlibNgF.Proof.ChunkMem
open ZlibNgF.Proof.ChunkCopy

theorem copyFacts_small (h : Heap) (bo p d : Nat) (data : Array UInt8) (len left : UInt64)
    (hd : h.bytes bo = some data) (hd1 : 1 ≤ d) (hdp : d ≤ p) (hl : p + left.toNat ≤ data.size) (hll : len ≤ left)
    (_ : 1 ≤ left) (hN : data.size < 2 ^ 63) :
    ∃ data' : Array UInt8,
      C.run (ZlibNg.ChunksetC.chunkmemset_safe_c (.ref (.heap bo) p) (.ref (.heap bo) (p - d)) len left) h =
        .ok (.ref (.heap bo) (p + len.toNat), { h with bytes := upd h.bytes bo (some data') }) ∧
      data'.size = data.size ∧ ∀ j, (j < p ∨ p + left.toNat ≤ j) → data'[j]! = data[j]! := by
  obtain ⟨q, H', e, hq, r⟩ := chunkmemset_safe_c_safe hd rfl hN (o := p) (f := p - d) len left hl (by omega)
  have hmin : min len.toNat left.toNat = len.toNat := by
    rw [UInt64.le_iff_toNat_le] at hll; omega
  obtain ⟨a0, a, e0, e1, s0, s1, hp⟩ := r.blk
  rw [hd] at e0; cases e0
  refine ⟨a, ?_, s1.trans s0.symm, hp⟩
  have heq := r.eq
  rw [e1] at heq
  rw [hq, hmin, heq] at e
  exact e

end ZlibNgF.Proof.InffastFacts
