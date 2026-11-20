import ZlibNgF.Proof.«deflate.c.gz.init»
import ZlibNgF.Proof.«gzwrite.c.needs»

/-!
# The deflate side of the gz write layer (`ZlibNgF`)

The parts of `GzWriteNeeds.DeflateGz` proved so far, stated with the definitions of `Proof/gzwrite.c.needs.lean`:
`deflateInit2_` and `deflateReset` (from `Proof/deflate.c.gz.init.lean`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateGz
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.GzWriteNeeds (DKeep BufSame)

/-- The `deflateInit2_` part of `DeflateGz`. -/
theorem init2_part : ∀ (h h' : Heap) (s : StreamPtr) (level method wb ml strat : Int32) (version : BPtr)
    (size r : Int32) (z : ZStream), StreamAt h s z → DInitReady h s → DFreshBlocks h →
    C.run (deflateInit2_ s level method wb ml strat version size) h = .ok (r, h') →
    ∃ z', StreamAt h' s z' ∧ z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧ z'.next_out = z.next_out ∧
      z'.avail_out = z.avail_out ∧
      (r ≠ Z_OK → z'.state = z.state ∧ (z'.zalloc = .null ∨ z'.zalloc = .zcalloc) ∧
        (z'.zfree = .null ∨ z'.zfree = .zcfree)) ∧ DKeep h h' s ∧
      (r = Z_OK → ∃ sb, z'.state = some sb ∧ h.nextBlk ≤ sb) :=
  DeflateGzInit.init2_gz

/-- The `deflateReset` part of `DeflateGz`. -/
theorem reset_part : ∀ (h h' : Heap) (s : StreamPtr) (r : Int32) (z : ZStream), DInv h s → StreamAt h s z →
    C.run (deflateReset s) h = .ok (r, h') → ∃ z', StreamAt h' s z' ∧ BufSame z z' ∧ DKeep h h' s :=
  DeflateGzInit.reset_gz

end ZlibNgF.Proof.DeflateGz
