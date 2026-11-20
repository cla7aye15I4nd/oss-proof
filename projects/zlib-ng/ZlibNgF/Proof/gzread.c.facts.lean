import ZlibNgF.Proof.«inflate.c.extra»
import ZlibNgF.Proof.«gzlib.c.mode»

/-!
# What the read path needs of `inflate` beyond `inflate_ok` (`ZlibNgF`)

`inflate_ok` gives the invariant, the frame and, on `Z_OK`, progress. The gz read path also needs, for every result:
no deflate object changes, the heap stays well formed (proved: `InflateExtra.inflate_extra`), the saved pointers of
the blocks other than the stream's state block stay (the buffers of the gz file are an aligned block whose saved
pointer `zng_free_aligned` reads), and no `gz_header` gets registered on the state (the gz file registers none).

The last two are not proved yet: `InflateExtra` states all of them as one hypothesis, which the read-path lemmas
take; `InflateExtra.of_facts` is where the proof will go.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzRead
open C ZlibNgF.Spec

/-- What `inflate` keeps beyond `inflate_ok`. -/
structure InflateExtra : Prop where
  ok : ∀ h i flush r h', InflateInv.Inv h (some i) → StreamIO h (some i) →
    h.crcTable = ZlibNg.Crc32Tbl.crc_table → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    h'.dstates = h.dstates ∧ h'.dallocs = h.dallocs ∧ (ObjBound h → ObjBound h') ∧ (FreshBlocks h → FreshBlocks h') ∧
    (∀ c, (∀ z, h.streams i = some z → z.state ≠ some c) → h'.savedPtrs c = h.savedPtrs c) ∧
    (∀ hp, RegisteredHeader h' (some i) hp → RegisteredHeader h (some i) hp)

/-- The two facts not proved yet. -/
structure InflateFacts : Prop where
  saved : ∀ h i flush r h', InflateInv.Inv h (some i) → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    ∀ c, (∀ z, h.streams i = some z → z.state ≠ some c) → h'.savedPtrs c = h.savedPtrs c
  header : ∀ h i flush r h', InflateInv.Inv h (some i) → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    ∀ hp, RegisteredHeader h' (some i) hp → RegisteredHeader h (some i) hp

/-- `InflateExtra` from the two facts: the rest is `InflateExtra.inflate_extra`. -/
theorem InflateExtra.of_facts (F : InflateFacts) : InflateExtra := by
  refine ⟨fun h i flush r h' hv hio hc e => ?_⟩
  obtain ⟨d, a, o, f⟩ := ZlibNgF.Proof.InflateExtra.inflate_extra h i flush r h' hv hio hc e
  exact ⟨d, a, o, f, F.saved h i flush r h' hv e, F.header h i flush r h' hv e⟩

end ZlibNgF.Proof.GzRead
