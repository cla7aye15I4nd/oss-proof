import ZlibNgF.Proof.«inflate.c.extra»
import ZlibNgF.Proof.«gzlib.c.mode»

/-!
# What the read path needs of `inflate` beyond `inflate_ok` (`ZlibNgF`)

`inflate_ok` gives the invariant, the frame and, on `Z_OK`, progress. The gz read path also needs, for every result:
no deflate object changes, the heap stays well formed (proved: `InflateExtra.inflate_extra`), the saved pointers of
the blocks other than the stream's state block stay (the buffers of the gz file are an aligned block whose saved
pointer `zng_free_aligned` reads), and no `gz_header` gets registered on the state (the gz file registers none).

All of them are proved: `inflateExtra` (from `InflateExtra.inflate_extra`, `inflate_saved` and `inflate_header`).
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

/-- `InflateExtra` holds: `InflateExtra.inflate_extra`, `inflate_saved` and `inflate_header`. -/
theorem inflateExtra : InflateExtra := by
  refine ⟨fun h i flush r h' hv hio hc e => ?_⟩
  obtain ⟨d, a, o, f⟩ := ZlibNgF.Proof.InflateExtra.inflate_extra h i flush r h' hv hio hc e
  exact ⟨d, a, o, f, ZlibNgF.Proof.InflateExtra.inflate_saved h i flush r h' hv e,
    ZlibNgF.Proof.InflateExtra.inflate_header h i flush r h' hv hio hc e⟩

end ZlibNgF.Proof.GzRead
