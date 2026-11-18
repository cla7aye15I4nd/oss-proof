import ZstdF.Spec.Common.Types

/-!
# Safety goals (`ZstdF`)

Strict ISO C17 runtime undefined-behaviour goals and public C translation safety goals.
-/

namespace ZstdF.Spec.Safety
open ZstdF.Spec

/-- `NULL + 0` raises `Fault.ub` (ISO C17 §6.5.6p8). -/
def Goal.null_ptr_add_zero_ub : Prop :=
  ∀ (h : C.Heap), FaultsWithUb (C.Ptr.add (.null : C.BPtr) 0) h

/-- Adding `0` to a freed/dangling pointer raises `Fault.ub` (ISO C17 §6.5.6p8, §6.2.4p2). -/
def Goal.dangling_ptr_add_zero_ub : Prop :=
  ∀ (h : C.Heap) (r : C.BRef) (off : Nat),
    C.Space.get h r = (none : Option (Array UInt8)) →
    FaultsWithUb (C.Ptr.add (.ref r off) 0) h

/-- `NULL - NULL` raises `Fault.ub` (ISO C17 §6.5.6p9). -/
def Goal.null_ptr_diff_null_ub : Prop :=
  ∀ (h : C.Heap), FaultsWithUb (C.Ptr.diff (.null : C.BPtr) .null) h

/-- Subtracting pointers into distinct allocations raises `Fault.ub` (ISO C17 §6.5.6p9). -/
def Goal.cross_object_ptr_diff_ub : Prop :=
  ∀ (h : C.Heap) (r1 r2 : C.BRef) (o1 o2 : Nat),
    r1 ≠ r2 →
    FaultsWithUb (C.Ptr.diff (.ref r1 o1) (.ref r2 o2)) h

/-- `memset(NULL, b, 0)` raises `Fault.ub` even when `n = 0` (ISO C17 §7.24.1p2). -/
def Goal.null_memset_zero_ub : Prop :=
  ∀ (h : C.Heap) (b : UInt8), FaultsWithUb (C.Ptr.memset (.null : C.BPtr) b 0) h

/-- Full C-translation safety goal for streaming decompression (`ZSTD_decompressStream` and `ZSTD_DCtx`
parameter/reset operations in `lib/decompress/zstd_decompress.c`). -/
def Goal.c_decompressStream_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

/-- Full C-translation safety goal for one-shot decompression (`ZSTD_decompress`, `ZSTD_decompressDCtx`,
`ZSTD_decompress_usingDict`, `ZSTD_decompress_usingDDict`). -/
def Goal.c_decompress_oneshot_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

/-- Full C-translation safety goal for raw and formatted (`0xEC30A437`) dictionary parsing and borrowed
prefix references (`ZSTD_createDDict`, `ZSTD_DCtx_loadDictionary`, `ZSTD_DCtx_refDDict`, `ZSTD_DCtx_refPrefix`). -/
def Goal.c_ddict_lifecycle_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

/-- Full C-translation safety goal for frame inspection and error/version queries (`ZSTD_getFrameContentSize`,
`ZSTD_findFrameCompressedSize`, `ZSTD_getDictID_fromFrame`, `ZSTD_isError`, `ZSTD_getErrorName`). -/
def Goal.c_frame_query_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

end ZstdF.Spec.Safety
