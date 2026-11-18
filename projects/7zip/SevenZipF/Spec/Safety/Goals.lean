import SevenZipF.Spec.Common.Types

/-!
# Safety goals (`SevenZipF`)

Strict ISO C17 runtime undefined-behaviour goals and public C translation safety goals.
-/

namespace SevenZipF.Spec.Safety
open SevenZipF.Spec

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

/-- Full C-translation safety goal for `.7z` archive opening and cached solid-folder extraction
(`SzArEx_Open`, `SzArEx_Extract`, `SzArEx_Free` in `C/7zArcIn.c` and `C/7zDec.c`). -/
def Goal.c_szArEx_extract_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

/-- Full C-translation safety goal for the 4-stream BCJ2 x86 filter (`Bcj2Dec_Decode` in `C/Bcj2.c`). -/
def Goal.c_bcj2Dec_decode_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

/-- Full C-translation safety goal for PPMd7 context decoding and its custom arena sub-allocator
(`Ppmd7_Alloc`, `Ppmd7_Init`, `Ppmd7_DecodeSymbol` in `C/Ppmd7.c` and `C/Ppmd7Dec.c`). -/
def Goal.c_ppmd7_decode_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

/-- Full C-translation safety goal for LZMA and LZMA2 chunked decompression
(`LzmaDec_DecodeToBuf`, `Lzma2Dec_DecodeToBuf` in `C/LzmaDec.c` and `C/Lzma2Dec.c`). -/
def Goal.c_lzma2Dec_decode_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

end SevenZipF.Spec.Safety
