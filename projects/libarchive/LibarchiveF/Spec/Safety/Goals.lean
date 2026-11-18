import LibarchiveF.Spec.Common.Types

/-!
# Safety goals (`LibarchiveF`)

Strict ISO C17 runtime undefined-behaviour goals and public C translation safety goals.
-/

namespace LibarchiveF.Spec.Safety
open LibarchiveF.Spec

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

/-- Full C-translation safety goal for `libarchive`'s RAR5 format reader
(`archive_read_support_format_rar5.c`). -/
def Goal.c_rar5_format_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

/-- Full C-translation safety goal for `libarchive`'s 7-Zip format reader
(`archive_read_support_format_7zip.c`). -/
def Goal.c_sevenZip_format_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

/-- Full C-translation safety goal for `libarchive`'s PPMd7 decoder and custom sub-allocator
(`archive_ppmd7.c`). -/
def Goal.c_ppmd7_allocator_safety (fn : BufferEntry) : Prop := BufferEntrySafe fn

end LibarchiveF.Spec.Safety
