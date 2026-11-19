import ZlibNgF.Runtime.Libc
import ZlibNgF.Math.Adler32
import ZlibNgF.ZlibNg.«zutil.c»
import ZlibNgF.ZlibNg.«adler32.c»
import ZlibNgF.ZlibNg.«crc32.c»
import ZlibNgF.ZlibNg.«compress.c»

/-!
# Shared specification vocabulary (`ZlibNgF`)

Common heap predicates, buffer views, and static-table invariants shared by `ZlibNgF.Spec.Safety` and
`ZlibNgF.Spec.Functional`. No `Goal.*` definitions live here.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec

/-- `m` faults on `h` with `Fault.ub` (not `outOfFuel` and not `.ok`). -/
def FaultsWithUb {α : Type} (m : C.M α) (h : C.Heap) : Prop :=
  ∃ msg : String, C.run m h = .error (.ub msg)

/-- Bytes of a caller buffer: either `NULL` (with any `length` and the empty byte list; `zlib.h` lets a
checksum caller pass `Z_NULL` with any length) or a live slice `[off, off + length)` of a heap, read-only
static, or string-literal byte object. -/
def BufferBytes (h : C.Heap) (pointer : C.BPtr) (length : Nat) (bytes : List UInt8) : Prop :=
  (pointer = .null ∧ bytes = []) ∨
  ∃ r off data,
    pointer = .ref r off ∧
    C.Space.get h r = some data ∧
    off + length ≤ data.size ∧
    bytes = (data.toList.drop off).take length

/-- Static CRC-32 tables (`crc_table[256]` and `x2n_table[32]`) are initialized to `zlib-ng`'s constants. -/
def CrcGlobals (h : C.Heap) : Prop :=
  h.crcTable = ZlibNg.Crc32Tbl.crc_table ∧
  h.x2nTable = ZlibNg.Crc32Tbl.x2n_table

/-- `p` points to the static NUL-terminated string literal `expected`. -/
def StaticCString (h : C.Heap) (p : C.BPtr) (expected : String) : Prop :=
  ∃ i : Nat,
    p = .ref (.str i) 0 ∧
    C.strTable[i]? = some expected ∧
    C.Space.get h (C.BRef.str i) = some (C.Heap.litBytes expected)

/-- Safety and round-trip deallocation postcondition for `zng_alloc_aligned(size, align)`:
either allocation is cleanly refused (`.null`), or `ret` points into a fresh live writable heap block with
an 8-byte pointer header before `ret`, `size` writable bytes starting at `ret`, and `zng_free_aligned ret`
reclaims the underlying allocation without faulting. -/
def AlignedAllocValid (h h' : C.Heap) (size : UInt32) (ret : C.BPtr) : Prop :=
  (ret = .null ∧ h'.bytes = h.bytes ∧ h'.savedPtrs = h.savedPtrs) ∨
  (ret = .ref (.heap h.nextBlk) (match ret with | .ref _ o => o | .null => 0) ∧
    ∃ off data,
      ret = .ref (.heap h.nextBlk) off ∧
      h'.bytes h.nextBlk = some data ∧
      8 ≤ off ∧
      off + size.toNat ≤ data.size ∧
      C.run (ZlibNg.Zutil.zng_free_aligned ret) h' =
        .ok ((), { h' with bytes := C.upd h'.bytes h.nextBlk none, savedPtrs := C.upd h'.savedPtrs h.nextBlk none }))

end ZlibNgF.Spec
