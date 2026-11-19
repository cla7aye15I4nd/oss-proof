import ZlibNgF.Spec.Common.Types

/-!
# Safety goals (`ZlibNgF`)

Strict ISO C17 runtime undefined-behaviour goals, proved C-translation safety and non-vacuity goals for
`zutil.c`, `adler32.c`, `crc32.c` / `crc32_braid_c.c` / `crc32_braid_comb.c`, and `compress.c`. Safety of the
other public functions is not done.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec.Safety
open ZlibNgF.Spec

/-! ## Strict ISO C17 runtime UB policy goals -/

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

/-! ## `zutil.c` safety & non-vacuity goals -/

/-- `const char *zlibVersion(void)`: never faults and leaves the heap unchanged. -/
def Goal.zlibVersion_safety : Prop :=
  ∀ (h : C.Heap), ∃ p, C.run ZlibNg.Zutil.zlibVersion h = .ok (p, h)

/-- `unsigned long zlibCompileFlags(void)`: never faults and leaves the heap unchanged. -/
def Goal.zlibCompileFlags_safety : Prop :=
  ∀ (h : C.Heap), ∃ flags, C.run ZlibNg.Zutil.zlibCompileFlags h = .ok (flags, h)

/-- `const char *zError(int err)`: never faults for any `Int32` (including `INT32_MIN`) and preserves the heap. -/
def Goal.zError_safety : Prop :=
  ∀ (h : C.Heap) (err : Int32), ∃ p, C.run (ZlibNg.Zutil.zError err) h = .ok (p, h)

/-- `zcalloc` followed by `zcfree`: never faults for any `opaque` pointer and any 32-bit `items`, `size`. -/
def Goal.zcalloc_zcfree_safety : Prop :=
  ∀ (h : C.Heap) (opq : C.BPtr) (items size : UInt32),
    ∃ p h1 h2,
      C.run (ZlibNg.Zutil.zcalloc opq items size) h = .ok (p, h1) ∧
      C.run (ZlibNg.Zutil.zcfree opq p) h1 = .ok ((), h2)

/-- `zng_alloc_aligned` + `zng_free_aligned` (internal; its only caller `gz_buffer_alloc` passes `align = 64` and
`size ≤ 3 * 2^30`): for every `align ≥ 8` and every `size` with `8 + size + align < 2^32` (the 32-bit
`alloc_size` does not wrap), allocation never faults and every non-null return value has a valid 8-byte header,
`size` writable bytes in bounds, and safe `zng_free_aligned` reclamation. -/
def Goal.zng_alloc_aligned_safety : Prop :=
  ∀ (h : C.Heap) (size align : UInt32),
    8 ≤ align.toNat →
    8 + size.toNat + align.toNat < 2 ^ 32 →
    ∃ ret h',
      C.run (ZlibNg.Zutil.zng_alloc_aligned size align) h = .ok (ret, h') ∧
      AlignedAllocValid h h' size ret

/-- Non-vacuity witness for `zng_alloc_aligned`: on `size = 0xC0000000` (`3 * 2^30`, the largest request of
`gz_buffer_alloc`, made for a 1 GiB `gzbuffer` on a write stream), `align = 64`, `zng_alloc_aligned` succeeds on
`Heap.empty` and returns a live non-null buffer of at least `0xC0000000` writable bytes. -/
def Goal.zng_alloc_aligned_nonvacuous : Prop :=
  ∃ off h' data,
    C.run (ZlibNg.Zutil.zng_alloc_aligned 0xc0000000 64) C.Heap.empty = .ok (.ref (.heap 0) off, h') ∧
    h'.bytes 0 = some data ∧
    8 ≤ off ∧
    off + (0xc0000000 : UInt32).toNat ≤ data.size

/-! ## `adler32.c` / `adler32_c.c` safety & non-vacuity goals -/

/-- `unsigned long adler32(unsigned long adler, const unsigned char *buf, unsigned int len)`:
safe and heap-preserving on every `BufferBytes` buffer, including `NULL` with any `len`. -/
def Goal.adler32_safety : Prop :=
  ∀ (h : C.Heap) (seed : UInt64) (buf : C.BPtr) (len : UInt32) (bytes : List UInt8),
    BufferBytes h buf len.toNat bytes →
    ∃ r, C.run (ZlibNg.Adler32.adler32 seed buf len) h = .ok (r, h)

/-- `unsigned long adler32_z(unsigned long adler, const unsigned char *buf, size_t len)`:
safe and heap-preserving on every `BufferBytes` buffer, including `NULL` with any `len`. -/
def Goal.adler32_z_safety : Prop :=
  ∀ (h : C.Heap) (seed : UInt64) (buf : C.BPtr) (len : UInt64) (bytes : List UInt8),
    BufferBytes h buf len.toNat bytes →
    ∃ r, C.run (ZlibNg.Adler32.adler32_z seed buf len) h = .ok (r, h)

/-- Non-vacuity witness for `adler32`: concrete heap buffer of `6000` bytes (`> NMAX = 5552`, so the 64-bit
SWAR blocks run) satisfies `BufferBytes` and executes `adler32` to `.ok`. -/
def Goal.adler32_nonvacuous : Prop :=
  ∃ h buf bytes r,
    buf ≠ .null ∧
    bytes.length = 6000 ∧
    BufferBytes h buf 6000 bytes ∧
    C.run (ZlibNg.Adler32.adler32 1 buf 6000) h = .ok (r, h)

/-- `unsigned long adler32_combine(unsigned long adler1, unsigned long adler2, z_off_t len2)`:
safe and heap-preserving for all `UInt64` checksums and all signed `Int64` lengths (including negative). -/
def Goal.adler32_combine_safety : Prop :=
  ∀ (h : C.Heap) (adler1 adler2 : UInt64) (len2 : Int64),
    ∃ r, C.run (ZlibNg.Adler32.adler32_combine adler1 adler2 len2) h = .ok (r, h)

/-- `unsigned long adler32_combine64(unsigned long adler1, unsigned long adler2, z_off64_t len2)`:
safe and heap-preserving for all `UInt64` checksums and all signed `Int64` lengths. -/
def Goal.adler32_combine64_safety : Prop :=
  ∀ (h : C.Heap) (adler1 adler2 : UInt64) (len2 : Int64),
    ∃ r, C.run (ZlibNg.Adler32.adler32_combine64 adler1 adler2 len2) h = .ok (r, h)

/-! ## `crc32.c` / `crc32_braid_c.c` / `crc32_braid_comb.c` safety & non-vacuity goals -/

/-- `const uint32_t *get_crc_table(void)`: returns a valid read-only pointer to all 256 `crc_table` entries. -/
def Goal.get_crc_table_safety : Prop :=
  ∀ (h : C.Heap),
    CrcGlobals h →
    ∃ p tbl,
      C.run ZlibNg.Crc32.get_crc_table h = .ok (p, h) ∧
      p = .ref .st_crc_table 0 ∧
      C.Space.get h C.URef.st_crc_table = some tbl ∧
      C.Space.ro h C.URef.st_crc_table = true ∧
      tbl.size = 256

/-- `unsigned long crc32(unsigned long crc, const unsigned char *buf, unsigned int len)`:
safe and heap-preserving over every `BufferBytes` slice and arbitrary `h.baseAddr` origin alignment. -/
def Goal.crc32_safety : Prop :=
  ∀ (h : C.Heap) (seed : UInt64) (buf : C.BPtr) (len : UInt32) (bytes : List UInt8),
    CrcGlobals h →
    BufferBytes h buf len.toNat bytes →
    ∃ r, C.run (ZlibNg.Crc32.crc32 seed buf len) h = .ok (r, h)

/-- `unsigned long crc32_z(unsigned long crc, const unsigned char *buf, size_t len)`:
safe and heap-preserving over every `BufferBytes` slice and arbitrary `h.baseAddr` origin alignment. -/
def Goal.crc32_z_safety : Prop :=
  ∀ (h : C.Heap) (seed : UInt64) (buf : C.BPtr) (len : UInt64) (bytes : List UInt8),
    CrcGlobals h →
    BufferBytes h buf len.toNat bytes →
    ∃ r, C.run (ZlibNg.Crc32.crc32_z seed buf len) h = .ok (r, h)

/-- Non-vacuity witness for `crc32_z`: concrete unaligned (`baseAddr = 3`) 128-byte buffer (`≥ 47`, exercising
alignment prefix + 5-way 64-bit braided kernel + tail loops) executes `crc32_z` cleanly to `.ok`. -/
def Goal.crc32_nonvacuous : Prop :=
  ∃ h buf bytes r,
    CrcGlobals h ∧
    buf ≠ .null ∧
    bytes.length = 128 ∧
    BufferBytes h buf 128 bytes ∧
    C.run (ZlibNg.Crc32.crc32_z 0 buf 128) h = .ok (r, h)

/-- `unsigned long crc32_combine_gen(z_off_t len2)`: terminates without fault and preserves the heap for every
signed `Int64` length (including negative `len2 < 0`, which `zlib.h` excludes and which returns 0). -/
def Goal.crc32_combine_gen_safety : Prop :=
  ∀ (h : C.Heap) (len2 : Int64),
    CrcGlobals h →
    ∃ r, C.run (ZlibNg.Crc32Comb.crc32_combine_gen len2) h = .ok (r, h)

/-- `unsigned long crc32_combine_gen64(z_off64_t len2)`: terminates without fault for all `Int64`. -/
def Goal.crc32_combine_gen64_safety : Prop :=
  ∀ (h : C.Heap) (len2 : Int64),
    CrcGlobals h →
    ∃ r, C.run (ZlibNg.Crc32Comb.crc32_combine_gen64 len2) h = .ok (r, h)

/-- `unsigned long crc32_combine_op(unsigned long crc1, unsigned long crc2, const unsigned long op)`:
terminates without fault for all `UInt64` checksums and every `op` whose low 32 bits are not zero. `zlib.h`
allows only an `op` made by `crc32_combine_gen` from a non-negative length, which is never 0 (`x^n mod p`);
with low half 0, `multmodp` does not return. -/
def Goal.crc32_combine_op_safety : Prop :=
  ∀ (h : C.Heap) (crc1 crc2 op : UInt64),
    op.toUInt32 ≠ 0 →
    ∃ r, C.run (ZlibNg.Crc32Comb.crc32_combine_op crc1 crc2 op) h = .ok (r, h)

/-- `unsigned long crc32_combine(unsigned long crc1, unsigned long crc2, z_off_t len2)`:
terminates without fault and preserves the heap for all `UInt64` checksums and all signed `Int64` lengths. -/
def Goal.crc32_combine_safety : Prop :=
  ∀ (h : C.Heap) (crc1 crc2 : UInt64) (len2 : Int64),
    CrcGlobals h →
    ∃ r, C.run (ZlibNg.Crc32Comb.crc32_combine crc1 crc2 len2) h = .ok (r, h)

/-- `unsigned long crc32_combine64(unsigned long crc1, unsigned long crc2, z_off64_t len2)`:
terminates without fault and preserves the heap for all `UInt64` checksums and all signed `Int64` lengths. -/
def Goal.crc32_combine64_safety : Prop :=
  ∀ (h : C.Heap) (crc1 crc2 : UInt64) (len2 : Int64),
    CrcGlobals h →
    ∃ r, C.run (ZlibNg.Crc32Comb.crc32_combine64 crc1 crc2 len2) h = .ok (r, h)

/-! ## `compress.c` safety goals -/

/-- `unsigned long compressBound(unsigned long sourceLen)`: never faults and preserves the heap for all `UInt64`. -/
def Goal.compressBound_safety : Prop :=
  ∀ (h : C.Heap) (sourceLen : UInt64),
    ∃ r, C.run (ZlibNg.Compress.compressBound sourceLen) h = .ok (r, h)

end ZlibNgF.Spec.Safety
