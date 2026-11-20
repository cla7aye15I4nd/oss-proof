import ZlibNgF.Spec.Common.Types

/-!
# Functional goals (`ZlibNgF`)

Exact value specifications for `zutil.c`, `adler32.c`, `crc32_braid_comb.c`, and `compress.c`.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec.Functional
open ZlibNgF.Spec

/-- `zlibVersion()` returns a read-only pointer to `"1.3.2.zlib-ng\0"` and preserves the heap. -/
def Goal.zlibVersion_functional : Prop :=
  ∀ (h : C.Heap),
    ∃ p, C.run ZlibNg.Zutil.zlibVersion h = .ok (p, h) ∧ StaticCString h p "1.3.2.zlib-ng"

/-- `zlibCompileFlags()` on LP64 Linux (`uInt = 4`, `uLong = 8`, `voidpf = 8`, `z_off_t = 8`) returns `0xa9`. -/
def Goal.zlibCompileFlags_functional : Prop :=
  ∀ (h : C.Heap), C.run ZlibNg.Zutil.zlibCompileFlags h = .ok (0xa9, h)

/-- Expected error string of `zError(err)` (`zutil.c:10-21, 99-101`). -/
def expectedZError (err : Int32) : String :=
  if err == 2 then "need dictionary"
  else if err == 1 then "stream end"
  else if err == 0 then ""
  else if err == -1 then "file error"
  else if err == -2 then "stream error"
  else if err == -3 then "data error"
  else if err == -4 then "insufficient memory"
  else if err == -5 then "buffer error"
  else if err == -6 then "incompatible version"
  else ""

/-- `zError(err)` returns a static read-only pointer to `expectedZError err` for every `Int32`. -/
def Goal.zError_functional : Prop :=
  ∀ (h : C.Heap) (err : Int32),
    ∃ p, C.run (ZlibNg.Zutil.zError err) h = .ok (p, h) ∧ StaticCString h p (expectedZError err)

/-- For every power-of-two alignment `align = 2 ^ k` with `3 ≤ k ≤ 31` (e.g. `align = 64`), any non-null pointer
returned by `zng_alloc_aligned(size, align)` with `8 + size + align < 2^32` has runtime address divisible by
`align` under every `baseAddr` oracle. -/
def Goal.zng_alloc_aligned_alignment : Prop :=
  ∀ (h : C.Heap) (size align : UInt32) (k : Nat),
    3 ≤ k → k ≤ 31 → align.toNat = 2 ^ k →
    8 + size.toNat + align.toNat < 2 ^ 32 →
    ∀ ret h',
      C.run (ZlibNg.Zutil.zng_alloc_aligned size align) h = .ok (ret, h') →
      ret ≠ .null →
      ∃ addr, C.run (C.addrOf ret) h' = .ok (addr, h') ∧ addr.toNat % align.toNat = 0

/-- `adler32_z` returns `1` for a `NULL` buffer with any `len`, and exact RFC 1950
`adler32Update seed bytes` on every readable buffer of arbitrary 64-bit length (including across `NMAX = 5552`
block boundaries and non-canonical seeds). -/
def Goal.adler32_z_functional : Prop :=
  ∀ (h : C.Heap) (seed : UInt64) (buf : C.BPtr) (len : UInt64) (bytes : List UInt8),
    BufferBytes h buf len.toNat bytes →
    C.run (ZlibNg.Adler32.adler32_z seed buf len) h =
      .ok ((if buf = .null then 1 else ZlibNgF.Math.Adler32.adler32Update seed bytes), h)

/-- `adler32` returns `1` for a `NULL` buffer with any `len`, and exact RFC 1950
`adler32Update seed bytes` on every readable buffer. -/
def Goal.adler32_functional : Prop :=
  ∀ (h : C.Heap) (seed : UInt64) (buf : C.BPtr) (len : UInt32) (bytes : List UInt8),
    BufferBytes h buf len.toNat bytes →
    C.run (ZlibNg.Adler32.adler32 seed buf len) h =
      .ok ((if buf = .null then 1 else ZlibNgF.Math.Adler32.adler32Update seed bytes), h)

/-- Shared functional specification for `adler32_combine` and `adler32_combine64`:
negative `len2` returns `0xffffffff`, and genuine checksums `adler32 xs`, `adler32 ys` combine to `adler32 (xs ++ ys)`. -/
def AdlerCombineSpec (prog : UInt64 → UInt64 → Int64 → C.M UInt64) : Prop :=
  ∀ (h : C.Heap) (adler1 adler2 : UInt64) (len2 : Int64),
    ∃ r,
      C.run (prog adler1 adler2 len2) h = .ok (r, h) ∧
      (len2 < 0 → r = 0xffffffff) ∧
      (∀ xs ys : List UInt8,
        adler1.toUInt32 = ZlibNgF.Math.Adler32.adler32 xs →
        adler2.toUInt32 = ZlibNgF.Math.Adler32.adler32 ys →
        len2.toInt = (ys.length : Int) →
        r = (ZlibNgF.Math.Adler32.adler32 (xs ++ ys)).toUInt64)

/-- `adler32_combine` functional specification. -/
def Goal.adler32_combine_functional : Prop := AdlerCombineSpec ZlibNg.Adler32.adler32_combine

/-- `adler32_combine64` functional specification. -/
def Goal.adler32_combine64_functional : Prop := AdlerCombineSpec ZlibNg.Adler32.adler32_combine64

/-- Rejection semantics of `crc32_combine*`: negative `len2` returns `0` in `crc32_combine`,
`crc32_combine64`, `crc32_combine_gen`, and `crc32_combine_gen64`. -/
def Goal.crc32_combine_rejection_functional : Prop :=
  ∀ (h : C.Heap) (crc1 crc2 : UInt64) (len2 : Int64),
    len2 < 0 →
      C.run (ZlibNg.Crc32Comb.crc32_combine crc1 crc2 len2) h = .ok (0, h) ∧
      C.run (ZlibNg.Crc32Comb.crc32_combine64 crc1 crc2 len2) h = .ok (0, h) ∧
      C.run (ZlibNg.Crc32Comb.crc32_combine_gen len2) h = .ok (0, h) ∧
      C.run (ZlibNg.Crc32Comb.crc32_combine_gen64 len2) h = .ok (0, h)

/-- Exact `deflate_quick` + zlib-wrapper compressed bound formula (`compress.c:104-110`) for all
`sourceLen ≤ 0xe38e38e38e38e377`; above it the sum wraps and `compressBound_z` returns `(z_size_t)-1`
(`docs/en/deviations.md`). -/
def Goal.compressBound_functional : Prop :=
  ∀ (h : C.Heap) (sourceLen : UInt64),
    sourceLen.toNat ≤ 0xe38e38e38e38e377 →
    ∃ r,
      C.run (ZlibNg.Compress.compressBound sourceLen) h = .ok (r, h) ∧
      r.toNat = sourceLen.toNat
        + (if sourceLen.toNat = 0 then 1 else 0)
        + (if sourceLen.toNat < 9 then 1 else 0)
        + (sourceLen.toNat + 7) / 8
        + 9 ∧
      sourceLen.toNat < r.toNat

/-- `z_size_t compressBound_z(z_size_t sourceLen)`: the same exact `deflate_quick` + zlib-wrapper bound
(`compress.c:104-110`) for all `sourceLen ≤ 0xe38e38e38e38e377`; above it the sum wraps and the function
returns `(z_size_t)-1` (`docs/en/deviations.md`). -/
def Goal.compressBound_z_functional : Prop :=
  ∀ (h : C.Heap) (sourceLen : UInt64),
    sourceLen.toNat ≤ 0xe38e38e38e38e377 →
    ∃ r,
      C.run (ZlibNg.Compress.compressBound_z sourceLen) h = .ok (r, h) ∧
      r.toNat = sourceLen.toNat
        + (if sourceLen.toNat = 0 then 1 else 0)
        + (if sourceLen.toNat < 9 then 1 else 0)
        + (sourceLen.toNat + 7) / 8
        + 9 ∧
      sourceLen.toNat < r.toNat

end ZlibNgF.Spec.Functional
