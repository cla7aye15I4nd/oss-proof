import ZlibNgF.ZlibNg.«zbuild.h»

/-!
# `compress.c` — compressed size bound (`ZlibNgF`)

Source: `zlib-ng/compress.c:90-121` and `zlib-ng/zutil.h:73-84`,
`ZLIB_COMPAT` LP64 Linux scalar build (`S390_DFLTCC_DEFLATE` and `NO_QUICK_STRATEGY` undefined).
Note: one-shot `compress`, `compress2`, `compress_z` and `compress2_z` depend on `deflateInit` / `deflate` /
`deflateEnd` and are not translated yet.
-/

set_option autoImplicit false

namespace ZlibNg.Compress
open C ZlibNg.Zbuild

/-- `#define ZLIB_WRAPLEN 6` (`zutil.h:73`). -/
def ZLIB_WRAPLEN : UInt64 := 6

/-- `#define DEFLATE_BLOCK_OVERHEAD ((3 + 15 + 6) >> 3)` (`zutil.h:76-79`). -/
def DEFLATE_BLOCK_OVERHEAD : UInt64 := ((3 : UInt64) + 15 + 6) >>> 3

/-- `#define DEFLATE_QUICK_OVERHEAD(x) ((x * (9 - 8) + 7) >> 3)` (`zutil.h:82-83`). -/
def DEFLATE_QUICK_OVERHEAD (x : UInt64) : UInt64 := (x * 1 + 7) >>> 3

/-- `#define DEFLATE_BOUND_COMPLEN(source_len) 0` (`compress.c:19`). -/
def DEFLATE_BOUND_COMPLEN (_source_len : UInt64) : UInt64 := 0

/-- `#define ULONG_MAX` on LP64 Linux. -/
def ULONG_MAX : UInt64 := 0xffffffffffffffff

/-- `z_size_t Z_EXPORT compressBound_z(z_size_t sourceLen)` (`compress.c:91-115`). -/
def compressBound_z (sourceLen : UInt64) : M UInt64 := do
  let complen : UInt64 := DEFLATE_BOUND_COMPLEN sourceLen
  if complen > 0 then
    let bound := complen + ZLIB_WRAPLEN
    return if bound < sourceLen then (-1 : Int64).toUInt64 else bound
  let bound := sourceLen
    + (if sourceLen == 0 then 1 else 0)
    + (if sourceLen < 9 then 1 else 0)
    + DEFLATE_QUICK_OVERHEAD sourceLen
    + DEFLATE_BLOCK_OVERHEAD
    + ZLIB_WRAPLEN
  return if bound < sourceLen then (-1 : Int64).toUInt64 else bound

/-- `unsigned long Z_EXPORT compressBound(unsigned long sourceLen)` (`compress.c:118-121`). -/
def compressBound (sourceLen : UInt64) : M UInt64 := do
  let bound ← compressBound_z sourceLen
  return MIN ULONG_MAX bound

end ZlibNg.Compress
