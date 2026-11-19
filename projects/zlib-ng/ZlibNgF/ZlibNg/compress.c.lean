import ZlibNgF.Runtime.Libc

/-!
# `compress.c` — compressed size bound (`ZlibNgF`)

Source: `zlib-ng/compress.c:81-98` and `zlib-ng/zutil.h:68-79`,
`ZLIB_COMPAT` LP64 Linux scalar build (`S390_DFLTCC_DEFLATE` and `NO_QUICK_STRATEGY` undefined).
Note: one-shot `compress` and `compress2` depend on `deflateInit` / `deflate` / `deflateEnd` and are not
translated yet.
-/

set_option autoImplicit false

namespace ZlibNg.Compress
open C

/-- `#define ZLIB_WRAPLEN 6` (`zutil.h:68`). -/
def ZLIB_WRAPLEN : UInt64 := 6

/-- `#define DEFLATE_BLOCK_OVERHEAD ((3 + 15 + 6) >> 3)` (`zutil.h:71-74`). -/
def DEFLATE_BLOCK_OVERHEAD : UInt64 := ((3 : UInt64) + 15 + 6) >>> 3

/-- `#define DEFLATE_QUICK_OVERHEAD(x) ((x * (9 - 8) + 7) >> 3)` (`zutil.h:77-78`). -/
def DEFLATE_QUICK_OVERHEAD (x : UInt64) : UInt64 := (x * 1 + 7) >>> 3

/-- `#define DEFLATE_BOUND_COMPLEN(source_len) 0` (`compress.c:17`). -/
def DEFLATE_BOUND_COMPLEN (_source_len : UInt64) : UInt64 := 0

/-- `unsigned long Z_EXPORT compressBound(unsigned long sourceLen)` (`compress.c:81-98`). -/
def compressBound (sourceLen : UInt64) : M UInt64 := do
  let complen : UInt64 := DEFLATE_BOUND_COMPLEN sourceLen
  if complen > 0 then
    return complen + ZLIB_WRAPLEN
  return sourceLen
    + (if sourceLen == 0 then 1 else 0)
    + (if sourceLen < 9 then 1 else 0)
    + DEFLATE_QUICK_OVERHEAD sourceLen
    + DEFLATE_BLOCK_OVERHEAD
    + ZLIB_WRAPLEN

end ZlibNg.Compress
