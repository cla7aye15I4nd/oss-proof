import ZlibNgF.ZlibNg.«zbuild.h»

/-!
# `zutil.h` — size macros of the compressed-size bounds (`ZlibNgF`)

Source: `zlib-ng/zutil.h:73-84` (`NO_QUICK_STRATEGY` undefined). Used by `compressBound_z` (`compress.c`) and
`deflateBound_z` (`deflate.c`). The definitions keep the namespace `ZlibNg.Compress` they were first given.
-/

set_option autoImplicit false

namespace ZlibNg.Compress

/-- `#define ZLIB_WRAPLEN 6` (`zutil.h:73`). -/
def ZLIB_WRAPLEN : UInt64 := 6

/-- `#define DEFLATE_BLOCK_OVERHEAD ((3 + 15 + 6) >> 3)` (`zutil.h:76-79`). -/
def DEFLATE_BLOCK_OVERHEAD : UInt64 := ((3 : UInt64) + 15 + 6) >>> 3

/-- `#define DEFLATE_QUICK_OVERHEAD(x) ((x * (9 - 8) + 7) >> 3)` (`zutil.h:82-83`). -/
def DEFLATE_QUICK_OVERHEAD (x : UInt64) : UInt64 := (x * 1 + 7) >>> 3

end ZlibNg.Compress
