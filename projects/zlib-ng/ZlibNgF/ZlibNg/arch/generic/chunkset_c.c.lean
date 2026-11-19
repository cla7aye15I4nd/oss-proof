import ZlibNgF.ZlibNg.«inffast_tpl.h»

/-!
# `arch/generic/chunkset_c.c` — generic chunk functions and `inflate_fast` (`ZlibNgF`)

Source: `zlib-ng/arch/generic/chunkset_c.c` (`CHUNKSET_FALLBACK` defined). It defines `chunk_t = uint64_t` and its
primitives (translated with `chunkset_tpl.h` in `chunkset_tpl.h.lean`), includes `chunkset_tpl.h` with
`CHUNKMEMSET_SAFE = chunkmemset_safe_c`, and includes `inffast_tpl.h` twice: `inflate_fast_c`, and
`inflate_fast_safe_c` with `USE_SAFE_MODE`. With the function table resolved at compile time these are
`FUNCTABLE_CALL(chunkmemset_safe)`, `FUNCTABLE_CALL(inflate_fast)` and `FUNCTABLE_CALL(inflate_fast_safe)`.
-/

set_option autoImplicit false

namespace ZlibNg.ChunksetC
open C

/-- `Z_INTERNAL uint8_t* chunkmemset_safe_c(uint8_t *out, uint8_t *from, size_t len, size_t left)` -/
def chunkmemset_safe_c (out from_ : BPtr) (len left : UInt64) : M BPtr :=
  ZlibNg.Chunkset.CHUNKMEMSET_SAFE out from_ len left

/-- `void Z_INTERNAL inflate_fast_c(PREFIX3(stream) *strm, uint32_t start)` -/
def inflate_fast_c (strm : StreamPtr) (start : UInt32) : M Unit :=
  ZlibNg.Inffast.INFLATE_FAST false strm start

/-- `void Z_INTERNAL inflate_fast_safe_c(PREFIX3(stream) *strm, uint32_t start)` -/
def inflate_fast_safe_c (strm : StreamPtr) (start : UInt32) : M Unit :=
  ZlibNg.Inffast.INFLATE_FAST true strm start

end ZlibNg.ChunksetC
