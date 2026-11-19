import ZlibNgF.ZlibNg.arch.generic.«crc32_braid_c.c»
import ZlibNgF.ZlibNg.«crc32_braid_comb.c»

/-!
# `crc32.c` — public CRC-32 entry points (`ZlibNgF`)

Source: `zlib-ng/crc32.c`, LP64 Linux build with `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`.
With `WITH_RUNTIME_CPU_DETECTION=OFF`, `FUNCTABLE_CALL(crc32)` is `native_crc32`, and with `WITH_OPTIM=OFF` and
`WITH_CRC32_CHORBA=OFF` (`WITHOUT_CHORBA`) `native_crc32` is `crc32_braid` (`arch/generic/generic_functions.h`).
With Chorba on (the default) it would be `crc32_chorba`, which is not translated.
-/

set_option autoImplicit false

namespace ZlibNg.Crc32
open C ZlibNg.Crc32Tbl ZlibNg.Crc32P ZlibNg.Crc32Braid

/-- Initialize static CRC tables on `Heap` (`crc_table[256]` and `x2n_table[32]`). -/
def initStatics (h : Heap) : Heap :=
  { h with crcTable := crc_table, x2nTable := x2n_table }

/-- `#define CRC32_INITIAL_VALUE 0` (`zutil.h:71`). -/
def CRC32_INITIAL_VALUE : UInt64 := 0

/-- `const uint32_t * Z_EXPORT get_crc_table(void)` (`crc32.c:16-18`). -/
def get_crc_table : M UPtr :=
  pure (Ptr.ref URef.st_crc_table 0)

/-- `Z_INTERNAL uint32_t crc32_small(uint32_t crc, const uint8_t *buf, size_t len)` (`crc32.c:21-27`). -/
def crc32_small (crc : UInt32) (buf : BPtr) (len : UInt64) : M UInt32 := do
  if len >= 32 then
    return ← crc32_braid crc buf len
  return ~~~(← crc32_copy_small (~~~crc) .null buf len 32 0)

/-- `unsigned long Z_EXPORT crc32_z(unsigned long crc, const unsigned char *buf, size_t len)` (`crc32.c:30-34`). -/
def crc32_z (crc : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
  if buf == .null then
    return CRC32_INITIAL_VALUE
  let r ← crc32_braid crc.toUInt32 buf len
  return r.toUInt64

/-- `unsigned long Z_EXPORT crc32(unsigned long crc, const unsigned char *buf, unsigned int len)` (`crc32.c:44-48`). -/
def crc32 (crc : UInt64) (buf : BPtr) (len : UInt32) : M UInt64 := do
  if buf == .null then
    return CRC32_INITIAL_VALUE
  let r ← crc32_braid crc.toUInt32 buf len.toUInt64
  return r.toUInt64

end ZlibNg.Crc32
