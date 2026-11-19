import ZlibNgF.ZlibNg.arch.generic.«adler32_c.c»

/-!
# `adler32.c` — faithful translation (`ZlibNgF`)

Source: `zlib-ng/adler32.c`, LP64 Linux build with `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`.
With `WITH_RUNTIME_CPU_DETECTION=OFF` and `WITH_OPTIM=OFF`, `FUNCTABLE_CALL(adler32)` is `native_adler32`, which is
`adler32_c` (`arch/generic/generic_functions.h`).
-/

set_option autoImplicit false

namespace ZlibNg.Adler32
open C ZlibNg.Adler32P ZlibNg.Adler32C

/-- `unsigned long Z_EXPORT adler32_z(unsigned long adler, const unsigned char *buf, size_t len)` (`adler32.c:11-13`). -/
def adler32_z (adler : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
  let r ← adler32_c adler.toUInt32 buf len
  return r.toUInt64

/-- `unsigned long Z_EXPORT adler32(unsigned long adler, const unsigned char *buf, unsigned int len)` (`adler32.c:22-24`). -/
def adler32 (adler : UInt64) (buf : BPtr) (len : UInt32) : M UInt64 := do
  let r ← adler32_c adler.toUInt32 buf len.toUInt64
  return r.toUInt64

/-- `static uint32_t adler32_combine_(uint32_t adler1, uint32_t adler2, z_off64_t len2)` (`adler32.c:32-54`). -/
def adler32_combine_ (adler1 adler2 : UInt32) (len2 : Int64) : M UInt32 := do
  if len2 < 0 then
    return 0xffffffff
  let len2 := len2 % 65521
  let rem : UInt32 := len2.toUInt64.toUInt32
  let sum1 : UInt32 := adler1 &&& 0xffff
  let sum2 : UInt32 := (rem * sum1) % BASE
  let mut sum1 : UInt32 := sum1 + (adler2 &&& 0xffff) + BASE - 1
  let mut sum2 : UInt32 := sum2 + (((adler1 >>> 16) &&& (0xffff : UInt32)) + ((adler2 >>> 16) &&& (0xffff : UInt32)) + BASE - rem)
  if sum1 >= BASE then sum1 := sum1 - BASE
  if sum1 >= BASE then sum1 := sum1 - BASE
  if sum2.toUInt64 >= (BASE.toUInt64 <<< 1) then sum2 := (sum2.toUInt64 - (BASE.toUInt64 <<< 1)).toUInt32
  if sum2 >= BASE then sum2 := sum2 - BASE
  return sum1 ||| (sum2 <<< 16)

/-- `unsigned long Z_EXPORT adler32_combine(unsigned long adler1, unsigned long adler2, z_off_t len2)` (`adler32.c:58-60`). -/
def adler32_combine (adler1 adler2 : UInt64) (len2 : Int64) : M UInt64 := do
  let r ← adler32_combine_ adler1.toUInt32 adler2.toUInt32 len2
  return r.toUInt64

/-- `unsigned long Z_EXPORT adler32_combine64(unsigned long adler1, unsigned long adler2, z_off64_t len2)` (`adler32.c:62-64`). -/
def adler32_combine64 (adler1 adler2 : UInt64) (len2 : Int64) : M UInt64 := do
  let r ← adler32_combine_ adler1.toUInt32 adler2.toUInt32 len2
  return r.toUInt64

end ZlibNg.Adler32
