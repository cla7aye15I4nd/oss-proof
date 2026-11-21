import ZlibNgF.ZlibNg.«crc32_braid_comb_p.h»

/-!
# `crc32_braid_comb.c` — CRC-32 combination functions (`ZlibNgF`)

Source: `zlib-ng/crc32_braid_comb.c`, `ZLIB_COMPAT` LP64 Linux build.
-/

set_option autoImplicit false

namespace ZlibNg.Crc32Comb
open C ZlibNg.Crc32CombP

/-- `static uint32_t crc32_combine_(uint32_t crc1, uint32_t crc2, z_off64_t len2)` (`crc32_braid_comb.c:15-19`). -/
def crc32_combine_ (crc1 crc2 : UInt32) (len2 : Int64) : M UInt32 := do
  if len2 < 0 then
    return 0
  let m ← multmodp (← x2nmodp len2 3) crc1
  return m ^^^ crc2

/-- `static uint32_t crc32_combine_gen_(z_off64_t len2)` (`crc32_braid_comb.c:20-24`). -/
def crc32_combine_gen_ (len2 : Int64) : M UInt32 := do
  if len2 < 0 then
    return 0
  x2nmodp len2 3

/-- `static uint32_t crc32_combine_op_(uint32_t crc1, uint32_t crc2, const uint32_t op)` (`crc32_braid_comb.c:25-27`). -/
def crc32_combine_op_ (crc1 crc2 op : UInt32) : M UInt32 := do
  let m ← multmodp op crc1
  return m ^^^ crc2

/-- `unsigned long Z_EXPORT crc32_combine(unsigned long crc1, unsigned long crc2, z_off_t len2)` (`crc32_braid_comb.c:32-34`). -/
def crc32_combine (crc1 crc2 : UInt64) (len2 : Int64) : M UInt64 := do
  let r ← crc32_combine_ crc1.toUInt32 crc2.toUInt32 len2
  return r.toUInt64

/-- `unsigned long Z_EXPORT crc32_combine64(unsigned long crc1, unsigned long crc2, z_off64_t len2)` (`crc32_braid_comb.c:35-37`). -/
def crc32_combine64 (crc1 crc2 : UInt64) (len2 : Int64) : M UInt64 := do
  let r ← crc32_combine_ crc1.toUInt32 crc2.toUInt32 len2
  return r.toUInt64

/-- `unsigned long Z_EXPORT crc32_combine_gen(z_off_t len2)` (`crc32_braid_comb.c:38-40`). -/
def crc32_combine_gen (len2 : Int64) : M UInt64 := do
  let r ← crc32_combine_gen_ len2
  return r.toUInt64

/-- `unsigned long Z_EXPORT crc32_combine_gen64(z_off64_t len2)` (`crc32_braid_comb.c:41-43`). -/
def crc32_combine_gen64 (len2 : Int64) : M UInt64 := do
  let r ← crc32_combine_gen_ len2
  return r.toUInt64

/-- `unsigned long Z_EXPORT crc32_combine_op(unsigned long crc1, unsigned long crc2, const unsigned long op)` (`crc32_braid_comb.c:44-46`). -/
def crc32_combine_op (crc1 crc2 op : UInt64) : M UInt64 := do
  let r ← crc32_combine_op_ crc1.toUInt32 crc2.toUInt32 op.toUInt32
  return r.toUInt64

end ZlibNg.Crc32Comb
