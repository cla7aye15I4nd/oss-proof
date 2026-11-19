import ZlibNgF.ZlibNg.«adler32_p.h»

/-!
# `arch/generic/adler32_c.c` — faithful translation (`ZlibNgF`)

Source: `zlib-ng/arch/generic/adler32_c.c` (`ADLER32_FALLBACK` defined: the build has no SIMD Adler-32).
-/

set_option autoImplicit false

namespace ZlibNg.Adler32C
open C ZlibNg.Zbuild ZlibNg.Adler32P

/-- Loop state of the `NMAX` block loop of `adler32_c`. -/
structure BlockState where
  adler : UInt32
  sum2 : UInt32
  buf : BPtr
  len : UInt64
  n : UInt64
  nmax : UInt64

/-- `Z_INTERNAL uint32_t adler32_c(uint32_t adler, const uint8_t *buf, size_t len)` (`adler32_c.c:14-59`). -/
def adler32_c (adler : UInt32) (buf : BPtr) (len : UInt64) : M UInt32 := do
  let sum2 : UInt32 := (adler >>> 16) &&& 0xffff
  let adler : UInt32 := adler &&& 0xffff
  if len == 1 then
    return ← adler32_copy_tail adler .null buf 1 sum2 1 1 0
  if len < 16 then
    return ← adler32_copy_tail adler .null buf len sum2 1 15 0
  let align_diff ← ALIGN_DIFF buf 8
  let mut nmax : UInt64 := NMAX_ALIGNED8
  let mut adler := adler
  let mut sum2 := sum2
  let mut buf := buf
  let mut len := len
  if align_diff != 0 then
    let (a, s) ← adler32_copy_align adler .null buf align_diff sum2 7 0
    adler := a
    sum2 := s
    buf ← buf.add (Int.ofNat align_diff.toNat)
    len := len - align_diff
    nmax := ALIGN_DOWN (nmax - align_diff) 8
  let s ← cwhile
    (fun (s : BlockState) => pure (s.len >= s.nmax, s))
    (fun (s : BlockState) => do
      let len := s.len - s.nmax
      let n := s.nmax
      let s ← cdoWhile
        (fun (s : BlockState) => do
          let chunk := MIN (ALIGN_DOWN s.n 8) ADLER32_SWAR_MAX_BYTES
          let (adler, sum2) ← adler32_swar s.adler .null s.buf chunk s.sum2 0
          let buf ← s.buf.add (Int.ofNat chunk.toNat)
          let n := s.n - chunk
          pure { s with adler, sum2, buf, n })
        (fun (s : BlockState) => pure (s.n >= 8, s))
        { s with len, n }
      pure { s with adler := s.adler % BASE, sum2 := s.sum2 % BASE, nmax := NMAX_ALIGNED8 })
    { adler, sum2, buf, len, n := 0, nmax }
  adler32_copy_tail s.adler .null s.buf s.len s.sum2 (if s.len != 0 then 1 else 0) (NMAX - 1).toUInt32.toInt32 0

/-- `Z_INTERNAL uint32_t adler32_copy_c(uint32_t adler, uint8_t *dst, const uint8_t *src, size_t len)`
(`adler32_c.c:61-65`). -/
def adler32_copy_c (adler : UInt32) (dst : BPtr) (src : BPtr) (len : UInt64) : M UInt32 := do
  let adler ← adler32_c adler src len
  Ptr.memcpy dst src len.toNat
  return adler

end ZlibNg.Adler32C
