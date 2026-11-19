import ZlibNgF.ZlibNg.«adler32_p.h»

/-!
# `arch/generic/adler32_c.c` — faithful translation (`ZlibNgF`)

Source: `zlib-ng/arch/generic/adler32_c.c` + Patch 0007 (`0007-adler32-null-before-len-1.patch`),
`UNROLL_MORE` undefined.
-/

set_option autoImplicit false

namespace ZlibNg.Adler32C
open C ZlibNg.Adler32P

/-- `Z_INTERNAL uint32_t adler32_c(uint32_t adler, const uint8_t *buf, size_t len)` (`adler32_c.c:11-54`, with Patch 0007:
the `buf == NULL` test precedes the `len == 1` fast path). -/
def adler32_c (adler : UInt32) (buf : BPtr) (len : UInt64) : M UInt32 := do
  let sum2 : UInt32 := (adler >>> 16) &&& 0xffff
  let adler : UInt32 := adler &&& 0xffff
  if buf == .null then
    return 1
  else if len == 1 then
    adler32_len_1 adler buf sum2
  else if len < 16 then
    adler32_len_16 adler buf len sum2
  else do
    let s ← cwhile
      (fun (s : State32) => pure (s.len >= NMAX, s))
      (fun (s : State32) => do
        let s := { s with len := s.len - NMAX, n := (NMAX / 8).toUInt32 }
        let s ← cdoWhile
          (fun (s : State32) => do
            let (adler, sum2) ← adler_do8 s.adler s.sum2 s.buf
            let buf ← s.buf.add 8
            pure { s with adler, sum2, buf })
          (fun (s : State32) =>
            let n := s.n - 1
            pure (n != 0, { s with n }))
          s
        pure { s with adler := s.adler % BASE, sum2 := s.sum2 % BASE })
      { adler, sum2, buf, len, n := 0 }
    adler32_len_64 s.adler s.buf s.len s.sum2

end ZlibNg.Adler32C
