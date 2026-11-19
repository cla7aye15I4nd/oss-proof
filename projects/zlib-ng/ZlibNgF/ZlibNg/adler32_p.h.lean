import ZlibNgF.Runtime.Libc

/-!
# `adler32_p.h` — private inline Adler-32 helpers (`ZlibNgF`)

Source: `zlib-ng/adler32_p.h`, default portable scalar build (`UNROLL_MORE` undefined).
Note that `zlib-ng` accumulates `adler` and `sum2` in 32-bit `uint32_t` (unlike `madler/zlib`'s 64-bit `unsigned long`),
relying on `NMAX = 5552` satisfying `255 * NMAX * (NMAX + 1) / 2 + (NMAX + 1) * (BASE - 1) <= 2^32 - 1`.
-/

set_option autoImplicit false

namespace ZlibNg.Adler32P
open C

def BASE : UInt32 := 65521
def NMAX : UInt64 := 5552

/-- Loop state for `ADLER_DO8` and tail byte accumulation. -/
structure State32 where
  adler : UInt32
  sum2 : UInt32
  buf : BPtr
  len : UInt64
  n : UInt32

/-- `ADLER_DO1(sum1, sum2, buf, i)`: `{ (sum1) += buf[(i)]; (sum2) += (sum1); }` -/
def adler_do1 (adler sum2 : UInt32) (buf : BPtr) (i : Int) : M (UInt32 × UInt32) := do
  let b ← index8 buf i
  let adler := adler + b.toUInt32
  let sum2 := sum2 + adler
  pure (adler, sum2)

/-- `ADLER_DO8(sum1, sum2, buf, 0)`: `ADLER_DO1` at offsets `0 .. 7`. -/
def adler_do8 (adler sum2 : UInt32) (buf : BPtr) : M (UInt32 × UInt32) := do
  let (adler, sum2) ← adler_do1 adler sum2 buf 0
  let (adler, sum2) ← adler_do1 adler sum2 buf 1
  let (adler, sum2) ← adler_do1 adler sum2 buf 2
  let (adler, sum2) ← adler_do1 adler sum2 buf 3
  let (adler, sum2) ← adler_do1 adler sum2 buf 4
  let (adler, sum2) ← adler_do1 adler sum2 buf 5
  let (adler, sum2) ← adler_do1 adler sum2 buf 6
  adler_do1 adler sum2 buf 7

/-- `static inline uint32_t adler32_len_1(uint32_t adler, const uint8_t *buf, uint32_t sum2)` (`adler32_p.h:21-27`). -/
def adler32_len_1 (adler : UInt32) (buf : BPtr) (sum2 : UInt32) : M UInt32 := do
  let b ← index8 buf 0
  let adler := (adler + b.toUInt32) % BASE
  let sum2 := (sum2 + adler) % BASE
  return adler ||| (sum2 <<< 16)

/-- `static inline uint32_t adler32_len_16(uint32_t adler, const uint8_t *buf, size_t len, uint32_t sum2)` (`adler32_p.h:29-39`). -/
def adler32_len_16 (adler : UInt32) (buf : BPtr) (len : UInt64) (sum2 : UInt32) : M UInt32 := do
  let s ← cwhile
    (fun (s : State32) => pure (s.len != 0, s))
    (fun (s : State32) => do
      let len := s.len - 1
      let b ← load8 s.buf
      let buf ← s.buf.add 1
      let adler := s.adler + b.toUInt32
      let sum2 := s.sum2 + adler
      pure { s with adler, sum2, buf, len })
    { adler, sum2, buf, len, n := 0 }
  let adler := s.adler % BASE
  let sum2 := s.sum2 % BASE
  return adler ||| (sum2 <<< 16)

/-- `static inline uint32_t adler32_len_64(uint32_t adler, const uint8_t *buf, size_t len, uint32_t sum2)` (`adler32_p.h:53-68`, `!UNROLL_MORE`). -/
def adler32_len_64 (adler : UInt32) (buf : BPtr) (len : UInt64) (sum2 : UInt32) : M UInt32 := do
  let s ← cwhile
    (fun (s : State32) => pure (s.len >= 8, s))
    (fun (s : State32) => do
      let len := s.len - 8
      let (adler, sum2) ← adler_do8 s.adler s.sum2 s.buf
      let buf ← s.buf.add 8
      pure { s with adler, sum2, buf, len })
    { adler, sum2, buf, len, n := 0 }
  adler32_len_16 s.adler s.buf s.len s.sum2

end ZlibNg.Adler32P
