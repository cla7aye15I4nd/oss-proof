import ZlibNgF.ZlibNg.«zbuild.h»

/-!
# `adler32_p.h` — private inline Adler-32 helpers (`ZlibNgF`)

Source: `zlib-ng/adler32_p.h`, x86_64 Linux LP64 (`BYTE_ORDER == LITTLE_ENDIAN`).

`zlib-ng` accumulates `adler` and `sum2` in 32-bit `uint32_t`, relying on `NMAX = 5552` satisfying
`255 * NMAX * (NMAX + 1) / 2 + (NMAX + 1) * (BASE - 1) <= 2^32 - 1`.

The `uint32_t *adler` / `uint32_t *sum2` out-parameters of `adler32_copy_align` and `adler32_swar` are passed by
value and returned (normalisation 1 of the root `AGENTS.md`). The compile-time `int` parameters `MAX_LEN`, `COPY`,
`REBASE` are ordinary arguments; `MAX_LEN` is only `Z_UNUSED`.

`adler32_swar` reads the buffer as `const uint64_t *`. The conversion `(const uint64_t *)buf` raises `Fault.ub`
unless `buf` is 8-byte aligned (ISO C17 §6.3.2.3p7); each 64-bit load is eight little-endian byte loads. The model
does not check the effective-type rule (ISO C17 §6.5p7) for these word reads.
-/

set_option autoImplicit false

namespace ZlibNg.Adler32P
open C ZlibNg.Zbuild

/-- `#define BASE 65521U` -/
def BASE : UInt32 := 65521
/-- `#define NMAX 5552` -/
def NMAX : UInt64 := 5552
/-- `#define NMAX_ALIGNED8 (NMAX & ~7)` -/
def NMAX_ALIGNED8 : UInt64 := NMAX &&& ~~~7
/-- `#define ADLER32_SWAR_MAX_BYTES (23 * 8)` -/
def ADLER32_SWAR_MAX_BYTES : UInt64 := 23 * 8
/-- `#define ADLER32_SWAR_EVEN_MASK 0x00FF00FF00FF00FFULL` -/
def ADLER32_SWAR_EVEN_MASK : UInt64 := 0x00FF00FF00FF00FF
/-- `#define ADLER32_SWAR_HSUM 0x1000100010001ULL` -/
def ADLER32_SWAR_HSUM : UInt64 := 0x1000100010001

/-- `p[i]` for `const uint64_t *p` on little-endian LP64: eight byte loads at `p + 8 i`. -/
def loadU64 (p : BPtr) (i : Nat) : M UInt64 := do
  let base : Int := Int.ofNat (8 * i)
  let b0 ← index8 p base
  let b1 ← index8 p (base + 1)
  let b2 ← index8 p (base + 2)
  let b3 ← index8 p (base + 3)
  let b4 ← index8 p (base + 4)
  let b5 ← index8 p (base + 5)
  let b6 ← index8 p (base + 6)
  let b7 ← index8 p (base + 7)
  return b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- `memcpy(dst, &v, sizeof(v))` for a `uint64_t v` on little-endian LP64: eight byte stores. -/
def storeU64 (dst : BPtr) (v : UInt64) : M Unit := do
  Ptr.store (← dst.add 0) v.toUInt8
  Ptr.store (← dst.add 1) (v >>> 8).toUInt8
  Ptr.store (← dst.add 2) (v >>> 16).toUInt8
  Ptr.store (← dst.add 3) (v >>> 24).toUInt8
  Ptr.store (← dst.add 4) (v >>> 32).toUInt8
  Ptr.store (← dst.add 5) (v >>> 40).toUInt8
  Ptr.store (← dst.add 6) (v >>> 48).toUInt8
  Ptr.store (← dst.add 7) (v >>> 56).toUInt8

/-- `#define ADLER_DO1(sum1, sum2, buf, i) {(sum1) += buf[(i)]; (sum2) += (sum1);}` -/
def adler_do1 (adler sum2 : UInt32) (buf : BPtr) (i : Int) : M (UInt32 × UInt32) := do
  let b ← index8 buf i
  let adler := adler + b.toUInt32
  let sum2 := sum2 + adler
  pure (adler, sum2)

/-- `#define ADLER_DO2(sum1, sum2, buf, i) {ADLER_DO1(sum1, sum2, buf, i); ADLER_DO1(sum1, sum2, buf, i+1);}` -/
def adler_do2 (adler sum2 : UInt32) (buf : BPtr) (i : Int) : M (UInt32 × UInt32) := do
  let (adler, sum2) ← adler_do1 adler sum2 buf i
  adler_do1 adler sum2 buf (i + 1)

/-- `#define ADLER_DO4(sum1, sum2, buf, i) {ADLER_DO2(sum1, sum2, buf, i); ADLER_DO2(sum1, sum2, buf, i+2);}` -/
def adler_do4 (adler sum2 : UInt32) (buf : BPtr) (i : Int) : M (UInt32 × UInt32) := do
  let (adler, sum2) ← adler_do2 adler sum2 buf i
  adler_do2 adler sum2 buf (i + 2)

/-- Loop state of the `while (len >= 4)` loops. -/
structure Do4State where
  adler : UInt32
  sum2 : UInt32
  dst : BPtr
  buf : BPtr
  len : UInt64

/-- `Z_FORCEINLINE static void adler32_copy_align(uint32_t *Z_RESTRICT adler, uint8_t *dst, const uint8_t *buf,
size_t len, uint32_t *Z_RESTRICT sum2, const int MAX_LEN, const int COPY)` (`adler32_p.h:27-55`).
Returns the final `(*adler, *sum2)`. -/
def adler32_copy_align (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64) (sum2 : UInt32)
    (_MAX_LEN : Int32) (COPY : Int32) : M (UInt32 × UInt32) := do
  let mut adler := adler
  let mut sum2 := sum2
  let mut dst := dst
  let mut buf := buf
  if len &&& 1 != 0 then
    if COPY != 0 then
      Ptr.store dst (← load8 buf)
      dst ← dst.add 1
    let (a, s) ← adler_do1 adler sum2 buf 0
    adler := a
    sum2 := s
    buf ← buf.add 1
  if len &&& 2 != 0 then
    if COPY != 0 then
      Ptr.memcpy dst buf 2
      dst ← dst.add 2
    let (a, s) ← adler_do2 adler sum2 buf 0
    adler := a
    sum2 := s
    buf ← buf.add 2
  let s ← cwhile
    (fun (s : Do4State) => pure (s.len >= 4, s))
    (fun (s : Do4State) => do
      let mut dst := s.dst
      if COPY != 0 then
        Ptr.memcpy dst s.buf 4
        dst ← dst.add 4
      let len := s.len - 4
      let (adler, sum2) ← adler_do4 s.adler s.sum2 s.buf 0
      let buf ← s.buf.add 4
      pure { adler, sum2, dst, buf, len })
    { adler, sum2, dst, buf, len }
  return (s.adler, s.sum2)

/-- Loop state of `adler32_swar`'s `while (len >= 16)` loop. -/
structure SwarState where
  sum_even : UInt64
  sum_odd : UInt64
  prefix_even : UInt64
  prefix_odd : UInt64
  dst : BPtr
  src64 : BPtr
  len : UInt64

/-- `Z_FORCEINLINE static void adler32_swar(uint32_t *adler, uint8_t *dst, const uint8_t *buf, size_t len,
uint32_t *sum2, const int COPY)` (`adler32_p.h:67-136`, `BYTE_ORDER == LITTLE_ENDIAN`).
Returns the final `(*adler, *sum2)`. -/
def adler32_swar (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64) (sum2 : UInt32)
    (COPY : Int32) : M (UInt32 × UInt32) := do
  let sum_even : UInt64 := 0
  let sum_odd : UInt64 := 0
  let prefix_even : UInt64 := 0
  let prefix_odd : UInt64 := 0
  let mut sum2 := sum2 + adler * len.toUInt32
  let src64 ← Ptr.castAligned buf 8
  let s ← cwhile
    (fun (s : SwarState) => pure (s.len >= 16, s))
    (fun (s : SwarState) => do
      let v0 ← loadU64 s.src64 0
      let v1 ← loadU64 s.src64 1
      let mut dst := s.dst
      if COPY != 0 then
        storeU64 dst v0
        storeU64 (← dst.add 8) v1
        dst ← dst.add 16
      let prefix_even := s.prefix_even + s.sum_even
      let prefix_odd := s.prefix_odd + s.sum_odd
      let sum_even := s.sum_even + (v0 &&& ADLER32_SWAR_EVEN_MASK)
      let sum_odd := s.sum_odd + ((v0 >>> 8) &&& ADLER32_SWAR_EVEN_MASK)
      let prefix_even := prefix_even + sum_even
      let prefix_odd := prefix_odd + sum_odd
      let sum_even := sum_even + (v1 &&& ADLER32_SWAR_EVEN_MASK)
      let sum_odd := sum_odd + ((v1 >>> 8) &&& ADLER32_SWAR_EVEN_MASK)
      let src64 ← s.src64.add 16
      let len := s.len - 16
      pure { sum_even, sum_odd, prefix_even, prefix_odd, dst, src64, len })
    { sum_even, sum_odd, prefix_even, prefix_odd, dst, src64, len }
  let mut sum_even := s.sum_even
  let mut sum_odd := s.sum_odd
  let mut prefix_even := s.prefix_even
  let mut prefix_odd := s.prefix_odd
  if s.len >= 8 then
    let v ← loadU64 s.src64 0
    if COPY != 0 then
      storeU64 s.dst v
    prefix_even := prefix_even + sum_even
    prefix_odd := prefix_odd + sum_odd
    sum_even := sum_even + (v &&& ADLER32_SWAR_EVEN_MASK)
    sum_odd := sum_odd + ((v >>> 8) &&& ADLER32_SWAR_EVEN_MASK)
  let adler := adler + (((sum_even + sum_odd) * ADLER32_SWAR_HSUM) >>> 48).toUInt32
  let pe_lo : UInt64 := prefix_even &&& 0xFFFF0000FFFF
  let pe_hi : UInt64 := (prefix_even >>> 16) &&& 0xFFFF0000FFFF
  let po_lo : UInt64 := prefix_odd &&& 0xFFFF0000FFFF
  let po_hi : UInt64 := (prefix_odd >>> 16) &&& 0xFFFF0000FFFF
  sum2 := sum2 + (((pe_lo + po_lo + pe_hi + po_hi) * 0x800000008) >>> 32).toUInt32
  sum2 := sum2 + ((2 : UInt32) * ((sum_even * 0x4000300020001) >>> 48).toUInt32
         + ((sum_odd * ADLER32_SWAR_HSUM) >>> 48).toUInt32
         + (2 : UInt32) * ((sum_odd * 0x3000200010000) >>> 48).toUInt32)
  return (adler, sum2)

/-- Loop state of `adler32_copy_tail`'s SWAR loop. -/
structure TailState where
  adler : UInt32
  sum2 : UInt32
  dst : BPtr
  buf : BPtr
  len : UInt64

/-- `Z_FORCEINLINE static uint32_t adler32_copy_tail(uint32_t adler, uint8_t *dst, const uint8_t *buf, size_t len,
uint32_t sum2, const int REBASE, const int MAX_LEN, const int COPY)` (`adler32_p.h:138-178`). -/
def adler32_copy_tail (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64) (sum2 : UInt32)
    (REBASE : Int32) (_MAX_LEN : Int32) (COPY : Int32) : M UInt32 := do
  let mut adler := adler
  let mut sum2 := sum2
  if len != 0 then
    let s ← cwhile
      (fun (s : TailState) => do
        if s.len >= 8 then
          let addr ← addrOf s.buf
          pure ((addr &&& 7) == 0, s)
        else
          pure (false, s))
      (fun (s : TailState) => do
        let chunk := MIN (ALIGN_DOWN s.len 8) ADLER32_SWAR_MAX_BYTES
        let (adler, sum2) ← adler32_swar s.adler s.dst s.buf chunk s.sum2 COPY
        let buf ← s.buf.add (Int.ofNat chunk.toNat)
        let mut dst := s.dst
        if COPY != 0 then
          dst ← dst.add (Int.ofNat chunk.toNat)
        let len := s.len - chunk
        pure { adler, sum2, dst, buf, len })
      { adler, sum2, dst, buf, len }
    let s ← cwhile
      (fun (s : TailState) => pure (s.len >= 4, s))
      (fun (s : TailState) => do
        let mut dst := s.dst
        if COPY != 0 then
          Ptr.memcpy dst s.buf 4
          dst ← dst.add 4
        let len := s.len - 4
        let (adler, sum2) ← adler_do4 s.adler s.sum2 s.buf 0
        let buf ← s.buf.add 4
        pure { adler, sum2, dst, buf, len })
      s
    let mut dst := s.dst
    let mut buf := s.buf
    adler := s.adler
    sum2 := s.sum2
    if s.len &&& 2 != 0 then
      if COPY != 0 then
        Ptr.memcpy dst buf 2
        dst ← dst.add 2
      let (a, b) ← adler_do2 adler sum2 buf 0
      adler := a
      sum2 := b
      buf ← buf.add 2
    if s.len &&& 1 != 0 then
      if COPY != 0 then
        Ptr.store dst (← load8 buf)
      let (a, b) ← adler_do1 adler sum2 buf 0
      adler := a
      sum2 := b
  if REBASE != 0 then
    adler := adler % BASE
    sum2 := sum2 % BASE
  return adler ||| (sum2 <<< 16)

end ZlibNg.Adler32P
