import ZlibNgF.Runtime.Libc
import ZlibNgF.ZlibNg.«crc32_braid_tbl.h»

/-!
# `crc32_p.h` — private CRC-32 helpers (`ZlibNgF`)

Source: `zlib-ng/crc32_p.h`. The compile-time `int` parameters `MAX_LEN` and `COPY` of `crc32_copy_small` are
ordinary arguments.
-/

set_option autoImplicit false

namespace ZlibNg.Crc32P
open C ZlibNg.Crc32Tbl

/-- Read `crc_table[i]` from the static read-only `crc_table`. -/
def crcTab (i : UInt64) : M UInt32 :=
  Ptr.index (Ptr.ref URef.st_crc_table 0) (Int.ofNat i.toNat)

/-- `#define CRC_DO1(c, buf, i) c = crc_table[(c ^ buf[i]) & 0xff] ^ (c >> 8)` (`crc32_p.h:13`). -/
def CRC_DO1 (c : UInt32) (buf : BPtr) (i : Int) : M UInt32 := do
  let b ← index8 buf i
  let t ← crcTab (((c ^^^ b.toUInt32) &&& 0xff).toUInt64)
  return t ^^^ (c >>> 8)

/-- `#define CRC_DO2(c, buf, i) {CRC_DO1(c, buf, i); CRC_DO1(c, buf, i+1);}` (`crc32_p.h:14`). -/
def CRC_DO2 (c : UInt32) (buf : BPtr) (i : Int) : M UInt32 := do
  let c ← CRC_DO1 c buf i
  CRC_DO1 c buf (i + 1)

/-- `#define CRC_DO4(c, buf, i) {CRC_DO2(c, buf, i); CRC_DO2(c, buf, i+2);}` (`crc32_p.h:15`). -/
def CRC_DO4 (c : UInt32) (buf : BPtr) (i : Int) : M UInt32 := do
  let c ← CRC_DO2 c buf i
  CRC_DO2 c buf (i + 2)

/-- `#define CRC_DO8(c, buf, i) {CRC_DO4(c, buf, i); CRC_DO4(c, buf, i+4);}` (`crc32_p.h:16`). -/
def CRC_DO8 (c : UInt32) (buf : BPtr) (i : Int) : M UInt32 := do
  let c ← CRC_DO4 c buf i
  CRC_DO4 c buf (i + 4)

/-- Loop state of `crc32_copy_small`'s `while (len >= 8)` loop. -/
structure SmallState where
  crc : UInt32
  dst : BPtr
  buf : BPtr
  len : UInt64

/-- `Z_FORCEINLINE static uint32_t crc32_copy_small(uint32_t crc, uint8_t *dst, const uint8_t *buf, size_t len,
const int MAX_LEN, const int COPY)` (`crc32_p.h:18-55`). -/
def crc32_copy_small (crc : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64) (MAX_LEN : Int32) (COPY : Int32) :
    M UInt32 := do
  let mut s : SmallState := { crc, dst, buf, len }
  if MAX_LEN >= 8 then
    s ← cwhile
      (fun (s : SmallState) => pure (s.len >= 8, s))
      (fun (s : SmallState) => do
        let mut dst := s.dst
        if COPY != 0 then
          Ptr.memcpy dst s.buf 8
          dst ← dst.add 8
        let crc ← CRC_DO8 s.crc s.buf 0
        let buf ← s.buf.add 8
        let len := s.len - 8
        pure { crc, dst, buf, len })
      s
  let mut crc := s.crc
  let mut dst := s.dst
  let mut buf := s.buf
  let len := s.len
  if len &&& 4 != 0 then
    if COPY != 0 then
      Ptr.memcpy dst buf 4
      dst ← dst.add 4
    crc ← CRC_DO4 crc buf 0
    buf ← buf.add 4
  if len &&& 2 != 0 then
    if COPY != 0 then
      Ptr.memcpy dst buf 2
      dst ← dst.add 2
    crc ← CRC_DO2 crc buf 0
    buf ← buf.add 2
  if len &&& 1 != 0 then
    if COPY != 0 then
      Ptr.store dst (← load8 buf)
    crc ← CRC_DO1 crc buf 0
  return crc

end ZlibNg.Crc32P
