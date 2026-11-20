import ZlibNgF.Runtime.CExpr
import ZlibNgF.Runtime.Inflate
import ZlibNgF.ZlibNg.«zbuild.h»

/-!
# `inflate_p.h` — helpers shared by `inflate()` and `inflate_fast()` (`ZlibNgF`)

Source: `zlib-ng/inflate_p.h`, x86_64 LP64, no DFLTCC. The register macros (`LOAD`, `RESTORE`, `PULLBYTE`,
`NEEDBITS`, ...), `CRC2`/`CRC4` and `SET_BAD` act on the locals of `inflate()` and are in `inflate.c.lean`;
`REFILL` and the copies of `inflate_fast()` are in `inffast_tpl.h.lean`.
-/

set_option autoImplicit false

namespace ZlibNg.InflateP
open C ZlibNg.Zbuild

/-- `#define INFLATE_FAST_MIN_HAVE 15` -/
def INFLATE_FAST_MIN_HAVE : UInt32 := 15
/-- `#define INFLATE_FAST_MIN_LEFT 260` -/
def INFLATE_FAST_MIN_LEFT : UInt32 := 260
/-- `#define INFLATE_FAST_MIN_SAFE 3` -/
def INFLATE_FAST_MIN_SAFE : UInt32 := 3
/-- `#define MAX_BITS 15` (`zutil.h`) -/
def MAX_BITS : UInt32 := 15

/-- `CODE_BITS(here)`: `(unsigned)((here.op & 16) ? (here.op & 15) : here.bits)` -/
def CODE_BITS (here : Code) : UInt32 :=
  if here.op &&& 16 != 0 then (here.op &&& 15).toUInt32 else here.bits.toUInt32

/-- `CODE_EXTRA(here)`: `(unsigned)((here.op & 16) ? (here.bits - (here.op & 15)) : 0)` (the subtraction is
in `int`). -/
def CODE_EXTRA (here : Code) : UInt32 :=
  if here.op &&& 16 != 0 then
    (Int32.ofInt ((here.bits.toNat : Int) - ((here.op &&& 15).toNat : Int))).toUInt32
  else 0

/-- `EXTRA_BITS(old, here, op)`: `((old & (((uint64_t)1 << here.bits) - 1)) >> (op & MAX_BITS))` -/
def EXTRA_BITS (old : UInt64) (here : Code) (op : UInt32) : M UInt64 := do
  let m ← shl64 1 here.bits.toUInt32
  shr64 (old &&& (m - 1)) (op &&& MAX_BITS)

/-- `COMBINE_OP(extra, code_bits)`: `((unsigned char)((extra) & 16 ? (code_bits) | 16 : (extra)))` -/
def COMBINE_OP (extra : UInt32) (code_bits : UInt8) : UInt8 :=
  if extra &&& 16 != 0 then code_bits ||| 16 else extra.toUInt8

/-- `COMBINE_BITS(code_bits, extra)`: `((unsigned char)((code_bits) + ((extra) & 15)))` -/
def COMBINE_BITS (code_bits : UInt8) (extra : UInt32) : UInt8 :=
  (code_bits.toUInt32 + (extra &&& 15)).toUInt8

/-- `static inline uint64_t load_64_bits(const unsigned char *in, unsigned bits)` (`inflate_p.h:209-212`). -/
def load_64_bits (in_ : BPtr) (bits : UInt32) : M UInt64 := do
  let chunk ← memread8 in_
  shl64 chunk bits

/-- `static uint8_t* chunkcopy_safe(uint8_t *out, uint8_t *from, size_t len, uint8_t *safe)`
(`inflate_p.h:221-283`). The pointer comparisons need `out` and `from` in one object (ISO C17 §6.5.8p5). -/
def chunkcopy_safe (out from_ : BPtr) (len : UInt64) (safe : BPtr) : M BPtr := do
  let safelen := (← Ptr.diff safe out).toUInt64
  let len := MIN len safelen
  let olap_src ← (do
    if ← Ptr.le out from_ then Ptr.lt from_ (← out.add (Int.ofNat len.toNat)) else pure false)
  let olap_dst ← (do
    if ← Ptr.le from_ out then Ptr.lt out (← from_.add (Int.ofNat len.toNat)) else pure false)
  if !(olap_src || olap_dst) then
    Ptr.memcpy out from_ len.toNat
    return ← out.add (Int.ofNat len.toNat)
  if out == from_ then
    return ← out.add (Int.ofNat len.toNat)
  let d ← Ptr.diff from_ out
  let non_olap_size : UInt64 := (if d < 0 then -d else d).toUInt64
  let (out, _, _) ← cwhile
    (fun ((out, from_, len) : BPtr × BPtr × UInt64) => pure (len != 0, (out, from_, len)))
    (fun ((out, from_, len) : BPtr × BPtr × UInt64) => do
      let tocopy := MIN non_olap_size len
      let len := len - tocopy
      let (out, from_, tocopy) ← cwhile
        (fun ((out, from_, t) : BPtr × BPtr × UInt64) => pure (t >= 16, (out, from_, t)))
        (fun ((out, from_, t) : BPtr × BPtr × UInt64) => do
          Ptr.memcpy out from_ 16
          pure (← out.add 16, ← from_.add 16, t - 16))
        (out, from_, tocopy)
      let (out, from_, tocopy) ← if tocopy >= 8 then do
          Ptr.memcpy out from_ 8
          pure (← out.add 8, ← from_.add 8, tocopy - 8)
        else pure (out, from_, tocopy)
      let (out, from_, tocopy) ← if tocopy >= 4 then do
          Ptr.memcpy out from_ 4
          pure (← out.add 4, ← from_.add 4, tocopy - 4)
        else pure (out, from_, tocopy)
      let (out, from_, _) ← cwhile
        (fun ((out, from_, t) : BPtr × BPtr × UInt64) => pure (t != 0, (out, from_, t - 1)))
        (fun ((out, from_, t) : BPtr × BPtr × UInt64) => do
          Ptr.store out (← load8 from_)
          pure (← out.add 1, ← from_.add 1, t))
        (out, from_, tocopy)
      pure (out, from_, len))
    (out, from_, len)
  return out

end ZlibNg.InflateP
