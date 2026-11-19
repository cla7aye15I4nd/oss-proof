import ZlibNgF.Runtime.CExpr
import ZlibNgF.ZlibNg.«zbuild.h»

/-!
# `chunkset_tpl.h` — chunk copies (`ZlibNgF`)

Source: `zlib-ng/chunkset_tpl.h` as instantiated by `zlib-ng/arch/generic/chunkset_c.c` (`chunk_t = uint64_t`;
`HAVE_CHUNKMEMSET_4`, `HAVE_CHUNKMEMSET_8`; no `HAVE_CHUNKCOPY`, `HAVE_CHUNK_MAG`, `HAVE_HALF_CHUNK`,
`HAVE_MASKED_READWRITE`, `HAVE_CHUNKMEMSET_1/2/16`; `OPTIMAL_CMP == 64` on x86_64), together with the chunk
primitives of `chunkset_c.c` (`chunkmemset_4`, `chunkmemset_8`, `loadchunk`, `storechunk`).

A `chunk_t` is a `uint64_t` value. `memcpy` from or to the bytes of the local `chunk_load` (`GET_CHUNK_MAG`, the
`rem_bytes` tail of `CHUNKMEMSET`) is a byte-wise read or write of that value (little-endian). The `size_t *`
out-parameters of `CHUNKUNROLL` and `GET_CHUNK_MAG` are passed by value and returned (normalisation 1).
-/

set_option autoImplicit false

namespace ZlibNg.Chunkset
open C ZlibNg.Zbuild

/-- `sizeof(chunk_t)` -/
def CHUNK : UInt64 := 8

/-- `static inline void chunkmemset_4(uint8_t *from, chunk_t *chunk)` (`chunkset_c.c:17-20`). -/
def chunkmemset_4 (from_ : BPtr) : M UInt64 := do
  let tmp ← memread4 from_
  return tmp.toUInt64 ||| (tmp.toUInt64 <<< 32)

/-- `static inline void chunkmemset_8(uint8_t *from, chunk_t *chunk)` (`chunkset_c.c:22-24`). -/
def chunkmemset_8 (from_ : BPtr) : M UInt64 := memread8 from_

/-- `static inline void loadchunk(uint8_t const *s, chunk_t *chunk)` (`chunkset_c.c:26-28`). -/
def loadchunk (s : BPtr) : M UInt64 := memread8 s

/-- `static inline void storechunk(uint8_t *out, chunk_t *chunk)` (`chunkset_c.c:30-32`). -/
def storechunk (out : BPtr) (chunk : UInt64) : M Unit := memwrite8 out chunk

/-- `static inline size_t CHUNKSIZE(void)` (`chunkset_tpl.h:9-11`). -/
def CHUNKSIZE : UInt64 := CHUNK

/-- `static inline uint8_t* CHUNKCOPY(uint8_t *out, uint8_t const *from, size_t len)` (`chunkset_tpl.h:24-41`). -/
def CHUNKCOPY (out from_ : BPtr) (len : UInt64) : M BPtr := do
  let align := ((len - 1) % CHUNK) + 1
  let chunk ← loadchunk from_
  storechunk out chunk
  let out ← out.add (Int.ofNat align.toNat)
  let from_ ← from_.add (Int.ofNat align.toNat)
  let len := len - align
  let (out, _, _) ← cwhile
    (fun ((out, from_, len) : BPtr × BPtr × UInt64) => pure (len > 0, (out, from_, len)))
    (fun ((out, from_, len) : BPtr × BPtr × UInt64) => do
      let chunk ← loadchunk from_
      storechunk out chunk
      let out ← out.add 8
      let from_ ← from_.add 8
      pure (out, from_, len - CHUNK))
    (out, from_, len)
  return out

/-- `static inline uint8_t* CHUNKUNROLL(uint8_t *out, unsigned *dist, unsigned *len)` (`chunkset_tpl.h:52-63`).
Returns `(out, *dist, *len)`. -/
def CHUNKUNROLL (out : BPtr) (dist len : UInt32) : M (BPtr × UInt32 × UInt32) := do
  let from_ ← out.add (-(Int.ofNat dist.toNat))
  let (out, dist, len) ← cwhile
    (fun ((out, dist, len) : BPtr × UInt32 × UInt32) => pure (dist < len && dist.toUInt64 < CHUNK, (out, dist, len)))
    (fun ((out, dist, len) : BPtr × UInt32 × UInt32) => do
      let chunk ← loadchunk from_
      storechunk out chunk
      let out ← out.add (Int.ofNat dist.toNat)
      pure (out, dist + dist, len - dist))
    (out, dist, len)
  return (out, dist, len)

/-- `static inline chunk_t GET_CHUNK_MAG(uint8_t *buf, size_t *chunk_rem, size_t dist)` (`chunkset_tpl.h:67-86`).
Returns `(chunk_load, *chunk_rem)`; `chunk_rem` is the value it had on entry if the loop does not run. -/
def GET_CHUNK_MAG (buf : BPtr) (chunk_rem dist : UInt64) : M (UInt64 × UInt64) := do
  let (chunk, _, _, rem) ← cwhile
    (fun ((c, br, cur, rem) : UInt64 × UInt64 × UInt64 × UInt64) => pure (br != 0, (c, br, cur, rem)))
    (fun ((c, br, cur, _) : UInt64 × UInt64 × UInt64 × UInt64) => do
      let cpy_dist := MIN dist br
      -- memcpy(cur_chunk, buf, cpy_dist): bytes cur .. cur + cpy_dist - 1 of chunk_load
      let (c, _) ← cwhile
        (fun ((c, i) : UInt64 × UInt64) => pure (i < cpy_dist, (c, i)))
        (fun ((c, i) : UInt64 × UInt64) => do
          let b ← index8 buf (Int.ofNat i.toNat)
          let sh := (cur + i) * 8
          let mask : UInt64 := ~~~((0xff : UInt64) <<< sh)
          pure ((c &&& mask) ||| (b.toUInt64 <<< sh), i + 1))
        (c, 0)
      pure (c, br - cpy_dist, cur + cpy_dist, cpy_dist))
    ((0 : UInt64), CHUNK, (0 : UInt64), chunk_rem)
  return (chunk, rem)

/-- Store bytes `start .. start + n - 1` of the chunk value at `out` (`memcpy(out, chunk_p + start, n)`). -/
def storeChunkBytes (out : BPtr) (chunk : UInt64) (start n : UInt64) : M Unit := do
  let _ ← cwhile
    (fun (i : UInt64) => pure (i < n, i))
    (fun (i : UInt64) => do
      Ptr.store (← out.add (Int.ofNat i.toNat)) (chunk >>> ((start + i) * 8)).toUInt8
      pure (i + 1))
    (0 : UInt64)
  pure ()

/-- `static inline uint8_t* CHUNKMEMSET(uint8_t *out, uint8_t *from, size_t len)` (`chunkset_tpl.h:111-274`). -/
def CHUNKMEMSET (out from_ : BPtr) (len : UInt64) : M BPtr := do
  let chunk_mod : UInt64 := 0
  let d ← Ptr.diff out from_
  let dist : UInt64 := (if d < 0 then -d else d).toUInt64
  if (← Ptr.lt out from_) && dist < len then
    Ptr.memmove out from_ len.toNat
    return ← out.add (Int.ofNat len.toNat)
  if dist == 1 then
    let b ← load8 from_
    Ptr.memset out b len.toNat
    return ← out.add (Int.ofNat len.toNat)
  if dist >= len || dist > CHUNK then
    return ← CHUNKCOPY out from_ len
  let (chunk_load, chunk_mod) ←
    if dist == 4 then do pure ((← chunkmemset_4 from_), chunk_mod)
    else if dist == 8 then do pure ((← chunkmemset_8 from_), chunk_mod)
    else if dist == CHUNK then do pure ((← loadchunk from_), chunk_mod)
    else GET_CHUNK_MAG from_ chunk_mod dist
  if len <= CHUNK then
    storechunk out chunk_load
    return ← out.add (Int.ofNat len.toNat)
  let adv_amount := CHUNK - chunk_mod
  let (out, len) ← cwhile
    (fun ((out, len) : BPtr × UInt64) => pure (len >= 2 * CHUNK, (out, len)))
    (fun ((out, len) : BPtr × UInt64) => do
      storechunk out chunk_load
      storechunk (← out.add (Int.ofNat adv_amount.toNat)) chunk_load
      let out ← out.add (Int.ofNat (2 * adv_amount).toNat)
      pure (out, len - 2 * adv_amount))
    (out, len)
  let (out, len) ← cwhile
    (fun ((out, len) : BPtr × UInt64) => pure (len >= CHUNK, (out, len)))
    (fun ((out, len) : BPtr × UInt64) => do
      storechunk out chunk_load
      let len := len - adv_amount
      let out ← out.add (Int.ofNat adv_amount.toNat)
      pure (out, len))
    (out, len)
  if len != 0 then
    if len >= 16 then
      storeChunkBytes out chunk_load 0 16
      storeChunkBytes (← out.add (Int.ofNat (len - 16).toNat)) chunk_load (len - 16) 16
    else if len >= 8 then
      storeChunkBytes out chunk_load 0 8
      storeChunkBytes (← out.add (Int.ofNat (len - 8).toNat)) chunk_load (len - 8) 8
    else if len >= 4 then
      storeChunkBytes out chunk_load 0 4
      storeChunkBytes (← out.add (Int.ofNat (len - 4).toNat)) chunk_load (len - 4) 4
    else if len >= 2 then
      storeChunkBytes out chunk_load 0 2
      storeChunkBytes (← out.add (Int.ofNat (len - 2).toNat)) chunk_load (len - 2) 2
    else
      storeChunkBytes out chunk_load 0 1
    return ← out.add (Int.ofNat len.toNat)
  return out

/-- `Z_INTERNAL uint8_t* CHUNKMEMSET_SAFE(uint8_t *out, uint8_t *from, size_t len, size_t left)`
(`chunkset_tpl.h:276-306`, `OPTIMAL_CMP == 64`: no alignment prologue). -/
def CHUNKMEMSET_SAFE (out from_ : BPtr) (len left : UInt64) : M BPtr := do
  let len := MIN len left
  if left < CHUNK then
    let (out, _, _) ← cwhile
      (fun ((out, from_, len) : BPtr × BPtr × UInt64) => pure (len > 0, (out, from_, len)))
      (fun ((out, from_, len) : BPtr × BPtr × UInt64) => do
        Ptr.store out (← load8 from_)
        pure (← out.add 1, ← from_.add 1, len - 1))
      (out, from_, len)
    return out
  if len != 0 then
    return ← CHUNKMEMSET out from_ len
  return out

/-- `static inline uint8_t *CHUNKCOPY_SAFE(uint8_t *out, uint8_t *from, size_t len, uint8_t *safe)`
(`chunkset_tpl.h:310-330`, no `HAVE_MASKED_READWRITE`). -/
def CHUNKCOPY_SAFE (out from_ : BPtr) (len : UInt64) (safe : BPtr) : M BPtr := do
  if out == from_ then
    return ← out.add (Int.ofNat len.toNat)
  let safelen := (← Ptr.diff safe out).toUInt64
  let len := MIN len safelen
  let d ← Ptr.diff safe from_
  let from_dist : UInt64 := (if d < 0 then -d else d).toUInt64
  if from_dist < CHUNK || safelen < CHUNK then
    let (out, _, _) ← cwhile
      (fun ((out, from_, len) : BPtr × BPtr × UInt64) => pure (len != 0, (out, from_, len)))
      (fun ((out, from_, len) : BPtr × BPtr × UInt64) => do
        Ptr.store out (← load8 from_)
        pure (← out.add 1, ← from_.add 1, len - 1))
      (out, from_, len)
    return out
  CHUNKMEMSET out from_ len

end ZlibNg.Chunkset
