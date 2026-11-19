import ZlibNgF.ZlibNg.«chunkset_tpl.h»
import ZlibNgF.ZlibNg.«inflate_p.h»

/-!
# `inffast_tpl.h` — fast decoding loop (`ZlibNgF`)

Source: `zlib-ng/inffast_tpl.h` with patch 0007, instantiated twice by `zlib-ng/arch/generic/chunkset_c.c`:
`inflate_fast_c` (`safeMode = false`) and `inflate_fast_safe_c` (`USE_SAFE_MODE`, `safeMode = true`), with the
chunk functions of `chunkset_tpl.h.lean`, no `HAVE_MASKED_READWRITE`, no `INFLATE_STRICT`, no
`INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR`. `bits_t` is `uint8_t` (x86_64).

## Control flow

One trip of the `do { ... } while (in < last && out < end);` loop is a small state machine over the labels of the
body: `top` (the start of the body), `dolen:`, the length/distance dispatch after `op = here.op;` (`common`), and
`dodist:`. `goto dolen` / `goto dodist` move to that label; `continue` ends the trip (the loop condition is then
evaluated); `break` leaves the loop.

`Z_TOUCH(here)` is an empty statement in this build.
-/

set_option autoImplicit false

namespace ZlibNg.Inffast
open C ZlibNg.Zbuild ZlibNg.InflateP ZlibNg.Chunkset

/-- `BAD` of `inflate_mode` -/
def BAD : UInt32 := 16209
/-- `TYPE` -/
def TYPE : UInt32 := 16191
/-- `MATCH` -/
def MATCH : UInt32 := 16204

/-- The locals of `INFLATE_FAST`. -/
structure FL where
  in_ : BPtr
  out : BPtr
  hold : UInt64
  bits : UInt8
  here : Code
  op : UInt32
  len : UInt32
  from_ : BPtr
  dist : UInt32
  old : UInt64
  deriving Inhabited

/-- Where a trip of the loop goes next. -/
inductive Lbl where
  | dolen
  | common
  | dodist
  | cont
  | brk
  deriving DecidableEq

/-- The values `INFLATE_FAST` copies from the state at entry. -/
structure FC where
  strm : StreamPtr
  st : StatePtr
  last : BPtr
  beg : BPtr
  end_ : BPtr
  safe : BPtr
  window : BPtr
  wsize : UInt32
  whave : UInt32
  wnext : UInt32
  lcode : CodePtr
  dcode : CodePtr
  lmask : UInt32
  dmask : UInt32
  safeMode : Bool

/-- `REFILL()`: `hold |= load_64_bits(in, bits); in += (63 ^ bits) >> 3; bits |= 56;` -/
def REFILL (l : FL) : M FL := do
  let w ← load_64_bits l.in_ l.bits.toUInt32
  let hold := l.hold ||| w
  let in_ ← l.in_.add (Int.ofNat ((63 ^^^ l.bits.toUInt32) >>> 3).toNat)
  return { l with hold, in_, bits := l.bits ||| 56 }

/-- `DROPBITS(n)`: `hold >>= u; bits -= (bits_t)u;` -/
def DROPBITS (l : FL) (n : UInt32) : M FL := do
  let hold ← shr64 l.hold n
  return { l with hold, bits := l.bits - n.toUInt8 }

/-- `BITS(n)`: `(hold & ((1U << (unsigned)(n)) - 1))` -/
def BITS (l : FL) (n : UInt32) : M UInt64 := do
  let m ← shl32 1 n
  return l.hold &&& (m - 1).toUInt64

/-- `SET_BAD(errmsg)`: `state->mode = BAD; strm->msg = errmsg;` -/
def SET_BAD (c : FC) (msg : String) : M Unit := do
  let s ← ldState c.st
  stState c.st { s with mode := BAD }
  let p ← strLitRef msg
  let z ← ldStream c.strm
  stStream c.strm { z with msg := p }

/-- `*out++ = (unsigned char)(here.val);` -/
def putLit (l : FL) : M FL := do
  Ptr.store l.out l.here.val.toUInt8
  return { l with out := ← l.out.add 1 }

/-- `here = lcode[hold & lmask];` -/
def lookupLen (c : FC) (l : FL) : M FL := do
  let here : Code ← Ptr.index c.lcode (Int.ofNat (l.hold &&& c.lmask.toUInt64).toNat)
  return { l with here }

/-- The body from the start of a trip to its first label change. -/
def stepTop (c : FC) (l : FL) : M (FL × Lbl) := do
  let l ← lookupLen c l
  let l ← REFILL l
  let l := { l with old := l.hold }
  let l ← DROPBITS l l.here.bits.toUInt32
  if l.here.op == 0 then
    let l ← putLit l
    let l ← lookupLen c l
    let l := { l with old := l.hold }
    let l ← DROPBITS l l.here.bits.toUInt32
    if l.here.op == 0 then
      let l ← putLit l
      let l ← lookupLen c l
      return (l, .dolen)
    return (l, .common)
  return (l, .common)

/-- `dolen:` -/
def stepDolen (_c : FC) (l : FL) : M (FL × Lbl) := do
  let l := { l with old := l.hold }
  let l ← DROPBITS l l.here.bits.toUInt32
  if l.here.op == 0 then
    let l ← putLit l
    return (l, .cont)
  return (l, .common)

/-- From `op = here.op;` to the next label. -/
def stepCommon (c : FC) (l : FL) : M (FL × Lbl) := do
  let l := { l with op := l.here.op.toUInt32 }
  if (l.op &&& 16 : UInt32) != (0 : UInt32) then
    let e ← EXTRA_BITS l.old l.here l.op
    let l := { l with len := l.here.val.toUInt32 + e.toUInt32 }
    let here : Code ← Ptr.index c.dcode (Int.ofNat (l.hold &&& c.dmask.toUInt64).toNat)
    let l := { l with here }
    let l ← if l.bits.toUInt32 < MAX_BITS + 13 + 10 then REFILL l else pure l
    return (l, .dodist)
  else if (l.op &&& 64 : UInt32) == (0 : UInt32) then
    let b ← BITS l l.op
    let here : Code ← Ptr.index c.lcode (Int.ofNat (l.here.val.toUInt64 + b).toNat)
    return ({ l with here }, .dolen)
  else if (l.op &&& 32 : UInt32) != (0 : UInt32) then
    let s ← ldState c.st
    stState c.st { s with mode := TYPE }
    return (l, .brk)
  else
    SET_BAD c "invalid literal/length code"
    return (l, .brk)

/-- `dodist:` -/
def stepDodist (c : FC) (l : FL) : M (FL × Lbl) := do
  let l : FL := { l with old := l.hold }
  let l ← DROPBITS l l.here.bits.toUInt32
  let l : FL := { l with op := l.here.op.toUInt32 }
  if (l.op &&& 16 : UInt32) != (0 : UInt32) then
    let e ← EXTRA_BITS l.old l.here l.op
    let l : FL := { l with dist := l.here.val.toUInt32 + e.toUInt32 }
    if c.safeMode then
      -- if (UNLIKELY(len > (unsigned)(safe - out)))
      let room := (← Ptr.diff c.safe l.out).toUInt64.toUInt32
      if l.len > room then
        let s ← ldState c.st
        stState c.st { s with mode := MATCH, length := l.len, was := l.len, offset := l.dist }
        return (l, .brk)
    let op := (← Ptr.diff l.out c.beg).toUInt64.toUInt32
    let l : FL := { l with op := op }
    if l.dist > l.op then
      let l : FL := { l with op := l.dist - l.op }
      if l.op > c.whave then
        SET_BAD c "invalid distance too far back"
        return (l, .brk)
      let mut l : FL := { l with from_ := c.window }
      if c.wnext == 0 then
        l := { l with from_ := ← l.from_.add (Int.ofNat (c.wsize - l.op).toNat) }
      else if c.wnext >= l.op then
        l := { l with from_ := ← l.from_.add (Int.ofNat (c.wnext - l.op).toNat) }
      else
        l := { l with op := l.op - c.wnext }
        l := { l with from_ := ← l.from_.add (Int.ofNat (c.wsize - l.op).toNat) }
        if l.op < l.len then
          l := { l with len := l.len - l.op }
          Ptr.memcpy l.out l.from_ l.op.toNat
          l := { l with out := ← l.out.add (Int.ofNat l.op.toNat) }
          l := { l with from_ := c.window, op := c.wnext }
      if l.op < l.len then
        l := { l with len := l.len - l.op }
        if !c.safeMode then
          Ptr.memcpy l.out l.from_ l.op.toNat
          l := { l with out := ← l.out.add (Int.ofNat l.op.toNat) }
          let (out, dist, len) ← CHUNKUNROLL l.out l.dist l.len
          l := { l with out, dist, len }
          let src ← l.out.add (-(Int.ofNat l.dist.toNat))
          l := { l with out := ← CHUNKCOPY_SAFE l.out src l.len.toUInt64 c.safe }
        else
          Ptr.memcpy l.out l.from_ l.op.toNat
          l := { l with out := ← l.out.add (Int.ofNat l.op.toNat) }
          let src ← l.out.add (-(Int.ofNat l.dist.toNat))
          l := { l with out := ← chunkcopy_safe l.out src l.len.toUInt64 c.safe }
      else
        Ptr.memcpy l.out l.from_ l.len.toNat
        l := { l with out := ← l.out.add (Int.ofNat l.len.toNat) }
      return (l, .cont)
    else
      if !c.safeMode then
        let src ← l.out.add (-(Int.ofNat l.dist.toNat))
        if l.dist >= l.len || l.dist.toUInt64 > CHUNKSIZE then
          return ({ l with out := ← CHUNKCOPY l.out src l.len.toUInt64 }, .cont)
        else
          return ({ l with out := ← CHUNKMEMSET l.out src l.len.toUInt64 }, .cont)
      else
        let src ← l.out.add (-(Int.ofNat l.dist.toNat))
        return ({ l with out := ← chunkcopy_safe l.out src l.len.toUInt64 c.safe }, .cont)
  else if (l.op &&& 64 : UInt32) == (0 : UInt32) then
    let b ← BITS l l.op
    let here : Code ← Ptr.index c.dcode (Int.ofNat (l.here.val.toUInt64 + b).toNat)
    return ({ l with here }, .dodist)
  else
    SET_BAD c "invalid distance code"
    return (l, .brk)

/-- One trip of the loop body: run from `top` until `continue` or `break`. Returns `true` for `break`. -/
def trip (c : FC) (l : FL) : M (FL × Bool) := do
  let (l, lbl) ← stepTop c l
  let (l, lbl) ← cwhile
    (fun ((l, lbl) : FL × Lbl) => pure (lbl != .cont && lbl != .brk, (l, lbl)))
    (fun ((l, lbl) : FL × Lbl) =>
      match lbl with
      | .dolen => stepDolen c l
      | .common => stepCommon c l
      | .dodist => stepDodist c l
      | _ => pure (l, lbl))
    (l, lbl)
  return (l, lbl == .brk)

/-- `void Z_INTERNAL INFLATE_FAST(PREFIX3(stream) *strm, uint32_t start)` (`inffast_tpl.h:96-342`). -/
def INFLATE_FAST (safeMode : Bool) (strm : StreamPtr) (start : UInt32) : M Unit := do
  let z ← ldStream strm
  let st := z.state
  let in_ := z.next_in
  let last ← in_.add (Int.ofNat (z.avail_in - (INFLATE_FAST_MIN_HAVE - 1)).toNat)
  let out := z.next_out
  let beg ← out.add (-(Int.ofNat (start - z.avail_out).toNat))
  let safe ← out.add (Int.ofNat z.avail_out.toNat)
  let end_ ← if safeMode then do (← safe.add (-(Int.ofNat INFLATE_FAST_MIN_SAFE.toNat))).add 1
    else do (← safe.add (-(Int.ofNat INFLATE_FAST_MIN_LEFT.toNat))).add 1
  let s ← ldState st
  let wsize := s.wsize
  let whave := s.whave
  let wnext := s.wnext
  let window ← s.window.get
  let hold := s.hold
  let bits := s.bits.toUInt8
  let lcode ← s.lencode.get
  let dcode ← s.distcode.get
  let lmask := (← shl32 1 s.lenbits) - 1
  let dmask := (← shl32 1 s.distbits) - 1
  let c : FC := ⟨strm, st, last, beg, end_, safe, window, wsize, whave, wnext, lcode, dcode, lmask, dmask,
    safeMode⟩
  let l : FL := ⟨in_, out, hold, bits, ⟨0, 0, 0⟩, 0, 0, .null, 0, 0⟩
  let l ← REFILL l
  let (l, _) ← cdoWhile
    (fun ((l, _) : FL × Bool) => trip c l)
    (fun ((l, brk) : FL × Bool) => do
      if brk then return (false, (l, brk))
      if ← Ptr.lt l.in_ c.last then
        return (← Ptr.lt l.out c.end_, (l, brk))
      return (false, (l, brk)))
    (l, false)
  -- return unused bytes (on entry, bits < 8, so in won't go too far back)
  let len := l.bits.toUInt32 >>> 3
  let in_ ← l.in_.add (-(Int.ofNat len.toNat))
  let bits := l.bits - (len <<< 3).toUInt8
  let hold := l.hold &&& ((← shl64 1 bits.toUInt32) - 1)
  -- update state and return
  let z ← ldStream strm
  let avail_in : UInt32 ←
    if ← Ptr.lt in_ last then do
      pure ((INFLATE_FAST_MIN_HAVE - 1).toUInt64 + (← Ptr.diff last in_).toUInt64).toUInt32
    else do
      pure ((INFLATE_FAST_MIN_HAVE - 1).toUInt64 - (← Ptr.diff in_ last).toUInt64).toUInt32
  let avail_out := (← Ptr.diff safe l.out).toUInt64.toUInt32
  stStream strm { z with next_in := in_, next_out := l.out, avail_in, avail_out }
  let s ← ldState st
  stState st { s with hold := hold.toUInt32.toUInt64, bits := bits.toUInt32 }

end ZlibNg.Inffast
