import ZlibNgF.ZlibNg.«inflate.c»

/-!
# `infback.c` — inflate using a call-back interface (`ZlibNgF`)

Source: `zlib-ng/infback.c`, same build as `inflate.c.lean` (read its header first: the locals of the decoder are the
record `IL`, a mode is one `def` of the monad `X`, `break` returns, a fall-through is a tail call, `goto inf_leave` is
`throw .leave`). `ZLIB_COMPAT`; `inflateBackInit` is the hidden function behind `inflateBackInit_`. No
`INFLATE_STRICT`, no `INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR`, no `PKZIP_BUG_WORKAROUND`, no `ZLIB_DEBUG` (`Tracev`
and the `TRACE_*` macros are empty). `FUNCTABLE_CALL(inflate_fast_safe)` = `inflate_fast_safe_c`,
`FUNCTABLE_CALL(chunkmemset_safe)` = `chunkmemset_safe_c`.

## The call-backs

`inflateBack` takes the caller's functions as parameters; they are caller code, not library code:

* `in_func`, `uint32_t (*)(void *, z_const unsigned char **)`, is `InCb`. The C passes `&next`, the address of the local
  `next`. The call-back receives the current value of `next` and returns `(count, new value of *buf)`; a call-back that
  does not write `*buf` returns the value it received. A call-back that keeps the address and writes through it after
  it returned is not modelled.
* `out_func`, `int (*)(void *, unsigned char *, uint32_t)`, is `OutCb`.

The descriptors `in_desc` / `out_desc` (`void *`) are passed through unchanged; the model represents them as byte
pointers. Both call-backs run on the shared heap and can read and write any object; `inflateBack` assumes nothing
about them. A theorem about it states what it needs (`ZlibNgF.Spec.Common.Infback`).

## The locals

The locals of `inflateBack()` are the record `IL` of `inflate.c.lean` (the fields `in_`, `out` and `code_bits` are
not used). They start uninitialised (`IL.init`); the C writes `next have hold bits put left` before the loop, and
every mode writes `copy from here last len` before it reads them; `ret` is written before every `goto inf_leave`.

`state->lencode`, `state->lenbits`, `state->extra`, ... are read again after every statement that may call `in()` or
`out()` (the C reads them there; a call-back is foreign code).
-/

set_option autoImplicit false

namespace ZlibNg.Infback
open C ZlibNg.Zbuild ZlibNg.InflateP ZlibNg.Inflate

/-- `in_func`: `uint32_t (*)(void *in_desc, z_const unsigned char **buf)`; see the file comment. -/
abbrev InCb := BPtr → BPtr → M (UInt32 × BPtr)
/-- `out_func`: `int (*)(void *out_desc, unsigned char *buf, uint32_t len)` -/
abbrev OutCb := BPtr → BPtr → UInt32 → M Int32

/-- `int32_t inflateBackInit(PREFIX3(stream) *strm, int32_t windowBits, uint8_t *window)` (`infback.c:34-69`). -/
def inflateBackInit (strm : StreamPtr) (windowBits : Int32) (window : BPtr) : M Int32 := do
  if strm == none || window == .null || windowBits < MIN_WBITS || windowBits > MAX_WBITS then
    return Z_STREAM_ERROR
  wrZ strm fun z => { z with msg := .null }
  if (← rdZ strm (·.zalloc)) == .null then
    wrZ strm fun z => { z with zalloc := .zcalloc }
    wrZ strm fun z => { z with «opaque» := .null }
  if (← rdZ strm (·.zfree)) == .null then
    wrZ strm fun z => { z with zfree := .zcfree }
  let alloc_bufs ← alloc_inflate strm
  if alloc_bufs == none then return Z_MEM_ERROR
  let st ← (← ldAllocs alloc_bufs).state.get
  wrS st fun s => { s with alloc_bufs := .val alloc_bufs }
  wrZ strm fun z => { z with state := st }
  wrS st fun s => { s with wbits := windowBits.toUInt32 }
  let w ← shl32 1 windowBits.toUInt32
  wrS st fun s => { s with wsize := w }
  let w ← shl32 1 windowBits.toUInt32
  wrS st fun s => { s with wbufsize := w }
  wrS st fun s => { s with window := .val window }
  wrS st fun s => { s with wnext := 0 }
  wrS st fun s => { s with whave := 0 }
  return Z_OK

/-- `int32_t Z_EXPORT inflateBackInit_(PREFIX3(stream) *strm, int32_t windowBits, uint8_t *window,
const char *version, int32_t stream_size)` (`infback.c:72-77`). -/
def inflateBackInit_ (strm : StreamPtr) (windowBits : Int32) (window : BPtr) (version : BPtr)
    (stream_size : Int32) : M Int32 := do
  if ← CHECK_VER_STSIZE version stream_size then return Z_VERSION_ERROR
  inflateBackInit strm windowBits window

/-! ## `inflateBack()` -/

/-- What the modes of `inflateBack()` share: the stream, its state, and the call-backs with their descriptors. -/
structure BCtx where
  strm : StreamPtr
  st : StatePtr
  inCb : InCb
  inDesc : BPtr
  outCb : OutCb
  outDesc : BPtr

/-- The stream and state, for the macros of `inflate_p.h` shared with `inflate()` (`LOAD`, `RESTORE`, `SET_BAD`);
they do not read `flush`. -/
def BCtx.ctx (c : BCtx) : Ctx := ⟨c.strm, c.st, 0⟩

/-- `PULL()` (`infback.c:86-96`) -/
def PULL (c : BCtx) : X Unit := do
  if (← get).have_ == 0 then
    let (n, nx) ← c.inCb c.inDesc (← get).next
    modify fun l => { l with have_ := n, next := nx }
    if (← get).have_ == 0 then
      modify fun l => { l with next := .null }
      modify fun l => { l with ret := Z_BUF_ERROR }
      throw Ex.leave

/-- `PULLBYTE()` (`infback.c:100-106`) -/
def PULLBYTE (c : BCtx) : X Unit := do
  PULL c
  modify fun l => { l with have_ := l.have_ - 1 }
  let l ← get
  let b ← load8 l.next
  let nx ← l.next.add 1
  let sh ← shl64 b.toUInt64 l.bits.toUInt32
  set { l with next := nx, hold := l.hold + sh }
  modify fun l => { l with bits := l.bits + 8 }

/-- `NEEDBITS(n)` of `inflate_p.h` with the `PULLBYTE()` of `infback.c`. -/
def NEEDBITS (c : BCtx) (n : UInt32) : X Unit :=
  xwhile (do return (← get).bits < n.toUInt8) (PULLBYTE c)

/-- `ROOM()` (`infback.c:111-122`) -/
def ROOM (c : BCtx) : X Unit := do
  if (← get).left == 0 then
    let w ← (← rdS c.st (·.window)).get
    modify fun l => { l with put := w }
    let ws ← rdS c.st (·.wsize)
    modify fun l => { l with left := ws }
    let left := (← get).left
    wrS c.st fun s => { s with whave := left }
    let l ← get
    if (← c.outCb c.outDesc l.put l.left) != 0 then
      modify fun l => { l with ret := Z_BUF_ERROR }
      throw Ex.leave

/-- `for (;;) { here = TAB[BITS(NBITS)]; if (CODE_BITS(here) <= bits) break; PULLBYTE(); }` and, when `first here`,
the second-level lookup `for (;;) { here = TAB[last.val + (BITS(last_bits + (last.op & 15)) >> last_bits)]; if
(last_bits + CODE_BITS(here) <= bits) break; PULLBYTE(); } DROPBITS(last_bits);` of `LEN` (`infback.c:377-394`,
`431-448`). `tab` and `nbits` read `state->lencode` / `state->lenbits` (or the distance fields) on every trip. -/
def decodeSym (c : BCtx) (tab : InflateState → Ival CodePtr) (nbits : InflateState → UInt32)
    (first : Code → Bool) : X Unit := do
  xloopBrk (do
    let t ← (← rdS c.st tab).get
    let b ← BITS (← rdS c.st nbits)
    let here : Code ← Ptr.index t (Int.ofNat b.toNat)
    modify fun l => { l with here := here }
    if CODE_BITS (← get).here <= (← get).bits.toUInt32 then return true
    PULLBYTE c
    return false)
  if first (← get).here then
    modify fun l => { l with last := l.here }
    let last_bits := CODE_BITS (← get).last
    xloopBrk (do
      let t ← (← rdS c.st tab).get
      let last := (← get).last
      let b ← BITS (last_bits + (last.op &&& 15).toUInt32)
      let idx := last.val.toUInt64 + (← shr64 b last_bits)
      let here : Code ← Ptr.index t (Int.ofNat idx.toNat)
      modify fun l => { l with here := here }
      if last_bits + CODE_BITS (← get).here <= (← get).bits.toUInt32 then return true
      PULLBYTE c
      return false)
    DROPBITS last_bits

/-! ### The modes -/

/-- `case TYPE:` (`infback.c:187-215`) -/
def back_TYPE (c : BCtx) : X Unit := do
  if (← rdS c.st (·.last)) != 0 then
    BYTEBITS
    setMode c.st DONE
    return
  NEEDBITS c 3
  let b ← BITS 1
  wrS c.st fun s => { s with last := b.toUInt32.toInt32 }
  DROPBITS 1
  let t ← BITS 2
  if t == 0 then
    setMode c.st STORED
  else if t == 1 then
    fixedtables c.st
    setMode c.st LEN
  else if t == 2 then
    setMode c.st TABLE
  else
    SET_BAD c.ctx "invalid block type"
  DROPBITS 2

/-- `case STORED:` (`infback.c:217-245`) -/
def back_STORED (c : BCtx) : X Unit := do
  BYTEBITS
  NEEDBITS c 32
  let hold := (← get).hold
  if (hold &&& (0xffff : UInt64)) != ((hold >>> 16) ^^^ (0xffff : UInt64)) then
    SET_BAD c.ctx "invalid stored block lengths"
    return
  wrS c.st fun s => { s with length := hold.toUInt16.toUInt32 }
  INITBITS
  xwhile (do return (← rdS c.st (·.length)) != 0) (do
    let len ← rdS c.st (·.length)
    modify fun l => { l with copy := len }
    PULL c
    ROOM c
    modify fun l => { l with copy := (MIN l.copy.toUInt64 l.have_.toUInt64).toUInt32 }
    modify fun l => { l with copy := (MIN l.copy.toUInt64 l.left.toUInt64).toUInt32 }
    let l ← get
    Ptr.memcpy l.put l.next l.copy.toNat
    let nx ← l.next.add (Int.ofNat l.copy.toNat)
    modify fun l => { l with have_ := l.have_ - l.copy, next := nx }
    let pt ← l.put.add (Int.ofNat l.copy.toNat)
    modify fun l => { l with left := l.left - l.copy, put := pt }
    let copy := (← get).copy
    wrS c.st fun s => { s with length := s.length - copy })
  setMode c.st TYPE

/-- `case MATCH:` (`infback.c:489-514`) -/
def back_MATCH (c : BCtx) : X Unit := do
  let s ← ldState c.st
  let left := (← get).left
  if s.offset > s.wsize - (if s.whave < s.wsize then left else 0) then
    SET_BAD c.ctx "invalid distance too far back"
    return
  let body : X Unit := do
    ROOM c
    let s ← ldState c.st
    modify fun l => { l with copy := s.wsize - s.offset }
    let l ← get
    if l.copy < l.left then
      let fr ← l.put.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with from_ := fr }
      modify fun l => { l with copy := l.left - l.copy }
      let len ← rdS c.st (·.length)
      modify fun l => { l with copy := (MIN l.copy.toUInt64 len.toUInt64).toUInt32 }
      let l ← get
      let safe ← l.put.add (Int.ofNat l.left.toNat)
      let pt ← chunkcopy_safe l.put l.from_ l.copy.toUInt64 safe
      modify fun l => { l with put := pt }
    else
      let len ← rdS c.st (·.length)
      modify fun l => { l with copy := (MIN len.toUInt64 l.left.toUInt64).toUInt32 }
      let l ← get
      let off ← rdS c.st (·.offset)
      let src ← l.put.add (-(Int.ofNat off.toNat))
      let pt ← ZlibNg.ChunksetC.chunkmemset_safe_c l.put src l.copy.toUInt64 l.left.toUInt64
      modify fun l => { l with put := pt }
    let copy := (← get).copy
    wrS c.st fun s => { s with length := s.length - copy }
    modify fun l => { l with left := l.left - l.copy }
  body
  xwhile (do return (← rdS c.st (·.length)) != 0) body
  setMode c.st LEN

/-- `case LEN:` (`infback.c:364-487`) -/
def back_LEN (c : BCtx) : X Unit := do
  let l ← get
  if l.have_ >= INFLATE_FAST_MIN_HAVE && l.left >= INFLATE_FAST_MIN_SAFE then
    RESTORE c.ctx
    ZlibNg.ChunksetC.inflate_fast_safe_c c.strm (← rdS c.st (·.wsize))
    LOAD c.ctx
    return
  decodeSym c (·.lencode) (·.lenbits) (fun h => h.op != 0 && (h.op &&& 0xf0) == 0)
  DROPBITS (CODE_BITS (← get).here)
  let here := (← get).here
  wrS c.st fun s => { s with length := here.val.toUInt32 }
  if here.op.toNat == 0 then
    ROOM c
    let len ← rdS c.st (·.length)
    let l ← get
    Ptr.store l.put len.toUInt8
    let pt ← l.put.add 1
    modify fun l => { l with put := pt }
    modify fun l => { l with left := l.left - 1 }
    setMode c.st LEN
    return
  if (here.op &&& 32) != 0 then
    setMode c.st TYPE
    return
  if (here.op &&& 64) != 0 then
    SET_BAD c.ctx "invalid literal/length code"
    return
  wrS c.st fun s => { s with extra := CODE_EXTRA here }
  if (← rdS c.st (·.extra)) != 0 then
    NEEDBITS c (← rdS c.st (·.extra))
    let b ← BITS (← rdS c.st (·.extra))
    wrS c.st fun s => { s with length := s.length + b.toUInt32 }
    DROPBITS (← rdS c.st (·.extra))
  decodeSym c (·.distcode) (·.distbits) (fun h => (h.op &&& 0xf0) == 0)
  DROPBITS (CODE_BITS (← get).here)
  let here := (← get).here
  if (here.op &&& 64) != 0 then
    SET_BAD c.ctx "invalid distance code"
    return
  wrS c.st fun s => { s with offset := here.val.toUInt32 }
  wrS c.st fun s => { s with extra := CODE_EXTRA here }
  if (← rdS c.st (·.extra)) != 0 then
    NEEDBITS c (← rdS c.st (·.extra))
    let b ← BITS (← rdS c.st (·.extra))
    wrS c.st fun s => { s with offset := s.offset + b.toUInt32 }
    DROPBITS (← rdS c.st (·.extra))
  let s ← ldState c.st
  let left := (← get).left
  if s.offset > s.wsize - (if s.whave < s.wsize then left else 0) then
    SET_BAD c.ctx "invalid distance too far back"
    return
  let body : X Unit := do
    ROOM c
    let s ← ldState c.st
    modify fun l => { l with copy := s.wsize - s.offset }
    let l ← get
    if l.copy < l.left then
      let fr ← l.put.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with from_ := fr }
      modify fun l => { l with copy := l.left - l.copy }
    else
      let off ← rdS c.st (·.offset)
      let fr ← l.put.add (-(Int.ofNat off.toNat))
      modify fun l => { l with from_ := fr }
      modify fun l => { l with copy := l.left }
    let len ← rdS c.st (·.length)
    modify fun l => { l with copy := (MIN l.copy.toUInt64 len.toUInt64).toUInt32 }
    let copy := (← get).copy
    wrS c.st fun s => { s with length := s.length - copy }
    modify fun l => { l with left := l.left - l.copy }
    let byte : X Unit := do
      let l ← get
      let v ← load8 l.from_
      Ptr.store l.put v
      let pt ← l.put.add 1
      let fr ← l.from_.add 1
      modify fun l => { l with put := pt, from_ := fr }
    byte
    xwhile (do modify fun l => { l with copy := l.copy - 1 }; return (← get).copy != 0) byte
  body
  xwhile (do return (← rdS c.st (·.length)) != 0) body

/-- `case TABLE:` (`infback.c:247-362`), falling through to `LEN`. -/
def back_TABLE (c : BCtx) : X Unit := do
  NEEDBITS c 14
  let b ← BITS 5
  wrS c.st fun s => { s with nlen := b.toUInt32 + 257 }
  DROPBITS 5
  let b ← BITS 5
  wrS c.st fun s => { s with ndist := b.toUInt32 + 1 }
  DROPBITS 5
  let b ← BITS 4
  wrS c.st fun s => { s with ncode := b.toUInt32 + 4 }
  DROPBITS 4
  let s ← ldState c.st
  if s.nlen > 286 || s.ndist > 30 then
    SET_BAD c.ctx "too many length or distance symbols"
    return
  wrS c.st fun s => { s with «have» := 0 }
  let lens ← lensP c.st
  xwhile (do let s ← ldState c.st; return s.«have» < s.ncode) (do
    NEEDBITS c 3
    let hv ← rdS c.st (·.«have»)
    wrS c.st fun s => { s with «have» := s.«have» + 1 }
    let o ← ZlibNg.Inftrees.aget order hv.toNat
    let b ← BITS 3
    Ptr.store (← lens.add (Int.ofNat o.toNat)) b.toUInt16
    DROPBITS 3)
  xwhile (do return (← rdS c.st (·.«have»)) < 19) (do
    let hv ← rdS c.st (·.«have»)
    wrS c.st fun s => { s with «have» := s.«have» + 1 }
    let o ← ZlibNg.Inftrees.aget order hv.toNat
    Ptr.store (← lens.add (Int.ofNat o.toNat)) (0 : UInt16))
  let codes ← codesP c.st
  wrS c.st fun s => { s with next := .val codes }
  let nx ← (← rdS c.st (·.next)).get
  wrS c.st fun s => { s with lencode := .val nx }
  wrS c.st fun s => { s with lenbits := 7 }
  let s ← ldState c.st
  let (ret, nx, lb) ← ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.CODES lens 19 (← s.next.get) s.lenbits
    (← workP c.st)
  wrS c.st fun s => { s with next := .val nx, lenbits := lb }
  modify fun l => { l with ret := ret }
  if ret != 0 then
    SET_BAD c.ctx "invalid code lengths set"
    return
  wrS c.st fun s => { s with «have» := 0 }
  xwhileBrk (do
      let s ← ldState c.st
      return s.«have» < s.nlen + s.ndist)
    (do
      xloopBrk (do
        let lc ← (← rdS c.st (·.lencode)).get
        let b ← BITS (← rdS c.st (·.lenbits))
        let here : Code ← Ptr.index lc (Int.ofNat b.toNat)
        modify fun l => { l with here := here }
        if (← get).here.bits <= (← get).bits then return true
        PULLBYTE c
        return false)
      let here := (← get).here
      if here.val < 16 then
        DROPBITS here.bits.toUInt32
        let hv ← rdS c.st (·.«have»)
        wrS c.st fun s => { s with «have» := s.«have» + 1 }
        Ptr.store (← lens.add (Int.ofNat hv.toNat)) here.val
        return false
      else
        if here.val == 16 then
          NEEDBITS c (here.bits.toUInt32 + 2)
          DROPBITS here.bits.toUInt32
          let hv ← rdS c.st (·.«have»)
          if hv == 0 then
            SET_BAD c.ctx "invalid bit length repeat"
            return true
          let len ← Ptr.index lens (Int.ofNat (hv - 1).toNat)
          modify fun l => { l with len := len.toUInt32 }
          let b ← BITS 2
          modify fun l => { l with copy := 3 + b.toUInt32 }
          DROPBITS 2
        else if here.val == 17 then
          NEEDBITS c (here.bits.toUInt32 + 3)
          DROPBITS here.bits.toUInt32
          modify fun l => { l with len := 0 }
          let b ← BITS 3
          modify fun l => { l with copy := 3 + b.toUInt32 }
          DROPBITS 3
        else
          NEEDBITS c (here.bits.toUInt32 + 7)
          DROPBITS here.bits.toUInt32
          modify fun l => { l with len := 0 }
          let b ← BITS 7
          modify fun l => { l with copy := 11 + b.toUInt32 }
          DROPBITS 7
        let s ← ldState c.st
        if s.«have» + (← get).copy > s.nlen + s.ndist then
          SET_BAD c.ctx "invalid bit length repeat"
          return true
        xwhile (do return (← get).copy != 0) (do
          modify fun l => { l with copy := l.copy - 1 }
          let hv ← rdS c.st (·.«have»)
          wrS c.st fun s => { s with «have» := s.«have» + 1 }
          Ptr.store (← lens.add (Int.ofNat hv.toNat)) (← get).len.toUInt16)
        return false)
  if (← rdS c.st (·.mode)) == BAD then return
  if (← Ptr.index lens 256) == (0 : UInt16) then
    SET_BAD c.ctx "invalid code -- missing end-of-block"
    return
  wrS c.st fun s => { s with next := .val codes }
  let nx ← (← rdS c.st (·.next)).get
  wrS c.st fun s => { s with lencode := .val nx }
  wrS c.st fun s => { s with lenbits := MAX_LEN_ROOT_BITS }
  let s ← ldState c.st
  let (ret, nx, lb) ← ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.LENS lens s.nlen (← s.next.get) s.lenbits
    (← workP c.st)
  wrS c.st fun s => { s with next := .val nx, lenbits := lb }
  modify fun l => { l with ret := ret }
  if ret != 0 then
    SET_BAD c.ctx "invalid literal/lengths set"
    return
  setWideLen c.st lens
  let nx ← (← rdS c.st (·.next)).get
  wrS c.st fun s => { s with distcode := .val nx }
  wrS c.st fun s => { s with distbits := 9 }
  let s ← ldState c.st
  let (ret, nx, db) ← ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.DISTS (← lens.add (Int.ofNat s.nlen.toNat))
    s.ndist (← s.next.get) s.distbits (← workP c.st)
  wrS c.st fun s => { s with next := .val nx, distbits := db }
  modify fun l => { l with ret := ret }
  if ret != 0 then
    SET_BAD c.ctx "invalid distances set"
    return
  setMode c.st LEN
  back_LEN c

/-- One trip of `for (;;) switch (state->mode)` (`infback.c:185-528`). -/
def dispatch (c : BCtx) : X Unit := do
  let m ← rdS c.st (·.mode)
  if m == TYPE then back_TYPE c
  else if m == STORED then back_STORED c
  else if m == TABLE then back_TABLE c
  else if m == LEN then back_LEN c
  else if m == MATCH then back_MATCH c
  else if m == DONE then
    modify fun l => { l with ret := Z_STREAM_END }
    throw Ex.leave
  else if m == BAD then
    modify fun l => { l with ret := Z_DATA_ERROR }
    throw Ex.leave
  else
    modify fun l => { l with ret := Z_STREAM_ERROR }
    throw Ex.leave

/-- The code after `inf_leave:` (`infback.c:531-539`). -/
def backLeave (c : BCtx) : X Int32 := do
  let s ← ldState c.st
  if (← get).left < s.wsize then
    let w ← s.window.get
    let r ← c.outCb c.outDesc w (s.wsize - (← get).left)
    if r != 0 && (← get).ret == Z_STREAM_END then
      modify fun l => { l with ret := Z_BUF_ERROR }
  let l ← get
  wrZ c.strm fun z => { z with next_in := l.next, avail_in := l.have_ }
  return (← get).ret

/-- `int32_t Z_EXPORT inflateBack(PREFIX3(stream) *strm, PREFIX(in_func) in, void *in_desc, PREFIX(out_func) out,
void *out_desc)` (`infback.c:151-540`). -/
def inflateBack (strm : StreamPtr) (inCb : InCb) (in_desc : BPtr) (outCb : OutCb) (out_desc : BPtr) :
    M Int32 := do
  if strm == none then return Z_STREAM_ERROR
  if (← rdZ strm (·.state)) == none then return Z_STREAM_ERROR
  let st ← stateOf strm
  wrZ strm fun z => { z with msg := .null }
  wrS st fun s => { s with mode := TYPE, last := 0, whave := 0 }
  let c : BCtx := ⟨strm, st, inCb, in_desc, outCb, out_desc⟩
  let body : X Int32 := do
    let nx ← rdZ strm (·.next_in)
    modify fun l => { l with next := nx }
    let hv ← if (← get).next != .null then rdZ strm (·.avail_in) else pure 0
    modify fun l => { l with have_ := hv }
    modify fun l => { l with hold := 0 }
    modify fun l => { l with bits := 0 }
    let w ← (← rdS st (·.window)).get
    modify fun l => { l with put := w }
    let ws ← rdS st (·.wsize)
    modify fun l => { l with left := ws }
    tryCatch (xloopBrk (do dispatch c; return false)) (fun _ => pure ())
    backLeave c
  let g ← uninitLocals 2
  let (r, _) ← StateT.run (ExceptT.run body) (IL.init g)
  match r with
  | .ok v => return v
  | .error _ => ub "unreachable: inf_leave outside inflateBack"

/-- `int32_t Z_EXPORT inflateBackEnd(PREFIX3(stream) *strm)` (`infback.c:542-551`). -/
def inflateBackEnd (strm : StreamPtr) : M Int32 := do
  if strm == none then return Z_STREAM_ERROR
  let z ← ldStream strm
  if z.state == none || z.zfree == .null then return Z_STREAM_ERROR
  free_inflate strm
  return Z_OK

end ZlibNg.Infback
