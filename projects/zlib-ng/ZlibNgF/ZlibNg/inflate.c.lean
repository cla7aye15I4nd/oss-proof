import ZlibNgF.ZlibNg.«zutil.c»
import ZlibNgF.ZlibNg.«adler32.c»
import ZlibNgF.ZlibNg.«crc32.c»
import ZlibNgF.ZlibNg.«inftrees.c»
import ZlibNgF.ZlibNg.arch.generic.«chunkset_c.c»

/-!
# `inflate.c` — zlib decompression (`ZlibNgF`)

Source: `zlib-ng/inflate.c` with patches 0001 (`inflateCopy`), 0004 (window copy in `MATCH`), 0005
(`inflateSync`), 0006 (`inflateSetDictionary`), 0007 (fast path only with fewer than 8 bits held, in `LEN`) and 0008 (bounded
copy into `head->extra`, in `EXTRA`); `ZLIB_COMPAT`, `GUNZIP` defined; no `INFLATE_STRICT`,
`INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR`, `S390_DFLTCC_INFLATE`, `ZLIB_DEBUG` (so `Tracev` and the hooks are
empty, `INFLATE_NEED_CHECKSUM` / `INFLATE_NEED_UPDATEWINDOW` are 1). `bits_t` is `uint8_t` (x86_64).

## Function table and callees
`FUNCTABLE_CALL(adler32)` = `adler32_c`, `(adler32_copy)` = `adler32_copy_c`, `(crc32)` = `crc32_braid`,
`(crc32_copy)` = `crc32_copy_braid`, `(inflate_fast)` = `inflate_fast_c`, `(inflate_fast_safe)` =
`inflate_fast_safe_c`, `(chunkmemset_safe)` = `chunkmemset_safe_c`. `strm->zalloc` / `strm->zfree` are called
through `FnPtr`: `zcalloc` / `zcfree` run the translation of `zutil.c`; any other function faults (not modelled).

## Control flow of `inflate()`
As in the translation of zlib's `inflate.c`: the locals of `inflate()` are the record `IL`, a mode of the `switch` is
one `def` of the monad `X = ExceptT Ex (StateT IL M)`; `break` returns, a fall-through is a tail call of the next
mode, `goto inf_leave` is `throw .leave`, `return v` is `throw (.ret v)`. The `for (;;)` reads `state->mode` on
every trip. The locals start uninitialised (`IL.init`): scalars from the garbage oracle, pointers NULL. `LOAD()` and
the next statement write `next put have left hold bits in out ret` first; every mode writes `copy len code_bits
here last from` before it reads them (a mode does not read a value left by another mode), so no path reads an
uninitialised local.

## Casts
`(int)(hold)` and the other conversions of an out-of-range value to a signed type are implementation-defined
(ISO C17 §6.3.1.3p3); the model takes GCC's modulo-2^N result. `strm->state` is an `inflate_state` here (deflate is
not translated).
-/

set_option autoImplicit false

namespace ZlibNg.Inflate
open C ZlibNg.Zbuild ZlibNg.InflateP

/-! ## Constants -/

def HEAD : UInt32 := 16180
def FLAGS : UInt32 := 16181
def TIME : UInt32 := 16182
def OS : UInt32 := 16183
def EXLEN : UInt32 := 16184
def EXTRA : UInt32 := 16185
def NAME : UInt32 := 16186
def COMMENT : UInt32 := 16187
def HCRC : UInt32 := 16188
def DICTID : UInt32 := 16189
def DICT : UInt32 := 16190
def TYPE : UInt32 := 16191
def TYPEDO : UInt32 := 16192
def STORED : UInt32 := 16193
def COPY_ : UInt32 := 16194
def COPY : UInt32 := 16195
def TABLE : UInt32 := 16196
def LENLENS : UInt32 := 16197
def CODELENS : UInt32 := 16198
def LEN_ : UInt32 := 16199
def LEN : UInt32 := 16200
def LENEXT : UInt32 := 16201
def DIST : UInt32 := 16202
def DISTEXT : UInt32 := 16203
def MATCH : UInt32 := 16204
def LIT : UInt32 := 16205
def CHECK : UInt32 := 16206
def LENGTH : UInt32 := 16207
def DONE : UInt32 := 16208
def BAD : UInt32 := 16209
def SYNC : UInt32 := 16211

def Z_OK : Int32 := 0
def Z_STREAM_END : Int32 := 1
def Z_NEED_DICT : Int32 := 2
def Z_STREAM_ERROR : Int32 := -2
def Z_DATA_ERROR : Int32 := -3
def Z_MEM_ERROR : Int32 := -4
def Z_BUF_ERROR : Int32 := -5
def Z_VERSION_ERROR : Int32 := -6
def Z_FINISH : Int32 := 4
def Z_BLOCK : Int32 := 5
def Z_TREES : Int32 := 6
def Z_DEFLATED : UInt64 := 8
def MAX_WBITS : Int32 := 15
def MIN_WBITS : Int32 := 8
def DEF_WBITS : Int32 := 15
def MAX_LEN_ROOT_BITS : UInt32 := 10
def ADLER32_INITIAL_VALUE : UInt64 := 1
def CRC32_INITIAL_VALUE : UInt64 := 0

/-! ## Heap access shorthands -/

def rdS {α : Type} (st : StatePtr) (f : InflateState → α) : M α := do return f (← ldState st)
def wrS (st : StatePtr) (f : InflateState → InflateState) : M Unit := do stState st (f (← ldState st))
def rdZ {α : Type} (strm : StreamPtr) (f : ZStream → α) : M α := do return f (← ldStream strm)
def wrZ (strm : StreamPtr) (f : ZStream → ZStream) : M Unit := do stStream strm (f (← ldStream strm))

/-- `state->lens` -/
def lensP (st : StatePtr) : M WPtr := match st with | some b => pure (.ref (.lens b) 0) | none => ub "null state"
/-- `state->work` -/
def workP (st : StatePtr) : M WPtr := match st with | some b => pure (.ref (.work b) 0) | none => ub "null state"
/-- `state->codes` -/
def codesP (st : StatePtr) : M CodePtr := match st with | some b => pure (.ref (.codes b) 0) | none => ub "null state"

/-- `strm->zalloc(strm->opaque, items, size)` -/
def callZalloc (f : FnPtr) (opq : BPtr) (items size : UInt32) : M BPtr :=
  match f with
  | .zcalloc => ZlibNg.Zutil.zcalloc opq items size
  | .null => ub "call through a null function pointer"
  | _ => ub "custom allocator not modelled"

/-- `zfree(opaque, ptr)` -/
def callZfree (f : FnPtr) (opq ptr : BPtr) : M Unit :=
  match f with
  | .zcfree => ZlibNg.Zutil.zcfree opq ptr
  | .null => ub "call through a null function pointer"
  | _ => ub "custom allocator not modelled"

/-- `strm->state` as an `inflate_state *` -/
def stateOf (strm : StreamPtr) : M StatePtr := rdZ strm (·.state)

/-! ## Checksums -/

/-- `static inline void inf_chksum_cpy(PREFIX3(stream) *strm, uint8_t *dst, const uint8_t *src, uint32_t copy)`
(`inflate.c:27-39`). -/
def inf_chksum_cpy (strm : StreamPtr) (dst src : BPtr) (copy : UInt32) : M Unit := do
  if copy == 0 then return
  let st ← stateOf strm
  let s ← ldState st
  let v ← if s.flags != 0 then
      ZlibNg.Crc32Braid.crc32_copy_braid s.check.toUInt32 dst src copy.toUInt64
    else ZlibNg.Adler32C.adler32_copy_c s.check.toUInt32 dst src copy.toUInt64
  wrS st fun s => { s with check := v.toUInt64 }
  wrZ strm fun z => { z with adler := v.toUInt64 }

/-- `static inline void inf_chksum(PREFIX3(stream) *strm, const uint8_t *src, uint32_t len)` (`inflate.c:41-51`). -/
def inf_chksum (strm : StreamPtr) (src : BPtr) (len : UInt32) : M Unit := do
  let st ← stateOf strm
  let s ← ldState st
  let v ← if s.flags != 0 then ZlibNg.Crc32Braid.crc32_braid s.check.toUInt32 src len.toUInt64
    else ZlibNg.Adler32C.adler32_c s.check.toUInt32 src len.toUInt64
  wrS st fun s => { s with check := v.toUInt64 }
  wrZ strm fun z => { z with adler := v.toUInt64 }

/-! ## State management -/

/-- `static int inflateStateCheck(PREFIX3(stream) *strm)` (`inflate.c:53-61`). -/
def inflateStateCheck (strm : StreamPtr) : M Bool := do
  if strm == none then return true
  let z ← ldStream strm
  if z.zalloc == .null || z.zfree == .null then return true
  let st := z.state
  if st == none then return true
  let s ← ldState st
  if (← s.alloc_bufs.get) == none then return true
  if (← s.strm.get) != strm then return true
  if s.mode < HEAD || s.mode > SYNC then return true
  return false

/-- `int32_t Z_EXPORT inflateResetKeep(PREFIX3(stream) *strm)` (`inflate.c:63-92`). -/
def inflateResetKeep (strm : StreamPtr) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let st ← stateOf strm
  wrS st fun s => { s with total := 0 }
  wrZ strm fun z => { z with total_out := 0 }
  wrZ strm fun z => { z with total_in := 0 }
  wrZ strm fun z => { z with msg := .null, data_type := 0 }
  let s ← ldState st
  if s.wrap != 0 then
    wrZ strm fun z => { z with adler := (s.wrap &&& 1).toInt64.toUInt64 }
  let codes ← codesP st
  wrS st fun s => { s with mode := HEAD, check := ADLER32_INITIAL_VALUE, last := 0, havedict := 0, flags := -1, head := .val none, hold := 0, bits := 0 }
  wrS st fun s => { s with next := .val codes }
  wrS st fun s => { s with distcode := .val codes }
  wrS st fun s => { s with lencode := .val codes }
  wrS st fun s => { s with back := -1 }
  return Z_OK

/-- `int32_t Z_EXPORT inflateReset(PREFIX3(stream) *strm)` (`inflate.c:94-105`). -/
def inflateReset (strm : StreamPtr) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let st ← stateOf strm
  wrS st fun s => { s with wbits := s.reqbits, wsize := 0, whave := 0, wnext := 0 }
  inflateResetKeep strm

/-- `int32_t Z_EXPORT inflateReset2(PREFIX3(stream) *strm, int32_t windowBits)` (`inflate.c:107-137`). -/
def inflateReset2 (strm : StreamPtr) (windowBits : Int32) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let st ← stateOf strm
  let mut windowBits := windowBits
  let mut wrap : Int32 := 0  -- `int wrap;`: both branches write it first; the 0 is never read
  if windowBits < 0 then
    wrap := 0
    if windowBits < -MAX_WBITS then return Z_STREAM_ERROR
    windowBits := -windowBits
  else
    wrap := ← chkI32 ((windowBits >>> 4).toInt + 5)
    if windowBits < 48 then
      windowBits := windowBits &&& MAX_WBITS
  if windowBits != 0 && (windowBits < MIN_WBITS || windowBits > MAX_WBITS) then return Z_STREAM_ERROR
  wrS st fun s => { s with wrap := wrap }
  wrS st fun s => { s with wbits := windowBits.toUInt32 }
  wrS st fun s => { s with reqbits := windowBits.toUInt32 }
  inflateReset strm

/-! ## Allocation -/

/-- `#define PADSZ(bpos, pad) (((pad) - ((uintptr_t)(bpos) % (pad))) % (pad))` on an integer `bpos`. -/
def PADSZ (bpos : UInt64) (pad : UInt64) : UInt64 := (pad - bpos % pad) % pad
/-- `PAD_64(bpos)` on an `int` `bpos`: `bpos + PADSZ(bpos, 64)` in `uintptr_t`, assigned back to `int`. -/
def PAD_64 (bpos : Int32) : Int32 := (bpos.toInt64.toUInt64 + PADSZ bpos.toInt64.toUInt64 64).toUInt32.toInt32
/-- `PAD_16(bpos)` on an `int`. -/
def PAD_16 (bpos : Int32) : Int32 := (bpos.toInt64.toUInt64 + PADSZ bpos.toInt64.toUInt64 16).toUInt32.toInt32

/-- `HINT_ALIGNED_64(p)`: `__builtin_assume_aligned(p, 64)`, undefined if `p` is not 64-byte aligned. -/
def HINT_ALIGNED_64 (p : BPtr) : M BPtr := Ptr.castAligned p 64

/-- `Z_INTERNAL inflate_allocs* alloc_inflate(PREFIX3(stream) *strm)` (`inflate.c:158-208`). -/
def alloc_inflate (strm : StreamPtr) : M AllocsPtr := do
  let curr_size : Int32 := 0
  let window_size : Int32 := ((1 : Int32) <<< 15) + 64
  let state_size : Int32 := SIZEOF_INFLATE_STATE.toInt32
  let alloc_size : Int32 := SIZEOF_INFLATE_ALLOCS.toInt32
  let window_pos := PAD_64 curr_size
  let curr_size ← chkI32 (window_pos.toInt + window_size.toInt)
  let state_pos := PAD_64 curr_size
  let curr_size ← chkI32 (state_pos.toInt + state_size.toInt)
  let alloc_pos := PAD_16 curr_size
  let curr_size ← chkI32 (alloc_pos.toInt + alloc_size.toInt)
  let total_size := PAD_64 (← chkI32 (curr_size.toInt + (64 - 1)))
  let z ← ldStream strm
  let original_buf ← callZalloc z.zalloc z.«opaque» 1 total_size.toUInt32
  if original_buf == .null then return none
  let ob ← addrOf original_buf
  let buff ← HINT_ALIGNED_64 (← original_buf.add (Int.ofNat (PADSZ ob 64).toNat))
  let alloc_bufs ← carveAllocs (← buff.add alloc_pos.toInt)
  let a ← ldAllocs alloc_bufs
  stAllocs alloc_bufs { a with buf_start := .val original_buf }
  let z ← ldStream strm
  let a ← ldAllocs alloc_bufs
  stAllocs alloc_bufs { a with zfree := .val z.zfree }
  let w ← HINT_ALIGNED_64 (← buff.add window_pos.toInt)
  let a ← ldAllocs alloc_bufs
  stAllocs alloc_bufs { a with window := .val w }
  let sp ← carveState (← buff.add state_pos.toInt)
  let a ← ldAllocs alloc_bufs
  stAllocs alloc_bufs { a with state := .val sp }
  return alloc_bufs

/-- `Z_INTERNAL void free_inflate(PREFIX3(stream) *strm)` (`inflate.c:213-221`). -/
def free_inflate (strm : StreamPtr) : M Unit := do
  let st ← stateOf strm
  let s ← ldState st
  let ab ← s.alloc_bufs.get
  if ab != none then
    let a ← ldAllocs ab
    let z ← ldStream strm
    callZfree (← a.zfree.get) z.«opaque» (← a.buf_start.get)
    wrZ strm fun z => { z with state := none }

/-- `int32_t ZNG_CONDEXPORT inflateInit2(PREFIX3(stream) *strm, int32_t windowBits)` (`inflate.c:227-258`). -/
def inflateInit2 (strm : StreamPtr) (windowBits : Int32) : M Int32 := do
  if strm == none then return Z_STREAM_ERROR
  wrZ strm fun z => { z with msg := .null }
  if (← rdZ strm (·.zalloc)) == .null then
    wrZ strm fun z => { z with zalloc := .zcalloc }
    wrZ strm fun z => { z with «opaque» := .null }
  if (← rdZ strm (·.zfree)) == .null then
    wrZ strm fun z => { z with zfree := .zcfree }
  let alloc_bufs ← alloc_inflate strm
  if alloc_bufs == none then return Z_MEM_ERROR
  let a ← ldAllocs alloc_bufs
  let st ← a.state.get
  let w ← (← ldAllocs alloc_bufs).window.get
  wrS st fun s => { s with window := .val w }
  wrS st fun s => { s with alloc_bufs := .val alloc_bufs }
  wrS st fun s => { s with wbufsize := ((1 : UInt32) <<< 15) + 64 }
  wrZ strm fun z => { z with state := st }
  wrS st fun s => { s with strm := .val strm }
  wrS st fun s => { s with mode := HEAD }
  let ret ← inflateReset2 strm windowBits
  if ret != Z_OK then
    free_inflate strm
  return ret

/-- `CHECK_VER_STSIZE(_ver,_stsize)` (`zutil.h:135`). -/
def CHECK_VER_STSIZE (version : BPtr) (stream_size : Int32) : M Bool := do
  if version == .null then return true
  let c ← index8 version 0
  if c != '1'.toNat.toUInt8 then return true
  return stream_size != SIZEOF_Z_STREAM.toInt32

/-- `int32_t Z_EXPORT inflateInit_(PREFIX3(stream) *strm, const char *version, int32_t stream_size)`
(`inflate.c:267-271`). -/
def inflateInit_ (strm : StreamPtr) (version : BPtr) (stream_size : Int32) : M Int32 := do
  if ← CHECK_VER_STSIZE version stream_size then return Z_VERSION_ERROR
  inflateInit2 strm DEF_WBITS

/-- `int32_t Z_EXPORT inflateInit2_(PREFIX3(stream) *strm, int32_t windowBits, const char *version,
int32_t stream_size)` (`inflate.c:274-278`). -/
def inflateInit2_ (strm : StreamPtr) (windowBits : Int32) (version : BPtr) (stream_size : Int32) : M Int32 := do
  if ← CHECK_VER_STSIZE version stream_size then return Z_VERSION_ERROR
  inflateInit2 strm windowBits

/-- `int32_t Z_EXPORT inflatePrime(PREFIX3(stream) *strm, int32_t bits, int32_t value)` (`inflate.c:280-299`). -/
def inflatePrime (strm : StreamPtr) (bits : Int32) (value : Int32) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  if bits == 0 then return Z_OK
  let st ← stateOf strm
  if bits < 0 then
    wrS st fun s => { s with hold := 0, bits := 0 }
    return Z_OK
  let s ← ldState st
  if bits > 16 || s.bits.toUInt64 + bits.toUInt32.toUInt64 > 32 then return Z_STREAM_ERROR
  -- value &= (1L << bits) - 1;   (long arithmetic)
  let m : Int64 := ((1 : Int64) <<< bits.toInt64) - 1
  let value := (value.toInt64 &&& m).toInt32
  let sh ← shl64 value.toInt64.toUInt64 s.bits
  wrS st fun s => { s with hold := s.hold + sh, bits := s.bits + bits.toUInt32 }
  return Z_OK

/-- `void Z_INTERNAL fixedtables(struct inflate_state *state)` (`inflate.c:306-311`). -/
def fixedtables (st : StatePtr) : M Unit := do
  wrS st fun s => { s with lencode := .val (.ref .lenfix 0) }
  wrS st fun s => { s with lenbits := 9 }
  wrS st fun s => { s with distcode := .val (.ref .distfix 0) }
  wrS st fun s => { s with distbits := 5 }

/-- `static void updatewindow(PREFIX3(stream) *strm, const uint8_t *end, uint32_t len, int32_t cksum)`
(`inflate.c:328-379`). -/
def updatewindow (strm : StreamPtr) (end_ : BPtr) (len : UInt32) (cksum : Int32) : M Unit := do
  let st ← stateOf strm
  if (← rdS st (·.wsize)) == 0 then
    let wb ← rdS st (·.wbits)
    let w ← shl32 1 wb
    wrS st fun s => { s with wsize := w }
  let s ← ldState st
  let window ← s.window.get
  if len >= s.wsize then
    if cksum != 0 then
      if len > s.wsize then
        inf_chksum strm (← end_.add (-(Int.ofNat len.toNat))) (len - s.wsize)
      inf_chksum_cpy strm window (← end_.add (-(Int.ofNat s.wsize.toNat))) s.wsize
    else
      Ptr.memcpy window (← end_.add (-(Int.ofNat s.wsize.toNat))) s.wsize.toNat
    wrS st fun s => { s with wnext := 0 }
    wrS st fun s => { s with whave := s.wsize }
  else
    let dist := s.wsize - s.wnext
    let dist := if dist > len then len else dist
    if cksum != 0 then
      inf_chksum_cpy strm (← window.add (Int.ofNat s.wnext.toNat)) (← end_.add (-(Int.ofNat len.toNat))) dist
    else
      Ptr.memcpy (← window.add (Int.ofNat s.wnext.toNat)) (← end_.add (-(Int.ofNat len.toNat))) dist.toNat
    let len := len - dist
    if len != 0 then
      if cksum != 0 then
        inf_chksum_cpy strm window (← end_.add (-(Int.ofNat len.toNat))) len
      else
        Ptr.memcpy window (← end_.add (-(Int.ofNat len.toNat))) len.toNat
      wrS st fun s => { s with wnext := len }
      wrS st fun s => { s with whave := s.wsize }
    else
      wrS st fun s => { s with wnext := s.wnext + dist }
      if (← rdS st (·.wnext)) == (← rdS st (·.wsize)) then
        wrS st fun s => { s with wnext := 0 }
      if (← rdS st (·.whave)) < (← rdS st (·.wsize)) then
        wrS st fun s => { s with whave := s.whave + dist }

/-! ## `inflate()` -/

/-- How a mode leaves other than by `break`: `goto inf_leave`, or `return v`. -/
inductive Ex where
  | leave
  | ret (v : Int32)

/-- The locals of `inflate()`. -/
structure IL where
  next : BPtr
  put : BPtr
  from_ : BPtr
  have_ : UInt32
  left : UInt32
  hold : UInt64
  bits : UInt8
  in_ : UInt32
  out : UInt32
  copy : UInt32
  here : Code
  last : Code
  len : UInt32
  code_bits : UInt32
  ret : Int32

/-- The locals at entry: every scalar is uninitialised (garbage `g`); the pointers `next`, `put`, `from` are NULL, so
an offset, copy or comparison of one before it is written faults. -/
def IL.init (g : Nat → UInt64) : IL :=
  ⟨.null, .null, .null, Junk.of (g 0), Junk.of (g 1), Junk.of (g 2), Junk.of (g 3), Junk.of (g 4), Junk.of (g 5),
    Junk.of (g 6), ⟨Junk.of (g 7), Junk.of (g 8), Junk.of (g 9)⟩, ⟨Junk.of (g 10), Junk.of (g 11), Junk.of (g 12)⟩,
    Junk.of (g 13), Junk.of (g 14), (Junk.of (g 15) : Int32)⟩

abbrev X := ExceptT Ex (StateT IL M)

/-- Why a loop of `X` ended. -/
inductive Stop where
  | go
  | brk
  | ex (e : Ex)

/-- `while (cond) body` where `body` returns `true` for `break`. -/
def xwhileBrk (cond : X Bool) (body : X Bool) : X Unit :=
  ExceptT.mk (fun l0 => do
    let r ← cwhile (σ := IL × Stop)
      (fun (l, s) => match s with
        | .go => do
          let (r, l') ← StateT.run (ExceptT.run cond) l
          pure (match r with
            | .ok b => (b, (l', Stop.go))
            | .error e => (false, (l', Stop.ex e)))
        | s => pure (false, (l, s)))
      (fun (l, _) => do
        let (r, l') ← StateT.run (ExceptT.run body) l
        pure (match r with
          | .ok b => (l', if b then Stop.brk else Stop.go)
          | .error e => (l', Stop.ex e)))
      (l0, Stop.go)
    let (l, s) := r
    pure (match s with
      | .ex e => (Except.error e, l)
      | _ => (Except.ok (), l)))

def xwhile (cond : X Bool) (body : X Unit) : X Unit := xwhileBrk cond (do body; pure false)
def xloopBrk (body : X Bool) : X Unit := xwhileBrk (pure true) body

/-- What the modes share. -/
structure Ctx where
  strm : StreamPtr
  st : StatePtr
  flush : Int32

/-- `LOAD()` -/
def LOAD (c : Ctx) : X Unit := do
  let z ← ldStream c.strm
  let s ← ldState c.st
  modify fun l => { l with put := z.next_out, left := z.avail_out, next := z.next_in, have_ := z.avail_in, hold := s.hold, bits := s.bits.toUInt8 }

/-- `RESTORE()` -/
def RESTORE (c : Ctx) : X Unit := do
  let l ← get
  wrZ c.strm fun z => { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }
  wrS c.st fun s => { s with hold := l.hold, bits := l.bits.toUInt32 }

/-- `INITBITS()` -/
def INITBITS : X Unit := modify fun l => { l with hold := 0, bits := 0 }

/-- `PULLBYTE()` -/
def PULLBYTE : X Unit := do
  let l ← get
  if l.have_ == 0 then throw Ex.leave
  let b ← load8 l.next
  let nx ← l.next.add 1
  let sh ← shl64 b.toUInt64 l.bits.toUInt32
  set { l with have_ := l.have_ - 1, next := nx, hold := l.hold + sh, bits := l.bits + 8 }

/-- `NEEDBITS(n)`: `while (bits < (bits_t)u) PULLBYTE();` -/
def NEEDBITS (n : UInt32) : X Unit :=
  xwhile (do return (← get).bits < n.toUInt8) PULLBYTE

/-- `BITS(n)`: `(hold & ((1U << (unsigned)(n)) - 1))` -/
def BITS (n : UInt32) : X UInt64 := do
  let m ← shl32 1 n
  return (← get).hold &&& (m - 1).toUInt64

/-- `DROPBITS(n)` -/
def DROPBITS (n : UInt32) : X Unit := do
  let l ← get
  let h ← shr64 l.hold n
  set { l with hold := h, bits := l.bits - n.toUInt8 }

/-- `BYTEBITS()` -/
def BYTEBITS : X Unit := do
  let l ← get
  let h ← shr64 l.hold (l.bits &&& 7).toUInt32
  set { l with hold := h, bits := l.bits - (l.bits &&& 7) }

/-- `SET_BAD(errmsg)` -/
def SET_BAD (c : Ctx) (msg : String) : M Unit := do
  wrS c.st fun s => { s with mode := BAD }
  let p ← strLitRef msg
  wrZ c.strm fun z => { z with msg := p }

/-- `CRC_DO1_B(c, b)`: `c = crc_table[(c ^ (b)) & 0xff] ^ (c >> 8)` -/
def CRC_DO1_B (c : UInt32) (b : UInt64) : M UInt32 := do
  let t ← ZlibNg.Crc32P.crcTab ((c.toUInt64 ^^^ b) &&& 0xff)
  return t ^^^ (c >>> 8)

/-- `CRC2(state->check, hold)` -/
def CRC2 (c : Ctx) : X Unit := do
  let word := (← get).hold
  let crc := ~~~(← rdS c.st (·.check)).toUInt32
  let crc ← CRC_DO1_B crc word
  let crc ← CRC_DO1_B crc (word >>> 8)
  wrS c.st fun s => { s with check := (~~~crc).toUInt64 }

/-- `CRC4(state->check, hold)` -/
def CRC4 (c : Ctx) : X Unit := do
  let word := (← get).hold
  let crc := ~~~(← rdS c.st (·.check)).toUInt32
  let crc ← CRC_DO1_B crc word
  let crc ← CRC_DO1_B crc (word >>> 8)
  let crc ← CRC_DO1_B crc (word >>> 16)
  let crc ← CRC_DO1_B crc (word >>> 24)
  wrS c.st fun s => { s with check := (~~~crc).toUInt64 }

/-- `ZSWAP32(q)`: byte swap of a 32-bit value. -/
def ZSWAP32 (q : UInt32) : UInt32 :=
  ((q >>> 24) &&& (0xff : UInt32)) + ((q >>> 8) &&& (0xff00 : UInt32)) + ((q &&& (0xff00 : UInt32)) <<< 8) +
    ((q &&& (0xff : UInt32)) <<< 24)

/-- `(state->flags & 0x0200) && (state->wrap & 4)` -/
def hcrcOn (st : StatePtr) : M Bool := do
  let s ← ldState st
  return (s.flags &&& 0x0200) != 0 && (s.wrap &&& 4) != 0

def setMode (st : StatePtr) (m : UInt32) : M Unit := wrS st fun s => { s with mode := m }

/-- `state->head` (`NULL` or a header) -/
def headOf (st : StatePtr) : M HeaderPtr := do (← rdS st (·.head)).get

/-- `static const uint16_t order[19]` -/
def order : Array UInt16 := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-! ### The modes, last first (a fall-through is a tail call) -/

def inflate_DONE (_c : Ctx) : X Unit := do
  modify fun l => { l with ret := Z_STREAM_END }
  throw Ex.leave

def inflate_LENGTH (c : Ctx) : X Unit := do
  let s ← ldState c.st
  if s.wrap != 0 && s.flags != 0 then
    NEEDBITS 32
    let s ← ldState c.st
    if (s.wrap &&& 4) != 0 && (← get).hold != (s.total &&& 0xffffffff) then
      SET_BAD c "incorrect length check"
      return
    INITBITS
  setMode c.st DONE
  inflate_DONE c

def inflate_CHECK (c : Ctx) : X Unit := do
  if (← rdS c.st (·.wrap)) != 0 then
    NEEDBITS 32
    let l ← get
    let out := l.out - l.left
    modify fun l => { l with out := out }
    wrZ c.strm fun z => { z with total_out := z.total_out + out.toUInt64 }
    wrS c.st fun s => { s with total := s.total + out.toUInt64 }
    if ((← rdS c.st (·.wrap)) &&& 4) != 0 then
      if out != 0 then
        inf_chksum c.strm (← l.put.add (-(Int.ofNat out.toNat))) out
    modify fun l => { l with out := l.left }
    let s ← ldState c.st
    let l ← get
    let v : UInt64 := if s.flags != 0 then l.hold else (ZSWAP32 l.hold.toUInt32).toUInt64
    if (s.wrap &&& 4) != 0 && v != s.check then
      SET_BAD c "incorrect data check"
      return
    INITBITS
  setMode c.st LENGTH
  inflate_LENGTH c

def inflate_LIT (c : Ctx) : X Unit := do
  let l ← get
  if l.left == 0 then throw Ex.leave
  let len ← rdS c.st (·.length)
  Ptr.store l.put len.toUInt8
  let put ← l.put.add 1
  modify fun l => { l with put := put, left := l.left - 1 }
  setMode c.st LEN

def inflate_MATCH (c : Ctx) : X Unit := do
  let l ← get
  if l.left == 0 then throw Ex.leave
  let mut copy := l.out - l.left
  let s ← ldState c.st
  if s.offset > copy then
    copy := s.offset - copy
    if copy > s.whave then
      SET_BAD c "invalid distance too far back"
      return
    let window ← s.window.get
    let mut from_ := window
    if copy > s.wnext then
      copy := copy - s.wnext
      from_ ← window.add (Int.ofNat (s.wsize - copy).toNat)
    else
      from_ ← window.add (Int.ofNat (s.wnext - copy).toNat)
    copy := if copy > s.length then s.length else copy
    copy := if copy > l.left then l.left else copy
    Ptr.memcpy l.put from_ copy.toNat
    let put ← l.put.add (Int.ofNat copy.toNat)
    modify fun l => { l with put := put, from_ := from_, copy := copy }
  else
    copy := if s.length > l.left then l.left else s.length
    let src ← l.put.add (-(Int.ofNat s.offset.toNat))
    let put ← ZlibNg.ChunksetC.chunkmemset_safe_c l.put src copy.toUInt64 l.left.toUInt64
    modify fun l => { l with put := put, copy := copy }
  modify fun l => { l with left := l.left - copy }
  wrS c.st fun s => { s with length := s.length - copy }
  if (← rdS c.st (·.length)) == 0 then setMode c.st LEN

def inflate_DISTEXT (c : Ctx) : X Unit := do
  let ex ← rdS c.st (·.extra)
  if ex != 0 then
    NEEDBITS ex
    let b ← BITS ex
    wrS c.st fun s => { s with offset := s.offset + b.toUInt32 }
    DROPBITS ex
    wrS c.st fun s => { s with back := s.back + ex.toInt32 }
  setMode c.st MATCH
  inflate_MATCH c

/-- The two-level lookup loop of `LEN` / `DIST` (`for (;;) { here = tab[...]; if (...) break; PULLBYTE(); }`)
followed by the second-level lookup. -/
def decodeSym (c : Ctx) (tab : CodePtr) (nbits : UInt32) (first : Code → Bool) : X Unit := do
  xloopBrk (do
    let b ← BITS nbits
    let here : Code ← Ptr.index tab (Int.ofNat b.toNat)
    modify fun l => { l with here := here }
    if CODE_BITS here <= (← get).bits.toUInt32 then return true
    PULLBYTE
    return false)
  let here := (← get).here
  if first here then
    let last := here
    let last_bits := CODE_BITS last
    modify fun l => { l with last := last }
    xloopBrk (do
      let b ← BITS (last_bits + (last.op &&& 15).toUInt32)
      let idx := last.val.toUInt64 + (b >>> last_bits.toUInt64)
      let here : Code ← Ptr.index tab (Int.ofNat idx.toNat)
      modify fun l => { l with here := here }
      if last_bits + CODE_BITS here <= (← get).bits.toUInt32 then return true
      PULLBYTE
      return false)
    DROPBITS last_bits
    wrS c.st fun s => { s with back := s.back + last_bits.toInt32 }

def inflate_DIST (c : Ctx) : X Unit := do
  let dc ← (← rdS c.st (·.distcode)).get
  let db ← rdS c.st (·.distbits)
  decodeSym c dc db (fun h => (h.op &&& 0xf0) == 0)
  let here := (← get).here
  let code_bits := CODE_BITS here
  modify fun l => { l with code_bits := code_bits }
  DROPBITS code_bits
  wrS c.st fun s => { s with back := s.back + code_bits.toInt32 }
  if (here.op &&& 64) != 0 then
    SET_BAD c "invalid distance code"
    return
  wrS c.st fun s => { s with offset := here.val.toUInt32 }
  wrS c.st fun s => { s with extra := CODE_EXTRA here }
  setMode c.st DISTEXT
  inflate_DISTEXT c

def inflate_LENEXT (c : Ctx) : X Unit := do
  let ex ← rdS c.st (·.extra)
  if ex != 0 then
    NEEDBITS ex
    let b ← BITS ex
    wrS c.st fun s => { s with length := s.length + b.toUInt32 }
    DROPBITS ex
    wrS c.st fun s => { s with back := s.back + ex.toInt32 }
  wrS c.st fun s => { s with was := s.length }
  setMode c.st DIST
  inflate_DIST c

def inflate_LEN (c : Ctx) : X Unit := do
  let l ← get
  if l.have_ >= INFLATE_FAST_MIN_HAVE && l.left >= INFLATE_FAST_MIN_SAFE && l.bits < 8 then
    RESTORE c
    if l.left >= INFLATE_FAST_MIN_LEFT then
      ZlibNg.ChunksetC.inflate_fast_c c.strm l.out
    else
      ZlibNg.ChunksetC.inflate_fast_safe_c c.strm l.out
    LOAD c
    if (← rdS c.st (·.mode)) == TYPE then
      wrS c.st fun s => { s with back := -1 }
    return
  wrS c.st fun s => { s with back := 0 }
  let lc ← (← rdS c.st (·.lencode)).get
  let lb ← rdS c.st (·.lenbits)
  decodeSym c lc lb (fun h => h.op != 0 && (h.op &&& 0xf0) == 0)
  let here := (← get).here
  let code_bits := CODE_BITS here
  modify fun l => { l with code_bits := code_bits }
  DROPBITS code_bits
  wrS c.st fun s => { s with back := s.back + code_bits.toInt32 }
  wrS c.st fun s => { s with length := here.val.toUInt32 }
  if here.op.toNat == 0 then
    setMode c.st LIT
    return
  if (here.op &&& 32) != 0 then
    wrS c.st fun s => { s with back := -1 }
    setMode c.st TYPE
    return
  if (here.op &&& 64) != 0 then
    SET_BAD c "invalid literal/length code"
    return
  wrS c.st fun s => { s with extra := CODE_EXTRA here }
  setMode c.st LENEXT
  inflate_LENEXT c

def inflate_LEN_ (c : Ctx) : X Unit := do
  setMode c.st LEN
  inflate_LEN c

def inflate_CODELENS (c : Ctx) : X Unit := do
  xwhileBrk (do
      let s ← ldState c.st
      return s.«have» < s.nlen + s.ndist)
    (do
      let lc ← (← rdS c.st (·.lencode)).get
      let lb ← rdS c.st (·.lenbits)
      xloopBrk (do
        let b ← BITS lb
        let here : Code ← Ptr.index lc (Int.ofNat b.toNat)
        modify fun l => { l with here := here }
        if here.bits <= (← get).bits then return true
        PULLBYTE
        return false)
      let here := (← get).here
      let lens ← lensP c.st
      if here.val < 16 then
        DROPBITS here.bits.toUInt32
        let hv ← rdS c.st (·.«have»)
        wrS c.st fun s => { s with «have» := s.«have» + 1 }
        Ptr.store (← lens.add (Int.ofNat hv.toNat)) here.val
        return false
      else
        if here.val == 16 then
          NEEDBITS (here.bits.toUInt32 + 2)
          DROPBITS here.bits.toUInt32
          let hv ← rdS c.st (·.«have»)
          if hv == 0 then
            SET_BAD c "invalid bit length repeat"
            return true
          let len ← Ptr.index lens (Int.ofNat (hv - 1).toNat)
          modify fun l => { l with len := len.toUInt32 }
          let b ← BITS 2
          modify fun l => { l with copy := 3 + b.toUInt32 }
          DROPBITS 2
        else if here.val == 17 then
          NEEDBITS (here.bits.toUInt32 + 3)
          DROPBITS here.bits.toUInt32
          modify fun l => { l with len := 0 }
          let b ← BITS 3
          modify fun l => { l with copy := 3 + b.toUInt32 }
          DROPBITS 3
        else
          NEEDBITS (here.bits.toUInt32 + 7)
          DROPBITS here.bits.toUInt32
          modify fun l => { l with len := 0 }
          let b ← BITS 7
          modify fun l => { l with copy := 11 + b.toUInt32 }
          DROPBITS 7
        let s ← ldState c.st
        if s.«have» + (← get).copy > s.nlen + s.ndist then
          SET_BAD c "invalid bit length repeat"
          return true
        xwhile (do return (← get).copy != 0) (do
          modify fun l => { l with copy := l.copy - 1 }
          let hv ← rdS c.st (·.«have»)
          wrS c.st fun s => { s with «have» := s.«have» + 1 }
          Ptr.store (← lens.add (Int.ofNat hv.toNat)) (← get).len.toUInt16)
        return false)
  if (← rdS c.st (·.mode)) == BAD then return
  let lens ← lensP c.st
  if (← Ptr.index lens 256) == (0 : UInt16) then
    SET_BAD c "invalid code -- missing end-of-block"
    return
  let codes ← codesP c.st
  wrS c.st fun s => { s with next := .val codes }
  wrS c.st fun s => { s with lencode := .val codes }
  wrS c.st fun s => { s with lenbits := MAX_LEN_ROOT_BITS }
  let s ← ldState c.st
  let (ret, nx, lb) ← ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.LENS lens s.nlen (← s.next.get) s.lenbits
    (← workP c.st)
  wrS c.st fun s => { s with next := .val nx, lenbits := lb }
  modify fun l => { l with ret := ret }
  if ret != 0 then
    SET_BAD c "invalid literal/lengths set"
    return
  let nx ← (← rdS c.st (·.next)).get
  wrS c.st fun s => { s with distcode := .val nx }
  wrS c.st fun s => { s with distbits := 9 }
  let s ← ldState c.st
  let (ret, nx, db) ← ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.DISTS (← lens.add (Int.ofNat s.nlen.toNat))
    s.ndist (← s.next.get) s.distbits (← workP c.st)
  wrS c.st fun s => { s with next := .val nx, distbits := db }
  modify fun l => { l with ret := ret }
  if ret != 0 then
    SET_BAD c "invalid distances set"
    return
  setMode c.st LEN_
  if c.flush == Z_TREES then throw Ex.leave
  inflate_LEN_ c

def inflate_LENLENS (c : Ctx) : X Unit := do
  let lens ← lensP c.st
  xwhile (do let s ← ldState c.st; return s.«have» < s.ncode) (do
    NEEDBITS 3
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
  wrS c.st fun s => { s with distcode := .val codes }
  wrS c.st fun s => { s with lencode := .val codes }
  wrS c.st fun s => { s with lenbits := 7 }
  let s ← ldState c.st
  let (ret, nx, lb) ← ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.CODES lens 19 (← s.next.get) s.lenbits
    (← workP c.st)
  wrS c.st fun s => { s with next := .val nx, lenbits := lb }
  modify fun l => { l with ret := ret }
  if ret != 0 then
    SET_BAD c "invalid code lengths set"
    return
  wrS c.st fun s => { s with «have» := 0 }
  setMode c.st CODELENS
  inflate_CODELENS c

def inflate_TABLE (c : Ctx) : X Unit := do
  NEEDBITS 14
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
    SET_BAD c "too many length or distance symbols"
    return
  wrS c.st fun s => { s with «have» := 0 }
  setMode c.st LENLENS
  inflate_LENLENS c

def inflate_COPY (c : Ctx) : X Unit := do
  let mut copy ← rdS c.st (·.length)
  if copy != 0 then
    let l ← get
    copy := if copy > l.have_ then l.have_ else copy
    copy := if copy > l.left then l.left else copy
    modify fun l => { l with copy := copy }
    if copy == 0 then throw Ex.leave
    Ptr.memcpy l.put l.next copy.toNat
    let nx ← l.next.add (Int.ofNat copy.toNat)
    let pt ← l.put.add (Int.ofNat copy.toNat)
    modify fun l => { l with have_ := l.have_ - copy, next := nx, left := l.left - copy, put := pt }
    wrS c.st fun s => { s with length := s.length - copy }
    return
  modify fun l => { l with copy := copy }
  setMode c.st TYPE

def inflate_COPY_ (c : Ctx) : X Unit := do
  setMode c.st COPY
  inflate_COPY c

def inflate_STORED (c : Ctx) : X Unit := do
  BYTEBITS
  NEEDBITS 32
  let hold := (← get).hold
  if (hold &&& (0xffff : UInt64)) != ((hold >>> 16) ^^^ (0xffff : UInt64)) then
    SET_BAD c "invalid stored block lengths"
    return
  wrS c.st fun s => { s with length := hold.toUInt16.toUInt32 }
  INITBITS
  setMode c.st COPY_
  if c.flush == Z_TREES then throw Ex.leave
  inflate_COPY_ c

def inflate_TYPEDO (c : Ctx) : X Unit := do
  if (← rdS c.st (·.last)) != 0 then
    BYTEBITS
    setMode c.st CHECK
    return
  NEEDBITS 3
  let b ← BITS 1
  wrS c.st fun s => { s with last := b.toUInt32.toInt32 }
  DROPBITS 1
  let t ← BITS 2
  if t == 0 then
    setMode c.st STORED
  else if t == 1 then
    fixedtables c.st
    setMode c.st LEN_
    if c.flush == Z_TREES then
      DROPBITS 2
      throw Ex.leave
  else if t == 2 then
    setMode c.st TABLE
  else
    SET_BAD c "invalid block type"
  DROPBITS 2

def inflate_TYPE (c : Ctx) : X Unit := do
  if c.flush == Z_BLOCK || c.flush == Z_TREES then throw Ex.leave
  inflate_TYPEDO c

def inflate_DICT (c : Ctx) : X Unit := do
  if (← rdS c.st (·.havedict)) == 0 then
    RESTORE c
    throw (Ex.ret Z_NEED_DICT)
  wrS c.st fun s => { s with check := ADLER32_INITIAL_VALUE }
  wrZ c.strm fun z => { z with adler := ADLER32_INITIAL_VALUE }
  setMode c.st TYPE
  inflate_TYPE c

def inflate_DICTID (c : Ctx) : X Unit := do
  NEEDBITS 32
  let v := (ZSWAP32 (← get).hold.toUInt32).toUInt64
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  INITBITS
  setMode c.st DICT
  inflate_DICT c

def inflate_HCRC (c : Ctx) : X Unit := do
  let s ← ldState c.st
  if (s.flags &&& 0x0200) != 0 then
    NEEDBITS 16
    let s ← ldState c.st
    if (s.wrap &&& 4) != 0 && (← get).hold != (s.check &&& 0xffff) then
      SET_BAD c "header crc mismatch"
      return
    INITBITS
  let hd ← headOf c.st
  if hd != none then
    let s ← ldState c.st
    let g ← ldHeader hd
    stHeader hd { g with hcrc := (s.flags >>> 9) &&& 1 }
    let g ← ldHeader hd
    stHeader hd { g with done := 1 }
  let s ← ldState c.st
  if (s.wrap &&& 4) != 0 && s.flags != 0 then
    wrS c.st fun s => { s with check := CRC32_INITIAL_VALUE }
    wrZ c.strm fun z => { z with adler := CRC32_INITIAL_VALUE }
  setMode c.st TYPE

/-- The `do { ... } while (len && copy < have)` loop of `NAME` and `COMMENT`, storing into `field` of the header
when it is not NULL and `state->length < max`. -/
def headerString (c : Ctx) (field : GzHeader → BPtr) (maxOf : GzHeader → UInt32) : X Unit := do
  modify fun l => { l with copy := 0 }
  let body : X Unit := do
    let l ← get
    let b ← index8 l.next (Int.ofNat l.copy.toNat)
    modify fun l => { l with copy := l.copy + 1, len := b.toUInt32 }
    let hd ← headOf c.st
    if hd != none then
      let g ← ldHeader hd
      if field g != .null then
        let s ← ldState c.st
        if s.length < maxOf g then
          wrS c.st fun s => { s with length := s.length + 1 }
          Ptr.store (← (field g).add (Int.ofNat s.length.toNat)) (← get).len.toUInt8
  body
  xwhile (do let l ← get; return l.len != 0 && l.copy < l.have_) body

def inflate_COMMENT (c : Ctx) : X Unit := do
  let s ← ldState c.st
  if (s.flags &&& 0x1000) != 0 then
    if (← get).have_ == 0 then throw Ex.leave
    headerString c (·.comment) (·.comm_max)
    if ← hcrcOn c.st then
      let l ← get
      let v ← ZlibNg.Crc32.crc32_small (← rdS c.st (·.check)).toUInt32 l.next l.copy.toUInt64
      wrS c.st fun s => { s with check := v.toUInt64 }
    let l ← get
    let nx ← l.next.add (Int.ofNat l.copy.toNat)
    modify fun l => { l with have_ := l.have_ - l.copy, next := nx }
    if (← get).len != 0 then throw Ex.leave
  else
    let hd ← headOf c.st
    if hd != none then
      let g ← ldHeader hd
      stHeader hd { g with comment := .null }
  setMode c.st HCRC
  inflate_HCRC c

def inflate_NAME (c : Ctx) : X Unit := do
  let s ← ldState c.st
  if (s.flags &&& 0x0800) != 0 then
    if (← get).have_ == 0 then throw Ex.leave
    headerString c (·.name) (·.name_max)
    if ← hcrcOn c.st then
      let l ← get
      let v ← ZlibNg.Crc32.crc32_small (← rdS c.st (·.check)).toUInt32 l.next l.copy.toUInt64
      wrS c.st fun s => { s with check := v.toUInt64 }
    let l ← get
    let nx ← l.next.add (Int.ofNat l.copy.toNat)
    modify fun l => { l with have_ := l.have_ - l.copy, next := nx }
    if (← get).len != 0 then throw Ex.leave
  else
    let hd ← headOf c.st
    if hd != none then
      let g ← ldHeader hd
      stHeader hd { g with name := .null }
  wrS c.st fun s => { s with length := 0 }
  setMode c.st COMMENT
  inflate_COMMENT c

def inflate_EXTRA (c : Ctx) : X Unit := do
  let s ← ldState c.st
  if (s.flags &&& 0x0400) != 0 then
    let l ← get
    let mut copy := s.length
    if copy > l.have_ then copy := l.have_
    modify fun l => { l with copy := copy }
    if copy != 0 then
      let hd ← headOf c.st
      if hd != none then
        let g ← ldHeader hd
        if g.extra != .null && s.length ≤ g.extra_len then
          let len := g.extra_len - s.length
          modify fun l => { l with len := len }
          if len < g.extra_max then
            let n := if copy > g.extra_max - len then g.extra_max - len else copy
            Ptr.memcpy (← g.extra.add (Int.ofNat len.toNat)) l.next n.toNat
      if ← hcrcOn c.st then
        let v ← ZlibNg.Crc32.crc32_small (← rdS c.st (·.check)).toUInt32 l.next copy.toUInt64
        wrS c.st fun s => { s with check := v.toUInt64 }
      let nx ← l.next.add (Int.ofNat copy.toNat)
      modify fun l => { l with have_ := l.have_ - copy, next := nx }
      wrS c.st fun s => { s with length := s.length - copy }
    if (← rdS c.st (·.length)) != 0 then throw Ex.leave
  wrS c.st fun s => { s with length := 0 }
  setMode c.st NAME
  inflate_NAME c

def inflate_EXLEN (c : Ctx) : X Unit := do
  let s ← ldState c.st
  if (s.flags &&& 0x0400) != 0 then
    NEEDBITS 16
    let hold := (← get).hold
    wrS c.st fun s => { s with length := hold.toUInt16.toUInt32 }
    let hd ← headOf c.st
    if hd != none then
      let g ← ldHeader hd
      stHeader hd { g with extra_len := hold.toUInt16.toUInt32 }
    if ← hcrcOn c.st then CRC2 c
    INITBITS
  else
    let hd ← headOf c.st
    if hd != none then
      let g ← ldHeader hd
      stHeader hd { g with extra := .null }
  setMode c.st EXTRA
  inflate_EXTRA c

def inflate_OS (c : Ctx) : X Unit := do
  NEEDBITS 16
  let hold := (← get).hold
  let hd ← headOf c.st
  if hd != none then
    let g ← ldHeader hd
    stHeader hd { g with xflags := (hold &&& 0xff).toUInt32.toInt32 }
    let g ← ldHeader hd
    stHeader hd { g with os := (hold >>> 8).toUInt32.toInt32 }
  if ← hcrcOn c.st then CRC2 c
  INITBITS
  setMode c.st EXLEN
  inflate_EXLEN c

def inflate_TIME (c : Ctx) : X Unit := do
  NEEDBITS 32
  let hold := (← get).hold
  let hd ← headOf c.st
  if hd != none then
    let g ← ldHeader hd
    stHeader hd { g with time := hold.toUInt32.toUInt64 }
  if ← hcrcOn c.st then CRC4 c
  INITBITS
  setMode c.st OS
  inflate_OS c

def inflate_FLAGS (c : Ctx) : X Unit := do
  NEEDBITS 16
  let hold := (← get).hold
  wrS c.st fun s => { s with flags := hold.toUInt32.toInt32 }
  let s ← ldState c.st
  if ((s.flags &&& 0xff).toInt64.toUInt64) != Z_DEFLATED then
    SET_BAD c "unknown compression method"
    return
  if (s.flags &&& 0xe000) != 0 then
    SET_BAD c "unknown header flags set"
    return
  let hd ← headOf c.st
  if hd != none then
    let g ← ldHeader hd
    stHeader hd { g with text := ((hold >>> 8) &&& 1).toUInt32.toInt32 }
  if ← hcrcOn c.st then CRC2 c
  INITBITS
  setMode c.st TIME
  inflate_TIME c

def inflate_HEAD (c : Ctx) : X Unit := do
  if (← rdS c.st (·.wrap)) == 0 then
    setMode c.st TYPEDO
    return
  NEEDBITS 16
  let s ← ldState c.st
  if (s.wrap &&& 2) != 0 && (← get).hold == 0x8b1f then
    if s.wbits == 0 then wrS c.st fun s => { s with wbits := MAX_WBITS.toUInt32 }
    wrS c.st fun s => { s with check := CRC32_INITIAL_VALUE }
    CRC2 c
    INITBITS
    setMode c.st FLAGS
    return
  let hd ← headOf c.st
  if hd != none then
    let g ← ldHeader hd
    stHeader hd { g with done := -1 }
  let s ← ldState c.st
  let bad ← if (s.wrap &&& 1) == 0 then pure true else do
    let b8 ← BITS 8
    pure (((b8 <<< 8) + ((← get).hold >>> 8)) % 31 != 0)
  if bad then
    SET_BAD c "incorrect header check"
    return
  if (← BITS 4) != Z_DEFLATED then
    SET_BAD c "unknown compression method"
    return
  DROPBITS 4
  let len := (← BITS 4).toUInt32 + 8
  modify fun l => { l with len := len }
  let s ← ldState c.st
  if len > MAX_WBITS.toUInt32 || (s.wbits != 0 && len > s.wbits) then
    SET_BAD c "invalid window size"
    return
  if s.wbits == 0 then wrS c.st fun s => { s with wbits := len }
  wrS c.st fun s => { s with flags := 0 }
  wrS c.st fun s => { s with check := ADLER32_INITIAL_VALUE }
  wrZ c.strm fun z => { z with adler := ADLER32_INITIAL_VALUE }
  let hold := (← get).hold
  setMode c.st (if (hold &&& 0x200) != 0 then DICTID else TYPE)
  INITBITS

/-- `case BAD:` -/
def inflate_BAD (_c : Ctx) : X Unit := do
  modify fun l => { l with ret := Z_DATA_ERROR }
  throw Ex.leave

/-- One trip of `for (;;) switch (state->mode)`. -/
def dispatch (c : Ctx) : X Unit := do
  let m ← rdS c.st (·.mode)
  if m == HEAD then inflate_HEAD c
  else if m == FLAGS then inflate_FLAGS c
  else if m == TIME then inflate_TIME c
  else if m == OS then inflate_OS c
  else if m == EXLEN then inflate_EXLEN c
  else if m == EXTRA then inflate_EXTRA c
  else if m == NAME then inflate_NAME c
  else if m == COMMENT then inflate_COMMENT c
  else if m == HCRC then inflate_HCRC c
  else if m == DICTID then inflate_DICTID c
  else if m == DICT then inflate_DICT c
  else if m == TYPE then inflate_TYPE c
  else if m == TYPEDO then inflate_TYPEDO c
  else if m == STORED then inflate_STORED c
  else if m == COPY_ then inflate_COPY_ c
  else if m == COPY then inflate_COPY c
  else if m == TABLE then inflate_TABLE c
  else if m == LENLENS then inflate_LENLENS c
  else if m == CODELENS then inflate_CODELENS c
  else if m == LEN_ then inflate_LEN_ c
  else if m == LEN then inflate_LEN c
  else if m == LENEXT then inflate_LENEXT c
  else if m == DIST then inflate_DIST c
  else if m == DISTEXT then inflate_DISTEXT c
  else if m == MATCH then inflate_MATCH c
  else if m == LIT then inflate_LIT c
  else if m == CHECK then inflate_CHECK c
  else if m == LENGTH then inflate_LENGTH c
  else if m == DONE then inflate_DONE c
  else if m == BAD then inflate_BAD c
  else throw (Ex.ret Z_STREAM_ERROR)

/-- The code after `inf_leave:` (`inflate.c:1182-1206`). -/
def infLeave (c : Ctx) : X Int32 := do
  RESTORE c
  let z ← ldStream c.strm
  let check_bytes := (← get).out - z.avail_out
  let s ← ldState c.st
  if s.wsize != 0 || ((← get).out != z.avail_out && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH)) then
    updatewindow c.strm z.next_out check_bytes (s.wrap &&& 4)
  let z ← ldStream c.strm
  modify fun l => { l with in_ := l.in_ - z.avail_in, out := l.out - z.avail_out }
  let l ← get
  wrZ c.strm fun z => { z with total_in := z.total_in + l.in_.toUInt64 }
  wrZ c.strm fun z => { z with total_out := z.total_out + l.out.toUInt64 }
  wrS c.st fun s => { s with total := s.total + l.out.toUInt64 }
  let s ← ldState c.st
  let dt : Int := (s.bits.toNat : Int) + (if s.last != 0 then 64 else 0) + (if s.mode == TYPE then 128 else 0) +
    (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0)
  wrZ c.strm fun z => { z with data_type := Int32.ofInt dt }
  if ((l.in_ == 0 && l.out == 0) || c.flush == Z_FINISH) && l.ret == Z_OK then
    let s ← ldState c.st
    if s.wsize == 0 && c.flush == Z_FINISH then
      inf_chksum c.strm (← l.put.add (-(Int.ofNat check_bytes.toNat))) check_bytes
    modify fun l => { l with ret := Z_BUF_ERROR }
  return (← get).ret

/-- `int32_t Z_EXPORT inflate(PREFIX3(stream) *strm, int32_t flush)` (`inflate.c:461-1207`). -/
def inflate (strm : StreamPtr) (flush : Int32) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let z ← ldStream strm
  if z.next_out == .null || (z.next_in == .null && z.avail_in != 0) then return Z_STREAM_ERROR
  let st := z.state
  if (← rdS st (·.mode)) == TYPE then setMode st TYPEDO
  let c : Ctx := ⟨strm, st, flush⟩
  let body : X Int32 := do
    LOAD c
    modify fun l => { l with in_ := l.have_, out := l.left, ret := Z_OK }
    let r ← tryCatch (do xloopBrk (do dispatch c; return false); return none)
      (fun e => match e with
        | .leave => pure none
        | .ret v => pure (some v))
    match r with
    | some v => return v
    | none => infLeave c
  let g ← uninitLocals 0
  let (r, _) ← StateT.run (ExceptT.run body) (IL.init g)
  match r with
  | .ok v => return v
  | .error (.ret v) => return v
  | .error .leave => ub "unreachable: inf_leave outside inflate"

/-! ## The other entry points -/

/-- `int32_t Z_EXPORT inflateEnd(PREFIX3(stream) *strm)` (`inflate.c:1209-1218`). -/
def inflateEnd (strm : StreamPtr) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  free_inflate strm
  return Z_OK

/-- `int32_t Z_EXPORT inflateGetDictionary(PREFIX3(stream) *strm, uint8_t *dictionary, uint32_t *dictLength)`
(`inflate.c:1220-1239`). `dictLength` is returned (`none` for a NULL pointer: nothing is written). -/
def inflateGetDictionary (strm : StreamPtr) (dictionary : BPtr) (hasLen : Bool) : M (Int32 × Option UInt32) := do
  if ← inflateStateCheck strm then return (Z_STREAM_ERROR, none)
  let st ← stateOf strm
  let s ← ldState st
  if s.whave != 0 && dictionary != .null then
    let w ← s.window.get
    Ptr.memcpy dictionary (← w.add (Int.ofNat s.wnext.toNat)) (s.whave - s.wnext).toNat
    Ptr.memcpy (← dictionary.add (Int.ofNat (s.whave - s.wnext).toNat)) w s.wnext.toNat
  return (Z_OK, if hasLen then some s.whave else none)

/-- `int32_t Z_EXPORT inflateSetDictionary(PREFIX3(stream) *strm, const uint8_t *dictionary, uint32_t dictLength)`
(`inflate.c:1241-1270`, with patch 0006). -/
def inflateSetDictionary (strm : StreamPtr) (dictionary : BPtr) (dictLength : UInt32) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let st ← stateOf strm
  if dictionary == .null then return Z_STREAM_ERROR
  let s ← ldState st
  if s.wrap != 0 && s.mode != DICT then return Z_STREAM_ERROR
  if s.mode == DICT then
    let dictid ← ZlibNg.Adler32C.adler32_c ADLER32_INITIAL_VALUE.toUInt32 dictionary dictLength.toUInt64
    if dictid.toUInt64 != s.check then return Z_DATA_ERROR
  updatewindow strm (← dictionary.add (Int.ofNat dictLength.toNat)) dictLength 0
  wrS st fun s => { s with havedict := 1 }
  return Z_OK

/-- `int32_t Z_EXPORT inflateGetHeader(PREFIX3(stream) *strm, PREFIX(gz_headerp) head)` (`inflate.c:1272-1285`). -/
def inflateGetHeader (strm : StreamPtr) (head : HeaderPtr) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let st ← stateOf strm
  if ((← rdS st (·.wrap)) &&& 2) == 0 then return Z_STREAM_ERROR
  wrS st fun s => { s with head := .val head }
  let g ← ldHeader head
  stHeader head { g with done := 0 }
  return Z_OK

/-- `static uint32_t syncsearch(uint32_t *have, const unsigned char *buf, uint32_t len)` (`inflate.c:1298-1314`).
Returns `(*have, result)`. -/
def syncsearch (have_ : UInt32) (buf : BPtr) (len : UInt32) : M (UInt32 × UInt32) := do
  let (got, next) ← cwhile
    (fun ((got, next) : UInt32 × UInt32) => pure (next < len && got < 4, (got, next)))
    (fun ((got, next) : UInt32 × UInt32) => do
      let b ← index8 buf (Int.ofNat next.toNat)
      let want : UInt32 := if got < 2 then 0 else 0xff
      let got := if b.toUInt32 == want then got + 1 else if b != 0 then 0 else 4 - got
      pure (got, next + 1))
    (have_, 0)
  return (got, next)

/-- `int32_t Z_EXPORT inflateSync(PREFIX3(stream) *strm)` (`inflate.c:1316-1366`, with patch 0005). The local
`unsigned char buf[4]` is a Lean array; `syncsearch` over it reads its first `len` bytes. -/
def inflateSync (strm : StreamPtr) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let st ← stateOf strm
  let z ← ldStream strm
  let s ← ldState st
  if z.avail_in == 0 && s.bits < 8 then return Z_BUF_ERROR
  if s.mode != SYNC then
    setMode st SYNC
    let s ← ldState st
    let hold ← shr64 s.hold (s.bits &&& 7)
    wrS st fun s => { s with hold := hold, bits := s.bits - (s.bits &&& 7) }
    let (buf, _) ← cwhile
      (fun ((buf, _) : Array UInt8 × Unit) => do pure ((← rdS st (·.bits)) >= 8, (buf, ())))
      (fun ((buf, _) : Array UInt8 × Unit) => do
        let s ← ldState st
        let buf := buf.push s.hold.toUInt8
        let hold ← shr64 s.hold 8
        wrS st fun s => { s with hold := hold, bits := s.bits - 8 }
        pure (buf, ()))
      (#[], ())
    if buf.size > 4 then ub "buf[4] overflow"
    wrS st fun s => { s with «have» := 0 }
    -- syncsearch(&(state->have), buf, len)
    let mut got : UInt32 := 0
    for b in buf do
      if got < 4 then
        let want : UInt32 := if got < 2 then 0 else 0xff
        got := if b.toUInt32 == want then got + 1 else if b != 0 then 0 else 4 - got
    wrS st fun s => { s with «have» := got }
  let z ← ldStream strm
  let (hv, len) ← syncsearch (← rdS st (·.«have»)) z.next_in z.avail_in
  wrS st fun s => { s with «have» := hv }
  wrZ strm fun z => { z with avail_in := z.avail_in - len }
  if len != 0 then
    let nx ← z.next_in.add (Int.ofNat len.toNat)
    wrZ strm fun z => { z with next_in := nx }
  wrZ strm fun z => { z with total_in := z.total_in + len.toUInt64 }
  if (← rdS st (·.«have»)) != 4 then return Z_DATA_ERROR
  if (← rdS st (·.flags)) == -1 then
    wrS st fun s => { s with wrap := 0 }
  else
    wrS st fun s => { s with wrap := s.wrap &&& ~~~4 }
  let flags ← rdS st (·.flags)
  let z ← ldStream strm
  let in_ := z.total_in
  let out := z.total_out
  let _ ← inflateReset strm
  wrZ strm fun z => { z with total_in := in_, total_out := out }
  wrS st fun s => { s with flags := flags }
  if (← rdS st (·.wbits)) == 0 then wrS st fun s => { s with wbits := MAX_WBITS.toUInt32 }
  setMode st TYPE
  return Z_OK

/-- `int32_t Z_EXPORT inflateSyncPoint(PREFIX3(stream) *strm)` (`inflate.c:1376-1384`). -/
def inflateSyncPoint (strm : StreamPtr) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let s ← ldState (← stateOf strm)
  return if s.mode == STORED && s.bits == 0 then 1 else 0

/-- `int32_t Z_EXPORT inflateCopy(PREFIX3(stream) *dest, PREFIX3(stream) *source)` (`inflate.c:1386-1424`, with
patch 0001). -/
def inflateCopy (dest source : StreamPtr) : M Int32 := do
  if (← inflateStateCheck source) || dest == none then return Z_STREAM_ERROR
  let st ← stateOf source
  -- memcpy(dest, source, sizeof(z_stream))
  if dest == source then ub "overlapping memcpy"
  let z ← ldStream source
  let _ ← ldStream dest
  stStream dest z
  let alloc_bufs ← alloc_inflate dest
  if alloc_bufs == none then return Z_MEM_ERROR
  let copy ← (← ldAllocs alloc_bufs).state.get
  copyState copy st
  wrS copy fun s => { s with strm := .val dest }
  let s ← ldState st
  let codes ← codesP st
  let ccodes ← codesP copy
  if (← s.lencode.get) == codes then
    wrS copy fun s => { s with lencode := .val ccodes }
    let d ← Ptr.diff (← s.distcode.get) codes
    let dc ← ccodes.add d.toInt
    wrS copy fun s => { s with distcode := .val dc }
  let d ← Ptr.diff (← s.next.get) codes
  let nx ← ccodes.add d.toInt
  wrS copy fun s => { s with next := .val nx }
  let w ← (← ldAllocs alloc_bufs).window.get
  wrS copy fun s => { s with window := .val w }
  wrS copy fun s => { s with alloc_bufs := .val alloc_bufs }
  Ptr.memcpy w (← s.window.get) s.wsize.toNat
  wrZ dest fun z => { z with state := copy }
  return Z_OK

/-- `int32_t Z_EXPORT inflateUndermine(PREFIX3(stream) *strm, int32_t subvert)` (`inflate.c:1426-1440`). -/
def inflateUndermine (_strm : StreamPtr) (_subvert : Int32) : M Int32 := pure Z_DATA_ERROR

/-- `int32_t Z_EXPORT inflateValidate(PREFIX3(stream) *strm, int32_t check)` (`inflate.c:1442-1454`). -/
def inflateValidate (strm : StreamPtr) (check : Int32) : M Int32 := do
  if ← inflateStateCheck strm then return Z_STREAM_ERROR
  let st ← stateOf strm
  if check != 0 && (← rdS st (·.wrap)) != 0 then
    wrS st fun s => { s with wrap := s.wrap ||| 4 }
  else
    wrS st fun s => { s with wrap := s.wrap &&& ~~~4 }
  return Z_OK

/-- `long Z_EXPORT inflateMark(PREFIX3(stream) *strm)` (`inflate.c:1456-1465`). -/
def inflateMark (strm : StreamPtr) : M Int64 := do
  if ← inflateStateCheck strm then return -65536
  let s ← ldState (← stateOf strm)
  let hi : UInt64 := s.back.toInt64.toUInt64 <<< 16
  let lo : UInt64 :=
    if s.mode == COPY then s.length.toUInt64
    else if s.mode == MATCH then (s.was - s.length).toUInt64 else 0
  return (hi + lo).toInt64

/-- `unsigned long Z_EXPORT inflateCodesUsed(PREFIX3(stream) *strm)` (`inflate.c:1467-1472`). -/
def inflateCodesUsed (strm : StreamPtr) : M UInt64 := do
  if strm == none then return (-1 : Int64).toUInt64
  let z ← ldStream strm
  if z.state == none then return (-1 : Int64).toUInt64
  let s ← ldState z.state
  let d ← Ptr.diff (← s.next.get) (← codesP z.state)
  return d.toUInt64

end ZlibNg.Inflate
