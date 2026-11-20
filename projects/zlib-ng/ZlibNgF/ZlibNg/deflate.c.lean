import ZlibNgF.ZlibNg.«deflate.c.fill_window»
import ZlibNgF.ZlibNg.«deflate_stored.c»
import ZlibNgF.ZlibNg.«deflate_quick.c»
import ZlibNgF.ZlibNg.«deflate_fast.c»
import ZlibNgF.ZlibNg.«deflate_medium.c»
import ZlibNgF.ZlibNg.«deflate_slow.c»
import ZlibNgF.ZlibNg.«deflate_rle.c»
import ZlibNgF.ZlibNg.«deflate_huff.c»
import ZlibNgF.ZlibNg.«crc32.c»
import ZlibNgF.ZlibNg.«zutil.h»

/-!
# `deflate.c` — zlib compression, public entry points (`ZlibNgF`)

Source: `zlib-ng/deflate.c` (`ZLIB_COMPAT`, `GZIP`; no `NO_QUICK_STRATEGY`, `NO_MEDIUM_STRATEGY`,
`S390_DFLTCC_DEFLATE`, `ZLIB_DEBUG`, `DEF_ALLOC_DEBUG`: the hooks are empty, `DEFLATE_DONE` is 1,
`DEFLATE_NEED_CONSERVATIVE_BOUND` is 0, `DEFLATE_HOOK` is 0, `DEFLATE_ADJUST_WINDOW_SIZE(n)` is `n`, `PAD_WINDOW` is
`PAD_64`, `HINT_ALIGNED_WINDOW` is `HINT_ALIGNED_64`), with patch 0003 (`deflateBound`). `fill_window` and the macro
`HASHLESS` are in `deflate.c.fill_window.lean`, `flush_pending` in `deflate_p.h.lean`. The `ZLIB_COMPAT`-excluded
`zng_deflateSetParams` / `zng_deflateGetParams` are not compiled.

## Function pointers
`strm->zalloc` / `strm->zfree` are `FnPtr` (only `zcalloc` / `zcfree` are modelled). `configuration_table[i].func`
is a `CompressFn`; `s->longest_match` / `s->insert_batch` are `LongestMatchFn` / `InsertBatchFn`.
`FUNCTABLE_FPTR(longest_match_slow_roll)` = `longest_match_slow_roll_c`, `(longest_match_slow_knuth)` =
`longest_match_slow_knuth_c`; `FUNCTABLE_CALL(adler32)` = `adler32_c`.

## Caller out-cells
As in the inflate translation, a caller's scalar out-cell (`uint32_t *pending`, `int32_t *bits`, `uint32_t
*dictLength`) is a flag "the pointer is not NULL"; the value stored through it is returned.
-/

set_option autoImplicit false

namespace ZlibNg.Deflate
open C ZlibNg.Inflate ZlibNg.DeflateP ZlibNg.InsertString

/-! ## Local data -/

/-- `typedef struct config_s` (`deflate.c:100-107`). -/
structure Config where
  good_length : UInt16
  max_lazy : UInt16
  nice_length : UInt16
  max_chain : UInt16
  func : CompressFn

/-- `static const config configuration_table[10]` (`deflate.c:109-135`). -/
def configuration_table : Array Config := #[
  ⟨0, 0, 0, 0, .deflate_stored⟩,
  ⟨0, 0, 0, 0, .deflate_quick⟩,
  ⟨4, 3, 8, 4, .deflate_fast⟩,
  ⟨4, 16, 16, 6, .deflate_medium⟩,
  ⟨4, 28, 32, 24, .deflate_medium⟩,
  ⟨8, 48, 32, 32, .deflate_medium_fizzle⟩,
  ⟨8, 56, 128, 128, .deflate_medium_fizzle⟩,
  ⟨8, 32, 128, 256, .deflate_slow⟩,
  ⟨32, 128, 258, 1024, .deflate_slow⟩,
  ⟨32, 258, 258, 4096, .deflate_slow⟩]

instance : Inhabited Config := ⟨⟨0, 0, 0, 0, .deflate_stored⟩⟩

/-- `configuration_table[level]`: faults outside the array. -/
def config (level : Int32) : M Config :=
  if level < 0 then ub "read outside a static table" else tblGet configuration_table level.toNatClampNeg

/-- A call through a `compress_func` pointer. -/
def call_compress (f : CompressFn) (st : StatePtr) (flush : Int32) : M BlockState :=
  match f with
  | .deflate_stored => ZlibNg.DeflateStored.deflate_stored st flush
  | .deflate_quick => ZlibNg.DeflateQuick.deflate_quick st flush
  | .deflate_fast => ZlibNg.DeflateFast.deflate_fast st flush
  | .deflate_medium => ZlibNg.DeflateMedium.deflate_medium st flush
  | .deflate_medium_fizzle => ZlibNg.DeflateMedium.deflate_medium_fizzle st flush
  | .deflate_slow => ZlibNg.DeflateSlow.deflate_slow st flush

/-- `#define RANK(f) (((f) * 2) - ((f) > 4 ? 9 : 0))` on `int` (checked). -/
def RANK (f : Int32) : M Int32 := do
  let a ← chkI32 (f.toInt * 2)
  chkI32 (a.toInt - (if f > 4 then 9 else 0))

/-- `#define CLEAR_HASH(s)`: `memset((unsigned char *)s->head, 0, HASH_SIZE * sizeof(*s->head))`. -/
def CLEAR_HASH (st : StatePtr) : M Unit := do
  Ptr.memset (← (← ldDState st).head.get) 0 (HASH_SIZE.toNat * 2)

/-- `#define PENDING_BUF_PAD 8` -/
def PENDING_BUF_PAD : Int32 := 8
/-- `#define LIT_BUFS 4` -/
def LIT_BUFS : Int32 := 4
/-- `#define PENDING_BUF_SIZE(lit_bufsize) (((lit_bufsize) * LIT_BUFS) + 1 + PENDING_BUF_PAD)` on `int`. -/
def PENDING_BUF_SIZE (lit_bufsize : Int32) : M Int32 := do
  let a ← chkI32 (lit_bufsize.toInt * LIT_BUFS.toInt)
  chkI32 (a.toInt + 1 + PENDING_BUF_PAD.toInt)

/-- `x << n` on `int`: undefined for a negative `x` or `n`, `n >= 32`, or a result outside `int` (§6.5.7p3-4). -/
def shlI32 (x n : Int32) : M Int32 :=
  if x < 0 || n < 0 || n ≥ 32 then ub "invalid shift" else chkI32 (x.toInt * 2 ^ n.toNatClampNeg)

/-- `(char *)HINT_ALIGNED_16(p)` -/
def HINT_ALIGNED_16 (p : BPtr) : M BPtr := Ptr.castAligned p 16

/-- `ERR_RETURN(strm, err)`: `strm->msg = ERR_MSG(err)` and return `err`. -/
def ERR_RETURN (strm : StreamPtr) (err : Int32) : M Int32 := do
  let m ← ZlibNg.Zutil.zError err
  wrZ strm fun z => { z with msg := m }
  return err

/-! ## Allocation -/

/-- `Z_INTERNAL deflate_allocs* alloc_deflate(PREFIX3(stream) *strm, int windowBits, int lit_bufsize)`
(`deflate.c:194-256`). The `int` size computations are checked. -/
def alloc_deflate (strm : StreamPtr) (windowBits lit_bufsize : Int32) : M DAllocsPtr := do
  let curr_size : Int32 := 0
  let wsz ← shlI32 1 windowBits
  let w2 ← chkI32 (2 * wsz.toInt)
  let window_size : Int32 := if w2 > 32768 then w2 else 32768
  let prev_size ← chkI32 (wsz.toInt * 2)
  let head_size : Int32 := (HASH_SIZE.toUInt64 * 2).toUInt32.toInt32
  let pending_size ← PENDING_BUF_SIZE lit_bufsize
  let state_size : Int32 := SIZEOF_DEFLATE_STATE.toInt32
  let alloc_size : Int32 := SIZEOF_DEFLATE_ALLOCS.toInt32
  let window_pos := PAD_64 curr_size
  let curr_size ← chkI32 (window_pos.toInt + window_size.toInt)
  let prev_pos := PAD_64 curr_size
  let curr_size ← chkI32 (prev_pos.toInt + prev_size.toInt)
  let head_pos := PAD_64 curr_size
  let curr_size ← chkI32 (head_pos.toInt + head_size.toInt)
  let pending_pos := PAD_64 curr_size
  let curr_size ← chkI32 (pending_pos.toInt + pending_size.toInt)
  let state_pos := PAD_64 curr_size
  let curr_size ← chkI32 (state_pos.toInt + state_size.toInt)
  let alloc_pos := PAD_16 curr_size
  let curr_size ← chkI32 (alloc_pos.toInt + alloc_size.toInt)
  let total_size := PAD_64 (← chkI32 (curr_size.toInt + (WINDOW_PAD_SIZE.toInt - 1)))
  let z ← ldStream strm
  let original_buf ← callZalloc z.zalloc z.«opaque» 1 total_size.toUInt32
  if original_buf == .null then return none
  let ob ← addrOf original_buf
  let buff ← HINT_ALIGNED_64 (← original_buf.add (Int.ofNat (PADSZ ob 64).toNat))
  let alloc_bufs ← carveDAllocs (← buff.add alloc_pos.toInt)
  let a ← ldDAllocs alloc_bufs
  stDAllocs alloc_bufs { a with buf_start := .val original_buf }
  let z ← ldStream strm
  let a ← ldDAllocs alloc_bufs
  stDAllocs alloc_bufs { a with zfree := .val z.zfree }
  let w ← HINT_ALIGNED_64 (← buff.add window_pos.toInt)
  let a ← ldDAllocs alloc_bufs
  stDAllocs alloc_bufs { a with window := .val w }
  let p ← HINT_ALIGNED_64 (← buff.add prev_pos.toInt)
  let a ← ldDAllocs alloc_bufs
  stDAllocs alloc_bufs { a with prev := .val p }
  let hd ← HINT_ALIGNED_64 (← buff.add head_pos.toInt)
  let a ← ldDAllocs alloc_bufs
  stDAllocs alloc_bufs { a with head := .val hd }
  let pb ← HINT_ALIGNED_64 (← buff.add pending_pos.toInt)
  let a ← ldDAllocs alloc_bufs
  stDAllocs alloc_bufs { a with pending_buf := .val pb }
  let sp ← carveDState (← HINT_ALIGNED_16 (← buff.add state_pos.toInt))
  let a ← ldDAllocs alloc_bufs
  stDAllocs alloc_bufs { a with state := .val sp }
  Ptr.memset (← (← ldDAllocs alloc_bufs).prev.get) 0 prev_size.toNatClampNeg
  return alloc_bufs

/-- `static inline void free_deflate(PREFIX3(stream) *strm)` (`deflate.c:261-269`). -/
def free_deflate (strm : StreamPtr) : M Unit := do
  let st ← dstateOf strm
  let s ← ldDState st
  let ab ← s.alloc_bufs.get
  if ab != none then
    let a ← ldDAllocs ab
    let z ← ldStream strm
    callZfree (← a.zfree.get) z.«opaque» (← a.buf_start.get)
    wrZ strm fun z => { z with state := none }

/-! ## Longest-match configuration -/

/-- `static void lm_set_level(deflate_state *s, int level)` (`deflate.c:1187-1203`). -/
def lm_set_level (st : StatePtr) (level : Int32) : M Unit := do
  let c ← config level
  wrD st fun s => { s with max_lazy_match := c.max_lazy.toUInt32, good_match := c.good_length.toUInt32, nice_match := c.nice_length.toUInt32.toInt32, max_chain_length := c.max_chain.toUInt32 }
  if level ≥ MIN_ROLL_LEVEL then
    wrD st fun s => { s with longest_match := .val .longest_match_slow_roll_c, insert_batch := .val .insert_roll_batch }
  else
    wrD st fun s => { s with longest_match := .val .longest_match_slow_knuth_c }
    if level == 1 then
      wrD st fun s => { s with insert_batch := .val .insert_knuth_batch_head }
    else
      wrD st fun s => { s with insert_batch := .val .insert_knuth_batch }
  wrD st fun s => { s with level := level }

/-- `static void lm_init(deflate_state *s)` (`deflate.c:1208-1229`). -/
def lm_init (st : StatePtr) : M Unit := do
  wrD st fun s => { s with window_size := W_BUF_SIZE s.w_size }
  wrD st fun s => { s with slide_len := 0, fill_end := 2 * s.w_size - MIN_LOOKAHEAD }
  let s ← ldDState st
  if !HASHLESS s.level s.strategy then
    CLEAR_HASH st
  lm_set_level st (← rdD st (·.level))
  wrD st fun s => { s with strstart := 0, block_start := 0, lookahead := 0, insert := 0, prev_length := 0, match_available := 0, match_start := 0, ins_h := 0 }

/-! ## Initialisation and reset -/

/-- `static int deflateStateCheck(PREFIX3(stream) *strm)` (`deflate.c:420-428`): `true` is 1 (bad). -/
def deflateStateCheck (strm : StreamPtr) : M Bool := do
  if strm == none then return true
  let z ← ldStream strm
  if z.zalloc == .null || z.zfree == .null then return true
  let st := z.state
  if st == none then return true
  let s ← ldDState st
  if (← s.alloc_bufs.get) == none then return true
  if (← s.strm.get) != strm then return true
  if s.status < INIT_STATE || s.status > MAX_STATE then return true
  return false

/-- `int32_t Z_EXPORT PREFIX(deflateResetKeep)(PREFIX3(stream) *strm)` (`deflate.c:516-554`). -/
def deflateResetKeep (strm : StreamPtr) : M Int32 := do
  if ← deflateStateCheck strm then return Z_STREAM_ERROR
  wrZ strm fun z => { z with total_out := 0 }
  wrZ strm fun z => { z with total_in := 0 }
  wrZ strm fun z => { z with msg := .null }
  wrZ strm fun z => { z with data_type := Z_UNKNOWN }
  let st ← dstateOf strm
  wrD st fun s => { s with pending := 0 }
  let pb ← (← ldDState st).pending_buf.get
  wrD st fun s => { s with pending_out := .val pb }
  let s ← ldDState st
  if s.wrap < 0 then
    let w ← chkI32 (-s.wrap.toInt)
    wrD st fun s => { s with wrap := w }
  wrD st fun s => { s with status := if s.wrap == 2 then GZIP_STATE else INIT_STATE }
  if (← rdD st (·.wrap)) == 2 then
    wrZ strm fun z => { z with adler := CRC32_INITIAL_VALUE }
  else
    wrZ strm fun z => { z with adler := ADLER32_INITIAL_VALUE }
  wrD st fun s => { s with last_flush := -2 }
  wrD st fun s => { s with gzhead := .val none }
  ZlibNg.Trees.zng_tr_init st
  return Z_OK

/-- `int32_t Z_EXPORT PREFIX(deflateReset)(PREFIX3(stream) *strm)` (`deflate.c:557-562`). -/
def deflateReset (strm : StreamPtr) : M Int32 := do
  let ret ← deflateResetKeep strm
  if ret == Z_OK then
    lm_init (← dstateOf strm)
  return ret

/-- `int32_t ZNG_CONDEXPORT PREFIX(deflateInit2)(PREFIX3(stream) *strm, int32_t level, int32_t method,
int32_t windowBits, int32_t memLevel, int32_t strategy)` (`deflate.c:275-394`). -/
def deflateInit2 (strm : StreamPtr) (level method windowBits memLevel strategy : Int32) : M Int32 := do
  let wrap : Int32 := 1
  if strm == none then return Z_STREAM_ERROR
  wrZ strm fun z => { z with msg := .null }
  if (← rdZ strm (·.zalloc)) == .null then
    wrZ strm fun z => { z with zalloc := .zcalloc }
    wrZ strm fun z => { z with «opaque» := .null }
  if (← rdZ strm (·.zfree)) == .null then
    wrZ strm fun z => { z with zfree := .zcfree }
  let level := if level == Z_DEFAULT_COMPRESSION then 6 else level
  let (wrap, windowBits, bad) ←
    if windowBits < 0 then do
      if windowBits < -MAX_WBITS then pure (0, windowBits, true)
      else pure ((0 : Int32), ← chkI32 (-windowBits.toInt), false)
    else if windowBits > MAX_WBITS then pure (2, windowBits - 16, false)
    else pure (wrap, windowBits, false)
  if bad then return Z_STREAM_ERROR
  if memLevel < 1 || memLevel > MAX_MEM_LEVEL || method.toInt64.toUInt64 != Z_DEFLATED || windowBits < MIN_WBITS ||
      windowBits > MAX_WBITS || level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED ||
      (windowBits == 8 && wrap != 1) then
    return Z_STREAM_ERROR
  let windowBits := if windowBits == 8 then 9 else windowBits
  let lit_bufsize ← shlI32 1 (memLevel + 6)
  let alloc_bufs ← alloc_deflate strm windowBits lit_bufsize
  if alloc_bufs == none then return Z_MEM_ERROR
  let st ← (← ldDAllocs alloc_bufs).state.get
  wrD st fun s => { s with alloc_bufs := .val alloc_bufs }
  let a ← ldDAllocs alloc_bufs
  let w ← a.window.get
  wrD st fun s => { s with window := .val w }
  let p ← (← ldDAllocs alloc_bufs).prev.get
  wrD st fun s => { s with prev := .val p }
  let hd ← (← ldDAllocs alloc_bufs).head.get
  wrD st fun s => { s with head := .val hd }
  let pb ← (← ldDAllocs alloc_bufs).pending_buf.get
  wrD st fun s => { s with pending_buf := .val pb }
  wrZ strm fun z => { z with state := st }
  wrD st fun s => { s with strm := .val strm }
  wrD st fun s => { s with status := INIT_STATE }
  wrD st fun s => { s with wrap := wrap }
  let ws ← shlI32 1 windowBits
  wrD st fun s => { s with w_size := ws.toUInt32 }
  wrD st fun s => { s with high_water := 0 }
  wrD st fun s => { s with lit_bufsize := lit_bufsize.toUInt32 }
  wrD st fun s => { s with pending_buf_size := s.lit_bufsize * 4 }
  let s ← ldDState st
  let sb ← (← (← s.pending_buf.get).add s.lit_bufsize.toNat).add PENDING_BUF_PAD.toInt
  wrD st fun s => { s with sym_buf := .val sb }
  wrD st fun s => { s with sym_end := (s.lit_bufsize - 1) * 3 }
  wrD st fun s => { s with level := level }
  wrD st fun s => { s with strategy := strategy }
  wrD st fun s => { s with block_open := 0 }
  wrD st fun s => { s with reproducible := 0 }
  deflateReset strm

/-- `int32_t Z_EXPORT PREFIX(deflateInit_)(PREFIX3(stream) *strm, int32_t level, const char *version,
int32_t stream_size)` (`deflate.c:403-407`). -/
def deflateInit_ (strm : StreamPtr) (level : Int32) (version : BPtr) (stream_size : Int32) : M Int32 := do
  if ← CHECK_VER_STSIZE version stream_size then return Z_VERSION_ERROR
  deflateInit2 strm level Z_DEFLATED.toUInt32.toInt32 MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY

/-- `int32_t Z_EXPORT PREFIX(deflateInit2_)(PREFIX3(stream) *strm, int32_t level, int32_t method,
int32_t windowBits, int32_t memLevel, int32_t strategy, const char *version, int32_t stream_size)`
(`deflate.c:410-415`). -/
def deflateInit2_ (strm : StreamPtr) (level method windowBits memLevel strategy : Int32) (version : BPtr)
    (stream_size : Int32) : M Int32 := do
  if ← CHECK_VER_STSIZE version stream_size then return Z_VERSION_ERROR
  deflateInit2 strm level method windowBits memLevel strategy

/-! ## Dictionary, header, queries -/

/-- `int32_t Z_EXPORT PREFIX(deflateSetDictionary)(PREFIX3(stream) *strm, const uint8_t *dictionary,
uint32_t dictLength)` (`deflate.c:431-494`). -/
def deflateSetDictionary (strm : StreamPtr) (dictionary : BPtr) (dictLength : UInt32) : M Int32 := do
  if (← deflateStateCheck strm) || dictionary == .null then return Z_STREAM_ERROR
  let st ← dstateOf strm
  let s ← ldDState st
  let wrap := s.wrap
  if wrap == 2 || (wrap == 1 && s.status != INIT_STATE) || s.lookahead != 0 then return Z_STREAM_ERROR
  let insert_batch ← s.insert_batch.get
  if wrap == 1 then
    let z ← ldStream strm
    let a ← ZlibNg.Adler32C.adler32_c z.adler.toUInt32 dictionary dictLength.toUInt64
    wrZ strm fun z => { z with adler := a.toUInt64 }
  wrD st fun s => { s with wrap := 0 }
  let s ← ldDState st
  let hashless := HASHLESS s.level s.strategy
  let (dictionary, dictLength) ← if dictLength ≥ s.w_size then do
      if wrap == 0 then
        if !hashless then CLEAR_HASH st
        wrD st fun s => { s with strstart := 0 }
        wrD st fun s => { s with block_start := 0 }
        wrD st fun s => { s with insert := 0 }
      let s ← ldDState st
      pure (← dictionary.add (dictLength - s.w_size).toNat, s.w_size)
    else pure (dictionary, dictLength)
  let z ← ldStream strm
  let avail := z.avail_in
  let next := z.next_in
  wrZ strm fun z => { z with avail_in := dictLength }
  wrZ strm fun z => { z with next_in := dictionary }
  fill_window st
  let _ ← cwhile
    (fun (u : Unit) => do return ((← rdD st (·.lookahead)) ≥ STD_MIN_MATCH, u))
    (fun (u : Unit) => do
      let s ← ldDState st
      let str := s.strstart
      let n := s.lookahead - (STD_MIN_MATCH - 1)
      if !hashless then
        call_insert_batch insert_batch st (← (← ldDState st).window.get) str n
      wrD st fun s => { s with strstart := str + n }
      wrD st fun s => { s with lookahead := STD_MIN_MATCH - 1 }
      fill_window st
      pure u)
    ()
  wrD st fun s => { s with strstart := s.strstart + s.lookahead }
  wrD st fun s => { s with block_start := s.strstart.toInt32 }
  wrD st fun s => { s with insert := s.lookahead }
  wrD st fun s => { s with lookahead := 0, prev_length := 0, match_available := 0 }
  wrZ strm fun z => { z with next_in := next }
  wrZ strm fun z => { z with avail_in := avail }
  wrD st fun s => { s with wrap := wrap }
  return Z_OK

/-- `int32_t Z_EXPORT PREFIX(deflateGetDictionary)(PREFIX3(stream) *strm, uint8_t *dictionary,
uint32_t *dictLength)` (`deflate.c:497-513`). -/
def deflateGetDictionary (strm : StreamPtr) (dictionary : BPtr) (hasLen : Bool) : M (Int32 × Option UInt32) := do
  if ← deflateStateCheck strm then return (Z_STREAM_ERROR, none)
  let st ← dstateOf strm
  let s ← ldDState st
  let len := s.strstart + s.lookahead
  let len := if len > s.w_size then s.w_size else len
  if dictionary != .null && len != 0 then
    let w ← s.window.get
    let src ← (← (← w.add s.strstart.toNat).add s.lookahead.toNat).add (-(len.toNat : Int))
    Ptr.memcpy dictionary src len.toNat
  return (Z_OK, if hasLen then some len else none)

/-- `int32_t Z_EXPORT PREFIX(deflateSetHeader)(PREFIX3(stream) *strm, PREFIX(gz_headerp) head)`
(`deflate.c:565-570`). -/
def deflateSetHeader (strm : StreamPtr) (head : HeaderPtr) : M Int32 := do
  if ← deflateStateCheck strm then return Z_STREAM_ERROR
  let st ← dstateOf strm
  if (← rdD st (·.wrap)) != 2 then return Z_STREAM_ERROR
  wrD st fun s => { s with gzhead := .val head }
  return Z_OK

/-- `int32_t Z_EXPORT PREFIX(deflatePending)(PREFIX3(stream) *strm, uint32_t *pending, int32_t *bits)`
(`deflate.c:573-581`). Returns the values stored through the non-NULL out-cells. -/
def deflatePending (strm : StreamPtr) (hasPending hasBits : Bool) :
    M (Int32 × Option UInt32 × Option Int32) := do
  if ← deflateStateCheck strm then return (Z_STREAM_ERROR, none, none)
  let st ← dstateOf strm
  let p ← if hasPending then pure (some (← rdD st (·.pending))) else pure none
  let b ← if hasBits then pure (some (← rdD st (·.bi_valid))) else pure none
  return (Z_OK, p, b)

/-- `int32_t Z_EXPORT PREFIX(deflateUsed)(PREFIX3(stream) *strm, int32_t *bits)` (`deflate.c:584-590`). -/
def deflateUsed (strm : StreamPtr) (hasBits : Bool) : M (Int32 × Option Int32) := do
  if ← deflateStateCheck strm then return (Z_STREAM_ERROR, none)
  let st ← dstateOf strm
  let b ← if hasBits then pure (some (← rdD st (·.bi_used))) else pure none
  return (Z_OK, b)

/-- `int32_t Z_EXPORT PREFIX(deflatePrime)(PREFIX3(stream) *strm, int32_t bits, int32_t value)`
(`deflate.c:593-624`). -/
def deflatePrime (strm : StreamPtr) (bits value : Int32) : M Int32 := do
  let value64 : UInt64 := value.toInt64.toUInt64
  if ← deflateStateCheck strm then return Z_STREAM_ERROR
  let st ← dstateOf strm
  if bits < 0 || bits > BIT_BUF_SIZE then return Z_BUF_ERROR
  let s ← ldDState st
  let k ← chkI32 (s.bi_valid.toInt + bits.toInt)
  let rhs ← (← (← s.pending_buf.get).add s.pending.toNat).add (k >>> 3).toInt
  if ← Ptr.lt (← s.sym_buf.get) rhs then return Z_BUF_ERROR
  let _ ← cdoWhile
    (fun ((bits, value64) : Int32 × UInt64) => do
      let s ← ldDState st
      let put ← chkI32 (BIT_BUF_SIZE.toInt - s.bi_valid.toInt)
      let put := if put > bits then bits else put
      let value64 ← if put == BIT_BUF_SIZE then do
          wrD st fun s => { s with bi_buf := value64 }
          pure 0
        else do
          let m ← shl64 1 put.toUInt32
          let v ← shl64 (value64 &&& (m - 1)) (← rdD st (·.bi_valid)).toUInt32
          wrD st fun s => { s with bi_buf := s.bi_buf ||| v }
          shr64 value64 put.toUInt32
      let bv ← chkI32 ((← rdD st (·.bi_valid)).toInt + put.toInt)
      wrD st fun s => { s with bi_valid := bv }
      ZlibNg.Trees.zng_tr_flush_bits st
      pure (bits - put, value64))
    (fun (x : Int32 × UInt64) => pure (x.1 != 0, x))
    (bits, value64)
  return Z_OK

/-- `int32_t Z_EXPORT PREFIX(deflateTune)(PREFIX3(stream) *strm, int32_t good_length, int32_t max_lazy,
int32_t nice_length, int32_t max_chain)` (`deflate.c:677-688`). -/
def deflateTune (strm : StreamPtr) (good_length max_lazy nice_length max_chain : Int32) : M Int32 := do
  if ← deflateStateCheck strm then return Z_STREAM_ERROR
  let st ← dstateOf strm
  wrD st fun s => { s with good_match := good_length.toUInt32, max_lazy_match := max_lazy.toUInt32, nice_match := nice_length, max_chain_length := max_chain.toUInt32 }
  return Z_OK

/-- `strlen`-like walk of `deflateBound`: `do { wraplen++; } while (*str++);` -/
def countStr (str : BPtr) (wraplen : UInt64) : M UInt64 := do
  let (_, wraplen, _) ← cdoWhile
    (fun ((str, wraplen, c) : BPtr × UInt64 × UInt8) => pure (str, wraplen + 1, c))
    (fun ((str, wraplen, _) : BPtr × UInt64 × UInt8) => do
      let c ← load8 str
      let str ← str.add 1
      pure (c != 0, (str, wraplen, c)))
    (str, wraplen, 0)
  return wraplen

/-- `z_size_t Z_EXPORT PREFIX(deflateBound_z)(PREFIX3(stream) *strm, z_size_t sourceLen)` (`deflate.c:707-787`,
patch 0003: `2 + (extra_len & 0xffff)` in `z_size_t`). -/
def deflateBound_z (strm : StreamPtr) (sourceLen : UInt64) : M UInt64 := do
  let complen : UInt64 := sourceLen + ((sourceLen + 7) >>> 3) + ((sourceLen + 63) >>> 6) + 5
  if ← deflateStateCheck strm then
    let bound := complen + GZIP_WRAPLEN
    return if bound < sourceLen then 0xffffffffffffffff else bound
  let st ← dstateOf strm
  let s ← ldDState st
  let aw := if s.wrap < 0 then -s.wrap else s.wrap
  let wraplen ←
    if aw == 0 then pure 0
    else if aw == 1 then pure (ZLIB_WRAPLEN + (if s.strstart != 0 then 4 else 0))
    else if aw == 2 then do
      let gh ← s.gzhead.get
      if gh != none then
        let g ← ldHeader gh
        let wraplen := GZIP_WRAPLEN
        let wraplen := if g.extra != .null then wraplen + (2 + (g.extra_len &&& 0xffff).toUInt64) else wraplen
        let g ← ldHeader gh
        let wraplen ← if g.name != .null then countStr g.name wraplen else pure wraplen
        let g ← ldHeader gh
        let wraplen ← if g.comment != .null then countStr g.comment wraplen else pure wraplen
        let g ← ldHeader gh
        pure (if g.hcrc != 0 then wraplen + 2 else wraplen)
      else pure GZIP_WRAPLEN
    else ub "Z_UNREACHABLE()"
  if (← W_BITS s) != MAX_WBITS.toUInt32 || HASH_BITS < 15 then
    let complen := if s.level == 0 then
        sourceLen + (sourceLen >>> 5) + (sourceLen >>> 7) + (sourceLen >>> 11) + 7 else complen
    let bound := complen + wraplen
    return if bound < sourceLen then 0xffffffffffffffff else bound
  let bound := sourceLen + (if sourceLen == 0 then 1 else 0) + (if sourceLen < 9 then 1 else 0)
    + ZlibNg.Compress.DEFLATE_QUICK_OVERHEAD sourceLen + ZlibNg.Compress.DEFLATE_BLOCK_OVERHEAD + wraplen
  return if bound < sourceLen then 0xffffffffffffffff else bound

/-- `unsigned long Z_EXPORT PREFIX(deflateBound)(PREFIX3(stream) *strm, unsigned long sourceLen)`
(`deflate.c:789-792`). -/
def deflateBound (strm : StreamPtr) (sourceLen : UInt64) : M UInt64 := do
  let bound ← deflateBound_z strm sourceLen
  return ZlibNg.Zbuild.MIN 0xffffffffffffffff bound

/-- `int32_t Z_EXPORT PREFIX(deflateParams)(PREFIX3(stream) *strm, int32_t level, int32_t strategy)`
(`deflate.c:627-674`); `deflate` is passed in because it is defined after this function in the translation's
order of definitions (the C calls it through its prototype). -/
def deflateParamsWith (deflateFn : StreamPtr → Int32 → M Int32) (strm : StreamPtr) (level strategy : Int32) :
    M Int32 := do
  let hook_flush : Int32 := Z_NO_FLUSH
  if ← deflateStateCheck strm then return Z_STREAM_ERROR
  let st ← dstateOf strm
  let level := if level == Z_DEFAULT_COMPRESSION then 6 else level
  if level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED then return Z_STREAM_ERROR
  let s ← ldDState st
  let func := (← config s.level).func
  if ((strategy != s.strategy || func != (← config level).func) && s.last_flush != -2) || hook_flush != Z_NO_FLUSH then
    let flush := if (← RANK hook_flush) > (← RANK Z_BLOCK) then hook_flush else Z_BLOCK
    let err ← deflateFn strm flush
    if err == Z_STREAM_ERROR then return err
    let z ← ldStream strm
    let s ← ldDState st
    if z.avail_in != 0 then return Z_BUF_ERROR
    let d ← chkI32 (s.strstart.toInt32.toInt - s.block_start.toInt)
    if d.toUInt32 + s.lookahead != 0 then return Z_BUF_ERROR
  let s ← ldDState st
  let hashless := HASHLESS level strategy
  let was_hashless := HASHLESS s.level s.strategy
  let stale_chain := (hashless != was_hashless) || ((level ≥ MIN_ROLL_LEVEL) != (s.level ≥ MIN_ROLL_LEVEL)) ||
    (s.level == 1 && level != 1)
  if stale_chain && !hashless then
    CLEAR_HASH st
    wrD st fun s => { s with ins_h := 0 }
    wrD st fun s => { s with insert := if s.strstart > s.w_size then s.w_size else s.strstart }
  if (← rdD st (·.level)) != level then
    lm_set_level st level
  wrD st fun s => { s with strategy := strategy }
  return Z_OK

/-! ## `deflate` -/

/-- `HCRC_UPDATE(beg)` (`deflate.c:804-808`). -/
def HCRC_UPDATE (strm : StreamPtr) (st : StatePtr) (beg : UInt32) : M Unit := do
  let s ← ldDState st
  let g ← ldHeader (← s.gzhead.get)
  if g.hcrc != 0 && s.pending > beg then
    let z ← ldStream strm
    let c ← ZlibNg.Crc32.crc32_small z.adler.toUInt32 (← (← s.pending_buf.get).add beg.toNat) (s.pending - beg).toUInt64
    wrZ strm fun z => { z with adler := c.toUInt64 }

/-- `if (s->pending != 0) { s->last_flush = -1; return Z_OK; }` after a flush in `deflateHeaders`: `true` returns. -/
def pendingReturn (st : StatePtr) : M Bool := do
  if (← rdD st (·.pending)) != 0 then
    wrD st fun s => { s with last_flush := -1 }
    return true
  return false

/-- The `INIT_STATE` part of `deflateHeaders` (`deflate.c:814-846`): `true` is `return Z_OK`. -/
def headersInit (s0 : DeflateState) (st : StatePtr) (strm : StreamPtr) : M Bool := do
  let wb ← W_BITS s0
  let header : UInt32 := (Z_DEFLATED.toUInt32 + ((wb - 8) <<< 4)) <<< 8
  let s ← ldDState st
  let level_flags : UInt32 :=
    if s.strategy ≥ Z_HUFFMAN_ONLY || s.level < 2 then 0
    else if s.level < 6 then 1
    else if s.level == 6 then 2
    else 3
  let header := header ||| (level_flags <<< 6)
  let header := if s.strstart != 0 then header ||| PRESET_DICT else header
  let header := header + (31 - (header % 31))
  put_short_msb st header.toUInt16
  if (← rdD st (·.strstart)) != 0 then
    put_uint32_msb st (← rdZ strm (·.adler)).toUInt32
  wrZ strm fun z => { z with adler := ADLER32_INITIAL_VALUE }
  wrD st fun s => { s with status := BUSY_STATE }
  flush_pending strm
  pendingReturn st

/-- The `GZIP_STATE` part of `deflateHeaders` (`deflate.c:848-885`): `true` is `return Z_OK`. -/
def headersGzip (st : StatePtr) (strm : StreamPtr) : M Bool := do
  wrZ strm fun z => { z with adler := CRC32_INITIAL_VALUE }
  put_byte st 31
  put_byte st 139
  put_byte st 8
  let gh ← (← ldDState st).gzhead.get
  if gh == none then
    put_uint32 st 0
    put_byte st 0
    let s ← ldDState st
    put_byte st (if s.level == 9 then 2 else if s.strategy ≥ Z_HUFFMAN_ONLY || s.level < 2 then 4 else 0)
    put_byte st OS_CODE
    wrD st fun s => { s with status := BUSY_STATE }
    flush_pending strm
    pendingReturn st
  else
    let g ← ldHeader gh
    let fl : Int32 := (if g.text != 0 then 1 else 0) + (if g.hcrc != 0 then 2 else 0) +
      (if g.extra == .null then 0 else 4) + (if g.name == .null then 0 else 8) + (if g.comment == .null then 0 else 16)
    put_byte st fl.toUInt32.toUInt8
    put_uint32 st (← ldHeader gh).time.toUInt32
    let s ← ldDState st
    put_byte st (if s.level == 9 then 2 else if s.strategy ≥ Z_HUFFMAN_ONLY || s.level < 2 then 4 else 0)
    put_byte st ((← ldHeader gh).os &&& 0xff).toUInt32.toUInt8
    if (← ldHeader gh).extra != .null then
      put_short st (← ldHeader gh).extra_len.toUInt16
    if (← ldHeader gh).hcrc != 0 then
      let s ← ldDState st
      let c ← ZlibNg.Crc32.crc32_small (← rdZ strm (·.adler)).toUInt32 (← s.pending_buf.get) s.pending.toUInt64
      wrZ strm fun z => { z with adler := c.toUInt64 }
    wrD st fun s => { s with gzindex := 0 }
    wrD st fun s => { s with status := EXTRA_STATE }
    return false

/-- The `EXTRA_STATE` part of `deflateHeaders` (`deflate.c:886-911`): `true` is `return Z_OK`. -/
def headersExtra (st : StatePtr) (strm : StreamPtr) : M Bool := do
  let gh ← (← ldDState st).gzhead.get
  if (← ldHeader gh).extra != .null then
    let s ← ldDState st
    let beg := s.pending
    let left := ((← ldHeader gh).extra_len &&& 0xffff) - s.gzindex
    -- while (s->pending + left > s->pending_buf_size) { ... }
    let (r, beg, left) ← cwhile
      (fun ((r, beg, left) : Bool × UInt32 × UInt32) => do
        if r then return (false, (r, beg, left))
        let s ← ldDState st
        return (s.pending + left > s.pending_buf_size, (r, beg, left)))
      (fun ((_, beg, left) : Bool × UInt32 × UInt32) => do
        let s ← ldDState st
        let copy := s.pending_buf_size - s.pending
        let g ← ldHeader gh
        Ptr.memcpy (← (← s.pending_buf.get).add s.pending.toNat) (← g.extra.add s.gzindex.toNat) copy.toNat
        wrD st fun s => { s with pending := s.pending_buf_size }
        HCRC_UPDATE strm st beg
        wrD st fun s => { s with gzindex := s.gzindex + copy }
        flush_pending strm
        if ← pendingReturn st then return (true, beg, left)
        pure (false, 0, left - copy))
      (false, beg, left)
    if r then return true
    let s ← ldDState st
    let g ← ldHeader gh
    Ptr.memcpy (← (← s.pending_buf.get).add s.pending.toNat) (← g.extra.add s.gzindex.toNat) left.toNat
    wrD st fun s => { s with pending := s.pending + left }
    HCRC_UPDATE strm st beg
    wrD st fun s => { s with gzindex := 0 }
  wrD st fun s => { s with status := NAME_STATE }
  return false

/-- The `NAME_STATE` / `COMMENT_STATE` loops of `deflateHeaders` (`deflate.c:913-931`, `936-953`) over the string
`str` of the header: `true` is `return Z_OK`. -/
def headersString (st : StatePtr) (strm : StreamPtr) (str : GzHeader → BPtr) : M Bool := do
  let gh ← (← ldDState st).gzhead.get
  let beg ← rdD st (·.pending)
  let (r, beg, _) ← cdoWhile
    (fun ((_, beg, _) : Bool × UInt32 × UInt8) => do
      let s ← ldDState st
      let (r, beg) ← if s.pending == s.pending_buf_size then do
          HCRC_UPDATE strm st beg
          flush_pending strm
          if ← pendingReturn st then pure (true, beg) else pure (false, 0)
        else pure (false, beg)
      if r then return (true, beg, 0)
      let s ← ldDState st
      let gi := s.gzindex
      wrD st fun s => { s with gzindex := gi + 1 }
      let v ← index8 (str (← ldHeader gh)) gi.toNat
      put_byte st v
      pure (false, beg, v))
    (fun ((r, beg, v) : Bool × UInt32 × UInt8) => pure (!r && v != 0, (r, beg, v)))
    (false, beg, 0)
  if r then return true
  HCRC_UPDATE strm st beg
  return false

/-- `static int deflateHeaders(deflate_state *s, PREFIX3(stream) *strm)` (`deflate.c:813-980`): returns `Z_OK` or
`-1`. -/
def deflateHeaders (st : StatePtr) (strm : StreamPtr) : M Int32 := do
  let s ← ldDState st
  if s.status == INIT_STATE then
    if ← headersInit s st strm then return Z_OK
  if (← rdD st (·.status)) == GZIP_STATE then
    if ← headersGzip st strm then return Z_OK
  if (← rdD st (·.status)) == EXTRA_STATE then
    if ← headersExtra st strm then return Z_OK
  if (← rdD st (·.status)) == NAME_STATE then
    let gh ← (← ldDState st).gzhead.get
    if (← ldHeader gh).name != .null then
      if ← headersString st strm (·.name) then return Z_OK
      wrD st fun s => { s with gzindex := 0 }
    wrD st fun s => { s with status := COMMENT_STATE }
  if (← rdD st (·.status)) == COMMENT_STATE then
    let gh ← (← ldDState st).gzhead.get
    if (← ldHeader gh).comment != .null then
      if ← headersString st strm (·.comment) then return Z_OK
    wrD st fun s => { s with status := HCRC_STATE }
  if (← rdD st (·.status)) == HCRC_STATE then
    let gh ← (← ldDState st).gzhead.get
    if (← ldHeader gh).hcrc != 0 then
      let s ← ldDState st
      if s.pending + 2 > s.pending_buf_size then
        flush_pending strm
        if ← pendingReturn st then return Z_OK
      put_short st (← rdZ strm (·.adler)).toUInt16
      wrZ strm fun z => { z with adler := CRC32_INITIAL_VALUE }
    wrD st fun s => { s with status := BUSY_STATE }
    flush_pending_inline strm
    if ← pendingReturn st then return Z_OK
  return -1

/-- `int32_t Z_EXPORT PREFIX(deflate)(PREFIX3(stream) *strm, int32_t flush)` (`deflate.c:983-1119`). -/
def deflate (strm : StreamPtr) (flush : Int32) : M Int32 := do
  if (← deflateStateCheck strm) || flush > Z_BLOCK || flush < 0 then return Z_STREAM_ERROR
  let st ← dstateOf strm
  let z ← ldStream strm
  let s ← ldDState st
  if z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) || (s.status == FINISH_STATE && flush != Z_FINISH) then
    return ← ERR_RETURN strm Z_STREAM_ERROR
  if z.avail_out == 0 then
    return ← ERR_RETURN strm Z_BUF_ERROR
  let old_flush := s.last_flush
  wrD st fun s => { s with last_flush := flush }
  if (← rdD st (·.pending)) != 0 then
    flush_pending_inline strm
    if (← rdZ strm (·.avail_out)) == 0 then
      wrD st fun s => { s with last_flush := -1 }
      return Z_OK
  else if (← rdZ strm (·.avail_in)) == 0 && (← RANK flush) ≤ (← RANK old_flush) && flush != Z_FINISH then
    return ← ERR_RETURN strm Z_BUF_ERROR
  if (← rdD st (·.status)) == FINISH_STATE && (← rdZ strm (·.avail_in)) != 0 then
    return ← ERR_RETURN strm Z_BUF_ERROR
  let s ← ldDState st
  if s.status == INIT_STATE && s.wrap == 0 then
    wrD st fun s => { s with status := BUSY_STATE }
  let s ← ldDState st
  if s.status != BUSY_STATE && s.status != FINISH_STATE && s.wrap != 0 then
    if (← deflateHeaders st strm) == Z_OK then return Z_OK
  let s ← ldDState st
  if (← rdZ strm (·.avail_in)) != 0 || s.lookahead != 0 || (flush != Z_NO_FLUSH && s.status != FINISH_STATE) then
    let s ← ldDState st
    let bstate ←
      if s.level == 0 then ZlibNg.DeflateStored.deflate_stored st flush
      else if s.strategy == Z_HUFFMAN_ONLY then ZlibNg.DeflateHuff.deflate_huff st flush
      else if s.strategy == Z_RLE then ZlibNg.DeflateRle.deflate_rle st flush
      else call_compress (← config s.level).func st flush
    if bstate == .finish_started || bstate == .finish_done then
      wrD st fun s => { s with status := FINISH_STATE }
    if bstate == .need_more || bstate == .finish_started then
      if (← rdZ strm (·.avail_out)) == 0 then
        wrD st fun s => { s with last_flush := -1 }
      return Z_OK
    if bstate == .block_done then
      if flush == Z_PARTIAL_FLUSH then
        ZlibNg.Trees.zng_tr_align st
      else if flush != Z_BLOCK then
        ZlibNg.Trees.zng_tr_stored_block st .null 0 0
        if flush == Z_FULL_FLUSH then
          CLEAR_HASH st
          if (← rdD st (·.lookahead)) == 0 then
            wrD st fun s => { s with strstart := 0 }
            wrD st fun s => { s with block_start := 0 }
            wrD st fun s => { s with insert := 0 }
      flush_pending strm
      if (← rdZ strm (·.avail_out)) == 0 then
        wrD st fun s => { s with last_flush := -1 }
        return Z_OK
  if flush != Z_FINISH then return Z_OK
  if (← rdD st (·.wrap)) == 2 then
    put_uint32 st (← rdZ strm (·.adler)).toUInt32
    put_uint32 st (← rdZ strm (·.total_in)).toUInt32
  else
    if (← rdD st (·.wrap)) == 1 then
      put_uint32_msb st (← rdZ strm (·.adler)).toUInt32
  flush_pending_inline strm
  let s ← ldDState st
  if s.wrap > 0 then
    wrD st fun s => { s with wrap := -s.wrap }
  if (← rdD st (·.pending)) == 0 then return Z_STREAM_END
  return Z_OK

/-- `int32_t Z_EXPORT PREFIX(deflateParams)(PREFIX3(stream) *strm, int32_t level, int32_t strategy)`
(`deflate.c:627-674`). -/
def deflateParams (strm : StreamPtr) (level strategy : Int32) : M Int32 :=
  deflateParamsWith deflate strm level strategy

/-- `int32_t Z_EXPORT PREFIX(deflateEnd)(PREFIX3(stream) *strm)` (`deflate.c:1122-1132`). -/
def deflateEnd (strm : StreamPtr) : M Int32 := do
  if ← deflateStateCheck strm then return Z_STREAM_ERROR
  let status := (← ldDState (← dstateOf strm)).status
  free_deflate strm
  return if status == BUSY_STATE then Z_DATA_ERROR else Z_OK

/-- `int32_t Z_EXPORT PREFIX(deflateCopy)(PREFIX3(stream) *dest, PREFIX3(stream) *source)` (`deflate.c:1137-1182`). -/
def deflateCopy (dest source : StreamPtr) : M Int32 := do
  if (← deflateStateCheck source) || dest == none then return Z_STREAM_ERROR
  let ss ← dstateOf source
  copyStream dest source
  let s ← ldDState ss
  let alloc_bufs ← alloc_deflate dest (← W_BITS s).toInt32 s.lit_bufsize.toInt32
  if alloc_bufs == none then return Z_MEM_ERROR
  let ds ← (← ldDAllocs alloc_bufs).state.get
  wrZ dest fun z => { z with state := ds }
  copyDState ds ss
  wrD ds fun s => { s with strm := .val dest }
  wrD ds fun s => { s with alloc_bufs := .val alloc_bufs }
  let w ← (← ldDAllocs alloc_bufs).window.get
  wrD ds fun s => { s with window := .val w }
  let p ← (← ldDAllocs alloc_bufs).prev.get
  wrD ds fun s => { s with prev := .val p }
  let hd ← (← ldDAllocs alloc_bufs).head.get
  wrD ds fun s => { s with head := .val hd }
  let pb ← (← ldDAllocs alloc_bufs).pending_buf.get
  wrD ds fun s => { s with pending_buf := .val pb }
  let d ← ldDState ds
  if (← d.window.get) == .null || (← d.prev.get) == .null || (← d.head.get) == .null || (← d.pending_buf.get) == .null then
    let _ ← deflateEnd dest
    return Z_MEM_ERROR
  let s ← ldDState ss
  Ptr.memcpy (← d.window.get) (← s.window.get) (W_BUF_SIZE d.w_size).toNat
  Ptr.memcpy (← d.prev.get) (← s.prev.get) (d.w_size.toNat * 2)
  Ptr.memcpy (← d.head.get) (← s.head.get) (HASH_SIZE.toNat * 2)
  Ptr.memcpy (← d.pending_buf.get) (← s.pending_buf.get) (d.lit_bufsize * 4 + 1 + 8).toNat
  let off ← Ptr.diff (← s.pending_out.get) (← s.pending_buf.get)
  let po ← (← d.pending_buf.get).add off.toInt
  wrD ds fun s => { s with pending_out := .val po }
  let d ← ldDState ds
  let sb ← (← (← d.pending_buf.get).add d.lit_bufsize.toNat).add PENDING_BUF_PAD.toInt
  wrD ds fun s => { s with sym_buf := .val sb }
  let lt ← dynLtreeP ds
  let dt ← dynDtreeP ds
  let bt ← blTreeP ds
  wrD ds fun s => { s with l_desc := { s.l_desc with dyn_tree := .val lt } }
  wrD ds fun s => { s with d_desc := { s.d_desc with dyn_tree := .val dt } }
  wrD ds fun s => { s with bl_desc := { s.bl_desc with dyn_tree := .val bt } }
  return Z_OK

end ZlibNg.Deflate
