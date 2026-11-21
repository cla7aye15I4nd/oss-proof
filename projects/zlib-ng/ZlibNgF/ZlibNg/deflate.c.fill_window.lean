import ZlibNgF.ZlibNg.«deflate_p.h»
import ZlibNgF.ZlibNg.«insert_string.c»
import ZlibNgF.ZlibNg.arch.generic.«slide_hash_c.c»

/-!
# `deflate.c` (part) — `fill_window` (`ZlibNgF`)

Source: `zlib-ng/deflate.c:1242-1361` and the macro `HASHLESS` (`deflate.c:165-166`). This part of `deflate.c` is
in its own module because the strategy files call `fill_window` and `deflate.c` calls the strategies; the rest of
`deflate.c` is `deflate.c.lean`. With patch 0015, the slide lowers `block_start` only while it stays at or above
`-(2^30 + 2^16)` (`(1 << 30)` and `(1 << 16)` are the constants 1073741824 and 65536). `HAVE_QUICK_STRATEGY` is 1. `FUNCTABLE_CALL(slide_hash)` = `slide_hash_c`,
`FUNCTABLE_CALL(slide_hash_head)` = `slide_hash_head_c`; the call `insert_batch(...)` goes through the function
pointer read from `s->insert_batch` (`call_insert_batch`).
-/

set_option autoImplicit false

namespace ZlibNg.Deflate
open C ZlibNg.Inflate ZlibNg.DeflateP ZlibNg.InsertStringP ZlibNg.InsertString

/-- `#define HASHLESS(level, strategy) ((level) == 0 || (strategy) == Z_HUFFMAN_ONLY || (strategy) == Z_RLE)` -/
def HASHLESS (level strategy : Int32) : Bool :=
  level == 0 || strategy == Z_HUFFMAN_ONLY || strategy == Z_RLE

/-- The first (sliding) part of one trip of the `do` loop of `fill_window` (`deflate.c:1260-1287`). -/
def fill_window_slide (st : StatePtr) (window : BPtr) (level : Int32) : M Unit := do
  let _ ← cwhile
    (fun (u : Unit) => do let s ← ldDState st; pure (s.strstart ≥ s.fill_end, u))
    (fun (u : Unit) => do wrD st fun s => { s with fill_end := s.fill_end + s.w_size }; pure u)
    ()
  let s ← ldDState st
  if s.fill_end > s.window_size - MIN_LOOKAHEAD then
    let slide_len : UInt32 := (s.strstart - MAX_DIST s) &&& ~~~(W_MASK s)
    Ptr.memcpy window (← window.add slide_len.toNat) (s.strstart + s.lookahead - slide_len).toNat
    let s ← ldDState st
    if s.match_start ≥ slide_len then
      wrD st fun s => { s with match_start := s.match_start - slide_len }
    else
      wrD st fun s => { s with match_start := 0, prev_length := 0 }
    wrD st fun s => { s with strstart := s.strstart - slide_len }
    let s ← ldDState st
    if s.block_start.toInt ≥ (← chkI32 ((← chkI32 (slide_len.toInt32.toInt - 1073741824)).toInt - 65536)).toInt then
      let bs ← chkI32 (s.block_start.toInt - slide_len.toInt32.toInt)
      wrD st fun s => { s with block_start := bs }
    wrD st fun s => { s with fill_end := s.fill_end - slide_len }
    let s ← ldDState st
    if s.insert > s.strstart then
      wrD st fun s => { s with insert := s.strstart }
    let s ← ldDState st
    if !HASHLESS level s.strategy then
      wrD st fun s => { s with slide_len := slide_len }
      if level == 1 then
        ZlibNg.SlideHash.slide_hash_head_c st
      else
        ZlibNg.SlideHash.slide_hash_c st

/-- The reading part of one trip of the `do` loop of `fill_window` (`deflate.c:1296-1321`). -/
def fill_window_read (st : StatePtr) (strm : StreamPtr) (insert_batch : InsertBatchFn) (window : BPtr)
    (level : Int32) : M Unit := do
  let s ← ldDState st
  let more : UInt32 := s.fill_end + MIN_LOOKAHEAD - s.lookahead - s.strstart
  let n ← read_buf strm (← window.add (s.strstart + s.lookahead).toNat) more
  wrD st fun s => { s with lookahead := s.lookahead + n }
  let s ← ldDState st
  if !HASHLESS level s.strategy && s.lookahead + s.insert ≥ STD_MIN_MATCH then
    let str : UInt32 := s.strstart - s.insert
    if level ≥ MIN_ROLL_LEVEL then
      let w0 ← index8 window str.toNat
      let w1 ← index8 window (str + 1).toNat
      wrD st fun s => { s with ins_h := update_hash_roll (update_hash_roll 0 w0.toUInt32) w1.toUInt32 }
    else if str ≥ 1 then
      if level == 1 then
        let _ ← insert_knuth_head st window (str + 2 - STD_MIN_MATCH)
      else
        let _ ← insert_knuth st window (str + 2 - STD_MIN_MATCH)
    let s ← ldDState st
    let count := s.insert
    let count := if s.lookahead == 1 then count - 1 else count
    if count > 0 then
      call_insert_batch insert_batch st window str count
      wrD st fun s => { s with insert := s.insert - count }

/-- `void Z_INTERNAL PREFIX(fill_window)(deflate_state *s)` (`deflate.c:1242-1361`). -/
def fill_window (st : StatePtr) : M Unit := do
  let s ← ldDState st
  let strm ← s.strm.get
  let insert_batch ← s.insert_batch.get
  let window ← s.window.get
  let level := s.level
  -- do { ... } while (s->lookahead < MIN_LOOKAHEAD && strm->avail_in != 0);  `break` when avail_in == 0
  let _ ← cdoWhile
    (fun (brk : Bool) => do
      let _ := brk
      fill_window_slide st window level
      if (← rdZ strm (·.avail_in)) == 0 then return true
      fill_window_read st strm insert_batch window level
      return false)
    (fun (brk : Bool) => do
      if brk then return (false, brk)
      let s ← ldDState st
      return (s.lookahead < MIN_LOOKAHEAD && (← rdZ strm (·.avail_in)) != 0, brk))
    false
  let s ← ldDState st
  if s.high_water < s.window_size then
    let curr := s.strstart + s.lookahead
    if s.high_water < curr then
      let init := s.window_size - curr
      let init := if init > WIN_INIT then WIN_INIT else init
      Ptr.memset (← window.add curr.toNat) 0 init.toNat
      wrD st fun s => { s with high_water := curr + init }
    else if s.high_water < curr + WIN_INIT then
      let init := curr + WIN_INIT - s.high_water
      let init := if init > s.window_size - s.high_water then s.window_size - s.high_water else init
      Ptr.memset (← window.add s.high_water.toNat) 0 init.toNat
      wrD st fun s => { s with high_water := s.high_water + init }

end ZlibNg.Deflate
