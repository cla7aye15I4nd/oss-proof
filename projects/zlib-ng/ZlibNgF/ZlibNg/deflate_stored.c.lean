import ZlibNgF.ZlibNg.«deflate_p.h»

/-!
# `deflate_stored.c` — the stored (level 0) strategy (`ZlibNgF`)

Source: `zlib-ng/deflate_stored.c` (no `ZLIB_DEBUG`: `cmpr_bits_add` / `sent_bits_add` are `Z_UNUSED(x)`, and their
operand `len << 3` is an unsigned shift by a constant that reads no memory, so they are omitted).

`MIN` / `MAX` of `zbuild.h` are applied to `unsigned` / `uint32_t` operands here (`MIN32`, `MAX32`). Every
`s->strm->x` reads the `strm` pointer field and then the `z_stream` member.

## Control flow
The `do { ... } while (last == 0)` loop (`:36-98`) is a `cdoWhile` over `(last, brk)`; `brk` is set by the two
`break`s (`:44`, `:58`) and stops the loop before its condition is evaluated. `len`, `left`, `have` are assigned
before every use inside a trip and are not read after the loop before being assigned again (`:143`, `:172`,
`:174`), so they are locals of the trip.
-/

set_option autoImplicit false

namespace ZlibNg.DeflateStored
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP ZlibNg.Trees

/-- `#define MIN(a, b) ((a) > (b) ? (b) : (a))` (`zbuild.h:148`) on `unsigned` / `uint32_t`. -/
def MIN32 (a b : UInt32) : UInt32 := if a > b then b else a
/-- `#define MAX(a, b) ((a) < (b) ? (b) : (a))` (`zbuild.h:150`) on `unsigned` / `uint32_t`. -/
def MAX32 (a b : UInt32) : UInt32 := if a < b then b else a

/-- `s->strm` -/
def strmOf (st : StatePtr) : M StreamPtr := do (← ldDState st).strm.get

/-- `(s->bi_valid + 42) >> 3` (number of header bytes): `int` addition (checked), right shift of an `int`
(arithmetic, GCC), converted to `unsigned` (modulo). -/
def headerBytes (st : StatePtr) : M UInt32 := do
  let t ← chkI32 ((← rdD st (·.bi_valid)).toInt + 42)
  return (t >>> 3).toUInt32

/-- `left = (int)s->strstart - s->block_start;` with `left` an `unsigned`: `(int)` of a `uint32_t` is GCC's modulo
conversion, the subtraction is `int` arithmetic (checked), and the result is converted to `unsigned` (modulo). -/
def leftOf (st : StatePtr) : M UInt32 := do
  let s ← ldDState st
  return (← chkI32 (s.strstart.toInt32.toInt - s.block_start.toInt)).toUInt32

/-- One trip of the `do` loop of `deflate_stored` (`deflate_stored.c:37-97`). Returns `(last, brk)`. -/
def stored_trip (st : StatePtr) (window : BPtr) (flush : Int32) (min_block : UInt32) (last : Int32) :
    M (Int32 × Bool) := do
  let len : UInt32 := MAX_STORED
  let have_ ← headerBytes st
  if (← rdZ (← strmOf st) (·.avail_out)) < have_ then
    return (last, true)
  let have_ := (← rdZ (← strmOf st) (·.avail_out)) - have_
  let left ← leftOf st
  -- `s->strm->avail_in` is read at `:48`, `:49`, `:57`, `:63` with no store in between (normalisation 2).
  let avail_in ← rdZ (← strmOf st) (·.avail_in)
  let len := if len.toUInt64 > left.toUInt64 + avail_in.toUInt64 then left + avail_in else len
  let len := MIN32 len have_
  if len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH || len != left + avail_in) then
    return (last, true)
  let last : Int32 := if flush == Z_FINISH && len == left + avail_in then 1 else 0
  zng_tr_stored_block st .null 0 last
  wrD st fun s => { s with pending := s.pending - 4 }
  put_short st len.toUInt16
  put_short st (~~~len).toUInt16
  flush_pending (← strmOf st)
  -- cmpr_bits_add(s, len << 3); sent_bits_add(s, len << 3);  (empty without ZLIB_DEBUG)
  let len ← if left != 0 then do
      let left := MIN32 left len
      let strm ← strmOf st
      let bs ← rdD st (·.block_start)
      Ptr.memcpy (← rdZ strm (·.next_out)) (← window.add bs.toInt) left.toNat
      let strm ← strmOf st
      let no ← (← rdZ strm (·.next_out)).add left.toNat
      wrZ strm fun z => { z with next_out := no }
      wrZ (← strmOf st) fun z => { z with avail_out := z.avail_out - left }
      wrZ (← strmOf st) fun z => { z with total_out := z.total_out + left.toUInt64 }
      let bs ← chkI32 ((← rdD st (·.block_start)).toInt + left.toInt32.toInt)
      wrD st fun s => { s with block_start := bs }
      pure (len - left)
    else pure len
  if len != 0 then
    let strm ← strmOf st
    let _ ← read_buf strm (← rdZ (← strmOf st) (·.next_out)) len
    let strm ← strmOf st
    let no ← (← rdZ strm (·.next_out)).add len.toNat
    wrZ strm fun z => { z with next_out := no }
    wrZ (← strmOf st) fun z => { z with avail_out := z.avail_out - len }
    wrZ (← strmOf st) fun z => { z with total_out := z.total_out + len.toUInt64 }
  return (last, false)

/-- The window update after the copy loop (`deflate_stored.c:107-130`). -/
def stored_update_window (st : StatePtr) (window : BPtr) (w_size used : UInt32) (last : Int32) : M Unit := do
  let used := used - (← rdZ (← strmOf st) (·.avail_in))
  if used != 0 && last == 0 then
    if used ≥ w_size then
      let strm ← strmOf st
      Ptr.memcpy window (← (← rdZ strm (·.next_in)).add (-(w_size.toNat : Int))) w_size.toNat
      wrD st fun s => { s with strstart := w_size }
      wrD st fun s => { s with insert := s.strstart }
    else
      let s ← ldDState st
      if s.window_size - s.strstart ≤ used then
        let slide_len : UInt32 := s.strstart - w_size
        wrD st fun s => { s with strstart := w_size }
        Ptr.memmove window (← window.add slide_len.toNat) (← rdD st (·.strstart)).toNat
        wrD st fun s => { s with insert := MIN32 s.insert s.strstart }
      let ss ← rdD st (·.strstart)
      let strm ← strmOf st
      Ptr.memcpy (← window.add ss.toNat) (← (← rdZ strm (·.next_in)).add (-(used.toNat : Int))) used.toNat
      wrD st fun s => { s with strstart := s.strstart + used }
      wrD st fun s => { s with insert := s.insert + MIN32 used (w_size - s.insert) }
    wrD st fun s => { s with block_start := s.strstart.toInt32 }
  wrD st fun s => { s with high_water := MAX32 s.high_water s.strstart }

/-- `Z_INTERNAL block_state deflate_stored(deflate_state *s, int flush)` (`deflate_stored.c:20-187`). -/
def deflate_stored (st : StatePtr) (flush : Int32) : M BlockState := do
  let window ← (← rdD st (·.window)).get
  let w_size ← rdD st (·.w_size)
  let min_block := MIN32 ((← rdD st (·.pending_buf_size)) - 5) w_size
  let last : Int32 := 0
  let used ← rdZ (← strmOf st) (·.avail_in)
  let (last, _) ← cdoWhile
    (fun ((last, _) : Int32 × Bool) => stored_trip st window flush min_block last)
    (fun ((last, brk) : Int32 × Bool) => pure (!brk && last == 0, (last, brk)))
    (last, false)
  stored_update_window st window w_size used last
  if last != 0 then
    wrD st fun s => { s with bi_used := 8 }
    return .finish_done
  if flush != Z_NO_FLUSH && flush != Z_FINISH && (← rdZ (← strmOf st) (·.avail_in)) == 0 then
    let s ← ldDState st
    if s.strstart.toInt32 == s.block_start then
      return .block_done
  -- Fill the window with any remaining input.
  let s ← ldDState st
  let have_ : UInt32 := s.window_size - s.strstart
  let c : Bool ← if (← rdZ (← strmOf st) (·.avail_in)) > have_ then do
      pure ((← rdD st (·.block_start)) ≥ w_size.toInt32)
    else pure false
  let have_ ← if c then do
      let s ← ldDState st
      let slide_len : UInt32 := MIN32 s.block_start.toUInt32 (s.strstart - w_size)
      let bs ← chkI32 (s.block_start.toInt - slide_len.toInt32.toInt)
      wrD st fun s => { s with block_start := bs }
      wrD st fun s => { s with strstart := s.strstart - slide_len }
      Ptr.memmove window (← window.add slide_len.toNat) (← rdD st (·.strstart)).toNat
      let have_ := have_ + slide_len
      wrD st fun s => { s with insert := MIN32 s.insert s.strstart }
      pure have_
    else pure have_
  let have_ := MIN32 have_ (← rdZ (← strmOf st) (·.avail_in))
  if have_ != 0 then
    let strm ← strmOf st
    let _ ← read_buf strm (← window.add (← rdD st (·.strstart)).toNat) have_
    wrD st fun s => { s with strstart := s.strstart + have_ }
    wrD st fun s => { s with insert := s.insert + MIN32 have_ (w_size - s.insert) }
  wrD st fun s => { s with high_water := MAX32 s.high_water s.strstart }
  -- Write a stored block to pending instead, if worthy or flushing.
  let have_ ← headerBytes st
  let have_ := MIN32 ((← rdD st (·.pending_buf_size)) - have_) MAX_STORED
  let min_block := MIN32 have_ w_size
  let left ← leftOf st
  let c : Bool ← if left ≥ min_block then pure true
    else if (left != 0 || flush == Z_FINISH) && flush != Z_NO_FLUSH then do
      pure ((← rdZ (← strmOf st) (·.avail_in)) == 0 && left ≤ have_)
    else pure false
  let last ← if c then do
      let len := MIN32 left have_
      let c2 : Bool ← if flush == Z_FINISH then do
          pure ((← rdZ (← strmOf st) (·.avail_in)) == 0 && len == left)
        else pure false
      let last : Int32 := if c2 then 1 else 0
      zng_tr_stored_block st (← window.add (← rdD st (·.block_start)).toInt) len last
      let bs ← chkI32 ((← rdD st (·.block_start)).toInt + len.toInt32.toInt)
      wrD st fun s => { s with block_start := bs }
      flush_pending (← strmOf st)
      pure last
    else pure last
  if last != 0 then
    wrD st fun s => { s with bi_used := 8 }
    return .finish_started
  return .need_more

end ZlibNg.DeflateStored
