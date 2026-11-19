import ZlibNgF.ZlibNg.«deflate.c.fill_window»

/-!
# `deflate_slow.c` — the slow (lazy) strategy of deflate (`ZlibNgF`)

Source: `zlib-ng/deflate_slow.c` (verified configuration: no `ZLIB_DEBUG`, so `Assert` and `check_match` are empty;
`MIN_ROLL_LEVEL` is 9; `LIKELY` / `UNLIKELY` are branch hints; `Z_UNUSED(x)` evaluates `x`). The calls
`longest_match(s, hash_head)` and `insert_batch(...)` go through the function pointers read from
`s->longest_match` / `s->insert_batch` at entry (`call_longest_match`, `call_insert_batch`); `PREFIX(fill_window)` =
`fill_window`.

## Control flow
The `for (;;)` (`deflate_slow.c:31-152`) is a `cwhile` whose body (`deflate_slow_trip`) is one trip and ends with a
`Ctl`: `cont` (next trip), `brk` (`break` at `:43`) or `ret r` (`return need_more` at `:40` and `:142`, or the
`return` inside `FLUSH_BLOCK`). `int bflush;` is written before each read, in the branch that reads it; it is a
local of the branch in the model.

`int64_t dist = (int64_t)s->strstart - hash_head;` converts `hash_head` to `int64_t` and cannot overflow; it is an
`Int`. `MAX(a, b)` is `((a) < (b) ? (b) : (a))`, `MIN(a, b)` is `((a) > (b) ? (b) : (a))`.
-/

set_option autoImplicit false

namespace ZlibNg.DeflateSlow
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP ZlibNg.InsertStringP ZlibNg.InsertString ZlibNg.Compare256

/-- How one trip of a `for (;;)` loop ends: the next trip, `break`, or `return r`. -/
inductive Ctl where
  | cont
  | brk
  | ret (r : BlockState)
  deriving DecidableEq, Repr, Inhabited

/-- One trip of the `for (;;)` of `deflate_slow` (`deflate_slow.c:31-152`). -/
def deflate_slow_trip (st : StatePtr) (flush : Int32) (longest_match : LongestMatchFn)
    (insert_batch : InsertBatchFn) (window : BPtr) (level : Int32) (match_discard match_floor : UInt32) :
    M Ctl := do
  if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD then
    ZlibNg.Deflate.fill_window st
    if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD && flush == Z_NO_FLUSH then
      return .ret .need_more
    if (← rdD st (·.lookahead)) == 0 then
      return .brk
  let mut hash_head : UInt32 := 0
  if (← rdD st (·.lookahead)) ≥ WANT_MIN_MATCH then
    if level ≥ MIN_ROLL_LEVEL then
      hash_head ← insert_roll st window (← rdD st (·.strstart))
    else
      hash_head ← insert_knuth st window (← rdD st (·.strstart))
  -- s->prev_match = s->match_start;
  wrD st fun s => { s with prev_match := s.match_start }
  let prev_length ← rdD st (·.prev_length)
  let mut match_len : UInt32 := STD_MIN_MATCH - 1
  let dist : Int := ((← rdD st (·.strstart)).toNat : Int) - (hash_head.toNat : Int)
  let s ← ldDState st
  if dist ≤ ((MAX_DIST s).toNat : Int) && dist > 0 && prev_length < s.max_lazy_match && hash_head != 0 then
    -- s->prev_length = MAX(prev_length, match_floor);
    wrD st fun s => { s with prev_length := if prev_length < match_floor then match_floor else prev_length }
    match_len ← call_longest_match longest_match st hash_head
    wrD st fun s => { s with prev_length := prev_length }
    if match_len ≤ match_discard then
      match_len := STD_MIN_MATCH - 1
  let s ← ldDState st
  if s.prev_length ≥ STD_MIN_MATCH && match_len ≤ s.prev_length then
    -- unsigned int max_insert = s->strstart + s->lookahead - STD_MIN_MATCH;
    let max_insert : UInt32 := s.strstart + s.lookahead - STD_MIN_MATCH
    let bflush ← zng_tr_tally_dist st (s.strstart - 1 - s.prev_match) (s.prev_length - STD_MIN_MATCH)
    wrD st fun s => { s with prev_length := s.prev_length - 1 }
    wrD st fun s => { s with lookahead := s.lookahead - s.prev_length }
    let mov_fwd : UInt32 := (← rdD st (·.prev_length)) - 1
    if max_insert > (← rdD st (·.strstart)) then
      let mut insert_cnt : UInt32 := mov_fwd
      if insert_cnt > max_insert - (← rdD st (·.strstart)) then
        insert_cnt := max_insert - (← rdD st (·.strstart))
      let s ← ldDState st
      let match_dist : UInt32 := s.strstart - 1 - s.prev_match
      -- uint32_t tail_cnt = MAX(match_dist + 2, 64);
      let tail_cnt : UInt32 := if match_dist + 2 < 64 then 64 else match_dist + 2
      if tail_cnt ≥ insert_cnt then
        call_insert_batch insert_batch st window ((← rdD st (·.strstart)) + 1) insert_cnt
      else if level ≥ MIN_ROLL_LEVEL then
        insert_roll_batch_tail_static st window ((← rdD st (·.strstart)) + 1) insert_cnt tail_cnt
      else
        insert_knuth_batch_tail_static st window ((← rdD st (·.strstart)) + 1) insert_cnt tail_cnt
    wrD st fun s => { s with prev_length := 0 }
    wrD st fun s => { s with match_available := 0 }
    wrD st fun s => { s with strstart := s.strstart + (mov_fwd + 1) }
    if bflush then
      match ← FLUSH_BLOCK st window 0 with
      | some r => return .ret r
      | none => pure ()
  else if s.match_available != 0 then
    -- bflush = zng_tr_tally_lit(s, window[s->strstart-1]);
    let bflush ← zng_tr_tally_lit st (← index8 window ((← rdD st (·.strstart)) - 1).toNat)
    if bflush then
      FLUSH_BLOCK_ONLY st (pure window) 0
    wrD st fun s => { s with prev_length := match_len }
    wrD st fun s => { s with strstart := s.strstart + 1 }
    wrD st fun s => { s with lookahead := s.lookahead - 1 }
    let strm ← (← rdD st (·.strm)).get
    if (← rdZ strm (·.avail_out)) == 0 then
      return .ret .need_more
  else
    wrD st fun s => { s with prev_length := match_len }
    wrD st fun s => { s with match_available := 1 }
    wrD st fun s => { s with strstart := s.strstart + 1 }
    wrD st fun s => { s with lookahead := s.lookahead - 1 }
  return .cont

/-- `Z_INTERNAL block_state deflate_slow(deflate_state *s, int flush)` (`deflate_slow.c:17-166`). -/
def deflate_slow (st : StatePtr) (flush : Int32) : M BlockState := do
  let longest_match ← (← rdD st (·.longest_match)).get
  let insert_batch ← (← rdD st (·.insert_batch)).get
  let window ← (← rdD st (·.window)).get
  let level ← rdD st (·.level)
  -- const uint32_t match_discard = (s->strategy == Z_FILTERED) ? 5 : 0;
  let match_discard : UInt32 := if (← rdD st (·.strategy)) == Z_FILTERED then 5 else 0
  -- const uint32_t match_floor = MIN(match_discard, s->good_match - 1);
  let gm1 : UInt32 := (← rdD st (·.good_match)) - 1
  let match_floor : UInt32 := if match_discard > gm1 then gm1 else match_discard
  let c ← cwhile
    (fun (c : Ctl) => pure (c matches .cont, c))
    (fun (_ : Ctl) =>
      deflate_slow_trip st flush longest_match insert_batch window level match_discard match_floor)
    Ctl.cont
  if let .ret r := c then
    return r
  if (← rdD st (·.match_available)) != 0 then
    -- Z_UNUSED(zng_tr_tally_lit(s, window[s->strstart-1]));
    let _ ← zng_tr_tally_lit st (← index8 window ((← rdD st (·.strstart)) - 1).toNat)
    wrD st fun s => { s with match_available := 0 }
  wrD st fun s => { s with insert := if s.strstart < STD_MIN_MATCH - 1 then s.strstart else STD_MIN_MATCH - 1 }
  if flush == Z_FINISH then
    match ← FLUSH_BLOCK st window 1 with
    | some r => return r
    | none => pure ()
    return .finish_done
  if (← rdD st (·.sym_next)) != 0 then
    match ← FLUSH_BLOCK st window 0 with
    | some r => return r
    | none => pure ()
  return .block_done

end ZlibNg.DeflateSlow
