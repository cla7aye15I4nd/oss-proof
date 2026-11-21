import ZlibNgF.ZlibNg.«deflate.c.fill_window»

/-!
# `deflate_fast.c` — the fast strategy of deflate (`ZlibNgF`)

Source: `zlib-ng/deflate_fast.c` (verified configuration: no `ZLIB_DEBUG`, so `Assert` and `check_match` are empty;
little-endian, so `Z_U32_FROM_LE` is the identity; `LIKELY` / `UNLIKELY` are branch hints).
`FUNCTABLE_CALL(longest_match)` = `longest_match_c`; `PREFIX(fill_window)` = `fill_window`.

## Control flow
The outer `for (;;)` is a `cwhile` whose body (`deflate_fast_trip`) is one trip and ends with a `Ctl`:
`cont` (next trip), `brk` (`break` at `deflate_fast.c:41`) or `ret r` (`return need_more` at `:38`, or the `return`
inside `FLUSH_BLOCK`). The inner `for (;;)` of max-length continuations (`:92-115`) is a `cwhile` whose body is
`deflate_fast_cont_trip`. `bflush` and `match_len` are function-scope locals and are threaded through the loops.

## Uninitialised locals
`uint8_t lc;` is written on both branches of `:48-66` before its only read at `:121`; the model starts it at `0`,
which is never observable.
-/

set_option autoImplicit false

namespace ZlibNg.DeflateFast
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP ZlibNg.InsertStringP ZlibNg.InsertString ZlibNg.Compare256

/-- How one trip of a `for (;;)` loop ends: the next trip, `break`, or `return r`. -/
inductive Ctl where
  | cont
  | brk
  | ret (r : BlockState)
  deriving DecidableEq, Repr, Inhabited

/-- One trip of the inner `for (;;)` of `deflate_fast` (`deflate_fast.c:92-115`): the continuation of a
max-length match at the distance `cont_dist`. Returns how the trip ends and the new `bflush`. -/
def deflate_fast_cont_trip (st : StatePtr) (window : BPtr) (max_inserts cont_dist : UInt32) (bflush : Bool) :
    M (Ctl × Bool) := do
  let mut bflush := bflush
  -- uint32_t cont_len = max_match_continues(window, s->strstart, cont_dist);
  let cont_len ← max_match_continues window (← rdD st (·.strstart)) cont_dist
  if cont_len < 8 then
    return (.brk, bflush)
  -- insert_knuth_spread_static(s, window, s->strstart, cont_len, max_inserts);
  insert_knuth_spread_static st window (← rdD st (·.strstart)) cont_len max_inserts
  wrD st fun s => { s with strstart := s.strstart + cont_len }
  wrD st fun s => { s with lookahead := s.lookahead - cont_len }
  -- bflush |= zng_tr_tally_dist(s, cont_dist, cont_len - STD_MIN_MATCH);
  let b ← zng_tr_tally_dist st cont_dist (cont_len - STD_MIN_MATCH)
  bflush := bflush || b
  if bflush then
    match ← FLUSH_BLOCK st window 0 with
    | some r => return (.ret r, bflush)
    | none => pure ()
    bflush := false
  if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD then
    return (.brk, bflush)
  return (.cont, bflush)

/-- One trip of the outer `for (;;)` of `deflate_fast` (`deflate_fast.c:27-127`). The loop state is
`(bflush, match_len)`. -/
def deflate_fast_trip (st : StatePtr) (flush : Int32) (window : BPtr) (max_inserts : UInt32)
    (bflush : Bool) (match_len : UInt32) : M (Ctl × Bool × UInt32) := do
  let mut bflush := bflush
  let mut match_len := match_len
  let mut lc : UInt8 := 0
  if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD then
    ZlibNg.Deflate.fill_window st
    if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD && flush == Z_NO_FLUSH then
      return (.ret .need_more, bflush, match_len)
    if (← rdD st (·.lookahead)) == 0 then
      return (.brk, bflush, match_len)
  if (← rdD st (·.lookahead)) ≥ WANT_MIN_MATCH then
    -- uint32_t str_val = Z_U32_FROM_LE(zng_memread_4(window + s->strstart));
    let str_val ← memread4 (← window.add (← rdD st (·.strstart)).toNat)
    -- uint32_t hash_head = insert_knuth_val(s, s->strstart, str_val);
    let hash_head ← insert_knuth_val st (← rdD st (·.strstart)) str_val
    -- int64_t dist = (int64_t)s->strstart - hash_head;   (no overflow in int64_t)
    let dist : Int := ((← rdD st (·.strstart)).toNat : Int) - (hash_head.toNat : Int)
    lc := str_val.toUInt8
    let s ← ldDState st
    if dist ≤ ((MAX_DIST s).toNat : Int) && dist > 0 && hash_head != 0 then
      match_len ← longest_match_c st hash_head
  else
    lc ← index8 window (← rdD st (·.strstart)).toNat
  if match_len ≥ WANT_MIN_MATCH then
    -- const uint32_t cont_dist = s->strstart - s->match_start;
    let s ← ldDState st
    let cont_dist : UInt32 := s.strstart - s.match_start
    bflush ← zng_tr_tally_dist st cont_dist (match_len - STD_MIN_MATCH)
    wrD st fun s => { s with lookahead := s.lookahead - match_len }
    if (← rdD st (·.lookahead)) ≥ WANT_MIN_MATCH then
      insert_knuth_spread_static st window ((← rdD st (·.strstart)) + 1) (match_len - 1) max_inserts
    else
      let _ ← insert_knuth st window ((← rdD st (·.strstart)) + 2 - STD_MIN_MATCH + match_len)
    wrD st fun s => { s with strstart := s.strstart + match_len }
    if match_len == STD_MAX_MATCH then
      if (← rdD st (·.lookahead)) ≥ MIN_LOOKAHEAD then
        let (c, bf) ← cwhile
          (fun (x : Ctl × Bool) => pure (x.1 matches .cont, x))
          (fun (x : Ctl × Bool) => deflate_fast_cont_trip st window max_inserts cont_dist x.2)
          (Ctl.cont, bflush)
        bflush := bf
        if let .ret r := c then
          return (.ret r, bflush, match_len)
    match_len := 0
  else
    bflush ← zng_tr_tally_lit st lc
    wrD st fun s => { s with lookahead := s.lookahead - 1 }
    wrD st fun s => { s with strstart := s.strstart + 1 }
  if bflush then
    match ← FLUSH_BLOCK st window 0 with
    | some r => return (.ret r, bflush, match_len)
    | none => pure ()
  return (.cont, bflush, match_len)

/-- `Z_INTERNAL block_state deflate_fast(deflate_state *s, int flush)` (`deflate_fast.c:21-137`). -/
def deflate_fast (st : StatePtr) (flush : Int32) : M BlockState := do
  let window ← (← rdD st (·.window)).get
  -- uint32_t max_inserts = MAX(2, s->max_insert_count);   (max_insert_count is max_lazy_match)
  let mic ← rdD st (·.max_lazy_match)
  let max_inserts : UInt32 := if 2 < mic then mic else 2
  let bflush : Bool := false
  let match_len : UInt32 := 0
  let (c, _, _) ← cwhile
    (fun (x : Ctl × Bool × UInt32) => pure (x.1 matches .cont, x))
    (fun (x : Ctl × Bool × UInt32) => deflate_fast_trip st flush window max_inserts x.2.1 x.2.2)
    (Ctl.cont, bflush, match_len)
  if let .ret r := c then
    return r
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

end ZlibNg.DeflateFast
