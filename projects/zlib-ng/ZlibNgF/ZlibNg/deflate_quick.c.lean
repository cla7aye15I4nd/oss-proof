import ZlibNgF.ZlibNg.«deflate.c.fill_window»

/-!
# `deflate_quick.c` — the quick (level 1) strategy (`ZlibNgF`)

Source: `zlib-ng/deflate_quick.c` (no `ZLIB_DEBUG`: `Assert` and `check_match` are empty; little-endian:
`Z_U32_FROM_LE` is the identity, `zng_memread_4` is `memread4`). `static_ltree` / `static_dtree` are the read-only
`.ref .static_ltree 0` / `.ref .static_dtree 0`. `FUNCTABLE_CALL(compare256)` is `compare256_c`.

The `Z_FORCEINLINE` helpers return an `int` that the callers only test for non-zero; here they return `Bool`
(`true` ↔ non-zero). The `uint32_t *strstart`, `uint32_t *lookahead` parameters of `quick_emit_lit` /
`quick_emit_dist` point to locals of `deflate_quick_impl`: they are passed by value and the new values returned
(normalisation 1). The `const int static_emit` parameter is kept as an `Int32` and tested against 0.
`(BIT_BUF_SIZE + 7) >> 3` is the `int` constant 8, converted to `unsigned` in the sum with `s->pending`.

## Control flow of `deflate_quick_impl`
The outer `for (;;)` (`:141-224`) is a `cwhile` over `(strstart, lookahead, exit)`; a trip ends with
`QuickExit.cont` (end of the body or `continue` at `:216`), `QuickExit.brk` (`break` at `:157`) or
`QuickExit.ret r` (a `return` inside the loop). The inner `for (;;)` (`:195-213`) is a `cwhile` over
`(strstart, lookahead, exit)` with the same encoding (`brk` for its three `break`s, `ret need_more` at `:209`).
-/

set_option autoImplicit false

namespace ZlibNg.DeflateQuick
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP ZlibNg.TreesEmit ZlibNg.InsertStringP

/-- `extern const ct_data static_ltree[L_CODES+2];` -/
def static_ltree_p : CtPtr := .ref .static_ltree 0
/-- `extern const ct_data static_dtree[D_CODES];` -/
def static_dtree_p : CtPtr := .ref .static_dtree 0

/-- `s->strm` -/
def strmOf (st : StatePtr) : M StreamPtr := do (← ldDState st).strm.get

/-- `Z_FORCEINLINE static int quick_end_block(deflate_state *s, uint32_t strstart, int last, const int static_emit)`
(`deflate_quick.c:32-50`). `FLUSH_BLOCK_ONLY(s, s->window, last)` reads `s->window` before the macro body (in C it
is read inside the macro, only when `s->block_start >= 0`). -/
def quick_end_block (st : StatePtr) (strstart : UInt32) (last : Int32) (static_emit : Int32) : M Bool := do
  if static_emit == 0 then
    -- Tallied symbols are coded by the flush, with trees built for the block
    let c ← if last != 0 then pure true else do pure ((← rdD st (·.sym_next)) != 0)
    if c then
      FLUSH_BLOCK_ONLY st (← (← rdD st (·.window)).get) last
      return (← rdZ (← strmOf st) (·.avail_out)) == 0
    return false
  if (← rdD st (·.block_open)) != 0 then
    zng_tr_emit_end_block st static_ltree_p last
    wrD st fun s => { s with block_open := 0 }
    wrD st fun s => { s with block_start := strstart.toInt32 }
    flush_pending (← strmOf st)
    return (← rdZ (← strmOf st) (·.avail_out)) == 0
  return false

/-- `Z_FORCEINLINE static int quick_start_block(deflate_state *s, uint32_t strstart, uint32_t lookahead, int last,
const int static_emit)` (`deflate_quick.c:53-71`). `s->block_open = 1 + last` is `int` arithmetic (checked),
converted to `unsigned int`. -/
def quick_start_block (st : StatePtr) (strstart lookahead : UInt32) (last : Int32) (static_emit : Int32) :
    M Bool := do
  -- Tallied blocks get their header from the flush
  if static_emit == 0 then
    return false
  let c ← if last != 0 then do pure ((← rdD st (·.block_open)) == 1) else pure false
  if c then
    -- Emit end of previous block so the last block can carry the final bit
    if ← quick_end_block st strstart 0 static_emit then
      return true
  -- `s->block_open == 0 && (last || lookahead > 0)`
  if (← rdD st (·.block_open)) == 0 && (last != 0 || lookahead > 0) then
    ZlibNg.TreesEmit.zng_tr_emit_tree st ZlibNg.Trees.STATIC_TREES last
    let bo ← chkI32 (1 + last.toInt)
    wrD st fun s => { s with block_open := bo.toUInt32 }
    wrD st fun s => { s with block_start := strstart.toInt32 }
  return false

/-- `Z_FORCEINLINE static int quick_flush_pending(deflate_state *s, const int static_emit)`
(`deflate_quick.c:75-84`). -/
def quick_flush_pending (st : StatePtr) (static_emit : Int32) : M Bool := do
  -- Tallied symbols reach the pending buffer only at the block flush
  if static_emit == 0 then
    return false
  let s ← ldDState st
  if s.pending + 8 ≥ s.pending_buf_size then
    flush_pending (← strmOf st)
    return (← rdZ (← strmOf st) (·.avail_out)) == 0
  return false

/-- `Z_FORCEINLINE static int quick_emit_lit(deflate_state *s, uint8_t lit, uint32_t *strstart, uint32_t *lookahead,
const int static_emit)` (`deflate_quick.c:87-104`). Returns `(result, *strstart, *lookahead)`. -/
def quick_emit_lit (st : StatePtr) (lit : UInt8) (strstart lookahead : UInt32) (static_emit : Int32) :
    M (Bool × UInt32 × UInt32) := do
  if static_emit != 0 then
    zng_tr_emit_lit st static_ltree_p lit.toUInt32
    let strstart := strstart + 1
    let lookahead := lookahead - 1
    return (false, strstart, lookahead)
  let bflush ← zng_tr_tally_lit st lit
  let strstart := strstart + 1
  let lookahead := lookahead - 1
  if bflush then
    wrD st fun s => { s with strstart := strstart, lookahead := lookahead }
    return (← quick_end_block st strstart 0 static_emit, strstart, lookahead)
  return (false, strstart, lookahead)

/-- `Z_FORCEINLINE static int quick_emit_dist(deflate_state *s, uint32_t match_len, uint32_t dist,
uint32_t *strstart, uint32_t *lookahead, const int static_emit)` (`deflate_quick.c:107-124`). Returns
`(result, *strstart, *lookahead)`. -/
def quick_emit_dist (st : StatePtr) (match_len dist : UInt32) (strstart lookahead : UInt32) (static_emit : Int32) :
    M (Bool × UInt32 × UInt32) := do
  if static_emit != 0 then
    zng_tr_emit_dist st static_ltree_p static_dtree_p (match_len - STD_MIN_MATCH) dist
    let lookahead := lookahead - match_len
    let strstart := strstart + match_len
    return (false, strstart, lookahead)
  let bflush ← zng_tr_tally_dist st dist (match_len - STD_MIN_MATCH)
  let lookahead := lookahead - match_len
  let strstart := strstart + match_len
  if bflush then
    wrD st fun s => { s with strstart := strstart, lookahead := lookahead }
    return (← quick_end_block st strstart 0 static_emit, strstart, lookahead)
  return (false, strstart, lookahead)

/-- How a trip of a `for (;;)` loop of `deflate_quick_impl` ends. -/
inductive QuickExit where
  | cont
  | brk
  | ret (r : BlockState)
  deriving Inhabited

def QuickExit.isCont : QuickExit → Bool
  | .cont => true
  | _ => false

/-- One trip of the continuation loop `for (;;)` of `deflate_quick_impl` (`deflate_quick.c:196-212`). -/
def quick_cont_trip (st : StatePtr) (window : BPtr) (static_emit : Int32) (cont_dist : UInt32)
    (strstart lookahead : UInt32) : M (UInt32 × UInt32 × QuickExit) := do
  -- Direct emission needs room, let the main loop flush pending
  if static_emit != 0 then
    let s ← ldDState st
    if s.pending + 8 ≥ s.pending_buf_size then
      return (strstart, lookahead, .brk)
  -- Check for continuing match
  let cont_len ← max_match_continues window strstart cont_dist
  if cont_len < 8 then
    return (strstart, lookahead, .brk)
  -- Emit match
  let (r, strstart, lookahead) ← quick_emit_dist st cont_len cont_dist strstart lookahead static_emit
  if r then
    return (strstart, lookahead, .ret .need_more)
  if lookahead < MIN_LOOKAHEAD then
    return (strstart, lookahead, .brk)
  return (strstart, lookahead, .cont)

/-- The match part of a trip of the main loop (`deflate_quick.c:168-220`): `some` is the end of the trip
(`continue` at `:216` or a `return`), `none` falls through to the literal at `:222`. -/
def quick_try_match (st : StatePtr) (window : BPtr) (static_emit : Int32) (strstart lookahead str_val : UInt32) :
    M (Option (UInt32 × UInt32 × QuickExit)) := do
  if lookahead ≥ WANT_MIN_MATCH then
    let hash_head ← insert_knuth_val_head st strstart str_val
    -- `int64_t dist = (int64_t)strstart - hash_head;` (`hash_head` converted to `int64_t`; no overflow)
    let dist : Int64 := strstart.toUInt64.toInt64 - hash_head.toUInt64.toInt64
    -- `dist <= MAX_DIST(s)`: the `unsigned` `MAX_DIST(s)` is converted to `int64_t`
    let maxd := MAX_DIST (← ldDState st)
    if dist ≤ maxd.toUInt64.toInt64 && dist > 0 then
      let match_start ← window.add hash_head.toNat
      let match_val ← memread4 match_start
      if str_val == match_val then
        let scan_start ← window.add strstart.toNat
        let match_len := (← ZlibNg.Compare256.compare256_c (← scan_start.add 2) (← match_start.add 2)) + 2
        if match_len ≥ WANT_MIN_MATCH then
          let match_len := if match_len > lookahead then lookahead else match_len
          let (r, strstart, lookahead) ←
            quick_emit_dist st match_len dist.toUInt64.toUInt32 strstart lookahead static_emit
          if r then
            return some (strstart, lookahead, .ret .need_more)
          -- A max-length match might continue
          if match_len == STD_MAX_MATCH && lookahead ≥ MIN_LOOKAHEAD then
            let cont_dist : UInt32 := dist.toUInt64.toUInt32
            let (strstart, lookahead, ex) ← cwhile
              (fun (v : UInt32 × UInt32 × QuickExit) => pure (v.2.2.isCont, v))
              (fun ((strstart, lookahead, _) : UInt32 × UInt32 × QuickExit) =>
                quick_cont_trip st window static_emit cont_dist strstart lookahead)
              (strstart, lookahead, QuickExit.cont)
            if let .ret r := ex then
              return some (strstart, lookahead, .ret r)
            return some (strstart, lookahead, .cont)
          return some (strstart, lookahead, .cont)
  return none

/-- One trip of the main `for (;;)` loop of `deflate_quick_impl` (`deflate_quick.c:142-223`). -/
def quick_trip (st : StatePtr) (window : BPtr) (flush : Int32) (last : UInt32) (static_emit : Int32)
    (strstart lookahead : UInt32) : M (UInt32 × UInt32 × QuickExit) := do
  if ← quick_flush_pending st static_emit then
    wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
    -- `last && s->strm->avail_in == 0 && s->bi_valid == 0 && s->block_open == 0` (short-circuit)
    let c ← if last != 0 then do
        if (← rdZ (← strmOf st) (·.avail_in)) == 0 then do
          if (← rdD st (·.bi_valid)) == 0 then do
            pure ((← rdD st (·.block_open)) == 0)
          else pure false
        else pure false
      else pure false
    return (strstart, lookahead, .ret (if c then .finish_started else .need_more))
  let (strstart, lookahead, ex) ← if lookahead < MIN_LOOKAHEAD then do
      wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
      Deflate.fill_window st
      let lookahead ← rdD st (·.lookahead)
      let strstart ← rdD st (·.strstart)
      if lookahead < MIN_LOOKAHEAD && flush == Z_NO_FLUSH then
        return (strstart, lookahead, QuickExit.ret .need_more)
      if lookahead == 0 then
        return (strstart, lookahead, QuickExit.brk)
      if (← rdD st (·.block_open)) == 0 then
        -- Start new block when we have lookahead data
        let _ ← quick_start_block st strstart lookahead last.toInt32 static_emit
      pure (strstart, lookahead, QuickExit.cont)
    else pure (strstart, lookahead, QuickExit.cont)
  if !ex.isCont then return (strstart, lookahead, ex)
  let str_val ← memread4 (← window.add strstart.toNat)
  if let some r ← quick_try_match st window static_emit strstart lookahead str_val then
    return r
  let (r, strstart, lookahead) ← quick_emit_lit st str_val.toUInt8 strstart lookahead static_emit
  if r then
    return (strstart, lookahead, .ret .need_more)
  return (strstart, lookahead, .cont)

/-- `Z_FORCEINLINE static block_state deflate_quick_impl(deflate_state *s, int flush, const int static_emit)`
(`deflate_quick.c:127-238`). `last` is an `unsigned`; it is converted to `int` (GCC modulo) at the `int last`
parameters of `quick_start_block`. -/
def deflate_quick_impl (st : StatePtr) (flush : Int32) (static_emit : Int32) : M BlockState := do
  let strstart ← rdD st (·.strstart)
  let lookahead ← rdD st (·.lookahead)
  let last : UInt32 := if flush == Z_FINISH then 1 else 0
  if ← quick_start_block st strstart lookahead last.toInt32 static_emit then
    return .need_more
  let window ← (← rdD st (·.window)).get
  let (strstart, lookahead, ex) ← cwhile
    (fun (v : UInt32 × UInt32 × QuickExit) => pure (v.2.2.isCont, v))
    (fun ((strstart, lookahead, _) : UInt32 × UInt32 × QuickExit) =>
      quick_trip st window flush last static_emit strstart lookahead)
    (strstart, lookahead, QuickExit.cont)
  if let .ret r := ex then return r
  wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
  wrD st fun s => { s with insert := if strstart < STD_MIN_MATCH - 1 then strstart else STD_MIN_MATCH - 1 }
  if last != 0 then
    if ← quick_end_block st strstart 1 static_emit then
      return .finish_started
    return .finish_done
  if ← quick_end_block st strstart 0 static_emit then
    return .need_more
  return .block_done

/-- `Z_INTERNAL block_state deflate_quick(deflate_state *s, int flush)` (`deflate_quick.c:240-246`). -/
def deflate_quick (st : StatePtr) (flush : Int32) : M BlockState := do
  -- Z_FIXED path: every symbol goes straight through the static tables.
  if (← rdD st (·.strategy)) == Z_FIXED then
    return ← deflate_quick_impl st flush 1
  -- Default path: symbols are tallied so the flush builds per-block trees.
  deflate_quick_impl st flush 0

end ZlibNg.DeflateQuick
