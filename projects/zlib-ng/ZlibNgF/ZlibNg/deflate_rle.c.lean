import ZlibNgF.ZlibNg.«deflate.c.fill_window»

/-!
# `deflate_rle.c` — the `Z_RLE` strategy (`ZlibNgF`)

Source: `zlib-ng/deflate_rle.c` and its helper `compare256_rle_64` of `zlib-ng/compare256_rle.h` (`OPTIMAL_CMP == 64`
on x86_64, so `compare256_rle` is `compare256_rle_64`). No `ZLIB_DEBUG`: `Assert` and `check_match` are empty.
Little-endian: `zng_memread_2` / `zng_memread_8` are `memread2` / `memread8`.

## Control flow
The `for (;;)` loop (`:32-80`) is a `cwhile` over `(lookahead, strstart, match_len, exit)`; `match_len` is a local of
the whole function (initialised at `:28`, reset to 0 after each match), so it is carried from trip to trip. A trip
ends with `RleExit.cont`, `RleExit.brk` (`break` at `:46`) or `RleExit.ret r` (`return need_more` at `:44`, or the
`return` inside `FLUSH_BLOCK` at `:78`). `scan` and `bflush` are assigned before every use in a trip. The pair of
assignments `s->lookahead = lookahead; s->strstart = strstart;` is one record update (normalisation 3).
-/

set_option autoImplicit false

namespace ZlibNg.DeflateRle
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP

/-- `Z_FORCEINLINE static uint32_t compare256_rle_64(const uint8_t *src0, const uint8_t *src1)`
(`compare256_rle.h:45-64`). Loop state `(src1, len, r)`; `r = some v` is `return v` inside the body. -/
def compare256_rle_64 (src0 src1 : BPtr) : M UInt32 := do
  let src0_cmp ← memread2 src0
  let src0_cmp32 : UInt32 := (src0_cmp.toUInt32 <<< 16) ||| src0_cmp.toUInt32
  let sv : UInt64 := (src0_cmp32.toUInt64 <<< 32) ||| src0_cmp32.toUInt64
  let (_, _, r) ← cdoWhile
    (fun ((src1, len, _) : BPtr × UInt32 × Option UInt32) => do
      let mv ← memread8 src1
      let diff := sv ^^^ mv
      if diff != 0 then return (src1, len, some (len + (← zng_first_diff_byte64 diff)))
      let src1 ← src1.add 8
      return (src1, len + 8, none))
    (fun ((src1, len, r) : BPtr × UInt32 × Option UInt32) => pure (r.isNone && len < 256, (src1, len, r)))
    (src1, (0 : UInt32), none)
  match r with
  | some v => return v
  | none => return 256

/-- `#define compare256_rle compare256_rle_64` (`deflate_rle.c:13-17`, `OPTIMAL_CMP != 8`). -/
def compare256_rle (src0 src1 : BPtr) : M UInt32 := compare256_rle_64 src0 src1

/-- How a trip of the main loop of `deflate_rle` ends. -/
inductive RleExit where
  | cont
  | brk
  | ret (r : BlockState)
  deriving Inhabited

def RleExit.isCont : RleExit → Bool
  | .cont => true
  | _ => false

/-- One trip of the `for (;;)` loop of `deflate_rle` (`deflate_rle.c:33-79`). -/
def rle_trip (st : StatePtr) (window : BPtr) (flush : Int32) (lookahead strstart match_len : UInt32) :
    M (UInt32 × UInt32 × UInt32 × RleExit) := do
  let (lookahead, strstart, ex) ← if lookahead ≤ STD_MAX_MATCH then do
      wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
      Deflate.fill_window st
      let lookahead ← rdD st (·.lookahead)
      let strstart ← rdD st (·.strstart)
      if lookahead ≤ STD_MAX_MATCH && flush == Z_NO_FLUSH then
        return (lookahead, strstart, match_len, RleExit.ret .need_more)
      if lookahead == 0 then
        return (lookahead, strstart, match_len, RleExit.brk)
      pure (lookahead, strstart, RleExit.cont)
    else pure (lookahead, strstart, RleExit.cont)
  if !ex.isCont then return (lookahead, strstart, match_len, ex)
  -- See how many times the previous byte repeats
  let match_len ← if lookahead ≥ STD_MIN_MATCH && strstart > 0 then do
      let scan ← (← window.add strstart.toNat).add (-1)
      -- `scan[0] == scan[1] && scan[1] == scan[2]` (short-circuit)
      let c ← if (← index8 scan 0) == (← index8 scan 1) then do
          pure ((← index8 scan 1) == (← index8 scan 2))
        else pure false
      if c then
        let match_len := (← compare256_rle scan (← scan.add 3)) + 2
        -- MIN(match_len, lookahead)
        pure (if match_len > lookahead then lookahead else match_len)
      else pure match_len
    else pure match_len
  -- Emit match if have run of STD_MIN_MATCH or longer, else emit literal
  let (bflush, lookahead, strstart, match_len) ← if match_len ≥ STD_MIN_MATCH then do
      let bflush ← zng_tr_tally_dist st 1 (match_len - STD_MIN_MATCH)
      pure (bflush, lookahead - match_len, strstart + match_len, (0 : UInt32))
    else do
      let bflush ← zng_tr_tally_lit st (← index8 window strstart.toNat)
      pure (bflush, lookahead - 1, strstart + 1, match_len)
  if bflush then
    wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
    if let some r ← FLUSH_BLOCK st window 0 then
      return (lookahead, strstart, match_len, .ret r)
  return (lookahead, strstart, match_len, .cont)

/-- `Z_INTERNAL block_state deflate_rle(deflate_state *s, int flush)` (`deflate_rle.c:24-91`). -/
def deflate_rle (st : StatePtr) (flush : Int32) : M BlockState := do
  let window ← (← rdD st (·.window)).get
  let match_len : UInt32 := 0
  let lookahead ← rdD st (·.lookahead)
  let strstart ← rdD st (·.strstart)
  let (lookahead, strstart, _, ex) ← cwhile
    (fun (v : UInt32 × UInt32 × UInt32 × RleExit) => pure (v.2.2.2.isCont, v))
    (fun ((lookahead, strstart, match_len, _) : UInt32 × UInt32 × UInt32 × RleExit) =>
      rle_trip st window flush lookahead strstart match_len)
    (lookahead, strstart, match_len, RleExit.cont)
  if let .ret r := ex then return r
  wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
  wrD st fun s => { s with insert := 0 }
  if flush == Z_FINISH then
    if let some r ← FLUSH_BLOCK st window 1 then return r
    return .finish_done
  if (← rdD st (·.sym_next)) != 0 then
    if let some r ← FLUSH_BLOCK st window 0 then return r
  return .block_done

end ZlibNg.DeflateRle
