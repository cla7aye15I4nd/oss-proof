import ZlibNgF.ZlibNg.«deflate.c.fill_window»

/-!
# `deflate_huff.c` — the `Z_HUFFMAN_ONLY` strategy (`ZlibNgF`)

Source: `zlib-ng/deflate_huff.c`. `PREFIX(fill_window)` is `fill_window` (`deflate.c.fill_window.lean`).

## Control flow
The `for (;;)` loop (`:22-46`) is a `cwhile` over `(lookahead, strstart, exit)`; a trip ends with
`HuffExit.cont` (next trip), `HuffExit.brk` (`break` at `:33`) or `HuffExit.ret r` (`return need_more` at `:32`, or
the `return` inside `FLUSH_BLOCK` at `:44`). The local `bflush` is assigned before every use in a trip. The pair of
assignments `s->lookahead = lookahead; s->strstart = strstart;` is one record update (normalisation 3).
-/

set_option autoImplicit false

namespace ZlibNg.DeflateHuff
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP

/-- How a trip of the main loop of `deflate_huff` ends. -/
inductive HuffExit where
  | cont
  | brk
  | ret (r : BlockState)
  deriving Inhabited

def HuffExit.isCont : HuffExit → Bool
  | .cont => true
  | _ => false

/-- One trip of the `for (;;)` loop of `deflate_huff` (`deflate_huff.c:23-45`). -/
def huff_trip (st : StatePtr) (window : BPtr) (flush : Int32) (lookahead strstart : UInt32) :
    M (UInt32 × UInt32 × HuffExit) := do
  -- Make sure that we have a literal to write.
  let (lookahead, strstart, ex) ← if lookahead == 0 then do
      wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
      Deflate.fill_window st
      let lookahead ← rdD st (·.lookahead)
      let strstart ← rdD st (·.strstart)
      if lookahead == 0 then
        if flush == Z_NO_FLUSH then
          return (lookahead, strstart, HuffExit.ret .need_more)
        return (lookahead, strstart, HuffExit.brk)
      pure (lookahead, strstart, HuffExit.cont)
    else pure (lookahead, strstart, HuffExit.cont)
  if !ex.isCont then return (lookahead, strstart, ex)
  -- Output a literal byte
  let bflush ← zng_tr_tally_lit st (← index8 window strstart.toNat)
  let lookahead := lookahead - 1
  let strstart := strstart + 1
  if bflush then
    wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
    if let some r ← FLUSH_BLOCK st window 0 then
      return (lookahead, strstart, .ret r)
  return (lookahead, strstart, .cont)

/-- `Z_INTERNAL block_state deflate_huff(deflate_state *s, int flush)` (`deflate_huff.c:16-57`). -/
def deflate_huff (st : StatePtr) (flush : Int32) : M BlockState := do
  let window ← (← rdD st (·.window)).get
  let lookahead ← rdD st (·.lookahead)
  let strstart ← rdD st (·.strstart)
  let (lookahead, strstart, ex) ← cwhile
    (fun (v : UInt32 × UInt32 × HuffExit) => pure (v.2.2.isCont, v))
    (fun ((lookahead, strstart, _) : UInt32 × UInt32 × HuffExit) =>
      huff_trip st window flush lookahead strstart)
    (lookahead, strstart, HuffExit.cont)
  if let .ret r := ex then return r
  wrD st fun s => { s with lookahead := lookahead, strstart := strstart }
  wrD st fun s => { s with insert := 0 }
  if flush == Z_FINISH then
    if let some r ← FLUSH_BLOCK st window 1 then return r
    return .finish_done
  if (← rdD st (·.sym_next)) != 0 then
    if let some r ← FLUSH_BLOCK st window 0 then return r
  return .block_done

end ZlibNg.DeflateHuff
