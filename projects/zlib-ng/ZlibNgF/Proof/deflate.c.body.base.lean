import ZlibNgF.Proof.«deflate.c.params»

/-!
# `deflate`: the body in parts (`ZlibNgF`)

`deflate_eq` restates `deflate` (by `rfl`) as the argument checks followed by named parts, so that the proofs walk one
small term at a time: `bodyA` (the pending output and the `Z_BUF_ERROR` of a repeated flush), `bodyB` (the finished
stream with input, the raw stream's `INIT_STATE`, the header), `bodyC` (the strategy call and its block tails),
`bodyD` (the trailer).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP

/-- The trailer (`deflate.c:1100-1118`). -/
def bodyD (st : StatePtr) (strm : StreamPtr) (flush : Int32) : M Int32 := do
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

/-- What follows the strategy call (`deflate.c:1071-1098`). -/
def afterStrat (bstate : BlockState) (st : StatePtr) (strm : StreamPtr) (flush : Int32) : M Int32 := do
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
  bodyD st strm flush

/-- The strategy part (`deflate.c:1060-1098`). -/
def bodyC (st : StatePtr) (strm : StreamPtr) (flush : Int32) : M Int32 := do
  let s ← ldDState st
  if (← rdZ strm (·.avail_in)) != 0 || s.lookahead != 0 || (flush != Z_NO_FLUSH && s.status != FINISH_STATE) then
    let s ← ldDState st
    if s.level == 0 then
      let bstate ← ZlibNg.DeflateStored.deflate_stored st flush
      afterStrat bstate st strm flush
    else if s.strategy == Z_HUFFMAN_ONLY then
      let bstate ← ZlibNg.DeflateHuff.deflate_huff st flush
      afterStrat bstate st strm flush
    else if s.strategy == Z_RLE then
      let bstate ← ZlibNg.DeflateRle.deflate_rle st flush
      afterStrat bstate st strm flush
    else
      let bstate ← call_compress (← config s.level).func st flush
      afterStrat bstate st strm flush
  else
    bodyD st strm flush

/-- The finished stream with input, the raw stream's `INIT_STATE`, the header (`deflate.c:1040-1058`). -/
def bodyB (st : StatePtr) (strm : StreamPtr) (flush : Int32) : M Int32 := do
  if (← rdD st (·.status)) == FINISH_STATE && (← rdZ strm (·.avail_in)) != 0 then
    return ← ERR_RETURN strm Z_BUF_ERROR
  let s ← ldDState st
  if s.status == INIT_STATE && s.wrap == 0 then
    wrD st fun s => { s with status := BUSY_STATE }
  let s ← ldDState st
  if s.status != BUSY_STATE && s.status != FINISH_STATE && s.wrap != 0 then
    if (← deflateHeaders st strm) == Z_OK then return Z_OK
  bodyC st strm flush

/-- The pending output and the repeated flush (`deflate.c:1018-1038`). -/
def bodyA (st : StatePtr) (strm : StreamPtr) (flush old_flush : Int32) : M Int32 := do
  if (← rdD st (·.pending)) != 0 then
    flush_pending_inline strm
    if (← rdZ strm (·.avail_out)) == 0 then
      wrD st fun s => { s with last_flush := -1 }
      return Z_OK
  else if (← rdZ strm (·.avail_in)) == 0 && (← RANK flush) ≤ (← RANK old_flush) && flush != Z_FINISH then
    return ← ERR_RETURN strm Z_BUF_ERROR
  bodyB st strm flush

theorem deflate_eq (strm : StreamPtr) (flush : Int32) :
    deflate strm flush = (do
      if (← deflateStateCheck strm) || flush > Z_BLOCK || flush < 0 then return Z_STREAM_ERROR
      let st ← dstateOf strm
      let z ← ldStream strm
      let s ← ldDState st
      if z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||
          (s.status == FINISH_STATE && flush != Z_FINISH) then
        return ← ERR_RETURN strm Z_STREAM_ERROR
      if z.avail_out == 0 then
        return ← ERR_RETURN strm Z_BUF_ERROR
      wrD st fun s => { s with last_flush := flush }
      bodyA st strm flush s.last_flush : M Int32) := by
  rfl

end ZlibNgF.Proof.DeflateBody
