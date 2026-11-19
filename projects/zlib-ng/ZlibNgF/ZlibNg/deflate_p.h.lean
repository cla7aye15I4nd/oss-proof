import ZlibNgF.ZlibNg.«trees.c»
import ZlibNgF.ZlibNg.arch.generic.«compare256_c.c»
import ZlibNgF.ZlibNg.arch.generic.«adler32_c.c»
import ZlibNgF.ZlibNg.arch.generic.«crc32_braid_c.c»

/-!
# `deflate_p.h` — inline helpers shared by the deflate strategies (`ZlibNgF`)

Source: `zlib-ng/deflate_p.h` (`OPTIMAL_CMP == 64`, no `ZLIB_DEBUG`, so `check_match`, `Tracev`, `Assert` are empty;
`DEFLATE_NEED_CHECKSUM(strm)` is 1). `bi_reverse` of this header is in `trees.c.lean`, which needs it and is needed
here. `flush_pending` of `deflate.c:797-799` (a call of `flush_pending_inline`) is defined here, after
`flush_pending_inline`, because `FLUSH_BLOCK_ONLY` calls it and `deflate.c` depends on the strategies.

`FUNCTABLE_CALL(adler32_copy)` = `adler32_copy_c`, `FUNCTABLE_CALL(crc32_copy)` = `crc32_copy_braid`,
`FUNCTABLE_CALL(compare256)` = `compare256_c`.
-/

set_option autoImplicit false

namespace ZlibNg.DeflateP
open C ZlibNg.Inflate ZlibNg.Deflate

/-- `#define MAX_STORED 65535` -/
def MAX_STORED : UInt32 := 65535

/-- `static inline int zng_tr_tally_lit(deflate_state *s, unsigned char c)` (`deflate_p.h:63-80`). -/
def zng_tr_tally_lit (st : StatePtr) (c : UInt8) : M Bool := do
  let s ← ldDState st
  let sym_next := s.sym_next
  memwrite4 (← (← s.sym_buf.get).add sym_next.toNat) (c.toUInt32 <<< 16)
  wrD st fun s => { s with sym_next := sym_next + 3 }
  let lt ← dynLtreeP st
  let f ← ctFc lt c.toNat
  ctSetFc lt c.toNat (f + 1)
  let s ← ldDState st
  return s.sym_next == s.sym_end

/-- `static inline int zng_tr_tally_dist(deflate_state* s, uint32_t dist, uint32_t len)` (`deflate_p.h:82-101`). -/
def zng_tr_tally_dist (st : StatePtr) (dist len : UInt32) : M Bool := do
  let s ← ldDState st
  let sym_next := s.sym_next
  memwrite4 (← (← s.sym_buf.get).add sym_next.toNat) (dist ||| (len <<< 16))
  wrD st fun s => { s with sym_next := sym_next + 3 }
  let dist := dist - 1
  let lt ← dynLtreeP st
  let i := (← tblGet zng_length_code len.toNat).toNat + LITERALS + 1
  ctSetFc lt i ((← ctFc lt i) + 1)
  let dt ← dynDtreeP st
  let j := (← d_code dist).toNat
  ctSetFc dt j ((← ctFc dt j) + 1)
  let s ← ldDState st
  return s.sym_next == s.sym_end

/-- `Z_FORCEINLINE static void flush_pending_inline(PREFIX3(stream) *strm)` (`deflate_p.h:109-127`). -/
def flush_pending_inline (strm : StreamPtr) : M Unit := do
  let st ← dstateOf strm
  ZlibNg.Trees.zng_tr_flush_bits st
  let s ← ldDState st
  let z ← ldStream strm
  let len : UInt32 := if s.pending > z.avail_out then z.avail_out else s.pending
  if len == 0 then return
  let po ← s.pending_out.get
  Ptr.memcpy z.next_out po len.toNat
  let no ← z.next_out.add len.toNat
  wrZ strm fun z => { z with next_out := no }
  let po' ← po.add len.toNat
  wrD st fun s => { s with pending_out := .val po' }
  wrZ strm fun z => { z with total_out := z.total_out + len.toUInt64 }
  wrZ strm fun z => { z with avail_out := z.avail_out - len }
  wrD st fun s => { s with pending := s.pending - len }
  let s ← ldDState st
  if s.pending == 0 then
    wrD st fun s => { s with pending_out := s.pending_buf }

/-- `Z_INTERNAL void PREFIX(flush_pending)(PREFIX3(stream) *strm)` (`deflate.c:797-799`). -/
def flush_pending (strm : StreamPtr) : M Unit := flush_pending_inline strm

/-- `Z_FORCEINLINE static unsigned read_buf(PREFIX3(stream) *strm, unsigned char *buf, unsigned size)`
(`deflate_p.h:147-172`). -/
def read_buf (strm : StreamPtr) (buf : BPtr) (size : UInt32) : M UInt32 := do
  let st ← dstateOf strm
  let z ← ldStream strm
  let len : UInt32 := if z.avail_in > size then size else z.avail_in
  if len == 0 then return 0
  let s ← ldDState st
  if s.wrap == 2 then
    let z ← ldStream strm
    let a ← ZlibNg.Crc32Braid.crc32_copy_braid z.adler.toUInt32 buf z.next_in len.toUInt64
    wrZ strm fun z => { z with adler := a.toUInt64 }
  else if s.wrap == 1 then
    let z ← ldStream strm
    let a ← ZlibNg.Adler32C.adler32_copy_c z.adler.toUInt32 buf z.next_in len.toUInt64
    wrZ strm fun z => { z with adler := a.toUInt64 }
  else
    Ptr.memcpy buf (← rdZ strm (·.next_in)) len.toNat
  wrZ strm fun z => { z with avail_in := z.avail_in - len }
  let ni ← (← rdZ strm (·.next_in)).add len.toNat
  wrZ strm fun z => { z with next_in := ni }
  wrZ strm fun z => { z with total_in := z.total_in + len.toUInt64 }
  return len

/-- `Z_FORCEINLINE static uint32_t max_match_continues(const unsigned char *window, unsigned int strstart,
uint32_t dist)` (`deflate_p.h:180-185`). -/
def max_match_continues (window : BPtr) (strstart dist : UInt32) : M UInt32 := do
  let scan ← window.add strstart.toNat
  let a ← memread8 scan
  let b ← memread8 (← scan.add (-(dist.toNat : Int)))
  if a != b then return 0
  let p ← scan.add 2
  let q ← (← scan.add (-(dist.toNat : Int))).add 2
  return (← ZlibNg.Compare256.compare256_c p q) + 2

/-- `#define FLUSH_BLOCK_ONLY(s, window, last)` (`deflate_p.h:191-200`). `block_start >= 0 ? &window[block_start] :
NULL`; `(uint32_t)((int)s->strstart - block_start)` is computed in `int` (checked). -/
def FLUSH_BLOCK_ONLY (st : StatePtr) (window : BPtr) (last : Int32) : M Unit := do
  let s ← ldDState st
  let block_start := s.block_start
  let buf ← if block_start ≥ 0 then window.add block_start.toInt.toNat else pure .null
  let len ← chkI32 (s.strstart.toInt32.toInt - block_start.toInt)
  ZlibNg.Trees.zng_tr_flush_block st buf len.toUInt32 last
  wrD st fun s => { s with block_start := s.strstart.toInt32 }
  let strm ← (← ldDState st).strm.get
  flush_pending strm

/-- `#define FLUSH_BLOCK(s, window, last)` (`deflate_p.h:203-206`): `some r` is the early `return r`. -/
def FLUSH_BLOCK (st : StatePtr) (window : BPtr) (last : Int32) : M (Option BlockState) := do
  FLUSH_BLOCK_ONLY st window last
  let strm ← (← ldDState st).strm.get
  if (← rdZ strm (·.avail_out)) == 0 then
    return some (if last != 0 then .finish_started else .need_more)
  return none

end ZlibNg.DeflateP
