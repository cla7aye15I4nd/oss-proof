import ZlibNgF.Runtime.Deflate
import ZlibNgF.ZlibNg.«inflate.c»

/-!
# `deflate.h` — deflate state, constants and pending-buffer helpers (`ZlibNgF`)

Source: `zlib-ng/deflate.h` (verified configuration: `GZIP` defined, `HASH_SIZE` 65536, no `S390_DFLTCC_DEFLATE`, so
`PAD_WINDOW` is `PAD_64`, `WINDOW_PAD_SIZE` is 64 and the hooks are empty / constant; no `ZLIB_DEBUG`), the deflate
constants of `zlib.h` / `zutil.h`, and the macros of `fallback_builtins.h` used by deflate. The structures
`deflate_state`, `deflate_allocs`, `tree_desc` and `ct_data` are the runtime records `C.DeflateState`,
`C.DeflateAllocs`, `C.TreeDesc`, `C.Ct` (`Runtime/Heap.lean`, `Runtime/TreesTbl.lean`).

The constants of `zlib.h` shared with inflate (`Z_OK`, ..., `Z_FINISH`, `Z_BLOCK`, `MAX_WBITS`), the `zutil.h` / `zbuild.h`
macros `PADSZ`, `PAD_64`, `PAD_16`, `HINT_ALIGNED_64`, `CHECK_VER_STSIZE`, the calls through `strm->zalloc` / `zfree`
and the `z_stream` access shorthands `rdZ` / `wrZ` are those of the inflate translation (`ZlibNg.Inflate`).

`OS_CODE` is 3: the verified build is Linux (`zutil.h` defines it differently only for other systems).
-/

set_option autoImplicit false

namespace ZlibNg.Deflate
open C ZlibNg.Inflate

/-! ## Constants of `zlib.h` and `zutil.h` -/

def Z_NO_FLUSH : Int32 := 0
def Z_PARTIAL_FLUSH : Int32 := 1
def Z_SYNC_FLUSH : Int32 := 2
def Z_FULL_FLUSH : Int32 := 3

def Z_FILTERED : Int32 := 1
def Z_HUFFMAN_ONLY : Int32 := 2
def Z_RLE : Int32 := 3
def Z_FIXED : Int32 := 4
def Z_DEFAULT_STRATEGY : Int32 := 0
def Z_DEFAULT_COMPRESSION : Int32 := -1

def Z_BINARY : Int32 := 0
def Z_TEXT : Int32 := 1
def Z_UNKNOWN : Int32 := 2

def MAX_MEM_LEVEL : Int32 := 9
def DEF_MEM_LEVEL : Int32 := 8
def MAX_BITS : Nat := 15
def STD_MIN_MATCH : UInt32 := 3
def STD_MAX_MATCH : UInt32 := 258
def WANT_MIN_MATCH : UInt32 := 4
def PRESET_DICT : UInt32 := 0x20
def ZLIB_WRAPLEN : UInt64 := 6
def GZIP_WRAPLEN : UInt64 := 18
def OS_CODE : UInt8 := 3

/-! ## Constants of `deflate.h` -/

def LENGTH_CODES : Nat := 29
def LITERALS : Nat := 256
def D_CODES : Nat := 30
def BL_CODES : Nat := 19
def BIT_BUF_SIZE : Int32 := 64
def END_BLOCK : Nat := 256

def INIT_STATE : Int32 := 1
def GZIP_STATE : Int32 := 4
def EXTRA_STATE : Int32 := 5
def NAME_STATE : Int32 := 6
def COMMENT_STATE : Int32 := 7
def HCRC_STATE : Int32 := 8
def BUSY_STATE : Int32 := 2
def FINISH_STATE : Int32 := 3
def MAX_STATE : Int32 := HCRC_STATE

def HASH_SIZE : UInt32 := 65536
def HASH_BITS : UInt32 := 16
def HASH_MASK : UInt32 := HASH_SIZE - 1
def MIN_ROLL_LEVEL : Int32 := 9

/-- `#define MIN_LOOKAHEAD (STD_MAX_MATCH + STD_MIN_MATCH + 1)` -/
def MIN_LOOKAHEAD : UInt32 := STD_MAX_MATCH + STD_MIN_MATCH + 1
/-- `#define WIN_INIT STD_MAX_MATCH` -/
def WIN_INIT : UInt32 := STD_MAX_MATCH
/-- `#define W_BUF_MIN 32768` -/
def W_BUF_MIN : UInt32 := 32768
/-- `#define W_BUF_SIZE(wsize) MAX(2 * (wsize), W_BUF_MIN)` (on `unsigned`). -/
def W_BUF_SIZE (wsize : UInt32) : UInt32 := if 2 * wsize > W_BUF_MIN then 2 * wsize else W_BUF_MIN
/-- `#define WINDOW_PAD_SIZE 64` -/
def WINDOW_PAD_SIZE : Int32 := 64

/-- `typedef enum { need_more, block_done, finish_started, finish_done } block_state;` -/
inductive BlockState where
  | need_more
  | block_done
  | finish_started
  | finish_done
  deriving DecidableEq, Repr, Inhabited

/-! ## `fallback_builtins.h` -/

/-- `zng_ctz32(value)`: `__builtin_ctz`, undefined for 0 (GCC documentation; `Assert(value != 0)`). -/
def zng_ctz32 (value : UInt32) : M UInt32 :=
  if value == 0 then ub "__builtin_ctz(0)" else
  pure (Id.run do
    let mut n : UInt32 := 0
    let mut v := value
    for _ in [0:32] do
      if v &&& 1 == 0 then
        n := n + 1
        v := v >>> 1
    return n)

/-- `zng_ctz64(value)`: `__builtin_ctzll`, undefined for 0. -/
def zng_ctz64 (value : UInt64) : M UInt32 :=
  if value == 0 then ub "__builtin_ctzll(0)" else
  pure (Id.run do
    let mut n : UInt32 := 0
    let mut v := value
    for _ in [0:64] do
      if v &&& 1 == 0 then
        n := n + 1
        v := v >>> 1
    return n)

/-- `zng_first_diff_byte64(diff)` = `zng_ctz64(diff) / 8` (little-endian). -/
def zng_first_diff_byte64 (diff : UInt64) : M UInt32 := do
  return (← zng_ctz64 diff) / 8

/-- `zng_first_bytes_mask64(n)` = `UINT64_MAX >> ((8 - (n)) * 8)` (little-endian), `n` an `unsigned`/`uint32_t`. -/
def zng_first_bytes_mask64 (n : UInt32) : M UInt64 :=
  shr64 0xffffffffffffffff ((8 - n) * 8)

/-- `zng_bitreverse16(value)` (`__builtin_bitreverse16`). -/
def zng_bitreverse16 (value : UInt16) : UInt16 := Id.run do
  let mut r : UInt16 := 0
  for i in [0:16] do
    if (value >>> i.toUInt16) &&& 1 == 1 then
      r := r ||| ((1 : UInt16) <<< (15 - i).toUInt16)
  return r

/-! ## Heap access shorthands -/

/-- Read a field of the `deflate_state` `*s`. -/
def rdD {α : Type} (st : StatePtr) (f : DeflateState → α) : M α := do return f (← ldDState st)
/-- Update fields of the `deflate_state` `*s`. -/
def wrD (st : StatePtr) (f : DeflateState → DeflateState) : M Unit := do stDState st (f (← ldDState st))
/-- `strm->state` as a `deflate_state *`. -/
def dstateOf (strm : StreamPtr) : M StatePtr := rdZ strm (·.state)

/-- `s->dyn_ltree` -/
def dynLtreeP (st : StatePtr) : M CtPtr :=
  match st with | some b => pure (.ref (.dyn_ltree b) 0) | none => ub "null state"
/-- `s->dyn_dtree` -/
def dynDtreeP (st : StatePtr) : M CtPtr :=
  match st with | some b => pure (.ref (.dyn_dtree b) 0) | none => ub "null state"
/-- `s->bl_tree` -/
def blTreeP (st : StatePtr) : M CtPtr :=
  match st with | some b => pure (.ref (.bl_tree b) 0) | none => ub "null state"
/-- `s->bl_count` -/
def blCountP (st : StatePtr) : M DHPtr :=
  match st with | some b => pure (.ref (.bl_count b) 0) | none => ub "null state"
/-- `s->pq_leaves` -/
def pqLeavesP (st : StatePtr) : M DWPtr :=
  match st with | some b => pure (.ref (.pq_leaves b) 0) | none => ub "null state"
/-- `s->pq_scratch` -/
def pqScratchP (st : StatePtr) : M DWPtr :=
  match st with | some b => pure (.ref (.pq_scratch b) 0) | none => ub "null state"

/-- `tree[i]` of a `ct_data *tree`. -/
def ctGet (p : CtPtr) (i : Int) : M Ct := Ptr.index p i
/-- `tree[i] = v` of a `ct_data *tree`. -/
def ctSet (p : CtPtr) (i : Int) (v : Ct) : M Unit := do Ptr.store (← p.add i) v
/-- `tree[i].Freq` / `tree[i].Code` (member `fc`). -/
def ctFc (p : CtPtr) (i : Int) : M UInt16 := do return (← ctGet p i).fc
/-- `tree[i].Dad` / `tree[i].Len` (member `dl`). -/
def ctDl (p : CtPtr) (i : Int) : M UInt16 := do return (← ctGet p i).dl
/-- `tree[i].Freq = v` / `tree[i].Code = v`. -/
def ctSetFc (p : CtPtr) (i : Int) (v : UInt16) : M Unit := do
  let c ← ctGet p i
  ctSet p i { c with fc := v }
/-- `tree[i].Dad = v` / `tree[i].Len = v`. -/
def ctSetDl (p : CtPtr) (i : Int) (v : UInt16) : M Unit := do
  let c ← ctGet p i
  ctSet p i { c with dl := v }

/-! ## Pending-buffer writes (`deflate.h`) -/

/-- `#define put_byte(s, c) { s->pending_buf[s->pending++] = (unsigned char)(c); }` -/
def put_byte (st : StatePtr) (c : UInt8) : M Unit := do
  let s ← ldDState st
  let pb ← s.pending_buf.get
  store8 (← pb.add s.pending.toNat) c
  wrD st fun s => { s with pending := s.pending + 1 }

/-- `static inline void put_short(deflate_state *s, uint16_t w)` -/
def put_short (st : StatePtr) (w : UInt16) : M Unit := do
  let s ← ldDState st
  memwrite2 (← (← s.pending_buf.get).add s.pending.toNat) w
  wrD st fun s => { s with pending := s.pending + 2 }

/-- `static inline void put_short_msb(deflate_state *s, uint16_t w)` (`Z_U16_TO_BE` swaps the bytes). -/
def put_short_msb (st : StatePtr) (w : UInt16) : M Unit := do
  let w := (w >>> 8) ||| (w <<< 8)
  let s ← ldDState st
  memwrite2 (← (← s.pending_buf.get).add s.pending.toNat) w
  wrD st fun s => { s with pending := s.pending + 2 }

/-- `static inline void put_uint32(deflate_state *s, uint32_t dw)` -/
def put_uint32 (st : StatePtr) (dw : UInt32) : M Unit := do
  let s ← ldDState st
  memwrite4 (← (← s.pending_buf.get).add s.pending.toNat) dw
  wrD st fun s => { s with pending := s.pending + 4 }

/-- `static inline void put_uint32_msb(deflate_state *s, uint32_t dw)` (`Z_U32_TO_BE` swaps the bytes). -/
def put_uint32_msb (st : StatePtr) (dw : UInt32) : M Unit := do
  let dw : UInt32 := ((dw &&& (0xff : UInt32)) <<< 24) ||| ((dw &&& (0xff00 : UInt32)) <<< 8) |||
    ((dw >>> 8) &&& (0xff00 : UInt32)) ||| (dw >>> 24)
  let s ← ldDState st
  memwrite4 (← (← s.pending_buf.get).add s.pending.toNat) dw
  wrD st fun s => { s with pending := s.pending + 4 }

/-- `static inline void put_uint64(deflate_state *s, uint64_t lld)` -/
def put_uint64 (st : StatePtr) (lld : UInt64) : M Unit := do
  let s ← ldDState st
  memwrite8 (← (← s.pending_buf.get).add s.pending.toNat) lld
  wrD st fun s => { s with pending := s.pending + 8 }

/-! ## Window macros -/

/-- `#define MAX_DIST(s) ((s)->w_size - MIN_LOOKAHEAD)` -/
def MAX_DIST (s : DeflateState) : UInt32 := s.w_size - MIN_LOOKAHEAD
/-- `#define W_MASK(s) ((s)->w_size - 1)` -/
def W_MASK (s : DeflateState) : UInt32 := s.w_size - 1
/-- `#define W_BITS(s) zng_ctz32((s)->w_size)` -/
def W_BITS (s : DeflateState) : M UInt32 := zng_ctz32 s.w_size

/-- `#define d_code(dist) ((dist) < 256 ? zng_dist_code[dist] : zng_dist_code[256+((dist)>>7)])` -/
def d_code (dist : UInt32) : M UInt8 :=
  if dist < 256 then tblGet zng_dist_code dist.toNat else tblGet zng_dist_code (256 + (dist >>> 7).toNat)

end ZlibNg.Deflate
