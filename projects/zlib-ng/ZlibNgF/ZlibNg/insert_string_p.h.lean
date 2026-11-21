import ZlibNgF.ZlibNg.«deflate.h»

/-!
# `insert_string_p.h` — hash insertion (`ZlibNgF`)

Source: `zlib-ng/insert_string_p.h` (verified configuration: `HASH_BITS` 16, `HASH_SIZE` 65536, little-endian, so
`Z_U32_FROM_LE` is the identity; no `ZLIB_DEBUG`, so `Assert` is empty). `LIKELY` / `UNLIKELY` are branch hints.

`Pos` is `uint16_t`; `s->head` and `s->prev` are byte pointers into the block of `alloc_deflate`, and `p[i]` on a
`Pos *p` is `posLoad p i` / `posStore p i v` (`Runtime/Deflate.lean`). `(Pos)x` truncates to 16 bits. The hash
macros shift by constant counts (16 and 5), which are in range, so they use the plain operators.

`insert_knuth_spread_static` calls the external `insert_knuth_stepped` of `insert_string.c`; it is defined in
`insert_string.c.lean`, right after that function, in this namespace.
-/

set_option autoImplicit false

namespace ZlibNg.InsertStringP
open C ZlibNg.Inflate ZlibNg.Deflate

/-- `#define KNUTH_SHIFT (32 - HASH_BITS)` (`insert_string_p.h:9`). -/
def KNUTH_SHIFT : UInt32 := 32 - HASH_BITS

/-- `#define UPDATE_HASH_KNUTH(h,val) h = (((val) * 2654435761U) >> KNUTH_SHIFT)` (`insert_string_p.h:10`): the
new value of `h`. -/
def UPDATE_HASH_KNUTH (val : UInt32) : UInt32 := (val * 2654435761) >>> KNUTH_SHIFT

/-- `#define ROLL_HASH_SIZE HASH_SIZE` (`insert_string_p.h:12-16`, `HASH_SIZE <= 65536`). -/
def ROLL_HASH_SIZE : UInt32 := HASH_SIZE

/-- `#define ROLL_MASK ((HASH_SIZE / 2) - 1u))` (`insert_string_p.h:17`; the unbalanced parenthesis closes the one
opened by `UPDATE_HASH_ROLL`). -/
def ROLL_MASK : UInt32 := (HASH_SIZE / 2) - 1

/-- `#define UPDATE_HASH_ROLL(h,val) h = (((h << 5) ^ ((uint8_t)(val))) & ROLL_MASK` (`insert_string_p.h:18`): the
new value of `h`. -/
def UPDATE_HASH_ROLL (h val : UInt32) : UInt32 := ((h <<< 5) ^^^ val.toUInt8.toUInt32) &&& ROLL_MASK

/-- `Z_FORCEINLINE static uint32_t update_hash_roll(uint32_t h, uint32_t val)` (`insert_string_p.h:26-29`). -/
def update_hash_roll (h val : UInt32) : UInt32 :=
  let h := UPDATE_HASH_ROLL h val
  h

/-- `Z_FORCEINLINE static uint32_t insert_knuth_val(deflate_state *const s, uint32_t str, uint32_t val)`
(`insert_string_p.h:36-47`). -/
def insert_knuth_val (st : StatePtr) (str val : UInt32) : M UInt32 := do
  let h := UPDATE_HASH_KNUTH val
  let head := (← posLoad (← (← rdD st (·.head)).get) h.toNat).toUInt32
  if head != str then
    let s ← ldDState st
    posStore (← s.prev.get) (str &&& W_MASK s).toNat head.toUInt16
    posStore (← (← rdD st (·.head)).get) h.toNat str.toUInt16
  return head

/-- `Z_FORCEINLINE static uint32_t insert_knuth_val_head(deflate_state *const s, uint32_t str, uint32_t val)`
(`insert_string_p.h:54-62`). -/
def insert_knuth_val_head (st : StatePtr) (str val : UInt32) : M UInt32 := do
  let h := UPDATE_HASH_KNUTH val
  let head := (← posLoad (← (← rdD st (·.head)).get) h.toNat).toUInt32
  posStore (← (← rdD st (·.head)).get) h.toNat str.toUInt16
  return head

/-- `Z_FORCEINLINE static uint32_t insert_knuth(deflate_state *const s, unsigned char *window, uint32_t str)`
(`insert_string_p.h:69-82`). -/
def insert_knuth (st : StatePtr) (window : BPtr) (str : UInt32) : M UInt32 := do
  let strstart ← window.add str.toNat
  let val ← memread4 strstart
  let h := UPDATE_HASH_KNUTH val
  let head := (← posLoad (← (← rdD st (·.head)).get) h.toNat).toUInt32
  if head != str then
    let s ← ldDState st
    posStore (← s.prev.get) (str &&& W_MASK s).toNat head.toUInt16
    posStore (← (← rdD st (·.head)).get) h.toNat str.toUInt16
  return head

/-- `Z_FORCEINLINE static uint32_t insert_knuth_head(deflate_state *const s, unsigned char *window, uint32_t str)`
(`insert_string_p.h:89-99`). -/
def insert_knuth_head (st : StatePtr) (window : BPtr) (str : UInt32) : M UInt32 := do
  let strstart ← window.add str.toNat
  let val ← memread4 strstart
  let h := UPDATE_HASH_KNUTH val
  let head := (← posLoad (← (← rdD st (·.head)).get) h.toNat).toUInt32
  posStore (← (← rdD st (·.head)).get) h.toNat str.toUInt16
  return head

/-- `Z_FORCEINLINE static void insert_knuth_one(Pos *headp, Pos *prevp, const unsigned int w_mask,
const unsigned char *window, uint32_t idx)` (`insert_string_p.h:104-115`). -/
def insert_knuth_one (headp prevp : BPtr) (w_mask : UInt32) (window : BPtr) (idx : UInt32) : M Unit := do
  let val ← memread4 (← window.add idx.toNat)
  let h := UPDATE_HASH_KNUTH val
  let head := (← posLoad headp h.toNat).toUInt32
  if head != idx then
    posStore prevp (idx &&& w_mask).toNat head.toUInt16
    posStore headp h.toNat idx.toUInt16

/-- `Z_FORCEINLINE static uint32_t insert_roll(deflate_state *const s, unsigned char *window, uint32_t str)`
(`insert_string_p.h:117-131`). `window + str + (STD_MIN_MATCH-1)` is `(window + str) + 2`: two pointer additions. -/
def insert_roll (st : StatePtr) (window : BPtr) (str : UInt32) : M UInt32 := do
  let strstart ← (← window.add str.toNat).add (STD_MIN_MATCH - 1).toNat
  let h ← rdD st (·.ins_h)
  let h := UPDATE_HASH_ROLL h (← index8 strstart 0).toUInt32
  wrD st fun s => { s with ins_h := h }
  let head := (← posLoad (← (← rdD st (·.head)).get) h.toNat).toUInt32
  if head != str then
    let s ← ldDState st
    posStore (← s.prev.get) (str &&& W_MASK s).toNat head.toUInt16
    posStore (← (← rdD st (·.head)).get) h.toNat str.toUInt16
  return head

/-- `Z_FORCEINLINE static void insert_knuth_batch_static(deflate_state *const s, unsigned char *window, uint32_t str,
uint32_t count)` (`insert_string_p.h:141-162`). Loop state `(idx, strstart)`. -/
def insert_knuth_batch_static (st : StatePtr) (window : BPtr) (str count : UInt32) : M Unit := do
  let strstart ← window.add str.toNat
  let strend ← strstart.add count.toNat
  let headp ← (← rdD st (·.head)).get
  let prevp ← (← rdD st (·.prev)).get
  let w_mask := W_MASK (← ldDState st)
  let _ ← cwhile
    (fun ((idx, strstart) : UInt32 × BPtr) => do
      return (← Ptr.lt strstart strend, (idx, strstart)))
    (fun ((idx, strstart) : UInt32 × BPtr) => do
      let val ← memread4 strstart
      let h := UPDATE_HASH_KNUTH val
      let head := (← posLoad headp h.toNat).toUInt32
      if head != idx then
        posStore prevp (idx &&& w_mask).toNat head.toUInt16
        posStore headp h.toNat idx.toUInt16
      return (idx + 1, ← strstart.add 1))
    (str, strstart)

/-- `Z_FORCEINLINE static void insert_knuth_stepped_static(deflate_state *const s, unsigned char *window,
uint32_t str, uint32_t count, uint32_t max_inserts)` (`insert_string_p.h:169-209`). The unsigned division by
`intervals` is undefined when `intervals` is 0 (ISO C17 §6.5.5p5), i.e. when `count` or `max_inserts` is at most
1 (excluded by the `Assert`s, which are not compiled). Loop state `(i, idx_fp)`. -/
def insert_knuth_stepped_static (st : StatePtr) (window : BPtr) (str count max_inserts : UInt32) : M Unit := do
  let headp ← (← rdD st (·.head)).get
  let prevp ← (← rdD st (·.prev)).get
  let w_mask := W_MASK (← ldDState st)
  let inserts := if count < max_inserts then count else max_inserts
  let intervals := inserts - 1
  if intervals == 0 then ub "division by zero"
  let inc_fp := (((count - 1) <<< 16) + (intervals - 1)) / intervals
  let idx_fp := str <<< 16
  let _ ← cwhile
    (fun ((i, idx_fp) : UInt32 × UInt32) => pure (i < inserts, (i, idx_fp)))
    (fun ((i, idx_fp) : UInt32 × UInt32) => do
      let idx := idx_fp >>> 16
      let idx_fp := idx_fp + inc_fp
      let val ← memread4 (← window.add idx.toNat)
      let h := UPDATE_HASH_KNUTH val
      let head := (← posLoad headp h.toNat).toUInt32
      if head != idx then
        posStore prevp (idx &&& w_mask).toNat head.toUInt16
        posStore headp h.toNat idx.toUInt16
      return (i + 1, idx_fp))
    ((0 : UInt32), idx_fp)

/-- `Z_FORCEINLINE static void insert_knuth_batch_head_static(deflate_state *const s, unsigned char *window,
uint32_t str, uint32_t count)` (`insert_string_p.h:242-255`). Loop state `(idx, strstart)`. -/
def insert_knuth_batch_head_static (st : StatePtr) (window : BPtr) (str count : UInt32) : M Unit := do
  let strstart ← window.add str.toNat
  let strend ← strstart.add count.toNat
  let headp ← (← rdD st (·.head)).get
  let _ ← cwhile
    (fun ((idx, strstart) : UInt32 × BPtr) => do
      return (← Ptr.lt strstart strend, (idx, strstart)))
    (fun ((idx, strstart) : UInt32 × BPtr) => do
      let val ← memread4 strstart
      let h := UPDATE_HASH_KNUTH val
      posStore headp h.toNat idx.toUInt16
      return (idx + 1, ← strstart.add 1))
    (str, strstart)

/-- `Z_FORCEINLINE static void insert_roll_batch_static(deflate_state *const s, unsigned char *window, uint32_t str,
uint32_t count)` (`insert_string_p.h:257-279`). `window + str + (STD_MIN_MATCH-1)` is two pointer additions. Loop
state `(idx, strstart, h)`. -/
def insert_roll_batch_static (st : StatePtr) (window : BPtr) (str count : UInt32) : M Unit := do
  let strstart ← (← window.add str.toNat).add (STD_MIN_MATCH - 1).toNat
  let strend ← strstart.add count.toNat
  let headp ← (← rdD st (·.head)).get
  let prevp ← (← rdD st (·.prev)).get
  let h ← rdD st (·.ins_h)
  let w_mask := W_MASK (← ldDState st)
  let (_, _, h) ← cwhile
    (fun ((idx, strstart, h) : UInt32 × BPtr × UInt32) => do
      return (← Ptr.lt strstart strend, (idx, strstart, h)))
    (fun ((idx, strstart, h) : UInt32 × BPtr × UInt32) => do
      let h := UPDATE_HASH_ROLL h (← index8 strstart 0).toUInt32
      let head := (← posLoad headp h.toNat).toUInt32
      if head != idx then
        posStore prevp (idx &&& w_mask).toNat head.toUInt16
        posStore headp h.toNat idx.toUInt16
      return (idx + 1, ← strstart.add 1, h))
    (str, strstart, h)
  wrD st fun s => { s with ins_h := h }

/-- `Z_FORCEINLINE static void insert_skip(deflate_state *const s, uint32_t str, uint32_t count)`
(`insert_string_p.h:286-293`). `&s->prev[idx]` is `s->prev + idx` (two bytes per `Pos`); the byte counts
`first * sizeof(Pos)` and `(count - first) * sizeof(Pos)` are `size_t` products of a `uint32_t` (no wrap). -/
def insert_skip (st : StatePtr) (str count : UInt32) : M Unit := do
  let s ← ldDState st
  let idx := str &&& W_MASK s
  let first := if count < s.w_size - idx then count else s.w_size - idx
  Ptr.memset (← (← s.prev.get).add (2 * idx.toNat)) 0 (first.toNat * 2)
  Ptr.memset (← s.prev.get) 0 ((count - first).toNat * 2)

/-- `Z_FORCEINLINE static void insert_knuth_batch_tail_static(deflate_state *const s, unsigned char *window,
uint32_t str, uint32_t count, uint32_t tail)` (`insert_string_p.h:299-305`). -/
def insert_knuth_batch_tail_static (st : StatePtr) (window : BPtr) (str count tail : UInt32) : M Unit := do
  let skip := count - tail
  insert_skip st str skip
  insert_knuth_batch_static st window (str + skip) tail

/-- `Z_FORCEINLINE static void insert_roll_batch_tail_static(deflate_state *const s, unsigned char *window,
uint32_t str, uint32_t count, uint32_t tail)` (`insert_string_p.h:307-316`). -/
def insert_roll_batch_tail_static (st : StatePtr) (window : BPtr) (str count tail : UInt32) : M Unit := do
  let skip := count - tail
  insert_skip st str skip
  let str := str + skip
  let a := (← index8 window str.toNat).toUInt32
  let b := (← index8 window (str + 1).toNat).toUInt32
  wrD st fun s => { s with ins_h := update_hash_roll a b }
  insert_roll_batch_static st window str tail

end ZlibNg.InsertStringP
