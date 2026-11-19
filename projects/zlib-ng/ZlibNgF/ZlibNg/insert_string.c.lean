import ZlibNgF.ZlibNg.«insert_string_p.h»

/-!
# `insert_string.c` — external hash insertion functions (`ZlibNgF`)

Source: `zlib-ng/insert_string.c`: each function calls the static inline function of `insert_string_p.h`.
`call_insert_batch` is a call through the function pointer `s->insert_batch` (an `insert_batch_func` value of
`lm_set_level`).

This file also holds `insert_knuth_spread_static` of `insert_string_p.h` (namespace `ZlibNg.InsertStringP`): it calls
`insert_knuth_stepped`, which is defined here.
-/

set_option autoImplicit false

namespace ZlibNg.InsertString
open C ZlibNg.InsertStringP

/-- `Z_INTERNAL void insert_knuth_batch(deflate_state *const s, unsigned char *window, uint32_t str,
uint32_t count)` (`insert_string.c:12-14`). -/
def insert_knuth_batch (st : StatePtr) (window : BPtr) (str count : UInt32) : M Unit :=
  insert_knuth_batch_static st window str count

/-- `Z_INTERNAL void insert_knuth_stepped(deflate_state *const s, unsigned char *window, uint32_t str,
uint32_t count, uint32_t step)` (`insert_string.c:16-18`). -/
def insert_knuth_stepped (st : StatePtr) (window : BPtr) (str count step : UInt32) : M Unit :=
  insert_knuth_stepped_static st window str count step

/-- `Z_INTERNAL void insert_roll_batch(deflate_state *const s, unsigned char *window, uint32_t str,
uint32_t count)` (`insert_string.c:20-22`). -/
def insert_roll_batch (st : StatePtr) (window : BPtr) (str count : UInt32) : M Unit :=
  insert_roll_batch_static st window str count

/-- `Z_INTERNAL void insert_knuth_batch_head(deflate_state *const s, unsigned char *window, uint32_t str,
uint32_t count)` (`insert_string.c:24-26`). -/
def insert_knuth_batch_head (st : StatePtr) (window : BPtr) (str count : UInt32) : M Unit :=
  insert_knuth_batch_head_static st window str count

/-- `insert_batch(s, window, str, count)` with `insert_batch_func insert_batch` (`deflate.h:148`): a call through
the function pointer, to the function the value designates. -/
def call_insert_batch (f : InsertBatchFn) (st : StatePtr) (window : BPtr) (str count : UInt32) : M Unit :=
  match f with
  | .insert_knuth_batch => insert_knuth_batch st window str count
  | .insert_knuth_batch_head => insert_knuth_batch_head st window str count
  | .insert_roll_batch => insert_roll_batch st window str count

end ZlibNg.InsertString

namespace ZlibNg.InsertStringP
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.InsertString

/-- `Z_FORCEINLINE static void insert_knuth_spread_static(deflate_state *const s, unsigned char *window,
uint32_t str, uint32_t count, uint32_t max_inserts)` (`insert_string_p.h:216-236`). Defined here, after
`insert_knuth_stepped` of `insert_string.c`, which it calls. -/
def insert_knuth_spread_static (st : StatePtr) (window : BPtr) (str count max_inserts : UInt32) : M Unit := do
  if max_inserts > 3 then
    insert_knuth_stepped st window str count max_inserts
    return
  let headp ← (← rdD st (·.head)).get
  let prevp ← (← rdD st (·.prev)).get
  let w_mask := W_MASK (← ldDState st)
  insert_knuth_one headp prevp w_mask window str
  if max_inserts == 3 then
    insert_knuth_one headp prevp w_mask window (str + ((count - 1) >>> 1))
  insert_knuth_one headp prevp w_mask window (str + count - 1)

end ZlibNg.InsertStringP
