import ZlibNgF.ZlibNg.«deflate.h»

/-!
# `arch/generic/slide_hash_c.c` — slide the hash table (`ZlibNgF`)

Source: `zlib-ng/arch/generic/slide_hash_c.c` (`SLIDE_HASH_FALLBACK` is defined: no SIMD in the verified build).
A `Pos *` is a byte pointer into the block of `alloc_deflate`; `*q` is the two-byte access `memread2` /
`memwrite2`, and `q++` advances it by `sizeof(Pos)` = 2 bytes.
-/

set_option autoImplicit false

namespace ZlibNg.SlideHash
open C ZlibNg.Inflate ZlibNg.Deflate

/-- `static inline void slide_hash_c_chain(Pos *table, uint32_t entries, Pos wsize)` (`slide_hash_c.c:17-26`).
`m - wsize` is an `int` subtraction of two promoted `uint16_t` with `m >= wsize` (in range), converted to `Pos`.
`*q++ = e` stores at the old `q`, then `q` is advanced. Loop state `(i, q)`. -/
def slide_hash_c_chain (table : BPtr) (entries : UInt32) (wsize : UInt16) : M Unit := do
  let q := table
  let _ ← cwhile
    (fun ((i, q) : UInt32 × BPtr) => pure (i < entries, (i, q)))
    (fun ((i, q) : UInt32 × BPtr) => do
      let m ← memread2 q
      memwrite2 q (if m >= wsize then m - wsize else 0)
      let q ← q.add 2
      return (i + 1, q))
    ((0 : UInt32), q)

/-- `Z_INTERNAL void slide_hash_c(deflate_state *s)` (`slide_hash_c.c:28-33`). -/
def slide_hash_c (st : StatePtr) : M Unit := do
  let slide := (← rdD st (·.slide_len)).toUInt16
  slide_hash_c_chain (← (← rdD st (·.head)).get) HASH_SIZE slide
  let s ← ldDState st
  slide_hash_c_chain (← s.prev.get) s.w_size slide

/-- `Z_INTERNAL void slide_hash_head_c(deflate_state *s)` (`slide_hash_c.c:35-39`). -/
def slide_hash_head_c (st : StatePtr) : M Unit := do
  let slide := (← rdD st (·.slide_len)).toUInt16
  slide_hash_c_chain (← (← rdD st (·.head)).get) HASH_SIZE slide

end ZlibNg.SlideHash
