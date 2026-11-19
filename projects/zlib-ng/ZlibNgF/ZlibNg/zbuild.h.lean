import ZlibNgF.Runtime.Libc

/-!
# `zbuild.h` — build macros (`ZlibNgF`)

Source: `zlib-ng/zbuild.h`. The function-like macros used by the translated code, at type `size_t` (the
type of every use in the translated files; `zng_alloc_aligned` in `zutil.c` uses `ALIGN_DIFF` with an
`unsigned` alignment and has its own instance in `zutil.c.lean`).
-/

set_option autoImplicit false

namespace ZlibNg.Zbuild
open C

/-- `#define MIN(a, b) ((a) > (b) ? (b) : (a))` (`zbuild.h:148`) on `size_t`. -/
def MIN (a b : UInt64) : UInt64 := if a > b then b else a

/-- `#define ALIGN_DOWN(value, align) ((value) & ~((align) - 1))` (`zbuild.h:294-295`) on `size_t`. -/
def ALIGN_DOWN (value align : UInt64) : UInt64 := value &&& ~~~(align - 1)

/-- `#define ALIGN_DIFF(ptr, align) (((uintptr_t)(align) - ((uintptr_t)(ptr) & ((align) - 1))) & ((align) - 1))`
(`zbuild.h:286-287`) with a `size_t` (or `int` constant) `align`. -/
def ALIGN_DIFF (ptr : BPtr) (align : UInt64) : M UInt64 := do
  let addr ← addrOf ptr
  return (align - (addr &&& (align - 1))) &&& (align - 1)

end ZlibNg.Zbuild
