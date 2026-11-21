import ZlibNgF.ZlibNg.«deflate_medium_tpl.h»

/-!
# `deflate_medium.c` — the two instantiations of the medium strategy (`ZlibNgF`)

Source: `zlib-ng/deflate_medium.c` (`NO_MEDIUM_STRATEGY` undefined in the verified build). It defines
`struct match` (`deflate_medium.c:12-17`, `ZlibNg.DeflateMedium.Match`, in `deflate_medium_tpl.h.lean` because the
template uses it) and includes `deflate_medium_tpl.h` twice: without `USE_FIZZLE` (`SUFFIX(name) = name`, levels 3-4)
and with it (`SUFFIX(name) = name ## _fizzle`, levels 5-6).
-/

set_option autoImplicit false

namespace ZlibNg.DeflateMedium
open C ZlibNg.Deflate

/-- `Z_INTERNAL block_state deflate_medium(deflate_state *s, int flush)` (`deflate_medium.c:24-26`:
`deflate_medium_tpl.h:170-335` without `USE_FIZZLE`). -/
def deflate_medium (st : StatePtr) (flush : Int32) : M BlockState :=
  deflate_medium_tpl false st flush

/-- `Z_INTERNAL block_state deflate_medium_fizzle(deflate_state *s, int flush)` (`deflate_medium.c:30-33`:
`deflate_medium_tpl.h:170-335` with `USE_FIZZLE`). -/
def deflate_medium_fizzle (st : StatePtr) (flush : Int32) : M BlockState :=
  deflate_medium_tpl true st flush

end ZlibNg.DeflateMedium
