import ZlibNgF.ZlibNg.«gzread.c»
import ZlibNgF.ZlibNg.«gzwrite.c»

/-!
# `gzclose` of `gzlib.c` (`ZlibNgF`)

Source: `zlib-ng/gzlib.c:323-335` (`NO_GZCOMPRESS` not defined). It calls `gzclose_r` (`gzread.c`) and `gzclose_w`
(`gzwrite.c`), so it follows their translations.
-/

set_option autoImplicit false

namespace ZlibNg.Gz
open C ZlibNg.Inflate

/-- `z_int32_t Z_EXPORT PREFIX(gzclose)(gzFile file)` (`gzlib.c:323-335`). -/
def gzclose (file : GzPtr) : G Int32 := do
  if file == none then
    return Z_STREAM_ERROR
  let state := file
  if (← rdG state (·.mode)) == GZ_READ then gzclose_r file else gzclose_w file

end ZlibNg.Gz
