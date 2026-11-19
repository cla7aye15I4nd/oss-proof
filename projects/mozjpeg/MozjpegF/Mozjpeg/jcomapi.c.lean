import MozjpegF.Mozjpeg.«jmemmgr.c»

/-!
# `jcomapi.c` — faithful statement-by-statement translation (`MozjpegF`)

Source: `mozjpeg/jcomapi.c` (`jpeg_abort`, `jpeg_destroy`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jcomapi
open C Mozjpeg.JpeglibH Mozjpeg.Jmemmgr

/-- `GLOBAL(void) jpeg_abort(j_common_ptr cinfo)` (`jcomapi.c:31-58`).
No-op if `cinfo->mem == NULL`; otherwise calls `free_pool(cinfo, pool)` for pools
`> JPOOL_PERMANENT` in reverse order, resets `global_state = DSTATE_START`, and clears
`marker_list` and `master->marker_list_end`. -/
def jpeg_abort (cinfo : DecompPtr) : M Unit := do
  let dc ← Ptr.load cinfo
  if dc.mem == .null then
    return ()
  -- `for (pool = JPOOL_NUMPOOLS - 1; pool > JPOOL_PERMANENT; pool--)` -> pool = 1
  free_pool cinfo 1
  let dc ← Ptr.load cinfo
  if dc.isDecompressor != 0 then
    Ptr.store cinfo { dc with globalState := DSTATE_START, markerList := .null }
    let mst ← Ptr.load dc.master
    Ptr.store dc.master { mst with markerListEnd := .null }
  else
    Ptr.store cinfo { dc with globalState := 100 } -- CSTATE_START

/-- `GLOBAL(void) jpeg_destroy(j_common_ptr cinfo)` (`jcomapi.c:72-81`).
Calls `self_destruct(cinfo)` when `cinfo->mem != NULL`, then sets `cinfo->mem = NULL` and
`cinfo->global_state = 0`. -/
def jpeg_destroy (cinfo : DecompPtr) : M Unit := do
  let dc ← Ptr.load cinfo
  if dc.mem != .null then
    self_destruct cinfo
  let dc ← Ptr.load cinfo
  Ptr.store cinfo { dc with mem := .null, globalState := 0 }

end Mozjpeg.Jcomapi
