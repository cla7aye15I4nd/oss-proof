import MozjpegF.Mozjpeg.«jmemmgr.c»

/-!
# `jdinput.c` — input controller initialization translation (`MozjpegF`)

Source: `mozjpeg/jdinput.c` (`jinit_input_controller`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdinput
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH Mozjpeg.Jmemmgr

/-- `GLOBAL(void) jinit_input_controller(j_decompress_ptr cinfo)` (`jdinput.c:398-419`). -/
def jinit_input_controller (cinfo : DecompPtr) : M (JpegRes Unit) := do
  match (← alloc_small_inputctl cinfo JPOOL_PERMANENT 48) with
  | .errExit code => return .errExit code
  | .ok icPtr =>
    let dc ← Ptr.load cinfo
    Ptr.store cinfo { dc with inputctl := icPtr }
    Ptr.store icPtr {
      consumeInput := .fn "consume_markers"
      resetInputController := .fn "reset_input_controller"
      startInputPass := .fn "start_input_pass"
      finishInputPass := .fn "finish_input_pass"
      hasMultipleScans := FALSE
      eoiReached := FALSE
      inheaders := TRUE
    }
    return .ok ()

end Mozjpeg.Jdinput
