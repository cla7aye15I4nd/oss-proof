import MozjpegF.Mozjpeg.«jpeglib.h»

/-!
# `jerror.c` — faithful statement-by-statement translation (`MozjpegF`)

Source: `mozjpeg/jerror.c`, LP64 Linux build (`JPEG_LIB_VERSION == 80`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jerror
open C Mozjpeg.JerrorH

/-- `METHODDEF(void) reset_error_mgr(j_common_ptr cinfo)` (`jerror.c:208-214`). -/
def reset_error_mgr (cinfo : DecompPtr) : M Unit := do
  let dc ← Ptr.load cinfo
  let err ← Ptr.load dc.err
  Ptr.store dc.err { err with numWarnings := 0, msgCode := 0 }

/-- `GLOBAL(struct jpeg_error_mgr *) jpeg_std_error(struct jpeg_error_mgr *err)` (`jerror.c:227-243`).
Zeroes `err` via `memset(err, 0, sizeof(struct jpeg_error_mgr))` (raising `Fault.ub` on `NULL`,
dangling, or non-base `err`), initializes method pointers and message table bounds, and returns `err`. -/
def jpeg_std_error (err : ErrPtr) : M ErrPtr := do
  memsetZeroErrMgr err
  let cur ← Ptr.load err
  let next : JpegErrorMgr := {
    cur with
    errorExit := .fn "error_exit"
    emitMessage := .fn "emit_message"
    outputMessage := .fn "output_message"
    formatMessage := .fn "format_message"
    resetErrorMgr := .fn "reset_error_mgr"
    jpegMessageTable := .ref .stdTable 0
    lastJpegMessage := JMSG_LASTMSGCODE - 1
  }
  Ptr.store err next
  return err

end Mozjpeg.Jerror
