import MozjpegF.Runtime.Libc

/-!
# `jerror.h` — error code constants and `ERREXIT*` macros (`MozjpegF`)

Source: `mozjpeg/jerror.h` (`JPEG_LIB_VERSION == 80`).
-/

set_option autoImplicit false

namespace Mozjpeg.JerrorH
open C

def JMSG_NOMESSAGE : Int32 := 0
def JERR_BAD_PRECISION : Int32 := 16
def JERR_BAD_STATE : Int32 := 21
def JERR_NO_IMAGE : Int32 := 53
def JERR_TOO_LITTLE_DATA : Int32 := 69
def JERR_UNKNOWN_MARKER : Int32 := 70
def JMSG_LASTMSGCODE : Int32 := 132

/-- Set `(cinfo)->err->msg_code = code` and unwind through `(*(cinfo)->err->error_exit)` (`jerror.h`). -/
def errexit (errPtr : ErrPtr) (code : Int32) : M (JpegRes Unit) := do
  let err ← Ptr.load errPtr
  Ptr.store errPtr { err with msgCode := code }
  return .errExit code

/-- `ERREXIT1(cinfo, code, p1)` (`jerror.h`). -/
def errexit1 (errPtr : ErrPtr) (code p1 : Int32) : M (JpegRes Unit) := do
  let err ← Ptr.load errPtr
  let parm := err.msgParmI.set! 0 p1
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  return .errExit code

end Mozjpeg.JerrorH
