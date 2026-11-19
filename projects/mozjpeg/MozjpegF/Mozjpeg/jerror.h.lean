import MozjpegF.Runtime.Libc

/-!
# `jerror.h` — error code constants and `ERREXIT*` macros (`MozjpegF`)

Source: `mozjpeg/jerror.h` (`JPEG_LIB_VERSION == 80`).
-/

set_option autoImplicit false

namespace Mozjpeg.JerrorH
open C

def JMSG_NOMESSAGE : Int32 := 0
def JERR_BAD_ALIGN_TYPE : Int32 := 1
def JERR_BAD_ALLOC_CHUNK : Int32 := 2
def JERR_BAD_LIB_VERSION : Int32 := 13
def JERR_BAD_POOL_ID : Int32 := 15
def JERR_BAD_PRECISION : Int32 := 16
def JERR_BAD_STATE : Int32 := 21
def JERR_BAD_STRUCT_SIZE : Int32 := 22
def JERR_BUFFER_SIZE : Int32 := 24
def JERR_INPUT_EMPTY : Int32 := 43
def JERR_NO_IMAGE : Int32 := 53
def JERR_OUT_OF_MEMORY : Int32 := 56
def JERR_TOO_LITTLE_DATA : Int32 := 69
def JERR_UNKNOWN_MARKER : Int32 := 70
def JTRC_RECOVERY_ACTION : Int32 := 99
def JWRN_EXTRANEOUS_DATA : Int32 := 119
def JWRN_JPEG_EOF : Int32 := 123
def JWRN_MUST_RESYNC : Int32 := 124
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

/-- `ERREXIT2(cinfo, code, p1, p2)` (`jerror.h`). -/
def errexit2 (errPtr : ErrPtr) (code p1 p2 : Int32) : M (JpegRes Unit) := do
  let err ← Ptr.load errPtr
  let parm := (err.msgParmI.set! 0 p1).set! 1 p2
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  return .errExit code

/-- Dispatch `(*(cinfo)->err->emit_message)(cinfo, msg_level)` for standard `jerror.c` handler. -/
def emitMessage (errPtr : ErrPtr) (msg_level : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  if msg_level < 0 then
    let nw ← i64Add err.numWarnings 1
    Ptr.store errPtr { err with numWarnings := nw }
  else
    pure ()

/-- `WARNMS(cinfo, code)` (`jerror.h:286-288`). -/
def warnms (errPtr : ErrPtr) (code : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  Ptr.store errPtr { err with msgCode := code }
  emitMessage errPtr (-1)

/-- `WARNMS2(cinfo, code, p1, p2)` (`jerror.h:293-297`). -/
def warnms2 (errPtr : ErrPtr) (code p1 p2 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := (err.msgParmI.set! 0 p1).set! 1 p2
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr (-1)

/-- `TRACEMS2(cinfo, lvl, code, p1, p2)` (`jerror.h:307-311`). -/
def tracems2 (errPtr : ErrPtr) (lvl code p1 p2 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := (err.msgParmI.set! 0 p1).set! 1 p2
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr lvl

end Mozjpeg.JerrorH
