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
def JERR_BAD_COMPONENT_ID : Int32 := 4
def JERR_BAD_HUFF_TABLE : Int32 := 9
def JERR_BAD_LENGTH : Int32 := 12
def JERR_BAD_LIB_VERSION : Int32 := 13
def JERR_BAD_MCU_SIZE : Int32 := 14
def JERR_BAD_POOL_ID : Int32 := 15
def JERR_BAD_PRECISION : Int32 := 16
def JERR_BAD_SAMPLING : Int32 := 19
def JERR_BAD_STATE : Int32 := 21
def JERR_BAD_STRUCT_SIZE : Int32 := 22
def JERR_BUFFER_SIZE : Int32 := 24
def JERR_COMPONENT_COUNT : Int32 := 27
def JERR_DAC_INDEX : Int32 := 29
def JERR_DAC_VALUE : Int32 := 30
def JERR_DHT_INDEX : Int32 := 31
def JERR_DQT_INDEX : Int32 := 32
def JERR_EMPTY_IMAGE : Int32 := 33
def JERR_EOI_EXPECTED : Int32 := 36
def JERR_IMAGE_TOO_BIG : Int32 := 42
def JERR_INPUT_EMPTY : Int32 := 43
def JERR_NO_IMAGE : Int32 := 53
def JERR_NO_QUANT_TABLE : Int32 := 54
def JERR_NO_SOI : Int32 := 55
def JERR_OUT_OF_MEMORY : Int32 := 56
def JERR_SOF_DUPLICATE : Int32 := 60
def JERR_SOF_NO_SOS : Int32 := 61
def JERR_SOF_UNSUPPORTED : Int32 := 62
def JERR_SOI_DUPLICATE : Int32 := 63
def JERR_SOS_NO_SOF : Int32 := 64
def JERR_TOO_LITTLE_DATA : Int32 := 69
def JERR_UNKNOWN_MARKER : Int32 := 70
def JTRC_ADOBE : Int32 := 78
def JTRC_APP0 : Int32 := 79
def JTRC_APP14 : Int32 := 80
def JTRC_DAC : Int32 := 81
def JTRC_DHT : Int32 := 82
def JTRC_DQT : Int32 := 83
def JTRC_DRI : Int32 := 84
def JTRC_EOI : Int32 := 87
def JTRC_HUFFBITS : Int32 := 88
def JTRC_JFIF : Int32 := 89
def JTRC_JFIF_BADTHUMBNAILSIZE : Int32 := 90
def JTRC_JFIF_EXTENSION : Int32 := 91
def JTRC_JFIF_THUMBNAIL : Int32 := 92
def JTRC_MISC_MARKER : Int32 := 93
def JTRC_PARMLESS_MARKER : Int32 := 94
def JTRC_QUANTVALS : Int32 := 95
def JTRC_RECOVERY_ACTION : Int32 := 99
def JTRC_RST : Int32 := 100
def JTRC_SOF : Int32 := 102
def JTRC_SOF_COMPONENT : Int32 := 103
def JTRC_SOI : Int32 := 104
def JTRC_SOS : Int32 := 105
def JTRC_SOS_COMPONENT : Int32 := 106
def JTRC_SOS_PARAMS : Int32 := 107
def JTRC_THUMB_JPEG : Int32 := 110
def JTRC_THUMB_PALETTE : Int32 := 111
def JTRC_THUMB_RGB : Int32 := 112
def JTRC_UNKNOWN_IDS : Int32 := 113
def JWRN_ADOBE_XFORM : Int32 := 116
def JWRN_EXTRANEOUS_DATA : Int32 := 119
def JWRN_JFIF_MAJOR : Int32 := 122
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

/-- `WARNMS1(cinfo, code, p1)` (`jerror.h:289-292`). -/
def warnms1 (errPtr : ErrPtr) (code p1 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := err.msgParmI.set! 0 p1
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr (-1)

/-- `WARNMS2(cinfo, code, p1, p2)` (`jerror.h:293-297`). -/
def warnms2 (errPtr : ErrPtr) (code p1 p2 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := (err.msgParmI.set! 0 p1).set! 1 p2
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr (-1)

/-- `TRACEMS(cinfo, lvl, code)` (`jerror.h:300-302`). -/
def tracems (errPtr : ErrPtr) (lvl code : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  Ptr.store errPtr { err with msgCode := code }
  emitMessage errPtr lvl

/-- `TRACEMS1(cinfo, lvl, code, p1)` (`jerror.h:303-306`). -/
def tracems1 (errPtr : ErrPtr) (lvl code p1 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := err.msgParmI.set! 0 p1
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr lvl

/-- `TRACEMS2(cinfo, lvl, code, p1, p2)` (`jerror.h:307-311`). -/
def tracems2 (errPtr : ErrPtr) (lvl code p1 p2 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := (err.msgParmI.set! 0 p1).set! 1 p2
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr lvl

/-- `TRACEMS3(cinfo, lvl, code, p1, p2, p3)` (`jerror.h:312-316`). -/
def tracems3 (errPtr : ErrPtr) (lvl code p1 p2 p3 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := ((err.msgParmI.set! 0 p1).set! 1 p2).set! 2 p3
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr lvl

/-- `TRACEMS4(cinfo, lvl, code, p1, p2, p3, p4)` (`jerror.h:317-321`). -/
def tracems4 (errPtr : ErrPtr) (lvl code p1 p2 p3 p4 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := (((err.msgParmI.set! 0 p1).set! 1 p2).set! 2 p3).set! 3 p4
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr lvl

/-- `TRACEMS5(cinfo, lvl, code, p1, p2, p3, p4, p5)` (`jerror.h:322-327`). -/
def tracems5 (errPtr : ErrPtr) (lvl code p1 p2 p3 p4 p5 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := ((((err.msgParmI.set! 0 p1).set! 1 p2).set! 2 p3).set! 3 p4).set! 4 p5
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr lvl

/-- `TRACEMS8(cinfo, lvl, code, p1..p8)` (`jerror.h:328-333`). -/
def tracems8 (errPtr : ErrPtr) (lvl code p1 p2 p3 p4 p5 p6 p7 p8 : Int32) : M Unit := do
  let err ← Ptr.load errPtr
  let parm := #[p1, p2, p3, p4, p5, p6, p7, p8]
  Ptr.store errPtr { err with msgCode := code, msgParmI := parm }
  emitMessage errPtr lvl

end Mozjpeg.JerrorH
