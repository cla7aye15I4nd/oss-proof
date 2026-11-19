import MozjpegF.Mozjpeg.«jpeglib.h»

/-!
# `jdmarker.c` — marker-saving configuration translation (`MozjpegF`)

Source: `mozjpeg/jdmarker.c:1323-1363` (`jpeg_save_markers`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdmarker
open C Mozjpeg.JpeglibH Mozjpeg.JerrorH

def APP0_DATA_LEN : UInt32 := 14
def APP14_DATA_LEN : UInt32 := 12

def M_APP0 : Int32 := 0xe0
def M_APP14 : Int32 := 0xee
def M_APP15 : Int32 := 0xef
def M_COM : Int32 := 0xfe

/-- `GLOBAL(void) jpeg_save_markers(j_decompress_ptr cinfo, int marker_code, unsigned int length_limit)`
(`jdmarker.c:1323-1363`). Configures the COM/APPn marker parser and byte limit on `cinfo->marker`,
or triggers `ERREXIT1(cinfo, JERR_UNKNOWN_MARKER, marker_code)` on unsupported marker codes. -/
def jpeg_save_markers (cinfo : DecompPtr) (marker_code : Int32) (length_limit : UInt32) :
    M (JpegRes Unit) := do
  let dc ← Ptr.load cinfo
  let marker ← Ptr.load dc.marker
  let mem ← Ptr.load dc.mem
  let maxlength : Int64 :=
    Int64.ofInt ((mem.maxAllocChunk.toInt) - sizeof_jpeg_marker_struct.toInt)
  let limit : UInt32 :=
    if Int64.ofNat length_limit.toNat > maxlength then
      maxlength.toInt.toNat.toUInt32
    else
      length_limit
  let (processor, finalLimit) : FnPtr × UInt32 :=
    if limit != 0 then
      let lim :=
        if marker_code == M_APP0 && limit < APP0_DATA_LEN then APP0_DATA_LEN
        else if marker_code == M_APP14 && limit < APP14_DATA_LEN then APP14_DATA_LEN
        else limit
      (.fn "save_marker", lim)
    else
      let proc :=
        if marker_code == M_APP0 || marker_code == M_APP14 then .fn "get_interesting_appn"
        else .fn "skip_variable"
      (proc, 0)
  if marker_code == M_COM then
    Ptr.store dc.marker { marker with processCOM := processor, lengthLimitCOM := finalLimit }
    return .ok ()
  else if marker_code ≥ M_APP0 && marker_code ≤ M_APP15 then
    let idx := (marker_code - M_APP0).toInt.toNat
    Ptr.store dc.marker {
      marker with
      processAPPn := marker.processAPPn.set! idx processor
      lengthLimitAPPn := marker.lengthLimitAPPn.set! idx finalLimit
    }
    return .ok ()
  else
    let _ ← errexit1 dc.err JERR_UNKNOWN_MARKER marker_code
    return .errExit JERR_UNKNOWN_MARKER

end Mozjpeg.Jdmarker
