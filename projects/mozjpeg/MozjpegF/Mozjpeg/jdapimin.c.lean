import MozjpegF.Mozjpeg.«jcomapi.c»
import MozjpegF.Mozjpeg.«jdmarker.c»
import MozjpegF.Mozjpeg.«jdinput.c»

/-!
# `jdapimin.c` — decompression API translations (`MozjpegF`)

Source: `mozjpeg/jdapimin.c` (`jpeg_CreateDecompress`, `jpeg_destroy_decompress`,
`jpeg_abort_decompress`, `jpeg_input_complete`, `jpeg_has_multiple_scans`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdapimin
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jmemmgr Mozjpeg.Jcomapi
open Mozjpeg.Jdmarker Mozjpeg.Jdinput Mozjpeg.Jdatasrc

/-- `GLOBAL(void) jpeg_CreateDecompress(j_decompress_ptr cinfo, int version, size_t structsize)`
(`jdapimin.c:35-99`). -/
def jpeg_CreateDecompress (cinfo : DecompPtr) (version : Int32) (structsize : UInt64) :
    M (JpegRes Unit) := do
  let dc0 ← Ptr.load cinfo
  Ptr.store cinfo { dc0 with mem := .null }
  if version != JPEG_LIB_VERSION then
    let _ ← errexit2 dc0.err JERR_BAD_LIB_VERSION JPEG_LIB_VERSION version
    return .errExit JERR_BAD_LIB_VERSION
  if structsize != sizeof_jpeg_decompress_struct then
    let _ ← errexit2 dc0.err JERR_BAD_STRUCT_SIZE
      (Int32.ofNat sizeof_jpeg_decompress_struct.toNat)
      (Int32.ofNat structsize.toNat)
    return .errExit JERR_BAD_STRUCT_SIZE
  let dc1 ← Ptr.load cinfo
  let err := dc1.err
  let client_data := dc1.clientData
  memsetZeroDecomp cinfo
  let dc2 ← Ptr.load cinfo
  Ptr.store cinfo { dc2 with err := err, clientData := client_data, isDecompressor := TRUE }
  match (← jinit_memory_mgr cinfo) with
  | .errExit code => return .errExit code
  | .ok () =>
    let dc3 ← Ptr.load cinfo
    Ptr.store cinfo {
      dc3 with
      progress := .null
      src := .null
      quantTblPtrs := Array.replicate 4 .null
      dcHuffTblPtrs := Array.replicate 4 .null
      acHuffTblPtrs := Array.replicate 4 .null
      markerList := .null
    }
    match (← jinit_marker_reader cinfo) with
    | .errExit code => return .errExit code
    | .ok () =>
      match (← jinit_input_controller cinfo) with
      | .errExit code => return .errExit code
      | .ok () =>
        let dc4 ← Ptr.load cinfo
        Ptr.store cinfo { dc4 with dataPrecision := 8, globalState := DSTATE_START }
        match (← alloc_small_master cinfo JPOOL_PERMANENT sizeof_my_decomp_master) with
        | .errExit code => return .errExit code
        | .ok mstPtr =>
          let dc5 ← Ptr.load cinfo
          Ptr.store cinfo { dc5 with master := mstPtr }
          memsetZeroMaster mstPtr
          return .ok ()

/-- `GLOBAL(void) jpeg_destroy_decompress(j_decompress_ptr cinfo)` (`jdapimin.c:106-110`). -/
def jpeg_destroy_decompress (cinfo : DecompPtr) : M Unit :=
  jpeg_destroy cinfo

/-- `GLOBAL(void) jpeg_abort_decompress(j_decompress_ptr cinfo)` (`jdapimin.c:118-122`). -/
def jpeg_abort_decompress (cinfo : DecompPtr) : M Unit :=
  jpeg_abort cinfo

/-- `GLOBAL(boolean) jpeg_input_complete(const j_decompress_ptr cinfo)` (`jdapimin.c:359-367`). -/
def jpeg_input_complete (cinfo : DecompPtr) : M (JpegRes Int32) := do
  let dc ← Ptr.load cinfo
  if dc.globalState < DSTATE_START || dc.globalState > DSTATE_STOPPING then
    let _ ← errexit1 dc.err JERR_BAD_STATE dc.globalState
    return .errExit JERR_BAD_STATE
  let ic ← Ptr.load dc.inputctl
  return .ok ic.eoiReached

/-- `GLOBAL(boolean) jpeg_has_multiple_scans(const j_decompress_ptr cinfo)` (`jdapimin.c:374-382`). -/
def jpeg_has_multiple_scans (cinfo : DecompPtr) : M (JpegRes Int32) := do
  let dc ← Ptr.load cinfo
  if dc.globalState < DSTATE_READY || dc.globalState > DSTATE_STOPPING then
    let _ ← errexit1 dc.err JERR_BAD_STATE dc.globalState
    return .errExit JERR_BAD_STATE
  let ic ← Ptr.load dc.inputctl
  return .ok ic.hasMultipleScans

/-- `LOCAL(void) default_decompress_parms(j_decompress_ptr cinfo)` (`jdapimin.c:129-236`). -/
def default_decompress_parms (cinfo : DecompPtr) : M Unit := do
  let dc0 ← Ptr.load cinfo
  if dc0.numComponents == 1 then
    Ptr.store cinfo { dc0 with jpegColorSpace := JCS_GRAYSCALE, outColorSpace := JCS_GRAYSCALE }
  else if dc0.numComponents == 3 then
    let jcs ← do
      if dc0.sawJFIFMarker != 0 then
        pure JCS_YCbCr
      else if dc0.sawAdobeMarker != 0 then
        if dc0.adobeTransform == 0 then pure JCS_RGB
        else if dc0.adobeTransform == 1 then pure JCS_YCbCr
        else
          warnms1 dc0.err JWRN_ADOBE_XFORM (Int32.ofNat dc0.adobeTransform.toNat)
          pure JCS_YCbCr
      else
        let p0 ← Ptr.add dc0.compInfo 0
        let p1 ← Ptr.add dc0.compInfo 1
        let p2 ← Ptr.add dc0.compInfo 2
        let cid0 := (← Ptr.load p0).componentId
        let cid1 := (← Ptr.load p1).componentId
        let cid2 := (← Ptr.load p2).componentId
        if cid0 == 1 && cid1 == 2 && cid2 == 3 then
          let mst ← Ptr.load dc0.master
          if mst.lossless != 0 then pure JCS_RGB else pure JCS_YCbCr
        else if cid0 == 82 && cid1 == 71 && cid2 == 66 then
          pure JCS_RGB
        else
          tracems3 dc0.err 1 JTRC_UNKNOWN_IDS cid0 cid1 cid2
          let mst ← Ptr.load dc0.master
          if mst.lossless != 0 then pure JCS_RGB else pure JCS_YCbCr
    let dc1 ← Ptr.load cinfo
    Ptr.store cinfo { dc1 with jpegColorSpace := jcs, outColorSpace := JCS_RGB }
  else if dc0.numComponents == 4 then
    let jcs ← do
      if dc0.sawAdobeMarker != 0 then
        if dc0.adobeTransform == 0 then pure JCS_CMYK
        else if dc0.adobeTransform == 2 then pure JCS_YCCK
        else
          warnms1 dc0.err JWRN_ADOBE_XFORM (Int32.ofNat dc0.adobeTransform.toNat)
          pure JCS_YCCK
      else
        pure JCS_CMYK
    let dc1 ← Ptr.load cinfo
    Ptr.store cinfo { dc1 with jpegColorSpace := jcs, outColorSpace := JCS_CMYK }
  else
    Ptr.store cinfo { dc0 with jpegColorSpace := JCS_UNKNOWN, outColorSpace := JCS_UNKNOWN }
  let dc2 ← Ptr.load cinfo
  Ptr.store cinfo {
    dc2 with
    scaleNum := 1
    scaleDenom := 1
    outputGamma := 0x3ff0000000000000
    bufferedImage := FALSE
    rawDataOut := FALSE
    dctMethod := JDCT_DEFAULT
    doFancyUpsampling := TRUE
    doBlockSmoothing := TRUE
    quantizeColors := FALSE
    ditherMode := JDITHER_FS
    twoPassQuantize := TRUE
    desiredNumberOfColors := 256
    colormap := .null
    enable1passQuant := FALSE
    enableExternalQuant := FALSE
    enable2passQuant := FALSE
  }

def callInitSource (cinfo : DecompPtr) (fn : FnPtr) : M Unit := do
  if fn == .fn "init_mem_source" then init_mem_source cinfo
  else if fn == .fn "noop" then return ()
  else ub "unsupported init_source"

def callTermSource (cinfo : DecompPtr) (fn : FnPtr) : M Unit := do
  if fn == .fn "term_source" then term_source cinfo
  else if fn == .fn "noop" then return ()
  else ub "unsupported term_source"

def callResetInputController (cinfo : DecompPtr) (fn : FnPtr) : M Unit := do
  if fn == .fn "reset_input_controller" then reset_input_controller cinfo
  else ub "unsupported reset_input_controller"

def callConsumeInput (cinfo : DecompPtr) (fn : FnPtr) : M (JpegRes Int32) := do
  if fn == .fn "consume_markers" then consume_markers cinfo
  else if fn == .fn "dummy_consume_data" then return .ok JPEG_SUSPENDED
  else ub "unsupported consume_input"

/-- `GLOBAL(int) jpeg_consume_input(j_decompress_ptr cinfo)` (`jdapimin.c:312-352`). -/
def jpeg_consume_input (cinfo : DecompPtr) : M (JpegRes Int32) := do
  let dc0 ← Ptr.load cinfo
  if dc0.globalState == DSTATE_START || dc0.globalState == DSTATE_INHEADER then
    if dc0.globalState == DSTATE_START then
      let ic0 ← Ptr.load dc0.inputctl
      callResetInputController cinfo ic0.resetInputController
      let dc1 ← Ptr.load cinfo
      let src1 ← Ptr.load dc1.src
      callInitSource cinfo src1.initSource
      let dc2 ← Ptr.load cinfo
      Ptr.store cinfo { dc2 with globalState := DSTATE_INHEADER }
    let dc3 ← Ptr.load cinfo
    let ic3 ← Ptr.load dc3.inputctl
    match (← callConsumeInput cinfo ic3.consumeInput) with
    | .errExit code => return .errExit code
    | .ok retcode =>
      if retcode == JPEG_REACHED_SOS then
        default_decompress_parms cinfo
        let dc4 ← Ptr.load cinfo
        Ptr.store cinfo { dc4 with globalState := DSTATE_READY }
      return .ok retcode
  else if dc0.globalState == DSTATE_READY then
    return .ok JPEG_REACHED_SOS
  else if dc0.globalState == DSTATE_PRELOAD || dc0.globalState == DSTATE_PRESCAN ||
      dc0.globalState == DSTATE_SCANNING || dc0.globalState == DSTATE_RAW_OK ||
      dc0.globalState == DSTATE_BUFIMAGE || dc0.globalState == DSTATE_BUFPOST ||
      dc0.globalState == DSTATE_STOPPING then
    let ic0 ← Ptr.load dc0.inputctl
    callConsumeInput cinfo ic0.consumeInput
  else
    let _ ← errexit1 dc0.err JERR_BAD_STATE dc0.globalState
    return .errExit JERR_BAD_STATE

/-- `GLOBAL(int) jpeg_read_header(j_decompress_ptr cinfo, boolean require_image)` (`jdapimin.c:266-297`). -/
def jpeg_read_header (cinfo : DecompPtr) (require_image : Int32) : M (JpegRes Int32) := do
  let dc0 ← Ptr.load cinfo
  if dc0.globalState != DSTATE_START && dc0.globalState != DSTATE_INHEADER then
    let _ ← errexit1 dc0.err JERR_BAD_STATE dc0.globalState
    return .errExit JERR_BAD_STATE
  match (← jpeg_consume_input cinfo) with
  | .errExit code => return .errExit code
  | .ok retcode =>
    if retcode == JPEG_REACHED_SOS then
      return .ok JPEG_HEADER_OK
    else if retcode == JPEG_REACHED_EOI then
      if require_image != 0 then
        let dc1 ← Ptr.load cinfo
        let _ ← errexit dc1.err JERR_NO_IMAGE
        return .errExit JERR_NO_IMAGE
      jpeg_abort cinfo
      return .ok JPEG_HEADER_TABLES_ONLY
    else
      return .ok retcode

structure FinishLoopState where
  done : Bool
  ret : JpegRes Int32

/-- `GLOBAL(boolean) jpeg_finish_decompress(j_decompress_ptr cinfo)` (`jdapimin.c:394-421`). -/
def jpeg_finish_decompress (cinfo : DecompPtr) : M (JpegRes Int32) := do
  let dc0 ← Ptr.load cinfo
  if (dc0.globalState == DSTATE_SCANNING || dc0.globalState == DSTATE_RAW_OK) &&
      dc0.bufferedImage == 0 then
    if dc0.outputScanline < dc0.outputHeight then
      let _ ← errexit dc0.err JERR_TOO_LITTLE_DATA
      return .errExit JERR_TOO_LITTLE_DATA
    let mst0 ← Ptr.load dc0.master
    if mst0.finishOutputPass != .fn "finish_output_pass" then
      ub "unsupported finish_output_pass"
    let dc1 ← Ptr.load cinfo
    Ptr.store cinfo { dc1 with globalState := DSTATE_STOPPING }
  else if dc0.globalState == DSTATE_BUFIMAGE then
    Ptr.store cinfo { dc0 with globalState := DSTATE_STOPPING }
  else if dc0.globalState != DSTATE_STOPPING then
    let _ ← errexit1 dc0.err JERR_BAD_STATE dc0.globalState
    return .errExit JERR_BAD_STATE
  let st ← cwhile
    (fun (s : FinishLoopState) => do
      if s.done then return (false, s)
      let dcL ← Ptr.load cinfo
      let icL ← Ptr.load dcL.inputctl
      return (icL.eoiReached == 0, s))
    (fun (_ : FinishLoopState) => do
      let dcL ← Ptr.load cinfo
      let icL ← Ptr.load dcL.inputctl
      match (← callConsumeInput cinfo icL.consumeInput) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok val =>
        if val == JPEG_SUSPENDED then
          return { done := true, ret := .ok FALSE }
        return { done := false, ret := .ok TRUE })
    { done := false, ret := .ok TRUE }
  if st.done then
    return st.ret
  let dcF ← Ptr.load cinfo
  let srcF ← Ptr.load dcF.src
  callTermSource cinfo srcF.termSource
  jpeg_abort cinfo
  return .ok TRUE

end Mozjpeg.Jdapimin
