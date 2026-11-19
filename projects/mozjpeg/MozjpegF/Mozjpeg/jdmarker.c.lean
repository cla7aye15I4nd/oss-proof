import MozjpegF.Mozjpeg.«jdatasrc.c»

/-!
# `jdmarker.c` — marker reader initialization, marker scanning, resync, and marker-saving (`MozjpegF`)

Source: `mozjpeg/jdmarker.c` (`next_marker`, `jpeg_resync_to_restart`, `reset_marker_reader`,
`jinit_marker_reader`, `jpeg_save_markers`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdmarker
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jmemmgr Mozjpeg.Jdatasrc

def APP0_DATA_LEN : UInt32 := 14
def APP14_DATA_LEN : UInt32 := 12

def M_SOF0 : Int32 := 0xc0
def M_RST0 : Int32 := 0xd0
def M_RST7 : Int32 := 0xd7
def M_EOI : Int32 := 0xd9
def M_APP0 : Int32 := 0xe0
def M_APP14 : Int32 := 0xee
def M_APP15 : Int32 := 0xef
def M_COM : Int32 := 0xfe

def sizeof_my_marker_reader : UInt64 := 264

def inputSync (cinfo : DecompPtr) (nib : BPtr) (bib : UInt64) : M Unit := do
  let dc ← Ptr.load cinfo
  let src ← Ptr.load dc.src
  Ptr.store dc.src { src with nextInputByte := nib, bytesInBuffer := bib }

def makeByteAvail (cinfo : DecompPtr) (nib : BPtr) (bib : UInt64) :
    M (Option (BPtr × UInt64)) := do
  if bib != 0 then
    return some (nib, bib)
  let dc ← Ptr.load cinfo
  let src ← Ptr.load dc.src
  if src.fillInputBuffer == .fn "fill_mem_input_buffer" then
    let ok ← fill_mem_input_buffer cinfo
    if ok == 0 then
      return none
    let src' ← Ptr.load dc.src
    if src'.bytesInBuffer == 0 then
      return none
    return some (src'.nextInputByte, src'.bytesInBuffer)
  else if src.fillInputBuffer == .fn "suspend_input" then
    return none
  else
    ub "unsupported fill_input_buffer"

def inputByte (cinfo : DecompPtr) (nib : BPtr) (bib : UInt64) :
    M (Option (Int32 × BPtr × UInt64)) := do
  match (← makeByteAvail cinfo nib bib) with
  | none => return none
  | some (nib1, bib1) =>
    let b ← Ptr.load nib1
    let nib2 ← Ptr.add nib1 1
    return some (Int32.ofNat b.toNat, nib2, bib1 - 1)

structure NextMarkerState where
  done : Bool
  ret : Int32
  c : Int32
  nib : BPtr
  bib : UInt64

structure ByteScanState where
  susp : Bool
  c : Int32
  nib : BPtr
  bib : UInt64

/-- `LOCAL(boolean) next_marker(j_decompress_ptr cinfo)` (`jdmarker.c:889-933`). -/
def next_marker (cinfo : DecompPtr) : M Int32 := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  let initSt : NextMarkerState :=
    { done := false, ret := TRUE, c := 0, nib := src0.nextInputByte, bib := src0.bytesInBuffer }
  let st ← cwhile
    (fun (s : NextMarkerState) => pure (!s.done, s))
    (fun (s : NextMarkerState) => do
      match (← inputByte cinfo s.nib s.bib) with
      | none => return { s with done := true, ret := FALSE }
      | some (c0, nib0, bib0) =>
        let sk0 : ByteScanState := { susp := false, c := c0, nib := nib0, bib := bib0 }
        let sk ← cwhile
          (fun (bs : ByteScanState) => pure (!bs.susp && bs.c != 0xFF, bs))
          (fun (bs : ByteScanState) => do
            let dc ← Ptr.load cinfo
            let mrk ← Ptr.load dc.marker
            Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 1 }
            inputSync cinfo bs.nib bs.bib
            match (← inputByte cinfo bs.nib bs.bib) with
            | none => return { bs with susp := true }
            | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
          sk0
        if sk.susp then
          return { s with done := true, ret := FALSE }
        let fd0 : ByteScanState := { susp := false, c := sk.c, nib := sk.nib, bib := sk.bib }
        let fd ← cdoWhile
          (fun (bs : ByteScanState) => do
            match (← inputByte cinfo bs.nib bs.bib) with
            | none => return { bs with susp := true }
            | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
          (fun (bs : ByteScanState) => pure (!bs.susp && bs.c == 0xFF, bs))
          fd0
        if fd.susp then
          return { s with done := true, ret := FALSE }
        if fd.c != 0 then
          return { done := true, ret := TRUE, c := fd.c, nib := fd.nib, bib := fd.bib }
        let dc ← Ptr.load cinfo
        let mrk ← Ptr.load dc.marker
        Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 2 }
        inputSync cinfo fd.nib fd.bib
        return { done := false, ret := TRUE, c := fd.c, nib := fd.nib, bib := fd.bib })
    initSt
  if st.ret == 0 then
    return FALSE
  let dc1 ← Ptr.load cinfo
  let mrk1 ← Ptr.load dc1.marker
  if mrk1.discardedBytes != 0 then
    warnms2 dc1.err JWRN_EXTRANEOUS_DATA (Int32.ofNat mrk1.discardedBytes.toNat) st.c
    let mrk2 ← Ptr.load dc1.marker
    Ptr.store dc1.marker { mrk2 with discardedBytes := 0 }
  let dc2 ← Ptr.load cinfo
  let src2 ← Ptr.load dc2.src
  Ptr.store dc2.src { src2 with nextInputByte := st.nib, bytesInBuffer := st.bib }
  Ptr.store cinfo { dc2 with unreadMarker := st.c }
  return TRUE

structure ResyncState where
  done : Bool
  ret : Int32
  marker : Int32

/-- `GLOBAL(boolean) jpeg_resync_to_restart(j_decompress_ptr cinfo, int desired)` (`jdmarker.c:1215-1258`).
Emits `JWRN_MUST_RESYNC` and scans ahead via `next_marker` until synchronized on a restart or
subsequent marker, returning `FALSE` on input suspension and `TRUE` otherwise. -/
def jpeg_resync_to_restart (cinfo : DecompPtr) (desired : Int32) : M Int32 := do
  let dc0 ← Ptr.load cinfo
  let marker0 := dc0.unreadMarker
  warnms2 dc0.err JWRN_MUST_RESYNC marker0 desired
  let initR : ResyncState := { done := false, ret := TRUE, marker := marker0 }
  let st ← cwhile
    (fun (s : ResyncState) => pure (!s.done, s))
    (fun (s : ResyncState) => do
      let action ← do
        if s.marker < M_SOF0 then
          pure (2 : Int32)
        else if s.marker < M_RST0 || s.marker > M_RST7 then
          pure (3 : Int32)
        else
          let p1 ← i32Add desired 1
          let p2 ← i32Add desired 2
          let m1 ← i32Sub desired 1
          let m2 ← i32Sub desired 2
          let r_p1 := M_RST0 + Int32.ofInt (p1.toInt % 8)
          let r_p2 := M_RST0 + Int32.ofInt (p2.toInt % 8)
          let r_m1 := M_RST0 + Int32.ofInt (m1.toInt % 8)
          let r_m2 := M_RST0 + Int32.ofInt (m2.toInt % 8)
          if s.marker == r_p1 || s.marker == r_p2 then
            pure (3 : Int32)
          else if s.marker == r_m1 || s.marker == r_m2 then
            pure (2 : Int32)
          else
            pure (1 : Int32)
      let dc ← Ptr.load cinfo
      tracems2 dc.err 4 JTRC_RECOVERY_ACTION s.marker action
      if action == 1 then
        Ptr.store cinfo { dc with unreadMarker := 0 }
        return { done := true, ret := TRUE, marker := s.marker }
      else if action == 2 then
        let nm ← next_marker cinfo
        if nm == 0 then
          return { done := true, ret := FALSE, marker := s.marker }
        let dc' ← Ptr.load cinfo
        return { done := false, ret := s.ret, marker := dc'.unreadMarker }
      else
        return { done := true, ret := TRUE, marker := s.marker })
    initR
  return st.ret

/-- `METHODDEF(void) reset_marker_reader(j_decompress_ptr cinfo)` (`jdmarker.c:1265-1277`). -/
def reset_marker_reader (cinfo : DecompPtr) : M Unit := do
  let dc ← Ptr.load cinfo
  Ptr.store cinfo { dc with compInfo := .null, inputScanNumber := 0, unreadMarker := 0 }
  let mrk ← Ptr.load dc.marker
  Ptr.store dc.marker {
    mrk with
    sawSOI := FALSE
    sawSOF := FALSE
    discardedBytes := 0
    curMarker := .null
  }

/-- `GLOBAL(void) jinit_marker_reader(j_decompress_ptr cinfo)` (`jdmarker.c:1285-1314`). -/
def jinit_marker_reader (cinfo : DecompPtr) : M (JpegRes Unit) := do
  match (← alloc_small_marker cinfo JPOOL_PERMANENT sizeof_my_marker_reader) with
  | .errExit code => return .errExit code
  | .ok mrkPtr =>
    let dc ← Ptr.load cinfo
    Ptr.store cinfo { dc with marker := mrkPtr }
    let apps := ((Array.replicate 16 (.fn "skip_variable")).set! 0 (.fn "get_interesting_appn")).set! 14 (.fn "get_interesting_appn")
    Ptr.store mrkPtr {
      resetMarkerReader := .fn "reset_marker_reader"
      readMarkers := .fn "read_markers"
      readRestartMarker := .fn "read_restart_marker"
      processCOM := .fn "skip_variable"
      lengthLimitCOM := 0
      processAPPn := apps
      lengthLimitAPPn := Array.replicate 16 0
    }
    reset_marker_reader cinfo
    return .ok ()

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
