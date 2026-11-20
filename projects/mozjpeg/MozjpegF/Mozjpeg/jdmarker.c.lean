import MozjpegF.Mozjpeg.«jdatasrc.c»
import MozjpegF.Mozjpeg.«jutils.c»
import MozjpegF.Mozjpeg.«jcomapi.c»

/-!
# `jdmarker.c` — marker reader initialization, marker scanning, resync, and marker-saving (`MozjpegF`)

Source: `mozjpeg/jdmarker.c` (full marker reader: `get_soi`, `get_sof`, `get_sos`, `get_dac`,
`get_dht`, `get_dqt`, `get_dri`, `get_interesting_appn`, `save_marker`, `skip_variable`,
`next_marker`, `first_marker`, `read_markers`, `read_restart_marker`, `jpeg_resync_to_restart`,
`reset_marker_reader`, `jinit_marker_reader`, `jpeg_save_markers`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdmarker
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jmemmgr Mozjpeg.Jdatasrc
open Mozjpeg.Jutils Mozjpeg.Jcomapi

def APP0_DATA_LEN : UInt32 := 14
def APP14_DATA_LEN : UInt32 := 12
def APPN_DATA_LEN : UInt32 := 14

def M_TEM : Int32 := 0x01
def M_SOF0 : Int32 := 0xc0
def M_SOF1 : Int32 := 0xc1
def M_SOF2 : Int32 := 0xc2
def M_SOF3 : Int32 := 0xc3
def M_DHT : Int32 := 0xc4
def M_SOF5 : Int32 := 0xc5
def M_SOF6 : Int32 := 0xc6
def M_SOF7 : Int32 := 0xc7
def M_JPG : Int32 := 0xc8
def M_SOF9 : Int32 := 0xc9
def M_SOF10 : Int32 := 0xca
def M_SOF11 : Int32 := 0xcb
def M_DAC : Int32 := 0xcc
def M_SOF13 : Int32 := 0xcd
def M_SOF14 : Int32 := 0xce
def M_SOF15 : Int32 := 0xcf
def M_RST0 : Int32 := 0xd0
def M_RST1 : Int32 := 0xd1
def M_RST2 : Int32 := 0xd2
def M_RST3 : Int32 := 0xd3
def M_RST4 : Int32 := 0xd4
def M_RST5 : Int32 := 0xd5
def M_RST6 : Int32 := 0xd6
def M_RST7 : Int32 := 0xd7
def M_SOI : Int32 := 0xd8
def M_EOI : Int32 := 0xd9
def M_SOS : Int32 := 0xda
def M_DQT : Int32 := 0xdb
def M_DNL : Int32 := 0xdc
def M_DRI : Int32 := 0xdd
def M_APP0 : Int32 := 0xe0
def M_APP1 : Int32 := 0xe1
def M_APP2 : Int32 := 0xe2
def M_APP3 : Int32 := 0xe3
def M_APP4 : Int32 := 0xe4
def M_APP5 : Int32 := 0xe5
def M_APP6 : Int32 := 0xe6
def M_APP7 : Int32 := 0xe7
def M_APP8 : Int32 := 0xe8
def M_APP9 : Int32 := 0xe9
def M_APP10 : Int32 := 0xea
def M_APP11 : Int32 := 0xeb
def M_APP12 : Int32 := 0xec
def M_APP13 : Int32 := 0xed
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

def input2Bytes (cinfo : DecompPtr) (nib : BPtr) (bib : UInt64) :
    M (Option (Int32 × BPtr × UInt64)) := do
  match (← inputByte cinfo nib bib) with
  | none => return none
  | some (b1, nib1, bib1) =>
    match (← inputByte cinfo nib1 bib1) with
    | none => return none
    | some (b2, nib2, bib2) =>
      return some ((b1 <<< 8) + b2, nib2, bib2)

def skipInputDataDispatch (cinfo : DecompPtr) (numBytes : Int64) : M Unit := do
  let dc ← Ptr.load cinfo
  let src ← Ptr.load dc.src
  if src.skipInputData == .fn "skip_input_data" then
    skip_input_data cinfo numBytes
  else if src.skipInputData == .fn "suspend_skip_input_data" then
    return ()
  else
    ub "unsupported skip_input_data"

/-- `LOCAL(boolean) get_soi(j_decompress_ptr cinfo)` (`jdmarker.c:201-238`). -/
def get_soi (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc ← Ptr.load cinfo
  tracems dc.err 1 JTRC_SOI
  let mrk ← Ptr.load dc.marker
  if mrk.sawSOI != 0 then
    let _ ← errexit dc.err JERR_SOI_DUPLICATE
    return .errExit JERR_SOI_DUPLICATE
  let dc' ← Ptr.load cinfo
  Ptr.store cinfo {
    dc' with
    arithDcL := Array.replicate 16 0
    arithDcU := Array.replicate 16 1
    arithAcK := Array.replicate 16 5
    restartInterval := 0
    jpegColorSpace := JCS_UNKNOWN
    ccir601Sampling := FALSE
    sawJFIFMarker := FALSE
    jfifMajorVersion := 1
    jfifMinorVersion := 1
    densityUnit := 0
    xDensity := 1
    yDensity := 1
    sawAdobeMarker := FALSE
    adobeTransform := 0
  }
  let mrk' ← Ptr.load dc'.marker
  Ptr.store dc'.marker { mrk' with sawSOI := TRUE }
  return .ok true

structure SofLoopState where
  done : Bool
  ret : JpegRes Bool
  ci : Nat
  nib : BPtr
  bib : UInt64

/-- `LOCAL(boolean) get_sof(j_decompress_ptr cinfo, boolean is_prog, boolean is_lossless, boolean is_arith)` (`jdmarker.c:241-304`). -/
def get_sof (cinfo : DecompPtr) (is_prog is_lossless is_arith : Int32) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  let mrk0 ← Ptr.load dc0.marker
  if mrk0.sawSOF != 0 then
    let _ ← errexit dc0.err JERR_SOF_DUPLICATE
    return .errExit JERR_SOF_DUPLICATE
  Ptr.store cinfo { dc0 with progressiveMode := is_prog, arithCode := is_arith }
  let mst0 ← Ptr.load dc0.master
  Ptr.store dc0.master { mst0 with lossless := is_lossless }
  match (← input2Bytes cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (lenRaw, nib1, bib1) =>
    match (← inputByte cinfo nib1 bib1) with
    | none => return .ok false
    | some (dp, nib2, bib2) =>
      let dc1 ← Ptr.load cinfo
      Ptr.store cinfo { dc1 with dataPrecision := dp }
      match (← input2Bytes cinfo nib2 bib2) with
      | none => return .ok false
      | some (ih, nib3, bib3) =>
        let dc2 ← Ptr.load cinfo
        Ptr.store cinfo { dc2 with imageHeight := UInt32.ofNat ih.toInt.toNat }
        match (← input2Bytes cinfo nib3 bib3) with
        | none => return .ok false
        | some (iw, nib4, bib4) =>
          let dc3 ← Ptr.load cinfo
          Ptr.store cinfo { dc3 with imageWidth := UInt32.ofNat iw.toInt.toNat }
          match (← inputByte cinfo nib4 bib4) with
          | none => return .ok false
          | some (nc, nib5, bib5) =>
            let dc4 ← Ptr.load cinfo
            let dc4' := { dc4 with numComponents := nc }
            Ptr.store cinfo dc4'
            let length : Int64 := Int64.ofInt (lenRaw.toInt - 8)
            tracems4 dc4'.err 1 JTRC_SOF dc4'.unreadMarker
              (Int32.ofNat dc4'.imageWidth.toNat) (Int32.ofNat dc4'.imageHeight.toNat) dc4'.numComponents
            if dc4'.imageHeight == 0 || dc4'.imageWidth == 0 || dc4'.numComponents ≤ 0 then
              let _ ← errexit dc4'.err JERR_EMPTY_IMAGE
              return .errExit JERR_EMPTY_IMAGE
            if length.toInt != dc4'.numComponents.toInt * 3 then
              let _ ← errexit dc4'.err JERR_BAD_LENGTH
              return .errExit JERR_BAD_LENGTH
            let dc5 ← Ptr.load cinfo
            if dc5.compInfo == .null then
              let nComps := dc5.numComponents.toInt.toNat
              match (← alloc_small_comps cinfo JPOOL_IMAGE nComps
                  (UInt64.ofNat nComps * sizeof_jpeg_component_info)) with
              | .errExit code => return .errExit code
              | .ok compP =>
                let dc6 ← Ptr.load cinfo
                Ptr.store cinfo { dc6 with compInfo := compP }
            let dc7 ← Ptr.load cinfo
            let nComps := dc7.numComponents.toInt.toNat
            let st ← cwhile
              (fun (s : SofLoopState) => pure (!s.done && s.ci < nComps, s))
              (fun (s : SofLoopState) => do
                let cp ← Ptr.add dc7.compInfo (Int.ofNat s.ci)
                let comp0 ← Ptr.load cp
                Ptr.store cp { comp0 with componentIndex := Int32.ofNat s.ci }
                match (← inputByte cinfo s.nib s.bib) with
                | none => return { s with done := true, ret := .ok false }
                | some (cid, nibA, bibA) =>
                  let comp1 ← Ptr.load cp
                  Ptr.store cp { comp1 with componentId := cid }
                  match (← inputByte cinfo nibA bibA) with
                  | none => return { s with done := true, ret := .ok false }
                  | some (cbyte, nibB, bibB) =>
                    let comp2 ← Ptr.load cp
                    Ptr.store cp {
                      comp2 with
                      hSampFactor := (cbyte >>> 4) &&& 15
                      vSampFactor := cbyte &&& 15
                    }
                    match (← inputByte cinfo nibB bibB) with
                    | none => return { s with done := true, ret := .ok false }
                    | some (qno, nibC, bibC) =>
                      let comp3 ← Ptr.load cp
                      let comp4 := { comp3 with quantTblNo := qno }
                      Ptr.store cp comp4
                      tracems4 dc7.err 1 JTRC_SOF_COMPONENT
                        comp4.componentId comp4.hSampFactor comp4.vSampFactor comp4.quantTblNo
                      return { done := false, ret := .ok true, ci := s.ci + 1, nib := nibC, bib := bibC })
              { done := false, ret := .ok true, ci := 0, nib := nib5, bib := bib5 }
            if st.done then
              return st.ret
            let dcEnd ← Ptr.load cinfo
            let mrkEnd ← Ptr.load dcEnd.marker
            Ptr.store dcEnd.marker { mrkEnd with sawSOF := TRUE }
            inputSync cinfo st.nib st.bib
            return .ok true

structure SosLoopState where
  done : Bool
  ret : JpegRes Bool
  i : Nat
  nib : BPtr
  bib : UInt64

/-- `LOCAL(boolean) get_sos(j_decompress_ptr cinfo)` (`jdmarker.c:307-385`). -/
def get_sos (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  let mrk0 ← Ptr.load dc0.marker
  if mrk0.sawSOF == 0 then
    let _ ← errexit dc0.err JERR_SOS_NO_SOF
    return .errExit JERR_SOS_NO_SOF
  match (← input2Bytes cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (lenRaw, nib1, bib1) =>
    match (← inputByte cinfo nib1 bib1) with
    | none => return .ok false
    | some (n, nib2, bib2) =>
      tracems1 dc0.err 1 JTRC_SOS n
      if lenRaw.toInt != n.toInt * 2 + 6 || n < 1 || n > MAX_COMPS_IN_SCAN then
        let _ ← errexit dc0.err JERR_BAD_LENGTH
        return .errExit JERR_BAD_LENGTH
      let dc1 ← Ptr.load cinfo
      Ptr.store cinfo { dc1 with compsInScan := n, curCompInfo := Array.replicate 4 .null }
      let nNat := n.toInt.toNat
      let st ← cwhile
        (fun (s : SosLoopState) => pure (!s.done && s.i < nNat, s))
        (fun (s : SosLoopState) => do
          match (← inputByte cinfo s.nib s.bib) with
          | none => return { s with done := true, ret := .ok false }
          | some (cc, nibA, bibA) =>
            match (← inputByte cinfo nibA bibA) with
            | none => return { s with done := true, ret := .ok false }
            | some (cbyte, nibB, bibB) =>
              let dcCur ← Ptr.load cinfo
              let lim := min dcCur.numComponents.toInt.toNat MAX_COMPS_IN_SCAN.toInt.toNat
              let mut found : Option CompPtr := none
              for ci in List.range lim do
                if found.isNone then
                  let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
                  let comp ← Ptr.load cp
                  if cc == comp.componentId && dcCur.curCompInfo[ci]! == .null then
                    found := some cp
              match found with
              | none =>
                let _ ← errexit1 dcCur.err JERR_BAD_COMPONENT_ID cc
                return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
              | some cp =>
                Ptr.store cinfo { dcCur with curCompInfo := dcCur.curCompInfo.set! s.i cp }
                let comp ← Ptr.load cp
                let comp' := { comp with dcTblNo := (cbyte >>> 4) &&& 15, acTblNo := cbyte &&& 15 }
                Ptr.store cp comp'
                tracems3 dcCur.err 1 JTRC_SOS_COMPONENT cc comp'.dcTblNo comp'.acTblNo
                let dcChk ← Ptr.load cinfo
                for pi in List.range s.i do
                  if dcChk.curCompInfo[pi]! == cp then
                    let _ ← errexit1 dcChk.err JERR_BAD_COMPONENT_ID cc
                    return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
                return { done := false, ret := .ok true, i := s.i + 1, nib := nibB, bib := bibB })
        { done := false, ret := .ok true, i := 0, nib := nib2, bib := bib2 }
      if st.done then
        return st.ret
      match (← inputByte cinfo st.nib st.bib) with
      | none => return .ok false
      | some (ssVal, nibS, bibS) =>
        let dcS ← Ptr.load cinfo
        Ptr.store cinfo { dcS with ss := ssVal }
        match (← inputByte cinfo nibS bibS) with
        | none => return .ok false
        | some (seVal, nibE, bibE) =>
          let dcE ← Ptr.load cinfo
          Ptr.store cinfo { dcE with se := seVal }
          match (← inputByte cinfo nibE bibE) with
          | none => return .ok false
          | some (ahAl, nibEnd, bibEnd) =>
            let dcF ← Ptr.load cinfo
            let dcF' := { dcF with ah := (ahAl >>> 4) &&& 15, al := ahAl &&& 15 }
            Ptr.store cinfo dcF'
            tracems4 dcF'.err 1 JTRC_SOS_PARAMS dcF'.ss dcF'.se dcF'.ah dcF'.al
            let mrkF ← Ptr.load dcF'.marker
            Ptr.store dcF'.marker { mrkF with nextRestartNum := 0 }
            let isn ← i32Add dcF'.inputScanNumber 1
            let dcF2 ← Ptr.load cinfo
            Ptr.store cinfo { dcF2 with inputScanNumber := isn }
            inputSync cinfo nibEnd bibEnd
            return .ok true

structure DacLoopState where
  done : Bool
  ret : JpegRes Bool
  length : Int64
  nib : BPtr
  bib : UInt64

/-- `LOCAL(boolean) get_dac(j_decompress_ptr cinfo)` (`jdmarker.c:390-427`). -/
def get_dac (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  match (← input2Bytes cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (lenRaw, nib1, bib1) =>
    let st ← cwhile
      (fun (s : DacLoopState) => pure (!s.done && s.length > 0, s))
      (fun (s : DacLoopState) => do
        match (← inputByte cinfo s.nib s.bib) with
        | none => return { s with done := true, ret := .ok false }
        | some (index, nibA, bibA) =>
          match (← inputByte cinfo nibA bibA) with
          | none => return { s with done := true, ret := .ok false }
          | some (val, nibB, bibB) =>
            let len' := Int64.ofInt (s.length.toInt - 2)
            let dcCur ← Ptr.load cinfo
            tracems2 dcCur.err 1 JTRC_DAC index val
            if index < 0 || index ≥ 2 * NUM_ARITH_TBLS then
              let _ ← errexit1 dcCur.err JERR_DAC_INDEX index
              return { s with done := true, ret := .errExit JERR_DAC_INDEX }
            if index ≥ NUM_ARITH_TBLS then
              let idx := (index - NUM_ARITH_TBLS).toInt.toNat
              Ptr.store cinfo { dcCur with arithAcK := dcCur.arithAcK.set! idx (UInt8.ofNat val.toInt.toNat) }
            else
              let idx := index.toInt.toNat
              let lVal := UInt8.ofNat (val.toInt.toNat &&& 0x0F)
              let uVal := UInt8.ofNat (val.toInt.toNat >>> 4)
              let dcNew := {
                dcCur with
                arithDcL := dcCur.arithDcL.set! idx lVal
                arithDcU := dcCur.arithDcU.set! idx uVal
              }
              Ptr.store cinfo dcNew
              if lVal > uVal then
                let _ ← errexit1 dcNew.err JERR_DAC_VALUE val
                return { s with done := true, ret := .errExit JERR_DAC_VALUE }
            return { done := false, ret := .ok true, length := len', nib := nibB, bib := bibB })
      { done := false, ret := .ok true, length := Int64.ofInt (lenRaw.toInt - 2), nib := nib1, bib := bib1 }
    if st.done then
      return st.ret
    if st.length != 0 then
      let dcErr ← Ptr.load cinfo
      let _ ← errexit dcErr.err JERR_BAD_LENGTH
      return .errExit JERR_BAD_LENGTH
    inputSync cinfo st.nib st.bib
    return .ok true

structure DhtLoopState where
  done : Bool
  ret : JpegRes Bool
  length : Int64
  nib : BPtr
  bib : UInt64

/-- `LOCAL(boolean) get_dht(j_decompress_ptr cinfo)` (`jdmarker.c:436-507`). -/
def get_dht (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  match (← input2Bytes cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (lenRaw, nib1, bib1) =>
    let st ← cwhile
      (fun (s : DhtLoopState) => pure (!s.done && s.length > 16, s))
      (fun (s : DhtLoopState) => do
        match (← inputByte cinfo s.nib s.bib) with
        | none => return { s with done := true, ret := .ok false }
        | some (index, nibA, bibA) =>
          let dcCur ← Ptr.load cinfo
          tracems1 dcCur.err 1 JTRC_DHT index
          let mut bits : Array UInt8 := Array.replicate 17 0
          let mut count : Int32 := 0
          let mut curNib := nibA
          let mut curBib := bibA
          let mut susp := false
          for i in List.range 16 do
            if !susp then
              match (← inputByte cinfo curNib curBib) with
              | none => susp := true
              | some (b, n', bi') =>
                let u := UInt8.ofNat b.toInt.toNat
                bits := bits.set! (i + 1) u
                count := count + Int32.ofNat u.toNat
                curNib := n'
                curBib := bi'
          if susp then
            return { s with done := true, ret := .ok false }
          let len' := Int64.ofInt (s.length.toInt - 17)
          tracems8 dcCur.err 2 JTRC_HUFFBITS
            (Int32.ofNat bits[1]!.toNat) (Int32.ofNat bits[2]!.toNat)
            (Int32.ofNat bits[3]!.toNat) (Int32.ofNat bits[4]!.toNat)
            (Int32.ofNat bits[5]!.toNat) (Int32.ofNat bits[6]!.toNat)
            (Int32.ofNat bits[7]!.toNat) (Int32.ofNat bits[8]!.toNat)
          tracems8 dcCur.err 2 JTRC_HUFFBITS
            (Int32.ofNat bits[9]!.toNat) (Int32.ofNat bits[10]!.toNat)
            (Int32.ofNat bits[11]!.toNat) (Int32.ofNat bits[12]!.toNat)
            (Int32.ofNat bits[13]!.toNat) (Int32.ofNat bits[14]!.toNat)
            (Int32.ofNat bits[15]!.toNat) (Int32.ofNat bits[16]!.toNat)
          if count > 256 || Int64.ofInt count.toInt > len' then
            let _ ← errexit dcCur.err JERR_BAD_HUFF_TABLE
            return { s with done := true, ret := .errExit JERR_BAD_HUFF_TABLE }
          let mut huffval : Array UInt8 := Array.replicate 256 0
          for i in List.range count.toInt.toNat do
            if !susp then
              match (← inputByte cinfo curNib curBib) with
              | none => susp := true
              | some (v, n', bi') =>
                huffval := huffval.set! i (UInt8.ofNat v.toInt.toNat)
                curNib := n'
                curBib := bi'
          if susp then
            return { s with done := true, ret := .ok false }
          let len'' := Int64.ofInt (len'.toInt - count.toInt)
          let dcTbl ← Ptr.load cinfo
          let isAc := (index &&& 0x10) != 0
          let tblIdx := if isAc then index - 0x10 else index
          if tblIdx < 0 || tblIdx ≥ NUM_HUFF_TBLS then
            let _ ← errexit1 dcTbl.err JERR_DHT_INDEX tblIdx
            return { s with done := true, ret := .errExit JERR_DHT_INDEX }
          let idxNat := tblIdx.toInt.toNat
          let existingPtr := if isAc then dcTbl.acHuffTblPtrs[idxNat]! else dcTbl.dcHuffTblPtrs[idxNat]!
          let tblPtr ←
            if existingPtr == .null then
              match (← jpeg_alloc_huff_table cinfo) with
              | .errExit code => return { s with done := true, ret := .errExit code }
              | .ok p =>
                let dcU ← Ptr.load cinfo
                let dcU' :=
                  if isAc then { dcU with acHuffTblPtrs := dcU.acHuffTblPtrs.set! idxNat p }
                  else { dcU with dcHuffTblPtrs := dcU.dcHuffTblPtrs.set! idxNat p }
                Ptr.store cinfo dcU'
                pure p
            else
              pure existingPtr
          let curTbl ← Ptr.load tblPtr
          Ptr.store tblPtr { curTbl with bits := bits, huffval := huffval }
          return { done := false, ret := .ok true, length := len'', nib := curNib, bib := curBib })
      { done := false, ret := .ok true, length := Int64.ofInt (lenRaw.toInt - 2), nib := nib1, bib := bib1 }
    if st.done then
      return st.ret
    if st.length != 0 then
      let dcErr ← Ptr.load cinfo
      let _ ← errexit dcErr.err JERR_BAD_LENGTH
      return .errExit JERR_BAD_LENGTH
    inputSync cinfo st.nib st.bib
    return .ok true

structure DqtLoopState where
  done : Bool
  ret : JpegRes Bool
  length : Int64
  nib : BPtr
  bib : UInt64

/-- `LOCAL(boolean) get_dqt(j_decompress_ptr cinfo)` (`jdmarker.c:510-565`). -/
def get_dqt (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  match (← input2Bytes cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (lenRaw, nib1, bib1) =>
    let st ← cwhile
      (fun (s : DqtLoopState) => pure (!s.done && s.length > 0, s))
      (fun (s : DqtLoopState) => do
        match (← inputByte cinfo s.nib s.bib) with
        | none => return { s with done := true, ret := .ok false }
        | some (nRaw, nibA, bibA) =>
          let prec := nRaw >>> 4
          let n := nRaw &&& 0x0F
          let dcCur ← Ptr.load cinfo
          tracems2 dcCur.err 1 JTRC_DQT n prec
          if n ≥ NUM_QUANT_TBLS then
            let _ ← errexit1 dcCur.err JERR_DQT_INDEX n
            return { s with done := true, ret := .errExit JERR_DQT_INDEX }
          let nNat := n.toInt.toNat
          let qPtr ←
            if dcCur.quantTblPtrs[nNat]! == .null then
              match (← jpeg_alloc_quant_table cinfo) with
              | .errExit code => return { s with done := true, ret := .errExit code }
              | .ok p =>
                let dcU ← Ptr.load cinfo
                Ptr.store cinfo { dcU with quantTblPtrs := dcU.quantTblPtrs.set! nNat p }
                pure p
            else
              pure dcCur.quantTblPtrs[nNat]!
          let mut qTbl ← Ptr.load qPtr
          let mut qvals := qTbl.quantval
          let mut curNib := nibA
          let mut curBib := bibA
          let mut susp := false
          for i in List.range DCTSIZE2.toInt.toNat do
            if !susp then
              let res ←
                if prec != 0 then input2Bytes cinfo curNib curBib
                else inputByte cinfo curNib curBib
              match res with
              | none => susp := true
              | some (tmp, n', bi') =>
                let z := jpeg_natural_order[i]!.toInt.toNat
                qvals := qvals.set! z (UInt16.ofNat tmp.toInt.toNat)
                curNib := n'
                curBib := bi'
          if susp then
            return { s with done := true, ret := .ok false }
          Ptr.store qPtr { qTbl with quantval := qvals }
          let dcErr ← Ptr.load cinfo
          let err ← Ptr.load dcErr.err
          if err.traceLevel ≥ 2 then
            for row in List.range 8 do
              let i := row * 8
              tracems8 dcErr.err 2 JTRC_QUANTVALS
                (Int32.ofNat qvals[i]!.toNat) (Int32.ofNat qvals[i + 1]!.toNat)
                (Int32.ofNat qvals[i + 2]!.toNat) (Int32.ofNat qvals[i + 3]!.toNat)
                (Int32.ofNat qvals[i + 4]!.toNat) (Int32.ofNat qvals[i + 5]!.toNat)
                (Int32.ofNat qvals[i + 6]!.toNat) (Int32.ofNat qvals[i + 7]!.toNat)
          let step := if prec != 0 then DCTSIZE2.toInt * 2 + 1 else DCTSIZE2.toInt + 1
          let len' := Int64.ofInt (s.length.toInt - step)
          return { done := false, ret := .ok true, length := len', nib := curNib, bib := curBib })
      { done := false, ret := .ok true, length := Int64.ofInt (lenRaw.toInt - 2), nib := nib1, bib := bib1 }
    if st.done then
      return st.ret
    if st.length != 0 then
      let dcErr ← Ptr.load cinfo
      let _ ← errexit dcErr.err JERR_BAD_LENGTH
      return .errExit JERR_BAD_LENGTH
    inputSync cinfo st.nib st.bib
    return .ok true

/-- `LOCAL(boolean) get_dri(j_decompress_ptr cinfo)` (`jdmarker.c:568-589`). -/
def get_dri (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  match (← input2Bytes cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (length, nib1, bib1) =>
    if length != 4 then
      let _ ← errexit dc0.err JERR_BAD_LENGTH
      return .errExit JERR_BAD_LENGTH
    match (← input2Bytes cinfo nib1 bib1) with
    | none => return .ok false
    | some (tmp, nib2, bib2) =>
      tracems1 dc0.err 1 JTRC_DRI tmp
      let dc1 ← Ptr.load cinfo
      Ptr.store cinfo { dc1 with restartInterval := UInt32.ofNat tmp.toInt.toNat }
      inputSync cinfo nib2 bib2
      return .ok true

/-- `LOCAL(void) examine_app0(j_decompress_ptr cinfo, JOCTET *data, unsigned int datalen, JLONG remaining)`
(`jdmarker.c:604-674`). -/
def examine_app0 (cinfo : DecompPtr) (data : Array UInt8) (datalen : UInt32) (remaining : Int64) : M Unit := do
  let dc ← Ptr.load cinfo
  let totallen : Int64 := Int64.ofInt (Int.ofNat datalen.toNat + remaining.toInt)
  if datalen ≥ APP0_DATA_LEN &&
      data[0]! == 0x4A && data[1]! == 0x46 && data[2]! == 0x49 && data[3]! == 0x46 && data[4]! == 0 then
    let xDens := UInt16.ofNat ((data[8]!.toNat <<< 8) + data[9]!.toNat)
    let yDens := UInt16.ofNat ((data[10]!.toNat <<< 8) + data[11]!.toNat)
    let dc' := {
      dc with
      sawJFIFMarker := TRUE
      jfifMajorVersion := data[5]!
      jfifMinorVersion := data[6]!
      densityUnit := data[7]!
      xDensity := xDens
      yDensity := yDens
    }
    Ptr.store cinfo dc'
    if dc'.jfifMajorVersion != 1 then
      warnms2 dc'.err JWRN_JFIF_MAJOR (Int32.ofNat dc'.jfifMajorVersion.toNat) (Int32.ofNat dc'.jfifMinorVersion.toNat)
    tracems5 dc'.err 1 JTRC_JFIF
      (Int32.ofNat dc'.jfifMajorVersion.toNat) (Int32.ofNat dc'.jfifMinorVersion.toNat)
      (Int32.ofNat dc'.xDensity.toNat) (Int32.ofNat dc'.yDensity.toNat) (Int32.ofNat dc'.densityUnit.toNat)
    if (data[12]! ||| data[13]!) != 0 then
      tracems2 dc'.err 1 JTRC_JFIF_THUMBNAIL (Int32.ofNat data[12]!.toNat) (Int32.ofNat data[13]!.toNat)
    let remThumb : Int64 := Int64.ofInt (totallen.toInt - Int.ofNat APP0_DATA_LEN.toNat)
    if remThumb.toInt != Int.ofNat data[12]!.toNat * Int.ofNat data[13]!.toNat * 3 then
      tracems1 dc'.err 1 JTRC_JFIF_BADTHUMBNAILSIZE (Int32.ofInt remThumb.toInt)
  else if datalen ≥ 6 &&
      data[0]! == 0x4A && data[1]! == 0x46 && data[2]! == 0x58 && data[3]! == 0x58 && data[4]! == 0 then
    let tag := data[5]!
    let totI := Int32.ofInt totallen.toInt
    if tag == 0x10 then tracems1 dc.err 1 JTRC_THUMB_JPEG totI
    else if tag == 0x11 then tracems1 dc.err 1 JTRC_THUMB_PALETTE totI
    else if tag == 0x13 then tracems1 dc.err 1 JTRC_THUMB_RGB totI
    else tracems2 dc.err 1 JTRC_JFIF_EXTENSION (Int32.ofNat tag.toNat) totI
  else
    tracems1 dc.err 1 JTRC_APP0 (Int32.ofInt totallen.toInt)

/-- `LOCAL(void) examine_app14(j_decompress_ptr cinfo, JOCTET *data, unsigned int datalen, JLONG remaining)`
(`jdmarker.c:677-705`). -/
def examine_app14 (cinfo : DecompPtr) (data : Array UInt8) (datalen : UInt32) (remaining : Int64) : M Unit := do
  let dc ← Ptr.load cinfo
  if datalen ≥ APP14_DATA_LEN &&
      data[0]! == 0x41 && data[1]! == 0x64 && data[2]! == 0x6F && data[3]! == 0x62 && data[4]! == 0x65 then
    let ver := Int32.ofNat ((data[5]!.toNat <<< 8) + data[6]!.toNat)
    let fl0 := Int32.ofNat ((data[7]!.toNat <<< 8) + data[8]!.toNat)
    let fl1 := Int32.ofNat ((data[9]!.toNat <<< 8) + data[10]!.toNat)
    let xform := data[11]!
    tracems4 dc.err 1 JTRC_ADOBE ver fl0 fl1 (Int32.ofNat xform.toNat)
    Ptr.store cinfo { dc with sawAdobeMarker := TRUE, adobeTransform := xform }
  else
    tracems1 dc.err 1 JTRC_APP14 (Int32.ofInt (Int.ofNat datalen.toNat + remaining.toInt))

/-- `METHODDEF(boolean) get_interesting_appn(j_decompress_ptr cinfo)` (`jdmarker.c:708-751`). -/
def get_interesting_appn (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  match (← input2Bytes cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (lenRaw, nib1, bib1) =>
    let mut length : Int64 := Int64.ofInt (lenRaw.toInt - 2)
    let numtoread : Nat :=
      if length.toInt ≥ Int.ofNat APPN_DATA_LEN.toNat then APPN_DATA_LEN.toNat
      else if length.toInt > 0 then length.toInt.toNat
      else 0
    let mut b : Array UInt8 := Array.replicate APPN_DATA_LEN.toNat 0
    let mut curNib := nib1
    let mut curBib := bib1
    let mut susp := false
    for i in List.range numtoread do
      if !susp then
        match (← inputByte cinfo curNib curBib) with
        | none => susp := true
        | some (byteVal, n', bi') =>
          b := b.set! i (UInt8.ofNat byteVal.toInt.toNat)
          curNib := n'
          curBib := bi'
    if susp then
      return .ok false
    length := Int64.ofInt (length.toInt - Int.ofNat numtoread)
    let dc1 ← Ptr.load cinfo
    if dc1.unreadMarker == M_APP0 then
      examine_app0 cinfo b (UInt32.ofNat numtoread) length
    else if dc1.unreadMarker == M_APP14 then
      examine_app14 cinfo b (UInt32.ofNat numtoread) length
    else
      let _ ← errexit1 dc1.err JERR_UNKNOWN_MARKER dc1.unreadMarker
      return .errExit JERR_UNKNOWN_MARKER
    inputSync cinfo curNib curBib
    if length > 0 then
      skipInputDataDispatch cinfo length
    return .ok true

structure SaveMarkerCopyState where
  br : UInt32
  nb : BPtr
  bb : UInt64
  dp : BPtr

structure SaveMarkerState where
  done : Bool
  susp : Bool
  bytesRead : UInt32
  nib : BPtr
  bib : UInt64
  dp : BPtr

/-- `METHODDEF(boolean) save_marker(j_decompress_ptr cinfo)` (`jdmarker.c:756-855`). -/
def save_marker (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let mrk0 ← Ptr.load dc0.marker
  let src0 ← Ptr.load dc0.src
  let mut curMarker := mrk0.curMarker
  let mut bytesRead : UInt32 := 0
  let mut dataLength : UInt32 := 0
  let mut dataPtr : BPtr := .null
  let mut curNib := src0.nextInputByte
  let mut curBib := src0.bytesInBuffer
  if curMarker == .null then
    match (← input2Bytes cinfo curNib curBib) with
    | none => return .ok false
    | some (lenRaw, nib1, bib1) =>
      curNib := nib1
      curBib := bib1
      let length : Int64 := Int64.ofInt (lenRaw.toInt - 2)
      if length ≥ 0 then
        let mut limit : UInt32 :=
          if dc0.unreadMarker == M_COM then mrk0.lengthLimitCOM
          else
            let idx := (dc0.unreadMarker - M_APP0).toInt.toNat
            if idx < 16 then mrk0.lengthLimitAPPn[idx]! else 0
        let lenU := UInt32.ofNat length.toInt.toNat
        if lenU < limit then
          limit := lenU
        match (← alloc_large_saved_marker cinfo JPOOL_IMAGE limit.toNat) with
        | .errExit code => return .errExit code
        | .ok (smP, dP) =>
          curMarker := smP
          dataPtr := dP
          Ptr.store smP {
            next := .null
            marker := UInt8.ofNat dc0.unreadMarker.toInt.toNat
            originalLength := lenU
            dataLength := limit
            data := dP
          }
          let dc1 ← Ptr.load cinfo
          let mrk1 ← Ptr.load dc1.marker
          Ptr.store dc1.marker { mrk1 with curMarker := smP, bytesRead := 0 }
          bytesRead := 0
          dataLength := limit
  else
    let sm ← Ptr.load curMarker
    bytesRead := mrk0.bytesRead
    dataLength := sm.dataLength
    dataPtr ← Ptr.add sm.data (Int.ofNat bytesRead.toNat)
  let st ← cwhile
    (fun (s : SaveMarkerState) => pure (!s.done && s.bytesRead < dataLength, s))
    (fun (s : SaveMarkerState) => do
      inputSync cinfo s.nib s.bib
      let dcS ← Ptr.load cinfo
      let mrkS ← Ptr.load dcS.marker
      Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
      match (← makeByteAvail cinfo s.nib s.bib) with
      | none => return { s with done := true, susp := true }
      | some (n1, bi1) =>
        let cs ← cwhile
          (fun (c : SaveMarkerCopyState) => pure (c.br < dataLength && c.bb > 0, c))
          (fun (c : SaveMarkerCopyState) => do
            let b ← Ptr.load c.nb
            Ptr.store c.dp b
            let dp' ← Ptr.add c.dp 1
            let nb' ← Ptr.add c.nb 1
            return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
          { br := s.bytesRead, nb := n1, bb := bi1, dp := s.dp }
        return { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp })
    { done := false, susp := false, bytesRead := bytesRead, nib := curNib, bib := curBib, dp := dataPtr }
  if st.susp then
    return .ok false
  let mut remLength : Int64 := 0
  let mut dataArr : Array UInt8 := #[]
  if curMarker != .null then
    let sm ← Ptr.load curMarker
    let dcCur ← Ptr.load cinfo
    let mst ← Ptr.load dcCur.master
    if dcCur.markerList == .null || mst.markerListEnd == .null then
      Ptr.store cinfo { dcCur with markerList := curMarker }
      Ptr.store dcCur.master { mst with markerListEnd := curMarker }
    else
      let tail ← Ptr.load mst.markerListEnd
      Ptr.store mst.markerListEnd { tail with next := curMarker }
      Ptr.store dcCur.master { mst with markerListEnd := curMarker }
    remLength := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat dataLength.toNat)
    for k in List.range dataLength.toNat do
      let bp ← Ptr.add sm.data (Int.ofNat k)
      let v ← Ptr.load bp
      dataArr := dataArr.push v
  let dcA ← Ptr.load cinfo
  let mrkA ← Ptr.load dcA.marker
  Ptr.store dcA.marker { mrkA with curMarker := .null }
  if dcA.unreadMarker == M_APP0 then
    examine_app0 cinfo dataArr dataLength remLength
  else if dcA.unreadMarker == M_APP14 then
    examine_app14 cinfo dataArr dataLength remLength
  else
    tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
      (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt))
  inputSync cinfo st.nib st.bib
  if remLength > 0 then
    skipInputDataDispatch cinfo remLength
  return .ok true

/-- `METHODDEF(boolean) skip_variable(j_decompress_ptr cinfo)` (`jdmarker.c:860-877`). -/
def skip_variable (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  match (← input2Bytes cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (lenRaw, nib1, bib1) =>
    let length : Int64 := Int64.ofInt (lenRaw.toInt - 2)
    tracems2 dc0.err 1 JTRC_MISC_MARKER dc0.unreadMarker (Int32.ofInt length.toInt)
    inputSync cinfo nib1 bib1
    if length > 0 then
      skipInputDataDispatch cinfo length
    return .ok true

/-- `LOCAL(boolean) first_marker(j_decompress_ptr cinfo)` (`jdmarker.c:936-957`). -/
def first_marker (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  let src0 ← Ptr.load dc0.src
  match (← inputByte cinfo src0.nextInputByte src0.bytesInBuffer) with
  | none => return .ok false
  | some (c, nib1, bib1) =>
    match (← inputByte cinfo nib1 bib1) with
    | none => return .ok false
    | some (c2, nib2, bib2) =>
      if c != 0xFF || c2 != M_SOI then
        let _ ← errexit2 dc0.err JERR_NO_SOI c c2
        return .errExit JERR_NO_SOI
      let dc1 ← Ptr.load cinfo
      Ptr.store cinfo { dc1 with unreadMarker := c2 }
      inputSync cinfo nib2 bib2
      return .ok true

def callMarkerParser (cinfo : DecompPtr) (fn : FnPtr) : M (JpegRes Bool) := do
  if fn == .fn "skip_variable" then skip_variable cinfo
  else if fn == .fn "save_marker" then save_marker cinfo
  else if fn == .fn "get_interesting_appn" then get_interesting_appn cinfo
  else ub "unsupported marker parser"

structure ReadMarkersState where
  done : Bool
  ret : JpegRes Int32

/-- `METHODDEF(int) read_markers(j_decompress_ptr cinfo)` (`jdmarker.c:967-1121`). -/
def read_markers (cinfo : DecompPtr) : M (JpegRes Int32) := do
  let st ← cwhile
    (fun (s : ReadMarkersState) => pure (!s.done, s))
    (fun (_ : ReadMarkersState) => do
      let dc0 ← Ptr.load cinfo
      if dc0.unreadMarker == 0 then
        let mrk0 ← Ptr.load dc0.marker
        if mrk0.sawSOI == 0 then
          match (← first_marker cinfo) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else
          let nm ← next_marker cinfo
          if nm == 0 then
            return { done := true, ret := .ok JPEG_SUSPENDED }
      let dc ← Ptr.load cinfo
      let um := dc.unreadMarker
      if um == M_SOI then
        match (← get_soi cinfo) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_SOF0 || um == M_SOF1 then
        match (← get_sof cinfo FALSE FALSE FALSE) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_SOF2 then
        match (← get_sof cinfo TRUE FALSE FALSE) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_SOF3 then
        match (← get_sof cinfo FALSE TRUE FALSE) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_SOF9 then
        match (← get_sof cinfo FALSE FALSE TRUE) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_SOF10 then
        match (← get_sof cinfo TRUE FALSE TRUE) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_SOF11 then
        match (← get_sof cinfo FALSE TRUE TRUE) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_SOF5 || um == M_SOF6 || um == M_SOF7 || um == M_JPG ||
          um == M_SOF13 || um == M_SOF14 || um == M_SOF15 then
        let _ ← errexit1 dc.err JERR_SOF_UNSUPPORTED um
        return { done := true, ret := .errExit JERR_SOF_UNSUPPORTED }
      else if um == M_SOS then
        match (← get_sos cinfo) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true =>
          let dcSos ← Ptr.load cinfo
          Ptr.store cinfo { dcSos with unreadMarker := 0 }
          return { done := true, ret := .ok JPEG_REACHED_SOS }
      else if um == M_EOI then
        tracems dc.err 1 JTRC_EOI
        Ptr.store cinfo { dc with unreadMarker := 0 }
        return { done := true, ret := .ok JPEG_REACHED_EOI }
      else if um == M_DAC then
        match (← get_dac cinfo) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_DHT then
        match (← get_dht cinfo) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_DQT then
        match (← get_dqt cinfo) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_DRI then
        match (← get_dri cinfo) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um ≥ M_APP0 && um ≤ M_APP15 then
        let mrk ← Ptr.load dc.marker
        let idx := (um - M_APP0).toInt.toNat
        match (← callMarkerParser cinfo (mrk.processAPPn[idx]!)) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if um == M_COM then
        let mrk ← Ptr.load dc.marker
        match (← callMarkerParser cinfo mrk.processCOM) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else if (um ≥ M_RST0 && um ≤ M_RST7) || um == M_TEM then
        tracems1 dc.err 1 JTRC_PARMLESS_MARKER um
      else if um == M_DNL then
        match (← skip_variable cinfo) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else
        let _ ← errexit1 dc.err JERR_UNKNOWN_MARKER um
        return { done := true, ret := .errExit JERR_UNKNOWN_MARKER }
      let dcEnd ← Ptr.load cinfo
      Ptr.store cinfo { dcEnd with unreadMarker := 0 }
      return { done := false, ret := .ok JPEG_SUSPENDED })
    { done := false, ret := .ok JPEG_SUSPENDED }
  return st.ret

/-- `METHODDEF(boolean) read_restart_marker(j_decompress_ptr cinfo)` (`jdmarker.c:1136-1163`). -/
def read_restart_marker (cinfo : DecompPtr) : M (JpegRes Bool) := do
  let dc0 ← Ptr.load cinfo
  if dc0.unreadMarker == 0 then
    let nm ← next_marker cinfo
    if nm == 0 then
      return .ok false
  let dc1 ← Ptr.load cinfo
  let mrk1 ← Ptr.load dc1.marker
  if dc1.unreadMarker == M_RST0 + mrk1.nextRestartNum then
    tracems1 dc1.err 3 JTRC_RST mrk1.nextRestartNum
    Ptr.store cinfo { dc1 with unreadMarker := 0 }
  else
    let res ← jpeg_resync_to_restart cinfo mrk1.nextRestartNum
    if res == 0 then
      return .ok false
  let dc2 ← Ptr.load cinfo
  let mrk2 ← Ptr.load dc2.marker
  Ptr.store dc2.marker { mrk2 with nextRestartNum := (mrk2.nextRestartNum + 1) &&& 7 }
  return .ok true

end Mozjpeg.Jdmarker
