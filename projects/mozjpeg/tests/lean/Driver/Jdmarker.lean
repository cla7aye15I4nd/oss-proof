import DiffTest.Common
import MozjpegF.Mozjpeg.«jdmarker.c»
import MozjpegF.Mozjpeg.«jdapimin.c»
import MozjpegF.Mozjpeg.«jdatasrc.c»

open DiffTest C Mozjpeg.Jdmarker Mozjpeg.Jdapimin Mozjpeg.Jdatasrc Mozjpeg.JpeglibH

def parseHex (hex : String) : Except String (Array UInt8) :=
  if hex == "-" then pure #[]
  else if hex.length % 2 != 0 then throw s!"odd hex length: {hex}"
  else
    let hexDigit (c : Char) : Except String UInt8 :=
      if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat).toUInt8
      else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10).toUInt8
      else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10).toUInt8
      else throw s!"bad hex char {c}"
    let rec parsePairs : List Char → Except String (Array UInt8)
      | [] => pure #[]
      | hi :: lo :: rest => do
        let h ← hexDigit hi
        let l ← hexDigit lo
        let tail ← parsePairs rest
        pure (#[h * 16 + l] ++ tail)
      | _ => throw "odd hex"
    parsePairs hex.toList

def mkFreshInit : C.Heap :=
  let err0 : C.JpegErrorMgr := {
    errorExit := .fn "error_exit"
    emitMessage := .fn "emit_message"
    outputMessage := .fn "output_message"
    formatMessage := .fn "format_message"
    resetErrorMgr := .fn "reset_error_mgr"
    lastJpegMessage := 131
  }
  let dc0 : C.JpegDecompressStruct := {
    err := .ref (.err 0) 0
    mem := .ref (.mem 0) 0
  }
  {
    C.Heap.empty with
    errMgrs := C.upd C.Tbl.empty 0 (some #[err0])
    decomps := C.upd C.Tbl.empty 0 (some #[dc0])
    nextBlk := 1
  }

def countSavedMarkers (h : C.Heap) (p : C.SavedMarkerPtr) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    match p with
    | .null => 0
    | .ref (.savedMarker bid) off =>
      match h.savedMarkers bid with
      | some arr =>
        match arr[off]? with
        | some sm => 1 + countSavedMarkers h sm.next fuel
        | none => 0
      | none => 0

def fmtFirstMarker (h : C.Heap) (p : C.SavedMarkerPtr) : String :=
  match p with
  | .null => "-"
  | .ref (.savedMarker bid) off =>
    match (h.savedMarkers bid).bind (·[off]?) with
    | none => "BADMRK"
    | some sm =>
      let hex :=
        if sm.dataLength == 0 then "-"
        else
          match sm.data with
          | .ref dr doff =>
            match h.getBytes dr with
            | some arr =>
              let slice := (List.range sm.dataLength.toNat).map fun i => arr.getD (doff + i) 0
              showBytes slice.toArray
            | none => "BADDATA"
          | .null => "NULLDATA"
      s!"{showBytes #[sm.marker]}:{sm.originalLength.toNat}:{sm.dataLength.toNat}:{hex}"

def mkMarkerState : C.Heap :=
  let mem0 : C.JpegMemMgr := { maxAllocChunk := 1000000000 }
  let mrk0 : C.JpegMarkerReader := {
    processAPPn := Array.replicate 16 (.fn "skip_variable")
    lengthLimitAPPn := Array.replicate 16 0
  }
  let dc0 : C.JpegDecompressStruct := {
    err := .ref (.err 0) 0
    mem := .ref (.mem 0) 0
    marker := .ref (.marker 0) 0
  }
  {
    C.Heap.empty with
    errMgrs := C.upd C.Tbl.empty 0 (some #[{}])
    mems := C.upd C.Tbl.empty 0 (some #[mem0])
    markers := C.upd C.Tbl.empty 0 (some #[mrk0])
    decomps := C.upd C.Tbl.empty 0 (some #[dc0])
  }

def runLine (tok : List String) : Except String String :=
  match tok with
  | ["jpeg_save_markers", codeS, limS] => do
    let code ← parseI32 codeS
    let lim ← parseU32 limS
    let h := mkMarkerState
    match C.run (jpeg_save_markers (.ref (.decomp 0) 0) code lim) h with
    | .ok (.ok (), h') =>
      match h'.markers 0 with
      | some mrks =>
        let mr := mrks[0]!
        let a := mr.lengthLimitAPPn
        pure s!"ok com={mr.lengthLimitCOM.toNat} app0={a[0]!.toNat} app1={a[1]!.toNat} app2={a[2]!.toNat} app13={a[13]!.toNat} app14={a[14]!.toNat} app15={a[15]!.toNat}"
      | none => pure "MISSING"
    | .ok (.errExit _, h') =>
      match h'.errMgrs 0 with
      | some errs =>
        let e := errs[0]!
        pure s!"err {e.msgCode.toInt} {e.msgParmI[0]!.toInt}"
      | none => pure "MISSING_ERR"
    | .error f => pure (showFault f)
  | ["resync", unreadS, desiredS, modeS, hex] => do
    let unread ← parseI32 unreadS
    let desired ← parseI32 desiredS
    let mode ← parseI32 modeS
    let bytes ←
      if hex == "-" then pure #[]
      else
        if hex.length % 2 != 0 then throw s!"odd hex length: {hex}"
        else
          let chars := hex.toList
          let hexDigit (c : Char) : Except String UInt8 :=
            if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat).toUInt8
            else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10).toUInt8
            else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10).toUInt8
            else throw s!"bad hex char {c}"
          let rec parsePairs : List Char → Except String (Array UInt8)
            | [] => pure #[]
            | hi :: lo :: rest => do
              let h ← hexDigit hi
              let l ← hexDigit lo
              let tail ← parsePairs rest
              pure (#[h * 16 + l] ++ tail)
            | _ => throw "odd hex"
          parsePairs chars
    let bufArr : Array UInt8 := if bytes.isEmpty then #[0] else bytes
    let fillFn : C.FnPtr := if mode == 1 then .fn "suspend_input" else .fn "fill_mem_input_buffer"
    let src0 : C.JpegSourceMgr := {
      initSource := .fn "init_mem_source"
      fillInputBuffer := fillFn
      skipInputData := .fn "skip_input_data"
      resyncToRestart := .fn "jpeg_resync_to_restart"
      termSource := .fn "term_source"
      nextInputByte := .ref (.heap 0) 0
      bytesInBuffer := bytes.size.toUInt64
    }
    let mrk0 : C.JpegMarkerReader := {
      processAPPn := Array.replicate 16 (.fn "skip_variable")
      lengthLimitAPPn := Array.replicate 16 0
    }
    let dc0 : C.JpegDecompressStruct := {
      err := .ref (.err 0) 0
      mem := .ref (.mem 0) 0
      src := .ref (.src 0) 0
      marker := .ref (.marker 0) 0
      unreadMarker := unread
    }
    let h0 : C.Heap := {
      C.Heap.empty with
      bytes := C.upd C.Tbl.empty 0 (some bufArr)
      errMgrs := C.upd C.Tbl.empty 0 (some #[{}])
      mems := C.upd C.Tbl.empty 0 (some #[])
      srcs := C.upd C.Tbl.empty 0 (some #[src0])
      markers := C.upd C.Tbl.empty 0 (some #[mrk0])
      decomps := C.upd C.Tbl.empty 0 (some #[dc0])
    }
    match C.run (jpeg_resync_to_restart (.ref (.decomp 0) 0) desired) h0 with
    | .ok (ret, h') =>
      let dc' := (h'.decomps 0).getD #[{}] |>.getD 0 {}
      let src' := (h'.srcs 0).getD #[{}] |>.getD 0 {}
      let mrk' := (h'.markers 0).getD #[{}] |>.getD 0 {}
      let err' := (h'.errMgrs 0).getD #[{}] |>.getD 0 {}
      let remS ←
        if src'.bytesInBuffer == 0 then pure "-"
        else
          match src'.nextInputByte with
          | .ref r off =>
            match h'.getBytes r with
            | some arr =>
              let slice := (List.range src'.bytesInBuffer.toNat).map fun i => arr.getD (off + i) 0
              pure (showBytes slice.toArray)
            | none => pure "BADPTR"
          | .null => pure "NULLPTR"
      pure s!"resync ret={ret.toInt} unread={dc'.unreadMarker.toInt} bib={src'.bytesInBuffer.toNat} rem={remS} warn={err'.numWarnings.toInt} disc={mrk'.discardedBytes.toNat} code={err'.msgCode.toInt} p0={err'.msgParmI[0]!.toInt} p1={err'.msgParmI[1]!.toInt}"
    | .error f => pure (showFault f)
  | ["read_markers", modeS, maskS, hex] => do
    let mode ← parseI32 modeS
    let mask ← parseU32 maskS
    let bytes ← parseHex hex
    let bufArr : Array UInt8 := if bytes.isEmpty then #[0] else bytes
    let h0 := mkFreshInit
    let p : C.DecompPtr := .ref (.decomp 0) 0
    match C.run (jpeg_CreateDecompress p JPEG_LIB_VERSION sizeof_jpeg_decompress_struct) h0 with
    | .ok (.ok (), h1) =>
      let h2 ←
        if mode == 1 then
          let src0 : C.JpegSourceMgr := {
            initSource := .fn "init_mem_source"
            fillInputBuffer := .fn "suspend_input"
            skipInputData := .fn "skip_input_data"
            resyncToRestart := .fn "jpeg_resync_to_restart"
            termSource := .fn "term_source"
            nextInputByte := .ref (.heap 0) 0
            bytesInBuffer := bytes.size.toUInt64
          }
          let dcs1 := (h1.decomps 0).getD #[{}]
          let dc1 := { dcs1[0]! with src := .ref (.src 0) 0 }
          pure {
            h1 with
            bytes := C.upd h1.bytes 0 (some bufArr)
            srcs := C.upd h1.srcs 0 (some #[src0])
            decomps := C.upd h1.decomps 0 (some (dcs1.set! 0 dc1))
          }
        else if bytes.size > 0 then
          let bid := h1.nextBlk
          let hBuf := { h1 with bytes := C.upd h1.bytes bid (some bufArr), nextBlk := bid + 1 }
          match C.run (jpeg_mem_src p (.ref (.heap bid) 0) bytes.size.toUInt64) hBuf with
          | .ok (.ok (), h') => pure h'
          | _ => throw "MEM_SRC_FAIL"
        else
          let bid := h1.nextBlk
          let hBuf := { h1 with bytes := C.upd h1.bytes bid (some #[0]), nextBlk := bid + 1 }
          match C.run (jpeg_mem_src p (.ref (.heap bid) 0) 1) hBuf with
          | .ok (.ok (), h') =>
            let dcs' := (h'.decomps 0).getD #[{}]
            match dcs'[0]!.src with
            | .ref (.src sid) 0 =>
              let srcs' := (h'.srcs sid).getD #[{}]
              let src' := { srcs'[0]! with bytesInBuffer := 0, nextInputByte := .ref (.heap bid) 0 }
              pure { h' with srcs := C.upd h'.srcs sid (some (srcs'.set! 0 src')) }
            | _ => throw "MEM_SRC_BAD_PTR"
          | _ => throw "MEM_SRC_FAIL"
      let act : C.M (JpegRes Int32) := do
        if (mask &&& 1) != 0 then
          match (← jpeg_save_markers p 0xE0 65535) with
          | .errExit c => return .errExit c
          | .ok () => pure ()
        if (mask &&& 2) != 0 then
          match (← jpeg_save_markers p 0xFE 8) with
          | .errExit c => return .errExit c
          | .ok () => pure ()
        if (mask &&& 4) != 0 then
          match (← jpeg_save_markers p 0xE1 4) with
          | .errExit c => return .errExit c
          | .ok () => pure ()
        if (mask &&& 8) != 0 then
          match (← jpeg_save_markers p 0xEE 65535) with
          | .errExit c => return .errExit c
          | .ok () => pure ()
        read_markers p
      match C.run act h2 with
      | .ok (.ok ret, h3) =>
        let dc3 := (h3.decomps 0).getD #[{}] |>.getD 0 {}
        let mrk3 := match dc3.marker with
          | .ref (.marker mid) 0 => (h3.markers mid).getD #[{}] |>.getD 0 {}
          | _ => {}
        let src3 := match dc3.src with
          | .ref (.src sid) 0 => (h3.srcs sid).getD #[{}] |>.getD 0 {}
          | _ => {}
        let err3 := (h3.errMgrs 0).getD #[{}] |>.getD 0 {}
        let nm := countSavedMarkers h3 dc3.markerList 256
        let m0 := fmtFirstMarker h3 dc3.markerList
        pure s!"rm ok ret={ret.toInt} soi={mrk3.sawSOI.toInt} sof={mrk3.sawSOF.toInt} w={dc3.imageWidth.toNat} h={dc3.imageHeight.toNat} nc={dc3.numComponents.toInt} cs={dc3.jpegColorSpace.toInt} prog={dc3.progressiveMode.toInt} arith={dc3.arithCode.toInt} dri={dc3.restartInterval.toNat} bib={src3.bytesInBuffer.toNat} unread={dc3.unreadMarker.toInt} nm={nm} m0={m0} warn={err3.numWarnings.toInt}"
      | .ok (.errExit _, h3) =>
        let e := (h3.errMgrs 0).getD #[{}] |>.getD 0 {}
        pure s!"err code={e.msgCode.toInt} p0={e.msgParmI[0]!.toInt} p1={e.msgParmI[1]!.toInt}"
      | .error f => pure (showFault f)
    | _ => pure "CREATE_FAIL"
  | _ => throw s!"unknown command: {tok}"

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut bad : UInt32 := 0
  while true do
    let line ← stdin.getLine
    if line.isEmpty then break
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    let tok := (trimmed.splitOn " ").filter (· ≠ "")
    match runLine tok with
    | .ok s => IO.println s
    | .error e =>
      IO.eprintln e
      IO.println "BADINPUT"
      bad := 1
  return bad
