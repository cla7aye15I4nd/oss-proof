import DiffTest.Common
import MozjpegF.Mozjpeg.«jdapimin.c»
import MozjpegF.Mozjpeg.«jdatasrc.c»
import MozjpegF.Mozjpeg.«jdmarker.c»

open DiffTest C Mozjpeg.Jdapimin Mozjpeg.Jdatasrc Mozjpeg.Jdmarker Mozjpeg.JpeglibH

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

def setupSrc (h1 : C.Heap) (p : C.DecompPtr) (mode : Int32) (bytes : Array UInt8) : Except String C.Heap :=
  let bufArr : Array UInt8 := if bytes.isEmpty then #[0] else bytes
  if mode == 1 then
    let bid := h1.nextBlk
    let sid := h1.nextBlk + 1
    let src0 : C.JpegSourceMgr := {
      initSource := .fn "init_mem_source"
      fillInputBuffer := .fn "suspend_input"
      skipInputData := .fn "skip_input_data"
      resyncToRestart := .fn "jpeg_resync_to_restart"
      termSource := .fn "term_source"
      nextInputByte := .ref (.heap bid) 0
      bytesInBuffer := bytes.size.toUInt64
    }
    let dcs1 := (h1.decomps 0).getD #[{}]
    let dc1 := { dcs1[0]! with src := .ref (.src sid) 0 }
    pure {
      h1 with
      bytes := C.upd h1.bytes bid (some bufArr)
      srcs := C.upd h1.srcs sid (some #[src0])
      decomps := C.upd h1.decomps 0 (some (dcs1.set! 0 dc1))
      nextBlk := sid + 1
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

def countSavedMarkers (h : C.Heap) (p : C.SavedMarkerPtr) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    match p with
    | .null => 0
    | .ref (.savedMarker bid) off =>
      match (h.savedMarkers bid).bind (·[off]?) with
      | some sm => 1 + countSavedMarkers h sm.next fuel
      | none => 0

def stdErr0 : C.JpegErrorMgr := {
  errorExit := .fn "error_exit"
  emitMessage := .fn "emit_message"
  outputMessage := .fn "output_message"
  formatMessage := .fn "format_message"
  resetErrorMgr := .fn "reset_error_mgr"
  lastJpegMessage := 131
}

def mkFreshInit : C.Heap :=
  let dc0 : C.JpegDecompressStruct := {
    err := .ref (.err 0) 0
    mem := .ref (.mem 0) 0
  }
  {
    C.Heap.empty with
    errMgrs := C.upd C.Tbl.empty 0 (some #[stdErr0])
    decomps := C.upd C.Tbl.empty 0 (some #[dc0])
    nextBlk := 1
  }

def runLine (tok : List String) : Except String String :=
  match tok with
  | ["create", verS, szS] => do
    let ver ← parseI32 verS
    let sz ← parseNat szS
    let h := mkFreshInit
    match C.run (jpeg_CreateDecompress (.ref (.decomp 0) 0) ver (UInt64.ofNat sz)) h with
    | .ok (.ok (), h') =>
      let dc' := (h'.decomps 0).getD #[{}] |>.getD 0 {}
      let h'' ←
        match C.run (jpeg_destroy_decompress (.ref (.decomp 0) 0)) h' with
        | .ok ((), x) => pure x
        | .error f => throw (showFault f)
      let dc'' := (h''.decomps 0).getD #[{}] |>.getD 0 {}
      let boolInt (b : Bool) : Int := if b then 1 else 0
      pure s!"ok state={dc'.globalState.toInt} dp={dc'.dataPrecision.toInt} isd={dc'.isDecompressor.toInt} mn={boolInt (dc'.mem == .null)} mrn={boolInt (dc'.marker == .null)} icn={boolInt (dc'.inputctl == .null)} man={boolInt (dc'.master == .null)} sn={boolInt (dc'.src == .null)} after_mn={boolInt (dc''.mem == .null)}"
    | .ok (.errExit _, h') =>
      let e := (h'.errMgrs 0).getD #[{}] |>.getD 0 {}
      let h'' ←
        match C.run (jpeg_destroy_decompress (.ref (.decomp 0) 0)) h' with
        | .ok ((), x) => pure x
        | .error f => throw (showFault f)
      let dc'' := (h''.decomps 0).getD #[{}] |>.getD 0 {}
      let afterMn := if dc''.mem == .null then 1 else 0
      pure s!"err code={e.msgCode.toInt} p0={e.msgParmI[0]!.toInt} p1={e.msgParmI[1]!.toInt} after_mn={afterMn}"
    | .error f => pure (showFault f)
  | ["abort_destroy", stS] => do
    let st ← parseI32 stS
    let h := mkFreshInit
    match C.run (jpeg_CreateDecompress (.ref (.decomp 0) 0) JPEG_LIB_VERSION sizeof_jpeg_decompress_struct) h with
    | .ok (.ok (), h1) =>
      let dcs1 := (h1.decomps 0).getD #[{}]
      let h2 := { h1 with decomps := C.upd h1.decomps 0 (some (dcs1.set! 0 { dcs1[0]! with globalState := st })) }
      let p : C.DecompPtr := .ref (.decomp 0) 0
      match C.run (do
        jpeg_abort_decompress p
        let dc2 ← Ptr.load p
        jpeg_destroy_decompress p
        return dc2.globalState) h2 with
      | .ok (afterSt, h3) =>
        let dc3 := (h3.decomps 0).getD #[{}] |>.getD 0 {}
        let afterMn := if dc3.mem == .null then 1 else 0
        pure s!"abort state={afterSt.toInt} after_mn={afterMn}"
      | .error f => pure (showFault f)
    | _ => pure "CREATE_FAIL"
  | ["input_complete", stS, eoiS] => do
    let st ← parseI32 stS
    let eoi ← parseI32 eoiS
    let h := mkFreshInit
    match C.run (jpeg_CreateDecompress (.ref (.decomp 0) 0) JPEG_LIB_VERSION sizeof_jpeg_decompress_struct) h with
    | .ok (.ok (), h1) =>
      let dcs1 := (h1.decomps 0).getD #[{}]
      let dc1 := { dcs1[0]! with globalState := st }
      let h2 :=
        match dc1.inputctl with
        | .ref (.inputctl bic) 0 =>
          let ics := (h1.inputctls bic).getD #[{}]
          {
            h1 with
            decomps := C.upd h1.decomps 0 (some (dcs1.set! 0 dc1))
            inputctls := C.upd h1.inputctls bic (some (ics.set! 0 { ics[0]! with eoiReached := eoi }))
          }
        | _ => h1
      match C.run (jpeg_input_complete (.ref (.decomp 0) 0)) h2 with
      | .ok (.ok r, _) => pure s!"ic {r.toInt}"
      | .ok (.errExit _, h') =>
        let e := (h'.errMgrs 0).getD #[{}] |>.getD 0 {}
        pure s!"err {e.msgCode.toInt} {e.msgParmI[0]!.toInt}"
      | .error f => pure (showFault f)
    | _ => pure "CREATE_FAIL"
  | ["has_multiple_scans", stS, hmsS] => do
    let st ← parseI32 stS
    let hms ← parseI32 hmsS
    let h := mkFreshInit
    match C.run (jpeg_CreateDecompress (.ref (.decomp 0) 0) JPEG_LIB_VERSION sizeof_jpeg_decompress_struct) h with
    | .ok (.ok (), h1) =>
      let dcs1 := (h1.decomps 0).getD #[{}]
      let dc1 := { dcs1[0]! with globalState := st }
      let h2 :=
        match dc1.inputctl with
        | .ref (.inputctl bic) 0 =>
          let ics := (h1.inputctls bic).getD #[{}]
          {
            h1 with
            decomps := C.upd h1.decomps 0 (some (dcs1.set! 0 dc1))
            inputctls := C.upd h1.inputctls bic (some (ics.set! 0 { ics[0]! with hasMultipleScans := hms }))
          }
        | _ => h1
      match C.run (jpeg_has_multiple_scans (.ref (.decomp 0) 0)) h2 with
      | .ok (.ok r, _) => pure s!"hms {r.toInt}"
      | .ok (.errExit _, h') =>
        let e := (h'.errMgrs 0).getD #[{}] |>.getD 0 {}
        pure s!"err {e.msgCode.toInt} {e.msgParmI[0]!.toInt}"
      | .error f => pure (showFault f)
    | _ => pure "CREATE_FAIL"
  | ["read_header", reqS, modeS, maskS, hex] => do
    let req ← parseI32 reqS
    let mode ← parseI32 modeS
    let mask ← parseU32 maskS
    let bytes ← parseHex hex
    let p : C.DecompPtr := .ref (.decomp 0) 0
    match C.run (jpeg_CreateDecompress p JPEG_LIB_VERSION sizeof_jpeg_decompress_struct) mkFreshInit with
    | .ok (.ok (), h1) =>
      let h2 ← setupSrc h1 p mode bytes
      let act : C.M (JpegRes Int32) := do
        if (mask &&& 1) != 0 then
          match (← jpeg_save_markers p 0xE0 65535) with
          | .errExit c => return .errExit c
          | .ok () => pure ()
        if (mask &&& 2) != 0 then
          match (← jpeg_save_markers p 0xFE 8) with
          | .errExit c => return .errExit c
          | .ok () => pure ()
        jpeg_read_header p req
      match C.run act h2 with
      | .ok (.ok ret, h3) =>
        let dc3 := (h3.decomps 0).getD #[{}] |>.getD 0 {}
        let ic3 := match dc3.inputctl with
          | .ref (.inputctl iid) 0 => (h3.inputctls iid).getD #[{}] |>.getD 0 {}
          | _ => {}
        let src3 := match dc3.src with
          | .ref (.src sid) 0 => (h3.srcs sid).getD #[{}] |>.getD 0 {}
          | _ => {}
        let err3 := (h3.errMgrs 0).getD #[{}] |>.getD 0 {}
        let ns := countSavedMarkers h3 dc3.markerList 256
        let q0 : Int :=
          match dc3.quantTblPtrs[0]! with
          | .ref (.quant bid) qoff =>
            match (h3.quants bid).bind (·[qoff]?) with
            | some qt => qt.quantval[0]!.toNat
            | none => -1
          | .null => -1
        let h0v : Int :=
          match dc3.dcHuffTblPtrs[0]! with
          | .ref (.huff bid) hoff =>
            match (h3.huffs bid).bind (·[hoff]?) with
            | some ht => ht.bits[2]!.toNat
            | none => -1
          | .null => -1
        let qtLatched : Int :=
          match dc3.compInfo with
          | .ref (.comp bid) coff =>
            match (h3.comps bid).bind (·[coff]?) with
            | some ci => if ci.quantTable != (.null : C.QuantPtr) then 1 else 0
            | none => 0
          | .null => 0
        pure s!"rh ret={ret.toInt} st={dc3.globalState.toInt} w={dc3.imageWidth.toNat} h={dc3.imageHeight.toNat} nc={dc3.numComponents.toInt} outcs={dc3.outColorSpace.toInt} dct={dc3.dctMethod.toInt} prog={dc3.progressiveMode.toInt} hms={ic3.hasMultipleScans.toInt} eoi={ic3.eoiReached.toInt} bib={src3.bytesInBuffer.toNat} ns={ns} q0={q0} qt={qtLatched} h0={h0v} warn={err3.numWarnings.toInt}"
      | .ok (.errExit _, h3) =>
        let e := (h3.errMgrs 0).getD #[{}] |>.getD 0 {}
        pure s!"err {e.msgCode.toInt} {e.msgParmI[0]!.toInt}"
      | .error f => pure (showFault f)
    | _ => pure "CREATE_FAIL"
  | ["consume_seq", initStS, modeS, stepsS, hex] => do
    let initSt ← parseI32 initStS
    let mode ← parseI32 modeS
    let steps ← parseNat stepsS
    let bytes ← parseHex hex
    let p : C.DecompPtr := .ref (.decomp 0) 0
    match C.run (jpeg_CreateDecompress p JPEG_LIB_VERSION sizeof_jpeg_decompress_struct) mkFreshInit with
    | .ok (.ok (), h1) =>
      let h2 ← setupSrc h1 p mode bytes
      let h3 :=
        if initSt == 200 then h2
        else
          let dcs := (h2.decomps 0).getD #[{}]
          { h2 with decomps := C.upd h2.decomps 0 (some (dcs.set! 0 { dcs[0]! with globalState := initSt })) }
      let act : C.M (JpegRes (Array (Int32 × Int32 × Int32))) := do
        let mut out : Array (Int32 × Int32 × Int32) := #[]
        for _ in List.range steps do
          match (← jpeg_consume_input p) with
          | .errExit c => return .errExit c
          | .ok r =>
            let dc' ← Ptr.load p
            let ic' ← Ptr.load dc'.inputctl
            out := out.push (r, dc'.globalState, ic'.eoiReached)
        return .ok out
      match C.run act h3 with
      | .ok (.ok outs, h4) =>
        let dc4 := (h4.decomps 0).getD #[{}] |>.getD 0 {}
        let ic4 := match dc4.inputctl with
          | .ref (.inputctl iid) 0 => (h4.inputctls iid).getD #[{}] |>.getD 0 {}
          | _ => {}
        let err4 := (h4.errMgrs 0).getD #[{}] |>.getD 0 {}
        let parts := outs.toList.map fun (r, st, eoi) => s!"{r.toInt}:{st.toInt}:{eoi.toInt}"
        let joined := String.intercalate " " parts
        pure s!"cs {joined} hms={ic4.hasMultipleScans.toInt} warn={err4.numWarnings.toInt}"
      | .ok (.errExit _, h4) =>
        let e := (h4.errMgrs 0).getD #[{}] |>.getD 0 {}
        pure s!"err {e.msgCode.toInt} {e.msgParmI[0]!.toInt}"
      | .error f => pure (showFault f)
    | _ => pure "CREATE_FAIL"
  | ["finish", initStS, eoiS, modeS, hex] => do
    let initSt ← parseI32 initStS
    let eoi ← parseI32 eoiS
    let mode ← parseI32 modeS
    let bytes ← parseHex hex
    let p : C.DecompPtr := .ref (.decomp 0) 0
    match C.run (jpeg_CreateDecompress p JPEG_LIB_VERSION sizeof_jpeg_decompress_struct) mkFreshInit with
    | .ok (.ok (), h1) =>
      let h2 ← setupSrc h1 p mode bytes
      let dcs := (h2.decomps 0).getD #[{}]
      let dc := { dcs[0]! with globalState := initSt }
      let h3 :=
        match dc.inputctl with
        | .ref (.inputctl iid) 0 =>
          let ics := (h2.inputctls iid).getD #[{}]
          {
            h2 with
            decomps := C.upd h2.decomps 0 (some (dcs.set! 0 dc))
            inputctls := C.upd h2.inputctls iid (some (ics.set! 0 { ics[0]! with eoiReached := eoi }))
          }
        | _ => h2
      match C.run (jpeg_finish_decompress p) h3 with
      | .ok (.ok ret, h4) =>
        let dc4 := (h4.decomps 0).getD #[{}] |>.getD 0 {}
        let ic4 := match dc4.inputctl with
          | .ref (.inputctl iid) 0 => (h4.inputctls iid).getD #[{}] |>.getD 0 {}
          | _ => {}
        let src4 := match dc4.src with
          | .ref (.src sid) 0 => (h4.srcs sid).getD #[{}] |>.getD 0 {}
          | _ => {}
        let err4 := (h4.errMgrs 0).getD #[{}] |>.getD 0 {}
        pure s!"fin ret={ret.toInt} st={dc4.globalState.toInt} bib={src4.bytesInBuffer.toNat} eoi={ic4.eoiReached.toInt} warn={err4.numWarnings.toInt}"
      | .ok (.errExit _, h4) =>
        let e := (h4.errMgrs 0).getD #[{}] |>.getD 0 {}
        pure s!"err {e.msgCode.toInt} {e.msgParmI[0]!.toInt}"
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
