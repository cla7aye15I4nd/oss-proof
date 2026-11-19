import DiffTest.Common
import MozjpegF.Mozjpeg.«jdmarker.c»

open DiffTest C Mozjpeg.Jdmarker

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
