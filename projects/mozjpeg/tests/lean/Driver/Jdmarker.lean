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
