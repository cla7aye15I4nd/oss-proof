import DiffTest.Common
import MozjpegF.Mozjpeg.«jerror.c»

open DiffTest C Mozjpeg.Jerror

def runLine (tok : List String) : Except String String :=
  match tok with
  | ["jpeg_std_error", traceS, warnS, idxS] => do
    let tl ← parseI32 traceS
    let nw ← parseI64 warnS
    let idx ← parseI32 idxS
    let mgr0 : C.JpegErrorMgr := {
      traceLevel := tl
      numWarnings := nw
      msgCode := 77
      lastJpegMessage := 999
    }
    let h : C.Heap := {
      C.Heap.empty with
      errMgrs := C.upd C.Tbl.empty 0 (some #[mgr0])
    }
    match C.run (jpeg_std_error (.ref (.err 0) 0)) h with
    | .ok (retPtr, h') =>
      match h'.errMgrs 0 with
      | some arr =>
        let mgr := arr[0]!
        let msg :=
          if 0 ≤ idx.toInt ∧ idx.toInt ≤ mgr.lastJpegMessage.toInt then
            match retPtr with
            | .ref _ _ => C.strTable[idx.toInt.toNat]?.getD ""
            | .null => ""
          else ""
        pure s!"{mgr.msgCode.toInt} {mgr.numWarnings.toInt} {mgr.traceLevel.toInt} {mgr.lastJpegMessage.toInt} {msg}"
      | none => pure "MISSING"
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
