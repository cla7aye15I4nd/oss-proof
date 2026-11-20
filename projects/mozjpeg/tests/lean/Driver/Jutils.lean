import DiffTest.Common
import MozjpegF.Mozjpeg.«jutils.c»

open DiffTest C Mozjpeg.Jutils

def runLine (tok : List String) : Except String String :=
  match tok with
  | ["jdiv_round_up", aS, bS] => do
    let a ← parseI64 aS
    let b ← parseI64 bS
    match C.run (jdiv_round_up a b) C.Heap.empty with
    | .ok (r, _) => pure (toString r.toInt)
    | .error f => pure (showFault f)
  | ["jround_up", aS, bS] => do
    let a ← parseI64 aS
    let b ← parseI64 bS
    match C.run (jround_up a b) C.Heap.empty with
    | .ok (r, _) => pure (toString r.toInt)
    | .error f => pure (showFault f)
  | ["jzero_far", lenS] => do
    let len ← parseNat lenS
    let blk := Array.replicate (if len > 0 then len else 1) (0xa5 : UInt8)
    let h : C.Heap := { C.Heap.empty with bytes := C.upd C.Tbl.empty 0 (some blk), nextBlk := 1, nalloc := 1 }
    match C.run (jzero_far (.ref (.heap 0) 0) (UInt64.ofNat len)) h with
    | .ok ((), h') =>
      match h'.bytes 0 with
      | some out => pure s!"{showBytes (out.extract 0 len)} {len}"
      | none => pure "MISSING"
    | .error f => pure (showFault f)
  | ["natural_order", idxS] => do
    let idx ← parseNat idxS
    match jpeg_natural_order[idx]? with
    | some v => pure (toString v.toInt)
    | none => pure "OOB"
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
