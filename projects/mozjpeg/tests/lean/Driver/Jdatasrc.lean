import DiffTest.Common
import MozjpegF.Mozjpeg.«jdatasrc.c»

open DiffTest C Mozjpeg.Jdatasrc Mozjpeg.JpeglibH

def sampleBuf : Array UInt8 :=
  Array.ofFn (fun (i : Fin 64) => UInt8.ofNat ((i.1 * 17 + 3) % 256))

def mkDecompForSrc (preset : Nat) : C.Heap :=
  let mem0 : C.JpegMemMgr := { maxAllocChunk := 1000000000 }
  let srcsArr : Array C.JpegSourceMgr :=
    if preset == 1 then
      #[{ initSource := .fn "init_mem_source", bytesInBuffer := 7, nextInputByte := .ref (.heap 0) 0 }]
    else if preset == 2 then
      #[{ initSource := .fn "foreign_init", bytesInBuffer := 0, nextInputByte := .null }]
    else
      #[]
  let srcPtr : C.SrcPtr := if preset == 0 then .null else .ref (.src 0) 0
  let dc0 : C.JpegDecompressStruct := {
    err := .ref (.err 0) 0
    mem := .ref (.mem 0) 0
    src := srcPtr
  }
  {
    C.Heap.empty with
    bytes := C.upd C.Tbl.empty 0 (some sampleBuf)
    errMgrs := C.upd C.Tbl.empty 0 (some #[{}])
    mems := C.upd C.Tbl.empty 0 (some #[mem0])
    srcs := if preset == 0 then C.Tbl.empty else C.upd C.Tbl.empty 0 (some srcsArr)
    decomps := C.upd C.Tbl.empty 0 (some #[dc0])
    nextBlk := 1
  }

def runLine (tok : List String) : Except String String :=
  match tok with
  | ["mem_src", nnS, szS, presetS] => do
    let nn ← parseI32 nnS
    let sz ← parseNat szS
    let preset ← parseNat presetS
    let h := mkDecompForSrc preset
    let inbuf : C.BPtr := if nn == 0 then .null else .ref (.heap 0) 0
    match C.run (do
      let r ← jpeg_mem_src (.ref (.decomp 0) 0) inbuf (UInt64.ofNat sz)
      match r with
      | JpegRes.ok () =>
        init_mem_source (.ref (.decomp 0) 0)
        return JpegRes.ok ()
      | JpegRes.errExit c => return JpegRes.errExit c) h with
    | .ok (.ok (), h') =>
      let dc' := (h'.decomps 0).getD #[{}] |>.getD 0 {}
      let src' ←
        match dc'.src with
        | .ref rs 0 => pure ((C.Space.get h' rs).getD #[{}] |>.getD 0 {})
        | _ => throw "null src after ok"
      let h'' ←
        match C.run (term_source (.ref (.decomp 0) 0)) h' with
        | .ok (_, x) => pure x
        | .error f => throw (showFault f)
      let _ := h''
      let samebuf := if src'.nextInputByte == .ref (.heap 0) 0 then 1 else 0
      pure s!"ok bib={src'.bytesInBuffer.toNat} samebuf={samebuf}"
    | .ok (.errExit _, h') =>
      let e := (h'.errMgrs 0).getD #[{}] |>.getD 0 {}
      pure s!"err {e.msgCode.toInt}"
    | .error f => pure (showFault f)
  | ["skip", szS, n1S, n2S] => do
    let sz ← parseNat szS
    let n1 ← parseI64 n1S
    let n2 ← parseI64 n2S
    let h := mkDecompForSrc 0
    match C.run (do
      let r ← jpeg_mem_src (.ref (.decomp 0) 0) (.ref (.heap 0) 0) (UInt64.ofNat sz)
      match r with
      | JpegRes.ok () =>
        skip_input_data (.ref (.decomp 0) 0) n1
        skip_input_data (.ref (.decomp 0) 0) n2
        return JpegRes.ok ()
      | JpegRes.errExit c => return JpegRes.errExit c) h with
    | .ok (.ok (), h') =>
      let dc' := (h'.decomps 0).getD #[{}] |>.getD 0 {}
      let src' ←
        match dc'.src with
        | .ref rs 0 => pure ((C.Space.get h' rs).getD #[{}] |>.getD 0 {})
        | _ => throw "null src after ok"
      let err' := (h'.errMgrs 0).getD #[{}] |>.getD 0 {}
      let head : Int ←
        if src'.bytesInBuffer == 0 then pure (-1)
        else
          match src'.nextInputByte with
          | .ref r off =>
            match h'.getBytes r with
            | some arr =>
              if off < arr.size then pure (Int.ofNat arr[off]!.toNat)
              else pure (-2)
            | none => pure (-3)
          | .null => pure (-4)
      pure s!"skip bib={src'.bytesInBuffer.toNat} warn={err'.numWarnings.toInt} code={err'.msgCode.toInt} head={head}"
    | .ok (.errExit _, h') =>
      let e := (h'.errMgrs 0).getD #[{}] |>.getD 0 {}
      pure s!"err {e.msgCode.toInt}"
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
