import DiffTest.Common
import MozjpegF.Mozjpeg.«jdapimin.c»

open DiffTest C Mozjpeg.Jdapimin Mozjpeg.JpeglibH

def mkFreshInit : C.Heap :=
  let dc0 : C.JpegDecompressStruct := {
    err := .ref (.err 0) 0
    mem := .ref (.mem 0) 0
  }
  {
    C.Heap.empty with
    errMgrs := C.upd C.Tbl.empty 0 (some #[{}])
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
