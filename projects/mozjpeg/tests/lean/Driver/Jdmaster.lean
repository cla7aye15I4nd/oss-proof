import DiffTest.Common
import MozjpegF.Mozjpeg.«jdmaster.c»

open DiffTest C Mozjpeg.Jdmaster

def fmtComps (comps : Array C.JpegCompInfo) (nc : Nat) : String :=
  String.join ((List.range nc).map fun i =>
    let c := comps[i]!
    s!" [{c.dctHScaledSize.toInt},{c.dctVScaledSize.toInt},{c.downsampledWidth.toNat},{c.downsampledHeight.toNat}]")

def runLine (tok : List String) : Except String String :=
  match tok with
  | [cmd, gsS, llS, wS, hS, snS, sdS, ncS, jcsS, ocsS, fancyS, ccirS, quantS, mhS, mvS] => do
    if cmd != "core" && cmd != "calc" then throw s!"unknown command {cmd}"
    let gstate ← parseI32 gsS
    let lossless ← parseI32 llS
    let w ← parseU32 wS
    let h ← parseU32 hS
    let snum ← parseU32 snS
    let sden ← parseU32 sdS
    let nc ← parseI32 ncS
    let jcs ← parseI32 jcsS
    let ocs ← parseI32 ocsS
    let fancy ← parseI32 fancyS
    let ccir ← parseI32 ccirS
    let quant ← parseI32 quantS
    let maxh ← parseI32 mhS
    let maxv ← parseI32 mvS
    let ncNat := nc.toInt.toNat
    let compsArr : Array C.JpegCompInfo :=
      if ncNat == 0 then #[{}]
      else
        #[{ hSampFactor := maxh, vSampFactor := maxv }] ++
          Array.replicate (ncNat - 1) { hSampFactor := 1, vSampFactor := 1 }
    let mst0 : C.JpegDecompMaster := { lossless := lossless }
    let dc0 : C.JpegDecompressStruct := {
      err := .ref (.err 0) 0
      globalState := gstate
      imageWidth := w
      imageHeight := h
      scaleNum := snum
      scaleDenom := sden
      numComponents := nc
      jpegColorSpace := jcs
      outColorSpace := ocs
      doFancyUpsampling := fancy
      ccir601Sampling := ccir
      quantizeColors := quant
      maxHSampFactor := maxh
      maxVSampFactor := maxv
      minDctHScaledSize := 0
      minDctVScaledSize := 0
      compInfo := .ref (.comp 0) 0
      master := .ref (.master 0) 0
    }
    let heap0 : C.Heap := {
      C.Heap.empty with
      errMgrs := C.upd C.Tbl.empty 0 (some #[{}])
      masters := C.upd C.Tbl.empty 0 (some #[mst0])
      comps := C.upd C.Tbl.empty 0 (some compsArr)
      decomps := C.upd C.Tbl.empty 0 (some #[dc0])
    }
    let act : C.M (C.JpegRes Unit) :=
      if cmd == "calc" then jpeg_calc_output_dimensions (.ref (.decomp 0) 0)
      else do jpeg_core_output_dimensions (.ref (.decomp 0) 0); return .ok ()
    match C.run act heap0 with
    | .ok (.ok (), h') =>
      match h'.decomps 0, h'.comps 0 with
      | some dcs, some cs =>
        let dc := dcs[0]!
        pure s!"ok {dc.outputWidth.toNat} {dc.outputHeight.toNat} {dc.outColorComponents.toInt} {dc.outputComponents.toInt} {dc.recOutbufHeight.toInt} {dc.minDctHScaledSize.toInt}{fmtComps cs ncNat}"
      | _, _ => pure "MISSING"
    | .ok (.errExit _, h') =>
      match h'.errMgrs 0 with
      | some errs =>
        let e := errs[0]!
        pure s!"err {e.msgCode.toInt} {e.msgParmI[0]!.toInt}"
      | none => pure "MISSING_ERR"
    | .error f => pure (showFault f)
  | _ => throw s!"unknown command or arity: {tok}"

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
