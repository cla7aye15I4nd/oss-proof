import MozjpegF.Mozjpeg.«jmemmgr.c»
import MozjpegF.Mozjpeg.«jerror.c»
import MozjpegF.Mozjpeg.«jutils.c»
import MozjpegF.Mozjpeg.«jdmarker.c»

/-!
# `jdinput.c` — input controller translation (`MozjpegF`)

Source: `mozjpeg/jdinput.c` (`initial_setup`, `per_scan_setup`, `latch_quant_tables`,
`start_input_pass`, `finish_input_pass`, `consume_markers`, `reset_input_controller`,
`jinit_input_controller`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jdinput
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jmemmgr
open Mozjpeg.Jerror Mozjpeg.Jutils Mozjpeg.Jdmarker

/-- `LOCAL(void) initial_setup(j_decompress_ptr cinfo)` (`jdinput.c:46-152`). -/
def initial_setup (cinfo : DecompPtr) : M (JpegRes Unit) := do
  let dc0 ← Ptr.load cinfo
  let mst0 ← Ptr.load dc0.master
  let data_unit : Int32 := if mst0.lossless != 0 then 1 else DCTSIZE
  if Int64.ofNat dc0.imageHeight.toNat > JPEG_MAX_DIMENSION ||
      Int64.ofNat dc0.imageWidth.toNat > JPEG_MAX_DIMENSION then
    let _ ← errexit1 dc0.err JERR_IMAGE_TOO_BIG (Int32.ofInt JPEG_MAX_DIMENSION.toInt)
    return .errExit JERR_IMAGE_TOO_BIG
  if dc0.dataPrecision != 8 && dc0.dataPrecision != 12 && dc0.dataPrecision != 16 then
    let _ ← errexit1 dc0.err JERR_BAD_PRECISION dc0.dataPrecision
    return .errExit JERR_BAD_PRECISION
  if dc0.numComponents > MAX_COMPONENTS then
    let _ ← errexit2 dc0.err JERR_COMPONENT_COUNT dc0.numComponents MAX_COMPONENTS
    return .errExit JERR_COMPONENT_COUNT
  Ptr.store cinfo { dc0 with maxHSampFactor := 1, maxVSampFactor := 1 }
  let nComps := dc0.numComponents.toInt.toNat
  for ci in List.range nComps do
    let dcCur ← Ptr.load cinfo
    let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
    let comp ← Ptr.load cp
    if comp.hSampFactor ≤ 0 || comp.hSampFactor > MAX_SAMP_FACTOR ||
        comp.vSampFactor ≤ 0 || comp.vSampFactor > MAX_SAMP_FACTOR then
      let _ ← errexit dcCur.err JERR_BAD_SAMPLING
      return .errExit JERR_BAD_SAMPLING
    Ptr.store cinfo {
      dcCur with
      maxHSampFactor := max dcCur.maxHSampFactor comp.hSampFactor
      maxVSampFactor := max dcCur.maxVSampFactor comp.vSampFactor
    }
  let dc1 ← Ptr.load cinfo
  Ptr.store cinfo {
    dc1 with
    blockSize := data_unit
    naturalOrder := .ref .st_natural_order 0
    limSe := DCTSIZE2 - 1
    minDctHScaledSize := data_unit
    minDctVScaledSize := data_unit
  }
  for ci in List.range nComps do
    let dcC ← Ptr.load cinfo
    let cp ← Ptr.add dcC.compInfo (Int.ofNat ci)
    let comp ← Ptr.load cp
    let wib ← jdiv_round_up
      (Int64.ofInt (Int.ofNat dcC.imageWidth.toNat * comp.hSampFactor.toInt))
      (Int64.ofInt (dcC.maxHSampFactor.toInt * data_unit.toInt))
    let hib ← jdiv_round_up
      (Int64.ofInt (Int.ofNat dcC.imageHeight.toNat * comp.vSampFactor.toInt))
      (Int64.ofInt (dcC.maxVSampFactor.toInt * data_unit.toInt))
    let mstC ← Ptr.load dcC.master
    Ptr.store dcC.master {
      mstC with
      firstMcuCol := mstC.firstMcuCol.set! ci 0
      lastMcuCol := mstC.lastMcuCol.set! ci (UInt32.ofNat wib.toInt.toNat - 1)
    }
    let dw ← jdiv_round_up
      (Int64.ofInt (Int.ofNat dcC.imageWidth.toNat * comp.hSampFactor.toInt))
      (Int64.ofInt dcC.maxHSampFactor.toInt)
    let dh ← jdiv_round_up
      (Int64.ofInt (Int.ofNat dcC.imageHeight.toNat * comp.vSampFactor.toInt))
      (Int64.ofInt dcC.maxVSampFactor.toInt)
    Ptr.store cp {
      comp with
      dctHScaledSize := data_unit
      dctVScaledSize := data_unit
      widthInBlocks := UInt32.ofNat wib.toInt.toNat
      heightInBlocks := UInt32.ofNat hib.toInt.toNat
      downsampledWidth := UInt32.ofNat dw.toInt.toNat
      downsampledHeight := UInt32.ofNat dh.toInt.toNat
      componentNeeded := TRUE
      quantTable := .null
    }
  let dc2 ← Ptr.load cinfo
  let totRows ← jdiv_round_up
    (Int64.ofNat dc2.imageHeight.toNat)
    (Int64.ofInt (dc2.maxVSampFactor.toInt * data_unit.toInt))
  Ptr.store cinfo { dc2 with totalIMcuRows := UInt32.ofNat totRows.toInt.toNat }
  let ic ← Ptr.load dc2.inputctl
  let hms := if dc2.compsInScan < dc2.numComponents || dc2.progressiveMode != 0 then TRUE else FALSE
  Ptr.store dc2.inputctl { ic with hasMultipleScans := hms }
  return .ok ()

/-- `LOCAL(void) per_scan_setup(j_decompress_ptr cinfo)` (`jdinput.c:155-232`). -/
def per_scan_setup (cinfo : DecompPtr) : M (JpegRes Unit) := do
  let dc0 ← Ptr.load cinfo
  let mst0 ← Ptr.load dc0.master
  let data_unit : Int32 := if mst0.lossless != 0 then 1 else DCTSIZE
  if dc0.compsInScan == 1 then
    let cp0 := dc0.curCompInfo[0]!
    let comp ← Ptr.load cp0
    if comp.vSampFactor ≤ 0 then
      ub "division by zero in per_scan_setup"
    let tmp0 := Int32.ofInt (Int.ofNat comp.heightInBlocks.toNat % comp.vSampFactor.toInt)
    let lrh := if tmp0 == 0 then comp.vSampFactor else tmp0
    Ptr.store cp0 {
      comp with
      mcuWidth := 1
      mcuHeight := 1
      mcuBlocks := 1
      mcuSampleWidth := comp.dctHScaledSize
      lastColWidth := 1
      lastRowHeight := lrh
    }
    let dc1 ← Ptr.load cinfo
    Ptr.store cinfo {
      dc1 with
      mcusPerRow := comp.widthInBlocks
      mcuRowsInScan := comp.heightInBlocks
      blocksInMcu := 1
      mcuMembership := dc1.mcuMembership.set! 0 0
    }
    return .ok ()
  else
    if dc0.compsInScan ≤ 0 || dc0.compsInScan > MAX_COMPS_IN_SCAN then
      let _ ← errexit2 dc0.err JERR_COMPONENT_COUNT dc0.compsInScan MAX_COMPS_IN_SCAN
      return .errExit JERR_COMPONENT_COUNT
    let mpr ← jdiv_round_up
      (Int64.ofNat dc0.imageWidth.toNat)
      (Int64.ofInt (dc0.maxHSampFactor.toInt * data_unit.toInt))
    let mris ← jdiv_round_up
      (Int64.ofNat dc0.imageHeight.toNat)
      (Int64.ofInt (dc0.maxVSampFactor.toInt * data_unit.toInt))
    Ptr.store cinfo {
      dc0 with
      mcusPerRow := UInt32.ofNat mpr.toInt.toNat
      mcuRowsInScan := UInt32.ofNat mris.toInt.toNat
      blocksInMcu := 0
    }
    let cis := dc0.compsInScan.toInt.toNat
    for ci in List.range cis do
      let dcC ← Ptr.load cinfo
      let cp := dcC.curCompInfo[ci]!
      let comp ← Ptr.load cp
      if comp.hSampFactor ≤ 0 || comp.vSampFactor ≤ 0 then
        ub "division by zero in per_scan_setup"
      let mw := comp.hSampFactor
      let mh := comp.vSampFactor
      let mb ← i32Mul mw mh
      let msw ← i32Mul mw comp.dctHScaledSize
      let tmpW := Int32.ofInt (Int.ofNat comp.widthInBlocks.toNat % mw.toInt)
      let lcw := if tmpW == 0 then mw else tmpW
      let tmpH := Int32.ofInt (Int.ofNat comp.heightInBlocks.toNat % mh.toInt)
      let lrh := if tmpH == 0 then mh else tmpH
      Ptr.store cp {
        comp with
        mcuWidth := mw
        mcuHeight := mh
        mcuBlocks := mb
        mcuSampleWidth := msw
        lastColWidth := lcw
        lastRowHeight := lrh
      }
      let dcB ← Ptr.load cinfo
      let bim ← i32Add dcB.blocksInMcu mb
      if bim > D_MAX_BLOCKS_IN_MCU then
        let _ ← errexit dcB.err JERR_BAD_MCU_SIZE
        return .errExit JERR_BAD_MCU_SIZE
      let mut memArr := dcB.mcuMembership
      let mut curBim := dcB.blocksInMcu
      for _ in List.range mb.toInt.toNat do
        memArr := memArr.set! curBim.toInt.toNat (Int32.ofNat ci)
        curBim := curBim + 1
      Ptr.store cinfo { dcB with blocksInMcu := curBim, mcuMembership := memArr }
    return .ok ()

/-- `LOCAL(void) latch_quant_tables(j_decompress_ptr cinfo)` (`jdinput.c:256-280`). -/
def latch_quant_tables (cinfo : DecompPtr) : M (JpegRes Unit) := do
  let dc0 ← Ptr.load cinfo
  let cis := dc0.compsInScan.toInt.toNat
  for ci in List.range cis do
    let dcCur ← Ptr.load cinfo
    let cp := dcCur.curCompInfo[ci]!
    let comp ← Ptr.load cp
    if comp.quantTable == .null then
      let qtblno := comp.quantTblNo
      if qtblno < 0 || qtblno ≥ NUM_QUANT_TBLS || dcCur.quantTblPtrs[qtblno.toInt.toNat]! == .null then
        let _ ← errexit1 dcCur.err JERR_NO_QUANT_TABLE qtblno
        return .errExit JERR_NO_QUANT_TABLE
      match (← alloc_small_quant cinfo JPOOL_IMAGE sizeof_JQUANT_TBL) with
      | .errExit code => return .errExit code
      | .ok qPtr =>
        let srcQ ← Ptr.load (dcCur.quantTblPtrs[qtblno.toInt.toNat]!)
        Ptr.store qPtr srcQ
        let comp' ← Ptr.load cp
        Ptr.store cp { comp' with quantTable := qPtr }
  return .ok ()

/-- `METHODDEF(void) start_input_pass(j_decompress_ptr cinfo)` (`jdinput.c:290-299`). -/
def start_input_pass (cinfo : DecompPtr) : M (JpegRes Unit) := do
  match (← per_scan_setup cinfo) with
  | .errExit code => return .errExit code
  | .ok () =>
    let dc0 ← Ptr.load cinfo
    let mst0 ← Ptr.load dc0.master
    if mst0.lossless == 0 then
      match (← latch_quant_tables cinfo) with
      | .errExit code => return .errExit code
      | .ok () => pure ()
    let dc1 ← Ptr.load cinfo
    if dc1.entropyStartPass != .fn "noop" then
      ub "unsupported entropy start_pass"
    if dc1.coefStartInputPass != .fn "noop" then
      ub "unsupported coef start_input_pass"
    let ic ← Ptr.load dc1.inputctl
    Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
    return .ok ()

/-- `METHODDEF(void) finish_input_pass(j_decompress_ptr cinfo)` (`jdinput.c:308-312`). -/
def finish_input_pass (cinfo : DecompPtr) : M Unit := do
  let dc ← Ptr.load cinfo
  let ic ← Ptr.load dc.inputctl
  Ptr.store dc.inputctl { ic with consumeInput := .fn "consume_markers" }

/-- `METHODDEF(int) consume_markers(j_decompress_ptr cinfo)` (`jdinput.c:325-369`). -/
def consume_markers (cinfo : DecompPtr) : M (JpegRes Int32) := do
  let dc0 ← Ptr.load cinfo
  let ic0 ← Ptr.load dc0.inputctl
  if ic0.eoiReached != 0 then
    return .ok JPEG_REACHED_EOI
  let mrk0 ← Ptr.load dc0.marker
  let valRes ←
    if mrk0.readMarkers == .fn "read_markers" then read_markers cinfo
    else ub "unsupported read_markers"
  match valRes with
  | .errExit code => return .errExit code
  | .ok val =>
    if val == JPEG_REACHED_SOS then
      let dcS ← Ptr.load cinfo
      let icS ← Ptr.load dcS.inputctl
      if icS.inheaders != 0 then
        match (← initial_setup cinfo) with
        | .errExit code => return .errExit code
        | .ok () =>
          let dcS2 ← Ptr.load cinfo
          let icS2 ← Ptr.load dcS2.inputctl
          Ptr.store dcS2.inputctl { icS2 with inheaders := FALSE }
      else
        if icS.hasMultipleScans == 0 then
          let _ ← errexit dcS.err JERR_EOI_EXPECTED
          return .errExit JERR_EOI_EXPECTED
        match (← start_input_pass cinfo) with
        | .errExit code => return .errExit code
        | .ok () => pure ()
    else if val == JPEG_REACHED_EOI then
      let dcE ← Ptr.load cinfo
      let icE ← Ptr.load dcE.inputctl
      Ptr.store dcE.inputctl { icE with eoiReached := TRUE }
      if icE.inheaders != 0 then
        let mrkE ← Ptr.load dcE.marker
        if mrkE.sawSOF != 0 then
          let _ ← errexit dcE.err JERR_SOF_NO_SOS
          return .errExit JERR_SOF_NO_SOS
      else
        if dcE.outputScanNumber > dcE.inputScanNumber then
          Ptr.store cinfo { dcE with outputScanNumber := dcE.inputScanNumber }
    return .ok val

/-- `METHODDEF(void) reset_input_controller(j_decompress_ptr cinfo)` (`jdinput.c:376-390`). -/
def reset_input_controller (cinfo : DecompPtr) : M Unit := do
  let dc0 ← Ptr.load cinfo
  let ic0 ← Ptr.load dc0.inputctl
  Ptr.store dc0.inputctl {
    ic0 with
    consumeInput := .fn "consume_markers"
    hasMultipleScans := FALSE
    eoiReached := FALSE
    inheaders := TRUE
  }
  let err0 ← Ptr.load dc0.err
  if err0.resetErrorMgr == .fn "reset_error_mgr" then
    reset_error_mgr cinfo
  else
    ub "unsupported reset_error_mgr"
  let dc1 ← Ptr.load cinfo
  let mrk1 ← Ptr.load dc1.marker
  if mrk1.resetMarkerReader == .fn "reset_marker_reader" then
    reset_marker_reader cinfo
  else
    ub "unsupported reset_marker_reader"
  let dc2 ← Ptr.load cinfo
  Ptr.store cinfo { dc2 with coefBits := .null }

/-- `GLOBAL(void) jinit_input_controller(j_decompress_ptr cinfo)` (`jdinput.c:398-419`). -/
def jinit_input_controller (cinfo : DecompPtr) : M (JpegRes Unit) := do
  match (← alloc_small_inputctl cinfo JPOOL_PERMANENT 48) with
  | .errExit code => return .errExit code
  | .ok icPtr =>
    let dc ← Ptr.load cinfo
    Ptr.store cinfo { dc with inputctl := icPtr }
    Ptr.store icPtr {
      consumeInput := .fn "consume_markers"
      resetInputController := .fn "reset_input_controller"
      startInputPass := .fn "start_input_pass"
      finishInputPass := .fn "finish_input_pass"
      hasMultipleScans := FALSE
      eoiReached := FALSE
      inheaders := TRUE
    }
    return .ok ()

end Mozjpeg.Jdinput
