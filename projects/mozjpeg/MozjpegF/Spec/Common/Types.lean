import MozjpegF.Runtime.Libc
import MozjpegF.Mozjpeg.«jmorecfg.h»
import MozjpegF.Mozjpeg.«jerror.h»
import MozjpegF.Mozjpeg.«jpeglib.h»
import MozjpegF.Mozjpeg.«jutils.c»
import MozjpegF.Mozjpeg.«jerror.c»
import MozjpegF.Mozjpeg.«jcomapi.c»
import MozjpegF.Mozjpeg.«jdmaster.c»
import MozjpegF.Mozjpeg.«jdmarker.c»
import MozjpegF.Mozjpeg.«jdapimin.c»

/-!
# Shared specification vocabulary (`MozjpegF`)

Common heap predicates and object-graph invariants shared by `MozjpegF.Spec.Safety` and
`MozjpegF.Spec.Functional`. No `Goal.*` definitions live here.
-/

set_option autoImplicit false

namespace MozjpegF.Spec
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH

/-- `m` faults on `h` with `Fault.ub` (not `outOfFuel` and not `.ok`). -/
def FaultsWithUb {α : Type} (m : C.M α) (h : C.Heap) : Prop :=
  ∃ msg : String, C.run m h = .error (.ub msg)

/-- `p` points to `length` live bytes inside one allocated or static byte object. -/
def LiveBytes (h : C.Heap) (pointer : C.BPtr) (length : Nat) : Prop :=
  ∃ r off data,
    pointer = .ref r off ∧
    C.Space.get h r = some data ∧
    off + length ≤ data.size

/-- `p` points to `length` live writable bytes in one heap block. -/
def WritableBytes (h : C.Heap) (pointer : C.BPtr) (length : Nat) : Prop :=
  ∃ b off data,
    pointer = .ref (.heap b) off ∧
    h.bytes b = some data ∧
    off + length ≤ data.size

/-- `err` points to a live writable single `struct jpeg_error_mgr` object at offset 0. -/
def ValidErrMgr (h : C.Heap) (err : C.ErrPtr) : Prop :=
  ∃ r a, err = .ref r 0 ∧ C.Space.get h r = some a ∧ 0 < a.size

/-- Live component array `compInfo` with at least `n` entries. -/
def LiveCompArray (h : C.Heap) (compInfo : C.CompPtr) (n : Nat) : Prop :=
  ∃ r comps,
    compInfo = .ref r 0 ∧
    C.Space.get h r = some comps ∧
    n ≤ comps.size

/-- Live component array `compInfo` with `n` initialized entries satisfying `initial_setup` bounds. -/
def ValidCompArray (h : C.Heap) (compInfo : C.CompPtr) (n : Nat) : Prop :=
  ∃ r comps,
    compInfo = .ref r 0 ∧
    C.Space.get h r = some comps ∧
    n ≤ comps.size ∧
    ∀ i, i < n →
      1 ≤ (comps[i]!).hSampFactor.toInt ∧ (comps[i]!).hSampFactor.toInt ≤ 4 ∧
      1 ≤ (comps[i]!).vSampFactor.toInt ∧ (comps[i]!).vSampFactor.toInt ≤ 4

/-- Core live object graph for a `jpeg_decompress_struct` and its subobjects (`err`, `mem`, `master`,
`inputctl`, `marker`). -/
def ValidDecompCore (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ∃ rc dcs dc rm mems rmas masters ric ics rmrk mrks,
    cinfo = .ref rc 0 ∧
    C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧
    dc = dcs[0]! ∧
    ValidErrMgr h dc.err ∧
    dc.mem = .ref rm 0 ∧ C.Space.get h rm = some mems ∧ 0 < mems.size ∧
    dc.master = .ref rmas 0 ∧ C.Space.get h rmas = some masters ∧ 0 < masters.size ∧
    dc.inputctl = .ref ric 0 ∧ C.Space.get h ric = some ics ∧ 0 < ics.size ∧
    dc.marker = .ref rmrk 0 ∧ C.Space.get h rmrk = some mrks ∧ 0 < mrks.size ∧
    2 ≤ (mems[0]!).poolAllocs.size ∧
    (∀ bmas, rmas = .master bmas → bmas ∉ (mems[0]!).poolAllocs[1]!.masters)

/-- Fresh-nextBlk heap freshness invariant: slots at or above `h.nextBlk` are unallocated. -/
def FreshNextBlk (h : C.Heap) : Prop :=
  ∀ k, h.nextBlk ≤ k →
    h.bytes k = none ∧ h.i32s k = none ∧ h.mems k = none ∧ h.masters k = none ∧
    h.markers k = none ∧ h.inputctls k = none ∧ h.srcs k = none ∧ h.comps k = none ∧
    h.quants k = none ∧ h.huffs k = none ∧ h.savedMarkers k = none

/-- Initial caller-allocated `cinfo` with live `err` and fresh `nextBlk` prior to `jpeg_CreateDecompress`. -/
def FreshDecompInit (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ∃ rc dcs dc,
    cinfo = .ref rc 0 ∧
    C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧
    dc = dcs[0]! ∧
    ValidErrMgr h dc.err ∧
    FreshNextBlk h

/-- Valid live source manager when `cinfo->src` is non-null or needs allocation in `cinfo->mem`. -/
def ValidDecompMem (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ∃ rc dcs dc rm mems,
    cinfo = .ref rc 0 ∧
    C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧
    dc = dcs[0]! ∧
    ValidErrMgr h dc.err ∧
    dc.mem = .ref rm 0 ∧ C.Space.get h rm = some mems ∧ 0 < mems.size ∧
    2 ≤ (mems[0]!).poolAllocs.size ∧
    (dc.src = .null ∨
      ∃ rs srcs, dc.src = .ref rs 0 ∧ C.Space.get h rs = some srcs ∧ 0 < srcs.size)

/-- Valid decompressor with live source manager ready for `next_marker` / `jpeg_resync_to_restart`. -/
def ValidDecompResyncInput (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ValidDecompCore h cinfo ∧
  ∃ rc dcs dc rs srcs src rerr errs,
    cinfo = .ref rc 0 ∧ C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
    dc.src = .ref rs 0 ∧ C.Space.get h rs = some srcs ∧ 0 < srcs.size ∧ src = srcs[0]! ∧
    dc.err = .ref rerr 0 ∧ C.Space.get h rerr = some errs ∧ 0 < errs.size ∧
    0 ≤ (errs[0]!).numWarnings.toInt ∧ (errs[0]!).numWarnings.toInt + 2 ^ 30 < 2 ^ 63 ∧
    src.bytesInBuffer.toNat < 2 ^ 20 ∧
    (src.bytesInBuffer = 0 ∨ LiveBytes h src.nextInputByte src.bytesInBuffer.toNat) ∧
    (src.fillInputBuffer = .fn "suspend_input" ∨ src.fillInputBuffer = .fn "fill_mem_input_buffer")

/-- Decompressor object satisfies `ValidDecompCore` plus valid `initial_setup` header bounds
(`DSTATE_READY` or general state check, `1 ≤ numComponents ≤ 10`, sampling factors in `1..4`,
`imageWidth/imageHeight ≤ 65500`). -/
def ValidDecompDimsInput (h : C.Heap) (cinfo : C.DecompPtr) (requireReady : Bool) : Prop :=
  ValidDecompCore h cinfo ∧
  ∃ rc dcs dc rmas masters mst,
    cinfo = .ref rc 0 ∧
    C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
    dc.master = .ref rmas 0 ∧ C.Space.get h rmas = some masters ∧ 0 < masters.size ∧
    mst = masters[0]! ∧
    (!requireReady || dc.globalState = DSTATE_READY) ∧
    (0 ≤ dc.numComponents.toInt ∧ dc.numComponents.toInt ≤ 10) ∧
    (dc.imageWidth.toNat ≤ 65500 ∧ dc.imageHeight.toNat ≤ 65500) ∧
    (1 ≤ dc.maxHSampFactor.toInt ∧ dc.maxHSampFactor.toInt ≤ 4) ∧
    (1 ≤ dc.maxVSampFactor.toInt ∧ dc.maxVSampFactor.toInt ≤ 4) ∧
    ValidCompArray h dc.compInfo dc.numComponents.toInt.toNat

/-- Preconditions for `start_input_pass` when continuing a multi-scan JPEG after headers (`inheaders = 0`). -/
def MultiScanReady (h : C.Heap) (dc : C.JpegDecompressStruct) : Prop :=
  dc.entropyStartPass = .fn "noop" ∧
  dc.coefStartInputPass = .fn "noop" ∧
  dc.coefConsumeData = .fn "dummy_consume_data" ∧
  0 ≤ dc.compsInScan.toInt ∧ dc.compsInScan.toInt ≤ 4 ∧
  dc.curCompInfo.size = 4 ∧
  1 ≤ dc.maxHSampFactor.toInt ∧ dc.maxHSampFactor.toInt ≤ 4 ∧
  1 ≤ dc.maxVSampFactor.toInt ∧ dc.maxVSampFactor.toInt ≤ 4 ∧
  dc.imageWidth.toNat ≤ 65500 ∧ dc.imageHeight.toNat ≤ 65500 ∧
  0 ≤ dc.numComponents.toInt ∧ dc.numComponents.toInt ≤ 10 ∧
  (∃ rmrk mrks,
    dc.marker = .ref rmrk 0 ∧ C.Space.get h rmrk = some mrks ∧ 0 < mrks.size ∧
    mrks[0]!.sawSOF ≠ 0) ∧
  (dc.numComponents = 0 ∨
    ∃ rcp cs,
      dc.compInfo = .ref rcp 0 ∧
      C.Space.get h rcp = some cs ∧ dc.numComponents.toInt.toNat ≤ cs.size ∧
      ∀ j < dc.numComponents.toInt.toNat,
        1 ≤ (cs[j]!).hSampFactor.toInt ∧ (cs[j]!).hSampFactor.toInt ≤ 4 ∧
        1 ≤ (cs[j]!).vSampFactor.toInt ∧ (cs[j]!).vSampFactor.toInt ≤ 4 ∧
        0 ≤ (cs[j]!).dctHScaledSize.toInt ∧ (cs[j]!).dctHScaledSize.toInt ≤ DCTSIZE.toInt) ∧
  ∀ i < dc.compsInScan.toInt.toNat,
    ∃ rcp off cs ci,
      dc.curCompInfo[i]! = .ref rcp off ∧
      C.Space.get h rcp = some cs ∧ off < cs.size ∧ ci = cs[off]! ∧
      1 ≤ ci.hSampFactor.toInt ∧ ci.hSampFactor.toInt ≤ 4 ∧
      1 ≤ ci.vSampFactor.toInt ∧ ci.vSampFactor.toInt ≤ 4 ∧
      0 ≤ ci.dctHScaledSize.toInt ∧ ci.dctHScaledSize.toInt ≤ DCTSIZE.toInt

/-- Shared valid decompressor, source, marker reader, input controller, and pool graph for
marker/header/finish operations (`read_markers`, `consume_markers`, `jpeg_consume_input`,
`jpeg_read_header`, `jpeg_finish_decompress`). -/
def ValidDecompIoBase (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ValidDecompCore h cinfo ∧
  FreshNextBlk h ∧
  ∃ rc dcs dc rerr errs rmem mems rmas masters ric ics rmrk mrks rs srcs,
    cinfo = .ref rc 0 ∧ C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
    dc.err = .ref rerr 0 ∧ C.Space.get h rerr = some errs ∧ 0 < errs.size ∧
    (errs[0]!).resetErrorMgr = .fn "reset_error_mgr" ∧
    0 ≤ (errs[0]!).numWarnings.toInt ∧ (errs[0]!).numWarnings.toInt + 2 ^ 25 < 2 ^ 63 ∧
    dc.mem = .ref rmem 0 ∧ C.Space.get h rmem = some mems ∧ 0 < mems.size ∧
    (mems[0]!).allocSmall = .fn "alloc_small" ∧
    (mems[0]!).freePool = .fn "free_pool" ∧
    (mems[0]!).selfDestruct = .fn "self_destruct" ∧
    (mems[0]!).livePools.size = 2 ∧
    (mems[0]!).livePools[0]! = true ∧ (mems[0]!).livePools[1]! = true ∧
    (mems[0]!).poolAllocs.size = 2 ∧
    (mems[0]!).poolAllocs[1]!.masters.isEmpty ∧
    (mems[0]!).poolAllocs[1]!.inputctls.isEmpty ∧
    (mems[0]!).poolAllocs[1]!.markers.isEmpty ∧
    (mems[0]!).poolAllocs[1]!.srcs.isEmpty ∧
    dc.master = .ref rmas 0 ∧ C.Space.get h rmas = some masters ∧ 0 < masters.size ∧
    dc.inputctl = .ref ric 0 ∧ C.Space.get h ric = some ics ∧ 0 < ics.size ∧
    (ics[0]!).resetInputController = .fn "reset_input_controller" ∧
    ((ics[0]!).consumeInput = .fn "consume_markers" ∨ (ics[0]!).consumeInput = .fn "dummy_consume_data") ∧
    dc.marker = .ref rmrk 0 ∧ C.Space.get h rmrk = some mrks ∧ 0 < mrks.size ∧
    (mrks[0]!).readMarkers = .fn "read_markers" ∧
    (mrks[0]!).resetMarkerReader = .fn "reset_marker_reader" ∧
    ((mrks[0]!).processCOM = .fn "save_marker" ∨ (mrks[0]!).processCOM = .fn "skip_variable") ∧
    (mrks[0]!).processAPPn.size = 16 ∧
    (∀ i < 16,
      (mrks[0]!).processAPPn[i]! = .fn "save_marker" ∨
      (mrks[0]!).processAPPn[i]! = .fn "skip_variable" ∨
      (mrks[0]!).processAPPn[i]! = .fn "get_interesting_appn") ∧
    (mrks[0]!).lengthLimitAPPn.size = 16 ∧
    dc.src = .ref rs 0 ∧ C.Space.get h rs = some srcs ∧ 0 < srcs.size ∧
    (srcs[0]!).initSource = .fn "init_mem_source" ∧
    ((srcs[0]!).termSource = .fn "term_source" ∨ (srcs[0]!).termSource = .fn "noop") ∧
    ((srcs[0]!).skipInputData = .fn "skip_input_data" ∨ (srcs[0]!).skipInputData = .fn "suspend_skip_input_data") ∧
    (srcs[0]!).resyncToRestart = .fn "jpeg_resync_to_restart" ∧
    ((srcs[0]!).fillInputBuffer = .fn "fill_mem_input_buffer" ∨
      ((srcs[0]!).fillInputBuffer = .fn "suspend_input" ∧ (srcs[0]!).skipInputData = .fn "suspend_skip_input_data")) ∧
    (srcs[0]!).bytesInBuffer.toNat < 2 ^ 20 ∧
    ((srcs[0]!).bytesInBuffer = 0 ∨ LiveBytes h (srcs[0]!).nextInputByte (srcs[0]!).bytesInBuffer.toNat) ∧
    (∀ off, (srcs[0]!).nextInputByte = .ref .const_eof off → off + (srcs[0]!).bytesInBuffer.toNat ≤ 2) ∧
    ((mrks[0]!).curMarker = .null ∨
      ∃ rsm off sms sm,
        (mrks[0]!).curMarker = .ref rsm off ∧ C.Space.get h rsm = some sms ∧ off < sms.size ∧
        sm = sms[off]! ∧ sm.dataLength.toNat ≤ 65535 ∧ sm.originalLength.toNat ≤ 65535 ∧
        WritableBytes h sm.data sm.dataLength.toNat ∧
        (mrks[0]!).bytesRead ≤ sm.dataLength) ∧
    (dc.markerList = .null ∨ (masters[0]!).markerListEnd = .null ∨
      ∃ rsm off sms,
        (masters[0]!).markerListEnd = .ref rsm off ∧ C.Space.get h rsm = some sms ∧ off < sms.size) ∧
    ((dc.compInfo = .null ∧ (mrks[0]!).sawSOF = 0) ∨
      (dc.compInfo ≠ .null ∧ (mrks[0]!).sawSOF ≠ 0 ∧ 0 ≤ dc.numComponents.toInt ∧
        LiveCompArray h dc.compInfo dc.numComponents.toInt.toNat)) ∧
    dc.quantTblPtrs.size = 4 ∧
    (∀ i < 4, dc.quantTblPtrs[i]! = .null ∨
      ∃ rq off qs, dc.quantTblPtrs[i]! = .ref rq off ∧ C.Space.get h rq = some qs ∧ off < qs.size) ∧
    dc.dcHuffTblPtrs.size = 4 ∧
    (∀ i < 4, dc.dcHuffTblPtrs[i]! = .null ∨
      ∃ rh off hs, dc.dcHuffTblPtrs[i]! = .ref rh off ∧ C.Space.get h rh = some hs ∧ off < hs.size) ∧
    dc.acHuffTblPtrs.size = 4 ∧
    (∀ i < 4, dc.acHuffTblPtrs[i]! = .null ∨
      ∃ rh off hs, dc.acHuffTblPtrs[i]! = .ref rh off ∧ C.Space.get h rh = some hs ∧ off < hs.size) ∧
    dc.curCompInfo.size = 4 ∧
    0 ≤ dc.inputScanNumber.toInt ∧ dc.inputScanNumber.toInt + 2 ^ 21 < 2 ^ 31

/-- Valid decompressor + input source ready for `jpeg_consume_input`. -/
def ValidDecompConsumeInput (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ValidDecompIoBase h cinfo ∧
  ∀ rc dcs dc ric ics,
    cinfo = .ref rc 0 → C.Space.get h rc = some dcs → 0 < dcs.size → dc = dcs[0]! →
    dc.inputctl = .ref ric 0 → C.Space.get h ric = some ics → 0 < ics.size →
    dc.globalState = DSTATE_START ∨
      ics[0]!.inheaders ≠ 0 ∨ ics[0]!.eoiReached ≠ 0 ∨ ics[0]!.hasMultipleScans = 0 ∨
      MultiScanReady h dc

/-- Valid decompressor + input source ready for `jpeg_read_header`. -/
def ValidDecompHeaderInput (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ValidDecompConsumeInput h cinfo

/-- Valid decompressor + input source ready for `jpeg_finish_decompress`. -/
def ValidDecompFinishInput (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ValidDecompIoBase h cinfo ∧
  ∀ rc dcs dc rmas masters ric ics,
    cinfo = .ref rc 0 → C.Space.get h rc = some dcs → 0 < dcs.size → dc = dcs[0]! →
    dc.master = .ref rmas 0 → C.Space.get h rmas = some masters → 0 < masters.size →
    dc.inputctl = .ref ric 0 → C.Space.get h ric = some ics → 0 < ics.size →
    ((ics[0]!.inheaders ≠ 0 ∧ dc.entropyStartPass = .fn "noop" ∧
        dc.coefStartInputPass = .fn "noop" ∧ dc.coefConsumeData = .fn "dummy_consume_data") ∨
      ics[0]!.eoiReached ≠ 0 ∨ ics[0]!.consumeInput = .fn "dummy_consume_data" ∨
      (ics[0]!.inheaders = 0 ∧ ics[0]!.hasMultipleScans = 0) ∨ MultiScanReady h dc) ∧
    ((dc.globalState ≠ DSTATE_SCANNING ∧ dc.globalState ≠ DSTATE_RAW_OK) ∨
      dc.bufferedImage ≠ 0 ∨ dc.outputScanline < dc.outputHeight ∨
      masters[0]!.finishOutputPass = .fn "finish_output_pass")

end MozjpegF.Spec
