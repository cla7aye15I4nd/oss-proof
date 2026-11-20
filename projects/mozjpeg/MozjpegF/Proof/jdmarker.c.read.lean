import MozjpegF.Proof.«jdmarker.c.helpers»
import MozjpegF.Proof.«jmemmgr.c.helpers»

/-!
# Marker-reader helper proofs (`jdmarker.c`, `MozjpegF`)

Proves safety and termination of `first_marker`, `get_soi`, `get_sof`, `get_sos`,
`get_dac`, `get_dht`, `get_dqt`, `get_dri`, `examine_app0`, `examine_app14`,
`get_interesting_appn`, `save_marker`, `skip_variable`, `callMarkerParser`,
and `read_markers`.
-/

set_option autoImplicit false

namespace MozjpegF.Proof.JdmarkerRead
open C MozjpegF.Spec Mozjpeg.Jerror Mozjpeg.JerrorH Mozjpeg.Jcomapi Mozjpeg.Jmemnobs
open Mozjpeg.Jmemmgr Mozjpeg.Jdatasrc Mozjpeg.Jdmarker Mozjpeg.JpeglibH Mozjpeg.MoreCfg
open MozjpegF.Proof.JdmarkerHelpers MozjpegF.Proof.JmemmgrHelpers

def isConstEofPtr (p : C.BPtr) : Bool :=
  match p with | .ref .const_eof _ => true | _ => false

def srcRank (src : C.JpegSourceMgr) : Nat :=
  src.bytesInBuffer.toNat + if isConstEofPtr src.nextInputByte then 0 else 2 ^ 15

def srcPotential (err : C.JpegErrorMgr) (src : C.JpegSourceMgr) : Int :=
  err.numWarnings.toInt + 4 * (src.bytesInBuffer.toNat : Int) +
    if isConstEofPtr src.nextInputByte then 0 else (2 ^ 17 : Int)

def scanLimit (dc : C.JpegDecompressStruct) (src : C.JpegSourceMgr) : Int :=
  dc.inputScanNumber.toInt +
    (if isConstEofPtr src.nextInputByte then
      if dc.unreadMarker == M_SOS then 2 else 0
    else (src.bytesInBuffer.toNat : Int) + 4)

/-- Frame invariant for operations that may mutate only `errMgrs`, `markers`, `srcs`,
`decomps`, `comps`, `quants`, `huffs`, `savedMarkers`, `mems`, `masters`, `bytes`,
`nextBlk`, `nalloc` while preserving `consts`, `i32s`, `inputctls`, `allocOk`, and fixed graph ids. -/
def IoEnv (h : C.Heap) (cinfo : C.DecompPtr) (nwBudget : Int) : Prop :=
  ValidDecompCore h cinfo ∧
  FreshNextBlk h ∧
  ∃ rc dcs dc rerr errs rmem mems rmas masters ric ics rmrk mrks rs srcs,
    cinfo = .ref rc 0 ∧ C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
    dc.err = .ref rerr 0 ∧ C.Space.get h rerr = some errs ∧ 0 < errs.size ∧
    (errs[0]!).resetErrorMgr = .fn "reset_error_mgr" ∧
    0 ≤ (errs[0]!).numWarnings.toInt ∧
    srcPotential (errs[0]!) (srcs[0]!) ≤ nwBudget ∧
    nwBudget + 2 ^ 17 < 2 ^ 63 ∧
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
    0 ≤ dc.inputScanNumber.toInt ∧ scanLimit dc (srcs[0]!) < 2 ^ 31

theorem ioEnv_of_validIoBase {h : C.Heap} {cinfo : C.DecompPtr}
    (hv : ValidDecompIoBase h cinfo) :
    ∃ nw, IoEnv h cinfo nw := by
  obtain ⟨hcore, hfr, rc, dcs, dc, rerr, errs, rmem, mems, rmas, masters, ric, ics, rmrk, mrks, rs, srcs,
    hc, hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0, hnwHi,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hbibLt, hbibLive, hceof,
    hcurm, hmlEnd, hcomp, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0, hisnHi⟩ := hv
  refine ⟨(errs[0]!).numWarnings.toInt + 2 ^ 24, hcore, hfr, rc, dcs, dc, rerr, errs, rmem, mems,
    rmas, masters, ric, ics, rmrk, mrks, rs, srcs, hc, hgdc, hszdc, hdc, herrp, hgerr, hszerr,
    hrem, hnw0, ?_, (by omega), hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz,
    hpm, hpi, hpmk, hps, hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci, hmrkp, hgmrk, hszmrk,
    hrm, hrmr, hpcom, hpappSz, hpapp, hllSz, hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill,
    hbibLt, hbibLive, hceof, hcurm, hmlEnd, hcomp, hqtSz, hqt, hdhSz, hdh, hahSz, hah,
    hccSz, hisn0, ?_⟩
  · unfold srcPotential; split <;> omega
  · unfold scanLimit; split <;> (try split) <;> omega

theorem ioEnv_mono {h : C.Heap} {cinfo : C.DecompPtr} {nw1 nw2 : Int}
    (hle : nw1 ≤ nw2) (hhi : nw2 + 2 ^ 17 < 2 ^ 63) (henv : IoEnv h cinfo nw1) :
    IoEnv h cinfo nw2 := by
  obtain ⟨hcore, hfr, rc, dcs, dc, rerr, errs, rmem, mems, rmas, masters, ric, ics, rmrk, mrks, rs, srcs,
    hc, hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0, hpot, _hbd, hrest⟩ := henv
  exact ⟨hcore, hfr, rc, dcs, dc, rerr, errs, rmem, mems, rmas, masters, ric, ics, rmrk, mrks, rs, srcs,
    hc, hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0, Int.le_trans hpot hle, hhi, hrest⟩

/-- Frame predicate describing fields left unchanged by marker parsing helpers. -/
def MarkerFrame (h' h : C.Heap) (bdc : Nat) (rmem : C.MemRef) (ric : C.InputCtlRef) : Prop :=
  h'.consts = h.consts ∧ h'.i32s = h.i32s ∧ h'.mems = h.mems ∧
  h'.inputctls = h.inputctls ∧ h'.allocOk = h.allocOk ∧
  h.nextBlk ≤ h'.nextBlk ∧
  (∀ dcs dc, C.Space.get h (C.DecompRef.decomp bdc) = some dcs → 0 < dcs.size → dc = dcs[0]! →
    ∃ dcs', C.Space.get h' (C.DecompRef.decomp bdc) = some dcs' ∧ 0 < dcs'.size ∧
      dcs'[0]!.err = dc.err ∧ dcs'[0]!.mem = dc.mem ∧ dcs'[0]!.master = dc.master ∧
      dcs'[0]!.inputctl = dc.inputctl ∧ dcs'[0]!.marker = dc.marker ∧ dcs'[0]!.src = dc.src ∧
      dcs'[0]!.curCompInfo.size = dc.curCompInfo.size ∧
      dcs'[0]!.quantTblPtrs.size = dc.quantTblPtrs.size ∧
      dcs'[0]!.dcHuffTblPtrs.size = dc.dcHuffTblPtrs.size ∧
      dcs'[0]!.acHuffTblPtrs.size = dc.acHuffTblPtrs.size) ∧
  (∀ mems, C.Space.get h rmem = some mems → C.Space.get h' rmem = some mems) ∧
  (∀ ics, C.Space.get h ric = some ics → C.Space.get h' ric = some ics)

/-! ## Indexed `IoCtx` / `IoState` representation for compact step proofs -/

structure IoCtx where
  bdc : Nat
  rerr : C.ErrRef
  rmem : C.MemRef
  rmas : C.MasterRef
  ric : C.InputCtlRef
  rmrk : C.MarkerRef
  rs : C.SrcRef

def IoState (ctx : IoCtx) (h : C.Heap) (nwBudget : Int) : Prop :=
  ValidDecompCore h (.ref (.decomp ctx.bdc) 0) ∧
  FreshNextBlk h ∧
  ∃ dcs dc errs mems masters ics mrks srcs,
    C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
    dc.err = .ref ctx.rerr 0 ∧ C.Space.get h ctx.rerr = some errs ∧ 0 < errs.size ∧
    (errs[0]!).resetErrorMgr = .fn "reset_error_mgr" ∧
    0 ≤ (errs[0]!).numWarnings.toInt ∧
    srcPotential (errs[0]!) (srcs[0]!) ≤ nwBudget ∧
    nwBudget + 2 ^ 17 < 2 ^ 63 ∧
    dc.mem = .ref ctx.rmem 0 ∧ C.Space.get h ctx.rmem = some mems ∧ 0 < mems.size ∧
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
    dc.master = .ref ctx.rmas 0 ∧ C.Space.get h ctx.rmas = some masters ∧ 0 < masters.size ∧
    dc.inputctl = .ref ctx.ric 0 ∧ C.Space.get h ctx.ric = some ics ∧ 0 < ics.size ∧
    (ics[0]!).resetInputController = .fn "reset_input_controller" ∧
    ((ics[0]!).consumeInput = .fn "consume_markers" ∨ (ics[0]!).consumeInput = .fn "dummy_consume_data") ∧
    dc.marker = .ref ctx.rmrk 0 ∧ C.Space.get h ctx.rmrk = some mrks ∧ 0 < mrks.size ∧
    (mrks[0]!).readMarkers = .fn "read_markers" ∧
    (mrks[0]!).resetMarkerReader = .fn "reset_marker_reader" ∧
    ((mrks[0]!).processCOM = .fn "save_marker" ∨ (mrks[0]!).processCOM = .fn "skip_variable") ∧
    (mrks[0]!).processAPPn.size = 16 ∧
    (∀ i < 16,
      (mrks[0]!).processAPPn[i]! = .fn "save_marker" ∨
      (mrks[0]!).processAPPn[i]! = .fn "skip_variable" ∨
      (mrks[0]!).processAPPn[i]! = .fn "get_interesting_appn") ∧
    (mrks[0]!).lengthLimitAPPn.size = 16 ∧
    dc.src = .ref ctx.rs 0 ∧ C.Space.get h ctx.rs = some srcs ∧ 0 < srcs.size ∧
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
    0 ≤ dc.inputScanNumber.toInt ∧ scanLimit dc (srcs[0]!) < 2 ^ 31

theorem ioEnv_to_ioState {h : C.Heap} {cinfo : C.DecompPtr} {nw : Int}
    (henv : IoEnv h cinfo nw) :
    ∃ ctx : IoCtx, cinfo = .ref (.decomp ctx.bdc) 0 ∧ IoState ctx h nw := by
  obtain ⟨hcore, hfr, rc, dcs, dc, rerr, errs, rmem, mems, rmas, masters, ric, ics, rmrk, mrks, rs, srcs,
    hc, hrest⟩ := henv
  cases rc with | decomp bdc =>
  exact ⟨⟨bdc, rerr, rmem, rmas, ric, rmrk, rs⟩, hc, hc ▸ hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs, hrest⟩

theorem ioState_to_ioEnv {ctx : IoCtx} {h : C.Heap} {nw : Int}
    (hs : IoState ctx h nw) :
    IoEnv h (.ref (.decomp ctx.bdc) 0) nw := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs, hrest⟩ := hs
  exact ⟨hcore, hfr, .decomp ctx.bdc, dcs, dc, ctx.rerr, errs, ctx.rmem, mems, ctx.rmas, masters,
    ctx.ric, ics, ctx.rmrk, mrks, ctx.rs, srcs, rfl, hrest⟩

theorem ioState_mono {ctx : IoCtx} {h : C.Heap} {nw1 nw2 : Int}
    (hle : nw1 ≤ nw2) (hhi : nw2 + 2 ^ 17 < 2 ^ 63) (hs : IoState ctx h nw1) :
    IoState ctx h nw2 := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    h1, h2, h3, h4, h5, h6, h7, h8, hpot, _hbd, hrest⟩ := hs
  exact ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    h1, h2, h3, h4, h5, h6, h7, h8, Int.le_trans hpot hle, hhi, hrest⟩

theorem ioState_to_resyncEnv {ctx : IoCtx} {h : C.Heap} {nw : Int}
    (hs : IoState ctx h nw) :
    ResyncEnv h ctx.bdc ctx.rerr ctx.rmrk ctx.rs nw ∧
    nw + 2 ^ 17 < 2 ^ 63 ∧
    (∃ srcs, C.Space.get h ctx.rs = some srcs ∧ 0 < srcs.size ∧
      srcs[0]!.bytesInBuffer.toNat < 2 ^ 20 ∧
      (srcs[0]!.bytesInBuffer = 0 ∨ LiveBytes h srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer.toNat)) := by
  obtain ⟨_hcore, _hfr, dcs, dc, errs, _mems, _masters, _ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, _hrem, hnw0, hpot, hbd,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    hmrkp, hgmrk, hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    hsrcp, hgsrc, hszsrc, _his, _hts, _hsip, _hrtr, hfill, hbibLt, hbibLive, _hrest⟩ := hs
  have hnwLe : (errs[0]!).numWarnings.toInt ≤ nw := by
    unfold srcPotential at hpot
    split at hpot <;> omega
  refine ⟨⟨dcs, errs, mrks, srcs, hgdc, hszdc, hdc ▸ herrp, hdc ▸ hmrkp, hdc ▸ hsrcp,
    hgerr, hszerr, hnw0, hnwLe, hgmrk, hszmrk, hgsrc, hszsrc, ?_⟩, hbd,
    ⟨srcs, hgsrc, hszsrc, hbibLt, hbibLive⟩⟩
  rcases hfill with hf | ⟨hf, _⟩
  · right; exact hf
  · left; exact hf

/-! ## Generic `cwhile`/`cdoWhile` frame preservation & `next_marker` frame -/

theorem cwhile_go_preserves {σ : Type} (cond : σ → C.M (Bool × σ)) (body : σ → C.M σ)
    (R : C.Heap → C.Heap → Prop)
    (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hCond : ∀ s h c s' h', C.run (cond s) h = .ok ((c, s'), h') → R h h')
    (hBody : ∀ s h s' h', C.run (body s) h = .ok (s', h') → R h h') :
    ∀ n s h s' h', C.run (C.cwhile.go cond body n s) h = .ok (s', h') → R h h' := by
  intro n
  induction n with
  | zero =>
    intro s h s' h' hrun
    cases hrun
  | succ n ih =>
    intro s h s' h' hrun
    unfold C.cwhile.go at hrun
    cases hc : C.run (cond s) h with
    | error e => rw [C.run_bind, hc] at hrun; cases hrun
    | ok res1 =>
      rcases res1 with ⟨⟨c, s1⟩, h1⟩
      rw [C.run_bind, hc] at hrun
      dsimp only at hrun
      have hr01 := hCond s h c s1 h1 hc
      cases c with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hrun
        cases hrun
        exact hr01
      | true =>
        simp only [↓reduceIte] at hrun
        cases hb : C.run (body s1) h1 with
        | error e => rw [C.run_bind, hb] at hrun; cases hrun
        | ok res2 =>
          rcases res2 with ⟨s2, h2⟩
          rw [C.run_bind, hb] at hrun
          exact hTrans (hTrans hr01 (hBody s1 h1 s2 h2 hb)) (ih s2 h2 s' h' hrun)

theorem cwhile_preserves {σ : Type} (cond : σ → C.M (Bool × σ)) (body : σ → C.M σ)
    (R : C.Heap → C.Heap → Prop)
    (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hCond : ∀ s h c s' h', C.run (cond s) h = .ok ((c, s'), h') → R h h')
    (hBody : ∀ s h s' h', C.run (body s) h = .ok (s', h') → R h h')
    {s : σ} {h : C.Heap} {s' : σ} {h' : C.Heap}
    (hrun : C.run (C.cwhile cond body s) h = .ok (s', h')) : R h h' :=
  cwhile_go_preserves cond body R @hTrans hCond hBody C.fuel s h s' h' hrun

theorem cdoWhile_go_preserves {σ : Type} (body : σ → C.M σ) (cond : σ → C.M (Bool × σ))
    (R : C.Heap → C.Heap → Prop)
    (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hBody : ∀ s h s' h', C.run (body s) h = .ok (s', h') → R h h')
    (hCond : ∀ s h c s' h', C.run (cond s) h = .ok ((c, s'), h') → R h h') :
    ∀ n s h s' h', C.run (C.cdoWhile.go body cond n s) h = .ok (s', h') → R h h' := by
  intro n
  induction n with
  | zero =>
    intro s h s' h' hrun
    cases hrun
  | succ n ih =>
    intro s h s' h' hrun
    unfold C.cdoWhile.go at hrun
    cases hb : C.run (body s) h with
    | error e => rw [C.run_bind, hb] at hrun; cases hrun
    | ok res1 =>
      rcases res1 with ⟨s1, h1⟩
      rw [C.run_bind, hb] at hrun
      dsimp only at hrun
      have hr01 := hBody s h s1 h1 hb
      cases hc : C.run (cond s1) h1 with
      | error e => rw [C.run_bind, hc] at hrun; cases hrun
      | ok res2 =>
        rcases res2 with ⟨⟨c, s2⟩, h2⟩
        rw [C.run_bind, hc] at hrun
        dsimp only at hrun
        have hr12 := hCond s1 h1 c s2 h2 hc
        cases c with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hrun
          cases hrun
          exact hTrans hr01 hr12
        | true =>
          simp only [↓reduceIte] at hrun
          exact hTrans (hTrans hr01 hr12) (ih s2 h2 s' h' hrun)

theorem cdoWhile_preserves {σ : Type} (body : σ → C.M σ) (cond : σ → C.M (Bool × σ))
    (R : C.Heap → C.Heap → Prop)
    (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hBody : ∀ s h s' h', C.run (body s) h = .ok (s', h') → R h h')
    (hCond : ∀ s h c s' h', C.run (cond s) h = .ok ((c, s'), h') → R h h')
    {s : σ} {h : C.Heap} {s' : σ} {h' : C.Heap}
    (hrun : C.run (C.cdoWhile body cond s) h = .ok (s', h')) : R h h' :=
  cdoWhile_go_preserves body cond R @hTrans hBody hCond C.fuel s h s' h' hrun

/-- Frame equivalence for operations that only modify `errMgrs` (`msgCode`, `msgParmI`, `numWarnings`),
`markers` (`discardedBytes`), `srcs` (`nextInputByte`, `bytesInBuffer`), and `decomps` (`unreadMarker`). -/
def NextMarkerFrame (ctx : IoCtx) (h h' : C.Heap) : Prop :=
  h'.bytes = h.bytes ∧ h'.consts = h.consts ∧ h'.i32s = h.i32s ∧
  h'.mems = h.mems ∧ h'.masters = h.masters ∧ h'.inputctls = h.inputctls ∧
  h'.comps = h.comps ∧ h'.quants = h.quants ∧ h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧
  h'.nextBlk = h.nextBlk ∧ h'.nalloc = h.nalloc ∧ h'.allocOk = h.allocOk ∧
  (∀ k dcs, h.decomps k = some dcs → 0 < dcs.size →
    k = ctx.bdc → ∃ dcs', h'.decomps k = some dcs' ∧ 0 < dcs'.size ∧
      { dcs'[0]! with unreadMarker := dcs[0]!.unreadMarker } = dcs[0]!) ∧
  (∀ k, h.markers k = none → h'.markers k = none) ∧
  (∀ k, h.srcs k = none → h'.srcs k = none) ∧
  (∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
    ∃ mrks', C.Space.get h' ctx.rmrk = some mrks' ∧ 0 < mrks'.size ∧
      { mrks'[0]! with discardedBytes := mrks[0]!.discardedBytes } = mrks[0]!) ∧
  (∀ srcs, C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
    ∃ srcs', C.Space.get h' ctx.rs = some srcs' ∧ 0 < srcs'.size ∧
      { srcs'[0]! with nextInputByte := srcs[0]!.nextInputByte, bytesInBuffer := srcs[0]!.bytesInBuffer } = srcs[0]!) ∧
  (∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
    ∃ errs', C.Space.get h' ctx.rerr = some errs' ∧ 0 < errs'.size ∧
      (errs'[0]!).resetErrorMgr = (errs[0]!).resetErrorMgr)

theorem nextMarkerFrame_refl (ctx : IoCtx) (h : C.Heap) : NextMarkerFrame ctx h h := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ dcs hg hsz _; exact ⟨dcs, hg, hsz, by cases dcs[0]!; rfl⟩
  · intro _ hk; exact hk
  · intro _ hk; exact hk
  · intro mrks hg hsz; exact ⟨mrks, hg, hsz, by cases mrks[0]!; rfl⟩
  · intro srcs hg hsz; exact ⟨srcs, hg, hsz, by cases srcs[0]!; rfl⟩
  · intro errs hg hsz; exact ⟨errs, hg, hsz, rfl⟩

theorem nextMarkerFrame_trans (ctx : IoCtx) {a b c : C.Heap}
    (hab : NextMarkerFrame ctx a b) (hbc : NextMarkerFrame ctx b c) :
    NextMarkerFrame ctx a c := by
  rcases hab with ⟨b1, c1, i1, m1, ma1, ic1, cp1, q1, huf1, sm1, nb1, na1, ao1, dcb1, mn1, sn1, mr1, sr1, er1⟩
  rcases hbc with ⟨b2, c2, i2, m2, ma2, ic2, cp2, q2, huf2, sm2, nb2, na2, ao2, dcb2, mn2, sn2, mr2, sr2, er2⟩
  refine ⟨b2.trans b1, c2.trans c1, i2.trans i1, m2.trans m1, ma2.trans ma1, ic2.trans ic1,
    cp2.trans cp1, q2.trans q1, huf2.trans huf1, sm2.trans sm1, nb2.trans nb1, na2.trans na1, ao2.trans ao1,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k dcs hg hsz hk
    obtain ⟨dcs1, hg1, hsz1, heq1⟩ := dcb1 k dcs hg hsz hk
    obtain ⟨dcs2, hg2, hsz2, heq2⟩ := dcb2 k dcs1 hg1 hsz1 hk
    refine ⟨dcs2, hg2, hsz2, ?_⟩
    have hcongr := congrArg (fun x => { x with unreadMarker := dcs[0]!.unreadMarker }) heq2
    simpa using hcongr.trans heq1
  · intro k hk; exact mn2 k (mn1 k hk)
  · intro k hk; exact sn2 k (sn1 k hk)
  · intro mrks hg hsz
    obtain ⟨mrks1, hg1, hsz1, heq1⟩ := mr1 mrks hg hsz
    obtain ⟨mrks2, hg2, hsz2, heq2⟩ := mr2 mrks1 hg1 hsz1
    refine ⟨mrks2, hg2, hsz2, ?_⟩
    have hcongr := congrArg (fun x => { x with discardedBytes := mrks[0]!.discardedBytes }) heq2
    simpa using hcongr.trans heq1
  · intro srcs hg hsz
    obtain ⟨srcs1, hg1, hsz1, heq1⟩ := sr1 srcs hg hsz
    obtain ⟨srcs2, hg2, hsz2, heq2⟩ := sr2 srcs1 hg1 hsz1
    refine ⟨srcs2, hg2, hsz2, ?_⟩
    have hcongr := congrArg (fun x => { x with nextInputByte := srcs[0]!.nextInputByte, bytesInBuffer := srcs[0]!.bytesInBuffer }) heq2
    simpa using hcongr.trans heq1
  · intro errs hg hsz
    obtain ⟨errs1, hg1, hsz1, heq1⟩ := er1 errs hg hsz
    obtain ⟨errs2, hg2, hsz2, heq2⟩ := er2 errs1 hg1 hsz1
    exact ⟨errs2, hg2, hsz2, heq2.trans heq1⟩

private theorem load_ref0_inv {R T : Type} [C.Space C.Heap R T] [Inhabited T]
    {r : R} {h : C.Heap} {x : T} {h' : C.Heap}
    (hload : C.run (C.Ptr.load (.ref r 0)) h = .ok (x, h')) :
    ∃ xs, C.Space.get h r = some xs ∧ 0 < xs.size ∧ x = xs[0]! ∧ h' = h := by
  simp only [C.run, C.Ptr.load] at hload
  cases hg : C.Space.get h r with
  | none => rw [hg] at hload; cases hload
  | some xs =>
    simp only [hg] at hload
    split at hload
    · rename_i hsz
      cases hload
      exact ⟨xs, rfl, hsz, (getElem!_pos xs 0 hsz).symm, rfl⟩
    · cases hload

private theorem store_ref0_inv {R T : Type} [C.Space C.Heap R T] {r : R} {v : T} {h h' : C.Heap}
    (hstore : C.run (C.Ptr.store (.ref r 0) v) h = .ok ((), h')) :
    ∃ xs, C.Space.get h r = some xs ∧ 0 < xs.size ∧ C.Space.ro h r = false ∧
      h' = C.Space.put h r (xs.set! 0 v) := by
  simp only [C.run, C.Ptr.store] at hstore
  cases hg : C.Space.get h r with
  | none => rw [hg] at hstore; cases hstore
  | some xs =>
    simp only [hg] at hstore
    by_cases hro : C.Space.ro h r = true
    · simp only [hro, ↓reduceIte] at hstore; cases hstore
    · simp only [hro] at hstore
      by_cases hsz : 0 < xs.size
      · simp only [hsz, ↓reduceIte] at hstore
        cases hstore
        refine ⟨xs, rfl, hsz, Bool.eq_false_iff.mpr hro, ?_⟩
        exact C.Space.modify_eq h r xs (fun a => a.set! 0 v) hg
      · simp only [hsz, ↓reduceIte] at hstore; cases hstore

private theorem set0_bang {T : Type} [Inhabited T] (xs : Array T) (hsz : 0 < xs.size) (v : T) :
    (xs.set! 0 v)[0]! = v := by
  simp only [Array.set!_eq_setIfInBounds]
  have hlt : 0 < (xs.setIfInBounds 0 v).size := by simpa using hsz
  rw [getElem!_pos _ 0 hlt, Array.getElem_setIfInBounds (by exact hsz)]
  simp

private theorem nextMarkerFrame_put_err (ctx : IoCtx) (h : C.Heap) (errs : Array C.JpegErrorMgr)
    (herr : ∀ ers, C.Space.get h ctx.rerr = some ers → 0 < ers.size →
      0 < errs.size ∧ (errs[0]!).resetErrorMgr = (ers[0]!).resetErrorMgr) :
    NextMarkerFrame ctx h (C.Space.put h ctx.rerr errs) := by
  cases herrp : ctx.rerr with | err bid =>
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, (fun _ hk => hk), (fun _ hk => hk), ?_, ?_, ?_⟩
  · intro _ dcs hg hsz _; exact ⟨dcs, hg, hsz, by cases dcs[0]!; rfl⟩
  · intro mrks hg hsz; exact ⟨mrks, hg, hsz, by cases mrks[0]!; rfl⟩
  · intro srcs hg hsz; exact ⟨srcs, hg, hsz, by cases srcs[0]!; rfl⟩
  · intro ers hg hsz
    obtain ⟨hsz', hrst⟩ := herr ers (herrp ▸ hg) hsz
    simp only [C.Space.get, C.Space.put, herrp, C.upd, Tbl.get_set, ↓reduceIte]
    exact ⟨errs, rfl, hsz', hrst⟩

private theorem nextMarkerFrame_put_mrk (ctx : IoCtx) (h : C.Heap) (mrks : Array C.JpegMarkerReader)
    (hmrk : (∃ ms, C.Space.get h ctx.rmrk = some ms) ∧
      ∀ ms, C.Space.get h ctx.rmrk = some ms → 0 < ms.size →
        0 < mrks.size ∧ { mrks[0]! with discardedBytes := ms[0]!.discardedBytes } = ms[0]!) :
    NextMarkerFrame ctx h (C.Space.put h ctx.rmrk mrks) := by
  cases hm : ctx.rmrk with | marker bid =>
  rcases hmrk with ⟨⟨ms0, hms0⟩, hmrk⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, (fun _ hk => hk), ?_, ?_, ?_⟩
  · intro _ dcs hg hsz _; exact ⟨dcs, hg, hsz, by cases dcs[0]!; rfl⟩
  · intro k hk
    change (h.markers.set bid (some mrks)).get k = none
    rw [Tbl.get_set]
    by_cases hkb : k = bid
    · subst hkb; simp only [C.Space.get, hm] at hms0; rw [hms0] at hk; cases hk
    · simp only [hkb, ↓reduceIte]; exact hk
  · intro ms hg hsz
    obtain ⟨hsz', heq⟩ := hmrk ms (hm ▸ hg) hsz
    simp only [C.Space.get, C.Space.put, hm, C.upd, Tbl.get_set, ↓reduceIte]
    exact ⟨mrks, rfl, hsz', heq⟩
  · intro srcs hg hsz; exact ⟨srcs, hg, hsz, by cases srcs[0]!; rfl⟩
  · intro errs hg hsz; exact ⟨errs, hg, hsz, rfl⟩

private theorem nextMarkerFrame_put_src (ctx : IoCtx) (h : C.Heap) (srcs : Array C.JpegSourceMgr)
    (hsrc : (∃ ss, C.Space.get h ctx.rs = some ss) ∧
      ∀ ss, C.Space.get h ctx.rs = some ss → 0 < ss.size →
        0 < srcs.size ∧
        { srcs[0]! with nextInputByte := ss[0]!.nextInputByte, bytesInBuffer := ss[0]!.bytesInBuffer } = ss[0]!) :
    NextMarkerFrame ctx h (C.Space.put h ctx.rs srcs) := by
  cases hs : ctx.rs with | src bid =>
  rcases hsrc with ⟨⟨ss0, hss0⟩, hsrc⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, (fun _ hk => hk), ?_, ?_, ?_, ?_⟩
  · intro _ dcs hg hsz _; exact ⟨dcs, hg, hsz, by cases dcs[0]!; rfl⟩
  · intro k hk
    change (h.srcs.set bid (some srcs)).get k = none
    rw [Tbl.get_set]
    by_cases hkb : k = bid
    · subst hkb; simp only [C.Space.get, hs] at hss0; rw [hss0] at hk; cases hk
    · simp only [hkb, ↓reduceIte]; exact hk
  · intro mrks hg hsz; exact ⟨mrks, hg, hsz, by cases mrks[0]!; rfl⟩
  · intro ss hg hsz
    obtain ⟨hsz', heq⟩ := hsrc ss (hs ▸ hg) hsz
    simp only [C.Space.get, C.Space.put, hs, C.upd, Tbl.get_set, ↓reduceIte]
    exact ⟨srcs, rfl, hsz', heq⟩
  · intro errs hg hsz; exact ⟨errs, hg, hsz, rfl⟩

private theorem nextMarkerFrame_put_dc (ctx : IoCtx) (h : C.Heap) (dcs : Array C.JpegDecompressStruct)
    (hdc : ∀ ds, h.decomps ctx.bdc = some ds → 0 < ds.size →
      0 < dcs.size ∧ { dcs[0]! with unreadMarker := ds[0]!.unreadMarker } = ds[0]!) :
    NextMarkerFrame ctx h (C.Space.put h (C.DecompRef.decomp ctx.bdc) dcs) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, (fun _ hk => hk), (fun _ hk => hk), ?_, ?_, ?_⟩
  · intro k ds hg hsz hk
    subst hk
    obtain ⟨hsz', heq⟩ := hdc ds hg hsz
    simp only [C.Space.put, C.upd, Tbl.get_set, ↓reduceIte]
    exact ⟨dcs, rfl, hsz', heq⟩
  · intro mrks hg hsz; exact ⟨mrks, hg, hsz, by cases mrks[0]!; rfl⟩
  · intro srcs hg hsz; exact ⟨srcs, hg, hsz, by cases srcs[0]!; rfl⟩
  · intro errs hg hsz; exact ⟨errs, hg, hsz, rfl⟩

private theorem nextMarkerFrame_of_emitMessage {ctx : IoCtx} {err : C.ErrPtr} {lvl : Int32}
    {h h' : C.Heap} (herr : err = .ref ctx.rerr 0)
    (hrun : C.run (emitMessage err lvl) h = .ok ((), h')) :
    NextMarkerFrame ctx h h' := by
  subst herr
  unfold emitMessage at hrun
  cases hl : C.run (Ptr.load (.ref ctx.rerr 0)) h with
  | error e => rw [C.run_bind, hl] at hrun; cases hrun
  | ok r0 =>
    rcases r0 with ⟨er0, h0⟩
    obtain ⟨ers0, hg0, hsz0, her0, hh0⟩ := load_ref0_inv hl
    rw [C.run_bind, hl] at hrun; dsimp only at hrun
    rw [hh0] at hrun
    by_cases hlvl : lvl < 0
    · simp only [hlvl, ↓reduceIte] at hrun
      cases hadd : C.run (i64Add er0.numWarnings 1) h with
      | error e => rw [C.run_bind, hadd] at hrun; cases hrun
      | ok r1 =>
        rcases r1 with ⟨nw, h1⟩
        have hh1 : h1 = h := by
          simp only [C.run, i64Add, checkI64] at hadd
          split at hadd <;> cases hadd; rfl
        rw [C.run_bind, hadd] at hrun; dsimp only at hrun
        rw [hh1] at hrun
        obtain ⟨ers1, hg1, hsz1, _, rfl⟩ := store_ref0_inv hrun
        apply nextMarkerFrame_put_err
        intro ers' hg' hsz'
        have he := Option.some.inj (hg'.symm.trans hg1)
        have he0 := Option.some.inj (hg'.symm.trans hg0)
        subst he
        refine ⟨by simp [hsz'], ?_⟩
        rw [set0_bang ers' hsz' _, her0, he0]
    · simp only [hlvl, ↓reduceIte] at hrun
      cases hrun
      exact nextMarkerFrame_refl ctx h

private theorem nextMarkerFrame_of_errStore {ctx : IoCtx} {err : C.ErrPtr}
    (f : C.JpegErrorMgr → C.JpegErrorMgr) (hf : ∀ e, (f e).resetErrorMgr = e.resetErrorMgr)
    {lvl : Int32} {h h' : C.Heap} (herr : err = .ref ctx.rerr 0)
    (hrun : C.run (do let e ← Ptr.load err; Ptr.store err (f e); emitMessage err lvl) h = .ok ((), h')) :
    NextMarkerFrame ctx h h' := by
  subst herr
  cases hl : C.run (Ptr.load (.ref ctx.rerr 0)) h with
  | error e => rw [C.run_bind, hl] at hrun; cases hrun
  | ok r0 =>
    rcases r0 with ⟨er0, h0⟩
    obtain ⟨ers0, hg0, hsz0, her0, hh0⟩ := load_ref0_inv hl
    rw [C.run_bind, hl] at hrun; dsimp only at hrun
    rw [hh0] at hrun
    cases hst : C.run (Ptr.store (.ref ctx.rerr 0) (f er0)) h with
    | error e => rw [C.run_bind, hst] at hrun; cases hrun
    | ok r1 =>
      rcases r1 with ⟨⟨⟩, h1⟩
      obtain ⟨ers1, hg1, hsz1, _, hh1⟩ := store_ref0_inv hst
      rw [C.run_bind, hst] at hrun; dsimp only at hrun
      rw [hh1] at hrun
      have hf01 : NextMarkerFrame ctx h (C.Space.put h ctx.rerr (ers1.set! 0 (f er0))) := by
        apply nextMarkerFrame_put_err
        intro ers' hg' hsz'
        have he := Option.some.inj (hg'.symm.trans hg1)
        have he0 := Option.some.inj (hg'.symm.trans hg0)
        subst he
        refine ⟨by simp [hsz'], ?_⟩
        rw [set0_bang ers' hsz' _, hf er0, her0, he0]
      exact nextMarkerFrame_trans ctx hf01 (nextMarkerFrame_of_emitMessage rfl hrun)

private theorem nextMarkerFrame_of_warnms {ctx : IoCtx} {err : C.ErrPtr} {code : Int32}
    {h h' : C.Heap} (herr : err = .ref ctx.rerr 0) (hrun : C.run (warnms err code) h = .ok ((), h')) :
    NextMarkerFrame ctx h h' :=
  nextMarkerFrame_of_errStore (fun e => { e with msgCode := code }) (fun _ => rfl) herr hrun

private theorem nextMarkerFrame_of_warnms2 {ctx : IoCtx} {err : C.ErrPtr} {code p1 p2 : Int32}
    {h h' : C.Heap} (herr : err = .ref ctx.rerr 0)
    (hrun : C.run (warnms2 err code p1 p2) h = .ok ((), h')) :
    NextMarkerFrame ctx h h' :=
  nextMarkerFrame_of_errStore (fun e => { e with msgCode := code, msgParmI := (e.msgParmI.set! 0 p1).set! 1 p2 })
    (fun _ => rfl) herr hrun

private theorem nextMarkerFrame_of_tracems2 {ctx : IoCtx} {err : C.ErrPtr} {lvl code p1 p2 : Int32}
    {h h' : C.Heap} (herr : err = .ref ctx.rerr 0)
    (hrun : C.run (tracems2 err lvl code p1 p2) h = .ok ((), h')) :
    NextMarkerFrame ctx h h' :=
  nextMarkerFrame_of_errStore (fun e => { e with msgCode := code, msgParmI := (e.msgParmI.set! 0 p1).set! 1 p2 })
    (fun _ => rfl) herr hrun

private theorem load_bptr_inv {p : C.BPtr} {h : C.Heap} {x : UInt8} {h' : C.Heap}
    (hl : C.run (C.Ptr.load p) h = .ok (x, h')) : h' = h := by
  simp only [C.run, C.Ptr.load] at hl
  cases p with
  | null => cases hl
  | ref r off =>
    simp only at hl
    cases hg : C.Space.get h r with
    | none => rw [hg] at hl; cases hl
    | some xs =>
      simp only [hg] at hl
      split at hl
      · cases hl; rfl
      · cases hl

private theorem add_bptr_inv {p p1 : C.BPtr} {k : Int} {h h' : C.Heap}
    (ha : C.run (C.Ptr.add p k) h = .ok (p1, h')) : h' = h := by
  simp only [C.run, C.Ptr.add] at ha
  cases p with
  | null => cases ha
  | ref r off =>
    simp only at ha
    cases hg : C.Space.get h r with
    | none => rw [hg] at ha; cases ha
    | some xs =>
      simp only [hg] at ha
      split at ha
      · cases ha; rfl
      · cases ha

/-- Core frame step lemma: `inputSync` preserves `NextMarkerFrame` and fixed pointer invariants. -/
private theorem nextMarkerFrame_of_inputSync {ctx : IoCtx} {h h' : C.Heap} {nib : C.BPtr} {bib : UInt64}
    (hdc : ∀ dcs, h.decomps ctx.bdc = some dcs → 0 < dcs.size → dcs[0]!.src = .ref ctx.rs 0)
    (hrun : C.run (inputSync (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) nib bib) h = .ok ((), h')) :
    NextMarkerFrame ctx h h' := by
  unfold inputSync at hrun
  cases hl0 : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h with
  | error e => rw [C.run_bind, hl0] at hrun; cases hrun
  | ok r0 =>
    rcases r0 with ⟨dc0, h0⟩
    obtain ⟨dcs0, hgdc0, hszdc0, rfl, hh0⟩ := load_ref0_inv hl0
    have hdc' := hdc dcs0 (hh0 ▸ hgdc0) hszdc0
    rw [C.run_bind, hl0] at hrun; dsimp only at hrun
    rw [hh0, hdc'] at hrun
    cases hl1 : C.run (Ptr.load (.ref ctx.rs 0)) h with
    | error e => rw [C.run_bind, hl1] at hrun; cases hrun
    | ok r1 =>
      rcases r1 with ⟨src0, h1⟩
      obtain ⟨srcs0, hgsrc0, hszsrc0, rfl, hh1⟩ := load_ref0_inv hl1
      rw [C.run_bind, hl1] at hrun; dsimp only at hrun
      rw [hh1] at hrun
      obtain ⟨srcs1, hgsrc1, hszsrc1, _, rfl⟩ := store_ref0_inv hrun
      apply nextMarkerFrame_put_src
      refine ⟨⟨srcs0, hgsrc0⟩, fun ss hgs hszs => ?_⟩
      have he := Option.some.inj (hgs.symm.trans hgsrc1)
      have he0 := Option.some.inj (hgs.symm.trans hgsrc0)
      subst he
      refine ⟨by simp [hszs], ?_⟩
      rw [set0_bang ss hszs _, he0]

private theorem nextMarkerFrame_of_fillMem {ctx : IoCtx} {h h' : C.Heap} {ret : Int32}
    (hdc : ∀ dcs, h.decomps ctx.bdc = some dcs → 0 < dcs.size →
      dcs[0]!.src = .ref ctx.rs 0 ∧ dcs[0]!.err = .ref ctx.rerr 0)
    (hrun : C.run (fill_mem_input_buffer (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h = .ok (ret, h')) :
    NextMarkerFrame ctx h h' := by
  unfold fill_mem_input_buffer at hrun
  cases hl0 : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h with
  | error e => rw [C.run_bind, hl0] at hrun; cases hrun
  | ok r0 =>
    rcases r0 with ⟨dc0, h0⟩
    obtain ⟨dcs0, hgdc0, hszdc0, rfl, hh0⟩ := load_ref0_inv hl0
    obtain ⟨hsrcp, herrp⟩ := hdc dcs0 (hh0 ▸ hgdc0) hszdc0
    rw [C.run_bind, hl0] at hrun; dsimp only at hrun
    rw [hh0, hsrcp, herrp] at hrun
    cases hw : C.run (warnms (.ref ctx.rerr 0) JWRN_JPEG_EOF) h with
    | error e => rw [C.run_bind, hw] at hrun; cases hrun
    | ok r2 =>
      rcases r2 with ⟨⟨⟩, h2⟩
      rw [C.run_bind, hw] at hrun; dsimp only at hrun
      have hf02 := nextMarkerFrame_of_warnms rfl hw
      cases hl1 : C.run (Ptr.load (.ref ctx.rs 0)) h2 with
      | error e => rw [C.run_bind, hl1] at hrun; cases hrun
      | ok r1 =>
        rcases r1 with ⟨src0, h1⟩
        obtain ⟨srcs0, hgsrc0, hszsrc0, rfl, hh1⟩ := load_ref0_inv hl1
        rw [C.run_bind, hl1] at hrun; dsimp only at hrun
        rw [hh1] at hrun
        cases hst : C.run (Ptr.store (.ref ctx.rs 0)
            { srcs0[0]! with nextInputByte := .ref .const_eof 0, bytesInBuffer := 2 }) h2 with
        | error e => rw [C.run_bind, hst] at hrun; cases hrun
        | ok r3 =>
          rcases r3 with ⟨⟨⟩, h3⟩
          rw [C.run_bind, hst] at hrun; dsimp only at hrun
          obtain ⟨srcs2, hgsrc2, hszsrc2, _, hh3⟩ := store_ref0_inv hst
          cases hrun
          rw [hh3]
          apply nextMarkerFrame_trans ctx hf02
          apply nextMarkerFrame_put_src
          refine ⟨⟨srcs0, hgsrc0⟩, fun ss hgs hszs => ?_⟩
          have he := Option.some.inj (hgs.symm.trans hgsrc2)
          have he0 := Option.some.inj (hgs.symm.trans hgsrc0)
          subst he
          refine ⟨by simp [hszs], ?_⟩
          rw [set0_bang ss hszs _, he0]

private theorem nextMarkerFrame_of_makeByteAvail {ctx : IoCtx} {h h' : C.Heap} {nib : C.BPtr} {bib : UInt64}
    {res : Option (C.BPtr × UInt64)}
    (hdc : ∀ dcs, h.decomps ctx.bdc = some dcs → 0 < dcs.size →
      dcs[0]!.src = .ref ctx.rs 0 ∧ dcs[0]!.err = .ref ctx.rerr 0)
    (hrun : C.run (makeByteAvail (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) nib bib) h = .ok (res, h')) :
    NextMarkerFrame ctx h h' := by
  unfold makeByteAvail at hrun
  by_cases hb : (bib != 0) = true
  · simp only [hb, ↓reduceIte] at hrun; cases hrun; exact nextMarkerFrame_refl ctx h
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hrun
    cases hl0 : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h with
    | error e => rw [C.run_bind, hl0] at hrun; cases hrun
    | ok r0 =>
      rcases r0 with ⟨dc0, h0⟩
      obtain ⟨dcs0, hgdc0, hszdc0, rfl, hh0⟩ := load_ref0_inv hl0
      obtain ⟨hsrcp, herrp⟩ := hdc dcs0 (hh0 ▸ hgdc0) hszdc0
      rw [C.run_bind, hl0] at hrun; dsimp only at hrun
      rw [hh0, hsrcp] at hrun
      cases hl1 : C.run (Ptr.load (.ref ctx.rs 0)) h with
      | error e => rw [C.run_bind, hl1] at hrun; cases hrun
      | ok r1 =>
        rcases r1 with ⟨src0, h1⟩
        obtain ⟨srcs0, hgsrc0, hszsrc0, _, hh1⟩ := load_ref0_inv hl1
        rw [C.run_bind, hl1] at hrun; dsimp only at hrun
        rw [hh1] at hrun
        by_cases hfm : src0.fillInputBuffer == .fn "fill_mem_input_buffer"
        · simp only [hfm, ↓reduceIte] at hrun
          cases hf : C.run (fill_mem_input_buffer (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h with
          | error e => rw [C.run_bind, hf] at hrun; cases hrun
          | ok rf =>
            rcases rf with ⟨okv, h2⟩
            rw [C.run_bind, hf] at hrun; dsimp only at hrun
            have hfr := nextMarkerFrame_of_fillMem hdc hf
            by_cases hok0 : okv == 0
            · simp only [hok0, ↓reduceIte] at hrun; cases hrun; exact hfr
            · simp only [hok0, Bool.false_eq_true, ↓reduceIte] at hrun
              cases hl2 : C.run (Ptr.load (.ref ctx.rs 0)) h2 with
              | error e => rw [C.run_bind, hl2] at hrun; cases hrun
              | ok r2 =>
                rcases r2 with ⟨src2, h3⟩
                obtain ⟨srcs2, hgsrc2, hszsrc2, rfl, hh3⟩ := load_ref0_inv hl2
                rw [C.run_bind, hl2] at hrun; dsimp only at hrun
                rw [hh3] at hrun
                split at hrun <;> cases hrun <;> exact hfr
        · simp only [hfm, Bool.false_eq_true, ↓reduceIte] at hrun
          by_cases hsu : src0.fillInputBuffer == .fn "suspend_input"
          · simp only [hsu, ↓reduceIte] at hrun; cases hrun; exact nextMarkerFrame_refl ctx h
          · simp only [hsu, Bool.false_eq_true, ↓reduceIte] at hrun; cases hrun

private theorem nextMarkerFrame_of_inputByte {ctx : IoCtx} {h h' : C.Heap} {nib : C.BPtr} {bib : UInt64}
    {res : Option (Int32 × C.BPtr × UInt64)}
    (hdc : ∀ dcs, h.decomps ctx.bdc = some dcs → 0 < dcs.size →
      dcs[0]!.src = .ref ctx.rs 0 ∧ dcs[0]!.err = .ref ctx.rerr 0)
    (hrun : C.run (inputByte (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) nib bib) h = .ok (res, h')) :
    NextMarkerFrame ctx h h' := by
  unfold inputByte at hrun
  cases hm : C.run (makeByteAvail (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) nib bib) h with
  | error e => rw [C.run_bind, hm] at hrun; cases hrun
  | ok rm =>
    rcases rm with ⟨opt, h1⟩
    rw [C.run_bind, hm] at hrun; dsimp only at hrun
    have hfr := nextMarkerFrame_of_makeByteAvail hdc hm
    cases opt with
    | none => cases hrun; exact hfr
    | some v =>
      rcases v with ⟨nib1, bib1⟩
      cases hl : C.run (Ptr.load nib1) h1 with
      | error e => rw [C.run_bind, hl] at hrun; cases hrun
      | ok rl =>
        rcases rl with ⟨b, h2⟩
        have hh2 := load_bptr_inv hl
        rw [C.run_bind, hl, hh2] at hrun; dsimp only at hrun
        cases ha : C.run (Ptr.add nib1 1) h1 with
        | error e => rw [C.run_bind, ha] at hrun; cases hrun
        | ok ra =>
          rcases ra with ⟨nib2, h3⟩
          have hh3 := add_bptr_inv ha
          rw [C.run_bind, ha, hh3] at hrun; dsimp only at hrun
          cases hrun; exact hfr

def HasDcPtrs (ctx : IoCtx) (h : C.Heap) : Prop :=
  ∃ dcs0, h.decomps ctx.bdc = some dcs0 ∧ 0 < dcs0.size ∧
    dcs0[0]!.src = .ref ctx.rs 0 ∧ dcs0[0]!.err = .ref ctx.rerr 0 ∧ dcs0[0]!.marker = .ref ctx.rmrk 0

private theorem hasDcPtrs_of_nextMarkerFrame {ctx : IoCtx} {h h' : C.Heap}
    (hf : NextMarkerFrame ctx h h') (hinit : HasDcPtrs ctx h) : HasDcPtrs ctx h' := by
  obtain ⟨dcs0, hg0, hsz0, hsrc0, herr0, hmrk0⟩ := hinit
  obtain ⟨dcs', hg', hsz', heq⟩ := hf.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ctx.bdc dcs0 hg0 hsz0 rfl
  exact ⟨dcs', hg', hsz',
    (congrArg C.JpegDecompressStruct.src heq).trans hsrc0,
    (congrArg C.JpegDecompressStruct.err heq).trans herr0,
    (congrArg C.JpegDecompressStruct.marker heq).trans hmrk0⟩

private theorem nextMarkerFrame_of_storeMrkDisc {ctx : IoCtx} {h h' : C.Heap} {v : UInt32}
    (hp : HasDcPtrs ctx h)
    (hrun : C.run (do
      let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
      let mrk ← Ptr.load dc.marker
      Ptr.store dc.marker { mrk with discardedBytes := v }) h = .ok ((), h')) :
    NextMarkerFrame ctx h h' := by
  obtain ⟨dcs0, hg0, hsz0, _, _, hmrk0⟩ := hp
  cases hl0 : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h with
  | error e => rw [C.run_bind, hl0] at hrun; cases hrun
  | ok r0 =>
    rcases r0 with ⟨dc0, h0⟩
    obtain ⟨dcs0', hg0', hsz0', rfl, hh0⟩ := load_ref0_inv hl0
    have hdeq : dcs0' = dcs0 := Option.some.inj (hg0'.symm.trans (hh0 ▸ hg0))
    have hmp : dcs0'[0]!.marker = .ref ctx.rmrk 0 := hdeq ▸ hmrk0
    rw [C.run_bind, hl0] at hrun; dsimp only at hrun
    rw [hh0, hmp] at hrun
    cases hl1 : C.run (Ptr.load (.ref ctx.rmrk 0)) h with
    | error e => rw [C.run_bind, hl1] at hrun; cases hrun
    | ok r1 =>
      rcases r1 with ⟨mrk0, h1⟩
      obtain ⟨mrks0, hgmrk0, hszmrk0, rfl, hh1⟩ := load_ref0_inv hl1
      rw [C.run_bind, hl1] at hrun; dsimp only at hrun
      rw [hh1] at hrun
      obtain ⟨mrks1, hgmrk1, hszmrk1, _, rfl⟩ := store_ref0_inv hrun
      apply nextMarkerFrame_put_mrk
      refine ⟨⟨mrks0, hgmrk0⟩, fun ms hgm hszm => ?_⟩
      have he := Option.some.inj (hgm.symm.trans hgmrk1)
      have he0 := Option.some.inj (hgm.symm.trans hgmrk0)
      subst he
      refine ⟨by simp [hszm], ?_⟩
      rw [set0_bang ms hszm _, he0]

theorem next_marker_frame {ctx : IoCtx} {h h' : C.Heap} {ret : Int32}
    (hinit : HasDcPtrs ctx h)
    (hrun : C.run (next_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (ret, h')) :
    NextMarkerFrame ctx h h' := by
  let R : C.Heap → C.Heap → Prop := fun a b =>
    HasDcPtrs ctx a → HasDcPtrs ctx b ∧ NextMarkerFrame ctx a b
  have hTransR : ∀ {a b c}, R a b → R b c → R a c := by
    intro a b c hab hbc ha
    obtain ⟨hb, fab⟩ := hab ha
    obtain ⟨hc, fbc⟩ := hbc hb
    exact ⟨hc, nextMarkerFrame_trans ctx fab fbc⟩
  have hR_of_frame : ∀ {a b}, (HasDcPtrs ctx a → NextMarkerFrame ctx a b) → R a b := by
    intro a b hf ha
    have f := hf ha
    exact ⟨hasDcPtrs_of_nextMarkerFrame f ha, f⟩
  have hdcPtr : ∀ {a}, HasDcPtrs ctx a →
      ∀ dcs, a.decomps ctx.bdc = some dcs → 0 < dcs.size →
        dcs[0]!.src = .ref ctx.rs 0 ∧ dcs[0]!.err = .ref ctx.rerr 0 := by
    intro a ha dcs hg _
    obtain ⟨dcs0, hg0, _, hsrc0, herr0, _⟩ := ha
    have he := Option.some.inj (hg.symm.trans hg0)
    subst he
    exact ⟨hsrc0, herr0⟩
  unfold next_marker at hrun
  cases hl0 : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h with
  | error e => rw [C.run_bind, hl0] at hrun; cases hrun
  | ok r0 =>
    rcases r0 with ⟨dc0, h0⟩
    obtain ⟨dcs0, hgdc0, hszdc0, hdc0Eq, hh0⟩ := load_ref0_inv hl0
    obtain ⟨dcs_i, hg_i, _, hsrc_i, _, _⟩ := id hinit
    have hdeq0 : dcs0 = dcs_i := Option.some.inj (hgdc0.symm.trans hg_i)
    have hsrcp0 : dc0.src = .ref ctx.rs 0 := (congrArg C.JpegDecompressStruct.src hdc0Eq).trans (hdeq0 ▸ hsrc_i)
    rw [C.run_bind, hl0] at hrun; dsimp only at hrun
    rw [hh0, hsrcp0] at hrun
    cases hl1 : C.run (Ptr.load (.ref ctx.rs 0)) h with
    | error e => rw [C.run_bind, hl1] at hrun; cases hrun
    | ok r1 =>
      rcases r1 with ⟨src0, h1⟩
      obtain ⟨srcs0, hgsrc0, hszsrc0, _, hh1⟩ := load_ref0_inv hl1
      rw [C.run_bind, hl1, hh1] at hrun; dsimp only at hrun
      cases hc : C.run (C.cwhile _ _ _) h with
      | error e => rw [C.run_bind, hc] at hrun; cases hrun
      | ok rcw =>
        rcases rcw with ⟨st, hw⟩
        rw [C.run_bind, hc] at hrun
        have hcwR : R h hw := by
          apply cwhile_preserves _ _ R @hTransR _ _ hc
          · intro s a c s' b hcond ha
            cases hcond; exact ⟨ha, nextMarkerFrame_refl ctx a⟩
          · intro s a s' b hbody
            cases hib : C.run (inputByte (.ref (.decomp ctx.bdc) 0) s.nib s.bib) a with
            | error e => rw [C.run_bind, hib] at hbody; cases hbody
            | ok rib =>
              rcases rib with ⟨opt0, a1⟩
              rw [C.run_bind, hib] at hbody; dsimp only at hbody
              have r01 : R a a1 := hR_of_frame (fun ha => nextMarkerFrame_of_inputByte (hdcPtr ha) hib)
              cases opt0 with
              | none => cases hbody; exact r01
              | some v0 =>
                rcases v0 with ⟨c0, nib0, bib0⟩
                cases hsk : C.run (C.cwhile _ _ _) a1 with
                | error e => rw [C.run_bind, hsk] at hbody; cases hbody
                | ok rsk =>
                  rcases rsk with ⟨sk, a2⟩
                  rw [C.run_bind, hsk] at hbody; dsimp only at hbody
                  have r12 : R a1 a2 := by
                    apply cwhile_preserves _ _ R @hTransR _ _ hsk
                    · intro _ x c _ y hcond hx; cases hcond; exact ⟨hx, nextMarkerFrame_refl ctx x⟩
                    · intro bs x s' y hbdy ha_x
                      have hstep1 : R x y := by
                        obtain ⟨dcs_x, hg_x, _, _, _, hmrk_x⟩ := id ha_x
                        cases hl_dx : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) x with
                        | error e => rw [C.run_bind, hl_dx] at hbdy; cases hbdy
                        | ok rd =>
                          rcases rd with ⟨dc_x, x'⟩
                          obtain ⟨dcsx', hgdcx', _, hdcxEq, hx'⟩ := load_ref0_inv hl_dx
                          have hdeqx : dcsx' = dcs_x := Option.some.inj (hgdcx'.symm.trans (hx' ▸ hg_x))
                          have hmx : dc_x.marker = .ref ctx.rmrk 0 :=
                            (congrArg C.JpegDecompressStruct.marker hdcxEq).trans (hdeqx ▸ hmrk_x)
                          rw [C.run_bind, hl_dx] at hbdy; dsimp only at hbdy
                          rw [hx', hmx] at hbdy
                          cases hl_mx : C.run (Ptr.load (.ref ctx.rmrk 0)) x with
                          | error e => rw [C.run_bind, hl_mx] at hbdy; cases hbdy
                          | ok rm =>
                            rcases rm with ⟨mrk_x, x''⟩
                            obtain ⟨mrksx', hgmrkx', _, hmrkxEq, hx''⟩ := load_ref0_inv hl_mx
                            rw [C.run_bind, hl_mx] at hbdy; dsimp only at hbdy
                            rw [hx''] at hbdy
                            cases hst_mx : C.run (Ptr.store (.ref ctx.rmrk 0)
                                { mrk_x with discardedBytes := mrk_x.discardedBytes + 1 }) x with
                            | error e => rw [C.run_bind, hst_mx] at hbdy; cases hbdy
                            | ok rm2 =>
                              rcases rm2 with ⟨⟨⟩, x1⟩
                              obtain ⟨mrks1, hgmrk1, _, _, hx1Eq⟩ := store_ref0_inv hst_mx
                              rw [C.run_bind, hst_mx] at hbdy; dsimp only at hbdy
                              have f_m : NextMarkerFrame ctx x x1 := by
                                rw [hx1Eq]
                                apply nextMarkerFrame_put_mrk
                                refine ⟨⟨mrksx', hgmrkx'⟩, fun ms hgm hszm => ?_⟩
                                have he := Option.some.inj (hgm.symm.trans hgmrk1)
                                have he0 := Option.some.inj (hgm.symm.trans hgmrkx')
                                subst he
                                refine ⟨by simp [hszm], ?_⟩
                                rw [set0_bang ms hszm _, hmrkxEq, he0]
                              have hx1P := hasDcPtrs_of_nextMarkerFrame f_m ha_x
                              have r_m : R x x1 := fun _ => ⟨hx1P, f_m⟩
                              cases hsy : C.run (inputSync (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) bs.nib bs.bib) x1 with
                              | error e => rw [C.run_bind, hsy] at hbdy; cases hbdy
                              | ok r_sy =>
                                rcases r_sy with ⟨⟨⟩, x2⟩
                                rw [C.run_bind, hsy] at hbdy; dsimp only at hbdy
                                have r_sy : R x1 x2 := hR_of_frame (fun h1x =>
                                  nextMarkerFrame_of_inputSync (fun dcs hg hsz => (hdcPtr h1x dcs hg hsz).1) hsy)
                                cases hib2 : C.run (inputByte (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) bs.nib bs.bib) x2 with
                                | error e => rw [C.run_bind, hib2] at hbdy; cases hbdy
                                | ok r_ib =>
                                  rcases r_ib with ⟨opt2, x3⟩
                                  rw [C.run_bind, hib2] at hbdy; dsimp only at hbdy
                                  have r_ib : R x2 x3 := hR_of_frame (fun h2x => nextMarkerFrame_of_inputByte (hdcPtr h2x) hib2)
                                  cases opt2 <;> cases hbdy <;> exact hTransR r_m (hTransR r_sy r_ib)
                      exact hstep1 ha_x
                  by_cases hsusp1 : sk.susp
                  · simp only [hsusp1, ↓reduceIte] at hbody; cases hbody; exact hTransR r01 r12
                  · simp only [hsusp1, Bool.false_eq_true, ↓reduceIte] at hbody
                    cases hfd : C.run (C.cdoWhile _ _ _) a2 with
                    | error e => rw [C.run_bind, hfd] at hbody; cases hbody
                    | ok rfd =>
                      rcases rfd with ⟨fd, a3⟩
                      rw [C.run_bind, hfd] at hbody; dsimp only at hbody
                      have r23 : R a2 a3 := by
                        apply cdoWhile_preserves _ _ R @hTransR _ _ hfd
                        · intro bs x s' y hbdy
                          cases hib3 : C.run (inputByte (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) bs.nib bs.bib) x with
                          | error e => rw [C.run_bind, hib3] at hbdy; cases hbdy
                          | ok r_ib =>
                            rcases r_ib with ⟨opt3, y'⟩
                            rw [C.run_bind, hib3] at hbdy; dsimp only at hbdy
                            have r3 := hR_of_frame (fun hx => nextMarkerFrame_of_inputByte (hdcPtr hx) hib3)
                            cases opt3 <;> cases hbdy <;> exact r3
                        · intro bs x c s' y hcond hx; cases hcond; exact ⟨hx, nextMarkerFrame_refl ctx x⟩
                      by_cases hsusp2 : fd.susp
                      · simp only [hsusp2, ↓reduceIte] at hbody; cases hbody; exact hTransR r01 (hTransR r12 r23)
                      · simp only [hsusp2, Bool.false_eq_true, ↓reduceIte] at hbody
                        by_cases hne : (fd.c != 0) = true
                        · simp only [hne, ↓reduceIte] at hbody; cases hbody; exact hTransR r01 (hTransR r12 r23)
                        · simp only [hne, Bool.false_eq_true, ↓reduceIte] at hbody
                          have htail : R a3 b := by
                            intro ha3
                            obtain ⟨dcs_3, hg_3, _, _, _, hmrk_3⟩ := id ha3
                            cases hl_d : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) a3 with
                            | error e => rw [C.run_bind, hl_d] at hbody; cases hbody
                            | ok rd =>
                              rcases rd with ⟨dc_3, a3'⟩
                              obtain ⟨dcs3', hgdc3', _, hdc3Eq, ha3'⟩ := load_ref0_inv hl_d
                              have hdeq3 : dcs3' = dcs_3 := Option.some.inj (hgdc3'.symm.trans (ha3' ▸ hg_3))
                              have hm3 : dc_3.marker = .ref ctx.rmrk 0 :=
                                (congrArg C.JpegDecompressStruct.marker hdc3Eq).trans (hdeq3 ▸ hmrk_3)
                              rw [C.run_bind, hl_d] at hbody; dsimp only at hbody
                              rw [ha3', hm3] at hbody
                              cases hl_m : C.run (Ptr.load (.ref ctx.rmrk 0)) a3 with
                              | error e => rw [C.run_bind, hl_m] at hbody; cases hbody
                              | ok rm =>
                                rcases rm with ⟨mrk_3, a3''⟩
                                obtain ⟨mrks3', hgmrk3', _, hmrk3Eq, ha3''⟩ := load_ref0_inv hl_m
                                rw [C.run_bind, hl_m] at hbody; dsimp only at hbody
                                rw [ha3''] at hbody
                                cases hst_m2 : C.run (Ptr.store (.ref ctx.rmrk 0)
                                    { mrk_3 with discardedBytes := mrk_3.discardedBytes + 2 }) a3 with
                                | error e => rw [C.run_bind, hst_m2] at hbody; cases hbody
                                | ok rm2 =>
                                  rcases rm2 with ⟨⟨⟩, a4⟩
                                  obtain ⟨mrks4, hgmrk4, _, _, ha4Eq⟩ := store_ref0_inv hst_m2
                                  rw [C.run_bind, hst_m2] at hbody; dsimp only at hbody
                                  have f34 : NextMarkerFrame ctx a3 a4 := by
                                    rw [ha4Eq]
                                    apply nextMarkerFrame_put_mrk
                                    refine ⟨⟨mrks3', hgmrk3'⟩, fun ms hgm hszm => ?_⟩
                                    have he := Option.some.inj (hgm.symm.trans hgmrk4)
                                    have he0 := Option.some.inj (hgm.symm.trans hgmrk3')
                                    subst he
                                    refine ⟨by simp [hszm], ?_⟩
                                    rw [set0_bang ms hszm _, hmrk3Eq, he0]
                                  have ha4 := hasDcPtrs_of_nextMarkerFrame f34 ha3
                                  cases hsy2 : C.run (inputSync (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) fd.nib fd.bib) a4 with
                                  | error e => rw [C.run_bind, hsy2] at hbody; cases hbody
                                  | ok r_sy =>
                                    rcases r_sy with ⟨⟨⟩, a5⟩
                                    rw [C.run_bind, hsy2] at hbody; dsimp only at hbody
                                    have f45 := nextMarkerFrame_of_inputSync (fun dcs hg hsz => (hdcPtr ha4 dcs hg hsz).1) hsy2
                                    have ha5 := hasDcPtrs_of_nextMarkerFrame f45 ha4
                                    cases hbody
                                    exact ⟨ha5, nextMarkerFrame_trans ctx f34 f45⟩
                          exact hTransR r01 (hTransR r12 (hTransR r23 htail))
        obtain ⟨hwP, f0w⟩ := hcwR hinit
        by_cases hret0 : st.ret == 0
        · simp only [hret0, ↓reduceIte] at hrun; cases hrun; exact f0w
        · simp only [hret0, Bool.false_eq_true, ↓reduceIte] at hrun
          cases hl2 : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) hw with
          | error e => rw [C.run_bind, hl2] at hrun; cases hrun
          | ok r2 =>
            rcases r2 with ⟨dc2, hw'⟩
            obtain ⟨dcs2, hgdc2, hszdc2, hdc2Eq, hhw'⟩ := load_ref0_inv hl2
            obtain ⟨dcs_w, hg_w, _, hsrc_w, herr_w, hmrk_w⟩ := id hwP
            have hdeq_w : dcs2 = dcs_w := Option.some.inj (hgdc2.symm.trans hg_w)
            have hmrkp2 : dc2.marker = .ref ctx.rmrk 0 :=
              (congrArg C.JpegDecompressStruct.marker hdc2Eq).trans (hdeq_w ▸ hmrk_w)
            have herrp2 : dc2.err = .ref ctx.rerr 0 :=
              (congrArg C.JpegDecompressStruct.err hdc2Eq).trans (hdeq_w ▸ herr_w)
            rw [C.run_bind, hl2] at hrun; dsimp only at hrun
            rw [hhw', hmrkp2] at hrun
            cases hl3 : C.run (Ptr.load (.ref ctx.rmrk 0)) hw with
            | error e => rw [C.run_bind, hl3] at hrun; cases hrun
            | ok r3 =>
              rcases r3 with ⟨mrk1, hw''⟩
              obtain ⟨mrks1, hgmrk1, hszmrk1, _, hhw''⟩ := load_ref0_inv hl3
              rw [C.run_bind, hl3] at hrun; dsimp only at hrun
              rw [hhw''] at hrun
              have htailR : ∀ hw1, HasDcPtrs ctx hw1 →
                  C.run (do
                    let dc2 ← Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
                    let src2 ← Ptr.load dc2.src
                    Ptr.store dc2.src { src2 with nextInputByte := st.nib, bytesInBuffer := st.bib }
                    Ptr.store (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) { dc2 with unreadMarker := st.c }
                    return TRUE) hw1 = .ok (ret, h') →
                  NextMarkerFrame ctx hw1 h' := by
                intro hw1 hwp ht
                obtain ⟨dcs_1, hg_1, _, hsrc_1, _, _⟩ := hwp
                cases hl4 : C.run (Ptr.load (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) hw1 with
                | error e => rw [C.run_bind, hl4] at ht; cases ht
                | ok r4 =>
                  rcases r4 with ⟨dc2', hw1'⟩
                  obtain ⟨dcs4, hgdc4, hszdc4, hdc2'Eq, hhw1'⟩ := load_ref0_inv hl4
                  have hdeq1 : dcs4 = dcs_1 := Option.some.inj (hgdc4.symm.trans hg_1)
                  have hsrcp4 : dc2'.src = .ref ctx.rs 0 :=
                    (congrArg C.JpegDecompressStruct.src hdc2'Eq).trans (hdeq1 ▸ hsrc_1)
                  rw [C.run_bind, hl4] at ht; dsimp only at ht
                  rw [hhw1', hsrcp4] at ht
                  cases hl5 : C.run (Ptr.load (.ref ctx.rs 0)) hw1 with
                  | error e => rw [C.run_bind, hl5] at ht; cases ht
                  | ok r5 =>
                    rcases r5 with ⟨src2, hw1''⟩
                    obtain ⟨srcs5, hgsrc5, hszsrc5, hsrc2Eq, hhw1''⟩ := load_ref0_inv hl5
                    rw [C.run_bind, hl5] at ht; dsimp only at ht
                    rw [hhw1''] at ht
                    cases hstS : C.run (Ptr.store (.ref ctx.rs 0)
                        { src2 with nextInputByte := st.nib, bytesInBuffer := st.bib }) hw1 with
                    | error e => rw [C.run_bind, hstS] at ht; cases ht
                    | ok rS =>
                      rcases rS with ⟨⟨⟩, hw2⟩
                      obtain ⟨srcs6, hgsrc6, hszsrc6, _, hhw2⟩ := store_ref0_inv hstS
                      rw [C.run_bind, hstS] at ht; dsimp only at ht
                      have fw12 : NextMarkerFrame ctx hw1 hw2 := by
                        rw [hhw2]
                        apply nextMarkerFrame_put_src
                        refine ⟨⟨srcs5, hgsrc5⟩, fun ss hgs hszs => ?_⟩
                        have he := Option.some.inj (hgs.symm.trans hgsrc6)
                        have he0 := Option.some.inj (hgs.symm.trans hgsrc5)
                        subst he
                        refine ⟨by simp [hszs], ?_⟩
                        rw [set0_bang ss hszs _, hsrc2Eq, he0]
                      cases hstD : C.run (Ptr.store (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
                          { dc2' with src := .ref ctx.rs 0, unreadMarker := st.c }) hw2 with
                      | error e => rw [C.run_bind, hstD] at ht; cases ht
                      | ok rD =>
                        rcases rD with ⟨⟨⟩, hw3⟩
                        obtain ⟨dcs7, hgdc7, hszdc7, _, hhw3⟩ := store_ref0_inv hstD
                        rw [C.run_bind, hstD] at ht; dsimp only at ht
                        cases ht
                        have fw23 : NextMarkerFrame ctx hw2 h' := by
                          rw [hhw3]
                          apply nextMarkerFrame_put_dc
                          intro ds hgd hszd
                          have hgdc4' : hw2.decomps ctx.bdc = some dcs4 := by
                            rw [hhw2]
                            cases ctx.rs; exact hgdc4
                          have hdeq2 : dcs7 = dcs4 := Option.some.inj (hgdc7.symm.trans hgdc4')
                          have he : ds = dcs4 := Option.some.inj (hgd.symm.trans hgdc4')
                          refine ⟨by simp [hdeq2, ← he, hszd], ?_⟩
                          have hds0 : ds[0]! = dc2' := by rw [he, ← hdc2'Eq]
                          rw [set0_bang dcs7 (hdeq2 ▸ he ▸ hszd) { dc2' with src := Ptr.ref ctx.rs 0, unreadMarker := st.c }, hds0]
                          have hsrc_dc4 : (dcs4[0]!).src = .ref ctx.rs 0 := hdeq1 ▸ hsrc_1
                          rw [← hdc2'Eq] at hsrc_dc4
                          rw [← hsrc_dc4]
                        exact nextMarkerFrame_trans ctx fw12 fw23
              by_cases hdis : (mrk1.discardedBytes != 0) = true
              · simp only [hdis, ↓reduceIte] at hrun
                rw [herrp2] at hrun
                cases hw2c : C.run (warnms2 (.ref ctx.rerr 0) JWRN_EXTRANEOUS_DATA
                    (Int32.ofNat mrk1.discardedBytes.toNat) st.c) hw with
                | error e => rw [C.run_bind, hw2c] at hrun; cases hrun
                | ok r2c =>
                  rcases r2c with ⟨⟨⟩, hw_a⟩
                  rw [C.run_bind, hw2c] at hrun; dsimp only at hrun
                  have f_wa := nextMarkerFrame_of_warnms2 rfl hw2c
                  have hp_a := hasDcPtrs_of_nextMarkerFrame f_wa hwP
                  cases hl_mrk : C.run (Ptr.load (.ref ctx.rmrk 0)) hw_a with
                  | error e => rw [C.run_bind, hl_mrk] at hrun; cases hrun
                  | ok rm_a =>
                    rcases rm_a with ⟨mrk2, hw_a'⟩
                    obtain ⟨mrks2, hgmrk2, hszmrk2, hmrk2Eq, hhw_a'⟩ := load_ref0_inv hl_mrk
                    rw [C.run_bind, hl_mrk] at hrun; dsimp only at hrun
                    rw [hhw_a'] at hrun
                    cases hst_m : C.run (Ptr.store (.ref ctx.rmrk 0) { mrk2 with discardedBytes := 0 }) hw_a with
                    | error e => rw [C.run_bind, hst_m] at hrun; cases hrun
                    | ok rm_b =>
                      rcases rm_b with ⟨⟨⟩, hw_b⟩
                      rw [C.run_bind, hst_m] at hrun; dsimp only at hrun
                      obtain ⟨mrks3, hgmrk3, hszmrk3, _, hhw_b⟩ := store_ref0_inv hst_m
                      have f_ab : NextMarkerFrame ctx hw_a hw_b := by
                        rw [hhw_b]
                        apply nextMarkerFrame_put_mrk
                        refine ⟨⟨mrks2, hgmrk2⟩, fun ms hgm hszm => ?_⟩
                        have he := Option.some.inj (hgm.symm.trans hgmrk3)
                        have he0 := Option.some.inj (hgm.symm.trans hgmrk2)
                        subst he
                        refine ⟨by simp [hszm], ?_⟩
                        rw [set0_bang ms hszm _, hmrk2Eq, he0]
                      have hp_b := hasDcPtrs_of_nextMarkerFrame f_ab hp_a
                      exact nextMarkerFrame_trans ctx f0w
                        (nextMarkerFrame_trans ctx f_wa (nextMarkerFrame_trans ctx f_ab (htailR hw_b hp_b hrun)))
              · have hdisF : (mrk1.discardedBytes != 0) = false := Bool.eq_false_iff.mpr hdis
                simp only [hdisF, Bool.false_eq_true, ↓reduceIte] at hrun
                exact nextMarkerFrame_trans ctx f0w (htailR hw hwP hrun)

theorem ioState_of_nextMarkerFrame {ctx : IoCtx} {h h' : C.Heap} {nw1 nw2 : Int}
    (hs : IoState ctx h nw1) (hf : NextMarkerFrame ctx h h')
    (hrenv : ResyncEnv h' ctx.bdc ctx.rerr ctx.rmrk ctx.rs nw2)
    (hsrcBound : ∃ srcs', C.Space.get h' ctx.rs = some srcs' ∧ 0 < srcs'.size ∧
      srcs'[0]!.bytesInBuffer.toNat < 2 ^ 20 ∧
      (srcs'[0]!.bytesInBuffer = 0 ∨ LiveBytes h' srcs'[0]!.nextInputByte srcs'[0]!.bytesInBuffer.toNat) ∧
      (∀ off, srcs'[0]!.nextInputByte = .ref .const_eof off → off + srcs'[0]!.bytesInBuffer.toNat ≤ 2))
    (hpot : ∀ errs' srcs', C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
      C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
      srcPotential errs'[0]! srcs'[0]! ≤ nw2 ∧ nw2 + 2 ^ 17 < 2 ^ 63)
    (hscan : ∀ dcs' srcs', C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
      C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
      scanLimit dcs'[0]! srcs'[0]! < 2 ^ 31) :
    IoState ctx h' nw2 := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, _hnw0, _hpot0, _hbd0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, _hbibLt, _hbibLive, _hceof,
    hcurm, hmlEnd, hcomp, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0, hisnHi⟩ := hs
  rcases hf with ⟨hb, hcst, hi32, hm, hma, hic, hcp, hq, hhuf, hsm, hnb, hna, hao, dcb, mn, sn, mrF, srF, erF⟩
  obtain ⟨dcs', errs', mrks', srcs', hgdc', hszdc', herrp', hmrkp', hsrcp',
    hgerr', hszerr', hnw0', _hnwLe', hgmrk', hszmrk', hgsrc', hszsrc', hfill'⟩ := hrenv
  obtain ⟨srcs'', hgsrc'', hszsrc'', hbibLt', hbibLive', hceof'⟩ := hsrcBound
  have hsEq'' : srcs'' = srcs' := Option.some.inj (hgsrc''.symm.trans hgsrc')
  rw [hsEq''] at hbibLt' hbibLive' hceof'
  obtain ⟨dcs1, hgdc1, hszdc1, hdceq⟩ := dcb ctx.bdc dcs hgdc hszdc rfl
  have hd1Eq : dcs1 = dcs' := Option.some.inj (hgdc1.symm.trans hgdc')
  rw [hd1Eq] at hdceq
  obtain ⟨mrks1, hgmrk1, hszmrk1, hmrkeq⟩ := mrF mrks hgmrk hszmrk
  have hm1Eq : mrks1 = mrks' := Option.some.inj (hgmrk1.symm.trans hgmrk')
  rw [hm1Eq] at hmrkeq
  obtain ⟨srcs1, hgsrc1, hszsrc1, hsrceq⟩ := srF srcs hgsrc hszsrc
  have hs1Eq : srcs1 = srcs' := Option.some.inj (hgsrc1.symm.trans hgsrc')
  rw [hs1Eq] at hsrceq
  obtain ⟨errs1, hgerr1, hszerr1, hrstEq⟩ := erF errs hgerr hszerr
  have he1Eq : errs1 = errs' := Option.some.inj (hgerr1.symm.trans hgerr')
  rw [he1Eq] at hrstEq
  have hgmem' : C.Space.get h' ctx.rmem = some mems := by
    rcases hr : ctx.rmem with ⟨b⟩; simp only [C.Space.get, hr] at hgmem ⊢; rw [hm]; exact hgmem
  have hgmas' : C.Space.get h' ctx.rmas = some masters := by
    rcases hr : ctx.rmas with ⟨b⟩; simp only [C.Space.get, hr] at hgmas ⊢; rw [hma]; exact hgmas
  have hgic' : C.Space.get h' ctx.ric = some ics := by
    rcases hr : ctx.ric with ⟨b⟩; simp only [C.Space.get, hr] at hgic ⊢; rw [hic]; exact hgic
  have hfr' : FreshNextBlk h' := by
    intro k hk
    rw [hnb] at hk
    obtain ⟨hbK, hiK, hmK, hmaK, hmrkK, hicK, hsrcK, hcpK, hqK, hhK, hsmK⟩ := hfr k hk
    refine ⟨hb ▸ hbK, hi32 ▸ hiK, hm ▸ hmK, hma ▸ hmaK, mn k hmrkK, hic ▸ hicK, sn k hsrcK,
      hcp ▸ hcpK, hq ▸ hqK, hhuf ▸ hhK, hsm ▸ hsmK⟩
  obtain ⟨hpot', hbd'⟩ := hpot errs' srcs' hgerr' hszerr' hgsrc' hszsrc'
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    refine ⟨.decomp ctx.bdc, dcs', dcs'[0]!, ctx.rmem, mems, ctx.rmas, masters, ctx.ric, ics, ctx.rmrk, mrks',
      rfl, hgdc', hszdc', rfl, ?_, ?_, hgmem', hszmem, ?_, hgmas', hszmas,
      ?_, hgic', hszic, hmrkp', hgmrk', hszmrk', (by omega), ?_⟩
    · refine ⟨ctx.rerr, errs', herrp', hgerr', hszerr'⟩
    · have hmemEq : dcs'[0]!.mem = dcs[0]!.mem := by have h := congrArg C.JpegDecompressStruct.mem hdceq; dsimp only at h; exact h
      rw [hmemEq, ← hdc]; exact hmemp
    · have hmasEq : dcs'[0]!.master = dcs[0]!.master := by have h := congrArg C.JpegDecompressStruct.master hdceq; dsimp only at h; exact h
      rw [hmasEq, ← hdc]; exact hmasp
    · have hicEq : dcs'[0]!.inputctl = dcs[0]!.inputctl := by have h := congrArg C.JpegDecompressStruct.inputctl hdceq; dsimp only at h; exact h
      rw [hicEq, ← hdc]; exact hicp
    · intro bmas _ hmem
      rcases hlst : (mems[0]!).poolAllocs[1]!.masters with ⟨l⟩
      cases l with
      | nil => simp [hlst] at hmem
      | cons _ _ => simp [hlst, Array.isEmpty] at hpm
  refine ⟨hcore', hfr', dcs', dcs'[0]!, errs', mems, masters, ics, mrks', srcs',
    hgdc', hszdc', rfl, herrp', hgerr', hszerr', hrstEq.trans hrem, hnw0', hpot', hbd',
    (by have hf : dcs'[0]!.mem = dcs[0]!.mem := by have h := congrArg C.JpegDecompressStruct.mem hdceq; dsimp only at h; exact h
        rw [hf, ← hdc]; exact hmemp),
    hgmem', hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    (by have hf : dcs'[0]!.master = dcs[0]!.master := by have h := congrArg C.JpegDecompressStruct.master hdceq; dsimp only at h; exact h
        rw [hf, ← hdc]; exact hmasp),
    hgmas', hszmas,
    (by have hf : dcs'[0]!.inputctl = dcs[0]!.inputctl := by have h := congrArg C.JpegDecompressStruct.inputctl hdceq; dsimp only at h; exact h
        rw [hf, ← hdc]; exact hicp),
    hgic', hszic, hric, hci, hmrkp', hgmrk', hszmrk',
    (by have hf : mrks'[0]!.readMarkers = mrks[0]!.readMarkers := by have h := congrArg C.JpegMarkerReader.readMarkers hmrkeq; dsimp only at h; exact h
        rw [hf]; exact hrm),
    (by have hf : mrks'[0]!.resetMarkerReader = mrks[0]!.resetMarkerReader := by have h := congrArg C.JpegMarkerReader.resetMarkerReader hmrkeq; dsimp only at h; exact h
        rw [hf]; exact hrmr),
    (by have hf : mrks'[0]!.processCOM = mrks[0]!.processCOM := by have h := congrArg C.JpegMarkerReader.processCOM hmrkeq; dsimp only at h; exact h
        rw [hf]; exact hpcom),
    (by have hf : mrks'[0]!.processAPPn = mrks[0]!.processAPPn := by have h := congrArg C.JpegMarkerReader.processAPPn hmrkeq; dsimp only at h; exact h
        rw [hf]; exact hpappSz),
    (by have hf : mrks'[0]!.processAPPn = mrks[0]!.processAPPn := by have h := congrArg C.JpegMarkerReader.processAPPn hmrkeq; dsimp only at h; exact h
        rw [hf]; exact hpapp),
    (by have hf : mrks'[0]!.lengthLimitAPPn = mrks[0]!.lengthLimitAPPn := by have h := congrArg C.JpegMarkerReader.lengthLimitAPPn hmrkeq; dsimp only at h; exact h
        rw [hf]; exact hllSz),
    hsrcp', hgsrc', hszsrc',
    (by have hf : srcs'[0]!.initSource = srcs[0]!.initSource := by have h := congrArg C.JpegSourceMgr.initSource hsrceq; dsimp only at h; exact h
        rw [hf]; exact his),
    (by have hf : srcs'[0]!.termSource = srcs[0]!.termSource := by have h := congrArg C.JpegSourceMgr.termSource hsrceq; dsimp only at h; exact h
        rw [hf]; exact hts),
    (by have hf : srcs'[0]!.skipInputData = srcs[0]!.skipInputData := by have h := congrArg C.JpegSourceMgr.skipInputData hsrceq; dsimp only at h; exact h
        rw [hf]; exact hsip),
    (by have hf : srcs'[0]!.resyncToRestart = srcs[0]!.resyncToRestart := by have h := congrArg C.JpegSourceMgr.resyncToRestart hsrceq; dsimp only at h; exact h
        rw [hf]; exact hrtr),
    (by have hf : srcs'[0]!.skipInputData = srcs[0]!.skipInputData := by have h := congrArg C.JpegSourceMgr.skipInputData hsrceq; dsimp only at h; exact h
        have hfb : srcs'[0]!.fillInputBuffer = srcs[0]!.fillInputBuffer := by have h := congrArg C.JpegSourceMgr.fillInputBuffer hsrceq; dsimp only at h; exact h
        rw [hf, hfb]; exact hfill),
    hbibLt', hbibLive', hceof', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hm_cm : mrks'[0]!.curMarker = mrks[0]!.curMarker := by have h := congrArg C.JpegMarkerReader.curMarker hmrkeq; dsimp only at h; exact h
    have hm_br : mrks'[0]!.bytesRead = mrks[0]!.bytesRead := by have h := congrArg C.JpegMarkerReader.bytesRead hmrkeq; dsimp only at h; exact h
    rw [hm_cm, hm_br]
    rcases hcurm with hnull | ⟨rsm, off, sms, sm, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · left; exact hnull
    · right; refine ⟨rsm, off, sms, sm, h1, ?_, h3, h4, h5, h6, ?_, h8⟩
      · have hgetSm : ∀ (r : C.SavedMarkerRef), C.Space.get h' r = C.Space.get h r :=
          fun r => by cases r; simp [C.Space.get, hsm]
        rw [hgetSm]; exact h2
      · rcases h7 with ⟨rb, boff, bdata, hp, hgb, hblen⟩
        exact ⟨rb, boff, bdata, hp, hb ▸ hgb, hblen⟩
  · have hdc_ml : dcs'[0]!.markerList = dcs[0]!.markerList := by have h := congrArg C.JpegDecompressStruct.markerList hdceq; dsimp only at h; exact h
    rw [hdc_ml, ← hdc]
    rcases hmlEnd with h1 | h2 | ⟨rsm, off, sms, h3, h4, h5⟩
    · left; exact h1
    · right; left; exact h2
    · right; right; refine ⟨rsm, off, sms, h3, ?_, h5⟩
      cases rsm; simp only [C.Space.get] at h4 ⊢; rw [hsm]; exact h4
  · have hdc_cp : dcs'[0]!.compInfo = dcs[0]!.compInfo := by have h := congrArg C.JpegDecompressStruct.compInfo hdceq; dsimp only at h; exact h
    have hdc_nc : dcs'[0]!.numComponents = dcs[0]!.numComponents := by have h := congrArg C.JpegDecompressStruct.numComponents hdceq; dsimp only at h; exact h
    have hm_sof : mrks'[0]!.sawSOF = mrks[0]!.sawSOF := by have h := congrArg C.JpegMarkerReader.sawSOF hmrkeq; dsimp only at h; exact h
    rw [hdc_cp, hdc_nc, ← hdc, hm_sof]
    rcases hcomp with ⟨hc1, hc2⟩ | ⟨hc1, hc2, hc3, hc4⟩
    · left; exact ⟨hc1, hc2⟩
    · right; refine ⟨hc1, hc2, hc3, ?_⟩
      obtain ⟨rcp, cps, hcpeq, hgcp, hlen⟩ := hc4
      refine ⟨rcp, cps, hcpeq, ?_, hlen⟩
      cases rcp; simp only [C.Space.get] at hgcp ⊢; rw [hcp]; exact hgcp
  · have hf_q : dcs'[0]!.quantTblPtrs = dcs[0]!.quantTblPtrs := by have h := congrArg C.JpegDecompressStruct.quantTblPtrs hdceq; dsimp only at h; exact h
    rw [hf_q, ← hdc]; exact hqtSz
  · have hf_q : dcs'[0]!.quantTblPtrs = dcs[0]!.quantTblPtrs := by have h := congrArg C.JpegDecompressStruct.quantTblPtrs hdceq; dsimp only at h; exact h
    rw [hf_q, ← hdc]
    intro i hi
    rcases hqt i hi with hnull | ⟨rq, off, qs, h1, h2, h3⟩
    · left; exact hnull
    · right; refine ⟨rq, off, qs, h1, ?_, h3⟩
      cases rq; simp only [C.Space.get] at h2 ⊢; rw [hq]; exact h2
  · have hf_dh : dcs'[0]!.dcHuffTblPtrs = dcs[0]!.dcHuffTblPtrs := by have h := congrArg C.JpegDecompressStruct.dcHuffTblPtrs hdceq; dsimp only at h; exact h
    rw [hf_dh, ← hdc]; exact hdhSz
  · have hf_dh : dcs'[0]!.dcHuffTblPtrs = dcs[0]!.dcHuffTblPtrs := by have h := congrArg C.JpegDecompressStruct.dcHuffTblPtrs hdceq; dsimp only at h; exact h
    rw [hf_dh, ← hdc]
    intro i hi
    rcases hdh i hi with hnull | ⟨rh, off, hs_, h1, h2, h3⟩
    · left; exact hnull
    · right; refine ⟨rh, off, hs_, h1, ?_, h3⟩
      cases rh; simp only [C.Space.get] at h2 ⊢; rw [hhuf]; exact h2
  · have hf_ah : dcs'[0]!.acHuffTblPtrs = dcs[0]!.acHuffTblPtrs := by have h := congrArg C.JpegDecompressStruct.acHuffTblPtrs hdceq; dsimp only at h; exact h
    rw [hf_ah, ← hdc]; exact hahSz
  · have hf_ah : dcs'[0]!.acHuffTblPtrs = dcs[0]!.acHuffTblPtrs := by have h := congrArg C.JpegDecompressStruct.acHuffTblPtrs hdceq; dsimp only at h; exact h
    rw [hf_ah, ← hdc]
    intro i hi
    rcases hah i hi with hnull | ⟨rh, off, hs_, h1, h2, h3⟩
    · left; exact hnull
    · right; refine ⟨rh, off, hs_, h1, ?_, h3⟩
      cases rh; simp only [C.Space.get] at h2 ⊢; rw [hhuf]; exact h2
  · have hf_cc : dcs'[0]!.curCompInfo = dcs[0]!.curCompInfo := by have h := congrArg C.JpegDecompressStruct.curCompInfo hdceq; dsimp only at h; exact h
    rw [hf_cc, ← hdc]; exact hccSz
  · have hf_isn : dcs'[0]!.inputScanNumber = dcs[0]!.inputScanNumber := by have h := congrArg C.JpegDecompressStruct.inputScanNumber hdceq; dsimp only at h; exact h
    rw [hf_isn, ← hdc]; exact hisn0
  · exact hscan dcs' srcs' hgdc' hszdc' hgsrc' hszsrc'

theorem next_marker_io {ctx : IoCtx} {h : C.Heap} {nw : Int}
    (hs : IoState ctx h nw) (hbd : nw + 2 + 2 ^ 17 < 2 ^ 63) :
    ∃ ret h',
      C.run (next_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (ret, h') ∧
      (ret = FALSE ∨
       ret = TRUE ∧ ∃ dcs' srcs' srcs0,
         C.Space.get h ctx.rs = some srcs0 ∧ 0 < srcs0.size ∧
         C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' ∧ 0 < dcs'.size ∧
         C.Space.get h' ctx.rs = some srcs' ∧ 0 < srcs'.size ∧
         ((dcs'[0]!.unreadMarker = M_EOI ∧ IoState ctx h' (nw + 2)) ∨
          (dcs'[0]!.unreadMarker ≠ M_EOI ∧
            isConstEofPtr srcs0[0]!.nextInputByte = false ∧
            srcRank srcs'[0]! < srcRank srcs0[0]! ∧
            IoState ctx h' nw))) := by
  obtain ⟨hrenv0, _hbd0, srcs0, hgsrc0, hszsrc0, hbib0Lt, hbib0Live⟩ := ioState_to_resyncEnv hs
  obtain ⟨_hc, _hf, dcs, _dc, errs, _mems, _mas, _ics, _mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, _hrem, hnw0, hpot0, _,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, hgsrc, hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hbibLt, _hbibLive, hceof0,
    _hcurm, _hmlEnd, _hcomp, _hqtSz, _hqt, _hdhSz, _hdh, _hahSz, _hah, _hccSz, _hisn0, hisnHi0⟩ := id hs
  have hs0Eq : srcs0 = srcs := Option.some.inj (hgsrc0.symm.trans hgsrc)
  have hnw0LeNw : errs[0]!.numWarnings.toInt ≤ nw := by
    have : 0 ≤ 4 * (srcs[0]!.bytesInBuffer.toNat : Int) := by omega
    have : 0 ≤ (if isConstEofPtr srcs[0]!.nextInputByte then (0 : Int) else 2 ^ 17) := by
      split <;> omega
    unfold srcPotential at hpot0; omega
  have hrenvInit : ResyncEnv h ctx.bdc ctx.rerr ctx.rmrk ctx.rs errs[0]!.numWarnings.toInt := by
    obtain ⟨dcs_, errs_, mrks_, srcs_, hgdc_, hszdc_, herrp_, hmrkp_, hsrcp_,
      hgerr_, hszerr_, hnw0_, _, hgmrk_, hszmrk_, hgsrc_, hszsrc_, hfill_⟩ := hrenv0
    have heEq : errs_ = errs := Option.some.inj (hgerr_.symm.trans hgerr)
    rw [heEq] at hgerr_ hszerr_ hnw0_
    exact ⟨dcs_, errs, mrks_, srcs_, hgdc_, hszdc_, herrp_, hmrkp_, hsrcp_,
      hgerr_, hszerr_, hnw0_, Int.le_refl _, hgmrk_, hszmrk_, hgsrc_, hszsrc_, hfill_⟩
  have hhas : HasDcPtrs ctx h := by
    obtain ⟨_dcs, _errs, _mrks, _srcs, hgdc1, _hsz1, _he1, hmrk1, hsrc1, _⟩ := hrenv0
    have hdEq : _dcs = dcs := Option.some.inj (hgdc1.symm.trans hgdc)
    rw [hdEq] at hsrc1 hmrk1
    exact ⟨dcs, hgdc, hszdc, hsrc1, hdc ▸ herrp, hmrk1⟩
  have hbib0Lt' : srcs[0]!.bytesInBuffer.toNat < 2 ^ 20 := by rw [← hs0Eq]; exact hbib0Lt
  have hbib0Live' : srcs[0]!.bytesInBuffer = 0 ∨
      LiveBytes h srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer.toNat := by
    rw [← hs0Eq]; exact hbib0Live
  obtain ⟨ret, h', hrun, _hb', hrenv', hret⟩ := next_marker_resync_ok (by omega : errs[0]!.numWarnings.toInt + 2 < 2 ^ 63)
    hrenvInit srcs[0]!.bytesInBuffer srcs[0]!.nextInputByte
    ⟨srcs, hgsrc, hszsrc, rfl, rfl⟩ hbib0Lt' hbib0Live'
  have hf := next_marker_frame hhas hrun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, dcbF, _, _, _, _, _⟩ := id hf
  obtain ⟨dcsF, hgdcF, _, hdceqF⟩ := dcbF ctx.bdc dcs hgdc hszdc rfl
  refine ⟨ret, h', hrun, ?_⟩
  rcases hret with hF | ⟨hT, dcs', srcs', hgdc', hszdc', hgsrc', hszsrc', hbibLt', hbibLive', hcase⟩
  · left; exact hF
  · have hdcEqF : dcs' = dcsF := Option.some.inj (hgdc'.symm.trans hgdcF)
    have hdisn : dcs'[0]!.inputScanNumber = _dc.inputScanNumber := by
      rw [hdcEqF, hdc]
      have h := congrArg C.JpegDecompressStruct.inputScanNumber hdceqF
      dsimp only at h; exact h
    right; refine ⟨hT, dcs', srcs', srcs, hgsrc, hszsrc, hgdc', hszdc', hgsrc', hszsrc', ?_⟩
    rcases hcase with ⟨hEoi, hnibE, hbibE, henvEoi⟩ | ⟨hbibDec, hsce, henvDec, hce⟩
    · left
      have hceof' : ∀ off, srcs'[0]!.nextInputByte = .ref .const_eof off →
          off + srcs'[0]!.bytesInBuffer.toNat ≤ 2 := by
        intro off hoff
        rw [hnibE] at hoff; cases hoff; rw [hbibE]; decide
      refine ⟨hEoi, ioState_of_nextMarkerFrame hs hf (resyncEnv_mono (by omega : errs[0]!.numWarnings.toInt + 2 ≤ nw + 2) henvEoi)
        ⟨srcs', hgsrc', hszsrc', hbibLt', hbibLive', hceof'⟩
        (fun errs' srcs'' hge' hsze' hgs' _ => ?_) (fun dcs'' srcs'' hgdc'' _ hgs'' _ => ?_)⟩
      · obtain ⟨_, errs2, _, _, _, _, _, _, _, hge2, _, _, hnw2, _, _, _, _, _⟩ := henvEoi
        have hee : errs' = errs2 := Option.some.inj (hge'.symm.trans hge2)
        have hss : srcs'' = srcs' := Option.some.inj (hgs'.symm.trans hgsrc')
        rw [hee, hss]
        have hite : isConstEofPtr srcs'[0]!.nextInputByte = true := by rw [hnibE]; rfl
        refine ⟨?_, hbd⟩
        unfold srcPotential
        rw [hite, hbibE]
        simp; omega
      · have hdd : dcs'' = dcs' := Option.some.inj (hgdc''.symm.trans hgdc')
        have hss : srcs'' = srcs' := Option.some.inj (hgs''.symm.trans hgsrc')
        rw [hdd, hss]
        have hite : isConstEofPtr srcs'[0]!.nextInputByte = true := by rw [hnibE]; rfl
        dsimp only [scanLimit] at hisnHi0 ⊢
        rw [hite, hEoi, hdisn]
        have hmne : (M_EOI == M_SOS) = false := by decide
        rw [hmne]
        simp only [Bool.false_eq_true, ↓reduceIte] at ⊢
        split at hisnHi0 <;> (try split at hisnHi0) <;> omega
    · by_cases hEoi : dcs'[0]!.unreadMarker = M_EOI
      · left
        have hceof' : ∀ off, srcs'[0]!.nextInputByte = .ref .const_eof off →
            off + srcs'[0]!.bytesInBuffer.toNat ≤ 2 := by
          intro off hoff
          obtain ⟨off0, hnib0, hsum⟩ := hsce.2 off hoff
          have := hceof0 off0 hnib0
          omega
        refine ⟨hEoi, ioState_of_nextMarkerFrame hs hf (resyncEnv_mono (by omega : errs[0]!.numWarnings.toInt + 1 ≤ nw + 2) henvDec)
          ⟨srcs', hgsrc', hszsrc', hbibLt', hbibLive', hceof'⟩
          (fun errs' srcs'' hge' hsze' hgs' _ => ?_) (fun dcs'' srcs'' hgdc'' _ hgs'' _ => ?_)⟩
        · obtain ⟨_, errs2, _, _, _, _, _, _, _, hge2, _, _, hnw2, _, _, _, _, _⟩ := henvDec
          have hee : errs' = errs2 := Option.some.inj (hge'.symm.trans hge2)
          have hss : srcs'' = srcs' := Option.some.inj (hgs'.symm.trans hgsrc')
          rw [hee, hss]
          refine ⟨?_, hbd⟩
          dsimp only [srcPotential] at hpot0 ⊢
          have hflag : isConstEofPtr srcs'[0]!.nextInputByte = isConstEofPtr srcs[0]!.nextInputByte := hsce.1
          rw [hflag]
          omega
        · have hdd : dcs'' = dcs' := Option.some.inj (hgdc''.symm.trans hgdc')
          have hss : srcs'' = srcs' := Option.some.inj (hgs''.symm.trans hgsrc')
          rw [hdd, hss]
          have hflag : isConstEofPtr srcs'[0]!.nextInputByte = isConstEofPtr srcs[0]!.nextInputByte := hsce.1
          dsimp only [scanLimit] at hisnHi0 ⊢
          rw [hflag, hEoi, hdisn]
          have hmne : (M_EOI == M_SOS) = false := by decide
          rw [hmne]
          by_cases hc : isConstEofPtr srcs[0]!.nextInputByte = true <;>
            simp only [hc, Bool.false_eq_true, ↓reduceIte] at hisnHi0 ⊢ <;>
            (try split at hisnHi0) <;> omega
      · right
        have hnibNotCeof : isConstEofPtr srcs[0]!.nextInputByte = false := by
          cases hn : srcs[0]!.nextInputByte with
          | ref r off =>
            cases r with
            | const_eof =>
              exact False.elim (hEoi (hce off hn (hceof0 off hn)))
            | _ => rfl
          | _ => rfl
        have hceof' : ∀ off, srcs'[0]!.nextInputByte = .ref .const_eof off →
            off + srcs'[0]!.bytesInBuffer.toNat ≤ 2 := by
          intro off hoff
          obtain ⟨off0, hnib0, hsum⟩ := hsce.2 off hoff
          have := hceof0 off0 hnib0
          omega
        have hflag : isConstEofPtr srcs'[0]!.nextInputByte = isConstEofPtr srcs[0]!.nextInputByte := hsce.1
        have hnwPlus : errs[0]!.numWarnings.toInt + 1 ≤ nw := by
          dsimp only [srcPotential] at hpot0
          split at hpot0 <;> omega
        refine ⟨hEoi, hs0Eq ▸ hnibNotCeof, ?_, ioState_of_nextMarkerFrame hs hf (resyncEnv_mono hnwPlus henvDec)
          ⟨srcs', hgsrc', hszsrc', hbibLt', hbibLive', hceof'⟩
          (fun errs' srcs'' hge' hsze' hgs' _ => ?_) (fun dcs'' srcs'' hgdc'' _ hgs'' _ => ?_)⟩
        · unfold srcRank; rw [hflag]; exact Nat.add_lt_add_right hbibDec _
        · obtain ⟨_, errs2, _, _, _, _, _, _, _, hge2, _, _, hnw2, _, _, _, _, _⟩ := henvDec
          have hee : errs' = errs2 := Option.some.inj (hge'.symm.trans hge2)
          have hss : srcs'' = srcs' := Option.some.inj (hgs'.symm.trans hgsrc')
          rw [hee, hss]
          refine ⟨?_, by omega⟩
          dsimp only [srcPotential] at hpot0 ⊢
          rw [hflag]
          omega
        · have hdd : dcs'' = dcs' := Option.some.inj (hgdc''.symm.trans hgdc')
          have hss : srcs'' = srcs' := Option.some.inj (hgs''.symm.trans hgsrc')
          rw [hdd, hss]
          have hflag' : isConstEofPtr srcs'[0]!.nextInputByte = false := hflag.trans hnibNotCeof
          dsimp only [scanLimit] at hisnHi0 ⊢
          rw [hnibNotCeof] at hisnHi0
          rw [hflag', hdisn]
          simp only [Bool.false_eq_true, ↓reduceIte] at hisnHi0 ⊢
          omega

end MozjpegF.Proof.JdmarkerRead

