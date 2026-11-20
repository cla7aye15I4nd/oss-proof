import MozjpegF.Proof.«jdmarker.c.read»

/-!
# Marker parsers and `read_markers` proofs (`jdmarker.c`, `MozjpegF`)

Proves safety, state preservation, and termination of every marker parser in `jdmarker.c`
(`first_marker`, `get_soi`, `get_dri`, `get_dac`, `get_dht`, `get_dqt`, `get_sof`, `get_sos`,
`examine_app0`, `examine_app14`, `get_interesting_appn`, `save_marker`, `skip_variable`,
`callMarkerParser`) and of `read_markers`.
-/

set_option autoImplicit false

namespace MozjpegF.Proof.JdmarkerParsers
open C MozjpegF.Spec Mozjpeg.Jerror Mozjpeg.JerrorH Mozjpeg.Jcomapi Mozjpeg.Jmemnobs
open Mozjpeg.Jmemmgr Mozjpeg.Jdatasrc Mozjpeg.Jdmarker Mozjpeg.JpeglibH Mozjpeg.MoreCfg
open MozjpegF.Proof.JdmarkerHelpers MozjpegF.Proof.JmemmgrHelpers MozjpegF.Proof.JdmarkerRead

/-! ## Generic `forIn`, `Ptr`, and `CurValid` helpers -/

private theorem set0_bang {α : Type} [Inhabited α] (a : Array α) (h : 0 < a.size) (v : α) :
    (a.set! 0 v)[0]! = v := by
  simp only [Array.set!, Array.setIfInBounds, h, ↓reduceDIte]
  rw [getElem!_pos _ 0 (by simp [h])]
  exact Array.getElem_set_self h

private theorem set_bang_self {α : Type} [Inhabited α] (a : Array α) {i : Nat} (h : i < a.size) (v : α) :
    (a.set! i v)[i]! = v := by
  simp only [Array.set!, Array.setIfInBounds, h, ↓reduceDIte]
  rw [getElem!_pos _ i (by simp [h])]
  exact Array.getElem_set_self h

private theorem set_bang_ne {α : Type} [Inhabited α] (a : Array α) {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (hne : i ≠ j) (v : α) :
    (a.set! j v)[i]! = a[i]! := by
  simp only [Array.set!, Array.setIfInBounds, hj, ↓reduceDIte]
  rw [getElem!_pos _ i (by simp [hi]), getElem!_pos _ i hi]
  simp [Array.getElem_set, hne.symm]

theorem forIn_range_idx_inv {σ : Type} (Inv : Nat → σ → C.Heap → Prop)
    (step : Nat → σ → C.M (ForInStep σ))
    (n : Nat)
    (hstep : ∀ i < n, ∀ s h, Inv i s h →
      ∃ st h', C.run (step i s) h = .ok (st, h') ∧
        match st with
        | .done s' => Inv n s' h'
        | .yield s' => Inv (i + 1) s' h') :
    ∀ k ≤ n, ∀ s h, Inv k s h →
      ∃ s' h', C.run (forIn (List.range' k (n - k)) s step) h = .ok (s', h') ∧ Inv n s' h' := by
  intro k hk s h hinv
  have hrec : ∀ d k, k + d = n → ∀ s h, Inv k s h →
      ∃ s' h', C.run (forIn (List.range' k d) s step) h = .ok (s', h') ∧ Inv n s' h' := by
    intro d
    induction d with
    | zero =>
      intro k hsum s h hinv
      have hkn : k = n := by omega
      rw [hkn] at hinv
      exact ⟨s, h, rfl, hinv⟩
    | succ d ih =>
      intro k hsum s h hinv
      have hkn : k < n := by omega
      obtain ⟨st, h1, hrun1, hinv1⟩ := hstep k hkn s h hinv
      rw [List.range'_succ, List.forIn_cons, C.run_bind, hrun1]
      dsimp only
      cases st with
      | done s1 => exact ⟨s1, h1, rfl, hinv1⟩
      | yield s1 => exact ih (k + 1) (by omega) s1 h1 hinv1
  simpa [Nat.add_sub_of_le hk] using hrec (n - k) k (Nat.add_sub_of_le hk) s h hinv

theorem forIn_range_inv {σ : Type} (Inv : Nat → σ → C.Heap → Prop)
    (step : Nat → σ → C.M (ForInStep σ))
    (n : Nat)
    (hstep : ∀ i < n, ∀ s h, Inv i s h →
      ∃ st h', C.run (step i s) h = .ok (st, h') ∧
        match st with
        | .done s' => Inv n s' h'
        | .yield s' => Inv (i + 1) s' h')
    {s : σ} {h : C.Heap} (hinv : Inv 0 s h) :
    ∃ s' h', C.run (forIn (List.range n) s step) h = .ok (s', h') ∧ Inv n s' h' := by
  rw [List.range_eq_range']
  simpa using forIn_range_idx_inv Inv step n hstep 0 (Nat.zero_le n) s h hinv

theorem ptr_load_ok {R T : Type} [C.Space C.Heap R T] [Inhabited T]
    {r : R} {off : Nat} {h : C.Heap} {xs : Array T}
    (hg : C.Space.get h r = some xs) (hoff : off < xs.size) :
    C.run (C.Ptr.load (.ref r off)) h = .ok (xs[off]!, h) := by
  simp only [C.run, C.Ptr.load, hg, hoff, ↓reduceDIte, getElem!_pos xs off hoff]

theorem ptr_store_ok {R T : Type} [C.Space C.Heap R T]
    {r : R} {off : Nat} {v : T} {h : C.Heap} {xs : Array T}
    (hg : C.Space.get h r = some xs) (hro : C.Space.ro h r = false) (hoff : off < xs.size) :
    C.run (C.Ptr.store (.ref r off) v) h = .ok ((), C.Space.put h r (xs.set! off v)) := by
  simp only [C.run, C.Ptr.store, hg, hro, Bool.false_eq_true, ↓reduceIte, hoff,
    C.Space.modify_eq h r xs (fun a => a.set! off v) hg]

theorem ptr_add_ok {R T : Type} [C.Space C.Heap R T]
    {r : R} {off : Nat} {k : Int} {h : C.Heap} {xs : Array T}
    (hg : C.Space.get h r = some xs)
    (h1 : off ≤ xs.size) (h2 : 0 ≤ (off : Int) + k) (h3 : (off : Int) + k ≤ (xs.size : Int)) :
    C.run (C.Ptr.add (.ref r off) k) h = .ok (.ref r ((off : Int) + k).toNat, h) := by
  simp only [C.run, C.Ptr.add, hg, h1, h2, h3, and_self, ↓reduceIte]

def CurValid (h : C.Heap) (nib : C.BPtr) (bib : UInt64) : Prop :=
  bib.toNat < 2 ^ 20 ∧
  (bib = 0 ∨ LiveBytes h nib bib.toNat) ∧
  (∀ off, nib = .ref .const_eof off → off + bib.toNat ≤ 2)

theorem curValid_bytes_irrel {h h' : C.Heap} {nib : C.BPtr} {bib : UInt64}
    (hb : h'.bytes = h.bytes) (hc : h'.consts = h.consts)
    (hcv : CurValid h nib bib) : CurValid h' nib bib := by
  rcases hcv with ⟨h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rcases h2 with rfl | ⟨r, off, data, hp, hg, hsz⟩
  · left; rfl
  · right
    have hg' : C.Space.get h' r = some data := by
      cases r with
      | heap b => simp only [C.Space.get, C.Heap.getBytes] at hg ⊢; rw [hb]; exact hg
      | const b => simp only [C.Space.get, C.Heap.getBytes] at hg ⊢; rw [hc]; exact hg
      | const_eof | str _ => exact hg
    exact ⟨r, off, data, hp, hg', hsz⟩

theorem curValid_set_byte {h : C.Heap} {b : Nat} {arr : Array UInt8} {idx : Nat} {v : UInt8}
    {nib : C.BPtr} {bib : UInt64}
    (hgb : h.bytes b = some arr) (hcv : CurValid h nib bib) :
    CurValid { h with bytes := C.upd h.bytes b (some (arr.set! idx v)) } nib bib := by
  rcases hcv with ⟨h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rcases h2 with rfl | ⟨r, off, data, hp, hg, hsz⟩
  · left; rfl
  · right
    cases r with
    | heap b' =>
      by_cases heq : b' = b
      · subst heq
        simp only [C.Space.get, C.Heap.getBytes] at hg
        have heqA : data = arr := Option.some.inj (hg.symm.trans hgb)
        refine ⟨.heap b', off, arr.set! idx v, hp, ?_, ?_⟩
        · simp [C.Space.get, C.Heap.getBytes, C.upd_same]
        · rw [Array.size_set!]; exact heqA ▸ hsz
      · refine ⟨.heap b', off, data, hp, ?_, hsz⟩
        simp only [C.Space.get, C.Heap.getBytes, C.upd_ne _ _ _ _ heq]
        exact hg
    | const _ | const_eof | str _ =>
      exact ⟨_, off, data, hp, hg, hsz⟩

theorem curValid_alloc_byte {h : C.Heap} {b : Nat} {arr : Array UInt8}
    {nib : C.BPtr} {bib : UInt64}
    (hnb : h.bytes b = none) (hcv : CurValid h nib bib) :
    CurValid { h with bytes := C.upd h.bytes b (some arr) } nib bib := by
  rcases hcv with ⟨h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rcases h2 with rfl | ⟨r, off, data, hp, hg, hsz⟩
  · left; rfl
  · right
    cases r with
    | heap b' =>
      have hne : b' ≠ b := by
        intro heq; subst heq; simp only [C.Space.get, C.Heap.getBytes] at hg; rw [hnb] at hg; cases hg
      exact ⟨.heap b', off, data, hp, by simp only [C.Space.get, C.Heap.getBytes, C.upd_ne _ _ _ _ hne]; exact hg, hsz⟩
    | const _ | const_eof | str _ =>
      exact ⟨_, off, data, hp, hg, hsz⟩

theorem curValid_advance {h : C.Heap} {nib : C.BPtr} {bib : UInt64} (k : Nat)
    (hkpos : 0 < k) (hk : k ≤ bib.toNat) (hcv : CurValid h nib bib) :
    ∃ nib',
      C.run (C.Ptr.add nib (Int.ofNat k)) h = .ok (nib', h) ∧
      CurValid h nib' (bib - UInt64.ofNat k) ∧
      (isConstEofPtr nib' = isConstEofPtr nib) := by
  rcases hcv with ⟨hlt, hlive, hce⟩
  have hbibPos : bib ≠ 0 := fun h0 => by rw [h0] at hk; have hz : (0 : UInt64).toNat = 0 := rfl; omega
  rcases hlive with rfl | ⟨r, off, data, hp, hg, hsz⟩
  · exact False.elim (hbibPos rfl)
  · have hkInt : Int.ofNat k = (k : Int) := rfl
    have haddBounds : off ≤ data.size ∧ 0 ≤ (off : Int) + (k : Int) ∧
        (off : Int) + (k : Int) ≤ (data.size : Int) := by omega
    have hadd := ptr_add_ok (r := r) (off := off) (k := (k : Int)) hg
      haddBounds.1 haddBounds.2.1 haddBounds.2.2
    have hkNat : (UInt64.ofNat k).toNat = k := by
      change k % 2 ^ 64 = k; exact Nat.mod_eq_of_lt (by omega)
    have hk64 : UInt64.ofNat k ≤ bib := by
      rw [UInt64.le_iff_toNat_le, hkNat]; exact hk
    have hsub : (bib - UInt64.ofNat k).toNat = bib.toNat - k := by
      rw [UInt64.toNat_sub_of_le bib _ hk64, hkNat]
    have hnewOff : ((off : Int) + (k : Int)).toNat = off + k := by omega
    refine ⟨.ref r ((off : Int) + (k : Int)).toNat, hp ▸ hkInt ▸ hadd, ⟨by omega, ?_, ?_⟩, ?_⟩
    · by_cases hrem : bib - UInt64.ofNat k = 0
      · left; exact hrem
      · right; exact ⟨r, ((off : Int) + (k : Int)).toNat, data, rfl, hg, by omega⟩
    · intro off' hoff'
      cases hoff'
      have hce0 := hce off hp
      omega
    · cases r <;> cases hp <;> rfl

/-! ## Persistent parser environment -/

/-- Parser-level invariant capturing the persistent `IoState` graph and bounds during marker parsing. -/
def ParserEnv (ctx : IoCtx) (h : C.Heap) : Prop :=
  ValidDecompCore h (.ref (.decomp ctx.bdc) 0) ∧
  FreshNextBlk h ∧
  ∃ dcs dc errs mems masters ics mrks srcs,
    C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
    dc.err = .ref ctx.rerr 0 ∧ C.Space.get h ctx.rerr = some errs ∧ 0 < errs.size ∧
    (errs[0]!).resetErrorMgr = .fn "reset_error_mgr" ∧
    0 ≤ (errs[0]!).numWarnings.toInt ∧
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
    CurValid h (srcs[0]!).nextInputByte (srcs[0]!).bytesInBuffer ∧
    ((mrks[0]!).curMarker = .null ∨
      ∃ rsm off sms sm,
        (mrks[0]!).curMarker = .ref rsm off ∧ C.Space.get h rsm = some sms ∧ off < sms.size ∧
        sm = sms[off]! ∧ sm.dataLength.toNat ≤ 65535 ∧ sm.originalLength.toNat ≤ 65535 ∧
        WritableBytes h sm.data sm.dataLength.toNat ∧
        (mrks[0]!).bytesRead ≤ sm.dataLength) ∧
    (dc.markerList = .null ∨ (masters[0]!).markerListEnd = .null ∨
      ∃ rsm off sms,
        (masters[0]!).markerListEnd = .ref rsm off ∧ C.Space.get h rsm = some sms ∧ off < sms.size) ∧
    ((mrks[0]!).sawSOF ≠ 0 → dc.compInfo ≠ .null) ∧
    (dc.compInfo ≠ .null → 0 ≤ dc.numComponents.toInt ∧
      LiveCompArray h dc.compInfo dc.numComponents.toInt.toNat) ∧
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
    0 ≤ dc.inputScanNumber.toInt

theorem parserEnv_of_ioState {ctx : IoCtx} {h : C.Heap} {nw : Int} (hs : IoState ctx h nw) :
    ParserEnv ctx h := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0, _hpot, _hbd,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hbibLt, hbibLive, hceof,
    hcurm, hmlEnd, hcomp, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0, _hscan⟩ := hs
  refine ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, ⟨hbibLt, hbibLive, hceof⟩,
    hcurm, hmlEnd, ?_, ?_, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  · intro hsaw
    rcases hcomp with ⟨_, h0⟩ | ⟨hne, _⟩
    · exact False.elim (hsaw h0)
    · exact hne
  · intro hne
    rcases hcomp with ⟨hnull, _⟩ | ⟨_, _, hnc0, hlive⟩
    · exact False.elim (hne hnull)
    · exact ⟨hnc0, hlive⟩

theorem ioState_of_parserEnv {ctx : IoCtx} {h : C.Heap} {nw : Int}
    (hp : ParserEnv ctx h)
    (hcomp : ∀ dcs mrks,
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
      (dcs[0]!).compInfo = .null ∧ (mrks[0]!).sawSOF = 0 ∨
      (dcs[0]!).compInfo ≠ .null ∧ (mrks[0]!).sawSOF ≠ 0)
    (hpot : ∀ errs srcs,
      C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
      srcPotential errs[0]! srcs[0]! ≤ nw ∧ nw + 2 ^ 17 < 2 ^ 63)
    (hscan : ∀ dcs srcs,
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
      scanLimit dcs[0]! srcs[0]! < 2 ^ 31) :
    IoState ctx h nw := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, ⟨hbibLt, hbibLive, hceof⟩,
    hcurm, hmlEnd, _hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  obtain ⟨hpotLe, hnwBd⟩ := hpot errs srcs hgerr hszerr hgsrc hszsrc
  have hscanLim := hscan dcs srcs hgdc hszdc hgsrc hszsrc
  refine ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0, hpotLe, hnwBd,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hbibLt, hbibLive, hceof,
    hcurm, hmlEnd, ?_, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0, hdc ▸ hscanLim⟩
  rcases hcomp dcs mrks hgdc hszdc hgmrk hszmrk with ⟨hnull, hsaw0⟩ | ⟨hne, hsawNe⟩
  · left; exact ⟨hdc ▸ hnull, hsaw0⟩
  · right
    obtain ⟨hnc0, hlive⟩ := hcompLive (hdc ▸ hne)
    exact ⟨hdc ▸ hne, hsawNe, hnc0, hlive⟩

/-! ## Compact single-space mutation preservation for `ParserEnv` -/

theorem validDecompCore_of_sameGraph {h h' : C.Heap} {bdc : Nat}
    (hc : ValidDecompCore h (.ref (.decomp bdc) 0))
    (h1 : ∃ dcs dc dcs' dc', C.Space.get h (C.DecompRef.decomp bdc) = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
      C.Space.get h' (C.DecompRef.decomp bdc) = some dcs' ∧ 0 < dcs'.size ∧ dc' = dcs'[0]! ∧
      dc'.err = dc.err ∧ dc'.mem = dc.mem ∧ dc'.master = dc.master ∧
      dc'.inputctl = dc.inputctl ∧ dc'.marker = dc.marker)
    (hErr : ∀ (r : C.ErrRef) a, C.Space.get h r = some a → 0 < a.size → ∃ a', C.Space.get h' r = some a' ∧ 0 < a'.size)
    (hMas : ∀ (r : C.MasterRef) a, C.Space.get h r = some a → 0 < a.size → ∃ a', C.Space.get h' r = some a' ∧ 0 < a'.size)
    (hIc : ∀ (r : C.InputCtlRef) a, C.Space.get h r = some a → 0 < a.size → ∃ a', C.Space.get h' r = some a' ∧ 0 < a'.size)
    (hMrk : ∀ (r : C.MarkerRef) a, C.Space.get h r = some a → 0 < a.size → ∃ a', C.Space.get h' r = some a' ∧ 0 < a'.size)
    (hMem : ∀ (rmems : C.MemRef) mems, C.Space.get h rmems = some mems → 0 < mems.size →
      2 ≤ mems[0]!.poolAllocs.size →
      ∃ mems', C.Space.get h' rmems = some mems' ∧ 0 < mems'.size ∧
        2 ≤ mems'[0]!.poolAllocs.size ∧ mems'[0]!.poolAllocs[1]!.masters = mems[0]!.poolAllocs[1]!.masters) :
    ValidDecompCore h' (.ref (.decomp bdc) 0) := by
  obtain ⟨rc, dcs0, dc0, rm, mems0, rmas, masters0, ric, ics0, rmrk, mrks0,
    hrc, hgdc0, hszdc0, hdc0, herr, hmemp, hgmem0, hszmem0,
    hmasp, hgmas0, hszmas0, hicp, hgic0, hszic0, hmrkp, hgmrk0, hszmrk0, hpaSz, hnb⟩ := hc
  cases hrc
  obtain ⟨dcs, dc, dcs', dc', hgdc, _, hdc, hgdc', hszdc', hdc', ke, km, kma, kic, kmrk⟩ := h1
  have hdEq : dcs = dcs0 := Option.some.inj (hgdc.symm.trans hgdc0)
  have hdcEq : dc = dc0 := hdc.trans (hdEq ▸ hdc0.symm)
  obtain ⟨rerr, errs0, herrp, hgerr0, hszerr0⟩ := herr
  obtain ⟨errs', hgerr', hszerr'⟩ := hErr rerr errs0 hgerr0 hszerr0
  obtain ⟨mems', hgmem', hszmem', hpaSz', hpaMas'⟩ := hMem rm mems0 hgmem0 hszmem0 hpaSz
  obtain ⟨masters', hgmas', hszmas'⟩ := hMas rmas masters0 hgmas0 hszmas0
  obtain ⟨ics', hgic', hszic'⟩ := hIc ric ics0 hgic0 hszic0
  obtain ⟨mrks', hgmrk', hszmrk'⟩ := hMrk rmrk mrks0 hgmrk0 hszmrk0
  refine ⟨.decomp bdc, dcs', dc', rm, mems', rmas, masters', ric, ics', rmrk, mrks',
    rfl, hgdc', hszdc', hdc', ⟨rerr, errs', ke.trans (hdcEq ▸ herrp), hgerr', hszerr'⟩,
    km.trans (hdcEq ▸ hmemp), hgmem', hszmem',
    kma.trans (hdcEq ▸ hmasp), hgmas', hszmas',
    kic.trans (hdcEq ▸ hicp), hgic', hszic',
    kmrk.trans (hdcEq ▸ hmrkp), hgmrk', hszmrk', hpaSz', ?_⟩
  rw [hpaMas']; exact hnb

theorem parserEnv_put_dc {ctx : IoCtx} {h : C.Heap} {dcs : Array C.JpegDecompressStruct}
    {dc' : C.JpegDecompressStruct}
    (hp : ParserEnv ctx h) (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (kerr : dc'.err = dcs[0]!.err) (kmem : dc'.mem = dcs[0]!.mem) (kmas : dc'.master = dcs[0]!.master)
    (kic : dc'.inputctl = dcs[0]!.inputctl) (kmrk : dc'.marker = dcs[0]!.marker) (ksrc : dc'.src = dcs[0]!.src)
    (kml : dc'.markerList = dcs[0]!.markerList ∨ dc'.markerList = .null ∨
      ∀ masters, C.Space.get h ctx.rmas = some masters → 0 < masters.size →
        masters[0]!.markerListEnd = .null ∨
        ∃ rsm off sms, masters[0]!.markerListEnd = .ref rsm off ∧ C.Space.get h rsm = some sms ∧ off < sms.size)
    (hcomp : dc'.compInfo = dcs[0]!.compInfo ∧ dc'.numComponents = dcs[0]!.numComponents ∨
      dc'.compInfo = .null ∨ 0 ≤ dc'.numComponents.toInt ∧ LiveCompArray h dc'.compInfo dc'.numComponents.toInt.toNat)
    (hqt : dc'.quantTblPtrs.size = 4 ∧
      (∀ i < 4, dc'.quantTblPtrs[i]! = .null ∨
        ∃ rq off qs, dc'.quantTblPtrs[i]! = .ref rq off ∧ C.Space.get h rq = some qs ∧ off < qs.size))
    (hdh : dc'.dcHuffTblPtrs.size = 4 ∧
      (∀ i < 4, dc'.dcHuffTblPtrs[i]! = .null ∨
        ∃ rh off hs, dc'.dcHuffTblPtrs[i]! = .ref rh off ∧ C.Space.get h rh = some hs ∧ off < hs.size))
    (hah : dc'.acHuffTblPtrs.size = 4 ∧
      (∀ i < 4, dc'.acHuffTblPtrs[i]! = .null ∨
        ∃ rh off hs, dc'.acHuffTblPtrs[i]! = .ref rh off ∧ C.Space.get h rh = some hs ∧ off < hs.size))
    (hcc : dc'.curCompInfo.size = 4)
    (hisn : 0 ≤ dc'.inputScanNumber.toInt)
    (hsaw : ∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
      mrks[0]!.sawSOF ≠ 0 → dc'.compInfo ≠ .null) :
    ParserEnv ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) := by
  obtain ⟨hcore, hfr, dcs0, dc0, errs, mems, masters, ics, mrks, srcs,
    hgdc0, hszdc0, hdc0, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, _hsawOld, hcompLiveOld, _hqtSz, _hqt, _hdhSz, _hdh, _hahSz, _hah, _hccSz, _hisn0⟩ := hp
  have hdEq : dcs = dcs0 := Option.some.inj (hg.symm.trans hgdc0)
  subst hdEq
  let h' := C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')
  have hg' : C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some (dcs.set! 0 dc') := by
    simp [h', C.Space.get, C.Space.put, C.upd_same]
  have hsz' : 0 < (dcs.set! 0 dc').size := by simpa using hsz
  have h0' : (dcs.set! 0 dc')[0]! = dc' := set0_bang dcs hsz dc'
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · refine ⟨dcs, dcs[0]!, dcs.set! 0 dc', dc', hgdc0, hszdc0, rfl, hg', hsz', h0'.symm,
        kerr, kmem, kmas, kic, kmrk⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ ms hgm hszm hpa; exact ⟨ms, hgm, hszm, hpa, rfl⟩
  refine ⟨hcore', hfr, dcs.set! 0 dc', dc', errs, mems, masters, ics, mrks, srcs,
    hg', hsz', h0'.symm, ?_, hgerr, hszerr, hrem, hnw0,
    ?_, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    ?_, hgmas, hszmas, ?_, hgic, hszic, hric, hci,
    ?_, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    ?_, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, ?_, hsaw mrks hgmrk hszmrk, ?_, hqt.1, hqt.2, hdh.1, hdh.2, hah.1, hah.2, hcc, hisn⟩
  · rw [kerr, ← hdc0]; exact herrp
  · rw [kmem, ← hdc0]; exact hmemp
  · rw [kmas, ← hdc0]; exact hmasp
  · rw [kic, ← hdc0]; exact hicp
  · rw [kmrk, ← hdc0]; exact hmrkp
  · rw [ksrc, ← hdc0]; exact hsrcp
  · rcases kml with kml1 | kml2 | kml3
    · rw [kml1, ← hdc0]; exact hmlEnd
    · left; exact kml2
    · right; exact kml3 masters hgmas hszmas
  · intro hne
    rcases hcomp with ⟨hc1, hnc1⟩ | hnull | ⟨hnc0, hlive⟩
    · have hc2 : dc0.compInfo ≠ .null := by rw [hdc0, ← hc1]; exact hne
      obtain ⟨hn0, hlv⟩ := hcompLiveOld hc2
      refine ⟨by rw [hnc1, ← hdc0]; exact hn0, ?_⟩
      rcases hlv with ⟨r1, cs1, hp1, hg1, hsz1⟩
      exact ⟨r1, cs1, by rw [hc1, ← hdc0]; exact hp1, hg1, by rw [hnc1, ← hdc0]; exact hsz1⟩
    · exact False.elim (hne hnull)
    · exact ⟨hnc0, hlive⟩

theorem parserEnv_put_mrk {ctx : IoCtx} {h : C.Heap} {mrks : Array C.JpegMarkerReader}
    {mrk' : C.JpegMarkerReader}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.rmrk = some mrks) (hsz : 0 < mrks.size)
    (hrm : mrk'.readMarkers = mrks[0]!.readMarkers)
    (hrmr : mrk'.resetMarkerReader = mrks[0]!.resetMarkerReader)
    (hpcom : mrk'.processCOM = mrks[0]!.processCOM)
    (hpapp : mrk'.processAPPn = mrks[0]!.processAPPn)
    (hllSz : mrk'.lengthLimitAPPn.size = 16)
    (hcurm : mrk'.curMarker = .null ∨
      ∃ rsm off sms sm,
        mrk'.curMarker = .ref rsm off ∧ C.Space.get h rsm = some sms ∧ off < sms.size ∧
        sm = sms[off]! ∧ sm.dataLength.toNat ≤ 65535 ∧ sm.originalLength.toNat ≤ 65535 ∧
        WritableBytes h sm.data sm.dataLength.toNat ∧
        mrk'.bytesRead ≤ sm.dataLength)
    (hsaw : ∀ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      mrk'.sawSOF ≠ 0 → dcs[0]!.compInfo ≠ .null) :
    ParserEnv ctx (C.Space.put h ctx.rmrk (mrks.set! 0 mrk')) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks0, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk0, hszmrk0, hrm0, hrmr0, hpcom0, hpappSz0, hpapp0, _hllSz0,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    _hcurm0, hmlEnd, _hsawOld, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hmEq : mrks = mrks0 := Option.some.inj (hg.symm.trans hgmrk0)
  subst hmEq
  let h' := C.Space.put h ctx.rmrk (mrks.set! 0 mrk')
  have hg' : C.Space.get h' ctx.rmrk = some (mrks.set! 0 mrk') := by
    rcases hr : ctx.rmrk with ⟨bm⟩
    simp [h', C.Space.get, C.Space.put, hr, C.upd_same]
  have hsz' : 0 < (mrks.set! 0 mrk').size := by simpa using hsz
  have h0' : (mrks.set! 0 mrk')[0]! = mrk' := set0_bang mrks hsz mrk'
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · exact ⟨dcs, dc, dcs, dc, hgdc, hszdc, hdc, hgdc, hszdc, hdc, rfl, rfl, rfl, rfl, rfl⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro r a hga hsza
      rcases r with ⟨bm⟩
      rcases hr : ctx.rmrk with ⟨bm0⟩
      by_cases heq : bm = bm0
      · subst heq; exact ⟨mrks.set! 0 mrk', by rw [← hr]; exact hg', hsz'⟩
      · exact ⟨a, by simp only [h', C.Space.get, C.Space.put, hr, C.upd_ne _ _ _ _ heq] at hga ⊢; exact hga, hsza⟩
    · intro _ ms hgm hszm hpa; exact ⟨ms, hgm, hszm, hpa, rfl⟩
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, hma, ?_, hic, hsr, hcp, hq, hhu, hsm⟩
    rcases hr : ctx.rmrk with ⟨bm0⟩
    by_cases heq : k = bm0
    · subst heq; simp only [C.Space.get, hr] at hg; rw [hmr] at hg; cases hg
    · simp only [h', C.Space.put, hr, C.upd_ne _ _ _ _ heq]; exact hmr
  refine ⟨hcore', hfr', dcs, dc, errs, mems, masters, ics, mrks.set! 0 mrk', srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hg', hsz', ?_, ?_, ?_, ?_, ?_, ?_,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    ?_, hmlEnd, ?_, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  · rw [h0', hrm]; exact hrm0
  · rw [h0', hrmr]; exact hrmr0
  · rw [h0', hpcom]; exact hpcom0
  · rw [h0', hpapp]; exact hpappSz0
  · intro i hi; rw [h0', hpapp]; exact hpapp0 i hi
  · rw [h0']; exact hllSz
  · rw [h0']
    rcases hcurm with hnull | ⟨rsm, off, sms, sm, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · left; exact hnull
    · right; exact ⟨rsm, off, sms, sm, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · rw [h0', hdc]; exact hsaw dcs hgdc hszdc

theorem parserEnv_put_err {ctx : IoCtx} {h : C.Heap} {errs : Array C.JpegErrorMgr}
    {err' : C.JpegErrorMgr}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.rerr = some errs) (hsz : 0 < errs.size)
    (hrem : err'.resetErrorMgr = errs[0]!.resetErrorMgr)
    (hnw0 : 0 ≤ err'.numWarnings.toInt) :
    ParserEnv ctx (C.Space.put h ctx.rerr (errs.set! 0 err')) := by
  obtain ⟨hcore, hfr, dcs, dc, errs0, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr0, hszerr0, hrem0, _hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have heEq : errs = errs0 := Option.some.inj (hg.symm.trans hgerr0)
  subst heEq
  let h' := C.Space.put h ctx.rerr (errs.set! 0 err')
  have hg' : C.Space.get h' ctx.rerr = some (errs.set! 0 err') := by
    rcases hr : ctx.rerr with ⟨be⟩; simp [h', C.Space.get, C.Space.put, hr, C.upd_same]
  have hsz' : 0 < (errs.set! 0 err').size := by simpa using hsz
  have h0' : (errs.set! 0 err')[0]! = err' := set0_bang errs hsz err'
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · exact ⟨dcs, dc, dcs, dc, hgdc, hszdc, hdc, hgdc, hszdc, hdc, rfl, rfl, rfl, rfl, rfl⟩
    · intro r a hga hsza
      rcases r with ⟨be⟩
      rcases hr : ctx.rerr with ⟨be0⟩
      by_cases heq : be = be0
      · subst heq; exact ⟨errs.set! 0 err', by rw [← hr]; exact hg', hsz'⟩
      · exact ⟨a, by simp only [h', C.Space.get, C.Space.put, hr, C.upd_ne _ _ _ _ heq] at hga ⊢; exact hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ ms hgm hszm hpa; exact ⟨ms, hgm, hszm, hpa, rfl⟩
  refine ⟨hcore', hfr, dcs, dc, errs.set! 0 err', mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hg', hsz', ?_, ?_,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  · rw [h0', hrem]; exact hrem0
  · rw [h0']; exact hnw0

theorem parserEnv_put_src {ctx : IoCtx} {h : C.Heap} {srcs : Array C.JpegSourceMgr}
    {src' : C.JpegSourceMgr}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.rs = some srcs) (hsz : 0 < srcs.size)
    (his : src'.initSource = srcs[0]!.initSource)
    (hts : src'.termSource = srcs[0]!.termSource)
    (hsip : src'.skipInputData = srcs[0]!.skipInputData)
    (hrtr : src'.resyncToRestart = srcs[0]!.resyncToRestart)
    (hfill : src'.fillInputBuffer = srcs[0]!.fillInputBuffer)
    (hcurv : CurValid h src'.nextInputByte src'.bytesInBuffer) :
    ParserEnv ctx (C.Space.put h ctx.rs (srcs.set! 0 src')) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs0,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc0, hszsrc0, his0, hts0, hsip0, hrtr0, hfill0, _hcurv0,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hsEq : srcs = srcs0 := Option.some.inj (hg.symm.trans hgsrc0)
  subst hsEq
  let h' := C.Space.put h ctx.rs (srcs.set! 0 src')
  have hg' : C.Space.get h' ctx.rs = some (srcs.set! 0 src') := by
    rcases hr : ctx.rs with ⟨bs⟩; simp [h', C.Space.get, C.Space.put, hr, C.upd_same]
  have hsz' : 0 < (srcs.set! 0 src').size := by simpa using hsz
  have h0' : (srcs.set! 0 src')[0]! = src' := set0_bang srcs hsz src'
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · exact ⟨dcs, dc, dcs, dc, hgdc, hszdc, hdc, hgdc, hszdc, hdc, rfl, rfl, rfl, rfl, rfl⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ ms hgm hszm hpa; exact ⟨ms, hgm, hszm, hpa, rfl⟩
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, hma, hmr, hic, ?_, hcp, hq, hhu, hsm⟩
    rcases hr : ctx.rs with ⟨bs0⟩
    by_cases heq : k = bs0
    · subst heq; simp only [C.Space.get, hr] at hg; rw [hsr] at hg; cases hg
    · simp only [h', C.Space.put, hr, C.upd_ne _ _ _ _ heq]; exact hsr
  refine ⟨hcore', hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs.set! 0 src',
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hg', hsz', ?_, ?_, ?_, ?_, ?_, ?_,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  · rw [h0', his]; exact his0
  · rw [h0', hts]; exact hts0
  · rw [h0', hsip]; exact hsip0
  · rw [h0', hrtr]; exact hrtr0
  · rw [h0', hfill, hsip]; exact hfill0
  · rw [h0']; exact hcurv

theorem parserEnv_put_mst {ctx : IoCtx} {h : C.Heap} {masters : Array C.JpegDecompMaster}
    {mst' : C.JpegDecompMaster}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.rmas = some masters) (hsz : 0 < masters.size)
    (hml : mst'.markerListEnd = masters[0]!.markerListEnd ∨ mst'.markerListEnd = .null ∨
      ∃ rsm off sms, mst'.markerListEnd = .ref rsm off ∧ C.Space.get h rsm = some sms ∧ off < sms.size) :
    ParserEnv ctx (C.Space.put h ctx.rmas (masters.set! 0 mst')) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters0, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas0, hszmas0, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hmEq : masters = masters0 := Option.some.inj (hg.symm.trans hgmas0)
  subst hmEq
  let h' := C.Space.put h ctx.rmas (masters.set! 0 mst')
  have hg' : C.Space.get h' ctx.rmas = some (masters.set! 0 mst') := by
    rcases hr : ctx.rmas with ⟨bm⟩; simp [h', C.Space.get, C.Space.put, hr, C.upd_same]
  have hsz' : 0 < (masters.set! 0 mst').size := by simpa using hsz
  have h0' : (masters.set! 0 mst')[0]! = mst' := set0_bang masters hsz mst'
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · exact ⟨dcs, dc, dcs, dc, hgdc, hszdc, hdc, hgdc, hszdc, hdc, rfl, rfl, rfl, rfl, rfl⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro r a hga hsza
      rcases r with ⟨bm⟩
      rcases hr : ctx.rmas with ⟨bm0⟩
      by_cases heq : bm = bm0
      · subst heq; exact ⟨masters.set! 0 mst', by rw [← hr]; exact hg', hsz'⟩
      · exact ⟨a, by simp only [h', C.Space.get, C.Space.put, hr, C.upd_ne _ _ _ _ heq] at hga ⊢; exact hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ ms hgm hszm hpa; exact ⟨ms, hgm, hszm, hpa, rfl⟩
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, ?_, hmr, hic, hsr, hcp, hq, hhu, hsm⟩
    rcases hr : ctx.rmas with ⟨bm0⟩
    by_cases heq : k = bm0
    · subst heq; simp only [C.Space.get, hr] at hg; rw [hma] at hg; cases hg
    · simp only [h', C.Space.put, hr, C.upd_ne _ _ _ _ heq]; exact hma
  refine ⟨hcore', hfr', dcs, dc, errs, mems, masters.set! 0 mst', ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hg', hsz', hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, ?_, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  rcases hml with hm1 | hm2 | hm3
  · rw [h0', hm1]; exact hmlEnd
  · right; left; rw [h0']; exact hm2
  · right; right; rw [h0']; exact hm3

theorem parserEnv_put_comp {ctx : IoCtx} {h : C.Heap} {rc : C.CompRef} {cs : Array C.JpegCompInfo}
    {off : Nat} {c' : C.JpegCompInfo}
    (hp : ParserEnv ctx h) (hg : C.Space.get h rc = some cs) :
    ParserEnv ctx (C.Space.put h rc (cs.set! off c')) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  let h' := C.Space.put h rc (cs.set! off c')
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, hma, hmr, hic, hsr, ?_, hq, hhu, hsm⟩
    rcases rc with ⟨b⟩
    by_cases heq : k = b
    · subst heq; simp only [C.Space.get] at hg; rw [hcp] at hg; cases hg
    · simp only [h', C.Space.put, C.upd_ne _ _ _ _ heq]; exact hcp
  refine ⟨hcore, hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, ?_, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  intro hne
  obtain ⟨hn0, ⟨r1, cs1, hp1, hg1, hsz1⟩⟩ := hcompLive hne
  refine ⟨hn0, r1, ?_⟩
  rcases rc with ⟨b⟩
  rcases r1 with ⟨b1⟩
  by_cases heq : b1 = b
  · subst heq
    simp only [C.Space.get] at hg hg1
    have heqCs : cs1 = cs := Option.some.inj (hg1.symm.trans hg)
    refine ⟨cs.set! off c', hp1, ?_, ?_⟩
    · simp [C.Space.get, C.Space.put]
    · simpa [heqCs] using hsz1
  · refine ⟨cs1, hp1, ?_, hsz1⟩
    simpa [h', C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq] using hg1

theorem parserEnv_put_quant {ctx : IoCtx} {h : C.Heap} {rq : C.QuantRef} {qs : Array C.JQuantTbl}
    {off : Nat} {q' : C.JQuantTbl}
    (hp : ParserEnv ctx h) (hg : C.Space.get h rq = some qs) :
    ParserEnv ctx (C.Space.put h rq (qs.set! off q')) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  let h' := C.Space.put h rq (qs.set! off q')
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, ?_, hhu, hsm⟩
    rcases rq with ⟨b⟩
    by_cases heq : k = b
    · subst heq; simp only [C.Space.get] at hg; rw [hq] at hg; cases hg
    · simp only [h', C.Space.put, C.upd_ne _ _ _ _ heq]; exact hq
  refine ⟨hcore, hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, ?_, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  intro i hi
  rcases hqt i hi with hnull | ⟨rq1, o1, qs1, hp1, hg1, hsz1⟩
  · left; exact hnull
  · right
    rcases rq with ⟨b⟩
    rcases rq1 with ⟨b1⟩
    by_cases heq : b1 = b
    · subst heq
      simp only [C.Space.get] at hg hg1
      have heqQ : qs1 = qs := Option.some.inj (hg1.symm.trans hg)
      exact ⟨.quant b1, o1, qs.set! off q', hp1, by simp [C.Space.get, C.Space.put],
        by simpa [heqQ] using hsz1⟩
    · exact ⟨.quant b1, o1, qs1, hp1, by simpa [h', C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq] using hg1, hsz1⟩

theorem parserEnv_put_huff {ctx : IoCtx} {h : C.Heap} {rh : C.HuffRef} {hs : Array C.JHuffTbl}
    {off : Nat} {h'tbl : C.JHuffTbl}
    (hp : ParserEnv ctx h) (hg : C.Space.get h rh = some hs) :
    ParserEnv ctx (C.Space.put h rh (hs.set! off h'tbl)) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  let h' := C.Space.put h rh (hs.set! off h'tbl)
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, ?_, hsm⟩
    rcases rh with ⟨b⟩
    by_cases heq : k = b
    · subst heq; simp only [C.Space.get] at hg; rw [hhu] at hg; cases hg
    · simp only [h', C.Space.put, C.upd_ne _ _ _ _ heq]; exact hhu
  refine ⟨hcore, hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, ?_, hahSz, ?_, hccSz, hisn0⟩
  · intro i hi
    rcases hdh i hi with hnull | ⟨rh1, o1, hs1, hp1, hg1, hsz1⟩
    · left; exact hnull
    · right
      rcases rh with ⟨b⟩; rcases rh1 with ⟨b1⟩
      by_cases heq : b1 = b
      · subst heq; simp only [C.Space.get] at hg hg1
        have heqH : hs1 = hs := Option.some.inj (hg1.symm.trans hg)
        exact ⟨.huff b1, o1, hs.set! off h'tbl, hp1, by simp [C.Space.get, C.Space.put],
          by simpa [heqH] using hsz1⟩
      · exact ⟨.huff b1, o1, hs1, hp1, by simpa [h', C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq] using hg1, hsz1⟩
  · intro i hi
    rcases hah i hi with hnull | ⟨rh1, o1, hs1, hp1, hg1, hsz1⟩
    · left; exact hnull
    · right
      rcases rh with ⟨b⟩; rcases rh1 with ⟨b1⟩
      by_cases heq : b1 = b
      · subst heq; simp only [C.Space.get] at hg hg1
        have heqH : hs1 = hs := Option.some.inj (hg1.symm.trans hg)
        exact ⟨.huff b1, o1, hs.set! off h'tbl, hp1, by simp [C.Space.get, C.Space.put],
          by simpa [heqH] using hsz1⟩
      · exact ⟨.huff b1, o1, hs1, hp1, by simpa [h', C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq] using hg1, hsz1⟩

theorem parserEnv_put_sm {ctx : IoCtx} {h : C.Heap} {rsm : C.SavedMarkerRef} {sms : Array C.JpegSavedMarker}
    {off : Nat} {sm' : C.JpegSavedMarker}
    (hp : ParserEnv ctx h) (hg : C.Space.get h rsm = some sms) (hoff : off < sms.size)
    (hcurOk : ∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
      mrks[0]!.curMarker = .ref rsm off →
      sm'.dataLength.toNat ≤ 65535 ∧ sm'.originalLength.toNat ≤ 65535 ∧
      WritableBytes h sm'.data sm'.dataLength.toNat ∧ mrks[0]!.bytesRead ≤ sm'.dataLength) :
    ParserEnv ctx (C.Space.put h rsm (sms.set! off sm')) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  let h' := C.Space.put h rsm (sms.set! off sm')
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, ?_⟩
    rcases rsm with ⟨b⟩
    by_cases heq : k = b
    · subst heq; simp only [C.Space.get] at hg; rw [hsm] at hg; cases hg
    · simp only [h', C.Space.put, C.upd_ne _ _ _ _ heq]; exact hsm
  refine ⟨hcore, hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    ?_, ?_, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  · rcases hcurm with hnull | ⟨rsm1, o1, sms1, sm1, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · left; exact hnull
    · right
      rcases rsm with ⟨b⟩; rcases rsm1 with ⟨b1⟩
      by_cases heq : b1 = b
      · subst heq
        simp only [C.Space.get] at hg h2
        have hSmsEq : sms1 = sms := Option.some.inj (h2.symm.trans hg)
        by_cases ho : o1 = off
        · subst ho
          obtain ⟨hd, ho, hw, hbr⟩ := hcurOk mrks hgmrk hszmrk h1
          exact ⟨.savedMarker b1, o1, sms.set! o1 sm', sm', h1,
            by simp [C.Space.get, C.Space.put],
            by simp [Array.set!_eq_setIfInBounds, hoff], (set_bang_self sms hoff sm').symm, hd, ho, hw, hbr⟩
        · have h3' : o1 < (sms.set! off sm').size := by simpa [Array.set!_eq_setIfInBounds, hSmsEq] using h3
          refine ⟨.savedMarker b1, o1, sms.set! off sm', sm1, h1,
            by simp [C.Space.get, C.Space.put],
            h3', ?_, h5, h6, h7, h8⟩
          rw [h4, hSmsEq]; exact (set_bang_ne sms (hSmsEq ▸ h3) hoff ho sm').symm
      · exact ⟨.savedMarker b1, o1, sms1, sm1, h1,
          by simpa [h', C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq] using h2,
          h3, h4, h5, h6, h7, h8⟩
  · rcases hmlEnd with hnull | hnull2 | ⟨rsm1, o1, sms1, h1, h2, h3⟩
    · left; exact hnull
    · right; left; exact hnull2
    · right; right
      rcases rsm with ⟨b⟩; rcases rsm1 with ⟨b1⟩
      by_cases heq : b1 = b
      · subst heq
        simp only [C.Space.get] at hg h2
        have hSmsEq : sms1 = sms := Option.some.inj (h2.symm.trans hg)
        exact ⟨.savedMarker b1, o1, sms.set! off sm', h1,
          by simp [C.Space.get, C.Space.put], by simpa [Array.set!_eq_setIfInBounds, hSmsEq] using h3⟩
      · exact ⟨.savedMarker b1, o1, sms1, h1,
          by simpa [h', C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq] using h2, h3⟩

theorem parserEnv_put_byte {ctx : IoCtx} {h : C.Heap} {b : Nat} {arr : Array UInt8}
    {idx : Nat} {v : UInt8}
    (hp : ParserEnv ctx h) (hgb : h.bytes b = some arr) :
    ParserEnv ctx (C.Space.put h (C.BRef.heap b) (arr.set! idx v)) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  let h' := C.Space.put h (C.BRef.heap b) (arr.set! idx v)
  have hEqB : h' = { h with bytes := C.upd h.bytes b (some (arr.set! idx v)) } := rfl
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨?_, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩
    by_cases heq : k = b
    · subst heq; rw [hb] at hgb; cases hgb
    · change h'.bytes.get k = none
      rw [hEqB, C.upd_ne _ _ _ _ heq]; exact hb
  have hcurv' : CurValid h' srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer := by
    rw [hEqB]; exact curValid_set_byte hgb hcurv
  refine ⟨hcore, hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv',
    ?_, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩
  rcases hcurm with hnull | ⟨rsm, off, sms, sm, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · left; exact hnull
  · right; refine ⟨rsm, off, sms, sm, h1, h2, h3, h4, h5, h6, ?_, h8⟩
    rcases h7 with ⟨b1, boff, bdata, bp, hgb1, hblen⟩
    by_cases heq : b1 = b
    · subst heq
      have hbdEq : bdata = arr := Option.some.inj (hgb1.symm.trans hgb)
      refine ⟨b1, boff, arr.set! idx v, bp, ?_, ?_⟩
      · change h'.bytes.get b1 = some (arr.set! idx v)
        rw [hEqB]; exact C.upd_same _ _ _
      · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, ← hbdEq]; exact hblen
    · refine ⟨b1, boff, bdata, bp, ?_, hblen⟩
      change h'.bytes.get b1 = some bdata
      rw [hEqB, C.upd_ne _ _ _ _ heq]; exact hgb1

/-! ## Accessors & primitive monadic specs on `ParserEnv` -/

theorem parserEnv_get_dc {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧
      dcs[0]!.err = .ref ctx.rerr 0 ∧ dcs[0]!.mem = .ref ctx.rmem 0 ∧
      dcs[0]!.master = .ref ctx.rmas 0 ∧ dcs[0]!.inputctl = .ref ctx.ric 0 ∧
      dcs[0]!.marker = .ref ctx.rmrk 0 ∧ dcs[0]!.src = .ref ctx.rs 0 := by
  obtain ⟨_hcore, _hfr, dcs, dc, _errs, _mems, _masters, _ics, _mrks, _srcs,
    hgdc, hszdc, hdc, herrp, _hgerr, _hszerr, _hrem, _hnw0,
    hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    hmasp, _hgmas, _hszmas, hicp, _hgic, _hszic, _hric, _hci,
    hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    _hcurm, _hmlEnd, _hsaw, _hcompLive, _hqtSz, _hqt, _hdhSz, _hdh, _hahSz, _hah, _hccSz, _hisn0⟩ := hp
  subst hdc
  exact ⟨dcs, hgdc, hszdc, herrp, hmemp, hmasp, hicp, hmrkp, hsrcp⟩

theorem parserEnv_get_err {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ errs, C.Space.get h ctx.rerr = some errs ∧ 0 < errs.size ∧
      errs[0]!.resetErrorMgr = .fn "reset_error_mgr" ∧ 0 ≤ errs[0]!.numWarnings.toInt := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, errs, _mems, _masters, _ics, _mrks, _srcs,
    _hgdc, _hszdc, _hdc, _herrp, hgerr, hszerr, hrem, hnw0,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    _hcurm, _hmlEnd, _hsaw, _hcompLive, _hqtSz, _hqt, _hdhSz, _hdh, _hahSz, _hah, _hccSz, _hisn0⟩ := hp
  exact ⟨errs, hgerr, hszerr, hrem, hnw0⟩

theorem parserEnv_get_mem {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ mems, C.Space.get h ctx.rmem = some mems ∧ 0 < mems.size ∧
      mems[0]!.allocSmall = .fn "alloc_small" ∧ mems[0]!.freePool = .fn "free_pool" ∧
      mems[0]!.selfDestruct = .fn "self_destruct" ∧ mems[0]!.livePools.size = 2 ∧
      mems[0]!.livePools[0]! = true ∧ mems[0]!.livePools[1]! = true ∧ mems[0]!.poolAllocs.size = 2 := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, _errs, mems, _masters, _ics, _mrks, _srcs,
    _hgdc, _hszdc, _hdc, _herrp, _hgerr, _hszerr, _hrem, _hnw0,
    _hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    _hcurm, _hmlEnd, _hsaw, _hcompLive, _hqtSz, _hqt, _hdhSz, _hdh, _hahSz, _hah, _hccSz, _hisn0⟩ := hp
  exact ⟨mems, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz⟩

theorem parserEnv_get_mas {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ masters, C.Space.get h ctx.rmas = some masters ∧ 0 < masters.size := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, _errs, _mems, masters, _ics, _mrks, _srcs,
    _hgdc, _hszdc, _hdc, _herrp, _hgerr, _hszerr, _hrem, _hnw0,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, hgmas, hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    _hcurm, _hmlEnd, _hsaw, _hcompLive, _hqtSz, _hqt, _hdhSz, _hdh, _hahSz, _hah, _hccSz, _hisn0⟩ := hp
  exact ⟨masters, hgmas, hszmas⟩

theorem parserEnv_get_mrk {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ mrks, C.Space.get h ctx.rmrk = some mrks ∧ 0 < mrks.size ∧
      mrks[0]!.readMarkers = .fn "read_markers" ∧ mrks[0]!.resetMarkerReader = .fn "reset_marker_reader" ∧
      (mrks[0]!.processCOM = .fn "save_marker" ∨ mrks[0]!.processCOM = .fn "skip_variable") ∧
      mrks[0]!.processAPPn.size = 16 ∧
      (∀ i < 16, mrks[0]!.processAPPn[i]! = .fn "save_marker" ∨
        mrks[0]!.processAPPn[i]! = .fn "skip_variable" ∨
        mrks[0]!.processAPPn[i]! = .fn "get_interesting_appn") ∧
      mrks[0]!.lengthLimitAPPn.size = 16 := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, _errs, _mems, _masters, _ics, mrks, _srcs,
    _hgdc, _hszdc, _hdc, _herrp, _hgerr, _hszerr, _hrem, _hnw0,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    _hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    _hcurm, _hmlEnd, _hsaw, _hcompLive, _hqtSz, _hqt, _hdhSz, _hdh, _hahSz, _hah, _hccSz, _hisn0⟩ := hp
  exact ⟨mrks, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz⟩

theorem parserEnv_get_src {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ srcs, C.Space.get h ctx.rs = some srcs ∧ 0 < srcs.size ∧
      srcs[0]!.initSource = .fn "init_mem_source" ∧
      (srcs[0]!.termSource = .fn "term_source" ∨ srcs[0]!.termSource = .fn "noop") ∧
      (srcs[0]!.skipInputData = .fn "skip_input_data" ∨ srcs[0]!.skipInputData = .fn "suspend_skip_input_data") ∧
      srcs[0]!.resyncToRestart = .fn "jpeg_resync_to_restart" ∧
      (srcs[0]!.fillInputBuffer = .fn "fill_mem_input_buffer" ∨
        (srcs[0]!.fillInputBuffer = .fn "suspend_input" ∧ srcs[0]!.skipInputData = .fn "suspend_skip_input_data")) ∧
      CurValid h srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, _errs, _mems, _masters, _ics, _mrks, srcs,
    _hgdc, _hszdc, _hdc, _herrp, _hgerr, _hszerr, _hrem, _hnw0,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    _hcurm, _hmlEnd, _hsaw, _hcompLive, _hqtSz, _hqt, _hdhSz, _hdh, _hahSz, _hah, _hccSz, _hisn0⟩ := hp
  exact ⟨srcs, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv⟩

/-- Generic error-manager update with continuation, leaving `resetErrorMgr` and `numWarnings` unchanged. -/
theorem errMsgUpdate_cont_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code : Int32) (f : Array Int32 → Array Int32) :
    ∃ h',
      (∀ {α : Type} (k : C.M α),
        C.run (do
          let err ← C.Ptr.load (.ref ctx.rerr 0)
          C.Ptr.store (.ref ctx.rerr 0) { err with msgCode := code, msgParmI := f err.msgParmI }
          k) h = C.run k h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨errs, hgerr, hszerr, _hrem, hnw0⟩ := parserEnv_get_err hp
  have hl := ptr_load_ok (r := ctx.rerr) (off := 0) hgerr hszerr
  have hro : C.Space.ro h ctx.rerr = false := by cases ctx.rerr; rfl
  let err' : C.JpegErrorMgr := { errs[0]! with msgCode := code, msgParmI := f errs[0]!.msgParmI }
  have hs := ptr_store_ok (r := ctx.rerr) (off := 0) (v := err') hgerr hro hszerr
  let h' := C.Space.put h ctx.rerr (errs.set! 0 err')
  have hp' : ParserEnv ctx h' := parserEnv_put_err hp hgerr hszerr rfl hnw0
  refine ⟨h', ?_, hp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _α k; rw [C.run_bind, hl]; dsimp only; rw [C.run_bind, hs]
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · intro errs1 errs' hg1 _ hg'
    have he1 := Option.some.inj (hg1.symm.trans hgerr)
    have hge' : C.Space.get h' ctx.rerr = some (errs.set! 0 err') := by
      rcases hr : ctx.rerr with ⟨be⟩; simp [h', C.Space.get, C.Space.put, hr]
    have he2 := Option.some.inj (hg'.symm.trans hge')
    refine ⟨by rw [he2]; simpa using hszerr, ?_⟩
    rw [he2, he1, set0_bang errs hszerr err']

theorem emitMessage_nonneg_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) {lvl : Int32} (hlvl : 0 ≤ lvl.toInt) :
    C.run (emitMessage (.ref ctx.rerr 0) lvl) h = .ok ((), h) := by
  obtain ⟨errs, hgerr, hszerr, _⟩ := parserEnv_get_err hp
  have hl := ptr_load_ok (r := ctx.rerr) (off := 0) hgerr hszerr
  have hneg : ¬(lvl < 0) := fun hlt => by
    have := Int32.lt_iff_toInt_lt.mp hlt
    change lvl.toInt < 0 at this; omega
  unfold emitMessage
  rw [C.run_bind, hl]; dsimp only
  simp [hneg, C.run]

theorem emitMessage_warn_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hbd : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63) :
    ∃ h',
      C.run (emitMessage (.ref ctx.rerr 0) (-1)) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt = errs[0]!.numWarnings.toInt + 1) := by
  obtain ⟨errs, hgerr, hszerr, _hrem, hnw0⟩ := parserEnv_get_err hp
  have hl := ptr_load_ok (r := ctx.rerr) (off := 0) hgerr hszerr
  have hnwLt := hbd errs hgerr hszerr
  have hlo : -(2 ^ 63 : Int) ≤ errs[0]!.numWarnings.toInt + (1 : Int64).toInt := by
    change -(2 ^ 63 : Int) ≤ errs[0]!.numWarnings.toInt + 1; omega
  have hhi : errs[0]!.numWarnings.toInt + (1 : Int64).toInt < 2 ^ 63 := by
    change errs[0]!.numWarnings.toInt + 1 < 2 ^ 63; omega
  have haddEq : C.i64Add errs[0]!.numWarnings 1 =
      pure (Int64.ofInt (errs[0]!.numWarnings.toInt + (1 : Int64).toInt)) :=
    C.i64Add_eq _ _ hlo hhi
  let nw' := Int64.ofInt (errs[0]!.numWarnings.toInt + (1 : Int64).toInt)
  have hro : C.Space.ro h ctx.rerr = false := by cases ctx.rerr; rfl
  let err' : C.JpegErrorMgr := { errs[0]! with numWarnings := nw' }
  have hs := ptr_store_ok (r := ctx.rerr) (off := 0) (v := err') hgerr hro hszerr
  let h' := C.Space.put h ctx.rerr (errs.set! 0 err')
  have hnwVal : nw'.toInt = errs[0]!.numWarnings.toInt + 1 := by
    change (Int64.ofInt (errs[0]!.numWarnings.toInt + 1)).toInt = errs[0]!.numWarnings.toInt + 1
    rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hp' : ParserEnv ctx h' := parserEnv_put_err hp hgerr hszerr rfl (by rw [hnwVal]; omega)
  refine ⟨h', ?_, hp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold emitMessage
    rw [C.run_bind, hl]; dsimp only
    have hlt : ((-1 : Int32) < 0) = true := by decide
    simp only [hlt, ↓reduceIte, C.run_bind, haddEq]
    dsimp only [pure, C.M]
    exact hs
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · cases ctx.rerr; rfl
  · intro errs1 errs' hg1 _ hg'
    have he1 := Option.some.inj (hg1.symm.trans hgerr)
    have hge' : C.Space.get h' ctx.rerr = some (errs.set! 0 err') := by
      rcases hr : ctx.rerr with ⟨be⟩; simp [h', C.Space.get, C.Space.put, hr]
    have he2 := Option.some.inj (hg'.symm.trans hge')
    refine ⟨by rw [he2]; simpa using hszerr, ?_⟩
    rw [he2, he1, set0_bang errs hszerr err']
    exact hnwVal

theorem tracems_nonneg_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (lvl code : Int32) (hlvl : 0 ≤ lvl.toInt) :
    ∃ h',
      C.run (tracems (.ref ctx.rerr 0) lvl code) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩ :=
    errMsgUpdate_cont_parser hp code (fun arr => arr)
  refine ⟨h', ?_, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩
  unfold tracems
  rw [hk (emitMessage (.ref ctx.rerr 0) lvl)]
  exact emitMessage_nonneg_parser hp' hlvl

theorem tracems1_nonneg_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (lvl code p1 : Int32) (hlvl : 0 ≤ lvl.toInt) :
    ∃ h',
      C.run (tracems1 (.ref ctx.rerr 0) lvl code p1) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩ :=
    errMsgUpdate_cont_parser hp code (fun arr => arr.set! 0 p1)
  refine ⟨h', ?_, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩
  unfold tracems1
  rw [hk (emitMessage (.ref ctx.rerr 0) lvl)]
  exact emitMessage_nonneg_parser hp' hlvl

theorem warnms_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code : Int32)
    (hbd : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63) :
    ∃ h',
      C.run (warnms (.ref ctx.rerr 0) code) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt = errs[0]!.numWarnings.toInt + 1) := by
  obtain ⟨h1, hk1, hp1, hd1, hmr1, hsr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1, hnw1⟩ :=
    errMsgUpdate_cont_parser hp code (fun arr => arr)
  have hbd1 : ∀ errs1, C.Space.get h1 ctx.rerr = some errs1 → 0 < errs1.size →
      errs1[0]!.numWarnings.toInt + 1 < 2 ^ 63 := by
    intro errs1 hg1 hsz1
    obtain ⟨errs0, hg0, hsz0, _⟩ := parserEnv_get_err hp
    obtain ⟨_, heq⟩ := hnw1 errs0 errs1 hg0 hsz0 hg1
    rw [heq]; exact hbd errs0 hg0 hsz0
  obtain ⟨h2, hrun2, hp2, hd2, hmr2, hsr2, hma2, hcp2, hq2, hhu2, hsm2, hby2, hme2, hco2, hnw2⟩ :=
    emitMessage_warn_parser hp1 hbd1
  refine ⟨h2, ?_, hp2, hd2.trans hd1, hmr2.trans hmr1, hsr2.trans hsr1, hma2.trans hma1,
    hcp2.trans hcp1, hq2.trans hq1, hhu2.trans hhu1, hsm2.trans hsm1, hby2.trans hby1,
    hme2.trans hme1, hco2.trans hco1, ?_⟩
  · unfold warnms; rw [hk1 (emitMessage (.ref ctx.rerr 0) (-1))]; exact hrun2
  · intro errs1 errs' hg hsz hg'
    obtain ⟨errsMid, hg1, hsz1, _⟩ := parserEnv_get_err hp1
    obtain ⟨_, heq1⟩ := hnw1 errs1 errsMid hg hsz hg1
    obtain ⟨hsz', heq2⟩ := hnw2 errsMid errs' hg1 hsz1 hg'
    exact ⟨hsz', by rw [heq2, heq1]⟩

theorem errexit_gen_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code : Int32) (f : Array Int32 → Array Int32) :
    ∃ h',
      C.run (do
        let err ← C.Ptr.load (.ref ctx.rerr 0)
        C.Ptr.store (.ref ctx.rerr 0) { err with msgCode := code, msgParmI := f err.msgParmI }
        return JpegRes.errExit code : C.M (JpegRes Unit)) h = .ok (.errExit code, h') ∧
      ParserEnv ctx h' := by
  obtain ⟨h', hk, hp', _⟩ := errMsgUpdate_cont_parser hp code f
  refine ⟨h', ?_, hp'⟩
  rw [hk (pure (JpegRes.errExit code))]; rfl

theorem fill_mem_input_buffer_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hbd : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63) :
    ∃ h',
      C.run (fill_mem_input_buffer (.ref (.decomp ctx.bdc) 0)) h = .ok (TRUE, h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ srcs', C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size ∧
        srcs'[0]!.nextInputByte = .ref .const_eof 0 ∧ srcs'[0]!.bytesInBuffer = 2 ∧
        (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          srcs'[0]!.skipInputData = srcs0[0]!.skipInputData)) ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt = errs[0]!.numWarnings.toInt + 1) := by
  obtain ⟨dcs, hgdc, hszdc, herrp, _, _, _, _, hsrcp⟩ := parserEnv_get_dc hp
  obtain ⟨errs, hgerr, hszerr, _⟩ := parserEnv_get_err hp
  obtain ⟨srcs, hgsrc, hszsrc, _⟩ := parserEnv_get_src hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  obtain ⟨h1, hwrun, hp1, hd1, hmr1, hsr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1, hnw1⟩ :=
    warnms_parser hp JWRN_JPEG_EOF hbd
  have hgsrc1 : C.Space.get h1 ctx.rs = some srcs := by
    rcases hrs : ctx.rs with ⟨bs⟩
    simp only [C.Space.get, hrs] at hgsrc ⊢
    rw [hsr1]; exact hgsrc
  have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc1 hszsrc
  have hroSrc : C.Space.ro h1 ctx.rs = false := by cases ctx.rs; rfl
  let src' : C.JpegSourceMgr := { srcs[0]! with nextInputByte := .ref .const_eof 0, bytesInBuffer := 2 }
  have hstsrc := ptr_store_ok (r := ctx.rs) (off := 0) (v := src') hgsrc1 hroSrc hszsrc
  let h2 := C.Space.put h1 ctx.rs (srcs.set! 0 src')
  have hce2 : CurValid h2 (.ref .const_eof 0) 2 := by
    refine ⟨by decide, Or.inr ⟨.const_eof, 0, #[0xFF, 0xD9, 0, 0], rfl, rfl, by decide⟩, ?_⟩
    intro off hoff; cases hoff; decide
  have hp2 : ParserEnv ctx h2 := parserEnv_put_src hp1 hgsrc1 hszsrc rfl rfl rfl rfl rfl hce2
  refine ⟨h2, ?_, hp2, hd1, hmr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, (by cases ctx.rs; exact hco1), ?_, ?_⟩
  · unfold fill_mem_input_buffer
    rw [C.run_bind, hldc]; dsimp only
    rw [herrp, hsrcp, C.run_bind, hwrun]
    dsimp only
    rw [C.run_bind, hlsrc]; dsimp only
    rw [C.run_bind, hstsrc]; rfl
  · intro srcs' hg2
    have hgs2 : C.Space.get h2 ctx.rs = some (srcs.set! 0 src') := by
      rcases hr : ctx.rs with ⟨bs⟩
      simp [h2, C.Space.get, C.Space.put, hr, C.upd_same]
    have heq := Option.some.inj (hg2.symm.trans hgs2)
    refine ⟨by rw [heq]; simpa using hszsrc, ?_, ?_, ?_⟩
    · rw [heq, set0_bang srcs hszsrc src']
    · rw [heq, set0_bang srcs hszsrc src']
    · intro srcs0 hg0 _
      have h0eq := Option.some.inj (hg0.symm.trans hgsrc)
      rw [heq, h0eq, set0_bang srcs hszsrc src']
  · intro errs1 errs' hg1 _ hg'
    have hg1' : C.Space.get h2 ctx.rerr = some errs' := hg'
    have hg1_h1 : C.Space.get h1 ctx.rerr = some errs' := by
      have herrEq : h2.errMgrs = h1.errMgrs := by rcases hrs : ctx.rs with ⟨bs⟩; rfl
      rcases hr : ctx.rerr with ⟨be⟩
      simp only [C.Space.get, hr] at hg1' ⊢
      rw [← herrEq]; exact hg1'
    exact hnw1 errs1 errs' hg1 ‹0 < errs1.size› hg1_h1

private theorem int32_toInt_ofNat {n : Nat} (hn : n < 2 ^ 31) :
    (Int32.ofNat n).toInt = (n : Int) := by
  rw [Int32.toInt_ofNat']
  have hsz : Int32.size = 2 ^ 32 := rfl
  rw [hsz]
  exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem uint64_toNat_pos {x : UInt64} (hx : x ≠ 0) : 0 < x.toNat :=
  Nat.pos_of_ne_zero fun h0 => hx (UInt64.toNat_inj.mp h0)

private theorem uint64_toNat_sub_one {x : UInt64} (hx : x ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hpos := uint64_toNat_pos hx
  rw [UInt64.toNat_sub_of_le x 1 (UInt64.le_iff_toNat_le.mpr hpos)]
  rfl

theorem inputByte_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (nib : C.BPtr) (bib : UInt64) (hcur : CurValid h nib bib)
    (hbd : bib = 0 → ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63) :
    ∃ res h',
      C.run (inputByte (.ref (.decomp ctx.bdc) 0) nib bib) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      match res with
      | none => h' = h
      | some (c, nib1, bib1) =>
        0 ≤ c.toInt ∧ c.toInt ≤ 255 ∧
        CurValid h' nib1 bib1 ∧
        (if isConstEofPtr nib1 = false then
          isConstEofPtr nib = false ∧ bib ≠ 0 ∧ bib1.toNat + 1 = bib.toNat ∧
          h' = h
         else
          ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
            C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
            errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + (if bib == 0 then 1 else 0)) := by
  have hp0 := hp
  obtain ⟨dcs, hgdc, hszdc, herrp, _, _, _, _, hsrcp⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _his, _hts, _hsip, _hrtr, hfill, _⟩ := parserEnv_get_src hp
  rcases hcur with ⟨hbibLt, hbibLive, hce⟩
  by_cases hbibZ : bib = 0
  · subst hbibZ
    have hn0 : ((0 : UInt64) != 0) = false := rfl
    have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
    have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc hszsrc
    rcases hfill with hfillMem | ⟨hfillSusp, _⟩
    · have hfne : (srcs[0]!.fillInputBuffer == .fn "fill_mem_input_buffer") = true := by simp [hfillMem]
      obtain ⟨h2, hf2, hp2, hd2, hmr2, hma2, hcp2, hq2, hhu2, hsm2, hby2, hme2, hco2, hsrc2, hnw2⟩ :=
        fill_mem_input_buffer_parser hp0 (hbd rfl)
      obtain ⟨srcs2, hgs2, hszs2, _⟩ := parserEnv_get_src hp2
      obtain ⟨_, hnib2, hbib2, _⟩ := hsrc2 srcs2 hgs2
      have hl2 := ptr_load_ok (r := ctx.rs) (off := 0) hgs2 hszs2
      have hconstLd := ptr_load_ok (r := C.BRef.const_eof) (off := 0) (h := h2) (xs := #[0xFF, 0xD9, 0, 0]) rfl (by decide)
      have hconstAdd := ptr_add_ok (r := C.BRef.const_eof) (off := 0) (k := 1) (h := h2) (xs := #[0xFF, 0xD9, 0, 0]) rfl (by decide) (by decide) (by decide)
      have hmba : C.run (makeByteAvail (.ref (.decomp ctx.bdc) 0) nib 0) h =
          .ok (some (.ref .const_eof 0, 2), h2) := by
        unfold makeByteAvail
        simp only [hn0, Bool.false_eq_true, ↓reduceIte, C.run_bind, hldc, hsrcp, hlsrc, hfne, hf2]
        have ht0 : (TRUE == 0) = false := by decide
        have hb2 : ((2 : UInt64) == 0) = false := by decide
        simp only [ht0, Bool.false_eq_true, ↓reduceIte, C.run_bind, hl2, hbib2, hb2]
        rw [hnib2]; rfl
      have hrun : C.run (inputByte (.ref (.decomp ctx.bdc) 0) nib 0) h =
          .ok (some (0xFF, .ref .const_eof 1, 1), h2) := by
        unfold inputByte
        rw [C.run_bind, hmba]; dsimp only
        rw [C.run_bind, hconstLd]; dsimp only
        rw [C.run_bind, hconstAdd]; dsimp only
        rfl
      have hcv1 : CurValid h2 (.ref .const_eof 1) 1 := by
        refine ⟨by decide, Or.inr ⟨.const_eof, 1, #[0xFF, 0xD9, 0, 0], rfl, rfl, by decide⟩, ?_⟩
        intro o ho; cases ho; decide
      refine ⟨some (0xFF, .ref .const_eof 1, 1), h2, hrun, hp2,
        hd2, hmr2, hma2, hcp2, hq2, hhu2, hsm2, hby2, hme2, hco2, by decide, by decide, hcv1, ?_⟩
      simp only [isConstEofPtr, Bool.true_eq_false, ↓reduceIte]
      intro errs1 errs2 hg1 hsz1 hg2
      obtain ⟨hsz2, heq⟩ := hnw2 errs1 errs2 hg1 hsz1 hg2
      exact ⟨hsz2, by simp [heq]⟩
    · have hfne : (srcs[0]!.fillInputBuffer == .fn "fill_mem_input_buffer") = false := by simp [hfillSusp]
      have hfsp : (srcs[0]!.fillInputBuffer == .fn "suspend_input") = true := by simp [hfillSusp]
      have hmba : C.run (makeByteAvail (.ref (.decomp ctx.bdc) 0) nib 0) h = .ok (none, h) := by
        unfold makeByteAvail
        simp only [hn0, Bool.false_eq_true, ↓reduceIte, C.run_bind, hldc, hsrcp, hlsrc, hfne, hfsp]
        rfl
      have hrun : C.run (inputByte (.ref (.decomp ctx.bdc) 0) nib 0) h = .ok (none, h) := by
        unfold inputByte; rw [C.run_bind, hmba]; rfl
      exact ⟨none, h, hrun, hp0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hne : (bib != 0) = true := by simp [bne, hbibZ]
    rcases hbibLive with rfl | ⟨r, off, data, hpNib, hgB, hlenB⟩
    · exact False.elim (hbibZ rfl)
    · have hpos : 0 < bib.toNat := uint64_toNat_pos hbibZ
      have hoff : off < data.size := by omega
      have hldB := ptr_load_ok (r := r) (off := off) hgB hoff
      have haddB := ptr_add_ok (r := r) (off := off) (k := 1) hgB (by omega) (by omega) (by omega)
      have hsub : (bib - 1).toNat = bib.toNat - 1 := uint64_toNat_sub_one hbibZ
      let nib1 : C.BPtr := .ref r (off + 1)
      have hcv1 : CurValid h nib1 (bib - 1) := by
        refine ⟨by omega, ?_, ?_⟩
        · by_cases hb1 : bib - 1 = 0
          · left; exact hb1
          · right; exact ⟨r, off + 1, data, rfl, hgB, by omega⟩
        · intro o1 ho1
          rw [show nib1 = .ref r (off + 1) from rfl] at ho1
          cases ho1
          have := hce off hpNib
          omega
      have hlt256 : (data[off]!).toNat < 256 := UInt8.toNat_lt (data[off]!)
      have hcEq : (Int32.ofNat (data[off]!).toNat).toInt = ((data[off]!).toNat : Int) :=
        int32_toInt_ofNat (by omega)
      have hc0 : 0 ≤ (Int32.ofNat (data[off]!).toNat).toInt := by omega
      have hc255 : (Int32.ofNat (data[off]!).toNat).toInt ≤ 255 := by omega
      have hmba : C.run (makeByteAvail (.ref (.decomp ctx.bdc) 0) nib bib) h =
          .ok (some (nib, bib), h) := by
        unfold makeByteAvail; simp [hne, C.run]
      have hrun : C.run (inputByte (.ref (.decomp ctx.bdc) 0) nib bib) h =
          .ok (some (Int32.ofNat (data[off]!).toNat, nib1, bib - 1), h) := by
        unfold inputByte
        rw [C.run_bind, hmba]; dsimp only
        rw [hpNib, C.run_bind, hldB]; dsimp only
        rw [C.run_bind, haddB]; rfl
      refine ⟨some (Int32.ofNat (data[off]!).toNat, nib1, bib - 1), h, hrun, hp0,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hc0, hc255, hcv1, ?_⟩
      by_cases hif : isConstEofPtr nib1 = false
      · simp only [hif, ↓reduceIte]
        have hif0 : isConstEofPtr nib = false := by
          have hif' : isConstEofPtr (.ref r (off + 1)) = false := hif
          rw [hpNib]; cases r <;> simp [isConstEofPtr] at hif' ⊢
        refine ⟨hif0, hbibZ, ?_, trivial⟩
        omega
      · cases hifT : isConstEofPtr nib1 <;> simp [hifT] at hif ⊢
        intro errs1 errs2 hg1 hsz1 hg2
        have heq := Option.some.inj (hg2.symm.trans hg1)
        subst heq; refine ⟨hsz1, by omega⟩

/-! ## Additional `tracems*`, `warnms*`, `errexit*`, `input2Bytes`, `inputSync`, `skip_input_data`, and allocator specs -/

theorem tracems2_nonneg_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (lvl code p1 p2 : Int32) (hlvl : 0 ≤ lvl.toInt) :
    ∃ h',
      C.run (tracems2 (.ref ctx.rerr 0) lvl code p1 p2) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩ :=
    errMsgUpdate_cont_parser hp code (fun arr => (arr.set! 0 p1).set! 1 p2)
  refine ⟨h', ?_, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩
  unfold tracems2; rw [hk (emitMessage (.ref ctx.rerr 0) lvl)]
  exact emitMessage_nonneg_parser hp' hlvl

theorem tracems3_nonneg_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (lvl code p1 p2 p3 : Int32) (hlvl : 0 ≤ lvl.toInt) :
    ∃ h',
      C.run (tracems3 (.ref ctx.rerr 0) lvl code p1 p2 p3) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩ :=
    errMsgUpdate_cont_parser hp code (fun arr => ((arr.set! 0 p1).set! 1 p2).set! 2 p3)
  refine ⟨h', ?_, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩
  unfold tracems3; rw [hk (emitMessage (.ref ctx.rerr 0) lvl)]
  exact emitMessage_nonneg_parser hp' hlvl

theorem tracems4_nonneg_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (lvl code p1 p2 p3 p4 : Int32) (hlvl : 0 ≤ lvl.toInt) :
    ∃ h',
      C.run (tracems4 (.ref ctx.rerr 0) lvl code p1 p2 p3 p4) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩ :=
    errMsgUpdate_cont_parser hp code (fun arr => (((arr.set! 0 p1).set! 1 p2).set! 2 p3).set! 3 p4)
  refine ⟨h', ?_, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩
  unfold tracems4; rw [hk (emitMessage (.ref ctx.rerr 0) lvl)]
  exact emitMessage_nonneg_parser hp' hlvl

theorem tracems5_nonneg_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (lvl code p1 p2 p3 p4 p5 : Int32) (hlvl : 0 ≤ lvl.toInt) :
    ∃ h',
      C.run (tracems5 (.ref ctx.rerr 0) lvl code p1 p2 p3 p4 p5) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩ :=
    errMsgUpdate_cont_parser hp code (fun arr => ((((arr.set! 0 p1).set! 1 p2).set! 2 p3).set! 3 p4).set! 4 p5)
  refine ⟨h', ?_, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩
  unfold tracems5; rw [hk (emitMessage (.ref ctx.rerr 0) lvl)]
  exact emitMessage_nonneg_parser hp' hlvl

theorem tracems8_nonneg_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (lvl code p1 p2 p3 p4 p5 p6 p7 p8 : Int32) (hlvl : 0 ≤ lvl.toInt) :
    ∃ h',
      C.run (tracems8 (.ref ctx.rerr 0) lvl code p1 p2 p3 p4 p5 p6 p7 p8) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩ :=
    errMsgUpdate_cont_parser hp code (fun _ => #[p1, p2, p3, p4, p5, p6, p7, p8])
  refine ⟨h', ?_, hp', hd, hmr, hsr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw⟩
  unfold tracems8; rw [hk (emitMessage (.ref ctx.rerr 0) lvl)]
  exact emitMessage_nonneg_parser hp' hlvl

theorem warnms2_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code p1 p2 : Int32)
    (hbd : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63) :
    ∃ h',
      C.run (warnms2 (.ref ctx.rerr 0) code p1 p2) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt = errs[0]!.numWarnings.toInt + 1) := by
  obtain ⟨h1, hk1, hp1, hd1, hmr1, hsr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1, hnw1⟩ :=
    errMsgUpdate_cont_parser hp code (fun arr => (arr.set! 0 p1).set! 1 p2)
  have hbd1 : ∀ errs1, C.Space.get h1 ctx.rerr = some errs1 → 0 < errs1.size →
      errs1[0]!.numWarnings.toInt + 1 < 2 ^ 63 := by
    intro errs1 hg1 hsz1
    obtain ⟨errs0, hg0, hsz0, _⟩ := parserEnv_get_err hp
    obtain ⟨_, heq⟩ := hnw1 errs0 errs1 hg0 hsz0 hg1
    rw [heq]; exact hbd errs0 hg0 hsz0
  obtain ⟨h2, hrun2, hp2, hd2, hmr2, hsr2, hma2, hcp2, hq2, hhu2, hsm2, hby2, hme2, hco2, hnw2⟩ :=
    emitMessage_warn_parser hp1 hbd1
  refine ⟨h2, ?_, hp2, hd2.trans hd1, hmr2.trans hmr1, hsr2.trans hsr1, hma2.trans hma1,
    hcp2.trans hcp1, hq2.trans hq1, hhu2.trans hhu1, hsm2.trans hsm1, hby2.trans hby1,
    hme2.trans hme1, hco2.trans hco1, ?_⟩
  · unfold warnms2; rw [hk1 (emitMessage (.ref ctx.rerr 0) (-1))]; exact hrun2
  · intro errs1 errs' hg hsz hg'
    obtain ⟨errsMid, hg1, hsz1, _⟩ := parserEnv_get_err hp1
    obtain ⟨_, heq1⟩ := hnw1 errs1 errsMid hg hsz hg1
    obtain ⟨hsz', heq2⟩ := hnw2 errsMid errs' hg1 hsz1 hg'
    exact ⟨hsz', by rw [heq2, heq1]⟩

theorem errexit_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code : Int32) :
    ∃ h', C.run (errexit (.ref ctx.rerr 0) code) h = .ok (.errExit code, h') ∧ ParserEnv ctx h' := by
  obtain ⟨h', hk, hp', _⟩ := errMsgUpdate_cont_parser hp code (fun arr => arr)
  refine ⟨h', ?_, hp'⟩
  unfold errexit; exact hk (pure (JpegRes.errExit code))

theorem errexit1_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code p1 : Int32) :
    ∃ h', C.run (errexit1 (.ref ctx.rerr 0) code p1) h = .ok (.errExit code, h') ∧ ParserEnv ctx h' := by
  obtain ⟨h', hk, hp', _⟩ := errMsgUpdate_cont_parser hp code (fun arr => arr.set! 0 p1)
  refine ⟨h', ?_, hp'⟩
  unfold errexit1; exact hk (pure (JpegRes.errExit code))

theorem errexit2_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code p1 p2 : Int32) :
    ∃ h', C.run (errexit2 (.ref ctx.rerr 0) code p1 p2) h = .ok (.errExit code, h') ∧ ParserEnv ctx h' := by
  obtain ⟨h', hk, hp', _⟩ := errMsgUpdate_cont_parser hp code (fun arr => (arr.set! 0 p1).set! 1 p2)
  refine ⟨h', ?_, hp'⟩
  unfold errexit2; exact hk (pure (JpegRes.errExit code))

private theorem int32_shiftLeft8_add {b1 b2 : Int32}
    (hb1Lo : 0 ≤ b1.toInt) (hb1Hi : b1.toInt ≤ 255)
    (hb2Lo : 0 ≤ b2.toInt) (hb2Hi : b2.toInt ≤ 255) :
    ((b1 <<< 8) + b2).toInt = b1.toInt * 256 + b2.toInt := by
  have hsh : ((8 : Int32).toBitVec.smod 32).toNat = 8 := by decide
  have hb1Sh : (b1 <<< 8).toInt = b1.toInt * 256 := by
    have hb1BvNat : b1.toBitVec.toNat = b1.toInt.toNat := by
      have hc := BitVec.toInt_eq_toNat_cond b1.toBitVec
      have hti : b1.toInt = b1.toBitVec.toInt := rfl
      omega
    have hbvNat : (b1 <<< 8).toBitVec.toNat = b1.toInt.toNat * 256 := by
      have hbv : (b1 <<< 8).toBitVec = b1.toBitVec <<< ((8 : Int32).toBitVec.smod 32).toNat := rfl
      rw [hbv, hsh, BitVec.toNat_shiftLeft, hb1BvNat, Nat.shiftLeft_eq]
      have hpow : (2 : Nat) ^ 8 = 256 := rfl
      rw [hpow, Nat.mod_eq_of_lt (by omega)]
    have htiSh : (b1 <<< 8).toInt = (b1 <<< 8).toBitVec.toInt := rfl
    rw [htiSh, BitVec.toInt_eq_toNat_cond]
    split <;> omega
  rw [Int32.toInt_add, hb1Sh]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem input2Bytes_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (nib : C.BPtr) (bib : UInt64) (hcur : CurValid h nib bib)
    (hbd : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 2 < 2 ^ 63) :
    ∃ res h',
      C.run (input2Bytes (.ref (.decomp ctx.bdc) 0) nib bib) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      match res with
      | none =>
        ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
          C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
          errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 2
      | some (v, nib2, bib2) =>
        0 ≤ v.toInt ∧ v.toInt ≤ 65535 ∧
        CurValid h' nib2 bib2 ∧
        (if isConstEofPtr nib2 = false then
          isConstEofPtr nib = false ∧ bib2.toNat + 2 = bib.toNat ∧ h' = h
         else
          ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
            C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
            errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 2) := by
  have hbd0 : bib = 0 → ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := by
    intro _ errs hg hsz; have := hbd errs hg hsz; omega
  obtain ⟨res1, h1, hrun1, hp1, hd1, hmr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1, hpost1⟩ :=
    inputByte_parser hp nib bib hcur hbd0
  cases res1 with
  | none =>
    refine ⟨none, h1, ?_, hp1, hd1, hmr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1, ?_⟩
    · unfold input2Bytes; rw [C.run_bind, hrun1]; rfl
    · rw [hpost1]
      intro errs errs' hg1 hsz1 hg2
      have := Option.some.inj (hg2.symm.trans hg1); subst this
      exact ⟨hsz1, by omega⟩
  | some x =>
    rcases x with ⟨b1, nib1, bib1⟩
    rcases hpost1 with ⟨hb10, hb1255, hcur1, hce1⟩
    have hbd1 : bib1 = 0 → ∀ errs, C.Space.get h1 ctx.rerr = some errs → 0 < errs.size →
        errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := by
      intro _ errs1 hg1 hsz1
      by_cases hce1f : isConstEofPtr nib1 = false
      · simp only [hce1f, ↓reduceIte] at hce1
        rcases hce1 with ⟨_, _, _, hh1⟩
        subst hh1; have := hbd errs1 hg1 hsz1; omega
      · have hcT : isConstEofPtr nib1 = true := by cases hc : isConstEofPtr nib1 <;> simp_all
        simp only [hcT, Bool.true_eq_false, ↓reduceIte] at hce1
        obtain ⟨errs0, hg0, hsz0, _⟩ := parserEnv_get_err hp
        obtain ⟨_, hle⟩ := hce1 errs0 errs1 hg0 hsz0 hg1
        have := hbd errs0 hg0 hsz0
        split at hle <;> omega
    obtain ⟨res2, h2, hrun2, hp2, hd2, hmr2, hma2, hcp2, hq2, hhu2, hsm2, hby2, hme2, hco2, hpost2⟩ :=
      inputByte_parser hp1 nib1 bib1 hcur1 hbd1
    cases res2 with
    | none =>
      refine ⟨none, h2, ?_, hp2, hd2.trans hd1, hmr2.trans hmr1, hma2.trans hma1,
        hcp2.trans hcp1, hq2.trans hq1, hhu2.trans hhu1, hsm2.trans hsm1, hby2.trans hby1,
        hme2.trans hme1, hco2.trans hco1, ?_⟩
      · unfold input2Bytes; rw [C.run_bind, hrun1]; dsimp only; rw [C.run_bind, hrun2]; rfl
      · rw [hpost2]
        intro errs errs1 hg hsz hg1
        by_cases hce1f : isConstEofPtr nib1 = false
        · simp only [hce1f, ↓reduceIte] at hce1
          rcases hce1 with ⟨_, _, _, hh1⟩; subst hh1
          have := Option.some.inj (hg1.symm.trans hg); subst this; exact ⟨hsz, by omega⟩
        · have hcT : isConstEofPtr nib1 = true := by cases hc : isConstEofPtr nib1 <;> simp_all
          simp only [hcT, Bool.true_eq_false, ↓reduceIte] at hce1
          obtain ⟨hsz1, hle⟩ := hce1 errs errs1 hg hsz hg1
          exact ⟨hsz1, by split at hle <;> omega⟩
    | some y =>
      rcases y with ⟨b2, nib2, bib2⟩
      rcases hpost2 with ⟨hb20, hb2255, hcur2, hce2⟩
      have hvEq : ((b1 <<< 8) + b2).toInt = b1.toInt * 256 + b2.toInt :=
        int32_shiftLeft8_add hb10 hb1255 hb20 hb2255
      refine ⟨some ((b1 <<< 8) + b2, nib2, bib2), h2, ?_, hp2,
        hd2.trans hd1, hmr2.trans hmr1, hma2.trans hma1, hcp2.trans hcp1,
        hq2.trans hq1, hhu2.trans hhu1, hsm2.trans hsm1, hby2.trans hby1,
        hme2.trans hme1, hco2.trans hco1,
        by omega, by omega, hcur2, ?_⟩
      · unfold input2Bytes; rw [C.run_bind, hrun1]; dsimp only; rw [C.run_bind, hrun2]; rfl
      · by_cases hce2f : isConstEofPtr nib2 = false
        · simp only [hce2f, ↓reduceIte]
          simp only [hce2f, ↓reduceIte] at hce2
          rcases hce2 with ⟨hce1f, _, hbib2, hh2⟩
          simp only [hce1f, ↓reduceIte] at hce1
          rcases hce1 with ⟨hcef, _, hbib1, hh1⟩
          refine ⟨hcef, by omega, hh2.trans hh1⟩
        · have hc2T : isConstEofPtr nib2 = true := by cases hc : isConstEofPtr nib2 <;> simp_all
          simp only [hc2T, Bool.true_eq_false, ↓reduceIte] at hce2 ⊢
          intro errs0 errs2 hg0 hsz0 hg2
          obtain ⟨errs1, hg1, hsz1, _⟩ := parserEnv_get_err hp1
          obtain ⟨_, hle2⟩ := hce2 errs1 errs2 hg1 hsz1 hg2
          have hnw1 : errs1[0]!.numWarnings.toInt ≤ errs0[0]!.numWarnings.toInt + 1 := by
            by_cases hce1f : isConstEofPtr nib1 = false
            · simp only [hce1f, ↓reduceIte] at hce1
              rcases hce1 with ⟨_, _, _, hh1⟩; subst hh1
              have := Option.some.inj (hg1.symm.trans hg0); subst this; omega
            · have hc1T : isConstEofPtr nib1 = true := by cases hc : isConstEofPtr nib1 <;> simp_all
              simp only [hc1T, Bool.true_eq_false, ↓reduceIte] at hce1
              obtain ⟨_, hle1⟩ := hce1 errs0 errs1 hg0 hsz0 hg1
              split at hle1 <;> omega
          have hsz2 : 0 < errs2.size := (hce2 errs1 errs2 hg1 hsz1 hg2).1
          exact ⟨hsz2, by split at hle2 <;> omega⟩

theorem inputSync_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (nib : C.BPtr) (bib : UInt64) (hcur : CurValid h nib bib) :
    ∃ h',
      C.run (inputSync (.ref (.decomp ctx.bdc) 0) nib bib) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.errMgrs = h.errMgrs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ srcs', C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size ∧
        srcs'[0]!.nextInputByte = nib ∧ srcs'[0]!.bytesInBuffer = bib) := by
  obtain ⟨dcs, hgdc, hszdc, _, _, _, _, _, hsrcp⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _⟩ := parserEnv_get_src hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc hszsrc
  have hro : C.Space.ro h ctx.rs = false := by cases ctx.rs; rfl
  let src' : C.JpegSourceMgr := { srcs[0]! with nextInputByte := nib, bytesInBuffer := bib }
  have hs := ptr_store_ok (r := ctx.rs) (off := 0) (v := src') hgsrc hro hszsrc
  let h' := C.Space.put h ctx.rs (srcs.set! 0 src')
  have hp' : ParserEnv ctx h' := parserEnv_put_src hp hgsrc hszsrc rfl rfl rfl rfl rfl hcur
  refine ⟨h', ?_, hp', by cases ctx.rs; rfl, by cases ctx.rs; rfl, by cases ctx.rs; rfl,
    by cases ctx.rs; rfl, by cases ctx.rs; rfl, by cases ctx.rs; rfl,
    by cases ctx.rs; rfl, by cases ctx.rs; rfl, by cases ctx.rs; rfl, by cases ctx.rs; rfl,
    by cases ctx.rs; rfl, ?_⟩
  · unfold inputSync; rw [C.run_bind, hldc]; dsimp only; rw [hsrcp, C.run_bind, hlsrc]; exact hs
  · intro srcs' hg'
    have hgs' : C.Space.get h' ctx.rs = some (srcs.set! 0 src') := by
      rcases hr : ctx.rs with ⟨bs⟩; simp [h', C.Space.get, C.Space.put, hr]
    have heq := Option.some.inj (hg'.symm.trans hgs')
    subst heq
    refine ⟨by simpa using hszsrc, ?_, ?_⟩ <;> rw [set0_bang srcs hszsrc src']

theorem skip_input_data_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (numBytes : Int64)
    (hskip : ∃ srcs, C.Space.get h ctx.rs = some srcs ∧ 0 < srcs.size ∧
      srcs[0]!.skipInputData = .fn "skip_input_data")
    (hnum : numBytes.toInt ≤ 65535)
    (hbd : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 2 ^ 16 < 2 ^ 63) :
    ∃ h',
      C.run (skip_input_data (.ref (.decomp ctx.bdc) 0) numBytes) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 1 + 65535 / 2) ∧
      (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
        (isConstEofPtr srcs0[0]!.nextInputByte = true → isConstEofPtr srcs'[0]!.nextInputByte = true) ∧
        (isConstEofPtr srcs'[0]!.nextInputByte = false →
          isConstEofPtr srcs0[0]!.nextInputByte = false ∧
          srcs'[0]!.bytesInBuffer.toNat ≤ srcs0[0]!.bytesInBuffer.toNat ∧
          ∀ errs0 errs1, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
            C.Space.get h' ctx.rerr = some errs1 → 0 < errs1.size →
            errs1[0]!.numWarnings.toInt = errs0[0]!.numWarnings.toInt)) := by
  obtain ⟨dcs, hgdc, hszdc, _, _, _, _, _, hsrcp⟩ := parserEnv_get_dc hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  by_cases hpos : numBytes > 0
  · have hposInt : 0 < numBytes.toInt := Int64.lt_iff_toInt_lt.mp hpos
    obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
    let Inv (k : Nat) (h1 : C.Heap) (nb : Int64) : Prop :=
      ParserEnv ctx h1 ∧
      0 < nb.toInt ∧ nb.toInt ≤ 65535 ∧
      h1.decomps = h.decomps ∧ h1.markers = h.markers ∧
      h1.masters = h.masters ∧ h1.comps = h.comps ∧ h1.quants = h.quants ∧
      h1.huffs = h.huffs ∧ h1.savedMarkers = h.savedMarkers ∧ h1.bytes = h.bytes ∧
      h1.mems = h.mems ∧ h1.consts = h.consts ∧
      (∀ srcs1, C.Space.get h1 ctx.rs = some srcs1 → 0 < srcs1.size →
        srcs1[0]!.skipInputData = .fn "skip_input_data" ∧
        k = 2 * nb.toInt.toNat + (if srcs1[0]!.bytesInBuffer.toNat < 2 then 1 else 0) ∧
        (isConstEofPtr srcs1[0]!.nextInputByte = false →
          isConstEofPtr srcs0[0]!.nextInputByte = false ∧
          srcs1[0]!.bytesInBuffer.toNat ≤ srcs0[0]!.bytesInBuffer.toNat ∧
          ∀ errs0 errs1, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
            C.Space.get h1 ctx.rerr = some errs1 → 0 < errs1.size →
            errs1[0]!.numWarnings.toInt = errs0[0]!.numWarnings.toInt) ∧
        (∀ errs0 errs1, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
          C.Space.get h1 ctx.rerr = some errs1 → 0 < errs1.size ∧
          errs1[0]!.numWarnings.toInt + nb.toInt / 2 +
            (if srcs1[0]!.bytesInBuffer.toNat < 2 then (1 : Int) else 0) ≤
            errs0[0]!.numWarnings.toInt + 65535 / 2 + 1))
    let Post (h1 : C.Heap) (nb : Int64) : Prop :=
      ParserEnv ctx h1 ∧
      0 < nb.toInt ∧ nb.toInt ≤ 65535 ∧
      h1.decomps = h.decomps ∧ h1.markers = h.markers ∧
      h1.masters = h.masters ∧ h1.comps = h.comps ∧ h1.quants = h.quants ∧
      h1.huffs = h.huffs ∧ h1.savedMarkers = h.savedMarkers ∧ h1.bytes = h.bytes ∧
      h1.mems = h.mems ∧ h1.consts = h.consts ∧
      (∃ srcs1, C.Space.get h1 ctx.rs = some srcs1 ∧ 0 < srcs1.size ∧
        nb.toInt ≤ (srcs1[0]!.bytesInBuffer.toNat : Int) ∧
        (isConstEofPtr srcs1[0]!.nextInputByte = false →
          isConstEofPtr srcs0[0]!.nextInputByte = false ∧
          srcs1[0]!.bytesInBuffer.toNat ≤ srcs0[0]!.bytesInBuffer.toNat ∧
          ∀ errs0 errs1, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
            C.Space.get h1 ctx.rerr = some errs1 → 0 < errs1.size →
            errs1[0]!.numWarnings.toInt = errs0[0]!.numWarnings.toInt)) ∧
      (∀ errs0 errs1, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h1 ctx.rerr = some errs1 → 0 < errs1.size ∧
        errs1[0]!.numWarnings.toInt ≤ errs0[0]!.numWarnings.toInt + 1 + 65535 / 2)
    let k0 : Nat := 2 * numBytes.toInt.toNat + (if srcs0[0]!.bytesInBuffer.toNat < 2 then 1 else 0)
    have hinit : Inv k0 h numBytes := by
      refine ⟨hp, hposInt, hnum, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro srcs1 hg1 _
      obtain ⟨srcsSk, hgSk, _, hsk⟩ := hskip
      have heq1 : srcs1 = srcsSk := Option.some.inj (hg1.symm.trans hgSk)
      have heq0 : srcs1 = srcs0 := Option.some.inj (hg1.symm.trans hgsrc0)
      refine ⟨heq1 ▸ hsk, by rw [heq0], ?_, ?_⟩
      · intro hfalse; subst heq0
        exact ⟨hfalse, Nat.le_refl _, fun errs0 errs1 hg0 _ hge1 _ => by rw [Option.some.inj (hge1.symm.trans hg0)]⟩
      · intro errs0 errs1 hg0 hsz0 hge1
        have := Option.some.inj (hge1.symm.trans hg0); subst this
        refine ⟨hsz0, ?_⟩
        split <;> omega
    have hk0Lt : k0 < C.fuel := by
      unfold C.fuel; dsimp only [k0]; split <;> omega
    obtain ⟨rem, h1, hloop, hpost⟩ :=
      cwhile_terminates
        (fun (nb : Int64) => do
          let src ← C.Ptr.load dcs[0]!.src
          if nb.toInt > Int.ofNat src.bytesInBuffer.toNat then return (true, nb) else return (false, nb))
        (fun (nb : Int64) => do
          let src ← C.Ptr.load dcs[0]!.src
          let nb' := Int64.ofInt (nb.toInt - Int.ofNat src.bytesInBuffer.toNat)
          if src.fillInputBuffer == .fn "fill_mem_input_buffer" then
            let _ ← fill_mem_input_buffer (.ref (.decomp ctx.bdc) 0)
            return nb'
          else
            C.ub "unsupported fill_input_buffer")
        Inv Post
        (fun k h1 nb hinv => by
          rcases hinv with ⟨hp1, hnb0, hnbLe, hd1, hmr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1, hfn⟩
          obtain ⟨srcs1, hg1, hsz1, _his, _hts, _hsip, _hrtr, hfill1, hcur1⟩ := parserEnv_get_src hp1
          obtain ⟨hsk1, hk1, hnoEof1, hnw1⟩ := hfn srcs1 hg1 hsz1
          have hl1 := ptr_load_ok (r := ctx.rs) (off := 0) hg1 hsz1
          by_cases hgt : nb.toInt > (srcs1[0]!.bytesInBuffer.toNat : Int)
          · have hcond : C.run (do
                let src ← C.Ptr.load dcs[0]!.src
                if nb.toInt > Int.ofNat src.bytesInBuffer.toNat then return (true, nb) else return (false, nb)) h1 =
                .ok ((true, nb), h1) := by
              rw [hsrcp, C.run_bind, hl1]; dsimp only; simp only [show nb.toInt > Int.ofNat srcs1[0]!.bytesInBuffer.toNat from hgt, ↓reduceIte]; rfl
            refine ⟨true, nb, h1, hcond, ?_⟩
            simp only [↓reduceIte]
            have hfillMem : srcs1[0]!.fillInputBuffer = .fn "fill_mem_input_buffer" := by
              rcases hfill1 with hm | ⟨_, hsusp⟩
              · exact hm
              · have hbad : FnPtr.fn "suspend_skip_input_data" = FnPtr.fn "skip_input_data" := hsusp.symm.trans hsk1
                injection hbad with hs
                exact absurd hs (by decide)
            have hfillEq : (srcs1[0]!.fillInputBuffer == .fn "fill_mem_input_buffer") = true := by simp [hfillMem]
            have hbd1 : ∀ errs1, C.Space.get h1 ctx.rerr = some errs1 → 0 < errs1.size →
                errs1[0]!.numWarnings.toInt + 1 < 2 ^ 63 := by
              intro errs1 hge1 hsze1
              obtain ⟨errs0, hg0, hsz0, _⟩ := parserEnv_get_err hp
              obtain ⟨_, hle⟩ := hnw1 errs0 errs1 hg0 hsz0 hge1
              have := hbd errs0 hg0 hsz0
              omega
            obtain ⟨h2, hw2, hp2, hd2, hmr2, hma2, hcp2, hq2, hhu2, hsm2, hby2, hme2, hco2, hsrc2, hnw2⟩ :=
              fill_mem_input_buffer_parser hp1 hbd1
            let nb' := Int64.ofInt (nb.toInt - (srcs1[0]!.bytesInBuffer.toNat : Int))
            have hgt' : (srcs1[0]!.bytesInBuffer.toNat : Int) < nb.toInt := hgt
            have hbLt' : srcs1[0]!.bytesInBuffer.toNat < 2 ^ 20 := hcur1.1
            have hnb'To : nb'.toInt = nb.toInt - (srcs1[0]!.bytesInBuffer.toNat : Int) := by
              change (Int64.ofInt _).toInt = _
              rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
              exact Int.bmod_eq_of_le (by omega) (by omega)
            obtain ⟨srcs2, hg2, hsz2, _his2, _hts2, hsip2, _hrtr2, hfill2, _⟩ := parserEnv_get_src hp2
            obtain ⟨_, hnib2, hbib2, hskEq⟩ := hsrc2 srcs2 hg2
            let k' : Nat := 2 * nb'.toInt.toNat + (if srcs2[0]!.bytesInBuffer.toNat < 2 then 1 else 0)
            have hbib2Eq : srcs2[0]!.bytesInBuffer.toNat = 2 := by rw [hbib2]; decide
            have hk'Lt : k' < k := by
              dsimp only [k']
              rw [hbib2Eq]
              have hnotlt : ¬(2 < 2) := by omega
              simp only [hnotlt, ↓reduceIte]
              split at hk1 <;> omega
            refine ⟨k', nb', h2, ?_, hk'Lt, ?_⟩
            · rw [hsrcp, C.run_bind, hl1]; dsimp only; simp only [hfillEq, ↓reduceIte, C.run_bind, hw2]; rfl
            · refine ⟨hp2, by omega, by omega, hd2.trans hd1, hmr2.trans hmr1, hma2.trans hma1,
                hcp2.trans hcp1, hq2.trans hq1, hhu2.trans hhu1, hsm2.trans hsm1, hby2.trans hby1, hme2.trans hme1, hco2.trans hco1, ?_⟩
              intro srcs2' hg2' hsz2'
              have heq2' := Option.some.inj (hg2'.symm.trans hg2); subst heq2'
              obtain ⟨_, hnib2', _, hskEq⟩ := hsrc2 srcs2' hg2
              have hsk2 : srcs2'[0]!.skipInputData = .fn "skip_input_data" := by
                rw [hskEq srcs1 hg1 hsz1, hsk1]
              refine ⟨hsk2, rfl, (fun hne => by rw [hnib2'] at hne; cases hne), ?_⟩
              intro errs0 errs2 hg0 hsz0 hge2
              obtain ⟨errs1, hge1, hsze1, _⟩ := parserEnv_get_err hp1
              obtain ⟨_, hnwLe1⟩ := hnw1 errs0 errs1 hg0 hsz0 hge1
              obtain ⟨hsze2, hnwEq2⟩ := hnw2 errs1 errs2 hge1 hsze1 hge2
              refine ⟨hsze2, ?_⟩
              rw [hnwEq2, hbib2Eq]
              have hnotlt : ¬((2 : Nat) < 2) := by omega
              simp only [hnotlt, ↓reduceIte]
              split at hnwLe1
              · have : nb'.toInt / 2 ≤ nb.toInt / 2 := by omega
                omega
              · have hb2 : 2 ≤ (srcs1[0]!.bytesInBuffer.toNat : Int) := by omega
                have : nb'.toInt / 2 ≤ nb.toInt / 2 - 1 := by omega
                omega
          · have hcond : C.run (do
                let src ← C.Ptr.load dcs[0]!.src
                if nb.toInt > Int.ofNat src.bytesInBuffer.toNat then return (true, nb) else return (false, nb)) h1 =
                .ok ((false, nb), h1) := by
              rw [hsrcp, C.run_bind, hl1]; dsimp only; simp only [show ¬(nb.toInt > Int.ofNat srcs1[0]!.bytesInBuffer.toNat) from hgt, ↓reduceIte]; rfl
            refine ⟨false, nb, h1, hcond, ?_⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨hp1, hnb0, hnbLe, hd1, hmr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1,
              ⟨srcs1, hg1, hsz1, by omega, hnoEof1⟩, ?_⟩
            intro errs0 errs1 hg0 hsz0 hge1
            obtain ⟨hsz1', hle⟩ := hnw1 errs0 errs1 hg0 hsz0 hge1
            refine ⟨hsz1', ?_⟩
            split at hle <;> omega)
        hk0Lt hinit
    rcases hpost with ⟨hp1, hrem0, hremLe, hd1, hmr1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1, ⟨srcs1, hg1, hsz1, hremLeBib, hnoEof1⟩, hnw1⟩
    obtain ⟨srcs1', hg1', hsz1', his1, hts1, hsip1, hrtr1, hfill1, hbib1Lt, hbib1Live, hce1⟩ :=
      parserEnv_get_src hp1
    have hs1Eq : srcs1' = srcs1 := Option.some.inj (hg1'.symm.trans hg1)
    rw [hs1Eq] at hbib1Lt hbib1Live hce1
    have hremLeBib' : rem.toInt ≤ (srcs1[0]!.bytesInBuffer.toNat : Int) := hremLeBib
    have hbib1Pos : 0 < srcs1[0]!.bytesInBuffer.toNat := by omega
    have hbib1Ne : srcs1[0]!.bytesInBuffer ≠ 0 := fun hz => by
      have := congrArg UInt64.toNat hz; change srcs1[0]!.bytesInBuffer.toNat = 0 at this; omega
    rcases hbib1Live with h0 | ⟨r, off, data, hpNib, hgB, hlenB⟩
    · exact False.elim (hbib1Ne h0)
    · have hof : Int.ofNat rem.toInt.toNat = (rem.toInt.toNat : Int) := rfl
      have haddB := ptr_add_ok (r := r) (off := off) (k := Int.ofNat rem.toInt.toNat) hgB
        (by omega) (by rw [hof]; omega) (by rw [hof]; omega)
      have hl1 := ptr_load_ok (r := ctx.rs) (off := 0) hg1 hsz1
      have hroSrc : C.Space.ro h1 ctx.rs = false := by cases ctx.rs; rfl
      let remU : UInt64 := rem.toInt.toNat.toUInt64
      have hremULt : remU.toNat = rem.toInt.toNat := by
        change rem.toInt.toNat.toUInt64.toNat = rem.toInt.toNat
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      have hsubBib : (srcs1[0]!.bytesInBuffer - remU).toNat = srcs1[0]!.bytesInBuffer.toNat - rem.toInt.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hremULt]
      let nextP : C.BPtr := .ref r (off + rem.toInt.toNat)
      let src' : C.JpegSourceMgr := {
        srcs1[0]! with nextInputByte := nextP, bytesInBuffer := srcs1[0]!.bytesInBuffer - remU
      }
      have hst := ptr_store_ok (r := ctx.rs) (off := 0) (v := src') hg1 hroSrc hsz1
      have hcv' : CurValid h1 nextP (srcs1[0]!.bytesInBuffer - remU) := by
        refine ⟨by omega, ?_, ?_⟩
        · by_cases hz : srcs1[0]!.bytesInBuffer - remU = 0
          · left; exact hz
          · right; exact ⟨r, off + rem.toInt.toNat, data, rfl, hgB, by omega⟩
        · intro o' ho'
          rw [show nextP = .ref r (off + rem.toInt.toNat) from rfl] at ho'
          cases ho'
          have := hce1 off hpNib; omega
      let h2 := C.Space.put h1 ctx.rs (srcs1.set! 0 src')
      have hp2 : ParserEnv ctx h2 := parserEnv_put_src hp1 hg1 hsz1 rfl rfl rfl rfl rfl hcv'
      refine ⟨h2, ?_, hp2,
        (by cases ctx.rs; exact hd1), (by cases ctx.rs; exact hmr1), (by cases ctx.rs; exact hma1),
        (by cases ctx.rs; exact hcp1), (by cases ctx.rs; exact hq1), (by cases ctx.rs; exact hhu1),
        (by cases ctx.rs; exact hsm1), (by cases ctx.rs; exact hby1), (by cases ctx.rs; exact hme1),
        (by cases ctx.rs; exact hco1), ?_, ?_⟩
      · unfold skip_input_data
        rw [C.run_bind, hldc]; dsimp only
        simp only [hpos, ↓reduceIte]
        rw [C.run_bind, hloop]; dsimp only
        rw [C.run_bind, hsrcp, hl1]; dsimp only
        rw [hpNib, C.run_bind, haddB]; dsimp only
        have hnatEq : (↑off + Int.ofNat rem.toInt.toNat).toNat = off + rem.toInt.toNat := by rw [hof]; omega
        rw [hnatEq]; exact hst
      · intro errs0 errs2 hg0 hsz0 hg2
        have hg2' : C.Space.get h1 ctx.rerr = some errs2 := by
          have herrEq : h2.errMgrs = h1.errMgrs := by rcases hrs : ctx.rs with ⟨bs⟩; rfl
          rcases hr : ctx.rerr with ⟨be⟩; simp only [C.Space.get, hr] at hg2 ⊢; rw [← herrEq]; exact hg2
        exact hnw1 errs0 errs2 hg0 hsz0 hg2'
      · intro srcs0' srcs2' hg0' _ hg2' _
        have heq0' := Option.some.inj (hg0'.symm.trans hgsrc0); subst heq0'
        have hgs2' : C.Space.get h2 ctx.rs = some (srcs1.set! 0 src') := by
          rcases hrs : ctx.rs with ⟨bs⟩; simp [h2, C.Space.get, C.Space.put, hrs]
        have heq2' := Option.some.inj (hg2'.symm.trans hgs2'); subst heq2'
        have h0_2 : (srcs1.set! 0 src')[0]! = src' := set0_bang srcs1 hsz1 src'
        have hceEq : isConstEofPtr src'.nextInputByte = isConstEofPtr srcs1[0]!.nextInputByte := by
          rw [hpNib]; change isConstEofPtr (.ref r (off + rem.toInt.toNat)) = isConstEofPtr (.ref r off)
          cases r <;> rfl
        rw [h0_2, hceEq]
        refine ⟨?_, ?_⟩
        · intro htrue
          by_cases hf : isConstEofPtr srcs1[0]!.nextInputByte = false
          · obtain ⟨hf0, _⟩ := hnoEof1 hf; rw [htrue] at hf0; cases hf0
          · cases hcf : isConstEofPtr srcs1[0]!.nextInputByte <;> simp_all
        · intro hfalse
          obtain ⟨hf0, hble, herrEq⟩ := hnoEof1 hfalse
          refine ⟨hf0, by dsimp only [src']; omega, ?_⟩
          intro errs0 errs2 hge0 hsze0 hge2 hsze2
          have hge2' : C.Space.get h1 ctx.rerr = some errs2 := by
            have hh : h2.errMgrs = h1.errMgrs := by rcases hrs : ctx.rs with ⟨bs⟩; rfl
            rcases hr : ctx.rerr with ⟨be⟩; simp only [C.Space.get, hr] at hge2 ⊢; rw [← hh]; exact hge2
          exact herrEq errs0 errs2 hge0 hsze0 hge2' hsze2
  · refine ⟨h, ?_, hp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · unfold skip_input_data; rw [C.run_bind, hldc]; dsimp only; simp only [hpos, ↓reduceIte]; rfl
    · intro errs0 errs1 hg0 hsz0 hg1
      have := Option.some.inj (hg1.symm.trans hg0); subst this; exact ⟨hsz0, by omega⟩
    · intro srcs0' srcs1' hg0' _ hg1' _
      have := Option.some.inj (hg1'.symm.trans hg0'); subst this
      refine ⟨id, fun hfalse => ⟨hfalse, Nat.le_refl _, ?_⟩⟩
      intro errs0 errs1 hge0 _ hge1 _; rw [Option.some.inj (hge1.symm.trans hge0)]

theorem skipInputDataDispatch_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (numBytes : Int64) (hnum : numBytes.toInt ≤ 65535)
    (hbd : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 2 ^ 16 < 2 ^ 63) :
    ∃ h',
      C.run (skipInputDataDispatch (.ref (.decomp ctx.bdc) 0) numBytes) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 1 + 65535 / 2) ∧
      (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
        (isConstEofPtr srcs0[0]!.nextInputByte = true → isConstEofPtr srcs'[0]!.nextInputByte = true) ∧
        (isConstEofPtr srcs'[0]!.nextInputByte = false →
          isConstEofPtr srcs0[0]!.nextInputByte = false ∧
          srcs'[0]!.bytesInBuffer.toNat ≤ srcs0[0]!.bytesInBuffer.toNat ∧
          ∀ errs0 errs1, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
            C.Space.get h' ctx.rerr = some errs1 → 0 < errs1.size →
            errs1[0]!.numWarnings.toInt = errs0[0]!.numWarnings.toInt)) := by
  obtain ⟨dcs, hgdc, hszdc, _, _, _, _, _, hsrcp⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _his, _hts, hsip, _⟩ := parserEnv_get_src hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc hszsrc
  rcases hsip with hsk | hsusp
  · obtain ⟨h', hrun, hp', hd, hmr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw, hsm2⟩ :=
      skip_input_data_parser hp numBytes ⟨srcs, hgsrc, hszsrc, hsk⟩ hnum hbd
    refine ⟨h', ?_, hp', hd, hmr, hma, hcp, hq, hhu, hsm, hby, hme, hco, hnw, hsm2⟩
    unfold skipInputDataDispatch
    rw [C.run_bind, hldc]; dsimp only
    rw [hsrcp, C.run_bind, hlsrc]; dsimp only
    have heq : (srcs[0]!.skipInputData == .fn "skip_input_data") = true := by simp [hsk]
    simp only [heq, ↓reduceIte]; exact hrun
  · refine ⟨h, ?_, hp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · unfold skipInputDataDispatch
      rw [C.run_bind, hldc]; dsimp only
      rw [hsrcp, C.run_bind, hlsrc]; dsimp only
      have hne : (srcs[0]!.skipInputData == .fn "skip_input_data") = false := by simp [hsusp]
      have heq : (srcs[0]!.skipInputData == .fn "suspend_skip_input_data") = true := by simp [hsusp]
      simp only [hne, Bool.false_eq_true, ↓reduceIte, heq]; rfl
    · intro errs errs' hg0 hsz0 hg1
      have := Option.some.inj (hg1.symm.trans hg0); subst this; exact ⟨hsz0, by omega⟩
    · intro srcs0' srcs1' hg0' _ hg1' _
      have := Option.some.inj (hg1'.symm.trans hg0'); subst this
      refine ⟨id, fun hfalse => ⟨hfalse, Nat.le_refl _, ?_⟩⟩
      intro errs0 errs1 hge0 _ hge1 _; rw [Option.some.inj (hge1.symm.trans hge0)]

/-! ## Allocation helpers preserving `ParserEnv` -/

theorem parserEnv_put_nalloc {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) (n' : Nat) :
    ParserEnv ctx { h with nalloc := n' } := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  exact ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩

theorem parserEnv_put_mem_pool {ctx : IoCtx} {h : C.Heap} {mems : Array C.JpegMemMgr}
    {pid : Nat} {pa' : C.PoolAllocs} {tsa' : UInt64}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.rmem = some mems) (hsz : 0 < mems.size)
    (hpid : pid < 2)
    (hpm : pa'.masters = mems[0]!.poolAllocs[pid]!.masters)
    (hpi : pa'.inputctls = mems[0]!.poolAllocs[pid]!.inputctls)
    (hpmk : pa'.markers = mems[0]!.poolAllocs[pid]!.markers)
    (hps : pa'.srcs = mems[0]!.poolAllocs[pid]!.srcs) :
    ParserEnv ctx (C.Space.put h ctx.rmem (mems.set! 0
      { mems[0]! with poolAllocs := mems[0]!.poolAllocs.set! pid pa', totalSpaceAllocated := tsa' })) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems0, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm0, hpi0, hpmk0, hps0,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hmEq : mems = mems0 := Option.some.inj (hg.symm.trans hgmem)
  rw [hmEq] at hsz hpm hpi hpmk hps
  let mem' : C.JpegMemMgr := {
    mems0[0]! with poolAllocs := mems0[0]!.poolAllocs.set! pid pa', totalSpaceAllocated := tsa'
  }
  let h' := C.Space.put h ctx.rmem (mems0.set! 0 mem')
  have hmemEq : (mems0.set! 0 mem')[0]! = mem' := set0_bang mems0 hsz mem'
  have hpas : (mem'.poolAllocs).size = 2 := by
    change (mems0[0]!.poolAllocs.set! pid pa').size = 2
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hpaSz
  have hpa1_mas : mem'.poolAllocs[1]!.masters = mems0[0]!.poolAllocs[1]!.masters := by
    change (mems0[0]!.poolAllocs.set! pid pa')[1]!.masters = _
    by_cases hp1 : pid = 1
    · subst hp1; rw [set_bang_self _ (by omega) pa']; exact hpm
    · rw [set_bang_ne _ (by omega) (by omega) (Ne.symm hp1)]
  have hpa1_ic : mem'.poolAllocs[1]!.inputctls = mems0[0]!.poolAllocs[1]!.inputctls := by
    change (mems0[0]!.poolAllocs.set! pid pa')[1]!.inputctls = _
    by_cases hp1 : pid = 1
    · subst hp1; rw [set_bang_self _ (by omega) pa']; exact hpi
    · rw [set_bang_ne _ (by omega) (by omega) (Ne.symm hp1)]
  have hpa1_mk : mem'.poolAllocs[1]!.markers = mems0[0]!.poolAllocs[1]!.markers := by
    change (mems0[0]!.poolAllocs.set! pid pa')[1]!.markers = _
    by_cases hp1 : pid = 1
    · subst hp1; rw [set_bang_self _ (by omega) pa']; exact hpmk
    · rw [set_bang_ne _ (by omega) (by omega) (Ne.symm hp1)]
  have hpa1_sr : mem'.poolAllocs[1]!.srcs = mems0[0]!.poolAllocs[1]!.srcs := by
    change (mems0[0]!.poolAllocs.set! pid pa')[1]!.srcs = _
    by_cases hp1 : pid = 1
    · subst hp1; rw [set_bang_self _ (by omega) pa']; exact hps
    · rw [set_bang_ne _ (by omega) (by omega) (Ne.symm hp1)]
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · exact ⟨dcs, dc, dcs, dc, hgdc, hszdc, hdc, by cases ctx.rmem; exact hgdc, hszdc, hdc,
        rfl, rfl, rfl, rfl, rfl⟩
    · intro _ a hga hsza; cases ctx.rmem; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; cases ctx.rmem; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; cases ctx.rmem; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; cases ctx.rmem; exact ⟨a, hga, hsza⟩
    · intro rm1 ms1 hgm1 hszm1 hpa1
      rcases hr : ctx.rmem with ⟨bm⟩; rcases rm1 with ⟨bm1⟩
      by_cases heq : bm1 = bm
      · subst heq; simp only [C.Space.get, hr] at hg hgm1
        have hmsEq := Option.some.inj (hgm1.symm.trans hg); subst hmsEq
        rw [hmEq]
        exact ⟨mems0.set! 0 mem', by simp [h', C.Space.get, C.Space.put, hr], by simpa using hsz,
          by rw [hmemEq, hpas]; omega, by rw [hmemEq, hpa1_mas]⟩
      · refine ⟨ms1, by simpa [h', C.Space.get, C.Space.put, hr, C.upd_ne _ _ _ _ heq] using hgm1,
          hszm1, hpa1, rfl⟩
  have hfr' : FreshNextBlk h' := by
    intro k hk; obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hfr k hk
    refine ⟨by cases ctx.rmem; exact h1, by cases ctx.rmem; exact h2, ?_,
      by cases ctx.rmem; exact h4, by cases ctx.rmem; exact h5, by cases ctx.rmem; exact h6,
      by cases ctx.rmem; exact h7, by cases ctx.rmem; exact h8, by cases ctx.rmem; exact h9,
      by cases ctx.rmem; exact h10, by cases ctx.rmem; exact h11⟩
    rcases hr : ctx.rmem with ⟨bm⟩
    by_cases heq : k = bm
    · subst heq; simp only [C.Space.get, hr] at hg; rw [h3] at hg; cases hg
    · simp only [h', C.Space.put, hr]; rw [C.upd_ne _ _ _ _ heq]; exact h3
  rw [hmEq]
  refine ⟨hcore', hfr', dcs, dc, errs, mems0.set! 0 mem', masters, ics, mrks, srcs,
    by cases ctx.rmem; exact hgdc, hszdc, hdc, herrp, by cases ctx.rmem; exact hgerr, hszerr, hrem, hnw0,
    hmemp, by simp [C.Space.get, C.Space.put]; rfl, by simpa using hsz,
    by rw [hmemEq]; exact has, by rw [hmemEq]; exact hfp, by rw [hmemEq]; exact hsd,
    by rw [hmemEq]; exact hlpSz, by rw [hmemEq]; exact hlp0, by rw [hmemEq]; exact hlp1,
    by rw [hmemEq]; exact hpas, by rw [hmemEq, hpa1_mas]; exact hpm0,
    by rw [hmemEq, hpa1_ic]; exact hpi0, by rw [hmemEq, hpa1_mk]; exact hpmk0,
    by rw [hmemEq, hpa1_sr]; exact hps0,
    hmasp, by cases ctx.rmem; exact hgmas, hszmas, hicp, by cases ctx.rmem; exact hgic, hszic, hric, hci,
    hmrkp, by cases ctx.rmem; exact hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, by cases ctx.rmem; exact hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩

theorem parserEnv_alloc_comps {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) (n : Nat) :
    let b := h.nextBlk
    let h' := { h with comps := C.upd h.comps b (some (Array.replicate n default)), nextBlk := b + 1, nalloc := h.nalloc + 1 }
    ParserEnv ctx h' ∧
    C.Space.get h' (C.CompRef.comp b) = some (Array.replicate n default) ∧
    LiveCompArray h' (.ref (.comp b) 0) n := by
  intro b h'
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hfr' : FreshNextBlk h' := by
    intro k hk
    dsimp only [h', b] at hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hfr k (by omega)
    refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h9, h10, h11⟩
    simp only [h', b]; rw [C.upd_ne _ _ _ _ (by omega)]; exact h8
  have hcompLive' : dc.compInfo ≠ .null →
      0 ≤ dc.numComponents.toInt ∧ LiveCompArray h' dc.compInfo dc.numComponents.toInt.toNat := by
    intro hne
    obtain ⟨hn0, r1, cs1, hp1, hg1, hsz1⟩ := hcompLive hne
    refine ⟨hn0, r1, cs1, hp1, ?_, hsz1⟩
    rcases r1 with ⟨b1⟩
    have hnone : h.comps b = none := (hfr b (Nat.le_refl _)).2.2.2.2.2.2.2.1
    have hneB : b1 ≠ b := fun hEq => by subst hEq; simp only [C.Space.get] at hg1; rw [hnone] at hg1; cases hg1
    simp only [h', C.Space.get]; rw [C.upd_ne _ _ _ _ hneB]; exact hg1
  have hgNew : C.Space.get h' (C.CompRef.comp b) = some (Array.replicate n default) := by
    simp only [h', C.Space.get]; exact C.upd_same _ _ _
  refine ⟨⟨hcore, hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive', hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩,
    hgNew, ⟨.comp b, Array.replicate n default, rfl, hgNew, by simp⟩⟩

theorem parserEnv_alloc_quant {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    let b := h.nextBlk
    let h' := { h with quants := C.upd h.quants b (some #[default]), nextBlk := b + 1, nalloc := h.nalloc + 1 }
    ParserEnv ctx h' ∧
    C.Space.get h' (C.QuantRef.quant b) = some #[default] := by
  intro b h'
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hfr' : FreshNextBlk h' := by
    intro k hk
    dsimp only [h', b] at hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hfr k (by omega)
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, h10, h11⟩
    simp only [h', b]; rw [C.upd_ne _ _ _ _ (by omega)]; exact h9
  have hqt' : ∀ i < 4, dc.quantTblPtrs[i]! = .null ∨
      ∃ rq off qs, dc.quantTblPtrs[i]! = .ref rq off ∧ C.Space.get h' rq = some qs ∧ off < qs.size := by
    intro i hi
    rcases hqt i hi with hn | ⟨rq, off, qs, hp1, hg1, hsz1⟩
    · left; exact hn
    · right; rcases rq with ⟨b1⟩
      have hnone : h.quants b = none := (hfr b (Nat.le_refl _)).2.2.2.2.2.2.2.2.1
      have hne : b1 ≠ b := fun hEq => by subst hEq; simp only [C.Space.get] at hg1; rw [hnone] at hg1; cases hg1
      exact ⟨.quant b1, off, qs, hp1, by simp only [h', C.Space.get]; rw [C.upd_ne _ _ _ _ hne]; exact hg1, hsz1⟩
  have hgNew : C.Space.get h' (C.QuantRef.quant b) = some #[default] := by
    simp only [h', C.Space.get]; exact C.upd_same _ _ _
  refine ⟨⟨hcore, hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt', hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩, hgNew⟩

theorem parserEnv_alloc_huff {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    let b := h.nextBlk
    let h' := { h with huffs := C.upd h.huffs b (some #[default]), nextBlk := b + 1, nalloc := h.nalloc + 1 }
    ParserEnv ctx h' ∧
    C.Space.get h' (C.HuffRef.huff b) = some #[default] := by
  intro b h'
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hfr' : FreshNextBlk h' := by
    intro k hk
    dsimp only [h', b] at hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hfr k (by omega)
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, h11⟩
    simp only [h', b]; rw [C.upd_ne _ _ _ _ (by omega)]; exact h10
  have hnone : h.huffs b = none := (hfr b (Nat.le_refl _)).2.2.2.2.2.2.2.2.2.1
  have hdh' : ∀ i < 4, dc.dcHuffTblPtrs[i]! = .null ∨
      ∃ rh off hs, dc.dcHuffTblPtrs[i]! = .ref rh off ∧ C.Space.get h' rh = some hs ∧ off < hs.size := by
    intro i hi
    rcases hdh i hi with hn | ⟨rh, off, hs1, hp1, hg1, hsz1⟩
    · left; exact hn
    · right; rcases rh with ⟨b1⟩
      have hne : b1 ≠ b := fun hEq => by subst hEq; simp only [C.Space.get] at hg1; rw [hnone] at hg1; cases hg1
      exact ⟨.huff b1, off, hs1, hp1, by simp only [h', C.Space.get]; rw [C.upd_ne _ _ _ _ hne]; exact hg1, hsz1⟩
  have hah' : ∀ i < 4, dc.acHuffTblPtrs[i]! = .null ∨
      ∃ rh off hs, dc.acHuffTblPtrs[i]! = .ref rh off ∧ C.Space.get h' rh = some hs ∧ off < hs.size := by
    intro i hi
    rcases hah i hi with hn | ⟨rh, off, hs1, hp1, hg1, hsz1⟩
    · left; exact hn
    · right; rcases rh with ⟨b1⟩
      have hne : b1 ≠ b := fun hEq => by subst hEq; simp only [C.Space.get] at hg1; rw [hnone] at hg1; cases hg1
      exact ⟨.huff b1, off, hs1, hp1, by simp only [h', C.Space.get]; rw [C.upd_ne _ _ _ _ hne]; exact hg1, hsz1⟩
  have hgNew : C.Space.get h' (C.HuffRef.huff b) = some #[default] := by
    simp only [h', C.Space.get]; exact C.upd_same _ _ _
  refine ⟨⟨hcore, hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh', hahSz, hah', hccSz, hisn0⟩, hgNew⟩

theorem parserEnv_alloc_savedMarker {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) (limit : Nat) :
    let b := h.nextBlk
    let h' := {
      h with
      savedMarkers := C.upd h.savedMarkers b (some #[default])
      bytes := C.upd h.bytes (b + 1) (some (Array.replicate limit 0))
      nextBlk := b + 2
      nalloc := h.nalloc + 1
    }
    ParserEnv ctx h' ∧
    C.Space.get h' (C.SavedMarkerRef.savedMarker b) = some #[default] ∧
    WritableBytes h' (.ref (.heap (b + 1)) 0) limit := by
  intro b h'
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hfr' : FreshNextBlk h' := by
    intro k hk
    dsimp only [h', b] at hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hfr k (by omega)
    refine ⟨?_, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
    · simp only [h', b]; rw [C.upd_ne _ _ _ _ (by omega)]; exact h1
    · simp only [h', b]; rw [C.upd_ne _ _ _ _ (by omega)]; exact h11
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · exact ⟨dcs, dc, dcs, dc, hgdc, hszdc, hdc, hgdc, hszdc, hdc, rfl, rfl, rfl, rfl, rfl⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ ms hgm hszm hpa; exact ⟨ms, hgm, hszm, hpa, rfl⟩
  have hbNoneB : h.bytes (b + 1) = none := (hfr (b + 1) (by dsimp only [b]; omega)).1
  have hbNoneSm : h.savedMarkers b = none := (hfr b (Nat.le_refl _)).2.2.2.2.2.2.2.2.2.2
  have hcurv' : CurValid h' srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer := by
    rcases hcurv with ⟨hblt, hblive, hce⟩
    refine ⟨hblt, ?_, hce⟩
    rcases hblive with hz | ⟨rb, boff, bdata, hpB, hgB, hblen⟩
    · left; exact hz
    · right; cases rb with
      | heap bb =>
        have hne : bb ≠ b + 1 := fun hEq => by subst hEq; simp only [C.Space.get, C.Heap.getBytes] at hgB; rw [hbNoneB] at hgB; cases hgB
        exact ⟨.heap bb, boff, bdata, hpB, by simp only [h', C.Space.get, C.Heap.getBytes]; rw [C.upd_ne _ _ _ _ hne]; exact hgB, hblen⟩
      | const c => exact ⟨.const c, boff, bdata, hpB, hgB, hblen⟩
      | const_eof => exact ⟨.const_eof, boff, bdata, hpB, hgB, hblen⟩
      | str s => exact ⟨.str s, boff, bdata, hpB, hgB, hblen⟩
  have hcurm' : mrks[0]!.curMarker = .null ∨ ∃ rsm off sms sm,
      mrks[0]!.curMarker = .ref rsm off ∧ C.Space.get h' rsm = some sms ∧ off < sms.size ∧
      sm = sms[off]! ∧ sm.dataLength.toNat ≤ 65535 ∧ sm.originalLength.toNat ≤ 65535 ∧
      WritableBytes h' sm.data sm.dataLength.toNat ∧ mrks[0]!.bytesRead ≤ sm.dataLength := by
    rcases hcurm with hnull | ⟨rsm, off, sms, sm, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · left; exact hnull
    · right
      rcases rsm with ⟨bsm⟩
      have hneS : bsm ≠ b := fun hEq => by subst hEq; simp only [C.Space.get] at h2; rw [hbNoneSm] at h2; cases h2
      refine ⟨.savedMarker bsm, off, sms, sm, h1,
        by simp only [h', C.Space.get]; rw [C.upd_ne _ _ _ _ hneS]; exact h2, h3, h4, h5, h6, ?_, h8⟩
      rcases h7 with ⟨bh, boff, bdata, hpB, hgB, hblen⟩
      have hneB : bh ≠ b + 1 := fun hEq => by subst hEq; rw [hbNoneB] at hgB; cases hgB
      exact ⟨bh, boff, bdata, hpB, by simp only [h']; rw [C.upd_ne _ _ _ _ hneB]; exact hgB, hblen⟩
  have hmlEnd' : dc.markerList = .null ∨ masters[0]!.markerListEnd = .null ∨
      ∃ rsm off sms, masters[0]!.markerListEnd = .ref rsm off ∧ C.Space.get h' rsm = some sms ∧ off < sms.size := by
    rcases hmlEnd with h1 | h2 | ⟨rsm, off, sms, h1, h2, h3⟩
    · left; exact h1
    · right; left; exact h2
    · right; right; rcases rsm with ⟨bsm⟩
      have hneS : bsm ≠ b := fun hEq => by subst hEq; simp only [C.Space.get] at h2; rw [hbNoneSm] at h2; cases h2
      exact ⟨.savedMarker bsm, off, sms, h1,
        by simp only [h', C.Space.get]; rw [C.upd_ne _ _ _ _ hneS]; exact h2, h3⟩
  have hgSm : C.Space.get h' (C.SavedMarkerRef.savedMarker b) = some #[default] := by
    simp only [h', C.Space.get]; exact C.upd_same _ _ _
  have hgBy : h'.bytes (b + 1) = some (Array.replicate limit 0) := by
    simp only [h']; exact C.upd_same _ _ _
  refine ⟨⟨hcore', hfr', dcs, dc, errs, mems, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv',
    hcurm', hmlEnd', hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩,
    hgSm, ⟨b + 1, 0, Array.replicate limit 0, rfl, hgBy, by simp⟩⟩

private theorem round_up_pow2_le (a : UInt64) (ha : a.toNat ≤ 10000000) :
    (round_up_pow2 a ALIGN_SIZE).toNat ≤ a.toNat + 7 := by
  unfold round_up_pow2 ALIGN_SIZE
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have ha8 : (a + 8).toNat = a.toNat + 8 := by
    rw [UInt64.toNat_add, h8, Nat.mod_eq_of_lt (by omega)]
  have h1 : (a + 8 - 1).toNat = a.toNat + 7 := by
    rw [UInt64.toNat_sub_of_le (a + 8) 1 (UInt64.le_iff_toNat_le.mpr (by rw [ha8]; change 1 ≤ a.toNat + 8; omega)), ha8]
    change a.toNat + 8 - 1 = a.toNat + 7
    omega
  have hle : ((a + 8 - 1) &&& (~~~((8 : UInt64) - 1))).toNat ≤ (a + 8 - 1).toNat := by
    change ((a + 8 - 1).toBitVec &&& (~~~((8 : UInt64) - 1)).toBitVec).toNat ≤ (a + 8 - 1).toNat
    rw [BitVec.toNat_and]
    exact Nat.and_le_left
  omega

private theorem allocSmallCore_parser {R : Type} [DecidableEq R] {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (pool_id : Int32) (sizeofobject : UInt64)
    (hpid : pool_id = JPOOL_PERMANENT ∨ pool_id = JPOOL_IMAGE)
    (hsz : sizeofobject.toNat ≤ 10000000)
    (allocFn : C.M (C.Ptr R)) (recordFn : C.PoolAllocs → C.Ptr R → C.PoolAllocs)
    (Pred : C.Heap → Prop) (PostOk : C.Ptr R → C.Heap → Prop)
    (hPred0 : Pred h)
    (hStep : ∀ h1, ParserEnv ctx h1 → Pred h1 →
      (∃ h_fail, C.run allocFn h1 = .ok (.null, h_fail) ∧ ParserEnv ctx h_fail ∧ Pred h_fail) ∨
      (∃ p h_ok, p ≠ .null ∧ C.run allocFn h1 = .ok (p, h_ok) ∧ ParserEnv ctx h_ok ∧ Pred h_ok ∧ PostOk p h_ok))
    (hPredPostMem : ∀ p h_ok h_post, Pred h_ok → PostOk p h_ok →
      h_post.decomps = h_ok.decomps → h_post.markers = h_ok.markers → h_post.srcs = h_ok.srcs →
      h_post.errMgrs = h_ok.errMgrs → h_post.masters = h_ok.masters → h_post.comps = h_ok.comps →
      h_post.quants = h_ok.quants → h_post.huffs = h_ok.huffs → h_post.savedMarkers = h_ok.savedMarkers →
      h_post.bytes = h_ok.bytes → h_post.consts = h_ok.consts → Pred h_post ∧ PostOk p h_post)
    (hRecMas : ∀ pa p, (recordFn pa p).masters = pa.masters)
    (hRecIc : ∀ pa p, (recordFn pa p).inputctls = pa.inputctls)
    (hRecMk : ∀ pa p, (recordFn pa p).markers = pa.markers)
    (hRecSrc : ∀ pa p, (recordFn pa p).srcs = pa.srcs)
    (PredErr : C.Heap → Prop)
    (hPredErrPost : ∀ h1 h2, Pred h1 → h2.decomps = h1.decomps → h2.markers = h1.markers →
      h2.comps = h1.comps → PredErr h2) :
    ∃ res h',
      C.run (allocSmallCore (.ref (.decomp ctx.bdc) 0) pool_id sizeofobject allocFn recordFn) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      match res with
      | .errExit _ => PredErr h'
      | .ok p => p ≠ .null ∧ Pred h' ∧ PostOk p h' := by
  obtain ⟨dcs, hgdc, hszdc, _, hmemp, _⟩ := parserEnv_get_dc hp
  obtain ⟨mems, hgmem, hszmem, _⟩ := parserEnv_get_mem hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlmem := ptr_load_ok (r := ctx.rmem) (off := 0) hgmem hszmem
  let maxChunkU : UInt64 := MAX_ALLOC_CHUNK.toInt.toNat.toUInt64
  let alignedSize := round_up_pow2 sizeofobject ALIGN_SIZE
  have hru : alignedSize.toNat ≤ sizeofobject.toNat + 7 := round_up_pow2_le sizeofobject hsz
  have hmck : maxChunkU.toNat = 1000000000 := by decide
  have hno1 : ¬(sizeofobject > maxChunkU) := fun hgt => by
    have hlt : maxChunkU.toNat < sizeofobject.toNat := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have hhdr : (sizeof_small_pool_hdr + alignedSize + ALIGN_SIZE - 1).toNat = 24 + alignedSize.toNat + 7 := by
    have h24 : sizeof_small_pool_hdr.toNat = 24 := by decide
    have h8 : ALIGN_SIZE.toNat = 8 := by decide
    have hsum1 : (sizeof_small_pool_hdr + alignedSize).toNat = 24 + alignedSize.toNat := by
      rw [UInt64.toNat_add, h24, Nat.mod_eq_of_lt (by omega)]
    have hsum2 : (sizeof_small_pool_hdr + alignedSize + ALIGN_SIZE).toNat = 24 + alignedSize.toNat + 8 := by
      rw [UInt64.toNat_add, hsum1, h8, Nat.mod_eq_of_lt (by omega)]
    rw [UInt64.toNat_sub_of_le _ 1 (UInt64.le_iff_toNat_le.mpr (by rw [hsum2]; change 1 ≤ 24 + alignedSize.toNat + 8; omega)), hsum2]
    change 24 + alignedSize.toNat + 8 - 1 = 24 + alignedSize.toNat + 7
    omega
  have hno2 : ¬(sizeof_small_pool_hdr + alignedSize + ALIGN_SIZE - 1 > maxChunkU) := fun hgt => by
    have hlt : maxChunkU.toNat < (sizeof_small_pool_hdr + alignedSize + ALIGN_SIZE - 1).toNat :=
      UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have hno3 : (pool_id < 0 || pool_id ≥ JPOOL_NUMPOOLS) = false := by
    rcases hpid with rfl | rfl <;> decide
  have hpidLt : pool_id.toInt.toNat < 2 := by
    rcases hpid with rfl | rfl <;> decide
  let pid := pool_id.toInt.toNat
  let remChunk := maxChunkU - (sizeof_small_pool_hdr + alignedSize + ALIGN_SIZE - 1)
  let initSlop := first_pool_slop[pid]!
  let slop := if initSlop > remChunk then remChunk else initSlop
  have hPredErr : ∀ h1, (ParserEnv ctx h1 ∧ Pred h1) →
      ∃ h_err, C.run (out_of_memory (.ref (.decomp ctx.bdc) 0) 2) h1 = .ok (.errExit JERR_OUT_OF_MEMORY, h_err) ∧
        ParserEnv ctx h_err ∧ PredErr h_err := by
    intro h1 ⟨hp1, hpr1⟩
    obtain ⟨dcs1, hgdc1, hszdc1, herrp1, _⟩ := parserEnv_get_dc hp1
    have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc1
    obtain ⟨h_err, hk, hp_err, hdE, hmkE, _, _, hcpE, _⟩ := errMsgUpdate_cont_parser hp1 JERR_OUT_OF_MEMORY (fun arr => arr.set! 0 2)
    refine ⟨h_err, ?_, hp_err, hPredErrPost h1 h_err hpr1 hdE hmkE hcpE⟩
    unfold out_of_memory
    rw [C.run_bind, hldc1]; dsimp only
    rw [herrp1]; unfold errexit1; exact hk (pure (JpegRes.errExit JERR_OUT_OF_MEMORY))
  have hSlop := allocSlopRetry_ok (.ref (.decomp ctx.bdc) 0) allocFn
    (fun h1 => ParserEnv ctx h1 ∧ Pred h1)
    (fun h_err => ParserEnv ctx h_err ∧ PredErr h_err)
    (fun p h_ok => ParserEnv ctx h_ok ∧ Pred h_ok ∧ PostOk p h_ok)
    hPredErr
    (fun h1 ⟨hp1, hpr1⟩ => hStep h1 hp1 hpr1)
    16 slop h ⟨hp, hPred0⟩
  rcases hSlop with ⟨h_err, herr_run, hp_err, herrPost⟩ | ⟨p, h_ok, hpne, hok_run, hp_ok, hpr_ok, hpost_ok⟩
  · refine ⟨.errExit JERR_OUT_OF_MEMORY, h_err, ?_, hp_err, herrPost⟩
    unfold allocSmallCore
    rw [C.run_bind, hldc]; dsimp only
    simp only [show ¬(sizeofobject > MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) from hno1,
      show ¬(sizeof_small_pool_hdr + round_up_pow2 sizeofobject ALIGN_SIZE + ALIGN_SIZE - 1 >
        MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) from hno2,
      ↓reduceIte, hno3, Bool.false_eq_true]
    rw [hmemp, C.run_bind, hlmem]; dsimp only
    rw [C.run_bind, herr_run]; rfl
  · obtain ⟨dcs2, hgdc2, hszdc2, _, hmemp2, _⟩ := parserEnv_get_dc hp_ok
    obtain ⟨mems2, hgmem2, hszmem2, _⟩ := parserEnv_get_mem hp_ok
    have hldc2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc2 hszdc2
    have hlmem2 := ptr_load_ok (r := ctx.rmem) (off := 0) hgmem2 hszmem2
    have hroMem2 : C.Space.ro h_ok ctx.rmem = false := by cases ctx.rmem; rfl
    let allocs2 := recordFn (mems2[0]!.poolAllocs[pid]!) p
    let mem2' : C.JpegMemMgr := {
      mems2[0]! with
      poolAllocs := mems2[0]!.poolAllocs.set! pid allocs2
      totalSpaceAllocated := mems2[0]!.totalSpaceAllocated + alignedSize
    }
    have hstMem2 := ptr_store_ok (r := ctx.rmem) (off := 0) (v := mem2') hgmem2 hroMem2 hszmem2
    let h' := C.Space.put h_ok ctx.rmem (mems2.set! 0 mem2')
    have hp' : ParserEnv ctx h' := parserEnv_put_mem_pool hp_ok hgmem2 hszmem2 hpidLt
      (hRecMas _ p) (hRecIc _ p) (hRecMk _ p) (hRecSrc _ p)
    obtain ⟨hpr', hpost'⟩ := hPredPostMem p h_ok h' hpr_ok hpost_ok
      (by cases ctx.rmem; rfl) (by cases ctx.rmem; rfl) (by cases ctx.rmem; rfl)
      (by cases ctx.rmem; rfl) (by cases ctx.rmem; rfl) (by cases ctx.rmem; rfl)
      (by cases ctx.rmem; rfl) (by cases ctx.rmem; rfl) (by cases ctx.rmem; rfl)
      (by cases ctx.rmem; rfl) (by cases ctx.rmem; rfl)
    refine ⟨.ok p, h', ?_, hp', hpne, hpr', hpost'⟩
    unfold allocSmallCore
    rw [C.run_bind, hldc]; dsimp only
    simp only [show ¬(sizeofobject > MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) from hno1,
      show ¬(sizeof_small_pool_hdr + round_up_pow2 sizeofobject ALIGN_SIZE + ALIGN_SIZE - 1 >
        MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) from hno2,
      ↓reduceIte, hno3, Bool.false_eq_true]
    rw [hmemp, C.run_bind, hlmem]; dsimp only
    rw [C.run_bind, hok_run]; dsimp only
    rw [C.run_bind, hldc2]; dsimp only
    rw [hmemp2, C.run_bind, hlmem2]; dsimp only
    rw [C.run_bind, hstMem2]; rfl

theorem alloc_small_comps_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (numComps : Nat) (hnc : numComps ≤ 25000) :
    ∃ res h',
      C.run (alloc_small_comps (.ref (.decomp ctx.bdc) 0) JPOOL_IMAGE numComps
        (UInt64.ofNat numComps * sizeof_jpeg_component_info)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      match res with
      | .errExit _ => h'.decomps = h.decomps ∧ h'.markers = h.markers
      | .ok p => p ≠ .null ∧
        h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧ h'.errMgrs = h.errMgrs ∧
        h'.masters = h.masters ∧ h'.quants = h.quants ∧ h'.huffs = h.huffs ∧
        h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧ h'.consts = h.consts ∧
        LiveCompArray h' p numComps := by
  have hszLt : (UInt64.ofNat numComps * sizeof_jpeg_component_info).toNat ≤ 10000000 := by
    have h96 : sizeof_jpeg_component_info.toNat = 96 := by decide
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat', h96]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  let Pred (h1 : C.Heap) : Prop :=
    h1.decomps = h.decomps ∧ h1.markers = h.markers ∧ h1.srcs = h.srcs ∧ h1.errMgrs = h.errMgrs ∧
    h1.masters = h.masters ∧ h1.quants = h.quants ∧ h1.huffs = h.huffs ∧
    h1.savedMarkers = h.savedMarkers ∧ h1.bytes = h.bytes ∧ h1.consts = h.consts
  let Post (p : C.CompPtr) (h1 : C.Heap) : Prop := LiveCompArray h1 p numComps
  unfold alloc_small_comps
  obtain ⟨res, h', hrun, hp', hres⟩ := allocSmallCore_parser hp JPOOL_IMAGE _ (Or.inr rfl) hszLt
    (C.allocComps numComps)
    (fun pa p => match p with | .ref (.comp b) _ => { pa with comps := pa.comps.push b } | .null => pa)
    Pred Post ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun h1 hp1 ⟨hd1, hmr1, hsr1, he1, hma1, hq1, hhu1, hsm1, hby1, hco1⟩ => by
      by_cases ha : h1.allocOk h1.nalloc
      · right
        obtain ⟨hp', _, hlive'⟩ := parserEnv_alloc_comps hp1 numComps
        refine ⟨.ref (.comp h1.nextBlk) 0, _, by simp, ?_, hp', ⟨hd1, hmr1, hsr1, he1, hma1, hq1, hhu1, hsm1, hby1, hco1⟩, hlive'⟩
        simp [C.run, C.allocComps, ha]
      · left
        refine ⟨_, ?_, parserEnv_put_nalloc hp1 (h1.nalloc + 1), hd1, hmr1, hsr1, he1, hma1, hq1, hhu1, hsm1, hby1, hco1⟩
        simp [C.run, C.allocComps, ha])
    (fun p h_ok h_post ⟨hd, hmr, hsr, he, hma, hq, hhu, hsm, hby, hco⟩ hpost hd2 hmr2 hsr2 he2 hma2 hcp2 hq2 hhu2 hsm2 hby2 hco2 => by
      refine ⟨⟨hd2.trans hd, hmr2.trans hmr, hsr2.trans hsr, he2.trans he, hma2.trans hma,
        hq2.trans hq, hhu2.trans hhu, hsm2.trans hsm, hby2.trans hby, hco2.trans hco⟩, ?_⟩
      rcases hpost with ⟨r, cs, hpR, hgR, hszR⟩
      refine ⟨r, cs, hpR, ?_, hszR⟩
      cases r; simp only [C.Space.get] at hgR ⊢; rw [hcp2]; exact hgR)
    (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
    (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
    (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
    (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
    (fun h' => h'.decomps = h.decomps ∧ h'.markers = h.markers)
    (fun _ h2 ⟨hd1, hmk1, _⟩ hd2 hmk2 _ => ⟨hd2.trans hd1, hmk2.trans hmk1⟩)
  refine ⟨res, h', hrun, hp', ?_⟩
  cases res with
  | errExit _ => exact hres
  | ok p =>
    rcases hres with ⟨hpne, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hlive⟩
    exact ⟨hpne, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hlive⟩

private theorem alloc_small_quant_parser {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ res h',
      C.run (alloc_small_quant (.ref (.decomp ctx.bdc) 0) JPOOL_PERMANENT sizeof_JQUANT_TBL) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      match res with
      | .errExit _ => h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.comps = h.comps
      | .ok p => p ≠ .null ∧
        h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧ h'.errMgrs = h.errMgrs ∧
        h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.huffs = h.huffs ∧
        h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧ h'.consts = h.consts ∧
        ∃ rq off qs, p = .ref rq off ∧ C.Space.get h' rq = some qs ∧ off < qs.size := by
  have hszLt : sizeof_JQUANT_TBL.toNat ≤ 10000000 := by decide
  let Pred (h1 : C.Heap) : Prop :=
    h1.decomps = h.decomps ∧ h1.markers = h.markers ∧ h1.srcs = h.srcs ∧ h1.errMgrs = h.errMgrs ∧
    h1.masters = h.masters ∧ h1.comps = h.comps ∧ h1.huffs = h.huffs ∧
    h1.savedMarkers = h.savedMarkers ∧ h1.bytes = h.bytes ∧ h1.consts = h.consts
  let Post (p : C.QuantPtr) (h1 : C.Heap) : Prop :=
    ∃ rq off qs, p = .ref rq off ∧ C.Space.get h1 rq = some qs ∧ off < qs.size
  unfold alloc_small_quant
  obtain ⟨res, h1, hrun1, hp1, hres1⟩ :=
    allocSmallCore_parser hp JPOOL_PERMANENT sizeof_JQUANT_TBL (Or.inl rfl) hszLt C.allocQuant
      (fun pa p => match p with | .ref (.quant b) _ => { pa with quants := pa.quants.push b } | .null => pa)
      Pred Post ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun h1 hp1 ⟨hd1, hmr1, hsr1, he1, hma1, hcp1, hhu1, hsm1, hby1, hco1⟩ => by
        by_cases ha : h1.allocOk h1.nalloc
        · right
          obtain ⟨hp', hgNew⟩ := parserEnv_alloc_quant hp1
          refine ⟨.ref (.quant h1.nextBlk) 0, _, by simp, ?_, hp', ⟨hd1, hmr1, hsr1, he1, hma1, hcp1, hhu1, hsm1, hby1, hco1⟩,
            ⟨.quant h1.nextBlk, 0, #[default], rfl, hgNew, by decide⟩⟩
          simp [C.run, C.allocQuant, ha]
        · left
          refine ⟨_, ?_, parserEnv_put_nalloc hp1 (h1.nalloc + 1), hd1, hmr1, hsr1, he1, hma1, hcp1, hhu1, hsm1, hby1, hco1⟩
          simp [C.run, C.allocQuant, ha])
      (fun p h_ok h_post ⟨hd, hmr, hsr, he, hma, hcp, hhu, hsm, hby, hco⟩ hpost hd2 hmr2 hsr2 he2 hma2 hcp2 hq2 hhu2 hsm2 hby2 hco2 => by
        refine ⟨⟨hd2.trans hd, hmr2.trans hmr, hsr2.trans hsr, he2.trans he, hma2.trans hma,
          hcp2.trans hcp, hhu2.trans hhu, hsm2.trans hsm, hby2.trans hby, hco2.trans hco⟩, ?_⟩
        rcases hpost with ⟨rq, off, qs, hpR, hgR, hszR⟩
        refine ⟨rq, off, qs, hpR, ?_, hszR⟩
        cases rq; simp only [C.Space.get] at hgR ⊢; rw [hq2]; exact hgR)
      (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
      (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
      (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
      (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
      (fun h' => h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.comps = h.comps)
      (fun _ h2 ⟨hd1, hmk1, _, _, _, hcp1, _⟩ hd2 hmk2 hcp2 => ⟨hd2.trans hd1, hmk2.trans hmk1, hcp2.trans hcp1⟩)
  refine ⟨res, h1, hrun1, hp1, ?_⟩
  cases res with
  | errExit _ => exact hres1
  | ok p =>
    rcases hres1 with ⟨hpne, ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10'⟩, hpst⟩
    exact ⟨hpne, h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', hpst⟩

theorem jpeg_alloc_quant_table_parser {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ res h',
      C.run (jpeg_alloc_quant_table (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      match res with
      | .errExit _ => h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.comps = h.comps
      | .ok p => p ≠ .null ∧
        h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧ h'.errMgrs = h.errMgrs ∧
        h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.huffs = h.huffs ∧
        h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧ h'.consts = h.consts ∧
        ∃ rq off qs, p = .ref rq off ∧ C.Space.get h' rq = some qs ∧ off < qs.size := by
  obtain ⟨res, h1, hrun1, hp1, hres1⟩ := alloc_small_quant_parser hp
  cases res with
  | errExit code =>
    refine ⟨.errExit code, h1, ?_, hp1, hres1⟩
    unfold jpeg_alloc_quant_table
    rw [C.run_bind, hrun1]; rfl
  | ok p =>
    rcases hres1 with ⟨hpne, hd1, hmr1, hsr1, he1, hma1, hcp1, hhu1, hsm1, hby1, hco1, ⟨rq, off, qs, hpEq, hgQ, hoffQ⟩⟩
    subst hpEq
    have hlQ := ptr_load_ok (r := rq) (off := off) hgQ hoffQ
    have hroQ : C.Space.ro h1 rq = false := by cases rq; rfl
    let tbl' : C.JQuantTbl := { qs[off]! with sentTable := FALSE }
    have hsQ := ptr_store_ok (r := rq) (off := off) (v := tbl') hgQ hroQ hoffQ
    let h2 := C.Space.put h1 rq (qs.set! off tbl')
    have hp2 : ParserEnv ctx h2 := parserEnv_put_quant hp1 hgQ
    refine ⟨.ok (.ref rq off), h2, ?_, hp2, hpne,
      (by cases rq; exact hd1), (by cases rq; exact hmr1), (by cases rq; exact hsr1),
      (by cases rq; exact he1), (by cases rq; exact hma1), (by cases rq; exact hcp1),
      (by cases rq; exact hhu1), (by cases rq; exact hsm1), (by cases rq; exact hby1),
      (by cases rq; exact hco1),
      rq, off, qs.set! off tbl', rfl, ?_, by simpa [Array.set!_eq_setIfInBounds] using hoffQ⟩
    · unfold jpeg_alloc_quant_table
      rw [C.run_bind, hrun1]; dsimp only
      rw [C.run_bind, hlQ]; dsimp only
      rw [C.run_bind, hsQ]; rfl
    · dsimp only [h2]; cases rq; simp only [C.Space.get, C.Space.put, C.upd_same]

private theorem alloc_small_huff_parser {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ res h',
      C.run (alloc_small_huff (.ref (.decomp ctx.bdc) 0) JPOOL_PERMANENT sizeof_JHUFF_TBL) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      match res with
      | .errExit _ => h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.comps = h.comps
      | .ok p => p ≠ .null ∧
        h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧ h'.errMgrs = h.errMgrs ∧
        h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
        h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧ h'.consts = h.consts ∧
        ∃ rh off hs, p = .ref rh off ∧ C.Space.get h' rh = some hs ∧ off < hs.size := by
  have hszLt : sizeof_JHUFF_TBL.toNat ≤ 10000000 := by decide
  let Pred (h1 : C.Heap) : Prop :=
    h1.decomps = h.decomps ∧ h1.markers = h.markers ∧ h1.srcs = h.srcs ∧ h1.errMgrs = h.errMgrs ∧
    h1.masters = h.masters ∧ h1.comps = h.comps ∧ h1.quants = h.quants ∧
    h1.savedMarkers = h.savedMarkers ∧ h1.bytes = h.bytes ∧ h1.consts = h.consts
  let Post (p : C.HuffPtr) (h1 : C.Heap) : Prop :=
    ∃ rh off hs, p = .ref rh off ∧ C.Space.get h1 rh = some hs ∧ off < hs.size
  unfold alloc_small_huff
  obtain ⟨res, h1, hrun1, hp1, hres1⟩ :=
    allocSmallCore_parser hp JPOOL_PERMANENT sizeof_JHUFF_TBL (Or.inl rfl) hszLt C.allocHuff
      (fun pa p => match p with | .ref (.huff b) _ => { pa with huffs := pa.huffs.push b } | .null => pa)
      Pred Post ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun h1 hp1 ⟨hd1, hmr1, hsr1, he1, hma1, hcp1, hq1, hsm1, hby1, hco1⟩ => by
        by_cases ha : h1.allocOk h1.nalloc
        · right
          obtain ⟨hp', hgNew⟩ := parserEnv_alloc_huff hp1
          refine ⟨.ref (.huff h1.nextBlk) 0, _, by simp, ?_, hp', ⟨hd1, hmr1, hsr1, he1, hma1, hcp1, hq1, hsm1, hby1, hco1⟩,
            ⟨.huff h1.nextBlk, 0, #[default], rfl, hgNew, by decide⟩⟩
          simp [C.run, C.allocHuff, ha]
        · left
          refine ⟨_, ?_, parserEnv_put_nalloc hp1 (h1.nalloc + 1), hd1, hmr1, hsr1, he1, hma1, hcp1, hq1, hsm1, hby1, hco1⟩
          simp [C.run, C.allocHuff, ha])
      (fun p h_ok h_post ⟨hd, hmr, hsr, he, hma, hcp, hq, hsm, hby, hco⟩ hpost hd2 hmr2 hsr2 he2 hma2 hcp2 hq2 hhu2 hsm2 hby2 hco2 => by
        refine ⟨⟨hd2.trans hd, hmr2.trans hmr, hsr2.trans hsr, he2.trans he, hma2.trans hma,
          hcp2.trans hcp, hq2.trans hq, hsm2.trans hsm, hby2.trans hby, hco2.trans hco⟩, ?_⟩
        rcases hpost with ⟨rh, off, hs, hpR, hgR, hszR⟩
        refine ⟨rh, off, hs, hpR, ?_, hszR⟩
        cases rh; simp only [C.Space.get] at hgR ⊢; rw [hhu2]; exact hgR)
      (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
      (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
      (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
      (fun pa p => by cases p with | null => rfl | ref r _ => cases r; rfl)
      (fun h' => h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.comps = h.comps)
      (fun _ h2 ⟨hd1, hmk1, _, _, _, hcp1, _⟩ hd2 hmk2 hcp2 => ⟨hd2.trans hd1, hmk2.trans hmk1, hcp2.trans hcp1⟩)
  refine ⟨res, h1, hrun1, hp1, ?_⟩
  cases res with
  | errExit _ => exact hres1
  | ok p =>
    rcases hres1 with ⟨hpne, ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10'⟩, hpst⟩
    exact ⟨hpne, h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', hpst⟩

theorem jpeg_alloc_huff_table_parser {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ res h',
      C.run (jpeg_alloc_huff_table (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      match res with
      | .errExit _ => h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.comps = h.comps
      | .ok p => p ≠ .null ∧
        h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧ h'.errMgrs = h.errMgrs ∧
        h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
        h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧ h'.consts = h.consts ∧
        ∃ rh off hs, p = .ref rh off ∧ C.Space.get h' rh = some hs ∧ off < hs.size := by
  obtain ⟨res, h1, hrun1, hp1, hres1⟩ := alloc_small_huff_parser hp
  cases res with
  | errExit code =>
    refine ⟨.errExit code, h1, ?_, hp1, hres1⟩
    unfold jpeg_alloc_huff_table
    rw [C.run_bind, hrun1]; rfl
  | ok p =>
    rcases hres1 with ⟨hpne, hd1, hmr1, hsr1, he1, hma1, hcp1, hq1, hsm1, hby1, hco1, ⟨rh, off, hs, hpEq, hgH, hoffH⟩⟩
    subst hpEq
    have hlH := ptr_load_ok (r := rh) (off := off) hgH hoffH
    have hroH : C.Space.ro h1 rh = false := by cases rh; rfl
    let tbl' : C.JHuffTbl := { hs[off]! with sentTable := FALSE }
    have hsH := ptr_store_ok (r := rh) (off := off) (v := tbl') hgH hroH hoffH
    let h2 := C.Space.put h1 rh (hs.set! off tbl')
    have hp2 : ParserEnv ctx h2 := parserEnv_put_huff hp1 hgH
    refine ⟨.ok (.ref rh off), h2, ?_, hp2, hpne,
      (by cases rh; exact hd1), (by cases rh; exact hmr1), (by cases rh; exact hsr1),
      (by cases rh; exact he1), (by cases rh; exact hma1), (by cases rh; exact hcp1),
      (by cases rh; exact hq1), (by cases rh; exact hsm1), (by cases rh; exact hby1),
      (by cases rh; exact hco1),
      rh, off, hs.set! off tbl', rfl, ?_, by simpa [Array.set!_eq_setIfInBounds] using hoffH⟩
    · unfold jpeg_alloc_huff_table
      rw [C.run_bind, hrun1]; dsimp only
      rw [C.run_bind, hlH]; dsimp only
      rw [C.run_bind, hsH]; rfl
    · dsimp only [h2]; cases rh; simp only [C.Space.get, C.Space.put, C.upd_same]

theorem alloc_large_saved_marker_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (limit : Nat) (hlim : limit ≤ 65535) :
    ∃ res h',
      C.run (alloc_large_saved_marker (.ref (.decomp ctx.bdc) 0) JPOOL_IMAGE limit) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      match res with
      | .errExit _ => h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.comps = h.comps
      | .ok (smP, dP) =>
        h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧ h'.errMgrs = h.errMgrs ∧
        h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧ h'.huffs = h.huffs ∧
        h'.consts = h.consts ∧
        ∃ rsm sms, smP = .ref rsm 0 ∧ C.Space.get h' rsm = some sms ∧ 0 < sms.size ∧
        WritableBytes h' dP limit := by
  obtain ⟨dcs, hgdc, hszdc, herrp, hmemp, _⟩ := parserEnv_get_dc hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  let maxChunkU : UInt64 := MAX_ALLOC_CHUNK.toInt.toNat.toUInt64
  let reqSize : UInt64 := sizeof_jpeg_marker_struct.toInt.toNat.toUInt64 + UInt64.ofNat limit
  have hmck : maxChunkU.toNat = 1000000000 := by decide
  have hreqNat : reqSize.toNat = 32 + limit := by
    have h32 : sizeof_jpeg_marker_struct.toInt.toNat.toUInt64.toNat = 32 := by decide
    rw [UInt64.toNat_add, h32, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hno1 : ¬(reqSize > maxChunkU) := fun hgt => by
    have hlt : maxChunkU.toNat < reqSize.toNat := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  let sizeofobject := round_up_pow2 reqSize ALIGN_SIZE
  have hru : sizeofobject.toNat ≤ reqSize.toNat + 7 := round_up_pow2_le reqSize (by omega)
  have hno2 : ¬(sizeof_small_pool_hdr + sizeofobject + ALIGN_SIZE - 1 > maxChunkU) := by
    have h24 : sizeof_small_pool_hdr.toNat = 24 := by decide
    have h8 : ALIGN_SIZE.toNat = 8 := by decide
    have hsum1 : (sizeof_small_pool_hdr + sizeofobject).toNat = 24 + sizeofobject.toNat := by
      rw [UInt64.toNat_add, h24, Nat.mod_eq_of_lt (by omega)]
    have hsum2 : (sizeof_small_pool_hdr + sizeofobject + ALIGN_SIZE).toNat = 24 + sizeofobject.toNat + 8 := by
      rw [UInt64.toNat_add, hsum1, h8, Nat.mod_eq_of_lt (by omega)]
    have hsum : (sizeof_small_pool_hdr + sizeofobject + ALIGN_SIZE - 1).toNat = 24 + sizeofobject.toNat + 7 := by
      rw [UInt64.toNat_sub_of_le _ 1 (UInt64.le_iff_toNat_le.mpr (by rw [hsum2]; change 1 ≤ 24 + sizeofobject.toNat + 8; omega)), hsum2]
      change 24 + sizeofobject.toNat + 8 - 1 = 24 + sizeofobject.toNat + 7; omega
    intro hgt
    have hlt : maxChunkU.toNat < (sizeof_small_pool_hdr + sizeofobject + ALIGN_SIZE - 1).toNat :=
      UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have hno3 : (JPOOL_IMAGE < 0 || JPOOL_IMAGE ≥ JPOOL_NUMPOOLS) = false := by decide
  by_cases ha : h.allocOk h.nalloc
  · obtain ⟨hp1, hgSm1, hwb1⟩ := parserEnv_alloc_savedMarker hp limit
    let h1 := {
      h with
      savedMarkers := C.upd h.savedMarkers h.nextBlk (some #[default])
      bytes := C.upd h.bytes (h.nextBlk + 1) (some (Array.replicate limit 0))
      nextBlk := h.nextBlk + 2
      nalloc := h.nalloc + 1
    }
    have hgl : C.run (jpeg_get_large_saved_marker limit) h =
        .ok ((.ref (.savedMarker h.nextBlk) 0, .ref (.heap (h.nextBlk + 1)) 0), h1) := by
      simp [jpeg_get_large_saved_marker, C.allocSavedMarkerData, C.run, ha, h1]
    obtain ⟨dcs1, hgdc1, hszdc1, _, hmemp1, _⟩ := parserEnv_get_dc hp1
    obtain ⟨mems1, hgmem1, hszmem1, _⟩ := parserEnv_get_mem hp1
    have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc1
    have hlmem1 := ptr_load_ok (r := ctx.rmem) (off := 0) hgmem1 hszmem1
    have hroMem1 : C.Space.ro h1 ctx.rmem = false := by cases ctx.rmem; rfl
    have hpid1 : (JPOOL_IMAGE.toInt.toNat : Nat) = 1 := by decide
    let pa1 := mems1[0]!.poolAllocs[1]!
    let pa' : C.PoolAllocs := {
      pa1 with savedMarkers := pa1.savedMarkers.push h.nextBlk, bytes := pa1.bytes.push (h.nextBlk + 1)
    }
    let mem1' : C.JpegMemMgr := {
      mems1[0]! with
      poolAllocs := mems1[0]!.poolAllocs.set! 1 pa'
      totalSpaceAllocated := mems1[0]!.totalSpaceAllocated + sizeofobject + sizeof_small_pool_hdr + ALIGN_SIZE - 1
    }
    have hstMem1 := ptr_store_ok (r := ctx.rmem) (off := 0) (v := mem1') hgmem1 hroMem1 hszmem1
    let h2 := C.Space.put h1 ctx.rmem (mems1.set! 0 mem1')
    have hp2 : ParserEnv ctx h2 := parserEnv_put_mem_pool hp1 hgmem1 hszmem1 (by omega) rfl rfl rfl rfl
    have hgSm2 : C.Space.get h2 (C.SavedMarkerRef.savedMarker h.nextBlk) = some #[default] := by
      cases ctx.rmem; exact hgSm1
    have hwb2 : WritableBytes h2 (.ref (.heap (h.nextBlk + 1)) 0) limit := by
      rcases hwb1 with ⟨bh, boff, bd, hpB, hgB, hbl⟩
      refine ⟨bh, boff, bd, hpB, ?_, hbl⟩
      cases ctx.rmem; exact hgB
    refine ⟨.ok (.ref (.savedMarker h.nextBlk) 0, .ref (.heap (h.nextBlk + 1)) 0), h2, ?_, hp2,
      (by cases ctx.rmem; rfl), (by cases ctx.rmem; rfl), (by cases ctx.rmem; rfl),
      (by cases ctx.rmem; rfl), (by cases ctx.rmem; rfl), (by cases ctx.rmem; rfl),
      (by cases ctx.rmem; rfl), (by cases ctx.rmem; rfl), (by cases ctx.rmem; rfl),
      .savedMarker h.nextBlk, #[default], rfl, hgSm2, by decide, hwb2⟩
    unfold alloc_large_saved_marker
    rw [C.run_bind, hldc]; dsimp only
    simp only [
      show ¬(sizeof_jpeg_marker_struct.toInt.toNat.toUInt64 + UInt64.ofNat limit >
        MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) from hno1,
      show ¬(sizeof_small_pool_hdr + round_up_pow2 (sizeof_jpeg_marker_struct.toInt.toNat.toUInt64 + UInt64.ofNat limit)
        ALIGN_SIZE + ALIGN_SIZE - 1 > MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) from hno2,
      ↓reduceIte, hno3, Bool.false_eq_true]
    rw [C.run_bind, hgl]; dsimp only
    have hne : ((C.Ptr.ref (C.SavedMarkerRef.savedMarker h.nextBlk) 0 : C.SavedMarkerPtr) == .null) = false := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hpid1]
    rw [C.run_bind, hldc1]; dsimp only
    rw [hmemp1, C.run_bind, hlmem1]; dsimp only
    rw [C.run_bind, hstMem1]; rfl
  · let h1 := { h with nalloc := h.nalloc + 1 }
    have hp1 : ParserEnv ctx h1 := parserEnv_put_nalloc hp (h.nalloc + 1)
    have hgl : C.run (jpeg_get_large_saved_marker limit) h = .ok ((.null, .null), h1) := by
      simp [jpeg_get_large_saved_marker, C.allocSavedMarkerData, C.run, ha, h1]
    obtain ⟨dcs1, hgdc1, hszdc1, herrp1, _⟩ := parserEnv_get_dc hp1
    have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc1
    obtain ⟨h_err, hk, hp_err, hdE, hmkE, _, _, hcpE, _⟩ :=
      errMsgUpdate_cont_parser hp1 JERR_OUT_OF_MEMORY (fun arr => arr.set! 0 4)
    have herr_run : C.run (errexit1 (.ref ctx.rerr 0) JERR_OUT_OF_MEMORY 4) h1 =
        .ok (.errExit JERR_OUT_OF_MEMORY, h_err) := by
      unfold errexit1; exact hk (pure (JpegRes.errExit JERR_OUT_OF_MEMORY))
    refine ⟨.errExit JERR_OUT_OF_MEMORY, h_err, ?_, hp_err, hdE, hmkE, hcpE⟩
    unfold alloc_large_saved_marker
    rw [C.run_bind, hldc]; dsimp only
    simp only [
      show ¬(sizeof_jpeg_marker_struct.toInt.toNat.toUInt64 + UInt64.ofNat limit >
        MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) from hno1,
      show ¬(sizeof_small_pool_hdr + round_up_pow2 (sizeof_jpeg_marker_struct.toInt.toNat.toUInt64 + UInt64.ofNat limit)
        ALIGN_SIZE + ALIGN_SIZE - 1 > MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) from hno2,
      ↓reduceIte, hno3, Bool.false_eq_true]
    rw [C.run_bind, hgl]; dsimp only
    have heqNull : ((C.Ptr.null : C.SavedMarkerPtr) == .null) = true := rfl
    simp only [heqNull, ↓reduceIte]
    have hoom : C.run (out_of_memory (.ref (.decomp ctx.bdc) 0) 4) h1 =
        .ok (.errExit JERR_OUT_OF_MEMORY, h_err) := by
      unfold out_of_memory; rw [C.run_bind, hldc1]; dsimp only; rw [herrp1]; exact herr_run
    rw [C.run_bind, hoom]; rfl

end MozjpegF.Proof.JdmarkerParsers
