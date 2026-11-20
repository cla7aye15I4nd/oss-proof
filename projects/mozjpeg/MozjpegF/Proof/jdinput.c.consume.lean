import MozjpegF.Spec.Safety.Goals
import MozjpegF.Proof.«jdmarker.c.helpers»
import MozjpegF.Proof.«jdmarker.c.readmarkers»
import MozjpegF.Proof.«public-jutils»

/-!
# Proofs of `jdinput.c` input-control and `consume_markers` safety (`MozjpegF`)

Kernel-checked safety and invariant-preservation theorems for:
- `reset_input_controller`
- `initial_setup`
- `per_scan_setup`
- `latch_quant_tables`
- `start_input_pass`
- `finish_input_pass`
- `consume_markers`
-/

set_option autoImplicit false

namespace MozjpegF.Proof.JdinputConsume
open C MozjpegF.Spec MozjpegF.Spec.Safety
open Mozjpeg.Jdinput Mozjpeg.Jdmarker Mozjpeg.Jerror Mozjpeg.Jmemmgr
open Mozjpeg.Jutils Mozjpeg.JerrorH Mozjpeg.JpeglibH Mozjpeg.MoreCfg
open MozjpegF.Proof.JdmarkerHelpers
open MozjpegF.Proof.JdmarkerRead
open MozjpegF.Proof.JdmarkerParsers
open MozjpegF.Proof.JdmarkerMarkers
open MozjpegF.Proof.JdmarkerReadMarkers
open MozjpegF.Proof.Jutils

private theorem array_set_bang_self {α : Type} [Inhabited α] (xs : Array α) {i : Nat}
    (hi : i < xs.size) (v : α) : (xs.set! i v)[i]! = v := by
  have hsz : i < (xs.set! i v).size := by simpa using hi
  rw [getElem!_pos _ i hsz]; simp [Array.set!_eq_setIfInBounds]

private theorem array_set_bang_ne {α : Type} [Inhabited α] (xs : Array α) {i j : Nat}
    (hi : i < xs.size) (hj : j < xs.size) (hne : i ≠ j) (v : α) :
    (xs.set! i v)[j]! = xs[j]! := by
  simp only [Array.set!, Array.setIfInBounds, hi, ↓reduceDIte]
  rw [getElem!_pos _ j (by simp [hj]), getElem!_pos _ j hj]
  exact Array.getElem_set_ne hi hj hne

/-! ## Common heap & invariant preservation helpers -/

theorem parserEnv_get_ic {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ ics, C.Space.get h ctx.ric = some ics ∧ 0 < ics.size ∧
      ics[0]!.resetInputController = .fn "reset_input_controller" ∧
      (ics[0]!.consumeInput = .fn "consume_markers" ∨ ics[0]!.consumeInput = .fn "dummy_consume_data") := by
  obtain ⟨_, _, _, _, _, _, _, ics, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hgic, hszic, hric, hci, _⟩ := hp
  exact ⟨ics, hgic, hszic, hric, hci⟩

theorem parserEnv_get_comp {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ dcs mrks,
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧
      C.Space.get h ctx.rmrk = some mrks ∧ 0 < mrks.size ∧
      (mrks[0]!.sawSOF ≠ 0 → dcs[0]!.compInfo ≠ .null) ∧
      (dcs[0]!.compInfo ≠ .null → 0 ≤ dcs[0]!.numComponents.toInt ∧
        LiveCompArray h dcs[0]!.compInfo dcs[0]!.numComponents.toInt.toNat) := by
  obtain ⟨_, _, dcs, dc, _, _, _, _, mrks, _,
    hgdc, hszdc, hdc,
    _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _,
    _, _, _, _, _,
    _, hgmrk, hszmrk, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, _, hsaw, hcomp, _⟩ := hp
  rw [hdc] at hsaw hcomp
  exact ⟨dcs, mrks, hgdc, hszdc, hgmrk, hszmrk, hsaw, hcomp⟩

theorem parserEnv_get_dc_arrs {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧
      dcs[0]!.quantTblPtrs.size = 4 ∧
      (∀ i < 4, dcs[0]!.quantTblPtrs[i]! = .null ∨
        ∃ rq off qs, dcs[0]!.quantTblPtrs[i]! = .ref rq off ∧ C.Space.get h rq = some qs ∧ off < qs.size) ∧
      dcs[0]!.dcHuffTblPtrs.size = 4 ∧
      (∀ i < 4, dcs[0]!.dcHuffTblPtrs[i]! = .null ∨
        ∃ rh off hs, dcs[0]!.dcHuffTblPtrs[i]! = .ref rh off ∧ C.Space.get h rh = some hs ∧ off < hs.size) ∧
      dcs[0]!.acHuffTblPtrs.size = 4 ∧
      (∀ i < 4, dcs[0]!.acHuffTblPtrs[i]! = .null ∨
        ∃ rh off hs, dcs[0]!.acHuffTblPtrs[i]! = .ref rh off ∧ C.Space.get h rh = some hs ∧ off < hs.size) ∧
      dcs[0]!.curCompInfo.size = 4 ∧
      0 ≤ dcs[0]!.inputScanNumber.toInt := by
  obtain ⟨_, _, dcs, dc, _, _, _, _, _, _,
    hgdc, hszdc, hdc,
    _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _,
    _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, _, _, _, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  rw [hdc] at hqtSz hqt hdhSz hdh hahSz hah hccSz hisn0
  exact ⟨dcs, hgdc, hszdc, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩

theorem parserEnv_put_dc_keep {ctx : IoCtx} {h : C.Heap} {dcs : Array C.JpegDecompressStruct}
    {dc' : C.JpegDecompressStruct}
    (hp : ParserEnv ctx h) (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (kerr : dc'.err = dcs[0]!.err) (kmem : dc'.mem = dcs[0]!.mem) (kmas : dc'.master = dcs[0]!.master)
    (kic : dc'.inputctl = dcs[0]!.inputctl) (kmrk : dc'.marker = dcs[0]!.marker) (ksrc : dc'.src = dcs[0]!.src)
    (kml : dc'.markerList = dcs[0]!.markerList)
    (kcomp : dc'.compInfo = dcs[0]!.compInfo)
    (knc : dc'.numComponents = dcs[0]!.numComponents)
    (kqt : dc'.quantTblPtrs = dcs[0]!.quantTblPtrs)
    (kdh : dc'.dcHuffTblPtrs = dcs[0]!.dcHuffTblPtrs)
    (kah : dc'.acHuffTblPtrs = dcs[0]!.acHuffTblPtrs)
    (kcc : dc'.curCompInfo = dcs[0]!.curCompInfo)
    (kisn : dc'.inputScanNumber = dcs[0]!.inputScanNumber) :
    ParserEnv ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) := by
  obtain ⟨dcsA, hgA, _, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := parserEnv_get_dc_arrs hp
  obtain ⟨dcsB, mrksB, hgB, _, hgmrkB, _, hsawB, _⟩ := parserEnv_get_comp hp
  have hEqA := Option.some.inj (hg.symm.trans hgA)
  have hEqB := Option.some.inj (hg.symm.trans hgB)
  rw [← hEqA] at hqtSz hqt hdhSz hdh hahSz hah hccSz hisn0
  rw [← hEqB] at hsawB
  refine parserEnv_put_dc hp hg hsz kerr kmem kmas kic kmrk ksrc (Or.inl kml) (Or.inl ⟨kcomp, knc⟩)
    ⟨by rw [kqt]; exact hqtSz, fun i hi => by rw [kqt]; exact hqt i hi⟩
    ⟨by rw [kdh]; exact hdhSz, fun i hi => by rw [kdh]; exact hdh i hi⟩
    ⟨by rw [kah]; exact hahSz, fun i hi => by rw [kah]; exact hah i hi⟩
    (by rw [kcc]; exact hccSz) (by rw [kisn]; exact hisn0)
    (fun mrks hgmrk _ hsawNe => by
      have hmEq := Option.some.inj (hgmrk.symm.trans hgmrkB); rw [hmEq] at hsawNe
      rw [kcomp]; exact hsawB hsawNe)

theorem parserEnv_put_dc_keep' {ctx : IoCtx} {h : C.Heap} {dcs : Array C.JpegDecompressStruct}
    {dc' : C.JpegDecompressStruct}
    (hp : ParserEnv ctx h) (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (kerr : dc'.err = dcs[0]!.err) (kmem : dc'.mem = dcs[0]!.mem) (kmas : dc'.master = dcs[0]!.master)
    (kic : dc'.inputctl = dcs[0]!.inputctl) (kmrk : dc'.marker = dcs[0]!.marker) (ksrc : dc'.src = dcs[0]!.src)
    (kml : dc'.markerList = dcs[0]!.markerList)
    (kcomp : dc'.compInfo = dcs[0]!.compInfo)
    (knc : dc'.numComponents = dcs[0]!.numComponents)
    (kqt : dc'.quantTblPtrs = dcs[0]!.quantTblPtrs)
    (kdh : dc'.dcHuffTblPtrs = dcs[0]!.dcHuffTblPtrs)
    (kah : dc'.acHuffTblPtrs = dcs[0]!.acHuffTblPtrs)
    (kcc : dc'.curCompInfo = dcs[0]!.curCompInfo)
    (kisn : dc'.inputScanNumber = dcs[0]!.inputScanNumber) :
    ParserEnv ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) :=
  parserEnv_put_dc_keep hp hg hsz kerr kmem kmas kic kmrk ksrc kml kcomp knc kqt kdh kah kcc kisn

theorem compSawZero_put_dc_keep {ctx : IoCtx} {h : C.Heap} {dcs : Array C.JpegDecompressStruct}
    {dc' : C.JpegDecompressStruct}
    (hsaw : CompSawZero ctx h)
    (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (kcomp : dc'.compInfo = dcs[0]!.compInfo) :
    CompSawZero ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) := by
  intro mrks dcs' hgm hszm hgd _ hsz0
  have hgd' : C.Space.get (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc'))
      (C.DecompRef.decomp ctx.bdc) = some (dcs.set! 0 dc') := by
    simp [C.Space.get, C.Space.put]
  rw [Option.some.inj (hgd.symm.trans hgd'), set0_bang_m dcs hsz dc', kcomp]
  rcases hrM : ctx.rmrk with ⟨bm⟩
  simp only [C.Space.get, C.Space.put, hrM] at hgm
  exact hsaw mrks dcs (by simp only [C.Space.get, hrM]; exact hgm) hszm hg hsz hsz0

theorem compSawZero_put_mst {ctx : IoCtx} {h : C.Heap} {masters : Array C.JpegDecompMaster}
    (hsaw : CompSawZero ctx h) :
    CompSawZero ctx (C.Space.put h ctx.rmas masters) := fun m d hm hsm hd hsd hs =>
  hsaw m d (by rcases hrM : ctx.rmrk with ⟨bm⟩; rcases hrA : ctx.rmas with ⟨ba⟩; simp only [C.Space.get, C.Space.put, hrM, hrA] at hm ⊢; exact hm) hsm hd hsd hs

theorem compSawZero_put_comp {ctx : IoCtx} {h : C.Heap} {rc : C.CompRef} {cs : Array C.JpegCompInfo}
    (hsaw : CompSawZero ctx h) :
    CompSawZero ctx (C.Space.put h rc cs) := fun m d hm hsm hd hsd hs =>
  hsaw m d (by rcases hrM : ctx.rmrk with ⟨bm⟩; rcases rc with ⟨bc⟩; simp only [C.Space.get, C.Space.put, hrM] at hm ⊢; exact hm) hsm (by rcases rc with ⟨bc⟩; exact hd) hsd hs

theorem compSawZero_put_quant {ctx : IoCtx} {h : C.Heap} {rq : C.QuantRef} {qs : Array C.JQuantTbl}
    (hsaw : CompSawZero ctx h) :
    CompSawZero ctx (C.Space.put h rq qs) := fun m d hm hsm hd hsd hs =>
  hsaw m d (by rcases hrM : ctx.rmrk with ⟨bm⟩; rcases rq with ⟨bq⟩; simp only [C.Space.get, C.Space.put, hrM] at hm ⊢; exact hm) hsm (by rcases rq with ⟨bq⟩; exact hd) hsd hs

theorem compSawZero_put_ic {ctx : IoCtx} {h : C.Heap} {ics : Array C.JpegInputController}
    (hsaw : CompSawZero ctx h) :
    CompSawZero ctx (C.Space.put h ctx.ric ics) := fun m d hm hsm hd hsd hs =>
  hsaw m d (by rcases hrM : ctx.rmrk with ⟨bm⟩; rcases hrI : ctx.ric with ⟨bi⟩; simp only [C.Space.get, C.Space.put, hrM, hrI] at hm ⊢; exact hm) hsm (by rcases hrI : ctx.ric with ⟨bi⟩; exact hd) hsd hs

theorem parserEnv_put_ic {ctx : IoCtx} {h : C.Heap} {ics : Array C.JpegInputController}
    {ic' : C.JpegInputController}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.ric = some ics) (hsz : 0 < ics.size)
    (hric : ic'.resetInputController = .fn "reset_input_controller")
    (hci : ic'.consumeInput = .fn "consume_markers" ∨ ic'.consumeInput = .fn "dummy_consume_data") :
    ParserEnv ctx (C.Space.put h ctx.ric (ics.set! 0 ic')) := by
  obtain ⟨hcore, hfr, dcs, dc, errs, mems, masters, ics0, mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic0, hszic0, _hric0, _hci0,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp
  have hicEq : ics = ics0 := Option.some.inj (hg.symm.trans hgic0)
  subst hicEq
  let h' := C.Space.put h ctx.ric (ics.set! 0 ic')
  have hg' : C.Space.get h' ctx.ric = some (ics.set! 0 ic') := by
    rcases hr : ctx.ric with ⟨bi⟩; simp [h', C.Space.get, C.Space.put, hr, C.upd_same]
  have hsz' : 0 < (ics.set! 0 ic').size := by simpa using hsz
  have h0' : (ics.set! 0 ic')[0]! = ic' := set0_bang_m ics hsz ic'
  have hcore' : ValidDecompCore h' (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · exact ⟨dcs, dc, dcs, dc, hgdc, hszdc, hdc, hgdc, hszdc, hdc, rfl, rfl, rfl, rfl, rfl⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro r a hga hsza
      rcases r with ⟨bi⟩
      rcases hr : ctx.ric with ⟨bi0⟩
      by_cases heq : bi = bi0
      · subst heq; exact ⟨ics.set! 0 ic', by rw [← hr]; exact hg', hsz'⟩
      · exact ⟨a, by simp only [h', C.Space.get, C.Space.put, hr, C.upd_ne _ _ _ _ heq] at hga ⊢; exact hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ ms hgm hszm hpa; exact ⟨ms, hgm, hszm, hpa, rfl⟩
  have hfr' : FreshNextBlk h' := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, hma, hmr, ?_, hsr, hcp, hq, hhu, hsm⟩
    rcases hr : ctx.ric with ⟨bi0⟩
    by_cases heq : k = bi0
    · subst heq; simp only [C.Space.get, hr] at hg; rw [hic] at hg; cases hg
    · simp only [h', C.Space.put, hr, C.upd_ne _ _ _ _ heq]; exact hic
  refine ⟨hcore', hfr', dcs, dc, errs, mems, masters, ics.set! 0 ic', mrks, srcs,
    hgdc, hszdc, hdc, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hg', hsz', (by rw [h0']; exact hric), (by rw [h0']; exact hci),
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, hmlEnd, hsaw, hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩

theorem multiScanReady_put_ic {ctx : IoCtx} {h : C.Heap} {ics : Array C.JpegInputController}
    {dc : C.JpegDecompressStruct} (hm : MultiScanReady h dc) :
    MultiScanReady (C.Space.put h ctx.ric ics) dc := by
  rcases hm with ⟨e1, e2, e3, c1, c2, cs, m1, m2, m3, m4, w1, h1, nc1, nc2, ⟨rmrk, mrks, km, hgm, hszm, hsof⟩, hc, hcur⟩
  refine ⟨e1, e2, e3, c1, c2, cs, m1, m2, m3, m4, w1, h1, nc1, nc2,
    ⟨rmrk, mrks, km, (by cases rmrk; exact hgm), hszm, hsof⟩, ?_, ?_⟩
  · rcases hc with h0 | ⟨rcp, cs0, kc, hgc, hszc, hf⟩
    · exact Or.inl h0
    · exact Or.inr ⟨rcp, cs0, kc, (by cases rcp; exact hgc), hszc, hf⟩
  · intro i hi
    obtain ⟨rcp, off, cs0, ci, h1i, h2i, h3i, h4i, h5i⟩ := hcur i hi
    exact ⟨rcp, off, cs0, ci, h1i, (by cases rcp; exact h2i), h3i, h4i, h5i⟩

theorem multiScanReady_put_mst {ctx : IoCtx} {h : C.Heap} {masters : Array C.JpegDecompMaster}
    {dc : C.JpegDecompressStruct} (hm : MultiScanReady h dc) :
    MultiScanReady (C.Space.put h ctx.rmas masters) dc := by
  rcases hm with ⟨e1, e2, e3, c1, c2, cs, m1, m2, m3, m4, w1, h1, nc1, nc2, ⟨rmrk, mrks, km, hgm, hszm, hsof⟩, hc, hcur⟩
  refine ⟨e1, e2, e3, c1, c2, cs, m1, m2, m3, m4, w1, h1, nc1, nc2,
    ⟨rmrk, mrks, km, (by cases rmrk; exact hgm), hszm, hsof⟩, ?_, ?_⟩
  · rcases hc with h0 | ⟨rcp, cs0, kc, hgc, hszc, hf⟩
    · exact Or.inl h0
    · exact Or.inr ⟨rcp, cs0, kc, (by cases rcp; exact hgc), hszc, hf⟩
  · intro i hi
    obtain ⟨rcp, off, cs0, ci, h1i, h2i, h3i, h4i, h5i⟩ := hcur i hi
    exact ⟨rcp, off, cs0, ci, h1i, (by cases rcp; exact h2i), h3i, h4i, h5i⟩

theorem multiScanReady_put_quant {h : C.Heap} {rq : C.QuantRef} {qs : Array C.JQuantTbl}
    {dc : C.JpegDecompressStruct} (hm : MultiScanReady h dc) :
    MultiScanReady (C.Space.put h rq qs) dc := by
  rcases hm with ⟨e1, e2, e3, c1, c2, cs, m1, m2, m3, m4, w1, h1, nc1, nc2, ⟨rmrk, mrks, km, hgm, hszm, hsof⟩, hc, hcur⟩
  refine ⟨e1, e2, e3, c1, c2, cs, m1, m2, m3, m4, w1, h1, nc1, nc2,
    ⟨rmrk, mrks, km, (by cases rmrk; exact hgm), hszm, hsof⟩, ?_, ?_⟩
  · rcases hc with h0 | ⟨rcp, cs0, kc, hgc, hszc, hf⟩
    · exact Or.inl h0
    · exact Or.inr ⟨rcp, cs0, kc, (by cases rcp; cases rq; exact hgc), hszc, hf⟩
  · intro i hi
    obtain ⟨rcp, off, cs0, ci, h1i, h2i, h3i, h4i, h5i⟩ := hcur i hi
    exact ⟨rcp, off, cs0, ci, h1i, (by cases rcp; cases rq; exact h2i), h3i, h4i, h5i⟩

theorem multiScanReady_put_comp {h : C.Heap} {rc : C.CompRef} {cs : Array C.JpegCompInfo}
    {off : Nat} {c' : C.JpegCompInfo} {dc : C.JpegDecompressStruct}
    (hg : C.Space.get h rc = some cs) (hoff : off < cs.size)
    (hk1 : c'.hSampFactor = cs[off]!.hSampFactor)
    (hk2 : c'.vSampFactor = cs[off]!.vSampFactor)
    (hk3 : c'.dctHScaledSize = cs[off]!.dctHScaledSize)
    (hm : MultiScanReady h dc) :
    MultiScanReady (C.Space.put h rc (cs.set! off c')) dc := by
  rcases hm with ⟨e1, e2, e3, c1, c2, csz, m1, m2, m3, m4, w1, h1, nc1, nc2, mk, hc, hcur⟩
  let h' := C.Space.put h rc (cs.set! off c')
  refine ⟨e1, e2, e3, c1, c2, csz, m1, m2, m3, m4, w1, h1, nc1, nc2,
    (by rcases mk with ⟨rmrk, mrks, km, hgm, hszm, hsof⟩; exact ⟨rmrk, mrks, km, (by cases rmrk; exact hgm), hszm, hsof⟩), ?_, ?_⟩
  · rcases hc with h0 | ⟨rcp, cs0, kc, hgc, hszc, hf⟩
    · exact Or.inl h0
    · rcases rc with ⟨b1⟩; rcases rcp with ⟨b2⟩
      by_cases heq : b2 = b1
      · subst heq
        have hcsEq := Option.some.inj (hgc.symm.trans hg)
        subst hcsEq
        refine Or.inr ⟨.comp b2, cs0.set! off c', kc, (by simp [C.Space.get, C.Space.put, C.upd_same]), (by simpa using hszc), fun j hj => ?_⟩
        by_cases hjo : j = off
        · subst hjo
          have hbj := hf j hj
          rw [array_set_bang_self cs0 hoff c', hk1, hk2, hk3]; exact hbj
        · have hjLt : j < cs0.size := Nat.lt_of_lt_of_le hj hszc
          rw [array_set_bang_ne cs0 hoff hjLt (Ne.symm hjo) c']; exact hf j hj
      · exact Or.inr ⟨.comp b2, cs0, kc, (by simp [C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq]; exact hgc), hszc, hf⟩
  · intro i hi
    obtain ⟨rcp, offI, cs0, ci, hci, hgc, hoffI, hciEq, hbounds⟩ := hcur i hi
    rcases rc with ⟨b1⟩; rcases rcp with ⟨b2⟩
    by_cases heq : b2 = b1
    · subst heq
      have hcsEq := Option.some.inj (hgc.symm.trans hg); rw [hcsEq] at hoffI hciEq hgc
      have hoffISz : offI < (cs.set! off c').size := by simpa using hoffI
      by_cases hio : offI = off
      · subst hio
        refine ⟨.comp b2, offI, cs.set! offI c', c', hci, (by simp [C.Space.get, C.Space.put, C.upd_same]), hoffISz, ?_, ?_⟩
        · exact (array_set_bang_self cs hoff c').symm
        · rw [hk1, hk2, hk3, ← hciEq]; exact hbounds
      · refine ⟨.comp b2, offI, cs.set! off c', ci, hci, (by simp [C.Space.get, C.Space.put, C.upd_same]), hoffISz, ?_, hbounds⟩
        rw [hciEq]; exact (array_set_bang_ne cs hoff hoffI (Ne.symm hio) c').symm
    · exact ⟨.comp b2, offI, cs0, ci, hci, (by simp [C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq]; exact hgc), hoffI, hciEq, hbounds⟩

theorem multiScanReady_put_dc_scalar {h : C.Heap} {bdc : Nat} {dcs : Array C.JpegDecompressStruct}
    {dc' : C.JpegDecompressStruct}
    (_hg : C.Space.get h (C.DecompRef.decomp bdc) = some dcs) (_hsz : 0 < dcs.size)
    (ke1 : dc'.entropyStartPass = dcs[0]!.entropyStartPass)
    (ke2 : dc'.coefStartInputPass = dcs[0]!.coefStartInputPass)
    (ke3 : dc'.coefConsumeData = dcs[0]!.coefConsumeData)
    (kc1 : dc'.compsInScan = dcs[0]!.compsInScan)
    (kcc : dc'.curCompInfo = dcs[0]!.curCompInfo)
    (kmh : dc'.maxHSampFactor = dcs[0]!.maxHSampFactor)
    (kmv : dc'.maxVSampFactor = dcs[0]!.maxVSampFactor)
    (kiw : dc'.imageWidth = dcs[0]!.imageWidth)
    (kih : dc'.imageHeight = dcs[0]!.imageHeight)
    (knc : dc'.numComponents = dcs[0]!.numComponents)
    (kmrk : dc'.marker = dcs[0]!.marker)
    (kcp : dc'.compInfo = dcs[0]!.compInfo)
    (hm : MultiScanReady h dcs[0]!) :
    MultiScanReady (C.Space.put h (C.DecompRef.decomp bdc) (dcs.set! 0 dc')) dc' := by
  rcases hm with ⟨e1, e2, e3, c1, c2, csz, m1, m2, m3, m4, w1, h1, nc1, nc2, ⟨rmrk, mrks, km, hgm, hszm, hsof⟩, hc, hcur⟩
  refine ⟨ke1.trans e1, ke2.trans e2, ke3.trans e3, kc1 ▸ c1, kc1 ▸ c2, kcc ▸ csz,
    kmh ▸ m1, kmh ▸ m2, kmv ▸ m3, kmv ▸ m4, kiw ▸ w1, kih ▸ h1, knc ▸ nc1, knc ▸ nc2,
    ⟨rmrk, mrks, kmrk.trans km, (by cases rmrk; exact hgm), hszm, hsof⟩, ?_, ?_⟩
  · rcases hc with h0 | ⟨rcp, cs0, kc, hgc, hszc, hf⟩
    · exact Or.inl (knc.trans h0)
    · exact Or.inr ⟨rcp, cs0, kcp.trans kc, (by cases rcp; exact hgc), knc ▸ hszc, knc ▸ hf⟩
  · intro i hi
    rw [kc1] at hi
    obtain ⟨rcp, off, cs0, ci, h1i, h2i, h3i, h4i, h5i⟩ := hcur i hi
    exact ⟨rcp, off, cs0, ci, kcc ▸ h1i, (by cases rcp; exact h2i), h3i, h4i, h5i⟩

private theorem scanCompsInRange_put_dc_scalar {h : C.Heap} {bdc : Nat} {dcs : Array C.JpegDecompressStruct}
    {dc' : C.JpegDecompressStruct}
    (kc1 : dc'.compsInScan = dcs[0]!.compsInScan)
    (kcc : dc'.curCompInfo = dcs[0]!.curCompInfo)
    (knc : dc'.numComponents = dcs[0]!.numComponents)
    (kcp : dc'.compInfo = dcs[0]!.compInfo)
    (hsc : ScanCompsInRange h dcs[0]!) :
    ScanCompsInRange (C.Space.put h (C.DecompRef.decomp bdc) (dcs.set! 0 dc')) dc' := by
  rcases hsc with ⟨h1, h2, hsz, hall⟩
  refine ⟨kc1 ▸ h1, kc1 ▸ h2, kcc ▸ hsz, fun i hi => ?_⟩
  rw [kc1] at hi
  obtain ⟨rcp, offI, cs, hci, hg, hoff1, hoff2, hget⟩ := hall i hi
  exact ⟨rcp, offI, cs, kcp.trans hci, (by cases rcp; exact hg), knc ▸ hoff1, hoff2, kcc ▸ hget⟩

private theorem scanCompsInRange_put_mst {ctx : IoCtx} {h : C.Heap} {masters : Array C.JpegDecompMaster}
    {dc : C.JpegDecompressStruct} (hsc : ScanCompsInRange h dc) :
    ScanCompsInRange (C.Space.put h ctx.rmas masters) dc := by
  rcases hsc with ⟨h1, h2, hsz, hall⟩
  refine ⟨h1, h2, hsz, fun i hi => ?_⟩
  obtain ⟨rcp, offI, cs, hci, hg, hoff1, hoff2, hget⟩ := hall i hi
  exact ⟨rcp, offI, cs, hci, (by cases rcp; exact hg), hoff1, hoff2, hget⟩

private theorem scanCompsInRange_put_comp {h : C.Heap} {rc : C.CompRef} {cs : Array C.JpegCompInfo}
    {off : Nat} {c' : C.JpegCompInfo} {dc : C.JpegDecompressStruct}
    (hg : C.Space.get h rc = some cs) (_hoff : off < cs.size)
    (hsc : ScanCompsInRange h dc) :
    ScanCompsInRange (C.Space.put h rc (cs.set! off c')) dc := by
  rcases hsc with ⟨h1, h2, hsz, hall⟩
  let h' := C.Space.put h rc (cs.set! off c')
  refine ⟨h1, h2, hsz, fun i hi => ?_⟩
  obtain ⟨rcp, offI, cs0, hci, hgc, hoff1, hoff2, hget⟩ := hall i hi
  rcases rc with ⟨b1⟩; rcases rcp with ⟨b2⟩
  by_cases heq : b2 = b1
  · subst heq
    have hcsEq := Option.some.inj (hgc.symm.trans hg); subst hcsEq
    exact ⟨.comp b2, offI, cs0.set! off c', hci, (by simp [C.Space.get, C.Space.put, C.upd_same]),
      hoff1, (by simpa using hoff2), hget⟩
  · exact ⟨.comp b2, offI, cs0, hci, (by simp [C.Space.get, C.Space.put, C.upd_ne _ _ _ _ heq]; exact hgc),
      hoff1, hoff2, hget⟩

private theorem scanCompsInRange_put_ic {ctx : IoCtx} {h : C.Heap} {ics : Array C.JpegInputController}
    {dc : C.JpegDecompressStruct} (hsc : ScanCompsInRange h dc) :
    ScanCompsInRange (C.Space.put h ctx.ric ics) dc := by
  rcases hsc with ⟨h1, h2, hsz, hall⟩
  refine ⟨h1, h2, hsz, fun i hi => ?_⟩
  obtain ⟨rcp, offI, cs, hci, hg, hoff1, hoff2, hget⟩ := hall i hi
  exact ⟨rcp, offI, cs, hci, (by cases rcp; exact hg), hoff1, hoff2, hget⟩

/-! ## `reset_input_controller` -/

private theorem parserEnv_put_dc_and_mrk_reset {ctx : IoCtx} {h : C.Heap}
    {dcs : Array C.JpegDecompressStruct} {dc' : C.JpegDecompressStruct}
    {mrks : Array C.JpegMarkerReader} {mrk' : C.JpegMarkerReader}
    (hp : ParserEnv ctx h)
    (hgdc : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hszdc : 0 < dcs.size)
    (hgmrk : C.Space.get h ctx.rmrk = some mrks) (hszmrk : 0 < mrks.size)
    (kerr : dc'.err = dcs[0]!.err) (kmem : dc'.mem = dcs[0]!.mem) (kmas : dc'.master = dcs[0]!.master)
    (kic : dc'.inputctl = dcs[0]!.inputctl) (kmrk : dc'.marker = dcs[0]!.marker) (ksrc : dc'.src = dcs[0]!.src)
    (kml : dc'.markerList = dcs[0]!.markerList)
    (kcomp : dc'.compInfo = .null)
    (kqt : dc'.quantTblPtrs = dcs[0]!.quantTblPtrs)
    (kdh : dc'.dcHuffTblPtrs = dcs[0]!.dcHuffTblPtrs)
    (kah : dc'.acHuffTblPtrs = dcs[0]!.acHuffTblPtrs)
    (kcc : dc'.curCompInfo = dcs[0]!.curCompInfo)
    (kisn : 0 ≤ dc'.inputScanNumber.toInt)
    (kmrm : mrk'.readMarkers = mrks[0]!.readMarkers)
    (kmrmr : mrk'.resetMarkerReader = mrks[0]!.resetMarkerReader)
    (kmpcom : mrk'.processCOM = mrks[0]!.processCOM)
    (kmpapp : mrk'.processAPPn = mrks[0]!.processAPPn)
    (kmll : mrk'.lengthLimitAPPn = mrks[0]!.lengthLimitAPPn)
    (kmsof : mrk'.sawSOF = 0)
    (kmcm : mrk'.curMarker = .null) :
    let h1 := C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')
    let h2 := C.Space.put h1 ctx.rmrk (mrks.set! 0 mrk')
    ParserEnv ctx h2 ∧ CompSawZero ctx h2 := by
  obtain ⟨hcore, hfr, dcs0, dc0, errs, mems, masters, ics, mrks0, srcs,
    hgdc0, hszdc0, hdc0, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas, hszmas, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk0, hszmrk0, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    _hcurm, hmlEnd, _hsaw, _hcompLive, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, _hisn0⟩ := hp
  have hdEq : dcs = dcs0 := Option.some.inj (hgdc.symm.trans hgdc0)
  have hmEq : mrks = mrks0 := Option.some.inj (hgmrk.symm.trans hgmrk0)
  subst hdEq; subst hmEq
  let h1 := C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')
  let h2 := C.Space.put h1 ctx.rmrk (mrks.set! 0 mrk')
  have hgdc2 : C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some (dcs.set! 0 dc') := by
    cases ctx.rmrk; simp [h2, h1, C.Space.get, C.Space.put]
  have hszdc2 : 0 < (dcs.set! 0 dc').size := by simpa using hszdc
  have hdc2 : (dcs.set! 0 dc')[0]! = dc' := set0_bang_m dcs hszdc dc'
  have hgmrk2 : C.Space.get h2 ctx.rmrk = some (mrks.set! 0 mrk') := by
    rcases hr : ctx.rmrk with ⟨bm⟩; simp [h2, C.Space.get, C.Space.put, hr, C.upd_same]
  have hszmrk2 : 0 < (mrks.set! 0 mrk').size := by simpa using hszmrk
  have hmrk2 : (mrks.set! 0 mrk')[0]! = mrk' := set0_bang_m mrks hszmrk mrk'
  have hcore2 : ValidDecompCore h2 (.ref (.decomp ctx.bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · exact ⟨dcs, dcs[0]!, dcs.set! 0 dc', dc', hgdc0, hszdc0, rfl, hgdc2, hszdc2, hdc2.symm,
        kerr, kmem, kmas, kic, kmrk⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro _ a hga hsza; exact ⟨a, hga, hsza⟩
    · intro r a hga hsza
      rcases r with ⟨bm⟩
      rcases hr : ctx.rmrk with ⟨bm0⟩
      by_cases heq : bm = bm0
      · subst heq; exact ⟨mrks.set! 0 mrk', by rw [← hr]; exact hgmrk2, hszmrk2⟩
      · exact ⟨a, by simp only [h2, h1, C.Space.get, C.Space.put, hr, C.upd_ne _ _ _ _ heq] at hga ⊢; exact hga, hsza⟩
    · intro _ ms hgm hszm hpa; exact ⟨ms, hgm, hszm, hpa, rfl⟩
  have hfr2 : FreshNextBlk h2 := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, hma, ?_, hic, hsr, hcp, hq, hhu, hsm⟩
    rcases hr : ctx.rmrk with ⟨bm0⟩
    by_cases heq : k = bm0
    · subst heq; simp only [C.Space.get, hr] at hgmrk; rw [hmr] at hgmrk; cases hgmrk
    · simp only [h2, h1, C.Space.put, hr, C.upd_ne _ _ _ _ heq]; exact hmr
  have hp2 : ParserEnv ctx h2 := by
    refine ⟨hcore2, hfr2, dcs.set! 0 dc', dc', errs, mems, masters, ics, mrks.set! 0 mrk', srcs,
      hgdc2, hszdc2, hdc2.symm, (kerr.trans (hdc0 ▸ herrp)), (by cases ctx.rmrk; exact hgerr), hszerr, hrem, hnw0,
      (kmem.trans (hdc0 ▸ hmemp)), (by cases ctx.rmrk; exact hgmem), hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz,
      hpm, hpi, hpmk, hps,
      (kmas.trans (hdc0 ▸ hmasp)), (by cases ctx.rmrk; exact hgmas), hszmas,
      (kic.trans (hdc0 ▸ hicp)), (by cases ctx.rmrk; exact hgic), hszic, hric, hci,
      (kmrk.trans (hdc0 ▸ hmrkp)), hgmrk2, hszmrk2,
      (by rw [hmrk2, kmrm]; exact hrm), (by rw [hmrk2, kmrmr]; exact hrmr),
      (by rw [hmrk2, kmpcom]; exact hpcom), (by rw [hmrk2, kmpapp]; exact hpappSz),
      (fun i hi => by rw [hmrk2, kmpapp]; exact hpapp i hi), (by rw [hmrk2, kmll]; exact hllSz),
      (ksrc.trans (hdc0 ▸ hsrcp)), (by cases ctx.rmrk; exact hgsrc), hszsrc,
      his, hts, hsip, hrtr, hfill, hcurv,
      (Or.inl (by rw [hmrk2]; exact kmcm)),
      (by rw [kml, ← hdc0]; rcases hmlEnd with h1' | h2' | h3'
          · exact Or.inl h1'
          · exact Or.inr (Or.inl h2')
          · exact Or.inr (Or.inr h3')),
      (fun hne => absurd (by rw [hmrk2]; exact kmsof) hne),
      (fun hne => absurd kcomp hne),
      (by rw [kqt, ← hdc0]; exact hqtSz), (fun i hi => by rw [kqt, ← hdc0]; exact hqt i hi),
      (by rw [kdh, ← hdc0]; exact hdhSz), (fun i hi => by rw [kdh, ← hdc0]; exact hdh i hi),
      (by rw [kah, ← hdc0]; exact hahSz), (fun i hi => by rw [kah, ← hdc0]; exact hah i hi),
      (by rw [kcc, ← hdc0]; exact hccSz), kisn⟩
  refine ⟨hp2, fun mrks' dcs' hgm' _ hgd' _ _ => ?_⟩
  rw [Option.some.inj (hgd'.symm.trans hgdc2), hdc2]; exact kcomp

theorem reset_input_controller_ok {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ h',
      C.run (reset_input_controller (.ref (.decomp ctx.bdc) 0)) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      CompSawZero ctx h' ∧
      (∀ dcs', C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
        dcs'[0]!.inputScanNumber = 0 ∧ dcs'[0]!.unreadMarker = 0) ∧
      (∀ ics', C.Space.get h' ctx.ric = some ics' → 0 < ics'.size →
        ics'[0]!.inheaders = TRUE ∧ ics'[0]!.eoiReached = FALSE ∧
        ics'[0]!.consumeInput = .fn "consume_markers" ∧ ics'[0]!.hasMultipleScans = FALSE) ∧
      (∀ mrks', C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
        mrks'[0]!.sawSOI = 0 ∧ mrks'[0]!.sawSOF = 0 ∧ mrks'[0]!.curMarker = .null) ∧
      (∀ errs', C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
        errs'[0]!.numWarnings = 0) ∧
      (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size → srcs'[0]! = srcs0[0]!) := by
  obtain ⟨dcs0, hgdc0, hszdc0, kerr0, kmem0, kmas0, kic0, kmrk0, ksrc0⟩ := parserEnv_get_dc hp
  obtain ⟨ics0, hgic0, hszic0, hric0, _⟩ := parserEnv_get_ic hp
  obtain ⟨errs0, hgerr0, hszerr0, hrem0⟩ := parserEnv_get_err hp
  obtain ⟨mrks0, hgmrk0, hszmrk0, _, hrmr0, _, _, _, _⟩ := parserEnv_get_mrk hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlic0 := ptr_load_ok (r := ctx.ric) (off := 0) hgic0 hszic0
  have hlic0' : C.run (Ptr.load dcs0[0]!.inputctl) h = .ok (ics0[0]!, h) := by rw [kic0]; exact hlic0
  have hroIc0 : C.Space.ro h ctx.ric = false := by cases ctx.ric; rfl
  let ic1 : C.JpegInputController := {
    ics0[0]! with
    consumeInput := .fn "consume_markers"
    hasMultipleScans := FALSE
    eoiReached := FALSE
    inheaders := TRUE
  }
  have hstic1 := ptr_store_ok (r := ctx.ric) (off := 0) (v := ic1) hgic0 hroIc0 hszic0
  have hstic1' : C.run (Ptr.store dcs0[0]!.inputctl ic1) h = .ok ((), C.Space.put h ctx.ric (ics0.set! 0 ic1)) := by
    rw [kic0]; exact hstic1
  let h1 := C.Space.put h ctx.ric (ics0.set! 0 ic1)
  have hp1 : ParserEnv ctx h1 := parserEnv_put_ic hp hgic0 hszic0 hric0 (Or.inl rfl)
  have hgerr1 : C.Space.get h1 ctx.rerr = some errs0 := by
    rcases h1r : ctx.rerr with ⟨be⟩; rcases h2r : ctx.ric with ⟨bi⟩
    simp only [h1, C.Space.get, C.Space.put, h1r, h2r] at hgerr0 ⊢; exact hgerr0
  have hgdc1 : C.Space.get h1 (C.DecompRef.decomp ctx.bdc) = some dcs0 := hgdc0
  have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc0
  have hlerr1 := ptr_load_ok (r := ctx.rerr) (off := 0) hgerr1 hszerr0
  have hlerr1' : C.run (Ptr.load dcs0[0]!.err) h1 = .ok (errs0[0]!, h1) := by rw [kerr0]; exact hlerr1
  have hroErr1 : C.Space.ro h1 ctx.rerr = false := by cases ctx.rerr; rfl
  let err2 : C.JpegErrorMgr := { errs0[0]! with numWarnings := 0, msgCode := 0 }
  have hsterr1 := ptr_store_ok (r := ctx.rerr) (off := 0) (v := err2) hgerr1 hroErr1 hszerr0
  have hsterr1' : C.run (Ptr.store dcs0[0]!.err err2) h1 = .ok ((), C.Space.put h1 ctx.rerr (errs0.set! 0 err2)) := by
    rw [kerr0]; exact hsterr1
  let h2 := C.Space.put h1 ctx.rerr (errs0.set! 0 err2)
  have hrunErr : C.run (reset_error_mgr (.ref (.decomp ctx.bdc) 0)) h1 = .ok ((), h2) := by
    unfold reset_error_mgr; rw [C.run_bind, hldc1]; dsimp only
    rw [C.run_bind, hlerr1']; dsimp only; exact hsterr1'
  have hp2 : ParserEnv ctx h2 := parserEnv_put_err hp1 hgerr1 hszerr0 rfl
    (by show (0 : Int) ≤ (0 : Int64).toInt; decide)
  have hgdc2 : C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs0 := by
    rcases h1r : ctx.rerr with ⟨be⟩; simp only [h2, C.Space.get, C.Space.put, h1r] at hgdc1 ⊢; exact hgdc1
  have hgmrk2 : C.Space.get h2 ctx.rmrk = some mrks0 := by
    rcases h1r : ctx.rerr with ⟨be⟩; rcases h2r : ctx.rmrk with ⟨bm⟩; rcases h3r : ctx.ric with ⟨bi⟩
    simp only [h2, h1, C.Space.get, C.Space.put, h1r, h2r, h3r] at hgmrk0 ⊢; exact hgmrk0
  have hldc2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc2 hszdc0
  have hlmrk2 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk2 hszmrk0
  have hlmrk2' : C.run (Ptr.load dcs0[0]!.marker) h2 = .ok (mrks0[0]!, h2) := by rw [kmrk0]; exact hlmrk2
  have hroDc2 : C.Space.ro h2 (C.DecompRef.decomp ctx.bdc) = false := rfl
  let dc3 : C.JpegDecompressStruct := {
    dcs0[0]! with
    compInfo := .null
    inputScanNumber := 0
    unreadMarker := 0
  }
  have hstdc2 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc3) hgdc2 hroDc2 hszdc0
  let h3 := C.Space.put h2 (C.DecompRef.decomp ctx.bdc) (dcs0.set! 0 dc3)
  have hgmrk3 : C.Space.get h3 ctx.rmrk = some mrks0 := hgmrk2
  have hlmrk3 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk3 hszmrk0
  have hlmrk3' : C.run (Ptr.load dc3.marker) h3 = .ok (mrks0[0]!, h3) := by
    have hk3 : dc3.marker = dcs0[0]!.marker := rfl
    rw [hk3, kmrk0]; exact hlmrk3
  have hlmrk3'' : C.run (Ptr.load dcs0[0]!.marker) h3 = .ok (mrks0[0]!, h3) := hlmrk3'
  have hroMrk3 : C.Space.ro h3 ctx.rmrk = false := by cases ctx.rmrk; rfl
  let mrk4 : C.JpegMarkerReader := {
    mrks0[0]! with
    sawSOI := FALSE
    sawSOF := FALSE
    discardedBytes := 0
    curMarker := .null
  }
  have hstmrk3 := ptr_store_ok (r := ctx.rmrk) (off := 0) (v := mrk4) hgmrk3 hroMrk3 hszmrk0
  have hstmrk3' : C.run (Ptr.store dcs0[0]!.marker mrk4) h3 = .ok ((), C.Space.put h3 ctx.rmrk (mrks0.set! 0 mrk4)) := by
    rw [kmrk0]; exact hstmrk3
  let h4 := C.Space.put h3 ctx.rmrk (mrks0.set! 0 mrk4)
  have hrunMrk : C.run (reset_marker_reader (.ref (.decomp ctx.bdc) 0)) h2 = .ok ((), h4) := by
    unfold reset_marker_reader; rw [C.run_bind, hldc2]; dsimp only
    rw [C.run_bind, hstdc2]; dsimp only; rw [C.run_bind, hlmrk3'']; dsimp only; exact hstmrk3'
  have ⟨hp4, hsaw4⟩ := parserEnv_put_dc_and_mrk_reset (dc' := dc3) (mrk' := mrk4)
    hp2 hgdc2 hszdc0 hgmrk2 hszmrk0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by show (0 : Int) ≤ (0 : Int32).toInt; decide)
    rfl rfl rfl rfl rfl rfl rfl
  have hgdc4 : C.Space.get h4 (C.DecompRef.decomp ctx.bdc) = some (dcs0.set! 0 dc3) := by
    cases ctx.rmrk; simp [h4, h3, C.Space.get, C.Space.put]
  have hszdc4 : 0 < (dcs0.set! 0 dc3).size := by simpa using hszdc0
  have hdc4_bang : (dcs0.set! 0 dc3)[0]! = dc3 := set0_bang_m dcs0 hszdc0 dc3
  have hldc4 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc4 hszdc4
  have hgmrk4 : C.Space.get h4 ctx.rmrk = some (mrks0.set! 0 mrk4) := by
    rcases hr : ctx.rmrk with ⟨bm⟩; simp [h4, C.Space.get, C.Space.put, hr, C.upd_same]
  have hszmrk4 : 0 < (mrks0.set! 0 mrk4).size := by simpa using hszmrk0
  have hmrk4_bang : (mrks0.set! 0 mrk4)[0]! = mrk4 := set0_bang_m mrks0 hszmrk0 mrk4
  have hlmrk4 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk4 hszmrk4
  have hlmrk4' : C.run (Ptr.load dc3.marker) h4 = .ok (mrk4, h4) := by
    have hkm3 : dc3.marker = .ref ctx.rmrk 0 := kmrk0
    rw [hkm3, hlmrk4, hmrk4_bang]
  have hroDc4 : C.Space.ro h4 (C.DecompRef.decomp ctx.bdc) = false := rfl
  let dc5 : C.JpegDecompressStruct := {
    dc3 with
    coefBits := .null
    unreadMarker := 0
  }
  have hstdc4 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc5) hgdc4 hroDc4 hszdc4
  let h5 := C.Space.put h4 (C.DecompRef.decomp ctx.bdc) ((dcs0.set! 0 dc3).set! 0 dc5)
  have hp5 : ParserEnv ctx h5 := parserEnv_put_dc_keep' (dc' := dc5) hp4 hgdc4 hszdc4
    (by rw [hdc4_bang]) (by rw [hdc4_bang]) (by rw [hdc4_bang])
    (by rw [hdc4_bang]) (by rw [hdc4_bang]) (by rw [hdc4_bang])
    (by rw [hdc4_bang]) (by rw [hdc4_bang]) (by rw [hdc4_bang])
    (by rw [hdc4_bang]) (by rw [hdc4_bang]) (by rw [hdc4_bang])
    (by rw [hdc4_bang]) (by rw [hdc4_bang])
  have hsaw5 : CompSawZero ctx h5 := compSawZero_put_dc_keep (dc' := dc5) hsaw4 hgdc4 hszdc4 (by rw [hdc4_bang])
  refine ⟨h5, ?_, hp5, hsaw5, ?_, ?_, ?_, ?_, ?_⟩
  · unfold reset_input_controller
    rw [C.run_bind, hldc0]; dsimp only
    rw [C.run_bind, hlic0']; dsimp only
    rw [C.run_bind, hstic1']; dsimp only
    rw [C.run_bind, hlerr1']; dsimp only
    have hremEq : (errs0[0]!.resetErrorMgr == .fn "reset_error_mgr") = true := by simp [hrem0]
    simp only [hremEq, ↓reduceIte, C.run_bind, hrunErr]
    rw [hldc2]; dsimp only
    rw [hlmrk2']; dsimp only
    have hrmrEq : (mrks0[0]!.resetMarkerReader == .fn "reset_marker_reader") = true := by simp [hrmr0]
    simp only [hrmrEq, ↓reduceIte, C.run_bind, hrunMrk]
    rw [hldc4, hdc4_bang]; dsimp only
    exact hstdc4
  · intro dcs' hgd' _
    have hg5 : C.Space.get h5 (C.DecompRef.decomp ctx.bdc) = some ((dcs0.set! 0 dc3).set! 0 dc5) := by
      simp [h5, C.Space.get, C.Space.put]
    rw [Option.some.inj (hgd'.symm.trans hg5), set0_bang_m _ hszdc4 dc5]
    exact ⟨rfl, rfl⟩
  · intro ics' hgi' _
    have hgi5 : C.Space.get h5 ctx.ric = some (ics0.set! 0 ic1) := by
      rcases hric : ctx.ric with ⟨bi⟩
      simp [h5, h4, h3, h2, h1, C.Space.get, C.Space.put, hric, C.upd_same]
    rw [Option.some.inj (hgi'.symm.trans hgi5), set0_bang_m ics0 hszic0 ic1]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro mrks' hgm' _
    have hgm5 : C.Space.get h5 ctx.rmrk = some (mrks0.set! 0 mrk4) := hgmrk4
    rw [Option.some.inj (hgm'.symm.trans hgm5), hmrk4_bang]
    exact ⟨rfl, rfl, rfl⟩
  · intro errs' hge' _
    have hge5 : C.Space.get h5 ctx.rerr = some (errs0.set! 0 err2) := by
      rcases hre : ctx.rerr with ⟨be⟩
      simp [h5, h4, h3, h2, C.Space.get, C.Space.put, hre, C.upd_same]
    rw [Option.some.inj (hge'.symm.trans hge5), set0_bang_m errs0 hszerr0 err2]
  · intro srcsA srcsB hgsA _ hgsB _
    have hgs5 : C.Space.get h5 ctx.rs = some srcsA := by
      rcases hre : ctx.rerr with ⟨be⟩; rcases hrm : ctx.rmrk with ⟨bm⟩
      rcases hri : ctx.ric with ⟨bi⟩; rcases hrs : ctx.rs with ⟨bs⟩
      simp only [h5, h4, h3, h2, h1, C.Space.get, C.Space.put, hre, hrm, hri, hrs] at hgsA ⊢
      exact hgsA
    rw [Option.some.inj (hgsB.symm.trans hgs5)]

/-! ## Full-frame `errexit` helpers preserving `ParserEnv` and `CompSawZero` -/

private theorem errMsgUpdate_full {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h) (code : Int32) (f : Array Int32 → Array Int32) :
    ∃ h',
      (∀ {α : Type} (k : C.M α),
        C.run (do
          let err ← C.Ptr.load (.ref ctx.rerr 0)
          C.Ptr.store (.ref ctx.rerr 0) { err with msgCode := code, msgParmI := f err.msgParmI }
          k) h = C.run k h') ∧
      ParserEnv ctx h' ∧
      CompSawZero ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.inputctls = h.inputctls ∧ h'.mems = h.mems ∧
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
  have hd : h'.decomps = h.decomps := by cases ctx.rerr; rfl
  have hm : h'.markers = h.markers := by cases ctx.rerr; rfl
  have hc : h'.comps = h.comps := by cases ctx.rerr; rfl
  refine ⟨h', ?_, hp', compSawZero_of_stable hsaw (decompHeaderStable_of_same hd hm hc) hp,
    hd, hm, (by cases ctx.rerr; rfl), (by cases ctx.rerr; rfl), hc,
    (by cases ctx.rerr; rfl), (by cases ctx.rerr; rfl), (by cases ctx.rerr; rfl), (by cases ctx.rerr; rfl), ?_⟩
  · intro _α k; rw [C.run_bind, hl]; dsimp only; rw [C.run_bind, hs]
  · intro errs1 errs' hg1 _ hg'
    have he1 := Option.some.inj (hg1.symm.trans hgerr)
    have hge' : C.Space.get h' ctx.rerr = some (errs.set! 0 err') := by
      rcases hr : ctx.rerr with ⟨be⟩; simp [h', C.Space.get, C.Space.put, hr]
    have he2 := Option.some.inj (hg'.symm.trans hge')
    refine ⟨by rw [he2]; simpa using hszerr, ?_⟩
    rw [he2, he1, set0_bang_m errs hszerr err']

private theorem errexit_full {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h) (code : Int32) :
    ∃ h',
      C.run (errexit (.ref ctx.rerr 0) code) h = .ok (.errExit code, h') ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.inputctls = h.inputctls ∧ h'.mems = h.mems ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hsaw', hd, hm, hsr, hma, hc, hq, hhu, hic, hme, hnw⟩ :=
    errMsgUpdate_full hp hsaw code (fun arr => arr)
  refine ⟨h', ?_, hp', hsaw', hd, hm, hsr, hma, hc, hq, hhu, hic, hme, hnw⟩
  unfold errexit; exact hk (pure (JpegRes.errExit code))

private theorem errexit1_full {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h) (code p1 : Int32) :
    ∃ h',
      C.run (errexit1 (.ref ctx.rerr 0) code p1) h = .ok (.errExit code, h') ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.inputctls = h.inputctls ∧ h'.mems = h.mems ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hsaw', hd, hm, hsr, hma, hc, hq, hhu, hic, hme, hnw⟩ :=
    errMsgUpdate_full hp hsaw code (fun arr => arr.set! 0 p1)
  refine ⟨h', ?_, hp', hsaw', hd, hm, hsr, hma, hc, hq, hhu, hic, hme, hnw⟩
  unfold errexit1; exact hk (pure (JpegRes.errExit code))

private theorem errexit2_full {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h) (code p1 p2 : Int32) :
    ∃ h',
      C.run (errexit2 (.ref ctx.rerr 0) code p1 p2) h = .ok (.errExit code, h') ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.comps = h.comps ∧ h'.quants = h.quants ∧
      h'.huffs = h.huffs ∧ h'.inputctls = h.inputctls ∧ h'.mems = h.mems ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨h', hk, hp', hsaw', hd, hm, hsr, hma, hc, hq, hhu, hic, hme, hnw⟩ :=
    errMsgUpdate_full hp hsaw code (fun arr => (arr.set! 0 p1).set! 1 p2)
  refine ⟨h', ?_, hp', hsaw', hd, hm, hsr, hma, hc, hq, hhu, hic, hme, hnw⟩
  unfold errexit2; exact hk (pure (JpegRes.errExit code))

/-! ## `initial_setup` -/

private theorem int32_max_bounds {a b : Int32} :
    a.toInt ≤ (if a > b then a else b).toInt ∧
    (if a > b then a else b).toInt ≤ max a.toInt b.toInt := by
  split
  · next hgt =>
    have := Int32.lt_iff_toInt_lt.mp hgt
    omega
  · next hle =>
    have : ¬ b.toInt < a.toInt := fun h => hle (Int32.lt_iff_toInt_lt.mpr h)
    omega

theorem initial_setup_ok {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw0 : CompSawZero ctx h)
    (hmrkSof : ∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size → mrks[0]!.sawSOF ≠ 0) :
    ∃ res h',
      C.run (initial_setup (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      CompSawZero ctx h' ∧
      (∀ errs0 errs', C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs0[0]!.numWarnings) ∧
      (∀ mrks0 mrks', C.Space.get h ctx.rmrk = some mrks0 → 0 < mrks0.size →
        C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size → mrks' = mrks0) ∧
      (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size → srcs' = srcs0) ∧
      (∀ dcs0 dcs',
        C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
        C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
        dcs'[0]!.inputScanNumber = dcs0[0]!.inputScanNumber ∧
        dcs'[0]!.unreadMarker = dcs0[0]!.unreadMarker) ∧
      (∀ ics0 ics', C.Space.get h ctx.ric = some ics0 → 0 < ics0.size →
        C.Space.get h' ctx.ric = some ics' → 0 < ics'.size →
        ics'[0]!.inheaders = ics0[0]!.inheaders ∧ ics'[0]!.eoiReached = ics0[0]!.eoiReached ∧
        ics'[0]!.consumeInput = ics0[0]!.consumeInput ∧
        ics'[0]!.resetInputController = ics0[0]!.resetInputController) ∧
      match res with
      | .errExit _ => True
      | .ok () =>
        (∀ mrks', C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size → mrks'[0]!.sawSOF ≠ 0) ∧
        (∀ dcs0 dcs',
          C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
          C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
          dcs'[0]!.entropyStartPass = dcs0[0]!.entropyStartPass ∧
          dcs'[0]!.coefStartInputPass = dcs0[0]!.coefStartInputPass ∧
          dcs'[0]!.coefConsumeData = dcs0[0]!.coefConsumeData) ∧
        (∀ dcs0 dcs',
          C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
          C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
          ScanCompsInRange h dcs0[0]! →
          dcs'[0]!.entropyStartPass = .fn "noop" →
          dcs'[0]!.coefStartInputPass = .fn "noop" →
          dcs'[0]!.coefConsumeData = .fn "dummy_consume_data" →
          MultiScanReady h' dcs'[0]!) := by
  obtain ⟨dcs0, hgdc0, hszdc0, kerr0, kmem0, kmas0, kic0, kmrk0, ksrc0⟩ := parserEnv_get_dc hp
  obtain ⟨masters0, hgmas0, hszmas0⟩ := parserEnv_get_mas hp
  obtain ⟨ics0, hgic0, hszic0, hric0, hci0⟩ := parserEnv_get_ic hp
  obtain ⟨errs0, hgerr0, hszerr0, _⟩ := parserEnv_get_err hp
  obtain ⟨dcsC, mrks0, hgdcC, _, hgmrk0, hszmrk0, hcompNe, hcompLive⟩ := parserEnv_get_comp hp
  have hEqC := Option.some.inj (hgdcC.symm.trans hgdc0)
  rw [hEqC] at hcompNe hcompLive
  have hsof0 : mrks0[0]!.sawSOF ≠ 0 := hmrkSof mrks0 hgmrk0 hszmrk0
  have hcpNe0 : dcs0[0]!.compInfo ≠ .null := hcompNe hsof0
  obtain ⟨hnc0, rcp, cs0, hci0_eq, hgcs0, hncLe0⟩ := hcompLive hcpNe0
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlmst0 := ptr_load_ok (r := ctx.rmas) (off := 0) hgmas0 hszmas0
  have hlmst0' : C.run (Ptr.load dcs0[0]!.master) h = .ok (masters0[0]!, h) := by rw [kmas0]; exact hlmst0
  let data_unit : Int32 := if (masters0[0]!.lossless != 0) = true then 1 else DCTSIZE
  have hduRange : data_unit = 1 ∨ data_unit = 8 := by
    dsimp only [data_unit]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hduPos : 0 < data_unit.toInt ∧ data_unit.toInt ≤ DCTSIZE.toInt := by
    rcases hduRange with hdu | hdu <;> rw [hdu] <;> decide
  by_cases hdim : (decide (Int64.ofNat dcs0[0]!.imageHeight.toNat > JPEG_MAX_DIMENSION) ||
      decide (Int64.ofNat dcs0[0]!.imageWidth.toNat > JPEG_MAX_DIMENSION)) = true
  · obtain ⟨hE, herr_run, hpE, hsawE, hdE, hmE, hsrE, _, _, _, _, hicE, _, hnwE⟩ :=
      errexit1_full hp hsaw0 JERR_IMAGE_TOO_BIG (Int32.ofInt JPEG_MAX_DIMENSION.toInt)
    refine ⟨.errExit JERR_IMAGE_TOO_BIG, hE, ?_, hpE, hsawE, hnwE,
      (fun m0 m' hm0 _ hm' _ => by
        simp only [C.Space.get] at hm0 hm'; rw [hmE] at hm'; exact Option.some.inj (hm'.symm.trans hm0)),
      (fun s0 s' hs0 _ hs' _ => by
        simp only [C.Space.get] at hs0 hs'; rw [hsrE] at hs'; exact Option.some.inj (hs'.symm.trans hs0)),
      (fun d0 d' hd0 _ hd' _ => by
        simp only [C.Space.get] at hd0 hd'; rw [hdE] at hd'
        rw [Option.some.inj (hd'.symm.trans hd0)]; exact ⟨rfl, rfl⟩),
      (fun i0 i' hi0 _ hi' _ => by
        simp only [C.Space.get] at hi0 hi'; rw [hicE] at hi'
        rw [Option.some.inj (hi'.symm.trans hi0)]; exact ⟨rfl, rfl, rfl, rfl⟩), trivial⟩
    · unfold initial_setup
      rw [C.run_bind, hldc0]; dsimp only
      rw [C.run_bind, hlmst0']; dsimp only
      simp only [hdim, ↓reduceIte, C.run_bind, kerr0, herr_run]; rfl
  · have hdimF : (decide (Int64.ofNat dcs0[0]!.imageHeight.toNat > JPEG_MAX_DIMENSION) ||
        decide (Int64.ofNat dcs0[0]!.imageWidth.toNat > JPEG_MAX_DIMENSION)) = false :=
      Bool.eq_false_iff.mpr hdim
    have himgBounds : dcs0[0]!.imageHeight.toNat ≤ 65500 ∧ dcs0[0]!.imageWidth.toNat ≤ 65500 := by
      have hH : ¬ (Int64.ofNat dcs0[0]!.imageHeight.toNat > JPEG_MAX_DIMENSION) := fun hgt =>
        hdim (by simp [hgt])
      have hW : ¬ (Int64.ofNat dcs0[0]!.imageWidth.toNat > JPEG_MAX_DIMENSION) := fun hgt =>
        hdim (by simp [hgt])
      have hbnd : ∀ n : UInt32, ¬ (Int64.ofNat n.toNat > JPEG_MAX_DIMENSION) → n.toNat ≤ 65500 := by
        intro n hn
        have hnLt : n.toNat < 2 ^ 32 := n.toFin.isLt
        have hlt : ¬ ((Int64.ofNat n.toNat).toInt > JPEG_MAX_DIMENSION.toInt) := fun h1 =>
          hn (Int64.lt_iff_toInt_lt.mpr h1)
        have hof : (Int64.ofNat n.toNat).toInt = (n.toNat : Int) := by
          change (Int64.ofInt (n.toNat : Int)).toInt = (n.toNat : Int)
          rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
          exact Int.bmod_eq_of_le (by omega) (by omega)
        have hjmd : JPEG_MAX_DIMENSION.toInt = 65500 := by decide
        omega
      exact ⟨hbnd _ hH, hbnd _ hW⟩
    by_cases hprec : (dcs0[0]!.dataPrecision != 8 && dcs0[0]!.dataPrecision != 12 &&
        dcs0[0]!.dataPrecision != 16) = true
    · obtain ⟨hE, herr_run, hpE, hsawE, hdE, hmE, hsrE, _, _, _, _, hicE, _, hnwE⟩ :=
        errexit1_full hp hsaw0 JERR_BAD_PRECISION dcs0[0]!.dataPrecision
      refine ⟨.errExit JERR_BAD_PRECISION, hE, ?_, hpE, hsawE, hnwE,
        (fun m0 m' hm0 _ hm' _ => by
          simp only [C.Space.get] at hm0 hm'; rw [hmE] at hm'; exact Option.some.inj (hm'.symm.trans hm0)),
        (fun s0 s' hs0 _ hs' _ => by
          simp only [C.Space.get] at hs0 hs'; rw [hsrE] at hs'; exact Option.some.inj (hs'.symm.trans hs0)),
        (fun d0 d' hd0 _ hd' _ => by
          simp only [C.Space.get] at hd0 hd'; rw [hdE] at hd'
          rw [Option.some.inj (hd'.symm.trans hd0)]; exact ⟨rfl, rfl⟩),
        (fun i0 i' hi0 _ hi' _ => by
          simp only [C.Space.get] at hi0 hi'; rw [hicE] at hi'
          rw [Option.some.inj (hi'.symm.trans hi0)]; exact ⟨rfl, rfl, rfl, rfl⟩), trivial⟩
      · unfold initial_setup
        rw [C.run_bind, hldc0]; dsimp only
        rw [C.run_bind, hlmst0']; dsimp only
        simp only [hdimF, hprec, Bool.false_eq_true, ↓reduceIte, C.run_bind, kerr0, herr_run]; rfl
    · have hprecF : (dcs0[0]!.dataPrecision != 8 && dcs0[0]!.dataPrecision != 12 &&
          dcs0[0]!.dataPrecision != 16) = false := Bool.eq_false_iff.mpr hprec
      by_cases hnc : dcs0[0]!.numComponents > MAX_COMPONENTS
      · obtain ⟨hE, herr_run, hpE, hsawE, hdE, hmE, hsrE, _, _, _, _, hicE, _, hnwE⟩ :=
          errexit2_full hp hsaw0 JERR_COMPONENT_COUNT dcs0[0]!.numComponents MAX_COMPONENTS
        refine ⟨.errExit JERR_COMPONENT_COUNT, hE, ?_, hpE, hsawE, hnwE,
          (fun m0 m' hm0 _ hm' _ => by
            simp only [C.Space.get] at hm0 hm'; rw [hmE] at hm'; exact Option.some.inj (hm'.symm.trans hm0)),
          (fun s0 s' hs0 _ hs' _ => by
            simp only [C.Space.get] at hs0 hs'; rw [hsrE] at hs'; exact Option.some.inj (hs'.symm.trans hs0)),
          (fun d0 d' hd0 _ hd' _ => by
            simp only [C.Space.get] at hd0 hd'; rw [hdE] at hd'
            rw [Option.some.inj (hd'.symm.trans hd0)]; exact ⟨rfl, rfl⟩),
          (fun i0 i' hi0 _ hi' _ => by
            simp only [C.Space.get] at hi0 hi'; rw [hicE] at hi'
            rw [Option.some.inj (hi'.symm.trans hi0)]; exact ⟨rfl, rfl, rfl, rfl⟩), trivial⟩
        · unfold initial_setup
          rw [C.run_bind, hldc0]; dsimp only
          rw [C.run_bind, hlmst0']; dsimp only
          simp only [hdimF, hprecF, Bool.false_eq_true, ↓reduceIte, hnc, C.run_bind, kerr0, herr_run]; rfl
      · have hncLe10 : dcs0[0]!.numComponents.toInt ≤ 10 := by
          have hm : MAX_COMPONENTS.toInt = 10 := by decide
          have := mt Int32.lt_iff_toInt_lt.mpr hnc
          omega
        let nComps : Nat := dcs0[0]!.numComponents.toInt.toNat
        have hncNat : nComps ≤ 10 := by dsimp only [nComps]; omega
        -- Store 1: maxHSampFactor := 1, maxVSampFactor := 1
        have hroDc0 : C.Space.ro h (C.DecompRef.decomp ctx.bdc) = false := rfl
        let dc1 : C.JpegDecompressStruct := { dcs0[0]! with maxHSampFactor := 1, maxVSampFactor := 1 }
        have hstdc1 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc1) hgdc0 hroDc0 hszdc0
        let h1 := C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs0.set! 0 dc1)
        have hp1 : ParserEnv ctx h1 := parserEnv_put_dc_keep' hp hgdc0 hszdc0
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hsaw1 : CompSawZero ctx h1 := compSawZero_put_dc_keep hsaw0 hgdc0 hszdc0 rfl
        have hgdc1 : C.Space.get h1 (C.DecompRef.decomp ctx.bdc) = some (dcs0.set! 0 dc1) := by
          simp [h1, C.Space.get, C.Space.put]
        have hszdc1 : 0 < (dcs0.set! 0 dc1).size := by simpa using hszdc0
        have hdc1_bang : (dcs0.set! 0 dc1)[0]! = dc1 := set0_bang_m dcs0 hszdc0 dc1
        have hgcs1 : C.Space.get h1 rcp = some cs0 := hgcs0
        -- Loop 1: check sampling factors & compute maxHSampFactor, maxVSampFactor
        let Inv1 (idx : Nat) (st : Option (JpegRes Unit) × Unit) (hCur : C.Heap) : Prop :=
          ParserEnv ctx hCur ∧ CompSawZero ctx hCur ∧
          hCur.markers = h.markers ∧ hCur.srcs = h.srcs ∧ hCur.inputctls = h.inputctls ∧
          hCur.masters = h.masters ∧ hCur.quants = h.quants ∧ hCur.huffs = h.huffs ∧
          hCur.comps = h.comps ∧
          (∀ dcsC, C.Space.get hCur (C.DecompRef.decomp ctx.bdc) = some dcsC → 0 < dcsC.size →
            dcsC[0]!.inputScanNumber = dcs0[0]!.inputScanNumber ∧
            dcsC[0]!.unreadMarker = dcs0[0]!.unreadMarker) ∧
          (∀ errs1, C.Space.get hCur ctx.rerr = some errs1 → 0 < errs1.size →
            errs1[0]!.numWarnings = errs0[0]!.numWarnings) ∧
          match st.1 with
          | some r => idx = nComps ∧ ∃ code, r = .errExit code
          | none =>
            hCur.errMgrs = h.errMgrs ∧
            ∃ dcsC, C.Space.get hCur (C.DecompRef.decomp ctx.bdc) = some dcsC ∧ 0 < dcsC.size ∧
              { (dcsC[0]!) with maxHSampFactor := dcs0[0]!.maxHSampFactor,
                                maxVSampFactor := dcs0[0]!.maxVSampFactor } = dcs0[0]! ∧
              1 ≤ dcsC[0]!.maxHSampFactor.toInt ∧ dcsC[0]!.maxHSampFactor.toInt ≤ 4 ∧
              1 ≤ dcsC[0]!.maxVSampFactor.toInt ∧ dcsC[0]!.maxVSampFactor.toInt ≤ 4 ∧
              (∀ j < idx, j < cs0.size →
                1 ≤ cs0[j]!.hSampFactor.toInt ∧ cs0[j]!.hSampFactor.toInt ≤ 4 ∧
                1 ≤ cs0[j]!.vSampFactor.toInt ∧ cs0[j]!.vSampFactor.toInt ≤ 4)
        have hInv1_init : Inv1 0 (none, ()) h1 := by
          refine ⟨hp1, hsaw1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, (fun errs1 hg1 _ => ?_), rfl,
            dcs0.set! 0 dc1, hgdc1, hszdc1, ?_,
            (by rw [hdc1_bang]; show (1 : Int) ≤ (1 : Int32).toInt; decide),
            (by rw [hdc1_bang]; show (1 : Int32).toInt ≤ 4; decide),
            (by rw [hdc1_bang]; show (1 : Int) ≤ (1 : Int32).toInt; decide),
            (by rw [hdc1_bang]; show (1 : Int32).toInt ≤ 4; decide), fun j hj => by omega⟩
          · intro dcsC hgdC _; rw [Option.some.inj (hgdC.symm.trans hgdc1), hdc1_bang]; exact ⟨rfl, rfl⟩
          · rw [Option.some.inj (hg1.symm.trans hgerr0)]
          · rw [hdc1_bang]
        let step1 : Nat → Option (JpegRes Unit) × Unit → M (ForInStep (Option (JpegRes Unit) × Unit)) :=
          fun ci _ => do
            let dcCur ← Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
            let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
            let comp ← Ptr.load cp
            if (decide (comp.hSampFactor ≤ 0) || decide (comp.hSampFactor > MAX_SAMP_FACTOR) ||
                decide (comp.vSampFactor ≤ 0) || decide (comp.vSampFactor > MAX_SAMP_FACTOR)) = true then
              let _ ← errexit dcCur.err JERR_BAD_SAMPLING
              return ForInStep.done (some (.errExit JERR_BAD_SAMPLING), ())
            else
              Ptr.store (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
                { dcCur with
                  maxHSampFactor := max dcCur.maxHSampFactor comp.hSampFactor
                  maxVSampFactor := max dcCur.maxVSampFactor comp.vSampFactor }
              return ForInStep.yield (none, ())
        have hloop1 : ∃ st1 hL1,
            C.run (forIn (List.range nComps) (none, ()) step1) h1 = .ok (st1, hL1) ∧ Inv1 nComps st1 hL1 := by
          refine forIn_range_inv Inv1 step1 nComps ?_ hInv1_init
          intro idx hlt ⟨o, u⟩ hCur hinv
          rcases o with _ | r
          · obtain ⟨hpC, hsawC, hmC, hsrC, hicC, hmaC, hqC, hhuC, hcpC, hdisnC, hnwC, herC,
              dcsC, hgdcC, hszdcC, hdcSameC, hmHLo, hmHHi, hmVLo, hmVHi, hprev⟩ := hinv
            have hldcC := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcC hszdcC
            have hcpSame : dcsC[0]!.compInfo = dcs0[0]!.compInfo := by
              have h1' := congrArg C.JpegDecompressStruct.compInfo hdcSameC; simpa using h1'
            have herrSame : dcsC[0]!.err = dcs0[0]!.err := by
              have h1' := congrArg C.JpegDecompressStruct.err hdcSameC; simpa using h1'
            have hgcsC : C.Space.get hCur rcp = some cs0 := by
              rcases rcp with ⟨bc⟩; simp only [C.Space.get] at hgcs0 ⊢; rw [hcpC]; exact hgcs0
            have hidxSz : idx < cs0.size := by omega
            have haddBounds : (0 : Int) ≤ 0 + (idx : Int) ∧ (0 : Int) + (idx : Int) ≤ cs0.size := by omega
            have hadd := ptr_add_ok (r := rcp) (off := 0) (k := Int.ofNat idx) hgcsC
              (Nat.zero_le _) haddBounds.1 haddBounds.2
            have hadd' : C.run (Ptr.add dcsC[0]!.compInfo (Int.ofNat idx)) hCur = .ok (.ref rcp idx, hCur) := by
              rw [hcpSame, hci0_eq]; simpa using hadd
            have hlcomp := ptr_load_ok (r := rcp) (off := idx) hgcsC hidxSz
            let comp := cs0[idx]!
            by_cases hbad : (decide (comp.hSampFactor ≤ 0) || decide (comp.hSampFactor > MAX_SAMP_FACTOR) ||
                decide (comp.vSampFactor ≤ 0) || decide (comp.vSampFactor > MAX_SAMP_FACTOR)) = true
            · obtain ⟨hE, herr_run, hpE, hsawE, hdE, hmE, hsrE, hmaE, hcpE, hqE, hhuE, hicE, _, hnwE⟩ :=
                errexit_full hpC hsawC JERR_BAD_SAMPLING
              refine ⟨.done (some (.errExit JERR_BAD_SAMPLING), ()), hE, ?_,
                hpE, hsawE, hmE.trans hmC, hsrE.trans hsrC, hicE.trans hicC, hmaE.trans hmaC,
                hqE.trans hqC, hhuE.trans hhuC, hcpE.trans hcpC, ?_, ?_, rfl, JERR_BAD_SAMPLING, rfl⟩
              · dsimp only [step1]
                rw [C.run_bind, hldcC]; dsimp only
                rw [C.run_bind, hadd']; dsimp only
                rw [C.run_bind, hlcomp]; dsimp only
                have hbad' : (decide (cs0[idx]!.hSampFactor ≤ 0) || decide (cs0[idx]!.hSampFactor > MAX_SAMP_FACTOR) ||
                    decide (cs0[idx]!.vSampFactor ≤ 0) || decide (cs0[idx]!.vSampFactor > MAX_SAMP_FACTOR)) = true := hbad
                simp only [hbad', ↓reduceIte, C.run_bind, herrSame, kerr0, herr_run]; rfl
              · intro dcsE hgdE hszE
                simp only [C.Space.get] at hgdE hgdcC; rw [hdE] at hgdE
                rw [Option.some.inj (hgdE.symm.trans hgdcC)]
                exact hdisnC dcsC hgdcC hszdcC
              · intro errs1 hg1 hsz1
                obtain ⟨errsC, hgC, hszC, _⟩ := parserEnv_get_err hpC
                obtain ⟨_, heq1⟩ := hnwE errsC errs1 hgC hszC hg1
                rw [heq1]; exact hnwC errsC hgC hszC
            · have hbadF : (decide (comp.hSampFactor ≤ 0) || decide (comp.hSampFactor > MAX_SAMP_FACTOR) ||
                  decide (comp.vSampFactor ≤ 0) || decide (comp.vSampFactor > MAX_SAMP_FACTOR)) = false :=
                Bool.eq_false_iff.mpr hbad
              have hcompBounds : 1 ≤ comp.hSampFactor.toInt ∧ comp.hSampFactor.toInt ≤ 4 ∧
                  1 ≤ comp.vSampFactor.toInt ∧ comp.vSampFactor.toInt ≤ 4 := by
                have h1 : ¬ (comp.hSampFactor ≤ 0) := fun x => hbad (by simp [x])
                have h2 : ¬ (comp.hSampFactor > MAX_SAMP_FACTOR) := fun x => hbad (by simp [x])
                have h3 : ¬ (comp.vSampFactor ≤ 0) := fun x => hbad (by simp [x])
                have h4 : ¬ (comp.vSampFactor > MAX_SAMP_FACTOR) := fun x => hbad (by simp [x])
                have hm4 : MAX_SAMP_FACTOR.toInt = 4 := by decide
                have hh1 : ¬ (comp.hSampFactor.toInt ≤ (0 : Int32).toInt) := fun x =>
                  h1 (Int32.le_iff_toInt_le.mpr x)
                have hh2 : ¬ ((4 : Int32).toInt < comp.hSampFactor.toInt) := fun x =>
                  h2 (Int32.lt_iff_toInt_lt.mpr (by rw [hm4]; exact x))
                have hv1 : ¬ (comp.vSampFactor.toInt ≤ (0 : Int32).toInt) := fun x =>
                  h3 (Int32.le_iff_toInt_le.mpr x)
                have hv2 : ¬ ((4 : Int32).toInt < comp.vSampFactor.toInt) := fun x =>
                  h4 (Int32.lt_iff_toInt_lt.mpr (by rw [hm4]; exact x))
                have h0i : (0 : Int32).toInt = 0 := rfl
                have h4i : (4 : Int32).toInt = 4 := rfl
                rw [h0i] at hh1 hv1; rw [h4i] at hh2 hv2
                omega
              let mh := max dcsC[0]!.maxHSampFactor comp.hSampFactor
              let mv := max dcsC[0]!.maxVSampFactor comp.vSampFactor
              let dcN : C.JpegDecompressStruct := { (dcsC[0]!) with maxHSampFactor := mh, maxVSampFactor := mv }
              have hroC : C.Space.ro hCur (C.DecompRef.decomp ctx.bdc) = false := rfl
              have hstdcN := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcN) hgdcC hroC hszdcC
              let hN := C.Space.put hCur (C.DecompRef.decomp ctx.bdc) (dcsC.set! 0 dcN)
              have hpN : ParserEnv ctx hN := parserEnv_put_dc_keep' hpC hgdcC hszdcC
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              have hsawN : CompSawZero ctx hN := compSawZero_put_dc_keep hsawC hgdcC hszdcC rfl
              have hgdcN : C.Space.get hN (C.DecompRef.decomp ctx.bdc) = some (dcsC.set! 0 dcN) := by
                simp [hN, C.Space.get, C.Space.put]
              have hszdcN : 0 < (dcsC.set! 0 dcN).size := by simpa using hszdcC
              have hdcN_bang : (dcsC.set! 0 dcN)[0]! = dcN := set0_bang_m dcsC hszdcC dcN
              refine ⟨.yield (none, ()), hN, ?_, hpN, hsawN, hmC, hsrC, hicC, hmaC, hqC, hhuC, hcpC,
                ?_, hnwC, herC, dcsC.set! 0 dcN, hgdcN, hszdcN, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · dsimp only [step1]
                rw [C.run_bind, hldcC]; dsimp only
                rw [C.run_bind, hadd']; dsimp only
                rw [C.run_bind, hlcomp]; dsimp only
                have hbadF' : (decide (cs0[idx]!.hSampFactor ≤ 0) || decide (cs0[idx]!.hSampFactor > MAX_SAMP_FACTOR) ||
                    decide (cs0[idx]!.vSampFactor ≤ 0) || decide (cs0[idx]!.vSampFactor > MAX_SAMP_FACTOR)) = false := hbadF
                simp only [hbadF', Bool.false_eq_true, ↓reduceIte, C.run_bind]
                rw [hstdcN]; rfl
              · intro dcsN hgdN _
                rw [Option.some.inj (hgdN.symm.trans hgdcN), hdcN_bang]
                exact hdisnC dcsC hgdcC hszdcC
              · rw [hdcN_bang, ← hdcSameC]
              · rw [hdcN_bang]
                have hlt : dcsC[0]!.maxHSampFactor.toInt ≤ mh.toInt := by
                  dsimp only [mh, max, maxOfLe]; split
                  · exact Int32.le_iff_toInt_le.mp ‹_›
                  · exact Int.le_refl _
                change 1 ≤ mh.toInt; omega
              · rw [hdcN_bang]
                change mh.toInt ≤ 4
                dsimp only [mh, max, maxOfLe]; split
                · exact hcompBounds.2.1
                · exact hmHHi
              · rw [hdcN_bang]
                have hlt : dcsC[0]!.maxVSampFactor.toInt ≤ mv.toInt := by
                  dsimp only [mv, max, maxOfLe]; split
                  · exact Int32.le_iff_toInt_le.mp ‹_›
                  · exact Int.le_refl _
                change 1 ≤ mv.toInt; omega
              · rw [hdcN_bang]
                change mv.toInt ≤ 4
                dsimp only [mv, max, maxOfLe]; split
                · exact hcompBounds.2.2.2
                · exact hmVHi
              · intro j hj _
                by_cases hji : j = idx
                · subst hji; exact hcompBounds
                · exact hprev j (by omega) (by omega)
          · rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, heqN, _⟩
            omega
        obtain ⟨⟨st1, _⟩, hL1, hrunL1, hInv1⟩ := hloop1
        rcases st1 with _ | r
        · obtain ⟨hpL1, hsawL1, hmL1, hsrL1, hicL1, hmaL1, hqL1, hhuL1, hcpL1, hdisnL1, hnwL1, herL1,
            dcs1, hgdc1', hszdc1', hdcSame1, hmHLo, hmHHi, hmVLo, hmVHi, hcompBnds⟩ := hInv1
          have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1' hszdc1'
          let dc2 : C.JpegDecompressStruct := {
            (dcs1[0]!) with
            minDctHScaledSize := data_unit
            minDctVScaledSize := data_unit
            blockSize := data_unit
            naturalOrder := .ref .st_natural_order 0
            limSe := DCTSIZE2 - 1
          }
          have hroDc1 : C.Space.ro hL1 (C.DecompRef.decomp ctx.bdc) = false := rfl
          have hstdc2 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc2) hgdc1' hroDc1 hszdc1'
          let h2 := C.Space.put hL1 (C.DecompRef.decomp ctx.bdc) (dcs1.set! 0 dc2)
          have hp2 : ParserEnv ctx h2 := parserEnv_put_dc_keep' hpL1 hgdc1' hszdc1'
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          have hsaw2 : CompSawZero ctx h2 := compSawZero_put_dc_keep hsawL1 hgdc1' hszdc1' rfl
          have hgdc2 : C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some (dcs1.set! 0 dc2) := by
            simp [h2, C.Space.get, C.Space.put]
          have hszdc2 : 0 < (dcs1.set! 0 dc2).size := by simpa using hszdc1'
          have hdc2_bang : (dcs1.set! 0 dc2)[0]! = dc2 := set0_bang_m dcs1 hszdc1' dc2
          have hcs2_same : C.Space.get h2 rcp = some cs0 := by
            dsimp only [h2]; rcases rcp with ⟨bc⟩
            simp only [C.Space.get, C.Space.put] at hgcs0 ⊢; rw [hcpL1]; exact hgcs0
          -- Loop 2: compute widthInBlocks, heightInBlocks, dctHScaledSize, downsampledWidth/Height
          let Inv2 (idx : Nat) (_st : PUnit) (hCur : C.Heap) : Prop :=
            ParserEnv ctx hCur ∧ CompSawZero ctx hCur ∧
            hCur.markers = h.markers ∧ hCur.srcs = h.srcs ∧ hCur.inputctls = h.inputctls ∧
            hCur.errMgrs = h.errMgrs ∧ hCur.quants = h.quants ∧ hCur.huffs = h.huffs ∧
            ∃ dcsC csC,
              C.Space.get hCur (C.DecompRef.decomp ctx.bdc) = some dcsC ∧ 0 < dcsC.size ∧
              dcsC[0]! = dc2 ∧
              C.Space.get hCur rcp = some csC ∧ csC.size = cs0.size ∧
              (∀ j, idx ≤ j → j < cs0.size → csC[j]! = cs0[j]!) ∧
              (∀ j < idx, j < cs0.size →
                1 ≤ csC[j]!.hSampFactor.toInt ∧ csC[j]!.hSampFactor.toInt ≤ 4 ∧
                1 ≤ csC[j]!.vSampFactor.toInt ∧ csC[j]!.vSampFactor.toInt ≤ 4 ∧
                0 ≤ csC[j]!.dctHScaledSize.toInt ∧ csC[j]!.dctHScaledSize.toInt ≤ DCTSIZE.toInt)
          have hInv2_init : Inv2 0 PUnit.unit h2 := by
            refine ⟨hp2, hsaw2, hmL1, hsrL1, hicL1, herL1, hqL1, hhuL1, dcs1.set! 0 dc2, cs0,
              hgdc2, hszdc2, hdc2_bang, hcs2_same, rfl, (fun _ _ _ => rfl), fun j hj => by omega⟩
          let step2 : Nat → PUnit → M (ForInStep PUnit) := fun ci _ => do
            let dcC ← Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
            let cp ← Ptr.add dcC.compInfo (Int.ofNat ci)
            let comp ← cp.load
            let wib ← jdiv_round_up
              (Int64.ofInt (Int.ofNat dcC.imageWidth.toNat * comp.hSampFactor.toInt))
              (Int64.ofInt (dcC.maxHSampFactor.toInt * data_unit.toInt))
            let hib ← jdiv_round_up
              (Int64.ofInt (Int.ofNat dcC.imageHeight.toNat * comp.vSampFactor.toInt))
              (Int64.ofInt (dcC.maxVSampFactor.toInt * data_unit.toInt))
            let mstC ← Ptr.load dcC.master
            Ptr.store dcC.master
              { mstC with
                firstMcuCol := mstC.firstMcuCol.set! ci 0
                lastMcuCol := mstC.lastMcuCol.set! ci (UInt32.ofNat wib.toInt.toNat - 1) }
            let dw ← jdiv_round_up
              (Int64.ofInt (Int.ofNat dcC.imageWidth.toNat * comp.hSampFactor.toInt))
              (Int64.ofInt dcC.maxHSampFactor.toInt)
            let dh ← jdiv_round_up
              (Int64.ofInt (Int.ofNat dcC.imageHeight.toNat * comp.vSampFactor.toInt))
              (Int64.ofInt dcC.maxVSampFactor.toInt)
            cp.store
              { comp with
                widthInBlocks := UInt32.ofNat wib.toInt.toNat
                heightInBlocks := UInt32.ofNat hib.toInt.toNat
                dctHScaledSize := data_unit
                dctVScaledSize := data_unit
                downsampledWidth := UInt32.ofNat dw.toInt.toNat
                downsampledHeight := UInt32.ofNat dh.toInt.toNat
                componentNeeded := TRUE
                quantTable := .null }
            return ForInStep.yield PUnit.unit
          have hloop2 : ∃ st2 hL2,
              C.run (forIn (List.range nComps) PUnit.unit step2) h2 = .ok (st2, hL2) ∧ Inv2 nComps st2 hL2 := by
            refine forIn_range_inv Inv2 step2 nComps ?_ hInv2_init
            intro idx hlt _ hCur hinv
            obtain ⟨hpC, hsawC, hmC, hsrC, hicC, herC, hqC, hhuC, dcsC, csC,
              hgdcC, hszdcC, hdcC_eq, hgcsC, hszCs, htailCs, hheadCs⟩ := hinv
            have hldcC := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcC hszdcC
            have hdcSame2 := hdcSame1
            have hcpEq : dc2.compInfo = dcs0[0]!.compInfo := by
              change dcs1[0]!.compInfo = dcs0[0]!.compInfo
              have h1' := congrArg C.JpegDecompressStruct.compInfo hdcSame2; simpa using h1'
            have hmasEq : dc2.master = dcs0[0]!.master := by
              change dcs1[0]!.master = dcs0[0]!.master
              have h1' := congrArg C.JpegDecompressStruct.master hdcSame2; simpa using h1'
            have himgW : dc2.imageWidth = dcs0[0]!.imageWidth := by
              change dcs1[0]!.imageWidth = dcs0[0]!.imageWidth
              have h1' := congrArg C.JpegDecompressStruct.imageWidth hdcSame2; simpa using h1'
            have himgH : dc2.imageHeight = dcs0[0]!.imageHeight := by
              change dcs1[0]!.imageHeight = dcs0[0]!.imageHeight
              have h1' := congrArg C.JpegDecompressStruct.imageHeight hdcSame2; simpa using h1'
            have hmaxH : dc2.maxHSampFactor = dcs1[0]!.maxHSampFactor := rfl
            have hmaxV : dc2.maxVSampFactor = dcs1[0]!.maxVSampFactor := rfl
            have hidxSzC : idx < csC.size := by omega
            have haddBounds : (0 : Int) ≤ 0 + (idx : Int) ∧ (0 : Int) + (idx : Int) ≤ csC.size := by omega
            have hadd := ptr_add_ok (r := rcp) (off := 0) (k := Int.ofNat idx) hgcsC
              (Nat.zero_le _) haddBounds.1 haddBounds.2
            have hadd' : C.run (Ptr.add dcsC[0]!.compInfo (Int.ofNat idx)) hCur = .ok (.ref rcp idx, hCur) := by
              rw [hdcC_eq, hcpEq, hci0_eq]; simpa using hadd
            have hlcomp := ptr_load_ok (r := rcp) (off := idx) hgcsC hidxSzC
            have hcsIdxEq : csC[idx]! = cs0[idx]! := htailCs idx (Nat.le_refl idx) (by omega)
            have hcb := hcompBnds idx hlt (by omega)
            rw [← hcsIdxEq] at hcb
            have hmulW : Int.ofNat dcs0[0]!.imageWidth.toNat * csC[idx]!.hSampFactor.toInt ≤ 65500 * 4 :=
              Int.mul_le_mul (by change (dcs0[0]!.imageWidth.toNat : Int) ≤ 65500; omega) hcb.2.1 (by omega) (by decide)
            have hmulW_lo : 0 ≤ Int.ofNat dcs0[0]!.imageWidth.toNat * csC[idx]!.hSampFactor.toInt :=
              Int.mul_nonneg (Int.natCast_nonneg _) (by omega)
            have hmulH : Int.ofNat dcs0[0]!.imageHeight.toNat * csC[idx]!.vSampFactor.toInt ≤ 65500 * 4 :=
              Int.mul_le_mul (by change (dcs0[0]!.imageHeight.toNat : Int) ≤ 65500; omega) hcb.2.2.2 (by omega) (by decide)
            have hmulH_lo : 0 ≤ Int.ofNat dcs0[0]!.imageHeight.toNat * csC[idx]!.vSampFactor.toInt :=
              Int.mul_nonneg (Int.natCast_nonneg _) (by omega)
            have hmulMH : dcs1[0]!.maxHSampFactor.toInt * data_unit.toInt ≤ 4 * 8 :=
              Int.mul_le_mul hmHHi hduPos.2 (by omega) (by decide)
            have hmulMH_lo : 0 < dcs1[0]!.maxHSampFactor.toInt * data_unit.toInt :=
              Int.mul_pos (by omega) (by omega)
            have hmulMV : dcs1[0]!.maxVSampFactor.toInt * data_unit.toInt ≤ 4 * 8 :=
              Int.mul_le_mul hmVHi hduPos.2 (by omega) (by decide)
            have hmulMV_lo : 0 < dcs1[0]!.maxVSampFactor.toInt * data_unit.toInt :=
              Int.mul_pos (by omega) (by omega)
            have hwibA : 0 ≤ (Int64.ofInt (Int.ofNat dcsC[0]!.imageWidth.toNat * csC[idx]!.hSampFactor.toInt)).toInt := by
              rw [hdcC_eq, himgW, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
            have hwibB : 0 < (Int64.ofInt (dcsC[0]!.maxHSampFactor.toInt * data_unit.toInt)).toInt := by
              rw [hdcC_eq, hmaxH, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
            have hwibSum : (Int64.ofInt (Int.ofNat dcsC[0]!.imageWidth.toNat * csC[idx]!.hSampFactor.toInt)).toInt +
                (Int64.ofInt (dcsC[0]!.maxHSampFactor.toInt * data_unit.toInt)).toInt < 2 ^ 63 := by
              rw [hdcC_eq, himgW, hmaxH, Int64.toInt_ofInt, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl,
                Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
              omega
            obtain ⟨wib, hwibRun, _⟩ := jdiv_round_up_functional hCur _ _ hwibA hwibB hwibSum
            have hhibA : 0 ≤ (Int64.ofInt (Int.ofNat dcsC[0]!.imageHeight.toNat * csC[idx]!.vSampFactor.toInt)).toInt := by
              rw [hdcC_eq, himgH, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
            have hhibB : 0 < (Int64.ofInt (dcsC[0]!.maxVSampFactor.toInt * data_unit.toInt)).toInt := by
              rw [hdcC_eq, hmaxV, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
            have hhibSum : (Int64.ofInt (Int.ofNat dcsC[0]!.imageHeight.toNat * csC[idx]!.vSampFactor.toInt)).toInt +
                (Int64.ofInt (dcsC[0]!.maxVSampFactor.toInt * data_unit.toInt)).toInt < 2 ^ 63 := by
              rw [hdcC_eq, himgH, hmaxV, Int64.toInt_ofInt, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl,
                Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
              omega
            obtain ⟨hib, hhibRun, _⟩ := jdiv_round_up_functional hCur _ _ hhibA hhibB hhibSum
            obtain ⟨mastersC, hgmasC, hszmasC⟩ := parserEnv_get_mas hpC
            have hlmstC := ptr_load_ok (r := ctx.rmas) (off := 0) hgmasC hszmasC
            have hlmstC' : C.run (Ptr.load dcsC[0]!.master) hCur = .ok (mastersC[0]!, hCur) := by
              rw [hdcC_eq, hmasEq, kmas0]; exact hlmstC
            have hroMstC : C.Space.ro hCur ctx.rmas = false := by cases ctx.rmas; rfl
            let mstN : C.JpegDecompMaster := {
              (mastersC[0]!) with
              firstMcuCol := mastersC[0]!.firstMcuCol.set! idx 0
              lastMcuCol := mastersC[0]!.lastMcuCol.set! idx (UInt32.ofNat wib.toInt.toNat - 1)
            }
            have hstmstC := ptr_store_ok (r := ctx.rmas) (off := 0) (v := mstN) hgmasC hroMstC hszmasC
            have hstmstC' : C.run (Ptr.store dcsC[0]!.master mstN) hCur =
                .ok ((), C.Space.put hCur ctx.rmas (mastersC.set! 0 mstN)) := by
              rw [hdcC_eq, hmasEq, kmas0]; exact hstmstC
            let hM := C.Space.put hCur ctx.rmas (mastersC.set! 0 mstN)
            have hdwA : 0 ≤ (Int64.ofInt (Int.ofNat dcsC[0]!.imageWidth.toNat * csC[idx]!.hSampFactor.toInt)).toInt := hwibA
            have hdwB : 0 < (Int64.ofInt dcsC[0]!.maxHSampFactor.toInt).toInt := by
              rw [hdcC_eq, hmaxH, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
            have hdwSum : (Int64.ofInt (Int.ofNat dcsC[0]!.imageWidth.toNat * csC[idx]!.hSampFactor.toInt)).toInt +
                (Int64.ofInt dcsC[0]!.maxHSampFactor.toInt).toInt < 2 ^ 63 := by
              rw [hdcC_eq, himgW, hmaxH, Int64.toInt_ofInt, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl,
                Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
              omega
            obtain ⟨dw, hdwRun, _⟩ := jdiv_round_up_functional hM _ _ hdwA hdwB hdwSum
            have hdhA : 0 ≤ (Int64.ofInt (Int.ofNat dcsC[0]!.imageHeight.toNat * csC[idx]!.vSampFactor.toInt)).toInt := hhibA
            have hdhB : 0 < (Int64.ofInt dcsC[0]!.maxVSampFactor.toInt).toInt := by
              rw [hdcC_eq, hmaxV, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
            have hdhSum : (Int64.ofInt (Int.ofNat dcsC[0]!.imageHeight.toNat * csC[idx]!.vSampFactor.toInt)).toInt +
                (Int64.ofInt dcsC[0]!.maxVSampFactor.toInt).toInt < 2 ^ 63 := by
              rw [hdcC_eq, himgH, hmaxV, Int64.toInt_ofInt, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl,
                Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
              omega
            obtain ⟨dh, hdhRun, _⟩ := jdiv_round_up_functional hM _ _ hdhA hdhB hdhSum
            have hgcsM : C.Space.get hM rcp = some csC := by
              dsimp only [hM]; rcases ctx.rmas with ⟨_⟩; rcases hr2 : rcp with ⟨bc⟩
              simp only [C.Space.get, C.Space.put, hr2] at hgcsC ⊢; exact hgcsC
            have hroCpM : C.Space.ro hM rcp = false := by cases rcp; rfl
            let compN : C.JpegCompInfo := {
              (csC[idx]!) with
              widthInBlocks := UInt32.ofNat wib.toInt.toNat
              heightInBlocks := UInt32.ofNat hib.toInt.toNat
              dctHScaledSize := data_unit
              dctVScaledSize := data_unit
              downsampledWidth := UInt32.ofNat dw.toInt.toNat
              downsampledHeight := UInt32.ofNat dh.toInt.toNat
              componentNeeded := TRUE
              quantTable := .null
            }
            have hstcompM := ptr_store_ok (r := rcp) (off := idx) (v := compN) hgcsM hroCpM hidxSzC
            let hN := C.Space.put hM rcp (csC.set! idx compN)
            have hpM : ParserEnv ctx hM := parserEnv_put_mst hpC hgmasC hszmasC (Or.inl rfl)
            have hsawM : CompSawZero ctx hM := compSawZero_put_mst hsawC
            have hpN : ParserEnv ctx hN := parserEnv_put_comp hpM hgcsM
            have hsawN : CompSawZero ctx hN := compSawZero_put_comp hsawM
            have hgdcN : C.Space.get hN (C.DecompRef.decomp ctx.bdc) = some dcsC := by
              dsimp only [hN, hM]; rcases ctx.rmas with ⟨_⟩; rcases rcp with ⟨_⟩
              simp only [C.Space.get, C.Space.put] at hgdcC ⊢; exact hgdcC
            have hgcsN : C.Space.get hN rcp = some (csC.set! idx compN) := by
              dsimp only [hN]; rcases rcp with ⟨_⟩
              simp only [C.Space.get, C.Space.put, C.upd_same]
            have hmN : hN.markers = h.markers := by
              have h1' : hN.markers = hCur.markers := by
                dsimp only [hN, hM]; rcases ctx.rmas with ⟨_⟩; rfl
              exact h1'.trans hmC
            have hsrN : hN.srcs = h.srcs := by
              have h1' : hN.srcs = hCur.srcs := by
                dsimp only [hN, hM]; rcases ctx.rmas with ⟨_⟩; rfl
              exact h1'.trans hsrC
            have hicN : hN.inputctls = h.inputctls := by
              have h1' : hN.inputctls = hCur.inputctls := by
                dsimp only [hN, hM]; rcases ctx.rmas with ⟨_⟩; rfl
              exact h1'.trans hicC
            have herN : hN.errMgrs = h.errMgrs := by
              have h1' : hN.errMgrs = hCur.errMgrs := by
                dsimp only [hN, hM]; rcases ctx.rmas with ⟨_⟩; rfl
              exact h1'.trans herC
            have hqN : hN.quants = h.quants := by
              have h1' : hN.quants = hCur.quants := by
                dsimp only [hN, hM]; rcases ctx.rmas with ⟨_⟩; rfl
              exact h1'.trans hqC
            have hhuN : hN.huffs = h.huffs := by
              have h1' : hN.huffs = hCur.huffs := by
                dsimp only [hN, hM]; rcases ctx.rmas with ⟨_⟩; rfl
              exact h1'.trans hhuC
            refine ⟨.yield PUnit.unit, hN, ?_, hpN, hsawN, hmN, hsrN, hicN, herN, hqN, hhuN,
              dcsC, csC.set! idx compN, hgdcN, hszdcC, hdcC_eq, hgcsN, (by simpa using hszCs), ?_, ?_⟩
            · dsimp only [step2]
              rw [C.run_bind, hldcC]; dsimp only
              rw [C.run_bind, hadd']; dsimp only
              rw [C.run_bind, hlcomp]; dsimp only
              rw [C.run_bind, hwibRun]; dsimp only
              rw [C.run_bind, hhibRun]; dsimp only
              rw [C.run_bind, hlmstC']; dsimp only
              rw [C.run_bind, hstmstC']; dsimp only
              rw [C.run_bind, hdwRun]; dsimp only
              rw [C.run_bind, hdhRun]; dsimp only
              rw [C.run_bind, hstcompM]; rfl
            · intro j hle hjLt
              have hne : idx ≠ j := by omega
              rw [array_set_bang_ne csC hidxSzC (by omega) hne compN]
              exact htailCs j (by omega) hjLt
            · intro j hjLt _
              by_cases hji : j = idx
              · subst hji
                rw [array_set_bang_self csC hidxSzC compN]
                exact ⟨hcb.1, hcb.2.1, hcb.2.2.1, hcb.2.2.2, Int.le_of_lt hduPos.1, hduPos.2⟩
              · rw [array_set_bang_ne csC hidxSzC (by omega) (Ne.symm hji) compN]
                exact hheadCs j (by omega) (by omega)
          obtain ⟨_, hL2, hrunL2, hInv2⟩ := hloop2
          obtain ⟨hpL2, hsawL2, hmL2, hsrL2, hicL2, herL2, hqL2, hhuL2,
            dcsL2, csL2, hgdcL2, hszdcL2, hdcL2_eq, hgcsL2, hszCsL2, _, hcsL2Bnds⟩ := hInv2
          have hldcL2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcL2 hszdcL2
          have hdcSameL2 := hdcSame1
          have himgH_L2 : dcsL2[0]!.imageHeight = dcs0[0]!.imageHeight := by
            rw [hdcL2_eq]; change dcs1[0]!.imageHeight = dcs0[0]!.imageHeight
            have h1' := congrArg C.JpegDecompressStruct.imageHeight hdcSameL2; simpa using h1'
          have hmaxV_L2 : dcsL2[0]!.maxVSampFactor = dcs1[0]!.maxVSampFactor := by rw [hdcL2_eq]
          have hmulMV_L2 : dcs1[0]!.maxVSampFactor.toInt * data_unit.toInt ≤ 4 * 8 :=
            Int.mul_le_mul hmVHi hduPos.2 (by omega) (by decide)
          have hmulMV_L2_lo : 0 < dcs1[0]!.maxVSampFactor.toInt * data_unit.toInt :=
            Int.mul_pos (by omega) (by omega)
          have htotA : 0 ≤ (Int64.ofNat dcsL2[0]!.imageHeight.toNat).toInt := by
            rw [himgH_L2]; change 0 ≤ (Int64.ofInt (dcs0[0]!.imageHeight.toNat : Int)).toInt
            rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
          have htotB : 0 < (Int64.ofInt (dcsL2[0]!.maxVSampFactor.toInt * data_unit.toInt)).toInt := by
            rw [hmaxV_L2, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
          have htotSum : (Int64.ofNat dcsL2[0]!.imageHeight.toNat).toInt +
              (Int64.ofInt (dcsL2[0]!.maxVSampFactor.toInt * data_unit.toInt)).toInt < 2 ^ 63 := by
            rw [himgH_L2, hmaxV_L2]; change (Int64.ofInt (dcs0[0]!.imageHeight.toNat : Int)).toInt + _ < 2 ^ 63
            rw [Int64.toInt_ofInt, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl,
              Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
            omega
          obtain ⟨totRows, htotRun, _⟩ := jdiv_round_up_functional hL2 _ _ htotA htotB htotSum
          have hroDcL2 : C.Space.ro hL2 (C.DecompRef.decomp ctx.bdc) = false := rfl
          let dc3 : C.JpegDecompressStruct := {
            (dcsL2[0]!) with totalIMcuRows := UInt32.ofNat totRows.toInt.toNat
          }
          have hstdc3 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc3) hgdcL2 hroDcL2 hszdcL2
          let h3 := C.Space.put hL2 (C.DecompRef.decomp ctx.bdc) (dcsL2.set! 0 dc3)
          have hp3 : ParserEnv ctx h3 := parserEnv_put_dc_keep' hpL2 hgdcL2 hszdcL2
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          have hsaw3 : CompSawZero ctx h3 := compSawZero_put_dc_keep hsawL2 hgdcL2 hszdcL2 rfl
          obtain ⟨icsL3, hgicL3, hszicL3, hricL3, hciL3⟩ := parserEnv_get_ic hp3
          have hlicL3 := ptr_load_ok (r := ctx.ric) (off := 0) hgicL3 hszicL3
          obtain ⟨dcs3P, hgdc3P, _, _, _, _, kic3P, _⟩ := parserEnv_get_dc hp3
          have hlicL3' : C.run (Ptr.load dc3.inputctl) h3 = .ok (icsL3[0]!, h3) := by
            have hd3Eq := Option.some.inj (hgdc3P.symm.trans (by simp [h3, C.Space.get, C.Space.put] : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcsL2.set! 0 dc3)))
            have hki3 : dc3.inputctl = .ref ctx.ric 0 := by
              rw [← set0_bang_m dcsL2 hszdcL2 dc3, ← hd3Eq]; exact kic3P
            rw [hki3]; exact hlicL3
          let ic3 : C.JpegInputController := {
            (icsL3[0]!) with
            hasMultipleScans :=
              if (decide (dcsL2[0]!.compsInScan < dcsL2[0]!.numComponents) || dcsL2[0]!.progressiveMode != 0) = true then TRUE else FALSE
          }
          have hroIcL3 : C.Space.ro h3 ctx.ric = false := by cases ctx.ric; rfl
          have hstic3 := ptr_store_ok (r := ctx.ric) (off := 0) (v := ic3) hgicL3 hroIcL3 hszicL3
          have hstic3' : C.run (Ptr.store dc3.inputctl ic3) h3 =
              .ok ((), C.Space.put h3 ctx.ric (icsL3.set! 0 ic3)) := by
            have hd3Eq := Option.some.inj (hgdc3P.symm.trans (by simp [h3, C.Space.get, C.Space.put] : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcsL2.set! 0 dc3)))
            have hki3 : dc3.inputctl = .ref ctx.ric 0 := by
              rw [← set0_bang_m dcsL2 hszdcL2 dc3, ← hd3Eq]; exact kic3P
            rw [hki3]; exact hstic3
          let h4 := C.Space.put h3 ctx.ric (icsL3.set! 0 ic3)
          have hp4 : ParserEnv ctx h4 := parserEnv_put_ic hp3 hgicL3 hszicL3 hricL3 hciL3
          have hsaw4 : CompSawZero ctx h4 := compSawZero_put_ic hsaw3
          refine ⟨.ok (), h4, ?_, hp4, hsaw4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · unfold initial_setup
            rw [C.run_bind, hldc0]; dsimp only
            rw [C.run_bind, hlmst0']; dsimp only
            simp only [hdimF, hprecF, Bool.false_eq_true, ↓reduceIte, hnc]
            rw [C.run_bind, hstdc1]; dsimp only
            rw [C.run_bind]
            rw [show (forIn (List.range dcs0[0]!.numComponents.toInt.toNat) (none, ()) fun ci __s => do
              let dcCur ← (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0).load
              let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
              let comp ← cp.load
              if (decide (comp.hSampFactor ≤ 0) || decide (comp.hSampFactor > MAX_SAMP_FACTOR) ||
                  decide (comp.vSampFactor ≤ 0) || decide (comp.vSampFactor > MAX_SAMP_FACTOR)) = true then
                let _ ← errexit dcCur.err JERR_BAD_SAMPLING
                pure (ForInStep.done (some (JpegRes.errExit JERR_BAD_SAMPLING), ()))
              else
                (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0).store
                  { dcCur with
                    maxHSampFactor := max dcCur.maxHSampFactor comp.hSampFactor
                    maxVSampFactor := max dcCur.maxVSampFactor comp.vSampFactor }
                pure (ForInStep.yield (none, ()))) =
              forIn (List.range nComps) (none, ()) step1 from rfl, hrunL1]; dsimp only
            rw [C.run_bind, hldc1]; dsimp only
            rw [C.run_bind, hstdc2]; dsimp only
            rw [C.run_bind]
            rw [show (forIn (List.range dcs0[0]!.numComponents.toInt.toNat) PUnit.unit fun ci __s => do
              let dcC ← (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0).load
              let cp ← Ptr.add dcC.compInfo (Int.ofNat ci)
              let comp ← cp.load
              let wib ← jdiv_round_up
                (Int64.ofInt (Int.ofNat dcC.imageWidth.toNat * comp.hSampFactor.toInt))
                (Int64.ofInt (dcC.maxHSampFactor.toInt * data_unit.toInt))
              let hib ← jdiv_round_up
                (Int64.ofInt (Int.ofNat dcC.imageHeight.toNat * comp.vSampFactor.toInt))
                (Int64.ofInt (dcC.maxVSampFactor.toInt * data_unit.toInt))
              let mstC ← Ptr.load dcC.master
              Ptr.store dcC.master
                { mstC with
                  firstMcuCol := mstC.firstMcuCol.set! ci 0
                  lastMcuCol := mstC.lastMcuCol.set! ci (UInt32.ofNat wib.toInt.toNat - 1) }
              let dw ← jdiv_round_up
                (Int64.ofInt (Int.ofNat dcC.imageWidth.toNat * comp.hSampFactor.toInt))
                (Int64.ofInt dcC.maxHSampFactor.toInt)
              let dh ← jdiv_round_up
                (Int64.ofInt (Int.ofNat dcC.imageHeight.toNat * comp.vSampFactor.toInt))
                (Int64.ofInt dcC.maxVSampFactor.toInt)
              cp.store
                { comp with
                  widthInBlocks := UInt32.ofNat wib.toInt.toNat
                  heightInBlocks := UInt32.ofNat hib.toInt.toNat
                  dctHScaledSize := data_unit
                  dctVScaledSize := data_unit
                  downsampledWidth := UInt32.ofNat dw.toInt.toNat
                  downsampledHeight := UInt32.ofNat dh.toInt.toNat
                  componentNeeded := TRUE
                  quantTable := .null }
              pure (ForInStep.yield PUnit.unit)) =
              forIn (List.range nComps) PUnit.unit step2 from rfl, hrunL2]; dsimp only
            rw [C.run_bind, hldcL2]; dsimp only
            rw [C.run_bind, htotRun]; dsimp only
            rw [C.run_bind, hstdc3]; dsimp only
            rw [C.run_bind, hlicL3']; dsimp only
            rw [C.run_bind, hstic3']; rfl
          · intro e0 e' he0 hsz0 he'
            have hher4 : h4.errMgrs = h.errMgrs := by
              have : h4.errMgrs = hL2.errMgrs := by dsimp only [h4, h3]; rcases ctx.ric with ⟨_⟩; rfl
              exact this.trans herL2
            simp only [C.Space.get] at he0 he'; rw [hher4] at he'
            rw [Option.some.inj (he'.symm.trans he0)]; exact ⟨hsz0, rfl⟩
          · intro m0 m' hm0 _ hm' _
            have hhm4 : h4.markers = h.markers := by
              have : h4.markers = hL2.markers := by dsimp only [h4, h3]; rcases ctx.ric with ⟨_⟩; rfl
              exact this.trans hmL2
            simp only [C.Space.get] at hm0 hm'; rw [hhm4] at hm'; exact Option.some.inj (hm'.symm.trans hm0)
          · intro s0 s' hs0 _ hs' _
            have hhs4 : h4.srcs = h.srcs := by
              have : h4.srcs = hL2.srcs := by dsimp only [h4, h3]; rcases ctx.ric with ⟨_⟩; rfl
              exact this.trans hsrL2
            simp only [C.Space.get] at hs0 hs'; rw [hhs4] at hs'; exact Option.some.inj (hs'.symm.trans hs0)
          · intro d0 d' hd0 _ hd' _
            rw [Option.some.inj (hd0.symm.trans hgdc0)]
            have hgd4 : C.Space.get h4 (C.DecompRef.decomp ctx.bdc) = some (dcsL2.set! 0 dc3) := by
              dsimp only [h4, h3]; rcases ctx.ric with ⟨_⟩; simp [C.Space.get, C.Space.put]
            rw [Option.some.inj (hd'.symm.trans hgd4), set0_bang_m dcsL2 hszdcL2 dc3]
            change dcsL2[0]!.inputScanNumber = dcs0[0]!.inputScanNumber ∧
              dcsL2[0]!.unreadMarker = dcs0[0]!.unreadMarker
            rw [hdcL2_eq]
            exact hdisnL1 dcs1 hgdc1' hszdc1'
          · intro i0 i' hi0 _ hi' _
            have hhicL2 : C.Space.get hL2 ctx.ric = some i0 := by
              rcases hr : ctx.ric with ⟨bi⟩
              simp only [C.Space.get, hr] at hi0 ⊢; rw [hicL2]; exact hi0
            have hgicL3Eq : icsL3 = i0 := by
              have hh3 : C.Space.get h3 ctx.ric = some i0 := by
                dsimp only [h3]; rcases hr : ctx.ric with ⟨bi⟩
                simp only [C.Space.get, C.Space.put, hr] at hhicL2 ⊢; exact hhicL2
              exact Option.some.inj (hgicL3.symm.trans hh3)
            have hgi4 : C.Space.get h4 ctx.ric = some (icsL3.set! 0 ic3) := by
              dsimp only [h4]; rcases ctx.ric with ⟨_⟩
              simp [C.Space.get, C.Space.put, C.upd_same]
            rw [Option.some.inj (hi'.symm.trans hgi4), set0_bang_m icsL3 hszicL3 ic3]
            dsimp only [ic3]; rw [hgicL3Eq]
            exact ⟨rfl, rfl, rfl, rfl⟩
          · intro mrks' hm' _
            have hhm4 : h4.markers = h.markers := by
              have : h4.markers = hL2.markers := by dsimp only [h4, h3]; rcases ctx.ric with ⟨_⟩; rfl
              exact this.trans hmL2
            have hm'0 : C.Space.get h ctx.rmrk = some mrks' := by
              simp only [C.Space.get] at hm' ⊢; rw [hhm4] at hm'; exact hm'
            rw [Option.some.inj (hm'0.symm.trans hgmrk0)]; exact hsof0
          · intro d0 d' hd0 _ hd' _
            rw [Option.some.inj (hd0.symm.trans hgdc0)]
            have hgd4 : C.Space.get h4 (C.DecompRef.decomp ctx.bdc) = some (dcsL2.set! 0 dc3) := by
              dsimp only [h4, h3]; rcases ctx.ric with ⟨_⟩; simp [C.Space.get, C.Space.put]
            rw [Option.some.inj (hd'.symm.trans hgd4), set0_bang_m dcsL2 hszdcL2 dc3]
            change dcsL2[0]!.entropyStartPass = dcs0[0]!.entropyStartPass ∧
              dcsL2[0]!.coefStartInputPass = dcs0[0]!.coefStartInputPass ∧
              dcsL2[0]!.coefConsumeData = dcs0[0]!.coefConsumeData
            rw [hdcL2_eq]
            have hdcS1 := hdcSame1
            refine ⟨by have := congrArg C.JpegDecompressStruct.entropyStartPass hdcS1; simpa using this,
                    by have := congrArg C.JpegDecompressStruct.coefStartInputPass hdcS1; simpa using this,
                    by have := congrArg C.JpegDecompressStruct.coefConsumeData hdcS1; simpa using this⟩
          · intro d0 d' hd0 _ hd' hszd' hscan he1 he2 he3
            rw [Option.some.inj (hd0.symm.trans hgdc0)] at hscan
            have hgd4 : C.Space.get h4 (C.DecompRef.decomp ctx.bdc) = some (dcsL2.set! 0 dc3) := by
              dsimp only [h4, h3]; rcases ctx.ric with ⟨_⟩; simp [C.Space.get, C.Space.put]
            have hd'Eq := Option.some.inj (hd'.symm.trans hgd4)
            rw [hd'Eq, set0_bang_m dcsL2 hszdcL2 dc3] at he1 he2 he3 ⊢
            have hcomp4 : C.Space.get h4 rcp = some csL2 := by
              dsimp only [h4, h3]; rcases hr : rcp with ⟨bc⟩; rcases ctx.ric with ⟨_⟩
              simp only [C.Space.get, C.Space.put, hr] at hgcsL2 ⊢; exact hgcsL2
            have hm4 : C.Space.get h4 ctx.rmrk = some mrks0 := by
              have : h4.markers = h.markers := by
                have : h4.markers = hL2.markers := by dsimp only [h4, h3]; rcases ctx.ric with ⟨_⟩; rfl
                exact this.trans hmL2
              simp only [C.Space.get] at hgmrk0 ⊢; rw [this]; exact hgmrk0
            have hdcS1 := hdcSame1
            have hk_cis : dcsL2[0]!.compsInScan = dcs0[0]!.compsInScan := by
              rw [hdcL2_eq]; exact (by have := congrArg C.JpegDecompressStruct.compsInScan hdcS1; simpa using this)
            have hk_cci : dcsL2[0]!.curCompInfo = dcs0[0]!.curCompInfo := by
              rw [hdcL2_eq]; exact (by have := congrArg C.JpegDecompressStruct.curCompInfo hdcS1; simpa using this)
            have hk_iw : dcsL2[0]!.imageWidth = dcs0[0]!.imageWidth := by
              rw [hdcL2_eq]; exact (by have := congrArg C.JpegDecompressStruct.imageWidth hdcS1; simpa using this)
            have hk_ih : dcsL2[0]!.imageHeight = dcs0[0]!.imageHeight := by
              rw [hdcL2_eq]; exact (by have := congrArg C.JpegDecompressStruct.imageHeight hdcS1; simpa using this)
            have hk_nc : dcsL2[0]!.numComponents = dcs0[0]!.numComponents := by
              rw [hdcL2_eq]; exact (by have := congrArg C.JpegDecompressStruct.numComponents hdcS1; simpa using this)
            have hk_mrk : dcsL2[0]!.marker = dcs0[0]!.marker := by
              rw [hdcL2_eq]; exact (by have := congrArg C.JpegDecompressStruct.marker hdcS1; simpa using this)
            have hk_cp : dcsL2[0]!.compInfo = dcs0[0]!.compInfo := by
              rw [hdcL2_eq]; exact (by have := congrArg C.JpegDecompressStruct.compInfo hdcS1; simpa using this)
            rcases hscan with ⟨hsc1, hsc2, hscSz, hscAll⟩
            refine ⟨he1, he2, he3, hk_cis ▸ hsc1, hk_cis ▸ hsc2, hk_cci ▸ hscSz,
              (by change 1 ≤ dcsL2[0]!.maxHSampFactor.toInt; rw [hdcL2_eq]; exact hmHLo),
              (by change dcsL2[0]!.maxHSampFactor.toInt ≤ 4; rw [hdcL2_eq]; exact hmHHi),
              (by change 1 ≤ dcsL2[0]!.maxVSampFactor.toInt; rw [hdcL2_eq]; exact hmVLo),
              (by change dcsL2[0]!.maxVSampFactor.toInt ≤ 4; rw [hdcL2_eq]; exact hmVHi),
              (by rw [hk_iw]; exact himgBounds.2), (by rw [hk_ih]; exact himgBounds.1),
              (by rw [hk_nc]; exact hnc0), (by rw [hk_nc]; exact hncLe10),
              ⟨ctx.rmrk, mrks0, hk_mrk.trans kmrk0, hm4, hszmrk0, hsof0⟩, ?_, ?_⟩
            · refine Or.inr ⟨rcp, csL2, hk_cp.trans hci0_eq, hcomp4, (by rw [hk_nc, hszCsL2]; exact hncLe0),
                fun j hj => by
                  change j < dcsL2[0]!.numComponents.toInt.toNat at hj
                  rw [hk_nc] at hj
                  exact hcsL2Bnds j hj (by omega)⟩
            · intro i hi
              rw [hk_cis] at hi
              obtain ⟨rcpI, offI, csI, hciI, hgI, hoffI1, hoffI2, hgetI⟩ := hscAll i hi
              have hrcpEq : rcpI = rcp := by
                have hci0' : .ref rcp 0 = (.ref rcpI 0 : C.CompPtr) := hci0_eq.symm.trans hciI
                cases hci0'; rfl
              subst hrcpEq
              have hcsIEq := Option.some.inj (hgI.symm.trans hgcs0)
              have hoffI_cs0 : offI < cs0.size := by rw [← hcsIEq]; exact hoffI2
              have hoffISz : offI < csL2.size := by rw [hszCsL2]; exact hoffI_cs0
              have hciB := hcsL2Bnds offI hoffI1 hoffI_cs0
              exact ⟨rcpI, offI, csL2, csL2[offI]!, hk_cci ▸ hgetI, hcomp4, hoffISz, rfl, hciB⟩
        · obtain ⟨hpL, hsawL, hmL, hsrL, hicL, _, _, _, _, hdisnL, hnwL, _, code, hcode⟩ := hInv1
          refine ⟨.errExit code, hL1, ?_, hpL, hsawL, ?_, ?_, ?_, ?_, ?_, trivial⟩
          · unfold initial_setup
            rw [C.run_bind, hldc0]; dsimp only
            rw [C.run_bind, hlmst0']; dsimp only
            simp only [hdimF, hprecF, Bool.false_eq_true, ↓reduceIte, hnc]
            rw [C.run_bind, hstdc1]; dsimp only
            rw [C.run_bind]
            rw [show (forIn (List.range dcs0[0]!.numComponents.toInt.toNat) (none, ()) fun ci __s => do
              let dcCur ← (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0).load
              let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
              let comp ← cp.load
              if (decide (comp.hSampFactor ≤ 0) || decide (comp.hSampFactor > MAX_SAMP_FACTOR) ||
                  decide (comp.vSampFactor ≤ 0) || decide (comp.vSampFactor > MAX_SAMP_FACTOR)) = true then
                let _ ← errexit dcCur.err JERR_BAD_SAMPLING
                pure (ForInStep.done (some (JpegRes.errExit JERR_BAD_SAMPLING), ()))
              else
                (Ptr.ref (C.DecompRef.decomp ctx.bdc) 0).store
                  { dcCur with
                    maxHSampFactor := max dcCur.maxHSampFactor comp.hSampFactor
                    maxVSampFactor := max dcCur.maxVSampFactor comp.vSampFactor }
                pure (ForInStep.yield (none, ()))) =
              forIn (List.range nComps) (none, ()) step1 from rfl, hrunL1]; dsimp only
            rw [hcode]; rfl
          · intro e0 e' he0 hsz0 he'
            obtain ⟨errs1, hg1, hsz1, _⟩ := parserEnv_get_err hpL
            have he0Eq := Option.some.inj (he0.symm.trans hgerr0)
            have he'Eq := Option.some.inj (he'.symm.trans hg1)
            rw [he0Eq, he'Eq]
            exact ⟨hsz1, hnwL errs1 hg1 hsz1⟩
          · intro m0 m' hm0 _ hm' _
            simp only [C.Space.get] at hm0 hm'; rw [hmL] at hm'; exact Option.some.inj (hm'.symm.trans hm0)
          · intro s0 s' hs0 _ hs' _
            simp only [C.Space.get] at hs0 hs'; rw [hsrL] at hs'; exact Option.some.inj (hs'.symm.trans hs0)
          · intro d0 d' hd0 hszd0 hd' hszd'
            rw [Option.some.inj (hd0.symm.trans hgdc0)]
            exact hdisnL d' hd' hszd'
          · intro i0 i' hi0 _ hi' _
            simp only [C.Space.get] at hi0 hi'; rw [hicL] at hi'
            rw [Option.some.inj (hi'.symm.trans hi0)]; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## `per_scan_setup` -/

private theorem multiScanReady_frame {h h' : C.Heap} {dc : C.JpegDecompressStruct}
    (hm : MultiScanReady h dc)
    (hmrk : h'.markers = h.markers) (hcp : h'.comps = h.comps) :
    MultiScanReady h' dc := by
  rcases hm with ⟨e1, e2, e3, c1, c2, csz, m1, m2, m3, m4, w1, h1, nc1, nc2, ⟨rmrk, mrks, km, hgm, hszm, hsof⟩, hc, hcur⟩
  refine ⟨e1, e2, e3, c1, c2, csz, m1, m2, m3, m4, w1, h1, nc1, nc2,
    ⟨rmrk, mrks, km, (by simp only [C.Space.get] at hgm ⊢; rcases rmrk with ⟨_⟩; rw [hmrk]; exact hgm), hszm, hsof⟩, ?_, ?_⟩
  · rcases hc with h0 | ⟨rcp, cs, kc, hgc, hszc, hf⟩
    · exact Or.inl h0
    · exact Or.inr ⟨rcp, cs, kc, (by simp only [C.Space.get] at hgc ⊢; cases rcp; rw [hcp]; exact hgc), hszc, hf⟩
  · intro i hi
    obtain ⟨rcp, off, cs, ci, h1i, h2i, h3i, h4i, h5i⟩ := hcur i hi
    exact ⟨rcp, off, cs, ci, h1i, (by simp only [C.Space.get] at h2i ⊢; cases rcp; rw [hcp]; exact h2i), h3i, h4i, h5i⟩

private theorem scanCompsInRange_frame {h h' : C.Heap} {dc : C.JpegDecompressStruct}
    (hsc : ScanCompsInRange h dc) (hcp : h'.comps = h.comps) :
    ScanCompsInRange h' dc := by
  rcases hsc with ⟨h1, h2, hsz, hall⟩
  refine ⟨h1, h2, hsz, fun i hi => ?_⟩
  obtain ⟨rcp, offI, cs, hci, hg, hoff1, hoff2, hget⟩ := hall i hi
  exact ⟨rcp, offI, cs, hci, (by cases rcp; simp only [C.Space.get] at hg ⊢; rw [hcp]; exact hg), hoff1, hoff2, hget⟩

theorem per_scan_setup_ok {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h)
    (hm : ∀ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size → MultiScanReady h dcs[0]!) :
    ∃ res h',
      C.run (per_scan_setup (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      CompSawZero ctx h' ∧
      (∀ errs0 errs', C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs0[0]!.numWarnings) ∧
      (∀ mrks0 mrks', C.Space.get h ctx.rmrk = some mrks0 → 0 < mrks0.size →
        C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size → mrks' = mrks0) ∧
      (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size → srcs' = srcs0) ∧
      (∀ masters0 masters', C.Space.get h ctx.rmas = some masters0 → 0 < masters0.size →
        C.Space.get h' ctx.rmas = some masters' → 0 < masters'.size → masters' = masters0) ∧
      (∀ ics0 ics', C.Space.get h ctx.ric = some ics0 → 0 < ics0.size →
        C.Space.get h' ctx.ric = some ics' → 0 < ics'.size → ics' = ics0) ∧
      (∀ dcs0 dcs',
        C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
        C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
        MultiScanReady h' dcs'[0]! ∧
        dcs'[0]!.inputScanNumber = dcs0[0]!.inputScanNumber ∧
        dcs'[0]!.unreadMarker = dcs0[0]!.unreadMarker) := by
  obtain ⟨dcs0, hgdc0, hszdc0, kerr0, _, kmas0, _, _, _⟩ := parserEnv_get_dc hp
  obtain ⟨masters0, hgmas0, hszmas0⟩ := parserEnv_get_mas hp
  obtain ⟨errs0, hgerr0, hszerr0, _⟩ := parserEnv_get_err hp
  have hm0 := hm dcs0 hgdc0 hszdc0
  rcases hm0 with ⟨_, _, _, hcis0_lo, hcis0_hi, hccSz0, hmHLo0, hmHHi0, hmVLo0, hmVHi0,
    hiw0, hih0, _, _, _, _, hcur0⟩
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlmst0 := ptr_load_ok (r := ctx.rmas) (off := 0) hgmas0 hszmas0
  have hlmst0' : C.run (Ptr.load dcs0[0]!.master) h = .ok (masters0[0]!, h) := by rw [kmas0]; exact hlmst0
  let data_unit : Int32 := if (masters0[0]!.lossless != 0) = true then 1 else DCTSIZE
  have hduRange : data_unit = 1 ∨ data_unit = 8 := by
    dsimp only [data_unit]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hduPos : 0 < data_unit.toInt ∧ data_unit.toInt ≤ DCTSIZE.toInt := by
    rcases hduRange with hdu | hdu <;> rw [hdu] <;> decide
  by_cases hcis1 : (dcs0[0]!.compsInScan == 1) = true
  · have hcis1Nat : 0 < dcs0[0]!.compsInScan.toInt.toNat := by
      have h1' : dcs0[0]!.compsInScan = 1 := beq_iff_eq.mp hcis1
      rw [h1']; decide
    obtain ⟨rcp0, off0, cs0, ci0, hcci0, hgcs0, hoff0, hci0Eq, hci0B⟩ := hcur0 0 hcis1Nat
    have hlcomp0 := ptr_load_ok (r := rcp0) (off := off0) hgcs0 hoff0
    have hlcomp0' : C.run (Ptr.load dcs0[0]!.curCompInfo[0]!) h = .ok (cs0[off0]!, h) := by
      rw [hcci0]; exact hlcomp0
    have hvPos : ¬ (cs0[off0]!.vSampFactor ≤ 0) := by
      have hv1 : (1 : Int) ≤ cs0[off0]!.vSampFactor.toInt := by rw [← hci0Eq]; exact hci0B.2.2.1
      intro hle
      have hle' := Int32.le_iff_toInt_le.mp hle
      change cs0[off0]!.vSampFactor.toInt ≤ 0 at hle'
      omega
    have hroCp0 : C.Space.ro h rcp0 = false := by cases rcp0; rfl
    let lrh :=
      if (Int32.ofInt (Int.ofNat cs0[off0]!.heightInBlocks.toNat % cs0[off0]!.vSampFactor.toInt) == 0) = true then
        cs0[off0]!.vSampFactor
      else Int32.ofInt (Int.ofNat cs0[off0]!.heightInBlocks.toNat % cs0[off0]!.vSampFactor.toInt)
    let comp0' : C.JpegCompInfo := {
      (cs0[off0]!) with
      mcuWidth := 1
      mcuHeight := 1
      mcuBlocks := 1
      mcuSampleWidth := cs0[off0]!.dctHScaledSize
      lastColWidth := 1
      lastRowHeight := lrh
    }
    have hstcomp0 := ptr_store_ok (r := rcp0) (off := off0) (v := comp0') hgcs0 hroCp0 hoff0
    have hstcomp0' : C.run (Ptr.store dcs0[0]!.curCompInfo[0]! comp0') h =
        .ok ((), C.Space.put h rcp0 (cs0.set! off0 comp0')) := by
      rw [hcci0]; exact hstcomp0
    let h1 := C.Space.put h rcp0 (cs0.set! off0 comp0')
    have hp1 : ParserEnv ctx h1 := parserEnv_put_comp hp hgcs0
    have hsaw1 : CompSawZero ctx h1 := compSawZero_put_comp hsaw
    have hm1 : MultiScanReady h1 dcs0[0]! := multiScanReady_put_comp hgcs0 hoff0 rfl rfl rfl (hm dcs0 hgdc0 hszdc0)
    have hgdc1 : C.Space.get h1 (C.DecompRef.decomp ctx.bdc) = some dcs0 := by
      rcases rcp0 with ⟨_⟩; exact hgdc0
    have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc0
    have hroDc1 : C.Space.ro h1 (C.DecompRef.decomp ctx.bdc) = false := rfl
    let dc1 : C.JpegDecompressStruct := {
      (dcs0[0]!) with
      mcusPerRow := cs0[off0]!.widthInBlocks
      mcuRowsInScan := cs0[off0]!.heightInBlocks
      blocksInMcu := 1
      mcuMembership := dcs0[0]!.mcuMembership.set! 0 0
    }
    have hstdc1 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc1) hgdc1 hroDc1 hszdc0
    let h2 := C.Space.put h1 (C.DecompRef.decomp ctx.bdc) (dcs0.set! 0 dc1)
    have hp2 : ParserEnv ctx h2 := parserEnv_put_dc_keep' hp1 hgdc1 hszdc0
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hsaw2 : CompSawZero ctx h2 := compSawZero_put_dc_keep hsaw1 hgdc1 hszdc0 rfl
    have hm2 : MultiScanReady h2 dc1 := multiScanReady_put_dc_scalar hgdc1 hszdc0
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm1
    refine ⟨.ok (), h2, ?_, hp2, hsaw2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold per_scan_setup
      rw [C.run_bind, hldc0]; dsimp only
      rw [C.run_bind, hlmst0']; dsimp only
      simp only [hcis1, ↓reduceIte, C.run_bind, hlcomp0', hvPos]
      rw [hstcomp0']; dsimp only
      rw [hldc1]; dsimp only
      rw [hstdc1]; rfl
    · intro e0 e' he0 hsz0 he'
      have hhe : h2.errMgrs = h.errMgrs := by dsimp only [h2, h1]; rcases rcp0 with ⟨_⟩; rfl
      simp only [C.Space.get] at he0 he'; rw [hhe] at he'
      rw [Option.some.inj (he'.symm.trans he0)]; exact ⟨hsz0, rfl⟩
    · intro m0 m' hm0 _ hm' _
      have hhm : h2.markers = h.markers := by dsimp only [h2, h1]; rcases rcp0 with ⟨_⟩; rfl
      simp only [C.Space.get] at hm0 hm'; rw [hhm] at hm'; exact Option.some.inj (hm'.symm.trans hm0)
    · intro s0 s' hs0 _ hs' _
      have hhs : h2.srcs = h.srcs := by dsimp only [h2, h1]; rcases rcp0 with ⟨_⟩; rfl
      simp only [C.Space.get] at hs0 hs'; rw [hhs] at hs'; exact Option.some.inj (hs'.symm.trans hs0)
    · intro a0 a' ha0 _ ha' _
      have hha : h2.masters = h.masters := by dsimp only [h2, h1]; rcases rcp0 with ⟨_⟩; rfl
      simp only [C.Space.get] at ha0 ha'; rw [hha] at ha'; exact Option.some.inj (ha'.symm.trans ha0)
    · intro i0 i' hi0 _ hi' _
      have hhi : h2.inputctls = h.inputctls := by dsimp only [h2, h1]; rcases rcp0 with ⟨_⟩; rfl
      simp only [C.Space.get] at hi0 hi'; rw [hhi] at hi'; exact Option.some.inj (hi'.symm.trans hi0)
    · intro d0 d' hd0 _ hd' _
      rw [Option.some.inj (hd0.symm.trans hgdc0)]
      have hgd2 : C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some (dcs0.set! 0 dc1) := by
        simp [h2, C.Space.get, C.Space.put]
      rw [Option.some.inj (hd'.symm.trans hgd2), set0_bang_m dcs0 hszdc0 dc1]
      exact ⟨hm2, rfl, rfl⟩
  · have hcis1F : (dcs0[0]!.compsInScan == 1) = false := Bool.eq_false_iff.mpr hcis1
    by_cases hbadCis : (decide (dcs0[0]!.compsInScan ≤ 0) || decide (dcs0[0]!.compsInScan > MAX_COMPS_IN_SCAN)) = true
    · obtain ⟨hE, herr_run, hpE, hsawE, hdE, hmE, hsrE, hmaE, hcpE, _, _, hicE, _, hnwE⟩ :=
        errexit2_full hp hsaw JERR_COMPONENT_COUNT dcs0[0]!.compsInScan MAX_COMPS_IN_SCAN
      refine ⟨.errExit JERR_COMPONENT_COUNT, hE, ?_, hpE, hsawE, hnwE,
        (fun m0 m' hm0 _ hm' _ => by
          simp only [C.Space.get] at hm0 hm'; rw [hmE] at hm'; exact Option.some.inj (hm'.symm.trans hm0)),
        (fun s0 s' hs0 _ hs' _ => by
          simp only [C.Space.get] at hs0 hs'; rw [hsrE] at hs'; exact Option.some.inj (hs'.symm.trans hs0)),
        (fun a0 a' ha0 _ ha' _ => by
          simp only [C.Space.get] at ha0 ha'; rw [hmaE] at ha'; exact Option.some.inj (ha'.symm.trans ha0)),
        (fun i0 i' hi0 _ hi' _ => by
          simp only [C.Space.get] at hi0 hi'; rw [hicE] at hi'; exact Option.some.inj (hi'.symm.trans hi0)),
        (fun d0 d' hd0 hszd0 hd' hszd' => by
          have hd'Eq : d' = d0 := by
            simp only [C.Space.get] at hd0 hd'; rw [hdE] at hd'
            exact Option.some.inj (hd'.symm.trans hd0)
          rw [hd'Eq]; exact ⟨multiScanReady_frame (hm d0 hd0 hszd0) hmE hcpE, rfl, rfl⟩)⟩
      · unfold per_scan_setup
        rw [C.run_bind, hldc0]; dsimp only
        rw [C.run_bind, hlmst0']; dsimp only
        simp only [hcis1F, Bool.false_eq_true, ↓reduceIte, hbadCis, C.run_bind, kerr0, herr_run]; rfl
    · have hbadCisF : (decide (dcs0[0]!.compsInScan ≤ 0) || decide (dcs0[0]!.compsInScan > MAX_COMPS_IN_SCAN)) = false :=
        Bool.eq_false_iff.mpr hbadCis
      have hcisGe2 : 2 ≤ dcs0[0]!.compsInScan.toInt := by
        have h1 : ¬ (dcs0[0]!.compsInScan ≤ 0) := fun x => hbadCis (by simp [x])
        have hne1 : dcs0[0]!.compsInScan ≠ 1 := fun x => hcis1 (beq_iff_eq.mpr x)
        have hm1 : ¬ (dcs0[0]!.compsInScan.toInt ≤ (0 : Int32).toInt) := fun x =>
          h1 (Int32.le_iff_toInt_le.mpr x)
        have h0i : (0 : Int32).toInt = 0 := rfl
        rw [h0i] at hm1
        have hne1' : dcs0[0]!.compsInScan.toInt ≠ 1 := fun hq =>
          hne1 (Int32.toInt_inj.mp (by change dcs0[0]!.compsInScan.toInt = (1 : Int32).toInt; exact hq))
        omega
      let nCis := dcs0[0]!.compsInScan.toInt.toNat
      have hmprA : 0 ≤ (Int64.ofNat dcs0[0]!.imageWidth.toNat).toInt := by
        change 0 ≤ (Int64.ofInt (dcs0[0]!.imageWidth.toNat : Int)).toInt
        rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
      have hmulMH_lo : 0 < dcs0[0]!.maxHSampFactor.toInt * data_unit.toInt := Int.mul_pos (by omega) (by omega)
      have hmulMH_hi : dcs0[0]!.maxHSampFactor.toInt * data_unit.toInt ≤ 4 * 8 :=
        Int.mul_le_mul hmHHi0 hduPos.2 (by omega) (by decide)
      have hmprB : 0 < (Int64.ofInt (dcs0[0]!.maxHSampFactor.toInt * data_unit.toInt)).toInt := by
        rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
      have hmprSum : (Int64.ofNat dcs0[0]!.imageWidth.toNat).toInt +
          (Int64.ofInt (dcs0[0]!.maxHSampFactor.toInt * data_unit.toInt)).toInt < 2 ^ 63 := by
        change (Int64.ofInt (dcs0[0]!.imageWidth.toNat : Int)).toInt + _ < 2 ^ 63
        rw [Int64.toInt_ofInt, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl,
          Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
        omega
      obtain ⟨mpr, hmprRun, _⟩ := jdiv_round_up_functional h _ _ hmprA hmprB hmprSum
      have hmrisA : 0 ≤ (Int64.ofNat dcs0[0]!.imageHeight.toNat).toInt := by
        change 0 ≤ (Int64.ofInt (dcs0[0]!.imageHeight.toNat : Int)).toInt
        rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
      have hmulMV_lo : 0 < dcs0[0]!.maxVSampFactor.toInt * data_unit.toInt := Int.mul_pos (by omega) (by omega)
      have hmulMV_hi : dcs0[0]!.maxVSampFactor.toInt * data_unit.toInt ≤ 4 * 8 :=
        Int.mul_le_mul hmVHi0 hduPos.2 (by omega) (by decide)
      have hmrisB : 0 < (Int64.ofInt (dcs0[0]!.maxVSampFactor.toInt * data_unit.toInt)).toInt := by
        rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, Int.bmod_eq_of_le] <;> omega
      have hmrisSum : (Int64.ofNat dcs0[0]!.imageHeight.toNat).toInt +
          (Int64.ofInt (dcs0[0]!.maxVSampFactor.toInt * data_unit.toInt)).toInt < 2 ^ 63 := by
        change (Int64.ofInt (dcs0[0]!.imageHeight.toNat : Int)).toInt + _ < 2 ^ 63
        rw [Int64.toInt_ofInt, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl,
          Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
        omega
      obtain ⟨mris, hmrisRun, _⟩ := jdiv_round_up_functional h _ _ hmrisA hmrisB hmrisSum
      have hroDc0 : C.Space.ro h (C.DecompRef.decomp ctx.bdc) = false := rfl
      let dc1 : C.JpegDecompressStruct := {
        (dcs0[0]!) with
        mcusPerRow := UInt32.ofNat mpr.toInt.toNat
        mcuRowsInScan := UInt32.ofNat mris.toInt.toNat
        blocksInMcu := 0
      }
      have hstdc1 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc1) hgdc0 hroDc0 hszdc0
      let h1 := C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs0.set! 0 dc1)
      have hp1 : ParserEnv ctx h1 := parserEnv_put_dc_keep' hp hgdc0 hszdc0
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hsaw1 : CompSawZero ctx h1 := compSawZero_put_dc_keep hsaw hgdc0 hszdc0 rfl
      have hm1 : MultiScanReady h1 dc1 := multiScanReady_put_dc_scalar hgdc0 hszdc0
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (hm dcs0 hgdc0 hszdc0)
      have hgdc1 : C.Space.get h1 (C.DecompRef.decomp ctx.bdc) = some (dcs0.set! 0 dc1) := by
        simp [h1, C.Space.get, C.Space.put]
      have hszdc1 : 0 < (dcs0.set! 0 dc1).size := by simpa using hszdc0
      have hdc1_bang : (dcs0.set! 0 dc1)[0]! = dc1 := set0_bang_m dcs0 hszdc0 dc1
      let InvScan (idx : Nat) (st : Option (JpegRes Unit) × Unit) (hCur : C.Heap) : Prop :=
        ParserEnv ctx hCur ∧ CompSawZero ctx hCur ∧
        hCur.markers = h.markers ∧ hCur.srcs = h.srcs ∧ hCur.masters = h.masters ∧
        hCur.inputctls = h.inputctls ∧
        (∀ errs1, C.Space.get hCur ctx.rerr = some errs1 → 0 < errs1.size →
          errs1[0]!.numWarnings = errs0[0]!.numWarnings) ∧
        (∀ dcsC, C.Space.get hCur (C.DecompRef.decomp ctx.bdc) = some dcsC → 0 < dcsC.size →
          MultiScanReady hCur dcsC[0]! ∧
          dcsC[0]!.inputScanNumber = dcs0[0]!.inputScanNumber ∧
          dcsC[0]!.unreadMarker = dcs0[0]!.unreadMarker) ∧
        match st.1 with
        | some r => idx = nCis ∧ ∃ code, r = .errExit code
        | none =>
          hCur.errMgrs = h.errMgrs ∧
          ∃ dcsC, C.Space.get hCur (C.DecompRef.decomp ctx.bdc) = some dcsC ∧ 0 < dcsC.size ∧
            dcsC[0]!.err = dcs0[0]!.err ∧
            dcsC[0]!.compsInScan = dcs0[0]!.compsInScan ∧
            dcsC[0]!.curCompInfo = dcs0[0]!.curCompInfo ∧
            0 ≤ dcsC[0]!.blocksInMcu.toInt ∧ dcsC[0]!.blocksInMcu.toInt ≤ 10
      have hInvScan_init : InvScan 0 (none, ()) h1 := by
        refine ⟨hp1, hsaw1, rfl, rfl, rfl, rfl, (fun errs1 hg1 _ => ?_), ?_, rfl,
          dcs0.set! 0 dc1, hgdc1, hszdc1, (by rw [hdc1_bang]), (by rw [hdc1_bang]),
          (by rw [hdc1_bang]), (by rw [hdc1_bang]; show (0 : Int) ≤ (0 : Int32).toInt; decide),
          (by rw [hdc1_bang]; show (0 : Int32).toInt ≤ 10; decide)⟩
        · rw [Option.some.inj (hg1.symm.trans hgerr0)]
        · intro dcsC hgdC _
          rw [Option.some.inj (hgdC.symm.trans hgdc1), hdc1_bang]
          exact ⟨hm1, rfl, rfl⟩
      let stepScan : Nat → Option (JpegRes Unit) × Unit → M (ForInStep (Option (JpegRes Unit) × Unit)) :=
        fun ci _ => do
          let dcC ← Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
          let comp ← Ptr.load dcC.curCompInfo[ci]!
          let __do_jp : Unit → M (ForInStep (Option (JpegRes Unit) × Unit)) := fun _ => do
            let mb ← i32Mul comp.hSampFactor comp.vSampFactor
            let msw ← i32Mul comp.hSampFactor comp.dctHScaledSize
            Ptr.store dcC.curCompInfo[ci]!
              { comp with
                mcuWidth := comp.hSampFactor
                mcuHeight := comp.vSampFactor
                mcuBlocks := mb
                mcuSampleWidth := msw
                lastColWidth :=
                  if (Int32.ofInt (Int.ofNat comp.widthInBlocks.toNat % comp.hSampFactor.toInt) == 0) = true then
                    comp.hSampFactor
                  else Int32.ofInt (Int.ofNat comp.widthInBlocks.toNat % comp.hSampFactor.toInt)
                lastRowHeight :=
                  if (Int32.ofInt (Int.ofNat comp.heightInBlocks.toNat % comp.vSampFactor.toInt) == 0) = true then
                    comp.vSampFactor
                  else Int32.ofInt (Int.ofNat comp.heightInBlocks.toNat % comp.vSampFactor.toInt) }
            let dcB ← Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
            let bim ← i32Add dcB.blocksInMcu mb
            if bim > D_MAX_BLOCKS_IN_MCU then
              let _ ← errexit dcB.err JERR_BAD_MCU_SIZE
              pure (ForInStep.done (some (.errExit JERR_BAD_MCU_SIZE), ()))
            else
              let __s ← forIn (List.range mb.toInt.toNat) (dcB.mcuMembership, dcB.blocksInMcu) fun _ __s =>
                pure (ForInStep.yield (__s.fst.set! __s.snd.toInt.toNat (Int32.ofNat ci), __s.snd + 1))
              Ptr.store (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
                { dcB with blocksInMcu := __s.snd, mcuMembership := __s.fst }
              pure (ForInStep.yield (none, ()))
          if (decide (comp.hSampFactor ≤ 0) || decide (comp.vSampFactor ≤ 0)) = true then do
            let __r ← ub "division by zero in per_scan_setup"
            __do_jp __r
          else
            __do_jp ()
      have hloopScan : ∃ stS hLS,
          C.run (forIn (List.range nCis) (none, ()) stepScan) h1 = .ok (stS, hLS) ∧ InvScan nCis stS hLS := by
        refine forIn_range_inv InvScan stepScan nCis ?_ hInvScan_init
        intro idx hlt ⟨o, u⟩ hCur hinv
        rcases o with _ | r
        · obtain ⟨hpC, hsawC, hmC, hsrC, hmaC, hicC, hnwC, hmultC, herC,
            dcsC, hgdcC, hszdcC, herrC, hcisC, hcciC, hbimLo, hbimHi⟩ := hinv
          have hldcC := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcC hszdcC
          have hmCur := (hmultC dcsC hgdcC hszdcC).1
          have hcurC := hmCur.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          obtain ⟨rcpI, offI, csI, ciI, hcciI, hgcsI, hoffI, hciIEq, hciIB⟩ := hcurC idx (by rw [hcisC]; exact hlt)
          have hlcompC := ptr_load_ok (r := rcpI) (off := offI) hgcsI hoffI
          have hlcompC' : C.run (Ptr.load dcsC[0]!.curCompInfo[idx]!) hCur = .ok (csI[offI]!, hCur) := by
            rw [hcciI]; exact hlcompC
          have hhsPos : ¬ (csI[offI]!.hSampFactor ≤ 0) := by
            have h1' : 1 ≤ csI[offI]!.hSampFactor.toInt := hciIEq ▸ hciIB.1
            intro hle; have := Int32.le_iff_toInt_le.mp hle
            change csI[offI]!.hSampFactor.toInt ≤ 0 at this; omega
          have hvsPos : ¬ (csI[offI]!.vSampFactor ≤ 0) := by
            have h1' : 1 ≤ csI[offI]!.vSampFactor.toInt := hciIEq ▸ hciIB.2.2.1
            intro hle; have := Int32.le_iff_toInt_le.mp hle
            change csI[offI]!.vSampFactor.toInt ≤ 0 at this; omega
          have hhsB : 1 ≤ csI[offI]!.hSampFactor.toInt ∧ csI[offI]!.hSampFactor.toInt ≤ 4 := by
            rw [← hciIEq]; exact ⟨hciIB.1, hciIB.2.1⟩
          have hvsB : 1 ≤ csI[offI]!.vSampFactor.toInt ∧ csI[offI]!.vSampFactor.toInt ≤ 4 := by
            rw [← hciIEq]; exact ⟨hciIB.2.2.1, hciIB.2.2.2.1⟩
          have hdctB : 0 ≤ csI[offI]!.dctHScaledSize.toInt ∧ csI[offI]!.dctHScaledSize.toInt ≤ DCTSIZE.toInt := by
            rw [← hciIEq]; exact hciIB.2.2.2.2
          have hmpmLo : -(2 ^ 31 : Int) ≤ csI[offI]!.hSampFactor.toInt * csI[offI]!.vSampFactor.toInt := by
            have := Int.mul_nonneg (by omega : 0 ≤ csI[offI]!.hSampFactor.toInt) (by omega : 0 ≤ csI[offI]!.vSampFactor.toInt)
            omega
          have hmpmHi : csI[offI]!.hSampFactor.toInt * csI[offI]!.vSampFactor.toInt ≤ 4 * 4 :=
            Int.mul_le_mul hhsB.2 hvsB.2 (by omega) (by decide)
          have hmbEq : C.run (i32Mul csI[offI]!.hSampFactor csI[offI]!.vSampFactor) hCur =
              .ok (Int32.ofInt (csI[offI]!.hSampFactor.toInt * csI[offI]!.vSampFactor.toInt), hCur) := by
            simp only [C.run, i32Mul_eq _ _ hmpmLo (by omega)]; rfl
          let mb := Int32.ofInt (csI[offI]!.hSampFactor.toInt * csI[offI]!.vSampFactor.toInt)
          have hmbVal : mb.toInt = csI[offI]!.hSampFactor.toInt * csI[offI]!.vSampFactor.toInt := by
            dsimp only [mb]; rw [Int32.toInt_ofInt, show Int32.size = 2 ^ 32 from rfl, Int.bmod_eq_of_le] <;> omega
          have hmbBounds : 1 ≤ mb.toInt ∧ mb.toInt ≤ 16 := by
            have hp := Int.mul_pos (by omega : 0 < csI[offI]!.hSampFactor.toInt) (by omega : 0 < csI[offI]!.vSampFactor.toInt)
            omega
          have hmswLo : -(2 ^ 31 : Int) ≤ csI[offI]!.hSampFactor.toInt * csI[offI]!.dctHScaledSize.toInt := by
            have := Int.mul_nonneg (by omega : 0 ≤ csI[offI]!.hSampFactor.toInt) (hdctB.1)
            omega
          have hmswHi : csI[offI]!.hSampFactor.toInt * csI[offI]!.dctHScaledSize.toInt ≤ 4 * 8 :=
            Int.mul_le_mul hhsB.2 hdctB.2 (hdctB.1) (by decide)
          have hmswEq : C.run (i32Mul csI[offI]!.hSampFactor csI[offI]!.dctHScaledSize) hCur =
              .ok (Int32.ofInt (csI[offI]!.hSampFactor.toInt * csI[offI]!.dctHScaledSize.toInt), hCur) := by
            simp only [C.run, i32Mul_eq _ _ hmswLo (by omega)]; rfl
          let msw := Int32.ofInt (csI[offI]!.hSampFactor.toInt * csI[offI]!.dctHScaledSize.toInt)
          have hroCp : C.Space.ro hCur rcpI = false := by cases rcpI; rfl
          let compN : C.JpegCompInfo := {
            (csI[offI]!) with
            mcuWidth := csI[offI]!.hSampFactor
            mcuHeight := csI[offI]!.vSampFactor
            mcuBlocks := mb
            mcuSampleWidth := msw
            lastColWidth :=
              if (Int32.ofInt (Int.ofNat csI[offI]!.widthInBlocks.toNat % csI[offI]!.hSampFactor.toInt) == 0) = true then
                csI[offI]!.hSampFactor
              else Int32.ofInt (Int.ofNat csI[offI]!.widthInBlocks.toNat % csI[offI]!.hSampFactor.toInt)
            lastRowHeight :=
              if (Int32.ofInt (Int.ofNat csI[offI]!.heightInBlocks.toNat % csI[offI]!.vSampFactor.toInt) == 0) = true then
                csI[offI]!.vSampFactor
              else Int32.ofInt (Int.ofNat csI[offI]!.heightInBlocks.toNat % csI[offI]!.vSampFactor.toInt)
          }
          have hstcompC := ptr_store_ok (r := rcpI) (off := offI) (v := compN) hgcsI hroCp hoffI
          have hstcompC' : C.run (Ptr.store dcsC[0]!.curCompInfo[idx]! compN) hCur =
              .ok ((), C.Space.put hCur rcpI (csI.set! offI compN)) := by
            rw [hcciI]; exact hstcompC
          let hM := C.Space.put hCur rcpI (csI.set! offI compN)
          have hpM : ParserEnv ctx hM := parserEnv_put_comp hpC hgcsI
          have hsawM : CompSawZero ctx hM := compSawZero_put_comp hsawC
          have hgdcM : C.Space.get hM (C.DecompRef.decomp ctx.bdc) = some dcsC := by
            rcases rcpI with ⟨_⟩; exact hgdcC
          have hldcM := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcM hszdcC
          have hmultM : MultiScanReady hM dcsC[0]! :=
            multiScanReady_put_comp hgcsI hoffI rfl rfl rfl hmCur
          have hbimAddEq : C.run (i32Add dcsC[0]!.blocksInMcu mb) hM =
              .ok (Int32.ofInt (dcsC[0]!.blocksInMcu.toInt + mb.toInt), hM) := by
            have hlo : -(2 ^ 31 : Int) ≤ dcsC[0]!.blocksInMcu.toInt + mb.toInt := by omega
            have hhi : dcsC[0]!.blocksInMcu.toInt + mb.toInt < 2 ^ 31 := by omega
            simp only [C.run, i32Add, checkI32, hlo, hhi, and_self, ↓reduceIte]; rfl
          let bim := Int32.ofInt (dcsC[0]!.blocksInMcu.toInt + mb.toInt)
          have hbimVal : bim.toInt = dcsC[0]!.blocksInMcu.toInt + mb.toInt := by
            dsimp only [bim]; rw [Int32.toInt_ofInt, show Int32.size = 2 ^ 32 from rfl, Int.bmod_eq_of_le] <;> omega
          have hmM : hM.markers = h.markers := by
            have : hM.markers = hCur.markers := by dsimp only [hM]; rcases rcpI with ⟨_⟩; rfl
            exact this.trans hmC
          have hsrM : hM.srcs = h.srcs := by
            have : hM.srcs = hCur.srcs := by dsimp only [hM]; rcases rcpI with ⟨_⟩; rfl
            exact this.trans hsrC
          have hmaM : hM.masters = h.masters := by
            have : hM.masters = hCur.masters := by dsimp only [hM]; rcases rcpI with ⟨_⟩; rfl
            exact this.trans hmaC
          have hicM : hM.inputctls = h.inputctls := by
            have : hM.inputctls = hCur.inputctls := by dsimp only [hM]; rcases rcpI with ⟨_⟩; rfl
            exact this.trans hicC
          have herM : hM.errMgrs = h.errMgrs := by
            have : hM.errMgrs = hCur.errMgrs := by dsimp only [hM]; rcases rcpI with ⟨_⟩; rfl
            exact this.trans herC
          have hnwM : ∀ errs1, C.Space.get hM ctx.rerr = some errs1 → 0 < errs1.size →
              errs1[0]!.numWarnings = errs0[0]!.numWarnings := by
            intro errs1 hg1 hsz1
            have hg1' : C.Space.get hCur ctx.rerr = some errs1 := by
              dsimp only [hM] at hg1; rcases rcpI with ⟨_⟩; rcases hre : ctx.rerr with ⟨_⟩
              simp only [C.Space.get, C.Space.put, hre] at hg1 ⊢; exact hg1
            exact hnwC errs1 hg1' hsz1
          have hdivF : (decide (csI[offI]!.hSampFactor ≤ 0) || decide (csI[offI]!.vSampFactor ≤ 0)) = false := by
            simp [hhsPos, hvsPos]
          by_cases hbig : bim > D_MAX_BLOCKS_IN_MCU
          · have hbig' : Int32.ofInt (dcsC[0]!.blocksInMcu.toInt + mb.toInt) > D_MAX_BLOCKS_IN_MCU := hbig
            obtain ⟨hE, herr_run, hpE, hsawE, hdE, hmE, hsrE, hmaE, hcpE, _, _, hicE, _, hnwE⟩ :=
              errexit_full hpM hsawM JERR_BAD_MCU_SIZE
            refine ⟨.done (some (.errExit JERR_BAD_MCU_SIZE), ()), hE, ?_,
              hpE, hsawE, hmE.trans hmM, hsrE.trans hsrM, hmaE.trans hmaM, hicE.trans hicM, ?_, ?_, rfl, JERR_BAD_MCU_SIZE, rfl⟩
            · dsimp only [stepScan]
              rw [C.run_bind, hldcC]; dsimp only
              rw [C.run_bind, hlcompC']; dsimp only
              simp only [hdivF, Bool.false_eq_true, ↓reduceIte]
              rw [C.run_bind, hmbEq]; dsimp only
              rw [C.run_bind, hmswEq]; dsimp only
              rw [C.run_bind, hstcompC']; dsimp only
              rw [C.run_bind, hldcM]; dsimp only
              rw [C.run_bind, hbimAddEq]; dsimp only
              simp only [hbig', ↓reduceIte, C.run_bind, herrC, kerr0, herr_run]; rfl
            · intro errs1 hg1 hsz1
              obtain ⟨errsM, hgM, hszM, _⟩ := parserEnv_get_err hpM
              obtain ⟨_, heq1⟩ := hnwE errsM errs1 hgM hszM hg1
              rw [heq1]; exact hnwM errsM hgM hszM
            · intro dcsE hgdE _
              simp only [C.Space.get] at hgdE hgdcM; rw [hdE] at hgdE
              rw [Option.some.inj (hgdE.symm.trans hgdcM)]
              exact ⟨multiScanReady_frame hmultM hmE hcpE, (hmultC dcsC hgdcC hszdcC).2.1,
                (hmultC dcsC hgdcC hszdcC).2.2⟩
          · have hbimLe10 : bim.toInt ≤ 10 := by
              have h10 : D_MAX_BLOCKS_IN_MCU.toInt = 10 := by decide
              have := mt Int32.lt_iff_toInt_lt.mpr hbig
              omega
            have hbigF : ¬ Int32.ofInt (dcsC[0]!.blocksInMcu.toInt + mb.toInt) > D_MAX_BLOCKS_IN_MCU := hbig
            have hsumLe10 : dcsC[0]!.blocksInMcu.toInt + mb.toInt ≤ 10 := by omega
            have hmbNat : (mb.toInt.toNat : Int) = mb.toInt := by omega
            let InvInner (k : Nat) (s : Array Int32 × Int32) (hIn : C.Heap) : Prop :=
              hIn = hM ∧ s.2.toInt = dcsC[0]!.blocksInMcu.toInt + (k : Int)
            have hInner : ∃ sFin hIn,
                C.run (forIn (List.range mb.toInt.toNat) (dcsC[0]!.mcuMembership, dcsC[0]!.blocksInMcu)
                  (fun _ __s => pure (ForInStep.yield (__s.fst.set! __s.snd.toInt.toNat (Int32.ofNat idx), __s.snd + 1)))) hM =
                  .ok (sFin, hIn) ∧ InvInner mb.toInt.toNat sFin hIn := by
              refine forIn_range_inv InvInner _ mb.toInt.toNat ?_
                (show InvInner 0 (dcsC[0]!.mcuMembership, dcsC[0]!.blocksInMcu) hM from ⟨rfl, by simp⟩)
              intro k hk s hIn ⟨heqH, hsVal⟩
              subst heqH
              refine ⟨.yield (s.1.set! s.2.toInt.toNat (Int32.ofNat idx), s.2 + 1), hM, rfl, rfl, ?_⟩
              have hkLt : (k : Int) < mb.toInt := by
                have hk0 : (k : Int) < (mb.toInt.toNat : Int) := Int.ofNat_lt.mpr hk
                omega
              have hsBnd : 0 ≤ s.2.toInt ∧ s.2.toInt + 1 ≤ 10 := by omega
              have h1Int : (1 : Int32).toInt = 1 := rfl
              have hplus1 : (s.2 + 1).toInt = s.2.toInt + 1 := by
                rw [Int32.toInt_add, h1Int]
                exact Int.bmod_eq_of_le (by omega) (by omega)
              rw [hplus1, hsVal, Int.natCast_add, Int.add_assoc]; rfl
            obtain ⟨sFin, hIn, hrunIn, heqH, hsFinVal⟩ := hInner
            subst heqH
            have hroDcM : C.Space.ro hM (C.DecompRef.decomp ctx.bdc) = false := rfl
            let dcN : C.JpegDecompressStruct := { (dcsC[0]!) with blocksInMcu := sFin.2, mcuMembership := sFin.1 }
            have hstdcM := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcN) hgdcM hroDcM hszdcC
            let hN := C.Space.put hM (C.DecompRef.decomp ctx.bdc) (dcsC.set! 0 dcN)
            have hpN : ParserEnv ctx hN := parserEnv_put_dc_keep' hpM hgdcM hszdcC
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            have hsawN : CompSawZero ctx hN := compSawZero_put_dc_keep hsawM hgdcM hszdcC rfl
            have hmN : MultiScanReady hN dcN := multiScanReady_put_dc_scalar hgdcM hszdcC
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hmultM
            have hgdcN : C.Space.get hN (C.DecompRef.decomp ctx.bdc) = some (dcsC.set! 0 dcN) := by
              simp [hN, C.Space.get, C.Space.put]
            have hszdcN : 0 < (dcsC.set! 0 dcN).size := by simpa using hszdcC
            have hdcN_bang : (dcsC.set! 0 dcN)[0]! = dcN := set0_bang_m dcsC hszdcC dcN
            refine ⟨.yield (none, ()), hN, ?_, hpN, hsawN, hmM, hsrM, hmaM, hicM, hnwM, ?_,
              herM, dcsC.set! 0 dcN, hgdcN, hszdcN,
              (by rw [hdcN_bang]; exact herrC), (by rw [hdcN_bang]; exact hcisC),
              (by rw [hdcN_bang]; exact hcciC),
              (by rw [hdcN_bang]; show 0 ≤ sFin.2.toInt; omega),
              (by rw [hdcN_bang]; show sFin.2.toInt ≤ 10; omega)⟩
            · dsimp only [stepScan]
              rw [C.run_bind, hldcC]; dsimp only
              rw [C.run_bind, hlcompC']; dsimp only
              simp only [hdivF, Bool.false_eq_true, ↓reduceIte]
              rw [C.run_bind, hmbEq]; dsimp only
              rw [C.run_bind, hmswEq]; dsimp only
              rw [C.run_bind, hstcompC']; dsimp only
              rw [C.run_bind, hldcM]; dsimp only
              rw [C.run_bind, hbimAddEq]; dsimp only
              simp only [hbigF, ↓reduceIte, C.run_bind]
              rw [hrunIn]; dsimp only
              rw [hstdcM]; rfl
            · intro dcsN hgdN _
              rw [Option.some.inj (hgdN.symm.trans hgdcN), hdcN_bang]
              exact ⟨hmN, (hmultC dcsC hgdcC hszdcC).2.1, (hmultC dcsC hgdcC hszdcC).2.2⟩
        · rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, heqN, _⟩
          omega
      obtain ⟨⟨stS, _⟩, hLS, hrunLS, hInvLS⟩ := hloopScan
      rcases stS with _ | r
      · obtain ⟨hpS, hsawS, hmS, hsrS, hmaS, hicS, hnwS, hmultS, _⟩ := hInvLS
        have hrunLS' := hrunLS
        dsimp only [nCis, stepScan, h1] at hrunLS'
        refine ⟨.ok (), hLS, ?_, hpS, hsawS, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · unfold per_scan_setup
          rw [C.run_bind, hldc0]; dsimp only
          rw [C.run_bind, hlmst0']; dsimp only
          simp only [hcis1F, Bool.false_eq_true, ↓reduceIte, hbadCisF, C.run_bind]
          rw [hmprRun]; dsimp only
          rw [hmrisRun]; dsimp only
          rw [hstdc1]; dsimp only
          rw [hrunLS']; rfl
        · intro e0 e' he0 _ he'
          rw [Option.some.inj (he0.symm.trans hgerr0)]
          obtain ⟨errs1, hg1, hsz1, _⟩ := parserEnv_get_err hpS
          rw [Option.some.inj (he'.symm.trans hg1)]
          exact ⟨hsz1, hnwS errs1 hg1 hsz1⟩
        · intro m0 m' hm0 _ hm' _
          simp only [C.Space.get] at hm0 hm'; rw [hmS] at hm'; exact Option.some.inj (hm'.symm.trans hm0)
        · intro s0 s' hs0 _ hs' _
          simp only [C.Space.get] at hs0 hs'; rw [hsrS] at hs'; exact Option.some.inj (hs'.symm.trans hs0)
        · intro a0 a' ha0 _ ha' _
          simp only [C.Space.get] at ha0 ha'; rw [hmaS] at ha'; exact Option.some.inj (ha'.symm.trans ha0)
        · intro i0 i' hi0 _ hi' _
          simp only [C.Space.get] at hi0 hi'; rw [hicS] at hi'; exact Option.some.inj (hi'.symm.trans hi0)
        · intro d0 d' hd0 _ hd' hszd'
          rw [Option.some.inj (hd0.symm.trans hgdc0)]
          exact hmultS d' hd' hszd'
      · obtain ⟨hpS, hsawS, hmS, hsrS, hmaS, hicS, hnwS, hmultS, _, code, hcode⟩ := hInvLS
        have hrunLS' := hrunLS
        dsimp only [nCis, stepScan, h1] at hrunLS'
        refine ⟨.errExit code, hLS, ?_, hpS, hsawS, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · unfold per_scan_setup
          rw [C.run_bind, hldc0]; dsimp only
          rw [C.run_bind, hlmst0']; dsimp only
          simp only [hcis1F, Bool.false_eq_true, ↓reduceIte, hbadCisF, C.run_bind]
          rw [hmprRun]; dsimp only
          rw [hmrisRun]; dsimp only
          rw [hstdc1]; dsimp only
          rw [hrunLS']; dsimp only; rw [hcode]; rfl
        · intro e0 e' he0 _ he'
          rw [Option.some.inj (he0.symm.trans hgerr0)]
          obtain ⟨errs1, hg1, hsz1, _⟩ := parserEnv_get_err hpS
          rw [Option.some.inj (he'.symm.trans hg1)]
          exact ⟨hsz1, hnwS errs1 hg1 hsz1⟩
        · intro m0 m' hm0 _ hm' _
          simp only [C.Space.get] at hm0 hm'; rw [hmS] at hm'; exact Option.some.inj (hm'.symm.trans hm0)
        · intro s0 s' hs0 _ hs' _
          simp only [C.Space.get] at hs0 hs'; rw [hsrS] at hs'; exact Option.some.inj (hs'.symm.trans hs0)
        · intro a0 a' ha0 _ ha' _
          simp only [C.Space.get] at ha0 ha'; rw [hmaS] at ha'; exact Option.some.inj (ha'.symm.trans ha0)
        · intro i0 i' hi0 _ hi' _
          simp only [C.Space.get] at hi0 hi'; rw [hicS] at hi'; exact Option.some.inj (hi'.symm.trans hi0)
        · intro d0 d' hd0 _ hd' hszd'
          rw [Option.some.inj (hd0.symm.trans hgdc0)]
          exact hmultS d' hd' hszd'

private theorem compSawZero_frame {ctx : IoCtx} {h h' : C.Heap}
    (hd : h'.decomps = h.decomps) (hm : h'.markers = h.markers)
    (hsaw : CompSawZero ctx h) : CompSawZero ctx h' := by
  intro mrks dcs hmrks hszmrks hdcs hszdcs h0
  exact hsaw mrks dcs
    (by simp only [C.Space.get] at hmrks ⊢; rw [← hm]; exact hmrks) hszmrks
    (by simp only [C.Space.get] at hdcs ⊢; rw [← hd]; exact hdcs) hszdcs h0

private theorem parserEnv_put_mem_quant {ctx : IoCtx} {h : C.Heap}
    {mems : Array C.JpegMemMgr} {mem' : C.JpegMemMgr}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.rmem = some mems)
    (has : mem'.allocSmall = mems[0]!.allocSmall)
    (hfp : mem'.freePool = mems[0]!.freePool)
    (hsd : mem'.selfDestruct = mems[0]!.selfDestruct)
    (hlp : mem'.livePools = mems[0]!.livePools)
    (hpasz : mem'.poolAllocs.size = 2)
    (hpmas : mem'.poolAllocs[1]!.masters = mems[0]!.poolAllocs[1]!.masters)
    (hpic : mem'.poolAllocs[1]!.inputctls = mems[0]!.poolAllocs[1]!.inputctls)
    (hpmrk : mem'.poolAllocs[1]!.markers = mems[0]!.poolAllocs[1]!.markers)
    (hpsrc : mem'.poolAllocs[1]!.srcs = mems[0]!.poolAllocs[1]!.srcs) :
    ParserEnv ctx (C.Space.put h ctx.rmem (mems.set! 0 mem')) := by
  let h' := C.Space.put h ctx.rmem (mems.set! 0 mem')
  rcases hp with ⟨hvc, hfr, dcs, dc, errs, mems0, masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herr, hgerr, hszerr, hrsterr, hnwerr,
    hmem, hgmem0, hszmem0, halloc, hfree, hself, hlpsz, hlp0, hlp1, hpasz0, hp1m, hp1i, hp1mk, hp1s,
    hmas, hgmas, hszmas, hic, hgic, hszic, hrstic, hconic,
    hmrk, hgmrk, hszmrk, hrm, hrmr, hcom, happn, happlim, hsrc, hgsrc, hszsrc, hinit, hterm, hrest⟩
  have hm0Eq : mems0 = mems := Option.some.inj (hgmem0.symm.trans hg)
  have hmemSz0 : 0 < mems.size := hm0Eq ▸ hszmem0
  have hmemSz : 0 < (mems.set! 0 mem').size := by simpa using hmemSz0
  have hm'Eq : (mems.set! 0 mem')[0]! = mem' := array_set_bang_self mems hmemSz0 mem'
  have hvc' : ValidDecompCore h' (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) := by
    rcases hvc with ⟨rc1, dcs1, dc1, rm1, mems1, rmas1, masters1, ric1, ics1, rmrk1, mrks1,
      hrc1, hgdc1, hszdc1, hdc1, hverr1, hmem1, hgmem1, hszmem1, hmas1, hgmas1, hszmas1,
      hic1, hgic1, hszic1, hmrk1, hgmrk1, hszmrk1, hpa1, hbmas1⟩
    have hrc1' : rc1 = C.DecompRef.decomp ctx.bdc := (C.Ptr.ref.inj hrc1).1.symm
    subst hrc1'
    have hdc1Eq : dcs1 = dcs := Option.some.inj (hgdc1.symm.trans hgdc)
    have hdcEq : dc1 = dc := by rw [hdc1, hdc1Eq, ← hdc]
    have hmem1' : dc.mem = C.Ptr.ref rm1 0 := hdcEq ▸ hmem1
    have hrm1Eq : rm1 = ctx.rmem := (C.Ptr.ref.inj (hmem1'.symm.trans hmem)).1
    subst hrm1Eq
    have hm1Eq : mems1 = mems := Option.some.inj (hgmem1.symm.trans hg)
    refine ⟨C.DecompRef.decomp ctx.bdc, dcs, dc1, ctx.rmem, mems.set! 0 mem', rmas1, masters1, ric1, ics1,
      rmrk1, mrks1, rfl, hgdc, hszdc, hdcEq ▸ hdc, hverr1, hmem1, ?_, hmemSz, hmas1, hgmas1, hszmas1,
      hic1, hgic1, hszic1, hmrk1, hgmrk1, hszmrk1, ?_, ?_⟩
    · dsimp only [h']; simp [C.Space.get, C.Space.put]
    · rw [hm'Eq]; omega
    · intro b hb; rw [hm'Eq, hpmas, ← hm1Eq]; exact hbmas1 b hb
  have hfr' : FreshNextBlk h' := fun b hle => by
    have hhk := hfr b hle
    refine ⟨hhk.1, hhk.2.1, ?_, hhk.2.2.2⟩
    dsimp only [h', C.Space.put, C.upd]
    rw [C.Tbl.get_set]
    by_cases heq : b = ctx.rmem.1
    · exfalso; have hnone := hhk.2.2.1; simp only [C.Space.get] at hg; rw [heq, hg] at hnone; exact absurd hnone (by simp)
    · simp [heq, hhk.2.2.1]
  refine ⟨hvc', hfr', dcs, dc, errs, mems.set! 0 mem', masters, ics, mrks, srcs,
    hgdc, hszdc, hdc, herr, hgerr, hszerr, hrsterr, hnwerr,
    hmem, by simp [C.Space.get, C.Space.put], hmemSz,
    by rw [hm'Eq, has, ← hm0Eq]; exact halloc,
    by rw [hm'Eq, hfp, ← hm0Eq]; exact hfree,
    by rw [hm'Eq, hsd, ← hm0Eq]; exact hself,
    by rw [hm'Eq, hlp, ← hm0Eq]; exact hlpsz,
    by rw [hm'Eq, hlp, ← hm0Eq]; exact hlp0,
    by rw [hm'Eq, hlp, ← hm0Eq]; exact hlp1,
    by rw [hm'Eq]; exact hpasz,
    by rw [hm'Eq, hpmas, ← hm0Eq]; exact hp1m,
    by rw [hm'Eq, hpic, ← hm0Eq]; exact hp1i,
    by rw [hm'Eq, hpmrk, ← hm0Eq]; exact hp1mk,
    by rw [hm'Eq, hpsrc, ← hm0Eq]; exact hp1s,
    hmas, hgmas, hszmas, hic, hgic, hszic, hrstic, hconic,
    hmrk, hgmrk, hszmrk, hrm, hrmr, hcom, happn, happlim, hsrc, hgsrc, hszsrc, hinit, hterm, hrest⟩

private theorem allocSlopRetry_quant_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h) (k : Nat) (slop : UInt64) :
    ∃ res h', C.run (Mozjpeg.Jmemmgr.allocSlopRetry (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) C.allocQuant k slop) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
      h'.decomps = h.decomps ∧ h'.comps = h.comps ∧ h'.markers = h.markers ∧
      h'.masters = h.masters ∧ h'.inputctls = h.inputctls ∧ h'.srcs = h.srcs ∧ h'.mems = h.mems ∧
      (∀ errs0 errs', C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs0[0]!.numWarnings) ∧
      match res with
      | .errExit _ => True
      | .ok p => ∃ b, p = C.Ptr.ref (C.QuantRef.quant b) 0 ∧ C.Space.get h' (C.QuantRef.quant b) = some #[default] := by
  induction k generalizing h slop with
  | zero =>
    obtain ⟨dcs, hgdc, hszdc, herr, _⟩ := parserEnv_get_dc hp
    obtain ⟨errs0, hgerr0, hszerr0, _, _⟩ := parserEnv_get_err hp
    have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
    obtain ⟨h', hrunE, hp', hsaw', hd', hmrk', hsrc', hmas', hc', _, _, hic', hm', hnw'⟩ :=
      errexit1_full hp hsaw JERR_OUT_OF_MEMORY 2
    have hoom : C.run (Mozjpeg.Jmemmgr.out_of_memory (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) 2) h =
        .ok (.errExit JERR_OUT_OF_MEMORY, h') := by
      unfold Mozjpeg.Jmemmgr.out_of_memory
      rw [C.run_bind, hldc]; dsimp only; rw [herr]; exact hrunE
    refine ⟨.errExit JERR_OUT_OF_MEMORY, h', ?_, hp', hsaw', hd', hc', hmrk', hmas', hic', hsrc', hm', hnw', trivial⟩
    change C.run (do
        let _ ← Mozjpeg.Jmemmgr.out_of_memory (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) 2
        pure (C.JpegRes.errExit JERR_OUT_OF_MEMORY)) h = .ok (.errExit JERR_OUT_OF_MEMORY, h')
    rw [C.run_bind, hoom]; rfl
  | succ k ih =>
    unfold Mozjpeg.Jmemmgr.allocSlopRetry
    dsimp only [Mozjpeg.Jmemmgr.allocSlopRetry._f]
    by_cases ha : h.allocOk h.nalloc = true
    · obtain ⟨hpA, hgetQ⟩ := parserEnv_alloc_quant hp
      let hA :=
        { bytes := h.bytes, consts := h.consts, i32s := h.i32s, rgbPixelsize := h.rgbPixelsize,
          naturalOrder := h.naturalOrder, errMgrs := h.errMgrs, decomps := h.decomps, comps := h.comps,
          masters := h.masters, inputctls := h.inputctls, markers := h.markers, mems := h.mems, srcs := h.srcs,
          quants := C.upd h.quants h.nextBlk (some #[default]), huffs := h.huffs, savedMarkers := h.savedMarkers,
          nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1, allocOk := h.allocOk, garbage := h.garbage,
          baseAddr := h.baseAddr : C.Heap }
      have hsawA : CompSawZero ctx hA := compSawZero_frame rfl rfl hsaw
      have hallocRun : C.run C.allocQuant h = .ok (C.Ptr.ref (C.QuantRef.quant h.nextBlk) 0, hA) := by
        simp [C.run, C.allocQuant, ha, hA]
      have hneNull : ((C.Ptr.ref (C.QuantRef.quant h.nextBlk) 0 : C.QuantPtr) != C.Ptr.null) = true := rfl
      refine ⟨.ok (C.Ptr.ref (C.QuantRef.quant h.nextBlk) 0), hA, ?_, hpA, hsawA,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ⟨h.nextBlk, rfl, hgetQ⟩⟩
      · rw [C.run_bind, hallocRun]; dsimp only
        simp [hneNull, C.run]
      · intro e0 e' he0 _ he'
        have hg1 : C.Space.get hA ctx.rerr = some e0 := by simp [hA, C.Space.get] at he0 ⊢; exact he0
        have heq := Option.some.inj (he'.symm.trans hg1)
        subst heq; exact ⟨by assumption, rfl⟩
    · have haF : h.allocOk h.nalloc = false := Bool.eq_false_iff.mpr ha
      let hA :=
        { bytes := h.bytes, consts := h.consts, i32s := h.i32s, rgbPixelsize := h.rgbPixelsize,
          naturalOrder := h.naturalOrder, errMgrs := h.errMgrs, decomps := h.decomps, comps := h.comps,
          masters := h.masters, inputctls := h.inputctls, markers := h.markers, mems := h.mems, srcs := h.srcs,
          quants := h.quants, huffs := h.huffs, savedMarkers := h.savedMarkers, nextBlk := h.nextBlk,
          nalloc := h.nalloc + 1, allocOk := h.allocOk, garbage := h.garbage, baseAddr := h.baseAddr : C.Heap }
      have hpA : ParserEnv ctx hA := parserEnv_put_nalloc hp (h.nalloc + 1)
      have hsawA : CompSawZero ctx hA := compSawZero_frame rfl rfl hsaw
      have hallocRun : C.run C.allocQuant h = .ok (C.Ptr.null, hA) := by
        simp [C.run, C.allocQuant, haF, hA]
      by_cases hsl : slop / 2 < Mozjpeg.Jmemmgr.MIN_SLOP
      · obtain ⟨dcs, hgdc, hszdc, herr, _⟩ := parserEnv_get_dc hpA
        have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
        obtain ⟨h', hrunE, hp', hsaw', hd', hmrk', hsrc', hmas', hc', _, _, hic', hm', hnw'⟩ :=
          errexit1_full hpA hsawA JERR_OUT_OF_MEMORY 2
        have hoom : C.run (Mozjpeg.Jmemmgr.out_of_memory (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) 2) hA =
            .ok (.errExit JERR_OUT_OF_MEMORY, h') := by
          unfold Mozjpeg.Jmemmgr.out_of_memory
          rw [C.run_bind, hldc]; dsimp only; rw [herr]; exact hrunE
        refine ⟨.errExit JERR_OUT_OF_MEMORY, h', ?_, hp', hsaw', hd', hc', hmrk', hmas', hic', hsrc', hm', ?_, trivial⟩
        · rw [C.run_bind, hallocRun]; dsimp only
          have hnnF : ((C.Ptr.null : C.QuantPtr) != C.Ptr.null) = false := by decide
          simp only [hnnF, Bool.false_eq_true, ↓reduceIte, hsl, C.run_bind, hoom]; rfl
        · intro e0 e' he0 hsze0 he'
          exact hnw' e0 e' he0 hsze0 he'
      · obtain ⟨res', h', hrec, hp', hsaw', hd', hc', hmrk', hmas', hic', hsrc', hm', hnw', hres'⟩ :=
          ih hpA hsawA (slop / 2)
        refine ⟨res', h', ?_, hp', hsaw', hd', hc', hmrk', hmas', hic', hsrc', hm', ?_, hres'⟩
        · rw [C.run_bind, hallocRun]; dsimp only
          have hnnF : ((C.Ptr.null : C.QuantPtr) != C.Ptr.null) = false := by decide
          simp only [hnnF, Bool.false_eq_true, ↓reduceIte, hsl]; exact hrec
        · intro e0 e' he0 hsze0 he'
          exact hnw' e0 e' he0 hsze0 he'

private theorem alloc_small_quant_image_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h) :
    ∃ res h', C.run (Mozjpeg.Jmemmgr.alloc_small_quant (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
        JPOOL_IMAGE sizeof_JQUANT_TBL) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
      h'.decomps = h.decomps ∧ h'.comps = h.comps ∧ h'.markers = h.markers ∧
      h'.masters = h.masters ∧ h'.inputctls = h.inputctls ∧ h'.srcs = h.srcs ∧
      (∀ errs0 errs', C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs0[0]!.numWarnings) ∧
      match res with
      | .errExit _ => True
      | .ok p => ∃ b, p = C.Ptr.ref (C.QuantRef.quant b) 0 ∧ C.Space.get h' (C.QuantRef.quant b) = some #[default] := by
  obtain ⟨dcs, hgdc, hszdc, herr, hmem, _⟩ := parserEnv_get_dc hp
  obtain ⟨mems, hgmem, hszmem, has, hfp, hsd, hlpsz, hlp0, hlp1, hpasz⟩ := parserEnv_get_mem hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlmem := ptr_load_ok (r := ctx.rmem) (off := 0) hgmem hszmem
  have hk1 : ¬ (sizeof_JQUANT_TBL > Mozjpeg.Jmemmgr.MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) := by decide
  have hk2 : ¬ (Mozjpeg.Jmemmgr.sizeof_small_pool_hdr +
      Mozjpeg.Jmemmgr.round_up_pow2 sizeof_JQUANT_TBL Mozjpeg.Jmemmgr.ALIGN_SIZE +
      Mozjpeg.Jmemmgr.ALIGN_SIZE - 1 > Mozjpeg.Jmemmgr.MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) := by decide
  have hk3 : ¬ ((decide (JPOOL_IMAGE < 0) || decide (JPOOL_IMAGE ≥ JPOOL_NUMPOOLS)) = true) := by decide
  have pidEq : JPOOL_IMAGE.toInt.toNat = 1 := rfl
  let alignedSize := Mozjpeg.Jmemmgr.round_up_pow2 sizeof_JQUANT_TBL Mozjpeg.Jmemmgr.ALIGN_SIZE
  let maxChunkU := Mozjpeg.Jmemmgr.MAX_ALLOC_CHUNK.toInt.toNat.toUInt64
  let initSlop := Mozjpeg.Jmemmgr.first_pool_slop[JPOOL_IMAGE.toInt.toNat]!
  let remChunk := maxChunkU - (Mozjpeg.Jmemmgr.sizeof_small_pool_hdr + alignedSize + Mozjpeg.Jmemmgr.ALIGN_SIZE - 1)
  let slop := if initSlop > remChunk then remChunk else initSlop
  obtain ⟨resR, hR, hrunR, hpR, hsawR, hdR, hcR, hmrkR, hmasR, hicR, hsrcR, hmR, hnwR, hresR⟩ :=
    allocSlopRetry_quant_parser hp hsaw 16 slop
  rcases resR with p | code
  · obtain ⟨b, rfl, hqR⟩ := hresR
    obtain ⟨dcsR, hgdcR, hszdcR, _, hmemR, _⟩ := parserEnv_get_dc hpR
    obtain ⟨memsR, hgmemR, hszmemR, _, _, _, _, _, _, hpaszR⟩ := parserEnv_get_mem hpR
    have hldcR := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcR hszdcR
    have hlmemR := ptr_load_ok (r := ctx.rmem) (off := 0) hgmemR hszmemR
    have hroMemR : C.Space.ro hR ctx.rmem = false := rfl
    let allocs0 := memsR[0]!.poolAllocs[JPOOL_IMAGE.toInt.toNat]!
    let allocs2 : C.PoolAllocs := { allocs0 with quants := allocs0.quants.push b }
    let mem2' : C.JpegMemMgr := {
      (memsR[0]!) with
      totalSpaceAllocated := memsR[0]!.totalSpaceAllocated + alignedSize
      poolAllocs := memsR[0]!.poolAllocs.set! JPOOL_IMAGE.toInt.toNat allocs2 }
    have hstMem := ptr_store_ok (r := ctx.rmem) (off := 0) (v := mem2') hgmemR hroMemR hszmemR
    let h' := C.Space.put hR ctx.rmem (memsR.set! 0 mem2')
    have h1lt : 1 < memsR[0]!.poolAllocs.size := by rw [hpaszR]; omega
    have hp' : ParserEnv ctx h' := parserEnv_put_mem_quant hpR hgmemR rfl rfl rfl rfl
      (by simpa [mem2'] using hpaszR)
      (by dsimp only [mem2']; rw [show JPOOL_IMAGE.toInt.toNat = 1 from rfl, array_set_bang_self memsR[0]!.poolAllocs h1lt allocs2]; rfl)
      (by dsimp only [mem2']; rw [show JPOOL_IMAGE.toInt.toNat = 1 from rfl, array_set_bang_self memsR[0]!.poolAllocs h1lt allocs2]; rfl)
      (by dsimp only [mem2']; rw [show JPOOL_IMAGE.toInt.toNat = 1 from rfl, array_set_bang_self memsR[0]!.poolAllocs h1lt allocs2]; rfl)
      (by dsimp only [mem2']; rw [show JPOOL_IMAGE.toInt.toNat = 1 from rfl, array_set_bang_self memsR[0]!.poolAllocs h1lt allocs2]; rfl)
    have hsaw' : CompSawZero ctx h' := compSawZero_frame rfl rfl hsawR
    have hq' : C.Space.get h' (C.QuantRef.quant b) = some #[default] := by
      simp only [h', C.Space.get, C.Space.put]; exact hqR
    refine ⟨.ok (C.Ptr.ref (C.QuantRef.quant b) 0), h', ?_, hp', hsaw', hdR, hcR, hmrkR, hmasR, hicR, hsrcR, ?_, ⟨b, rfl, hq'⟩⟩
    · unfold Mozjpeg.Jmemmgr.alloc_small_quant Mozjpeg.Jmemmgr.allocSmallCore
      rw [C.run_bind, hldc]; dsimp only
      simp only [hk1, hk2, hk3, Bool.false_eq_true, ↓reduceIte, C.run_bind]
      rw [hmem, hlmem]; dsimp only
      rw [hrunR]; dsimp only
      rw [C.run_bind, hldcR]; dsimp only
      rw [C.run_bind, hmemR, hlmemR]; dsimp only
      rw [C.run_bind, hstMem]; rfl
    · intro e0 e' he0 hsze0 he'
      have he'R : C.Space.get hR ctx.rerr = some e' := by simp only [h', C.Space.get, C.Space.put] at he'; exact he'
      exact hnwR e0 e' he0 hsze0 he'R
  · refine ⟨.errExit code, hR, ?_, hpR, hsawR, hdR, hcR, hmrkR, hmasR, hicR, hsrcR, hnwR, trivial⟩
    unfold Mozjpeg.Jmemmgr.alloc_small_quant Mozjpeg.Jmemmgr.allocSmallCore
    rw [C.run_bind, hldc]; dsimp only
    simp only [hk1, hk2, hk3, Bool.false_eq_true, ↓reduceIte, C.run_bind]
    rw [hmem, hlmem]; dsimp only
    rw [hrunR]; rfl

private theorem bind_jpegRes_eq {α β : Type} (m : C.M (C.JpegRes α))
    {f g : C.JpegRes α → C.M β}
    (herr : ∀ c, f (.errExit c) = g (.errExit c))
    (hok : ∀ a, f (.ok a) = g (.ok a)) :
    (m >>= f) = (m >>= g) := by
  congr 1; funext x; cases x with | ok a => exact hok a | errExit c => exact herr c

theorem latch_quant_tables_ok {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h)
    (hm : ∀ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      MultiScanReady h dcs[0]!) :
    ∃ res h', C.run (Mozjpeg.Jdinput.latch_quant_tables (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
      (∀ errs0 errs', C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs0[0]!.numWarnings) ∧
      (∀ mrks0 mrks', C.Space.get h ctx.rmrk = some mrks0 → 0 < mrks0.size →
        C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size → mrks' = mrks0) ∧
      (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size → srcs' = srcs0) ∧
      (∀ masters0 masters', C.Space.get h ctx.rmas = some masters0 → 0 < masters0.size →
        C.Space.get h' ctx.rmas = some masters' → 0 < masters'.size → masters' = masters0) ∧
      (∀ ics0 ics', C.Space.get h ctx.ric = some ics0 → 0 < ics0.size →
        C.Space.get h' ctx.ric = some ics' → 0 < ics'.size → ics' = ics0) ∧
      (∀ dcs0 dcs', C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
        C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
        MultiScanReady h' dcs'[0]! ∧
        dcs'[0]!.inputScanNumber = dcs0[0]!.inputScanNumber ∧
        dcs'[0]!.unreadMarker = dcs0[0]!.unreadMarker ∧
        dcs'[0]!.entropyStartPass = dcs0[0]!.entropyStartPass ∧
        dcs'[0]!.coefStartInputPass = dcs0[0]!.coefStartInputPass ∧
        dcs'[0]!.coefConsumeData = dcs0[0]!.coefConsumeData) := by
  obtain ⟨dcs0, hgdc0, hszdc0, herr0, _, _, _⟩ := parserEnv_get_dc hp
  obtain ⟨errs0, hgerr0, hszerr0, _, _⟩ := parserEnv_get_err hp
  obtain ⟨mrks0, hgmrk0, hszmrk0, _⟩ := parserEnv_get_mrk hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
  obtain ⟨masters0, hgmas0, hszmas0⟩ := parserEnv_get_mas hp
  obtain ⟨ics0, hgic0, hszic0, _, _⟩ := parserEnv_get_ic hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  let nCis := dcs0[0]!.compsInScan.toInt.toNat
  let InvLatch : Nat → Option (C.JpegRes Unit) × Unit → C.Heap → Prop := fun idx st hCur =>
    ParserEnv ctx hCur ∧ CompSawZero ctx hCur ∧
    C.Space.get hCur ctx.rmrk = some mrks0 ∧
    C.Space.get hCur ctx.rs = some srcs0 ∧
    C.Space.get hCur ctx.rmas = some masters0 ∧
    C.Space.get hCur ctx.ric = some ics0 ∧
    (∀ errs1, C.Space.get hCur ctx.rerr = some errs1 → 0 < errs1.size → errs1[0]!.numWarnings = errs0[0]!.numWarnings) ∧
    hCur.decomps = h.decomps ∧
    (∀ dcsC, C.Space.get hCur (C.DecompRef.decomp ctx.bdc) = some dcsC → 0 < dcsC.size →
      MultiScanReady hCur dcsC[0]!) ∧
    (match st.fst with
    | none => True
    | some r => idx = nCis ∧ ∃ code, r = .errExit code)
  have hInv_init : InvLatch 0 (none, ()) h :=
    ⟨hp, hsaw, hgmrk0, hgsrc0, hgmas0, hgic0,
      fun e1 hg1 _ => by rw [Option.some.inj (hg1.symm.trans hgerr0)],
      rfl, hm, trivial⟩
  let stepLatch : Nat → Option (C.JpegRes Unit) × Unit → C.M (ForInStep (Option (C.JpegRes Unit) × Unit)) :=
    fun ci _ => do
      let dcCur ← C.Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
      have cp : C.CompPtr := dcCur.curCompInfo[ci]!
      let comp ← C.Ptr.load cp
      if (comp.quantTable == C.Ptr.null) = true then
        have qtblno := comp.quantTblNo
        if (decide (qtblno < 0) || decide (qtblno ≥ NUM_QUANT_TBLS) ||
            dcCur.quantTblPtrs[qtblno.toInt.toNat]! == C.Ptr.null) = true then do
          let _ ← Mozjpeg.JerrorH.errexit1 dcCur.err JERR_NO_QUANT_TABLE qtblno
          pure (ForInStep.done (some (C.JpegRes.errExit JERR_NO_QUANT_TABLE), ()))
        else do
          let __do_lift ← Mozjpeg.Jmemmgr.alloc_small_quant (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
            JPOOL_IMAGE sizeof_JQUANT_TBL
          match __do_lift with
          | C.JpegRes.errExit code => pure (ForInStep.done (some (C.JpegRes.errExit code), ()))
          | C.JpegRes.ok qPtr => do
            let srcQ ← C.Ptr.load dcCur.quantTblPtrs[qtblno.toInt.toNat]!
            C.Ptr.store qPtr srcQ
            let comp' ← C.Ptr.load cp
            C.Ptr.store cp { comp' with quantTable := qPtr }
            pure (ForInStep.yield (none, ()))
      else
        pure (ForInStep.yield (none, ()))
  have hloop : ∃ stL hL,
      C.run (forIn (List.range nCis) (none, ()) stepLatch) h = .ok (stL, hL) ∧ InvLatch nCis stL hL := by
    refine forIn_range_inv InvLatch stepLatch nCis ?_ hInv_init
    intro idx hlt ⟨o, u⟩ hCur hinv
    rcases o with _ | r
    · obtain ⟨hpC, hsawC, hmC, hsrC, hmaC, hicC, hnwC, hdeqC, hmultC, _⟩ := hinv
      obtain ⟨dcsC, hgdcC, hszdcC, herrC, _, _, _, _, _⟩ := parserEnv_get_dc hpC
      have hgdcC' : C.Space.get hCur (C.DecompRef.decomp ctx.bdc) = some dcsC := hgdcC
      have hldcC := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcC' hszdcC
      have hmCur := hmultC dcsC hgdcC' hszdcC
      have hcisC : idx < dcsC[0]!.compsInScan.toInt.toNat := by
        have hdeq : dcsC = dcs0 := Option.some.inj (by
          simp only [C.Space.get] at hgdcC' hgdc0
          rw [hdeqC] at hgdcC'
          exact hgdcC'.symm.trans hgdc0)
        rw [hdeq]; exact hlt
      obtain ⟨rcpI, offI, csI, ciI, hcciI, hgcsI, hoffI, hciIEq, hciIB⟩ := hmCur.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hcisC
      have hlcompC := ptr_load_ok (r := rcpI) (off := offI) hgcsI hoffI
      have hlcompC' : C.run (C.Ptr.load dcsC[0]!.curCompInfo[idx]!) hCur = .ok (csI[offI]!, hCur) := by
        rw [hcciI]; exact hlcompC
      by_cases hqn : (csI[offI]!.quantTable == C.Ptr.null) = true
      · have hqnB : csI[offI]!.quantTable == C.Ptr.null := hqn
        let qtblno := csI[offI]!.quantTblNo
        by_cases hbadQ : (decide (qtblno < 0) || decide (qtblno ≥ NUM_QUANT_TBLS) ||
            dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]! == C.Ptr.null) = true
        · obtain ⟨hE, hrunE, hpE, hsawE, hdE, hmrkE, hsrcE, hmasE, hcE, _, _, hicE, _, hnwE⟩ :=
            errexit1_full hpC hsawC JERR_NO_QUANT_TABLE qtblno
          refine ⟨ForInStep.done (.some (.errExit JERR_NO_QUANT_TABLE), ()), hE, ?_, ?_⟩
          · dsimp only [stepLatch]
            rw [C.run_bind, hldcC]; dsimp only
            rw [C.run_bind, hlcompC']; dsimp only
            simp only [hqn, ↓reduceIte]
            change C.run (if (decide (qtblno < 0) || decide (qtblno ≥ NUM_QUANT_TBLS) ||
                dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]! == C.Ptr.null) = true then do
                let _ ← Mozjpeg.JerrorH.errexit1 dcsC[0]!.err JERR_NO_QUANT_TABLE qtblno
                pure (ForInStep.done (some (C.JpegRes.errExit JERR_NO_QUANT_TABLE), ()))
              else _) hCur = _
            simp only [hbadQ, ↓reduceIte, C.run_bind]
            rw [herrC, hrunE]; rfl
          · refine ⟨hpE, hsawE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, JERR_NO_QUANT_TABLE, rfl⟩
            · simp only [C.Space.get] at hmC ⊢; rw [hmrkE]; exact hmC
            · simp only [C.Space.get] at hsrC ⊢; rw [hsrcE]; exact hsrC
            · simp only [C.Space.get] at hmaC ⊢; rw [hmasE]; exact hmaC
            · simp only [C.Space.get] at hicC ⊢; rw [hicE]; exact hicC
            · intro e1 hg1 hsz1
              obtain ⟨errsC, hgerrC, hszerrC, _, _⟩ := parserEnv_get_err hpC
              exact (hnwE errsC e1 hgerrC hszerrC hg1).2.trans (hnwC errsC hgerrC hszerrC)
            · exact hdE.trans hdeqC
            · intro dcsE hgdcE _
              have hdeqE : dcsE = dcsC := Option.some.inj (by
                simp only [C.Space.get] at hgdcE hgdcC'
                rw [hdE] at hgdcE; exact hgdcE.symm.trans hgdcC')
              rw [hdeqE]
              exact multiScanReady_frame hmCur hmrkE hcE
        · have hbadQF : (decide (qtblno < 0) || decide (qtblno ≥ NUM_QUANT_TBLS) ||
              dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]! == C.Ptr.null) = false :=
            Bool.eq_false_iff.mpr hbadQ
          have hqLt : qtblno.toInt.toNat < 4 := by
            simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hbadQF
            have h1 : ¬ (qtblno < 0) := hbadQF.1.1
            have h2 : ¬ (qtblno ≥ NUM_QUANT_TBLS) := hbadQF.1.2
            have h1' : 0 ≤ qtblno.toInt := by
              suffices ¬ (qtblno.toInt < 0) by omega
              exact fun hlt' => h1 (Int32.lt_iff_toInt_lt.mpr hlt')
            have h2' : qtblno.toInt < 4 := by
              suffices ¬ (4 ≤ qtblno.toInt) by omega
              exact fun hge' => h2 (Int32.le_iff_toInt_le.mpr hge')
            omega
          have hqNeNull : dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]! ≠ C.Ptr.null := by
            simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hbadQF
            exact hbadQF.2
          obtain ⟨resQ, hQ, hrunQ, hpQ, hsawQ, hdQ, hcQ, hmrkQ, hmasQ, hicQ, hsrcQ, hnwQ, hresQ⟩ :=
            alloc_small_quant_image_parser hpC hsawC
          have hmQ : ∀ dcsQ, C.Space.get hQ (C.DecompRef.decomp ctx.bdc) = some dcsQ → 0 < dcsQ.size →
              MultiScanReady hQ dcsQ[0]! := fun dcsQ hgdcQ _ => by
            have hdeq : dcsQ = dcsC := Option.some.inj (by
              simp only [C.Space.get] at hgdcQ hgdcC'; rw [hdQ] at hgdcQ; exact hgdcQ.symm.trans hgdcC')
            rw [hdeq]
            exact multiScanReady_frame hmCur hmrkQ hcQ
          rcases resQ with qPtr | code
          · obtain ⟨b, rfl, hgetQ⟩ := hresQ
            obtain ⟨dcsQ, hgdcQ, _, _, hqtPtrsQ, _⟩ := parserEnv_get_dc_arrs hpQ
            have hdeqQ : dcsQ = dcsC := Option.some.inj (by
              simp only [C.Space.get] at hgdcQ hgdcC'; rw [hdQ] at hgdcQ; exact hgdcQ.symm.trans hgdcC')
            have hqPtrCases := hqtPtrsQ qtblno.toInt.toNat hqLt
            have hqNeNullQ : dcsQ[0]!.quantTblPtrs[qtblno.toInt.toNat]! ≠ C.Ptr.null := by
              rw [hdeqQ]; exact hqNeNull
            obtain ⟨rq, offQ, qsQ, hqPtrEq, hgqsQ, hoffQ⟩ := hqPtrCases.resolve_left hqNeNullQ
            have hldSrcQ : C.run (C.Ptr.load dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]!) hQ = .ok (qsQ[offQ]!, hQ) := by
              rw [← hdeqQ, hqPtrEq]; exact ptr_load_ok hgqsQ hoffQ
            have hroQ : C.Space.ro hQ (C.QuantRef.quant b) = false := rfl
            have hszQ : 0 < (#[default] : Array C.JQuantTbl).size := by decide
            have hstQ := ptr_store_ok (r := C.QuantRef.quant b) (off := 0) (v := qsQ[offQ]!) hgetQ hroQ hszQ
            let hA := C.Space.put hQ (C.QuantRef.quant b) ((#[default] : Array C.JQuantTbl).set! 0 qsQ[offQ]!)
            have hpA : ParserEnv ctx hA := parserEnv_put_quant hpQ hgetQ
            have hsawA : CompSawZero ctx hA := compSawZero_put_quant hsawQ
            have hmA : ∀ dcsA, C.Space.get hA (C.DecompRef.decomp ctx.bdc) = some dcsA → 0 < dcsA.size →
                MultiScanReady hA dcsA[0]! := fun dcsA hgdcA hszdcA =>
              multiScanReady_put_quant (hmQ dcsA hgdcA hszdcA)
            have hgcsA : C.Space.get hA rcpI = some csI := by
              simp only [hA, C.Space.get, C.Space.put]; rw [hcQ]; exact hgcsI
            have hldCompA := ptr_load_ok (r := rcpI) (off := offI) hgcsA hoffI
            have hldCompA' : C.run (C.Ptr.load dcsC[0]!.curCompInfo[idx]!) hA = .ok (csI[offI]!, hA) := by
              rw [hcciI]; exact hldCompA
            have hroCompA : C.Space.ro hA rcpI = false := rfl
            let comp'' : C.JpegCompInfo := { (csI[offI]!) with quantTable := C.Ptr.ref (C.QuantRef.quant b) 0 }
            have hstCompA := ptr_store_ok (r := rcpI) (off := offI) (v := comp'') hgcsA hroCompA hoffI
            have hstCompA' : C.run (C.Ptr.store dcsC[0]!.curCompInfo[idx]! comp'') hA =
                .ok ((), C.Space.put hA rcpI (csI.set! offI comp'')) := by
              rw [hcciI]; exact hstCompA
            let hB := C.Space.put hA rcpI (csI.set! offI comp'')
            have hpB : ParserEnv ctx hB := parserEnv_put_comp hpA hgcsA
            have hsawB : CompSawZero ctx hB := compSawZero_put_comp hsawA
            have hmB : ∀ dcsB, C.Space.get hB (C.DecompRef.decomp ctx.bdc) = some dcsB → 0 < dcsB.size →
                MultiScanReady hB dcsB[0]! := fun dcsB hgdcB hszdcB =>
              multiScanReady_put_comp hgcsA hoffI rfl rfl rfl (hmA dcsB hgdcB hszdcB)
            refine ⟨ForInStep.yield (.none, ()), hB, ?_, ?_⟩
            · dsimp only [stepLatch]
              rw [C.run_bind, hldcC]; dsimp only
              rw [C.run_bind, hlcompC']; dsimp only
              simp only [hqn, ↓reduceIte]
              change C.run (if (decide (qtblno < 0) || decide (qtblno ≥ NUM_QUANT_TBLS) ||
                  dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]! == C.Ptr.null) = true then _ else do
                let __do_lift ← Mozjpeg.Jmemmgr.alloc_small_quant (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
                  JPOOL_IMAGE sizeof_JQUANT_TBL
                match __do_lift with
                | C.JpegRes.errExit code => pure (ForInStep.done (some (C.JpegRes.errExit code), ()))
                | C.JpegRes.ok qPtr => do
                  let srcQ ← C.Ptr.load dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]!
                  C.Ptr.store qPtr srcQ
                  let comp' ← C.Ptr.load dcsC[0]!.curCompInfo[idx]!
                  C.Ptr.store dcsC[0]!.curCompInfo[idx]! { comp' with quantTable := qPtr }
                  pure (ForInStep.yield (none, ()))) hCur = _
              simp only [hbadQF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hrunQ]; dsimp only
              rw [C.run_bind, hldSrcQ]; dsimp only
              rw [C.run_bind, hstQ]; dsimp only
              rw [C.run_bind, hldCompA']; dsimp only
              rw [C.run_bind, hstCompA']; rfl
            · refine ⟨hpB, hsawB, ?_, ?_, ?_, ?_, ?_, ?_, hmB, trivial⟩
              · simp only [hB, hA, C.Space.get, C.Space.put]; rw [hmrkQ]; exact hmC
              · simp only [hB, hA, C.Space.get, C.Space.put]; rw [hsrcQ]; exact hsrC
              · simp only [hB, hA, C.Space.get, C.Space.put]; rw [hmasQ]; exact hmaC
              · simp only [hB, hA, C.Space.get, C.Space.put]; rw [hicQ]; exact hicC
              · intro e1 hg1 hsz1
                have hg1Q : C.Space.get hQ ctx.rerr = some e1 := by
                  simp only [hB, hA, C.Space.get, C.Space.put] at hg1; exact hg1
                obtain ⟨errsC, hgerrC, hszerrC, _, _⟩ := parserEnv_get_err hpC
                exact (hnwQ errsC e1 hgerrC hszerrC hg1Q).2.trans (hnwC errsC hgerrC hszerrC)
              · exact hdQ.trans hdeqC
          · refine ⟨ForInStep.done (.some (.errExit code), ()), hQ, ?_, ?_⟩
            · dsimp only [stepLatch]
              rw [C.run_bind, hldcC]; dsimp only
              rw [C.run_bind, hlcompC']; dsimp only
              simp only [hqn, ↓reduceIte]
              change C.run (if (decide (qtblno < 0) || decide (qtblno ≥ NUM_QUANT_TBLS) ||
                  dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]! == C.Ptr.null) = true then _ else do
                let __do_lift ← Mozjpeg.Jmemmgr.alloc_small_quant (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
                  JPOOL_IMAGE sizeof_JQUANT_TBL
                match __do_lift with
                | C.JpegRes.errExit code => pure (ForInStep.done (some (C.JpegRes.errExit code), ()))
                | C.JpegRes.ok qPtr => do
                  let srcQ ← C.Ptr.load dcsC[0]!.quantTblPtrs[qtblno.toInt.toNat]!
                  C.Ptr.store qPtr srcQ
                  let comp' ← C.Ptr.load dcsC[0]!.curCompInfo[idx]!
                  C.Ptr.store dcsC[0]!.curCompInfo[idx]! { comp' with quantTable := qPtr }
                  pure (ForInStep.yield (none, ()))) hCur = _
              simp only [hbadQF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hrunQ]; rfl
            · refine ⟨hpQ, hsawQ, ?_, ?_, ?_, ?_, ?_, ?_, hmQ, rfl, code, rfl⟩
              · simp only [C.Space.get] at hmC ⊢; rw [hmrkQ]; exact hmC
              · simp only [C.Space.get] at hsrC ⊢; rw [hsrcQ]; exact hsrC
              · simp only [C.Space.get] at hmaC ⊢; rw [hmasQ]; exact hmaC
              · simp only [C.Space.get] at hicC ⊢; rw [hicQ]; exact hicC
              · intro e1 hg1 hsz1
                obtain ⟨errsC, hgerrC, hszerrC, _, _⟩ := parserEnv_get_err hpC
                exact (hnwQ errsC e1 hgerrC hszerrC hg1).2.trans (hnwC errsC hgerrC hszerrC)
              · exact hdQ.trans hdeqC
      · have hqnF : (csI[offI]!.quantTable == C.Ptr.null) = false := Bool.eq_false_iff.mpr hqn
        refine ⟨ForInStep.yield (.none, ()), hCur, ?_, hpC, hsawC, hmC, hsrC, hmaC, hicC, hnwC, hdeqC, hmultC, trivial⟩
        dsimp only [stepLatch]
        rw [C.run_bind, hldcC]; dsimp only
        rw [C.run_bind, hlcompC']; dsimp only
        simp [hqnF, C.run]
    · obtain ⟨hpC, hsawC, hmC, hsrC, hmaC, hicC, hnwC, hdeqC, hmultC, hidxEq, code, rfl⟩ := hinv
      omega
  obtain ⟨stL, hL, hrunL, hInvL⟩ := hloop
  obtain ⟨hpL, hsawL, hmL, hsrL, hmaL, hicL, hnwL, hdL, hmultL, hstL⟩ := hInvL
  rcases stL with ⟨oL, ⟨⟩⟩
  have hresL : ∃ resL, C.run (match oL with | some r => pure r | none => pure (JpegRes.ok ())) hL = .ok (resL, hL) := by
    rcases oL with _ | r
    · exact ⟨.ok (), rfl⟩
    · exact ⟨r, rfl⟩
  obtain ⟨resL, hpostL⟩ := hresL
  refine ⟨resL, hL, ?_, hpL, hsawL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Mozjpeg.Jdinput.latch_quant_tables
    rw [C.run_bind, hldc0]; dsimp only
    rw [C.run_bind]
    have hforEq :
        ∀ fn : Nat → Option (C.JpegRes Unit) × Unit → C.M (ForInStep (Option (C.JpegRes Unit) × Unit)),
          (∀ ci __s, fn ci __s = stepLatch ci __s) →
          forIn (List.range dcs0[0]!.compsInScan.toInt.toNat) (none, ()) fn =
          forIn (List.range nCis) (none, ()) stepLatch := by
      intro fn hfn
      change forIn (List.range nCis) (none, ()) fn = forIn (List.range nCis) (none, ()) stepLatch
      congr 1; exact funext fun ci => funext (hfn ci)
    rw [hforEq]
    · rw [hrunL]; dsimp only
      rcases oL with _ | r <;> simpa using hpostL
    · intro ci _
      dsimp only [stepLatch]
      apply congrArg (C.Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0) >>= ·)
      funext dcCur
      apply congrArg (C.Ptr.load dcCur.curCompInfo[ci]! >>= ·)
      funext comp
      by_cases h1 : (comp.quantTable == C.Ptr.null) = true <;> simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (decide (comp.quantTblNo < 0) || decide (comp.quantTblNo ≥ NUM_QUANT_TBLS) ||
          dcCur.quantTblPtrs[comp.quantTblNo.toInt.toNat]! == C.Ptr.null) = true <;>
        simp only [h2, Bool.false_eq_true, ↓reduceIte]
      exact bind_jpegRes_eq _ (fun _ => rfl) (fun _ => rfl)
  · intro e0 e' he0 _ he'
    rw [Option.some.inj (he0.symm.trans hgerr0)]
    obtain ⟨errs1, hg1, hsz1, _⟩ := parserEnv_get_err hpL
    rw [Option.some.inj (he'.symm.trans hg1)]
    exact ⟨hsz1, hnwL errs1 hg1 hsz1⟩
  · intro m0 m' hm0 _ hm' _; exact Option.some.inj (hm'.symm.trans (hmL.trans (hgmrk0.symm.trans hm0)))
  · intro s0 s' hs0 _ hs' _; exact Option.some.inj (hs'.symm.trans (hsrL.trans (hgsrc0.symm.trans hs0)))
  · intro a0 a' ha0 _ ha' _; exact Option.some.inj (ha'.symm.trans (hmaL.trans (hgmas0.symm.trans ha0)))
  · intro i0 i' hi0 _ hi' _; exact Option.some.inj (hi'.symm.trans (hicL.trans (hgic0.symm.trans hi0)))
  · intro d0 d' hd0 _ hd' hszd'
    have hmrL' := hmultL d' hd' hszd'
    have hd0eq : d0 = dcs0 := Option.some.inj (hd0.symm.trans hgdc0)
    have hd'eq : d' = dcs0 := Option.some.inj (by
      simp only [C.Space.get] at hd' hgdc0
      rw [hdL] at hd'; exact hd'.symm.trans hgdc0)
    rw [hd0eq, hd'eq]
    exact ⟨by rw [← hd'eq]; exact hmrL', rfl, rfl, rfl, rfl, rfl⟩

theorem start_input_pass_ok {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h)
    (hm : ∀ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      MultiScanReady h dcs[0]!) :
    ∃ res h', C.run (Mozjpeg.Jdinput.start_input_pass (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
      (∀ errs0 errs', C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs0[0]!.numWarnings) ∧
      (∀ mrks0 mrks', C.Space.get h ctx.rmrk = some mrks0 → 0 < mrks0.size →
        C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size → mrks' = mrks0) ∧
      (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size → srcs' = srcs0) ∧
      (∀ masters0 masters', C.Space.get h ctx.rmas = some masters0 → 0 < masters0.size →
        C.Space.get h' ctx.rmas = some masters' → 0 < masters'.size → masters' = masters0) ∧
      (∀ dcs0 dcs', C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
        C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
        MultiScanReady h' dcs'[0]! ∧
        dcs'[0]!.inputScanNumber = dcs0[0]!.inputScanNumber ∧
        dcs'[0]!.unreadMarker = dcs0[0]!.unreadMarker) ∧
      (∀ ics0 ics', C.Space.get h ctx.ric = some ics0 → 0 < ics0.size →
        C.Space.get h' ctx.ric = some ics' → 0 < ics'.size →
        ics'[0]!.eoiReached = ics0[0]!.eoiReached ∧
        ics'[0]!.inheaders = ics0[0]!.inheaders ∧
        ics'[0]!.hasMultipleScans = ics0[0]!.hasMultipleScans ∧
        match res with
        | .ok () => ics'[0]!.consumeInput = C.FnPtr.fn "dummy_consume_data"
        | .errExit _ => ics'[0]!.consumeInput = ics0[0]!.consumeInput) := by
  obtain ⟨dcs0, hgdc0, hszdc0, _⟩ := parserEnv_get_dc hp
  obtain ⟨errs0, hgerr0, hszerr0, _, _⟩ := parserEnv_get_err hp
  obtain ⟨mrks0, hgmrk0, hszmrk0, _⟩ := parserEnv_get_mrk hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
  obtain ⟨masters0, hgmas0, hszmas0⟩ := parserEnv_get_mas hp
  obtain ⟨ics0, hgic0, hszic0, _, _⟩ := parserEnv_get_ic hp
  obtain ⟨resP, hP, hrunP, hpP, hsawP, hnwP, hmrkP, hsrcP, hmasP, hicP, hmultP⟩ :=
    per_scan_setup_ok hp hsaw hm
  rcases resP with ⟨⟩ | code
  · obtain ⟨dcsP, hgdcP, hszdcP, _, _, hmasP_ref, hicP_ref, _⟩ := parserEnv_get_dc hpP
    obtain ⟨mastersP, hgmasP, hszmasP⟩ := parserEnv_get_mas hpP
    have hldcP := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcP hszdcP
    have hlmstP := ptr_load_ok (r := ctx.rmas) (off := 0) hgmasP hszmasP
    have hmasEqP : mastersP = masters0 := hmasP masters0 mastersP hgmas0 hszmas0 hgmasP hszmasP
    have hicEqP : ∀ icsP, C.Space.get hP ctx.ric = some icsP → 0 < icsP.size → icsP = ics0 :=
      fun icsP hgi hszi => hicP ics0 icsP hgic0 hszic0 hgi hszi
    have hdP_flds := hmultP dcs0 dcsP hgdc0 hszdc0 hgdcP hszdcP
    have hrunPost :
        ∃ resL hL,
          C.run (if (mastersP[0]!.lossless == 0) = true then do
              let __do_lift ← Mozjpeg.Jdinput.latch_quant_tables (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
              match __do_lift with
              | .errExit code => pure (.errExit code)
              | .ok () => do
                let dc1 ← C.Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
                if (dc1.entropyStartPass != C.FnPtr.fn "noop") = true then do
                  let _ : Unit ← C.ub "unsupported entropy start_pass"
                  if (dc1.coefStartInputPass != C.FnPtr.fn "noop") = true then do
                    let _ : Unit ← C.ub "unsupported coef start_input_pass"
                    let ic ← C.Ptr.load dc1.inputctl
                    C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                    pure (C.JpegRes.ok ())
                  else do
                    let ic ← C.Ptr.load dc1.inputctl
                    C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                    pure (C.JpegRes.ok ())
                else if (dc1.coefStartInputPass != C.FnPtr.fn "noop") = true then do
                  let _ : Unit ← C.ub "unsupported coef start_input_pass"
                  let ic ← C.Ptr.load dc1.inputctl
                  C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                  pure (C.JpegRes.ok ())
                else do
                  let ic ← C.Ptr.load dc1.inputctl
                  C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                  pure (C.JpegRes.ok ())
            else do
              let dc1 ← C.Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
              if (dc1.entropyStartPass != C.FnPtr.fn "noop") = true then do
                let _ : Unit ← C.ub "unsupported entropy start_pass"
                if (dc1.coefStartInputPass != C.FnPtr.fn "noop") = true then do
                  let _ : Unit ← C.ub "unsupported coef start_input_pass"
                  let ic ← C.Ptr.load dc1.inputctl
                  C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                  pure (C.JpegRes.ok ())
                else do
                  let ic ← C.Ptr.load dc1.inputctl
                  C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                  pure (C.JpegRes.ok ())
              else if (dc1.coefStartInputPass != C.FnPtr.fn "noop") = true then do
                let _ : Unit ← C.ub "unsupported coef start_input_pass"
                let ic ← C.Ptr.load dc1.inputctl
                C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                pure (C.JpegRes.ok ())
              else do
                let ic ← C.Ptr.load dc1.inputctl
                C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                pure (C.JpegRes.ok ())) hP = .ok (resL, hL) ∧
          ParserEnv ctx hL ∧ CompSawZero ctx hL ∧
          (∀ errs1 errs', C.Space.get hP ctx.rerr = some errs1 → 0 < errs1.size →
            C.Space.get hL ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs1[0]!.numWarnings) ∧
          (∀ mrks1 mrks', C.Space.get hP ctx.rmrk = some mrks1 → 0 < mrks1.size →
            C.Space.get hL ctx.rmrk = some mrks' → 0 < mrks'.size → mrks' = mrks1) ∧
          (∀ srcs1 srcs', C.Space.get hP ctx.rs = some srcs1 → 0 < srcs1.size →
            C.Space.get hL ctx.rs = some srcs' → 0 < srcs'.size → srcs' = srcs1) ∧
          (∀ masters1 masters', C.Space.get hP ctx.rmas = some masters1 → 0 < masters1.size →
            C.Space.get hL ctx.rmas = some masters' → 0 < masters'.size → masters' = masters1) ∧
          (∀ dcs1 dcs', C.Space.get hP (C.DecompRef.decomp ctx.bdc) = some dcs1 → 0 < dcs1.size →
            C.Space.get hL (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
            MultiScanReady hL dcs'[0]! ∧
            dcs'[0]!.inputScanNumber = dcs1[0]!.inputScanNumber ∧
            dcs'[0]!.unreadMarker = dcs1[0]!.unreadMarker) ∧
          (∀ ics1 ics', C.Space.get hP ctx.ric = some ics1 → 0 < ics1.size →
            C.Space.get hL ctx.ric = some ics' → 0 < ics'.size →
            ics'[0]!.eoiReached = ics1[0]!.eoiReached ∧
            ics'[0]!.inheaders = ics1[0]!.inheaders ∧
            ics'[0]!.hasMultipleScans = ics1[0]!.hasMultipleScans ∧
            match resL with
            | .ok () => ics'[0]!.consumeInput = C.FnPtr.fn "dummy_consume_data"
            | .errExit _ => ics'[0]!.consumeInput = ics1[0]!.consumeInput) := by
      have finishStep :
          ∀ hX, ParserEnv ctx hX → CompSawZero ctx hX →
            (∀ dcsX, C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
              MultiScanReady hX dcsX[0]!) →
            ∃ h',
              C.run (do
                let dc1 ← C.Ptr.load (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)
                if (dc1.entropyStartPass != C.FnPtr.fn "noop") = true then do
                  let _ : Unit ← C.ub "unsupported entropy start_pass"
                  if (dc1.coefStartInputPass != C.FnPtr.fn "noop") = true then do
                    let _ : Unit ← C.ub "unsupported coef start_input_pass"
                    let ic ← C.Ptr.load dc1.inputctl
                    C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                    pure (C.JpegRes.ok ())
                  else do
                    let ic ← C.Ptr.load dc1.inputctl
                    C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                    pure (C.JpegRes.ok ())
                else if (dc1.coefStartInputPass != C.FnPtr.fn "noop") = true then do
                  let _ : Unit ← C.ub "unsupported coef start_input_pass"
                  let ic ← C.Ptr.load dc1.inputctl
                  C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                  pure (C.JpegRes.ok ())
                else do
                  let ic ← C.Ptr.load dc1.inputctl
                  C.Ptr.store dc1.inputctl { ic with consumeInput := dc1.coefConsumeData }
                  pure (C.JpegRes.ok ())) hX = .ok (.ok (), h') ∧
              ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
              h'.errMgrs = hX.errMgrs ∧ h'.markers = hX.markers ∧ h'.srcs = hX.srcs ∧
              h'.masters = hX.masters ∧ h'.decomps = hX.decomps ∧
              (∀ dcs', C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
                MultiScanReady h' dcs'[0]!) ∧
              (∀ icsX ics', C.Space.get hX ctx.ric = some icsX → 0 < icsX.size →
                C.Space.get h' ctx.ric = some ics' → 0 < ics'.size →
                ics'[0]!.eoiReached = icsX[0]!.eoiReached ∧
                ics'[0]!.inheaders = icsX[0]!.inheaders ∧
                ics'[0]!.hasMultipleScans = icsX[0]!.hasMultipleScans ∧
                ics'[0]!.consumeInput = C.FnPtr.fn "dummy_consume_data") := by
        intro hX hpX hsawX hmX
        obtain ⟨dcsX, hgdcX, hszdcX, _, _, _, hicX, _⟩ := parserEnv_get_dc hpX
        obtain ⟨icsX, hgicX, hszicX, hrstX, _⟩ := parserEnv_get_ic hpX
        have hmX0 := hmX dcsX hgdcX hszdcX
        have hldcX := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcX hszdcX
        have hlicX := ptr_load_ok (r := ctx.ric) (off := 0) hgicX hszicX
        have hentF : (dcsX[0]!.entropyStartPass != C.FnPtr.fn "noop") = false := by simp [hmX0.1]
        have hcoefF : (dcsX[0]!.coefStartInputPass != C.FnPtr.fn "noop") = false := by simp [hmX0.2.1]
        have hcdEq : dcsX[0]!.coefConsumeData = C.FnPtr.fn "dummy_consume_data" := hmX0.2.2.1
        let ic' : C.JpegInputController := { (icsX[0]!) with consumeInput := dcsX[0]!.coefConsumeData }
        have hroIcX : C.Space.ro hX ctx.ric = false := rfl
        have hstIcX := ptr_store_ok (r := ctx.ric) (off := 0) (v := ic') hgicX hroIcX hszicX
        let h' := C.Space.put hX ctx.ric (icsX.set! 0 ic')
        have hp' : ParserEnv ctx h' := parserEnv_put_ic hpX hgicX hszicX hrstX (Or.inr hcdEq)
        have hsaw' : CompSawZero ctx h' := compSawZero_put_ic hsawX
        refine ⟨h', ?_, hp', hsaw', rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · rw [C.run_bind, hldcX]; dsimp only
          simp only [hentF, hcoefF, Bool.false_eq_true, ↓reduceIte]
          rw [C.run_bind, hicX, hlicX]; dsimp only
          rw [C.run_bind, hstIcX]; rfl
        · intro dcs' hgdc' hszdc'
          have hdeq : dcs' = dcsX := Option.some.inj (by
            simp only [h', C.Space.get, C.Space.put] at hgdc' hgdcX
            exact hgdc'.symm.trans hgdcX)
          rw [hdeq]
          exact multiScanReady_put_ic hmX0
        · intro iX i' hiX _ hi' _
          have hiXeq : iX = icsX := Option.some.inj (hiX.symm.trans hgicX)
          have hget' : C.Space.get h' ctx.ric = some (icsX.set! 0 ic') := by simp [h', C.Space.get, C.Space.put]
          have hi'eq : i' = icsX.set! 0 ic' := Option.some.inj (hi'.symm.trans hget')
          rw [hiXeq, hi'eq, array_set_bang_self icsX hszicX ic']
          exact ⟨rfl, rfl, rfl, hcdEq⟩
      by_cases hll : (mastersP[0]!.lossless == 0) = true
      · obtain ⟨resL, hL, hrunL, hpL, hsawL, hnwL, hmrkL, hsrcL, hmasL, hicL, hmultL⟩ :=
          latch_quant_tables_ok hpP hsawP (fun dcs hg hsz => (hmultP dcs0 dcs hgdc0 hszdc0 hg hsz).1)
        rcases resL with ⟨⟩ | codeL
        · obtain ⟨h', hrunF, hp', hsaw', herr', hmrk', hsrc', hmas', hdeq', hmult', hic'⟩ :=
            finishStep hL hpL hsawL (fun dcs hg hsz => by
              obtain ⟨dcsP', hgdcP', hszdcP', _⟩ := parserEnv_get_dc hpP
              exact (hmultL dcsP' dcs hgdcP' hszdcP' hg hsz).1)
          obtain ⟨dcsL, hgdcL, hszdcL, _⟩ := parserEnv_get_dc hpL
          obtain ⟨icsL, hgicL, hszicL, _, _⟩ := parserEnv_get_ic hpL
          refine ⟨.ok (), h', ?_, hp', hsaw', ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [hll, ↓reduceIte]
            rw [C.run_bind, hrunL]; dsimp only
            exact hrunF
          · intro e1 e' he1 hsze1 he'
            simp only [C.Space.get] at he'; rw [herr'] at he'
            exact hnwL e1 e' he1 hsze1 he'
          · intro m1 m' hm1 hszm1 hm' hszm'
            simp only [C.Space.get] at hm'; rw [hmrk'] at hm'
            exact hmrkL m1 m' hm1 hszm1 hm' hszm'
          · intro s1 s' hs1 hszs1 hs' hszs'
            simp only [C.Space.get] at hs'; rw [hsrc'] at hs'
            exact hsrcL s1 s' hs1 hszs1 hs' hszs'
          · intro a1 a' ha1 hsza1 ha' hsza'
            simp only [C.Space.get] at ha'; rw [hmas'] at ha'
            exact hmasL a1 a' ha1 hsza1 ha' hsza'
          · intro d1 d' hd1 hszd1 hd' hszd'
            have hLget : C.Space.get hL (C.DecompRef.decomp ctx.bdc) = some d' := by
              simp only [C.Space.get] at hd' ⊢; rw [← hdeq']; exact hd'
            have hL_flds := hmultL d1 d' hd1 hszd1 hLget hszd'
            exact ⟨hmult' d' hd' hszd', hL_flds.2.1, hL_flds.2.2.1⟩
          · intro i1 i' hi1 hszi1 hi' hszi'
            have hicLeq : icsL = i1 := hicL i1 icsL hi1 hszi1 hgicL hszicL
            have hfin := hic' icsL i' hgicL hszicL hi' hszi'
            rw [hicLeq] at hfin; exact hfin
        · refine ⟨.errExit codeL, hL, ?_, hpL, hsawL, hnwL, hmrkL, hsrcL, hmasL, ?_, ?_⟩
          · simp only [hll, ↓reduceIte]
            rw [C.run_bind, hrunL]; rfl
          · intro d1 d' hd1 hszd1 hd' hszd'
            have hL_flds := hmultL d1 d' hd1 hszd1 hd' hszd'
            exact ⟨hL_flds.1, hL_flds.2.1, hL_flds.2.2.1⟩
          · intro i1 i' hi1 hszi1 hi' hszi'
            rw [hicL i1 i' hi1 hszi1 hi' hszi']
            exact ⟨rfl, rfl, rfl, rfl⟩
      · have hllF : (mastersP[0]!.lossless == 0) = false := Bool.eq_false_iff.mpr hll
        obtain ⟨h', hrunF, hp', hsaw', herr', hmrk', hsrc', hmas', hdeq', hmult', hic'⟩ :=
          finishStep hP hpP hsawP (fun dcs hg hsz => (hmultP dcs0 dcs hgdc0 hszdc0 hg hsz).1)
        refine ⟨.ok (), h', ?_, hp', hsaw', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hllF, Bool.false_eq_true, ↓reduceIte]
          exact hrunF
        · intro e1 e' he1 hsze1 he'
          simp only [C.Space.get] at he'; rw [herr'] at he'
          rw [Option.some.inj (he'.symm.trans he1)]
          exact ⟨hsze1, rfl⟩
        · intro m1 m' hm1 _ hm' _
          simp only [C.Space.get] at hm'; rw [hmrk'] at hm'
          exact Option.some.inj (hm'.symm.trans hm1)
        · intro s1 s' hs1 _ hs' _
          simp only [C.Space.get] at hs'; rw [hsrc'] at hs'
          exact Option.some.inj (hs'.symm.trans hs1)
        · intro a1 a' ha1 _ ha' _
          simp only [C.Space.get] at ha'; rw [hmas'] at ha'
          exact Option.some.inj (ha'.symm.trans ha1)
        · intro d1 d' hd1 _ hd' hszd'
          have hdeq : d' = d1 := Option.some.inj (by
            simp only [C.Space.get] at hd' hd1; rw [hdeq'] at hd'; exact hd'.symm.trans hd1)
          rw [← hdeq]
          exact ⟨hmult' d' hd' hszd', rfl, rfl⟩
        · intro i1 i' hi1 hszi1 hi' hszi'
          exact hic' i1 i' hi1 hszi1 hi' hszi'
    obtain ⟨resL, hL, hrunL, hpL, hsawL, hnwL, hmrkL, hsrcL, hmasL, hdL, hicL⟩ := hrunPost
    obtain ⟨errsP, hgerrP, hszerrP, _⟩ := parserEnv_get_err hpP
    obtain ⟨mrksP, hgmrkP, hszmrkP, _⟩ := parserEnv_get_mrk hpP
    obtain ⟨srcsP, hgsrcP, hszsrcP, _⟩ := parserEnv_get_src hpP
    obtain ⟨icsP, hgicP, hszicP, _⟩ := parserEnv_get_ic hpP
    refine ⟨resL, hL, ?_, hpL, hsawL, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold Mozjpeg.Jdinput.start_input_pass
      rw [C.run_bind, hrunP]; dsimp only
      rw [C.run_bind, hldcP]; dsimp only
      rw [C.run_bind, hmasP_ref, hlmstP]; dsimp only
      exact hrunL
    · intro e0 e' he0 _ he'
      rw [Option.some.inj (he0.symm.trans hgerr0)]
      have hwP := hnwP errs0 errsP hgerr0 hszerr0 hgerrP
      have hwL := hnwL errsP e' hgerrP hszerrP he'
      exact ⟨hwL.1, hwL.2.trans hwP.2⟩
    · intro m0 m' hm0 _ hm' hszm'
      rw [Option.some.inj (hm0.symm.trans hgmrk0)]
      exact (hmrkL mrksP m' hgmrkP hszmrkP hm' hszm').trans (hmrkP mrks0 mrksP hgmrk0 hszmrk0 hgmrkP hszmrkP)
    · intro s0 s' hs0 _ hs' hszs'
      rw [Option.some.inj (hs0.symm.trans hgsrc0)]
      exact (hsrcL srcsP s' hgsrcP hszsrcP hs' hszs').trans (hsrcP srcs0 srcsP hgsrc0 hszsrc0 hgsrcP hszsrcP)
    · intro a0 a' ha0 _ ha' hsza'
      rw [Option.some.inj (ha0.symm.trans hgmas0)]
      exact (hmasL mastersP a' hgmasP hszmasP ha' hsza').trans hmasEqP
    · intro d0 d' hd0 _ hd' hszd'
      rw [Option.some.inj (hd0.symm.trans hgdc0)]
      have hfL := hdL dcsP d' hgdcP hszdcP hd' hszd'
      exact ⟨hfL.1, hfL.2.1.trans hdP_flds.2.1, hfL.2.2.trans hdP_flds.2.2⟩
    · intro i0 i' hi0 _ hi' hszi'
      rw [Option.some.inj (hi0.symm.trans hgic0)]
      have hiPL := hicL icsP i' hgicP hszicP hi' hszi'
      have hiP0 := hicP ics0 icsP hgic0 hszic0 hgicP hszicP
      rw [hiP0] at hiPL
      exact hiPL
  · refine ⟨.errExit code, hP, ?_, hpP, hsawP, hnwP, hmrkP, hsrcP, hmasP, ?_, ?_⟩
    · unfold Mozjpeg.Jdinput.start_input_pass
      rw [C.run_bind, hrunP]; rfl
    · intro d0 d' hd0 hszd0 hd' hszd'
      exact hmultP d0 d' hd0 hszd0 hd' hszd'
    · intro i0 i' hi0 hszi0 hi' hszi'
      rw [hicP i0 i' hi0 hszi0 hi' hszi']
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem finish_input_pass_ok {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h) :
    ∃ h', C.run (Mozjpeg.Jdinput.finish_input_pass (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.srcs = h.srcs ∧
      h'.masters = h.masters ∧ h'.errMgrs = h.errMgrs ∧ h'.comps = h.comps ∧
      (∀ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
        MultiScanReady h dcs[0]! → MultiScanReady h' dcs[0]!) ∧
      (∀ ics0 ics', C.Space.get h ctx.ric = some ics0 → 0 < ics0.size →
        C.Space.get h' ctx.ric = some ics' → 0 < ics'.size →
        ics'[0]!.consumeInput = C.FnPtr.fn "consume_markers" ∧
        ics'[0]!.eoiReached = ics0[0]!.eoiReached ∧
        ics'[0]!.inheaders = ics0[0]!.inheaders ∧
        ics'[0]!.hasMultipleScans = ics0[0]!.hasMultipleScans ∧
        ics'[0]!.resetInputController = ics0[0]!.resetInputController) := by
  obtain ⟨dcs0, hgdc0, hszdc0, _, _, _, hic0, _⟩ := parserEnv_get_dc hp
  obtain ⟨ics0, hgic0, hszic0, hrst0, _⟩ := parserEnv_get_ic hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlic0 := ptr_load_ok (r := ctx.ric) (off := 0) hgic0 hszic0
  let ic' : C.JpegInputController := { (ics0[0]!) with consumeInput := C.FnPtr.fn "consume_markers" }
  have hroIc0 : C.Space.ro h ctx.ric = false := rfl
  have hstIc0 := ptr_store_ok (r := ctx.ric) (off := 0) (v := ic') hgic0 hroIc0 hszic0
  let h' := C.Space.put h ctx.ric (ics0.set! 0 ic')
  have hp' : ParserEnv ctx h' := parserEnv_put_ic hp hgic0 hszic0 hrst0 (Or.inl rfl)
  have hsaw' : CompSawZero ctx h' := compSawZero_put_ic hsaw
  refine ⟨h', ?_, hp', hsaw', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · unfold Mozjpeg.Jdinput.finish_input_pass
    rw [C.run_bind, hldc0]; dsimp only
    rw [C.run_bind, hic0, hlic0]; dsimp only
    rw [hstIc0]
  · intro _ _ _ hm; exact multiScanReady_put_ic hm
  · intro i0 i' hi0 _ hi' _
    have hi0eq : i0 = ics0 := Option.some.inj (hi0.symm.trans hgic0)
    have hget' : C.Space.get h' ctx.ric = some (ics0.set! 0 ic') := by simp [h', C.Space.get, C.Space.put]
    have hi'eq : i' = ics0.set! 0 ic' := Option.some.inj (hi'.symm.trans hget')
    rw [hi0eq, hi'eq, array_set_bang_self ics0 hszic0 ic']
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### `read_markers` preserves `inputctls` -/

private def PreservesIC {α : Type} (m : C.M α) : Prop :=
  ∀ h a h', C.run m h = .ok (a, h') → h'.inputctls = h.inputctls

private theorem pic_pure {α : Type} (a : α) : PreservesIC (pure a : C.M α) :=
  fun _ _ _ h => by cases h; rfl

private theorem pic_bind {α β : Type} {m : C.M α} {f : α → C.M β}
    (hm : PreservesIC m) (hf : ∀ a, PreservesIC (f a)) : PreservesIC (m >>= f) :=
  fun h b h' hr => by
    rw [C.run_bind] at hr
    cases h1 : C.run m h with
    | error e => simp [h1] at hr
    | ok p => simp [h1] at hr; exact (hf p.1 p.2 b h' hr).trans (hm h p.1 p.2 h1)

private theorem pic_ite {α : Type} (c : Prop) [Decidable c] {t e : C.M α}
    (ht : c → PreservesIC t) (he : ¬ c → PreservesIC e) : PreservesIC (if c then t else e) := by
  by_cases hc : c <;> simp [hc]
  · exact ht hc
  · exact he hc

private theorem pic_load {R T : Type} [C.Space C.Heap R T] (p : C.Ptr R) : PreservesIC (C.Ptr.load p) :=
  fun h a h' hr => by
    cases p with
    | null => simp [C.run, C.Ptr.load] at hr
    | ref r off =>
      cases hg : C.Space.get h r with
      | none => simp [C.run, C.Ptr.load, hg] at hr
      | some xs =>
        by_cases hlt : off < xs.size <;> simp [C.run, C.Ptr.load, hg, hlt] at hr
        · rcases hr with ⟨_, rfl⟩; rfl

private theorem pic_ub {α : Type} (msg : String) : PreservesIC (C.ub msg : C.M α) :=
  fun h a h' hr => by simp [C.run, C.ub] at hr

private theorem pic_allocComp (n : Nat) : PreservesIC (C.allocComps n) := fun h a h' hr => by
  simp only [C.run, C.allocComps] at hr; split at hr <;> cases hr <;> rfl
private theorem pic_allocQuant : PreservesIC C.allocQuant := fun h a h' hr => by
  simp only [C.run, C.allocQuant] at hr; split at hr <;> cases hr <;> rfl
private theorem pic_allocHuff : PreservesIC C.allocHuff := fun h a h' hr => by
  simp only [C.run, C.allocHuff] at hr; split at hr <;> cases hr <;> rfl
private theorem pic_getLargeSM (n : Nat) : PreservesIC (Mozjpeg.Jmemnobs.jpeg_get_large_saved_marker n) :=
  fun h a h' hr => by
    unfold Mozjpeg.Jmemnobs.jpeg_get_large_saved_marker C.allocSavedMarkerData at hr
    simp only [C.run] at hr
    split at hr <;> cases hr <;> rfl

private theorem pic_store_of_put {R T : Type} [inst : C.Space C.Heap R T]
    (hmod : ∀ (h : C.Heap) (r : R) (f : Array T → Array T), (C.Space.modify h r f).inputctls = h.inputctls)
    (p : C.Ptr R) (v : T) : PreservesIC (C.Ptr.store p v) :=
  fun h a h' hr => by
    cases p with
    | null => simp [C.run, C.Ptr.store] at hr
    | ref r off =>
      cases hg : C.Space.get h r with
      | none => simp [C.run, C.Ptr.store, hg] at hr
      | some xs =>
        by_cases hro : C.Space.ro h r <;> by_cases hlt : off < xs.size <;>
          simp [C.run, C.Ptr.store, hg, hro, hlt] at hr
        · rcases hr with ⟨rfl, rfl⟩; exact hmod h r (fun a => a.setIfInBounds off v)

private theorem pic_store_dc (p : C.DecompPtr) (v : C.JpegDecompressStruct) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_err (p : C.ErrPtr) (v : C.JpegErrorMgr) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_mem (p : C.MemPtr) (v : C.JpegMemMgr) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_mas (p : C.MasterPtr) (v : C.JpegDecompMaster) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_mrk (p : C.MarkerPtr) (v : C.JpegMarkerReader) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_src (p : C.SrcPtr) (v : C.JpegSourceMgr) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_comp (p : C.CompPtr) (v : C.JpegCompInfo) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_quant (p : C.QuantPtr) (v : C.JQuantTbl) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_huff (p : C.HuffPtr) (v : C.JHuffTbl) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_sm (p : C.SavedMarkerPtr) (v : C.JpegSavedMarker) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ _ _ => rfl) p v
private theorem pic_store_byte (p : C.BPtr) (v : UInt8) : PreservesIC (C.Ptr.store p v) :=
  pic_store_of_put (fun _ r f => by cases r <;> rfl) p v

private theorem pic_cwhile {σ : Type} (cond : σ → C.M (Bool × σ)) (body : σ → C.M σ)
    (hc : ∀ s, PreservesIC (cond s)) (hb : ∀ s, PreservesIC (body s)) (s : σ) :
    PreservesIC (C.cwhile cond body s) := fun _ _ _ hr =>
  (JdmarkerRead.cwhile_preserves cond body (fun a b => b.inputctls = a.inputctls)
    (fun hab hbc => hbc.trans hab) (fun s h _ _ h' hr => hc s h _ h' hr) hb hr)

private theorem pic_cdoWhile {σ : Type} (body : σ → C.M σ) (cond : σ → C.M (Bool × σ))
    (hb : ∀ s, PreservesIC (body s)) (hc : ∀ s, PreservesIC (cond s)) (s : σ) :
    PreservesIC (C.cdoWhile body cond s) := fun h s' h' hr =>
  (JdmarkerRead.cdoWhile_go_preserves body cond (fun a b => b.inputctls = a.inputctls)
    (fun hab hbc => hbc.trans hab) hb (fun s h _ _ h' hr => hc s h _ h' hr) C.fuel s h s' h' hr)

private theorem pic_forIn {α σ : Type} (l : List α) (body : α → σ → C.M (ForInStep σ))
    (hb : ∀ a s, PreservesIC (body a s)) : ∀ s, PreservesIC (forIn l s body) := by
  induction l with
  | nil => intro s; simp [forIn]; exact pic_pure s
  | cons a l ih =>
    intro s h s' h' hr
    simp only [List.forIn_cons] at hr
    rw [C.run_bind] at hr
    cases h1 : C.run (body a s) h with
    | error e => simp [h1] at hr
    | ok p =>
      simp [h1] at hr
      rcases p with ⟨step, h1'⟩
      have h1eq : h1'.inputctls = h.inputctls := hb a s h step h1' h1
      cases step with
      | done s1 => cases hr; exact h1eq
      | yield s1 => exact (ih s1 h1' s' h' hr).trans h1eq

private theorem pic_ptrAdd {R T : Type} [C.Space C.Heap R T] (p : C.Ptr R) (k : Int) :
    PreservesIC (C.Ptr.add p k) :=
  fun h a h' hr => by
    cases p with
    | null => simp [C.run, C.Ptr.add] at hr
    | ref r off =>
      cases hg : C.Space.get h r with
      | none => simp [C.run, C.Ptr.add, hg] at hr
      | some xs =>
        simp only [C.run, C.Ptr.add, hg] at hr
        split at hr <;> cases hr <;> rfl

private theorem pic_checkI32 (x : Int) (w : String) : PreservesIC (C.checkI32 x w) :=
  fun h a h' hr => by unfold C.checkI32 at hr; simp only [C.run] at hr; split at hr <;> cases hr <;> rfl
private theorem pic_checkI64 (x : Int) (w : String) : PreservesIC (C.checkI64 x w) :=
  fun h a h' hr => by unfold C.checkI64 at hr; simp only [C.run] at hr; split at hr <;> cases hr <;> rfl
private theorem pic_i64Div (a b : Int64) : PreservesIC (C.i64Div a b) := by
  unfold C.i64Div
  exact pic_ite _ (fun _ => pic_ub _) (fun _ => pic_ite _ (fun _ => pic_ub _) (fun _ => pic_checkI64 _ _))
private theorem pic_i32Add (a b : Int32) : PreservesIC (C.i32Add a b) := pic_checkI32 _ _
private theorem pic_i32Sub (a b : Int32) : PreservesIC (C.i32Sub a b) := pic_checkI32 _ _
private theorem pic_i32Mul (a b : Int32) : PreservesIC (C.i32Mul a b) := pic_checkI32 _ _
private theorem pic_i64Add (a b : Int64) : PreservesIC (C.i64Add a b) := pic_checkI64 _ _
private theorem pic_i64Sub (a b : Int64) : PreservesIC (C.i64Sub a b) := pic_checkI64 _ _
private theorem pic_jdiv_round_up (a b : Int64) : PreservesIC (Mozjpeg.Jutils.jdiv_round_up a b) := by
  unfold Mozjpeg.Jutils.jdiv_round_up
  exact pic_bind (pic_i64Add _ _) (fun _ => pic_bind (pic_i64Sub _ _) (fun _ => pic_i64Div _ _))

private theorem pic_emitMessage (ep : C.ErrPtr) (lvl : Int32) :
    PreservesIC (Mozjpeg.JerrorH.emitMessage ep lvl) := by
  unfold Mozjpeg.JerrorH.emitMessage
  refine pic_bind (pic_load ep) (fun _ => pic_ite _ (fun _ => pic_bind (pic_i64Add _ _) (fun _ => pic_store_err _ _)) (fun _ => pic_pure _))

private theorem pic_errorExit (ep : C.ErrPtr) (code : Int32) :
    PreservesIC (Mozjpeg.JerrorH.errexit ep code) := by
  unfold Mozjpeg.JerrorH.errexit; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_pure _))
private theorem pic_errexit1 (ep : C.ErrPtr) (code p1 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.errexit1 ep code p1) := by
  unfold Mozjpeg.JerrorH.errexit1; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_pure _))
private theorem pic_errexit2 (ep : C.ErrPtr) (code p1 p2 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.errexit2 ep code p1 p2) := by
  unfold Mozjpeg.JerrorH.errexit2; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_pure _))
private theorem pic_warnms (ep : C.ErrPtr) (code : Int32) :
    PreservesIC (Mozjpeg.JerrorH.warnms ep code) := by
  unfold Mozjpeg.JerrorH.warnms; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))
private theorem pic_warnms2 (ep : C.ErrPtr) (code p1 p2 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.warnms2 ep code p1 p2) := by
  unfold Mozjpeg.JerrorH.warnms2; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))
private theorem pic_tracems (ep : C.ErrPtr) (lvl code : Int32) :
    PreservesIC (Mozjpeg.JerrorH.tracems ep lvl code) := by
  unfold Mozjpeg.JerrorH.tracems; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))
private theorem pic_tracems1 (ep : C.ErrPtr) (lvl code p1 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.tracems1 ep lvl code p1) := by
  unfold Mozjpeg.JerrorH.tracems1; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))
private theorem pic_tracems2 (ep : C.ErrPtr) (lvl code p1 p2 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.tracems2 ep lvl code p1 p2) := by
  unfold Mozjpeg.JerrorH.tracems2; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))
private theorem pic_tracems3 (ep : C.ErrPtr) (lvl code p1 p2 p3 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.tracems3 ep lvl code p1 p2 p3) := by
  unfold Mozjpeg.JerrorH.tracems3; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))
private theorem pic_tracems4 (ep : C.ErrPtr) (lvl code p1 p2 p3 p4 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.tracems4 ep lvl code p1 p2 p3 p4) := by
  unfold Mozjpeg.JerrorH.tracems4; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))
private theorem pic_tracems5 (ep : C.ErrPtr) (lvl code p1 p2 p3 p4 p5 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.tracems5 ep lvl code p1 p2 p3 p4 p5) := by
  unfold Mozjpeg.JerrorH.tracems5; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))
private theorem pic_tracems8 (ep : C.ErrPtr) (lvl code p1 p2 p3 p4 p5 p6 p7 p8 : Int32) :
    PreservesIC (Mozjpeg.JerrorH.tracems8 ep lvl code p1 p2 p3 p4 p5 p6 p7 p8) := by
  unfold Mozjpeg.JerrorH.tracems8; refine pic_bind (pic_load ep) (fun _ => pic_bind (pic_store_err _ _) (fun _ => pic_emitMessage _ _))

private theorem pic_oom (cinfo : C.DecompPtr) (which : Int32) : PreservesIC (Mozjpeg.Jmemmgr.out_of_memory cinfo which) := by
  unfold Mozjpeg.Jmemmgr.out_of_memory; exact pic_bind (pic_load cinfo) (fun _ => pic_errexit1 _ _ _)

private theorem pic_allocSlopRetry {R : Type} [DecidableEq R] (cinfo : C.DecompPtr) (allocFn : C.M (C.Ptr R))
    (ha : PreservesIC allocFn) (k : Nat) (slop : UInt64) :
    PreservesIC (Mozjpeg.Jmemmgr.allocSlopRetry cinfo allocFn k slop) := by
  induction k generalizing slop with
  | zero =>
    unfold Mozjpeg.Jmemmgr.allocSlopRetry
    exact pic_bind (pic_oom cinfo 2) (fun _ => pic_pure _)
  | succ k ih =>
    unfold Mozjpeg.Jmemmgr.allocSlopRetry
    exact pic_bind ha (fun p => pic_ite _ (fun _ => pic_pure _) (fun _ => pic_ite _ (fun _ => pic_bind (pic_oom _ _) (fun _ => pic_pure _)) (fun _ => ih _)))

private theorem pic_allocSmallCore {R : Type} [DecidableEq R] (cinfo : C.DecompPtr) (pool_id : Int32) (sizeofobject : UInt64)
    (allocFn : C.M (C.Ptr R)) (ha : PreservesIC allocFn) (recFn : C.PoolAllocs → C.Ptr R → C.PoolAllocs) :
    PreservesIC (Mozjpeg.Jmemmgr.allocSmallCore cinfo pool_id sizeofobject allocFn recFn) := by
  unfold Mozjpeg.Jmemmgr.allocSmallCore
  refine pic_bind (pic_load cinfo) (fun _ => pic_ite _ (fun _ => pic_bind (pic_oom _ _) (fun _ => pic_pure _)) (fun _ =>
    pic_ite _ (fun _ => pic_bind (pic_oom _ _) (fun _ => pic_pure _)) (fun _ =>
      pic_ite _ (fun _ => pic_bind (pic_errexit1 _ _ _) (fun _ => pic_pure _)) (fun _ =>
        pic_bind (pic_load _) (fun _ => pic_bind (pic_allocSlopRetry cinfo allocFn ha 16 _) (fun r => by
          cases r <;> dsimp only
          · exact pic_bind (pic_load cinfo) (fun _ => pic_bind (pic_load _) (fun _ => pic_bind (pic_store_mem _ _) (fun _ => pic_pure _)))
          · exact pic_pure _))))))

private theorem pic_alloc_small_comps (cinfo : C.DecompPtr) (pid : Int32) (n : Nat) (sz : UInt64) :
    PreservesIC (Mozjpeg.Jmemmgr.alloc_small_comps cinfo pid n sz) :=
  pic_allocSmallCore cinfo pid sz (C.allocComps n) (pic_allocComp n) _
private theorem pic_alloc_small_quant (cinfo : C.DecompPtr) (pid : Int32) (sz : UInt64) :
    PreservesIC (Mozjpeg.Jmemmgr.alloc_small_quant cinfo pid sz) :=
  pic_allocSmallCore cinfo pid sz C.allocQuant pic_allocQuant _
private theorem pic_alloc_quant (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jcomapi.jpeg_alloc_quant_table cinfo) := by
  unfold Mozjpeg.Jcomapi.jpeg_alloc_quant_table
  refine pic_bind (pic_alloc_small_quant _ _ _) (fun r => by
    cases r <;> dsimp only
    · exact pic_bind (pic_load _) (fun _ => pic_bind (pic_store_quant _ _) (fun _ => pic_pure _))
    · exact pic_pure _)
private theorem pic_alloc_small_huff (cinfo : C.DecompPtr) (pid : Int32) (sz : UInt64) :
    PreservesIC (Mozjpeg.Jmemmgr.alloc_small_huff cinfo pid sz) :=
  pic_allocSmallCore cinfo pid sz C.allocHuff pic_allocHuff _
private theorem pic_alloc_huff (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jcomapi.jpeg_alloc_huff_table cinfo) := by
  unfold Mozjpeg.Jcomapi.jpeg_alloc_huff_table
  refine pic_bind (pic_alloc_small_huff _ _ _) (fun r => by
    cases r <;> dsimp only
    · exact pic_bind (pic_load _) (fun _ => pic_bind (pic_store_huff _ _) (fun _ => pic_pure _))
    · exact pic_pure _)
private theorem pic_alloc_large_sm (cinfo : C.DecompPtr) (pid : Int32) (lim : Nat) :
    PreservesIC (Mozjpeg.Jmemmgr.alloc_large_saved_marker cinfo pid lim) := by
  unfold Mozjpeg.Jmemmgr.alloc_large_saved_marker
  refine pic_bind (pic_load cinfo) (fun _ => pic_ite _ (fun _ => pic_bind (pic_oom _ _) (fun _ => pic_pure _)) (fun _ =>
    pic_ite _ (fun _ => pic_bind (pic_oom _ _) (fun _ => pic_pure _)) (fun _ =>
      pic_ite _ (fun _ => pic_bind (pic_errexit1 _ _ _) (fun _ => pic_pure _)) (fun _ =>
        pic_bind (pic_getLargeSM lim) (fun (sm, _) => by
          dsimp only; refine pic_ite _ (fun _ => pic_bind (pic_oom _ _) (fun _ => pic_pure _)) (fun _ =>
            pic_bind (pic_load cinfo) (fun _ => pic_bind (pic_load _) (fun _ => pic_bind (pic_store_mem _ _) (fun _ => pic_pure _)))))))))

local syntax "solve_pic_step" : tactic
local macro_rules
  | `(tactic| solve_pic_step) => `(tactic|
      (try dsimp only
       first
       | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
       | ((with_reducible apply pic_ite) <;> intro _)
       | ((with_reducible apply pic_cwhile) <;> intro _)
       | ((with_reducible apply pic_cdoWhile) <;> intro _)
       | (with_reducible apply pic_forIn; intro _ _)
       | with_reducible apply pic_pure
       | with_reducible apply pic_load
       | with_reducible apply pic_ub
       | with_reducible apply pic_store_dc
       | with_reducible apply pic_store_err
       | with_reducible apply pic_store_mem
       | with_reducible apply pic_store_mas
       | with_reducible apply pic_store_mrk
       | with_reducible apply pic_store_src
       | with_reducible apply pic_store_comp
       | with_reducible apply pic_store_quant
       | with_reducible apply pic_store_huff
       | with_reducible apply pic_store_sm
       | with_reducible apply pic_store_byte
       | with_reducible apply pic_ptrAdd
       | with_reducible apply pic_i32Add
       | with_reducible apply pic_i32Sub
       | with_reducible apply pic_i32Mul
       | with_reducible apply pic_i64Add
       | with_reducible apply pic_i64Sub
       | with_reducible apply pic_i64Div
       | with_reducible apply pic_jdiv_round_up
       | with_reducible apply pic_errorExit
       | with_reducible apply pic_errexit1
       | with_reducible apply pic_errexit2
       | with_reducible apply pic_warnms
       | with_reducible apply pic_warnms2
       | with_reducible apply pic_tracems
        | with_reducible apply pic_tracems1
        | with_reducible apply pic_tracems2
        | with_reducible apply pic_tracems3
        | with_reducible apply pic_tracems4
        | with_reducible apply pic_tracems5
        | with_reducible apply pic_tracems8
       | with_reducible apply pic_alloc_small_comps
       | with_reducible apply pic_alloc_quant
       | with_reducible apply pic_alloc_huff
       | with_reducible apply pic_alloc_large_sm
       | split))

private theorem pic_fill_mem (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdatasrc.fill_mem_input_buffer cinfo) := by
  unfold Mozjpeg.Jdatasrc.fill_mem_input_buffer; repeat' solve_pic_step

private theorem pic_skip_data (cinfo : C.DecompPtr) (n : Int64) : PreservesIC (Mozjpeg.Jdatasrc.skip_input_data cinfo n) := by
  unfold Mozjpeg.Jdatasrc.skip_input_data
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_fill_mem
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | ((with_reducible apply pic_cwhile) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_ub
    | with_reducible apply pic_store_src
    | with_reducible apply pic_ptrAdd)

private theorem pic_skipDispatch (cinfo : C.DecompPtr) (n : Int64) : PreservesIC (Mozjpeg.Jdmarker.skipInputDataDispatch cinfo n) := by
  unfold Mozjpeg.Jdmarker.skipInputDataDispatch
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_skip_data
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_ub)

private theorem pic_inputSync (cinfo : C.DecompPtr) (nib : C.BPtr) (bib : UInt64) : PreservesIC (Mozjpeg.Jdmarker.inputSync cinfo nib bib) := by
  unfold Mozjpeg.Jdmarker.inputSync; repeat' solve_pic_step

private theorem pic_makeByteAvail (cinfo : C.DecompPtr) (nib : C.BPtr) (bib : UInt64) : PreservesIC (Mozjpeg.Jdmarker.makeByteAvail cinfo nib bib) := by
  unfold Mozjpeg.Jdmarker.makeByteAvail
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_fill_mem
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_ub
    | with_reducible apply pic_store_src)

private theorem pic_inputByte (cinfo : C.DecompPtr) (nib : C.BPtr) (bib : UInt64) : PreservesIC (Mozjpeg.Jdmarker.inputByte cinfo nib bib) := by
  unfold Mozjpeg.Jdmarker.inputByte
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_makeByteAvail
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_ptrAdd
    | split)

private theorem pic_input2Bytes (cinfo : C.DecompPtr) (nib : C.BPtr) (bib : UInt64) : PreservesIC (Mozjpeg.Jdmarker.input2Bytes cinfo nib bib) := by
  unfold Mozjpeg.Jdmarker.input2Bytes
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_inputByte
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | with_reducible apply pic_pure
    | split)

private theorem pic_first_marker (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.first_marker cinfo) := by
  unfold Mozjpeg.Jdmarker.first_marker
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_inputSync
    | with_reducible apply pic_inputByte
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_store_dc
    | with_reducible apply pic_warnms2
    | with_reducible apply pic_errorExit
    | with_reducible apply pic_errexit2
    | split)

private theorem pic_next_marker (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.next_marker cinfo) := by
  unfold Mozjpeg.Jdmarker.next_marker
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_inputSync
    | with_reducible apply pic_inputByte
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | ((with_reducible apply pic_cwhile) <;> intro _)
    | ((with_reducible apply pic_cdoWhile) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_store_dc
    | with_reducible apply pic_store_mrk
    | with_reducible apply pic_store_src
    | with_reducible apply pic_warnms
    | with_reducible apply pic_warnms2
    | with_reducible apply pic_tracems2
    | with_reducible apply pic_errorExit
    | with_reducible apply pic_i32Add
    | split)

private theorem pic_get_soi (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.get_soi cinfo) := by
  unfold Mozjpeg.Jdmarker.get_soi; repeat' solve_pic_step

private theorem pic_get_dri (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.get_dri cinfo) := by
  unfold Mozjpeg.Jdmarker.get_dri
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_inputSync
    | with_reducible apply pic_input2Bytes
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_store_dc
    | with_reducible apply pic_tracems1
    | with_reducible apply pic_errorExit
    | with_reducible apply pic_errexit2
    | split)

private theorem pic_skip_variable (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.skip_variable cinfo) := by
  unfold Mozjpeg.Jdmarker.skip_variable
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_skipDispatch
    | with_reducible apply pic_inputSync
    | with_reducible apply pic_input2Bytes
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_tracems2
    | with_reducible apply pic_i64Sub
    | split)

local syntax "solve_pic" : tactic
local macro_rules
  | `(tactic| solve_pic) => `(tactic|
      repeat' (
        try dsimp only
        first
        | with_reducible apply pic_skipDispatch
        | with_reducible apply pic_inputSync
        | with_reducible apply pic_makeByteAvail
        | with_reducible apply pic_inputByte
        | with_reducible apply pic_input2Bytes
        | with_reducible apply pic_first_marker
        | with_reducible apply pic_next_marker
        | with_reducible apply pic_get_soi
        | with_reducible apply pic_get_dri
        | with_reducible apply pic_skip_variable
        | solve_pic_step))

private theorem pic_get_sof (cinfo : C.DecompPtr) (is_prog is_lossless is_arith : Int32) :
    PreservesIC (Mozjpeg.Jdmarker.get_sof cinfo is_prog is_lossless is_arith) := by
  unfold Mozjpeg.Jdmarker.get_sof
  solve_pic

private theorem pic_get_sos (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.get_sos cinfo) := by
  unfold Mozjpeg.Jdmarker.get_sos
  solve_pic

private theorem pic_get_dac (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.get_dac cinfo) := by
  unfold Mozjpeg.Jdmarker.get_dac
  solve_pic

private theorem pic_get_dht (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.get_dht cinfo) := by
  unfold Mozjpeg.Jdmarker.get_dht
  solve_pic

private theorem pic_get_dqt (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.get_dqt cinfo) := by
  unfold Mozjpeg.Jdmarker.get_dqt
  solve_pic

private theorem pic_examine_app0 (cinfo : C.DecompPtr) (data : Array UInt8) (datalen : UInt32) (remaining : Int64) :
    PreservesIC (Mozjpeg.Jdmarker.examine_app0 cinfo data datalen remaining) := by
  unfold Mozjpeg.Jdmarker.examine_app0
  solve_pic

private theorem pic_examine_app14 (cinfo : C.DecompPtr) (data : Array UInt8) (datalen : UInt32) (remaining : Int64) :
    PreservesIC (Mozjpeg.Jdmarker.examine_app14 cinfo data datalen remaining) := by
  unfold Mozjpeg.Jdmarker.examine_app14
  solve_pic

private theorem pic_get_interesting_appn (cinfo : C.DecompPtr) :
    PreservesIC (Mozjpeg.Jdmarker.get_interesting_appn cinfo) := by
  unfold Mozjpeg.Jdmarker.get_interesting_appn
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_examine_app0
    | with_reducible apply pic_examine_app14
    | with_reducible apply pic_skipDispatch
    | with_reducible apply pic_inputSync
    | with_reducible apply pic_makeByteAvail
    | with_reducible apply pic_input2Bytes
    | with_reducible apply pic_inputByte
    | with_reducible apply pic_skip_variable
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | (with_reducible apply pic_forIn; intro _ _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_i64Sub
    | with_reducible apply pic_tracems2
    | with_reducible apply pic_errexit1
    | split)

private theorem pic_save_marker (cinfo : C.DecompPtr) : PreservesIC (Mozjpeg.Jdmarker.save_marker cinfo) := by
  unfold Mozjpeg.Jdmarker.save_marker
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_examine_app0
    | with_reducible apply pic_examine_app14
    | with_reducible apply pic_skipDispatch
    | with_reducible apply pic_inputSync
    | with_reducible apply pic_makeByteAvail
    | with_reducible apply pic_input2Bytes
    | with_reducible apply pic_inputByte
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | ((with_reducible apply pic_cwhile) <;> intro _)
    | (with_reducible apply pic_forIn; intro _ _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_ub
    | with_reducible apply pic_store_dc
    | with_reducible apply pic_store_mas
    | with_reducible apply pic_store_mrk
    | with_reducible apply pic_store_src
    | with_reducible apply pic_store_sm
    | with_reducible apply pic_store_byte
    | with_reducible apply pic_ptrAdd
    | with_reducible apply pic_i32Add
    | with_reducible apply pic_i64Add
    | with_reducible apply pic_i64Sub
    | with_reducible apply pic_tracems2
    | with_reducible apply pic_alloc_large_sm
    | split)

private theorem pic_callMarkerParser (cinfo : C.DecompPtr) (fn : C.FnPtr) :
    PreservesIC (Mozjpeg.Jdmarker.callMarkerParser cinfo fn) := by
  unfold Mozjpeg.Jdmarker.callMarkerParser
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_skip_variable
    | with_reducible apply pic_save_marker
    | with_reducible apply pic_get_interesting_appn
    | ((with_reducible apply pic_ite) <;> intro _)
    | with_reducible apply pic_ub)

theorem read_markers_preserves_inputctls (cinfo : C.DecompPtr) :
    PreservesIC (Mozjpeg.Jdmarker.read_markers cinfo) := by
  unfold Mozjpeg.Jdmarker.read_markers
  repeat' (
    try dsimp only
    first
    | with_reducible apply pic_first_marker
    | with_reducible apply pic_next_marker
    | with_reducible apply pic_get_soi
    | with_reducible apply pic_get_sof
    | with_reducible apply pic_get_sos
    | with_reducible apply pic_get_dac
    | with_reducible apply pic_get_dht
    | with_reducible apply pic_get_dqt
    | with_reducible apply pic_get_dri
    | with_reducible apply pic_skip_variable
    | with_reducible apply pic_callMarkerParser
    | (with_reducible apply pic_bind; rotate_left 1; intro _; rotate_right 1)
    | ((with_reducible apply pic_ite) <;> intro _)
    | ((with_reducible apply pic_cwhile) <;> intro _)
    | with_reducible apply pic_pure
    | with_reducible apply pic_load
    | with_reducible apply pic_store_dc
    | with_reducible apply pic_ub
    | with_reducible apply pic_errorExit
    | with_reducible apply pic_errexit1
    | with_reducible apply pic_warnms2
    | with_reducible apply pic_tracems
    | with_reducible apply pic_tracems1
    | split)

private theorem postSofBase_of_multiScanReady {h : C.Heap} {dc : C.JpegDecompressStruct}
    (hm : MultiScanReady h dc) : PostSofBase h dc :=
  ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

private theorem rmWarnPot_congr {errs errs' : Array C.JpegErrorMgr} {srcs srcs' : Array C.JpegSourceMgr}
    {dc dc' : C.JpegDecompressStruct}
    (hnw : errs'[0]!.numWarnings = errs[0]!.numWarnings) (hsrc : srcs' = srcs)
    (hum : dc'.unreadMarker = dc.unreadMarker) :
    rmWarnPot errs' srcs' dc' = rmWarnPot errs srcs dc := by
  simp only [rmWarnPot, warnPotVal, hnw, hsrc, hum]

private theorem rmRank_congr {dc dc' : C.JpegDecompressStruct} {mrk mrk' : C.JpegMarkerReader}
    {src src' : C.JpegSourceMgr}
    (hsoi : mrk'.sawSOI = mrk.sawSOI) (hsrc : src' = src) (hum : dc'.unreadMarker = dc.unreadMarker) :
    rmRank dc' mrk' src' = rmRank dc mrk src := by
  simp only [rmRank, hsoi, hsrc, hum]

theorem consume_markers_ok {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw : CompSawZero ctx h)
    (potBd : Int)
    (hpotBd : ∀ dcs mrks srcs errs,
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
      C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
      C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      rmWarnPot errs srcs dcs[0]! + ↑(rmRank dcs[0]! mrks[0]! srcs[0]!) ≤ potBd)
    (hpotHi : potBd + 2 ^ 23 < 2 ^ 63)
    (hscanBd : ∀ dcs,
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      dcs[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31)
    (hstate : ∀ ics dcs,
      C.Space.get h ctx.ric = some ics → 0 < ics.size →
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      ics[0]!.eoiReached ≠ 0 ∨ ics[0]!.inheaders ≠ 0 ∨
      ics[0]!.hasMultipleScans = 0 ∨ MultiScanReady h dcs[0]!) :
    ∃ res h', C.run (Mozjpeg.Jdinput.consume_markers (C.Ptr.ref (C.DecompRef.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      match res with
      | .errExit _ => True
      | .ok val =>
        (val = JPEG_REACHED_SOS ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
          (∀ ics', C.Space.get h' ctx.ric = some ics' → 0 < ics'.size →
            ics'[0]!.eoiReached = 0) ∧
          (∀ mrks', C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
            mrks'[0]!.sawSOF ≠ 0) ∧
          (∀ dcs' mrks' srcs' errs' dcs0 mrks0 srcs0 ics0 ics',
            C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
            C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
            C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
            C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
            C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
            C.Space.get h ctx.rmrk = some mrks0 → 0 < mrks0.size →
            C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
            C.Space.get h ctx.ric = some ics0 → 0 < ics0.size →
            C.Space.get h' ctx.ric = some ics' → 0 < ics'.size →
            rmWarnPot errs' srcs' dcs'[0]! + ↑(rmRank dcs'[0]! mrks'[0]! srcs'[0]!) ≤ potBd ∧
            rmRank dcs'[0]! mrks'[0]! srcs'[0]! < rmRank dcs0[0]! mrks0[0]! srcs0[0]! ∧
            dcs'[0]!.inputScanNumber.toInt = dcs0[0]!.inputScanNumber.toInt + 1 ∧
            (isConstEofPtr srcs'[0]!.nextInputByte = false →
              isConstEofPtr srcs0[0]!.nextInputByte = false ∧
              srcs'[0]!.bytesInBuffer.toNat + 8 ≤ srcs0[0]!.bytesInBuffer.toNat) ∧
            (ics0[0]!.inheaders ≠ 0 →
              ics'[0]!.inheaders = 0 ∧
              ics'[0]!.consumeInput = ics0[0]!.consumeInput ∧
              (dcs0[0]!.entropyStartPass = C.FnPtr.fn "noop" →
                dcs0[0]!.coefStartInputPass = C.FnPtr.fn "noop" →
                dcs0[0]!.coefConsumeData = C.FnPtr.fn "dummy_consume_data" →
                MultiScanReady h' dcs'[0]!)) ∧
            (ics0[0]!.inheaders = 0 →
              ics'[0]!.consumeInput = C.FnPtr.fn "dummy_consume_data"))) ∨
        (val = JPEG_REACHED_EOI ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
          (∀ ics', C.Space.get h' ctx.ric = some ics' → 0 < ics'.size → ics'[0]!.eoiReached ≠ 0)) ∨
        val = JPEG_SUSPENDED := by
  obtain ⟨dcs0, hgdc0, hszdc0, herr0, _, _, hic0, hmrk0_ref, _⟩ := parserEnv_get_dc hp
  obtain ⟨ics0, hgic0, hszic0, hrst0, hcon0⟩ := parserEnv_get_ic hp
  obtain ⟨mrks0, hgmrk0, hszmrk0, hrm0, _⟩ := parserEnv_get_mrk hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlic0 := ptr_load_ok (r := ctx.ric) (off := 0) hgic0 hszic0
  by_cases heoi0 : (ics0[0]!.eoiReached != 0) = true
  · have heoiNe0 : ics0[0]!.eoiReached ≠ 0 := by simpa using heoi0
    refine ⟨.ok JPEG_REACHED_EOI, h, ?_, Or.inr (Or.inl ⟨rfl, hp, hsaw, fun ics' hgi _ => ?_⟩)⟩
    · unfold Mozjpeg.Jdinput.consume_markers
      rw [C.run_bind, hldc0]; dsimp only
      rw [C.run_bind, hic0, hlic0]; dsimp only
      simp [heoi0, C.run]
    · rw [Option.some.inj (hgi.symm.trans hgic0)]; exact heoiNe0
  · have heoiF : (ics0[0]!.eoiReached != 0) = false := Bool.eq_false_iff.mpr heoi0
    have heoiZ : ics0[0]!.eoiReached = 0 := by simpa using heoiF
    have hlmrk0 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk0 hszmrk0
    have hrmEq0 : (mrks0[0]!.readMarkers == C.FnPtr.fn "read_markers") = true := by simp [hrm0]
    obtain ⟨resR, hR, hrunR, hresR⟩ := read_markers_parser hp hsaw potBd hpotBd hpotHi hscanBd
    have hicReq : hR.inputctls = h.inputctls := read_markers_preserves_inputctls _ h resR hR hrunR
    have hgicR : C.Space.get hR ctx.ric = some ics0 := by simp only [C.Space.get]; rw [hicReq]; exact hgic0
    rcases resR with val | code
    · rcases hresR with ⟨rfl, hpR, hsawR, hmrkSofR, hdcR, hrkR⟩ | ⟨rfl, hpR, hsawR, _⟩ | rfl
      · obtain ⟨dcsR, hgdcR, hszdcR, herrR, _, _, hicR, hmrkR_ref, _⟩ := parserEnv_get_dc hpR
        have hldcR := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcR hszdcR
        have hlicR := ptr_load_ok (r := ctx.ric) (off := 0) hgicR hszic0
        have hvalSos : (JPEG_REACHED_SOS == JPEG_REACHED_SOS) = true := by decide
        have hdr_flds := hdcR dcs0 dcsR hgdc0 hszdc0 hgdcR hszdcR
        by_cases hinh : (ics0[0]!.inheaders != 0) = true
        · have hinhNe0 : ics0[0]!.inheaders ≠ 0 := by simpa using hinh
          obtain ⟨resI, hI, hrunI, hpI, hsawI, hnwI, hmrkI, hsrcI, hdcI, hicI, hpostI⟩ :=
            initial_setup_ok hpR hsawR hmrkSofR
          rcases resI with ⟨⟩ | codeI
          · obtain ⟨hmrkSofI, hfnI, hmscI⟩ := hpostI
            obtain ⟨dcsI, hgdcI, hszdcI, _, _, _, hicI_ref, _⟩ := parserEnv_get_dc hpI
            obtain ⟨icsI, hgicI, hszicI, _, _⟩ := parserEnv_get_ic hpI
            have hicIFlds := hicI ics0 icsI hgicR hszic0 hgicI hszicI
            have hldcI := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcI hszdcI
            have hlicI := ptr_load_ok (r := ctx.ric) (off := 0) hgicI hszicI
            let ic' : C.JpegInputController := { (icsI[0]!) with inheaders := Mozjpeg.MoreCfg.FALSE }
            have hroIcI : C.Space.ro hI ctx.ric = false := rfl
            have hstIcI := ptr_store_ok (r := ctx.ric) (off := 0) (v := ic') hgicI hroIcI hszicI
            let h' := C.Space.put hI ctx.ric (icsI.set! 0 ic')
            have hp' : ParserEnv ctx h' := parserEnv_put_ic hpI hgicI hszicI
              (hicIFlds.2.2.2.trans hrst0)
              (by rw [show ic'.consumeInput = icsI[0]!.consumeInput from rfl, hicIFlds.2.2.1]; exact hcon0)
            have hsaw' : CompSawZero ctx h' := compSawZero_put_ic hsawI
            refine ⟨.ok JPEG_REACHED_SOS, h', ?_, Or.inl ⟨rfl, hp', hsaw', ?_, ?_, ?_⟩⟩
            · unfold Mozjpeg.Jdinput.consume_markers
              rw [C.run_bind, hldc0]; dsimp only
              rw [C.run_bind, hic0, hlic0]; dsimp only
              simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hmrk0_ref, hlmrk0]; dsimp only
              simp only [hrmEq0, ↓reduceIte, C.run_bind]
              rw [hrunR]; dsimp only
              simp only [hvalSos, ↓reduceIte, C.run_bind]
              rw [hldcR]; dsimp only
              rw [hicR, hlicR]; dsimp only
              simp only [hinh, ↓reduceIte, C.run_bind]
              rw [hrunI]; dsimp only
              rw [C.run_bind, hldcI]; dsimp only
              rw [C.run_bind, hicI_ref, hlicI]; dsimp only
              rw [C.run_bind, hstIcI]; rfl
            · intro ics' hgi _
              have hget' : C.Space.get h' ctx.ric = some (icsI.set! 0 ic') := by simp [h', C.Space.get, C.Space.put]
              rw [Option.some.inj (hgi.symm.trans hget'), array_set_bang_self icsI hszicI ic']
              exact hicIFlds.2.1.trans heoiZ
            · intro mrks' hgm' hszm'
              simp only [h', C.Space.get, C.Space.put] at hgm'
              exact hmrkSofI mrks' hgm' hszm'
            · intro dcs' mrks' srcs' errs' dcsA mrksA srcsA icsA ics'
                hgdc' _ hgmrk' hszmrk' hgsrc' hszsrc' hgerr' hszerr'
                hgdcA _ hgmrkA _ hgsrcA _ hgicA _ hgic' _
              have hdcAeq : dcsA = dcs0 := Option.some.inj (hgdcA.symm.trans hgdc0)
              have hmkAeq : mrksA = mrks0 := Option.some.inj (hgmrkA.symm.trans hgmrk0)
              have hicAeq : icsA = ics0 := Option.some.inj (hgicA.symm.trans hgic0)
              obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
              have hsrAeq : srcsA = srcs0 := Option.some.inj (hgsrcA.symm.trans hgsrc0)
              obtain ⟨mrksR, hgmrkR, hszmrkR, _⟩ := parserEnv_get_mrk hpR
              obtain ⟨srcsR, hgsrcR, hszsrcR, _⟩ := parserEnv_get_src hpR
              obtain ⟨errsR, hgerrR, hszerrR, _⟩ := parserEnv_get_err hpR
              have hrkR0 := hrkR dcsR mrksR srcsR errsR dcs0 mrks0 srcs0 hgdcR hszdcR hgmrkR hszmrkR hgsrcR hszsrcR hgerrR hszerrR hgdc0 hszdc0 hgmrk0 hszmrk0 hgsrc0 hszsrc0
              have hdc'R : dcs' = dcsI := Option.some.inj (by
                simp only [h', C.Space.get, C.Space.put] at hgdc'; exact hgdc'.symm.trans hgdcI)
              have hgetmk : C.Space.get hI ctx.rmrk = some mrks' := by
                simp only [h', C.Space.get, C.Space.put] at hgmrk'; exact hgmrk'
              have hmk'eq : mrks' = mrksR := hmrkI mrksR mrks' hgmrkR hszmrkR hgetmk hszmrk'
              have hgetsr : C.Space.get hI ctx.rs = some srcs' := by
                simp only [h', C.Space.get, C.Space.put] at hgsrc'; exact hgsrc'
              have hsr'eq : srcs' = srcsR := hsrcI srcsR srcs' hgsrcR hszsrcR hgetsr hszsrc'
              have hgeter : C.Space.get hI ctx.rerr = some errs' := by
                simp only [h', C.Space.get, C.Space.put] at hgerr'; exact hgerr'
              have hnw'eq := (hnwI errsR errs' hgerrR hszerrR hgeter).2
              have hdcIflds := hdcI dcsR dcsI hgdcR hszdcR hgdcI hszdcI
              have hfnIflds := hfnI dcsR dcsI hgdcR hszdcR hgdcI hszdcI
              have hwpEq : rmWarnPot errs' srcs' dcs'[0]! = rmWarnPot errsR srcsR dcsR[0]! :=
                rmWarnPot_congr hnw'eq hsr'eq (by rw [hdc'R, hdcIflds.2])
              have hrkEq : rmRank dcs'[0]! mrks'[0]! srcs'[0]! = rmRank dcsR[0]! mrksR[0]! srcsR[0]! :=
                rmRank_congr (by rw [hmk'eq]) (by rw [hsr'eq]) (by rw [hdc'R, hdcIflds.2])
              have hgetI' : C.Space.get h' ctx.ric = some (icsI.set! 0 ic') := by simp [h', C.Space.get, C.Space.put]
              have hic'Eq : ics' = icsI.set! 0 ic' := Option.some.inj (hgic'.symm.trans hgetI')
              refine ⟨?_, ?_, ?_, ?_, ?_, fun h0 => absurd (hicAeq ▸ h0) hinhNe0⟩
              · rw [hwpEq, hrkEq]; exact hrkR0.1
              · rw [hrkEq, hdcAeq, hmkAeq, hsrAeq]; exact hrkR0.2.2.1
              · rw [hdc'R, hdcAeq, hdcIflds.1, hdr_flds.1]
              · intro hce; rw [hsr'eq] at hce; rw [hsr'eq, hsrAeq]; exact hrkR0.2.2.2 hce
              · intro _
                refine ⟨?_, ?_, ?_⟩
                · rw [hic'Eq, array_set_bang_self icsI hszicI ic']; rfl
                · rw [hic'Eq, array_set_bang_self icsI hszicI ic', hicAeq]; exact hicIFlds.2.2.1
                · intro hf1 hf2 hf3
                  have hmsrI : MultiScanReady hI dcs'[0]! := by
                    rw [hdc'R]
                    exact hmscI dcsR dcsI hgdcR hszdcR hgdcI hszdcI hdr_flds.2.2.2.2.1
                      (hfnIflds.1.trans (hdr_flds.2.1.trans (hdcAeq ▸ hf1)))
                      (hfnIflds.2.1.trans (hdr_flds.2.2.1.trans (hdcAeq ▸ hf2)))
                      (hfnIflds.2.2.trans (hdr_flds.2.2.2.1.trans (hdcAeq ▸ hf3)))
                  exact multiScanReady_put_ic hmsrI
          · refine ⟨.errExit codeI, hI, ?_, trivial⟩
            unfold Mozjpeg.Jdinput.consume_markers
            rw [C.run_bind, hldc0]; dsimp only
            rw [C.run_bind, hic0, hlic0]; dsimp only
            simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
            rw [hmrk0_ref, hlmrk0]; dsimp only
            simp only [hrmEq0, ↓reduceIte, C.run_bind]
            rw [hrunR]; dsimp only
            simp only [hvalSos, ↓reduceIte, C.run_bind]
            rw [hldcR]; dsimp only
            rw [hicR, hlicR]; dsimp only
            simp only [hinh, ↓reduceIte, C.run_bind]
            rw [hrunI]; rfl
        · have hinhF : (ics0[0]!.inheaders != 0) = false := Bool.eq_false_iff.mpr hinh
          have hinhZ : ics0[0]!.inheaders = 0 := by simpa using hinhF
          by_cases hms : (ics0[0]!.hasMultipleScans == 0) = true
          · obtain ⟨errsR, hgerrR, hszerrR, _, _⟩ := parserEnv_get_err hpR
            obtain ⟨hE, hrunE, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
              errexit_full hpR hsawR JERR_EOI_EXPECTED
            refine ⟨.errExit JERR_EOI_EXPECTED, hE, ?_, trivial⟩
            unfold Mozjpeg.Jdinput.consume_markers
            rw [C.run_bind, hldc0]; dsimp only
            rw [C.run_bind, hic0, hlic0]; dsimp only
            simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
            rw [hmrk0_ref, hlmrk0]; dsimp only
            simp only [hrmEq0, ↓reduceIte, C.run_bind]
            rw [hrunR]; dsimp only
            simp only [hvalSos, ↓reduceIte, C.run_bind]
            rw [hldcR]; dsimp only
            rw [hicR, hlicR]; dsimp only
            simp only [hinhF, Bool.false_eq_true, ↓reduceIte]
            simp only [hms, ↓reduceIte, C.run_bind]
            rw [herrR, hrunE]; rfl
          · have hmsF : (ics0[0]!.hasMultipleScans == 0) = false := Bool.eq_false_iff.mpr hms
            have hmsNe : ics0[0]!.hasMultipleScans ≠ 0 := by simpa using hmsF
            have hmsr0 : MultiScanReady h dcs0[0]! := by
              rcases hstate ics0 dcs0 hgic0 hszic0 hgdc0 hszdc0 with h1 | h2 | h3 | h4
              · exact absurd heoiZ h1
              · exact absurd hinhZ h2
              · exact absurd h3 hmsNe
              · exact h4
            have hmR : ∀ dcsC, C.Space.get hR (C.DecompRef.decomp ctx.bdc) = some dcsC → 0 < dcsC.size →
                MultiScanReady hR dcsC[0]! := fun dcsC hgC hszC =>
              (hdcR dcs0 dcsC hgdc0 hszdc0 hgC hszC).2.2.2.2.2 (postSofBase_of_multiScanReady hmsr0)
            obtain ⟨resS, hS, hrunS, hpS, hsawS, hnwS, hmrkS, hsrcS, _, hdS, hicS⟩ :=
              start_input_pass_ok hpR hsawR hmR
            rcases resS with ⟨⟩ | codeS
            · refine ⟨.ok JPEG_REACHED_SOS, hS, ?_, Or.inl ⟨rfl, hpS, hsawS, ?_, ?_, ?_⟩⟩
              · unfold Mozjpeg.Jdinput.consume_markers
                rw [C.run_bind, hldc0]; dsimp only
                rw [C.run_bind, hic0, hlic0]; dsimp only
                simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
                rw [hmrk0_ref, hlmrk0]; dsimp only
                simp only [hrmEq0, ↓reduceIte, C.run_bind]
                rw [hrunR]; dsimp only
                simp only [hvalSos, ↓reduceIte, C.run_bind]
                rw [hldcR]; dsimp only
                rw [hicR, hlicR]; dsimp only
                simp only [hinhF, Bool.false_eq_true, ↓reduceIte]
                simp only [hmsF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
                rw [hrunS]; rfl
              · intro ics' hgi hszi'
                exact (hicS ics0 ics' hgicR hszic0 hgi hszi').1.trans heoiZ
              · intro mrks' hgm' hszm'
                obtain ⟨mrksR, hgR, hszR, _⟩ := parserEnv_get_mrk hpR
                rw [hmrkS mrksR mrks' hgR hszR hgm' hszm']
                exact hmrkSofR mrksR hgR hszR
              · intro dcs' mrks' srcs' errs' dcsA mrksA srcsA icsA ics'
                  hgdc' hszdc' hgmrk' hszmrk' hgsrc' hszsrc' hgerr' hszerr'
                  hgdcA _ hgmrkA _ hgsrcA _ hgicA _ hgic' hszic'
                have hdcAeq : dcsA = dcs0 := Option.some.inj (hgdcA.symm.trans hgdc0)
                have hmkAeq : mrksA = mrks0 := Option.some.inj (hgmrkA.symm.trans hgmrk0)
                have hicAeq : icsA = ics0 := Option.some.inj (hgicA.symm.trans hgic0)
                obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
                have hsrAeq : srcsA = srcs0 := Option.some.inj (hgsrcA.symm.trans hgsrc0)
                obtain ⟨mrksR, hgmrkR, hszmrkR, _⟩ := parserEnv_get_mrk hpR
                obtain ⟨srcsR, hgsrcR, hszsrcR, _⟩ := parserEnv_get_src hpR
                obtain ⟨errsR, hgerrR, hszerrR, _⟩ := parserEnv_get_err hpR
                have hrkR0 := hrkR dcsR mrksR srcsR errsR dcs0 mrks0 srcs0 hgdcR hszdcR hgmrkR hszmrkR hgsrcR hszsrcR hgerrR hszerrR hgdc0 hszdc0 hgmrk0 hszmrk0 hgsrc0 hszsrc0
                have hmk'eq : mrks' = mrksR := hmrkS mrksR mrks' hgmrkR hszmrkR hgmrk' hszmrk'
                have hsr'eq : srcs' = srcsR := hsrcS srcsR srcs' hgsrcR hszsrcR hgsrc' hszsrc'
                have hnw'eq := (hnwS errsR errs' hgerrR hszerrR hgerr').2
                have hdSflds := hdS dcsR dcs' hgdcR hszdcR hgdc' hszdc'
                have hwpEq : rmWarnPot errs' srcs' dcs'[0]! = rmWarnPot errsR srcsR dcsR[0]! :=
                  rmWarnPot_congr hnw'eq hsr'eq hdSflds.2.2
                have hrkEq : rmRank dcs'[0]! mrks'[0]! srcs'[0]! = rmRank dcsR[0]! mrksR[0]! srcsR[0]! :=
                  rmRank_congr (by rw [hmk'eq]) (by rw [hsr'eq]) hdSflds.2.2
                have hicSflds := hicS ics0 ics' hgicR hszic0 hgic' hszic'
                refine ⟨?_, ?_, ?_, ?_, fun h0 => absurd (hicAeq ▸ hinhZ) h0, fun _ => hicSflds.2.2.2⟩
                · rw [hwpEq, hrkEq]; exact hrkR0.1
                · rw [hrkEq, hdcAeq, hmkAeq, hsrAeq]; exact hrkR0.2.2.1
                · rw [hdcAeq, hdSflds.2.1, hdr_flds.1]
                · intro hce; rw [hsr'eq] at hce; rw [hsr'eq, hsrAeq]; exact hrkR0.2.2.2 hce
            · refine ⟨.errExit codeS, hS, ?_, trivial⟩
              unfold Mozjpeg.Jdinput.consume_markers
              rw [C.run_bind, hldc0]; dsimp only
              rw [C.run_bind, hic0, hlic0]; dsimp only
              simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hmrk0_ref, hlmrk0]; dsimp only
              simp only [hrmEq0, ↓reduceIte, C.run_bind]
              rw [hrunR]; dsimp only
              simp only [hvalSos, ↓reduceIte, C.run_bind]
              rw [hldcR]; dsimp only
              rw [hicR, hlicR]; dsimp only
              simp only [hinhF, Bool.false_eq_true, ↓reduceIte]
              simp only [hmsF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hrunS]; rfl
      · have hvalSosF : (JPEG_REACHED_EOI == JPEG_REACHED_SOS) = false := by decide
        have hvalEoiT : (JPEG_REACHED_EOI == JPEG_REACHED_EOI) = true := by decide
        obtain ⟨dcsE, hgdcE, hszdcE, herrE, _, _, hicE, hmrkE_ref, _⟩ := parserEnv_get_dc hpR
        have hldcE := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcE hszdcE
        have hlicE := ptr_load_ok (r := ctx.ric) (off := 0) hgicR hszic0
        let icE' : C.JpegInputController := { (ics0[0]!) with eoiReached := Mozjpeg.MoreCfg.TRUE }
        have hroIcE : C.Space.ro hR ctx.ric = false := rfl
        have hstIcE := ptr_store_ok (r := ctx.ric) (off := 0) (v := icE') hgicR hroIcE hszic0
        let hA := C.Space.put hR ctx.ric (ics0.set! 0 icE')
        have hpA : ParserEnv ctx hA := parserEnv_put_ic hpR hgicR hszic0 hrst0 hcon0
        have hsawA : CompSawZero ctx hA := compSawZero_put_ic hsawR
        have hgetIcA : C.Space.get hA ctx.ric = some (ics0.set! 0 icE') := by simp [hA, C.Space.get, C.Space.put]
        have heoiTrue : icE'.eoiReached ≠ 0 := by dsimp only [icE']; decide
        by_cases hinhE : (ics0[0]!.inheaders != 0) = true
        · obtain ⟨mrksA, hgmrkA, hszmrkA, _⟩ := parserEnv_get_mrk hpA
          have hlmrkA := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrkA hszmrkA
          by_cases hsofE : (mrksA[0]!.sawSOF != 0) = true
          · obtain ⟨errsA, hgerrA, hszerrA, _, _⟩ := parserEnv_get_err hpA
            obtain ⟨hE, hrunE, _⟩ := errexit_full hpA hsawA JERR_SOF_NO_SOS
            refine ⟨.errExit JERR_SOF_NO_SOS, hE, ?_, trivial⟩
            unfold Mozjpeg.Jdinput.consume_markers
            rw [C.run_bind, hldc0]; dsimp only
            rw [C.run_bind, hic0, hlic0]; dsimp only
            simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
            rw [hmrk0_ref, hlmrk0]; dsimp only
            simp only [hrmEq0, ↓reduceIte, C.run_bind]
            rw [hrunR]; dsimp only
            simp only [hvalSosF, hvalEoiT, Bool.false_eq_true, ↓reduceIte, C.run_bind]
            rw [hldcE]; dsimp only
            rw [hicE, hlicE]; dsimp only
            rw [hstIcE]; dsimp only
            simp only [hinhE, ↓reduceIte, C.run_bind]
            rw [hmrkE_ref, hlmrkA]; dsimp only
            simp only [hsofE, ↓reduceIte, C.run_bind]
            rw [herrE, hrunE]; rfl
          · have hsofEF : (mrksA[0]!.sawSOF != 0) = false := Bool.eq_false_iff.mpr hsofE
            refine ⟨.ok JPEG_REACHED_EOI, hA, ?_, Or.inr (Or.inl ⟨rfl, hpA, hsawA, fun ics' hgi _ => ?_⟩)⟩
            · unfold Mozjpeg.Jdinput.consume_markers
              rw [C.run_bind, hldc0]; dsimp only
              rw [C.run_bind, hic0, hlic0]; dsimp only
              simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hmrk0_ref, hlmrk0]; dsimp only
              simp only [hrmEq0, ↓reduceIte, C.run_bind]
              rw [hrunR]; dsimp only
              simp only [hvalSosF, hvalEoiT, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hldcE]; dsimp only
              rw [hicE, hlicE]; dsimp only
              rw [hstIcE]; dsimp only
              simp only [hinhE, ↓reduceIte, C.run_bind]
              rw [hmrkE_ref, hlmrkA]; dsimp only
              simp only [hsofEF, Bool.false_eq_true, ↓reduceIte]; rfl
            · rw [Option.some.inj (hgi.symm.trans hgetIcA), array_set_bang_self ics0 hszic0 icE']
              exact heoiTrue
        · have hinhEF : (ics0[0]!.inheaders != 0) = false := Bool.eq_false_iff.mpr hinhE
          by_cases hscanGt : dcsE[0]!.outputScanNumber > dcsE[0]!.inputScanNumber
          · let dcE' : C.JpegDecompressStruct := { (dcsE[0]!) with outputScanNumber := dcsE[0]!.inputScanNumber }
            have hgdcEA : C.Space.get hA (C.DecompRef.decomp ctx.bdc) = some dcsE := by
              simp only [hA, C.Space.get, C.Space.put]; exact hgdcE
            have hroDcA : C.Space.ro hA (C.DecompRef.decomp ctx.bdc) = false := rfl
            have hstDcA := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcE') hgdcEA hroDcA hszdcE
            let h' := C.Space.put hA (C.DecompRef.decomp ctx.bdc) (dcsE.set! 0 dcE')
            have hp' : ParserEnv ctx h' := parserEnv_put_dc_keep' hpA hgdcEA hszdcE
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            have hsaw' : CompSawZero ctx h' := compSawZero_put_dc_keep hsawA hgdcEA hszdcE rfl
            refine ⟨.ok JPEG_REACHED_EOI, h', ?_, Or.inr (Or.inl ⟨rfl, hp', hsaw', fun ics' hgi _ => ?_⟩)⟩
            · unfold Mozjpeg.Jdinput.consume_markers
              rw [C.run_bind, hldc0]; dsimp only
              rw [C.run_bind, hic0, hlic0]; dsimp only
              simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hmrk0_ref, hlmrk0]; dsimp only
              simp only [hrmEq0, ↓reduceIte, C.run_bind]
              rw [hrunR]; dsimp only
              simp only [hvalSosF, hvalEoiT, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hldcE]; dsimp only
              have hldIcE : C.run (C.Ptr.load dcsE[0]!.inputctl) hR = .ok (ics0[0]!, hR) := by
                rw [hicE]; exact hlicE
              have hstIcE' : C.run (dcsE[0]!.inputctl.store icE') hR =
                  .ok ((), C.Space.put hR ctx.ric (ics0.set! 0 icE')) := by
                rw [hicE]; exact hstIcE
              rw [hldIcE]; dsimp only
              rw [hstIcE']; dsimp only
              simp only [hinhEF, Bool.false_eq_true, ↓reduceIte, hscanGt, ↓reduceIte, C.run_bind]
              rw [hstDcA]; rfl
            · have hget' : C.Space.get h' ctx.ric = some (ics0.set! 0 icE') := by
                simp only [h', C.Space.get, C.Space.put] at hgetIcA ⊢; exact hgetIcA
              rw [Option.some.inj (hgi.symm.trans hget'), array_set_bang_self ics0 hszic0 icE']
              exact heoiTrue
          · refine ⟨.ok JPEG_REACHED_EOI, hA, ?_, Or.inr (Or.inl ⟨rfl, hpA, hsawA, fun ics' hgi _ => ?_⟩)⟩
            · unfold Mozjpeg.Jdinput.consume_markers
              rw [C.run_bind, hldc0]; dsimp only
              rw [C.run_bind, hic0, hlic0]; dsimp only
              simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hmrk0_ref, hlmrk0]; dsimp only
              simp only [hrmEq0, ↓reduceIte, C.run_bind]
              rw [hrunR]; dsimp only
              simp only [hvalSosF, hvalEoiT, Bool.false_eq_true, ↓reduceIte, C.run_bind]
              rw [hldcE]; dsimp only
              rw [hicE, hlicE]; dsimp only
              rw [hstIcE]; dsimp only
              simp only [hinhEF, Bool.false_eq_true, ↓reduceIte, hscanGt]; rfl
            · rw [Option.some.inj (hgi.symm.trans hgetIcA), array_set_bang_self ics0 hszic0 icE']
              exact heoiTrue
      · have hvalSosF : (JPEG_SUSPENDED == JPEG_REACHED_SOS) = false := by decide
        have hvalEoiF : (JPEG_SUSPENDED == JPEG_REACHED_EOI) = false := by decide
        refine ⟨.ok JPEG_SUSPENDED, hR, ?_, Or.inr (Or.inr rfl)⟩
        unfold Mozjpeg.Jdinput.consume_markers
        rw [C.run_bind, hldc0]; dsimp only
        rw [C.run_bind, hic0, hlic0]; dsimp only
        simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
        rw [hmrk0_ref, hlmrk0]; dsimp only
        simp only [hrmEq0, ↓reduceIte, C.run_bind]
        rw [hrunR]; dsimp only
        simp only [hvalSosF, hvalEoiF, Bool.false_eq_true, ↓reduceIte]; rfl
    · refine ⟨.errExit code, hR, ?_, trivial⟩
      unfold Mozjpeg.Jdinput.consume_markers
      rw [C.run_bind, hldc0]; dsimp only
      rw [C.run_bind, hic0, hlic0]; dsimp only
      simp only [heoiF, Bool.false_eq_true, ↓reduceIte, C.run_bind]
      rw [hmrk0_ref, hlmrk0]; dsimp only
      simp only [hrmEq0, ↓reduceIte, C.run_bind]
      rw [hrunR]; rfl

end MozjpegF.Proof.JdinputConsume

