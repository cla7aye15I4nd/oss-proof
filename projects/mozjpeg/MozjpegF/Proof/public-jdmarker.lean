import MozjpegF.Spec.Safety.Goals
import MozjpegF.Proof.«jdmarker.c.helpers»

/-!
# Proofs of `jdmarker.c` safety specifications (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.Jdmarker
open C MozjpegF.Spec MozjpegF.Spec.Safety Mozjpeg.Jdmarker Mozjpeg.JerrorH Mozjpeg.JpeglibH Mozjpeg.MoreCfg
open MozjpegF.Proof.JdmarkerHelpers

theorem jpeg_save_markers_safety : Goal.jpeg_save_markers_safety := by
  intro h cinfo markerCode limit hvalid _hchunk
  obtain ⟨rc, dcs, dc, rm, mems, _rmas, _masters, _ric, _ics, rmrk, mrks,
    hc, hgetdc, hszdc, hdc, herrValid, hmem, hgetmem, hszmem, _hmas, _hgetmas, _hszmas,
    _hin, _hgetin, _hszin, hmrk, hgetmrk, hszmrk, _hpool⟩ := hvalid
  subst hc
  obtain ⟨rerr, errs, herr, hgeterr, hszerr⟩ := herrValid
  unfold jpeg_save_markers errexit1
  cases rc with | decomp bdc =>
  cases rm with | mem bmem =>
  cases rmrk with | marker bmrk =>
  cases rerr with | err berr =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hmrk]
  rw [Ptr.load_bind h _ 0 mrks _ hgetmrk hszmrk, hmem]
  rw [Ptr.load_bind h _ 0 mems _ hgetmem hszmem]
  dsimp only
  have hro_mrk : C.Space.ro h (C.MarkerRef.marker bmrk) = false := rfl
  have hro_err : C.Space.ro h (C.ErrRef.err berr) = false := rfl
  by_cases hcom : (markerCode == M_COM) = true
  · simp only [hcom, ↓reduceIte]
    rw [Ptr.store_bind h _ 0 _ mrks _ hgetmrk hro_mrk hszmrk]
    exact ⟨_, _, rfl⟩
  · have hcomF : (markerCode == M_COM) = false := Bool.eq_false_iff.mpr hcom
    simp only [hcomF, Bool.false_eq_true, ↓reduceIte]
    by_cases happ : (markerCode ≥ M_APP0 && markerCode ≤ M_APP15) = true
    · simp only [happ, ↓reduceIte]
      rw [Ptr.store_bind h _ 0 _ mrks _ hgetmrk hro_mrk hszmrk]
      exact ⟨_, _, rfl⟩
    · have happF : (markerCode ≥ M_APP0 && markerCode ≤ M_APP15) = false := Bool.eq_false_iff.mpr happ
      simp only [happF, Bool.false_eq_true, ↓reduceIte, herr, bind_assoc_m, pure_bind_m]
      rw [Ptr.load_bind h _ 0 errs _ hgeterr hszerr]
      rw [Ptr.store_bind h _ 0 _ errs _ hgeterr hro_err hszerr]
      exact ⟨_, _, rfl⟩

private theorem resyncAction_ok (desired : Int32)
    (hlo : -(2 ^ 31 : Int) + 2 ≤ desired.toInt) (hhi : desired.toInt < 2 ^ 31 - 2)
    (s : ResyncState) (h : C.Heap) :
    ∃ act : Int32,
      (∀ {α : Type} (k : Int32 → C.M α),
        C.run (do
          let action ← do
            if s.marker < M_SOF0 then
              pure (2 : Int32)
            else if s.marker < M_RST0 || s.marker > M_RST7 then
              pure (3 : Int32)
            else
              let p1 ← i32Add desired 1
              let p2 ← i32Add desired 2
              let m1 ← i32Sub desired 1
              let m2 ← i32Sub desired 2
              let r_p1 := M_RST0 + Int32.ofInt (p1.toInt % 8)
              let r_p2 := M_RST0 + Int32.ofInt (p2.toInt % 8)
              let r_m1 := M_RST0 + Int32.ofInt (m1.toInt % 8)
              let r_m2 := M_RST0 + Int32.ofInt (m2.toInt % 8)
              if s.marker == r_p1 || s.marker == r_p2 then
                pure (3 : Int32)
              else if s.marker == r_m1 || s.marker == r_m2 then
                pure (2 : Int32)
              else
                pure (1 : Int32)
          k action) h = C.run (k act) h) ∧
      (act = 1 ∨ act = 2 ∨ act = 3) ∧
      (s.marker = M_EOI → act = 3) := by
  by_cases hsof : s.marker < M_SOF0
  · refine ⟨2, (fun k => by simp [hsof, pure_bind_m]), Or.inr (Or.inl rfl), fun heoi => ?_⟩
    rw [heoi] at hsof; exfalso; revert hsof; decide
  · by_cases hrst : (s.marker < M_RST0 || s.marker > M_RST7) = true
    · refine ⟨3, (fun k => by simp [hsof, hrst, pure_bind_m]), Or.inr (Or.inr rfl), fun _ => rfl⟩
    · have hrstF : (s.marker < M_RST0 || s.marker > M_RST7) = false := Bool.eq_false_iff.mpr hrst
      have hp1 : -(2 ^ 31 : Int) ≤ desired.toInt + 1 ∧ desired.toInt + 1 < 2 ^ 31 := by omega
      have hp2 : -(2 ^ 31 : Int) ≤ desired.toInt + 2 ∧ desired.toInt + 2 < 2 ^ 31 := by omega
      have hm1 : -(2 ^ 31 : Int) ≤ desired.toInt - 1 ∧ desired.toInt - 1 < 2 ^ 31 := by omega
      have hm2 : -(2 ^ 31 : Int) ≤ desired.toInt - 2 ∧ desired.toInt - 2 < 2 ^ 31 := by omega
      let p1 := Int32.ofInt (desired.toInt + 1)
      let p2 := Int32.ofInt (desired.toInt + 2)
      let m1 := Int32.ofInt (desired.toInt - 1)
      let m2 := Int32.ofInt (desired.toInt - 2)
      let r_p1 := M_RST0 + Int32.ofInt (p1.toInt % 8)
      let r_p2 := M_RST0 + Int32.ofInt (p2.toInt % 8)
      let r_m1 := M_RST0 + Int32.ofInt (m1.toInt % 8)
      let r_m2 := M_RST0 + Int32.ofInt (m2.toInt % 8)
      have hneEoi : s.marker ≠ M_EOI := by
        intro heoi
        have : (M_EOI < M_RST0 || M_EOI > M_RST7) = true := by decide
        rw [heoi, this] at hrstF
        exact Bool.noConfusion hrstF
      have hbind4 : ∀ (α : Type) (f : Int32 → Int32 → Int32 → Int32 → C.M α),
          C.run (do
            let x1 ← i32Add desired 1
            let x2 ← i32Add desired 2
            let y1 ← i32Sub desired 1
            let y2 ← i32Sub desired 2
            f x1 x2 y1 y2) h = C.run (f p1 p2 m1 m2) h := by
        intro α f
        dsimp only [i32Add, i32Sub, checkI32]
        have h1eq : (1 : Int32).toInt = 1 := rfl
        have h2eq : (2 : Int32).toInt = 2 := rfl
        rw [h1eq, h2eq]
        simp only [hp1, hp2, hm1, hm2, and_self, ↓reduceIte, pure_bind_m]
        rfl
      by_cases h3 : (s.marker == r_p1 || s.marker == r_p2) = true
      · refine ⟨3, ?_, Or.inr (Or.inr rfl), fun heoi => absurd heoi hneEoi⟩
        intro α k
        simp only [hsof, ↓reduceIte, hrstF, Bool.false_eq_true]
        rw [hbind4 α (fun x1 x2 y1 y2 => do
          let action ←
            if (s.marker == M_RST0 + Int32.ofInt (x1.toInt % 8) ||
                s.marker == M_RST0 + Int32.ofInt (x2.toInt % 8)) = true then
              pure (3 : Int32)
            else if (s.marker == M_RST0 + Int32.ofInt (y1.toInt % 8) ||
                s.marker == M_RST0 + Int32.ofInt (y2.toInt % 8)) = true then
              pure (2 : Int32)
            else
              pure (1 : Int32)
          k action)]
        change C.run (do
          let action ← if (s.marker == r_p1 || s.marker == r_p2) = true then pure (3 : Int32)
            else if (s.marker == r_m1 || s.marker == r_m2) = true then pure (2 : Int32)
            else pure (1 : Int32)
          k action) h = C.run (k 3) h
        simp [h3, pure_bind_m]
      · have h3F : (s.marker == r_p1 || s.marker == r_p2) = false := Bool.eq_false_iff.mpr h3
        by_cases h2 : (s.marker == r_m1 || s.marker == r_m2) = true
        · refine ⟨2, ?_, Or.inr (Or.inl rfl), fun heoi => absurd heoi hneEoi⟩
          intro α k
          simp only [hsof, ↓reduceIte, hrstF, Bool.false_eq_true]
          rw [hbind4 α (fun x1 x2 y1 y2 => do
            let action ←
              if (s.marker == M_RST0 + Int32.ofInt (x1.toInt % 8) ||
                  s.marker == M_RST0 + Int32.ofInt (x2.toInt % 8)) = true then
                pure (3 : Int32)
              else if (s.marker == M_RST0 + Int32.ofInt (y1.toInt % 8) ||
                  s.marker == M_RST0 + Int32.ofInt (y2.toInt % 8)) = true then
                pure (2 : Int32)
              else
                pure (1 : Int32)
            k action)]
          change C.run (do
            let action ← if (s.marker == r_p1 || s.marker == r_p2) = true then pure (3 : Int32)
              else if (s.marker == r_m1 || s.marker == r_m2) = true then pure (2 : Int32)
              else pure (1 : Int32)
            k action) h = C.run (k 2) h
          simp [h3F, h2, pure_bind_m]
        · have h2F : (s.marker == r_m1 || s.marker == r_m2) = false := Bool.eq_false_iff.mpr h2
          refine ⟨1, ?_, Or.inl rfl, fun heoi => absurd heoi hneEoi⟩
          intro α k
          simp only [hsof, ↓reduceIte, hrstF, Bool.false_eq_true]
          rw [hbind4 α (fun x1 x2 y1 y2 => do
            let action ←
              if (s.marker == M_RST0 + Int32.ofInt (x1.toInt % 8) ||
                  s.marker == M_RST0 + Int32.ofInt (x2.toInt % 8)) = true then
                pure (3 : Int32)
              else if (s.marker == M_RST0 + Int32.ofInt (y1.toInt % 8) ||
                  s.marker == M_RST0 + Int32.ofInt (y2.toInt % 8)) = true then
                pure (2 : Int32)
              else
                pure (1 : Int32)
            k action)]
          change C.run (do
            let action ← if (s.marker == r_p1 || s.marker == r_p2) = true then pure (3 : Int32)
              else if (s.marker == r_m1 || s.marker == r_m2) = true then pure (2 : Int32)
              else pure (1 : Int32)
            k action) h = C.run (k 1) h
          simp [h3F, h2F, pure_bind_m]

theorem jpeg_resync_to_restart_safety : Goal.jpeg_resync_to_restart_safety := by
  intro h cinfo desired hv hdesLo hdesHi
  obtain ⟨bdc, rerr, rmrk, rs, dcs0, errs0, srcs0, rfl, henv0, hgetdc0, hszdc0, _hge0, _hsze0,
    hgetsrc0, hszsrc0, hbib0Lt, hlive0⟩ := resyncEnv_of_valid hv
  unfold jpeg_resync_to_restart
  have hdc0_0 : dcs0[0] = dcs0[0]! := by rw [← getElem!_pos dcs0 0 hszdc0]
  obtain ⟨dcs0', errs0', mrks0', srcs0', hgd0, hsd0, herr0, hmrk0, hsrc0, _⟩ := id henv0
  have herr0' : dcs0[0]!.err = .ref rerr 0 := by
    have : dcs0' = dcs0 := Option.some.inj (hgd0.symm.trans hgetdc0)
    subst this; exact herr0
  obtain ⟨h1, hwarn0, hb1, ⟨hde1, hsr1⟩, henv1⟩ :=
    warnms2_resync_ok (by omega) JWRN_MUST_RESYNC dcs0[0]!.unreadMarker desired henv0
  rw [Ptr.load_bind h _ 0 dcs0 _ hgetdc0 hszdc0, hdc0_0, herr0']
  rw [C.run_bind, hwarn0]; dsimp only
  let Inv : Nat → C.Heap → ResyncState → Prop := fun k hx s =>
    if s.done then k = 0
    else
      ∃ nwMax : Int,
        ResyncEnv hx bdc rerr rmrk rs nwMax ∧
        ∃ srcs dcs,
          C.Space.get hx (C.DecompRef.decomp bdc) = some dcs ∧ 0 < dcs.size ∧
          C.Space.get hx rs = some srcs ∧ 0 < srcs.size ∧
          srcs[0]!.bytesInBuffer.toNat < 2 ^ 20 ∧
          (srcs[0]!.bytesInBuffer = 0 ∨ LiveBytes hx srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer.toNat) ∧
          k = (if s.marker == M_EOI then 1 else srcs[0]!.bytesInBuffer.toNat + 2) ∧
          nwMax + 2 * (k : Int) + 2 < 2 ^ 63
  let Post : C.Heap → ResyncState → Prop := fun _ _ => True
  let initR : ResyncState := { done := false, ret := TRUE, marker := dcs0[0]!.unreadMarker }
  let k0 := if initR.marker == M_EOI then 1 else srcs0[0]!.bytesInBuffer.toNat + 2
  have hk0Lt : k0 < C.fuel := by
    change k0 < 2 ^ 64
    dsimp [k0]; split <;> omega
  have hinvInit : Inv k0 h1 initR := by
    simp only [Inv, initR, Bool.false_eq_true, ↓reduceIte]
    have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcs0 := by
      simp only [C.Space.get, hde1]; exact hgetdc0
    have hgetsrc1 : C.Space.get h1 rs = some srcs0 := by
      cases rs; simp only [C.Space.get, hsr1]; exact hgetsrc0
    have hlive1 : srcs0[0]!.bytesInBuffer = 0 ∨
        LiveBytes h1 srcs0[0]!.nextInputByte srcs0[0]!.bytesInBuffer.toNat := by
      rcases hlive0 with hb0 | hl
      · left; exact hb0
      · right; exact resyncEnv_bytes_irrel hb1 hl
    have hnwBound : (2 ^ 63 - 1 - 2 ^ 30 : Int) + 1 + 2 * (k0 : Int) + 2 < 2 ^ 63 := by
      dsimp [k0]; split <;> omega
    exact ⟨(2 ^ 63 - 1 - 2 ^ 30 : Int) + 1, henv1, srcs0, dcs0,
      hgetdc1, hszdc0, hgetsrc1, hszsrc0, hbib0Lt, hlive1, rfl, hnwBound⟩
  let bodyFn : ResyncState → C.M ResyncState := fun s => do
    let action ← do
      if s.marker < M_SOF0 then
        pure (2 : Int32)
      else if s.marker < M_RST0 || s.marker > M_RST7 then
        pure (3 : Int32)
      else
        let p1 ← i32Add desired 1
        let p2 ← i32Add desired 2
        let m1 ← i32Sub desired 1
        let m2 ← i32Sub desired 2
        let r_p1 := M_RST0 + Int32.ofInt (p1.toInt % 8)
        let r_p2 := M_RST0 + Int32.ofInt (p2.toInt % 8)
        let r_m1 := M_RST0 + Int32.ofInt (m1.toInt % 8)
        let r_m2 := M_RST0 + Int32.ofInt (m2.toInt % 8)
        if s.marker == r_p1 || s.marker == r_p2 then
          pure (3 : Int32)
        else if s.marker == r_m1 || s.marker == r_m2 then
          pure (2 : Int32)
        else
          pure (1 : Int32)
    let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
    tracems2 dc.err 4 JTRC_RECOVERY_ACTION s.marker action
    if action == 1 then
      Ptr.store (Ptr.ref (C.DecompRef.decomp bdc) 0) { dc with unreadMarker := 0 }
      return { done := true, ret := TRUE, marker := s.marker }
    else if action == 2 then
      let nm ← next_marker (Ptr.ref (C.DecompRef.decomp bdc) 0)
      if nm == 0 then
        return { done := true, ret := FALSE, marker := s.marker }
      let dc' ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
      return { done := false, ret := s.ret, marker := dc'.unreadMarker }
    else
      return { done := true, ret := TRUE, marker := s.marker }
  obtain ⟨st, h2, houter, _⟩ := cwhile_terminates
    (fun (s : ResyncState) => pure (!s.done, s))
    bodyFn
    Inv Post (fun k hx s hinv => by
      by_cases hdone : s.done = false
      · simp only [Inv, hdone, Bool.false_eq_true, ↓reduceIte] at hinv
        obtain ⟨nwMax, henv, srcs, dcs, hgetdc, hszdc, hgetsrc, hszsrc, hbibLt, hlive, hkEq, hnwBound⟩ := hinv
        have hcond : (!s.done) = true := by simp [hdone]
        refine ⟨true, s, hx, (by simp [C.run, hcond]), ?_⟩
        obtain ⟨act, hactRun, hactVal, hactEoi⟩ := resyncAction_ok desired hdesLo hdesHi s hx
        obtain ⟨dcsE, _errsE, _mrksE, _srcsE, hgdE, _hsdE, herrE, _⟩ := id henv
        have hdcEqE : dcsE = dcs := Option.some.inj (hgdE.symm.trans hgetdc)
        have herrDc : dcs[0]!.err = .ref rerr 0 := hdcEqE ▸ herrE
        have hdc_0 : dcs[0] = dcs[0]! := by rw [← getElem!_pos dcs 0 hszdc]
        obtain ⟨htr, htraceRun, hbTr, ⟨hdeTr, hsrTr⟩, henvTr⟩ :=
          tracems2_lvl4_resync_ok JTRC_RECOVERY_ACTION s.marker act henv
        have hkPos : 0 < k := by rw [hkEq]; split <;> omega
        rcases hactVal with rfl | rfl | rfl
        · let s' : ResyncState := { done := true, ret := TRUE, marker := s.marker }
          have hgetdcTr : C.Space.get htr (C.DecompRef.decomp bdc) = some dcs := by
            simp only [C.Space.get, hdeTr]; exact hgetdc
          have hroTr : C.Space.ro htr (C.DecompRef.decomp bdc) = false := rfl
          let dcNew := { dcs[0]! with err := .ref rerr 0, unreadMarker := 0 }
          let dcsNew := dcs.set! 0 dcNew
          let hFinal := C.Space.put htr (C.DecompRef.decomp bdc) dcsNew
          have hbody : C.run (bodyFn s) hx = .ok (s', hFinal) := by
            dsimp only [bodyFn]
            rw [hactRun]
            rw [Ptr.load_bind hx _ 0 dcs _ hgetdc hszdc, hdc_0, herrDc]
            rw [C.run_bind, htraceRun]; dsimp only
            have h1eq : ((1 : Int32) == 1) = true := by decide
            simp only [h1eq, ↓reduceIte]
            rw [Ptr.store_bind htr (C.DecompRef.decomp bdc) 0 dcNew dcs _ hgetdcTr hroTr hszdc]
            rfl
          exact ⟨0, s', hFinal, hbody, hkPos, by simp [Inv, s']⟩
        · have hneEoi : s.marker ≠ M_EOI := fun h => by
            have := hactEoi h
            exact absurd this (by decide)
          have hneEoiB : (s.marker == M_EOI) = false := Bool.eq_false_iff.mpr fun h =>
            hneEoi (by simpa using h)
          have hkVal : k = srcs[0]!.bytesInBuffer.toNat + 2 := by
            rw [hkEq, hneEoiB]; rfl
          have hgetdcTr : C.Space.get htr (C.DecompRef.decomp bdc) = some dcs := by
            simp only [C.Space.get, hdeTr]; exact hgetdc
          have hgetsrcTr : C.Space.get htr rs = some srcs := by
            cases rs; simp only [C.Space.get, hsrTr]; exact hgetsrc
          have hliveTr : srcs[0]!.bytesInBuffer = 0 ∨
              LiveBytes htr srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer.toNat := by
            rcases hlive with hb0 | hl
            · left; exact hb0
            · right; exact resyncEnv_bytes_irrel hbTr hl
          obtain ⟨nm, hnm, hnmRun, _hbNm, henvNm, hnmCase⟩ := next_marker_resync_ok (nwMax := nwMax)
            (by omega) henvTr srcs[0]!.bytesInBuffer srcs[0]!.nextInputByte
            ⟨srcs, hgetsrcTr, hszsrc, rfl, rfl⟩ hbibLt hliveTr
          have h2ne1 : ((2 : Int32) == 1) = false := by decide
          have h2eq2 : ((2 : Int32) == 2) = true := by decide
          rcases hnmCase with rfl | ⟨rfl, dcs', srcs', hgd', hsd', hgs', hss', hbibLt', hlive', hprog⟩
          · let s' : ResyncState := { done := true, ret := FALSE, marker := s.marker }
            have hbody : C.run (bodyFn s) hx = .ok (s', hnm) := by
              dsimp only [bodyFn]
              rw [hactRun]
              rw [Ptr.load_bind hx _ 0 dcs _ hgetdc hszdc, hdc_0, herrDc]
              rw [C.run_bind, htraceRun]; dsimp only
              simp only [h2ne1, Bool.false_eq_true, ↓reduceIte, h2eq2]
              rw [C.run_bind, hnmRun]; dsimp only
              have hfz : (FALSE == 0) = true := by decide
              simp only [hfz, ↓reduceIte]; rfl
            exact ⟨0, s', hnm, hbody, hkPos, by simp [Inv, s']⟩
          · let s' : ResyncState := { done := false, ret := s.ret, marker := dcs'[0]!.unreadMarker }
            let k' := if s'.marker == M_EOI then 1 else srcs'[0]!.bytesInBuffer.toNat + 2
            have hbody : C.run (bodyFn s) hx = .ok (s', hnm) := by
              dsimp only [bodyFn]
              rw [hactRun]
              rw [Ptr.load_bind hx _ 0 dcs _ hgetdc hszdc, hdc_0, herrDc]
              rw [C.run_bind, htraceRun]; dsimp only
              simp only [h2ne1, Bool.false_eq_true, ↓reduceIte, h2eq2]
              rw [C.run_bind, hnmRun]; dsimp only
              have htz : (TRUE == 0) = false := by decide
              simp only [htz, Bool.false_eq_true, ↓reduceIte]
              have hdc'_0 : dcs'[0] = dcs'[0]! := by rw [← getElem!_pos dcs' 0 hsd']
              rw [Ptr.load_bind hnm _ 0 dcs' _ hgd' hsd', hdc'_0]; rfl
            have hkLt : k' < k := by
              rcases hprog with hEoi | hBib
              · have hs'm : s'.marker = M_EOI := hEoi.1
                have hk1 : k' = 1 := by dsimp [k']; simp [hs'm]
                omega
              · have hkLe : k' ≤ srcs'[0]!.bytesInBuffer.toNat + 2 := by
                  dsimp [k']; split <;> omega
                omega
            have hnw' : nwMax + 2 + 2 * (k' : Int) + 2 < 2 ^ 63 := by omega
            refine ⟨k', s', hnm, hbody, hkLt, ?_⟩
            simp only [Inv, s', Bool.false_eq_true, ↓reduceIte]
            exact ⟨nwMax + 2, henvNm, srcs', dcs', hgd', hsd', hgs', hss', hbibLt', hlive', rfl, hnw'⟩
        · let s' : ResyncState := { done := true, ret := TRUE, marker := s.marker }
          have hbody : C.run (bodyFn s) hx = .ok (s', htr) := by
            dsimp only [bodyFn]
            rw [hactRun]
            rw [Ptr.load_bind hx _ 0 dcs _ hgetdc hszdc, hdc_0, herrDc]
            rw [C.run_bind, htraceRun]; dsimp only
            have h3ne1 : ((3 : Int32) == 1) = false := by decide
            have h3ne2 : ((3 : Int32) == 2) = false := by decide
            simp only [h3ne1, h3ne2, Bool.false_eq_true, ↓reduceIte]; rfl
          exact ⟨0, s', htr, hbody, hkPos, by simp [Inv, s']⟩
      · have hdoneT : s.done = true := by
          cases h : s.done with
          | false => exact False.elim (hdone h)
          | true => rfl
        have hcf : (!s.done) = false := by simp [hdoneT]
        exact ⟨false, s, hx, (by simp [C.run, hcf]), trivial⟩)
    hk0Lt hinvInit
  rw [C.run_bind]
  erw [houter]
  exact ⟨st.ret, h2, rfl⟩

end MozjpegF.Proof.Jdmarker
