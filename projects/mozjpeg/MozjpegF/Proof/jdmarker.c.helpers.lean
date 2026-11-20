import MozjpegF.Spec.Common.Types

/-!
# Helper lemmas for `jdmarker.c` termination and safety proofs (`MozjpegF`)

Generic bounded loop termination lemmas for `C.cwhile` / `C.cdoWhile`, plus `inputByte`,
`skip_to_ff`, `find_non_ff`, and `next_marker` step invariants.
-/

set_option autoImplicit false

namespace MozjpegF.Proof.JdmarkerHelpers
open C MozjpegF.Spec Mozjpeg.Jerror Mozjpeg.JerrorH Mozjpeg.Jdatasrc Mozjpeg.Jdmarker
open Mozjpeg.JpeglibH Mozjpeg.MoreCfg

/-! ## Generic bounded loop induction for `C.cwhile` and `C.cdoWhile` -/

theorem cwhile_go_terminates {σ : Type} (cond : σ → C.M (Bool × σ)) (body : σ → C.M σ)
    (Inv : Nat → C.Heap → σ → Prop) (Post : C.Heap → σ → Prop)
    (hstep : ∀ k h s, Inv k h s →
      ∃ c s' h1, C.run (cond s) h = .ok ((c, s'), h1) ∧
        (if c then ∃ k' s2 h2, C.run (body s') h1 = .ok (s2, h2) ∧ k' < k ∧ Inv k' h2 s2
         else Post h1 s')) :
    ∀ n k h s, k < n → Inv k h s →
      ∃ s' h', C.run (C.cwhile.go cond body n s) h = .ok (s', h') ∧ Post h' s' := by
  intro n
  induction n with
  | zero =>
    intro k _ _ hlt _
    omega
  | succ n ih =>
    intro k h s hlt hinv
    obtain ⟨c, s', h1, hcond, hrest⟩ := hstep k h s hinv
    unfold C.cwhile.go
    rw [C.run_bind, hcond]
    dsimp only
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨s', h1, rfl, hrest⟩
    | true =>
      simp only [↓reduceIte]
      obtain ⟨k', s2, h2, hbody, hk', hinv'⟩ := hrest
      rw [C.run_bind, hbody]
      exact ih k' h2 s2 (by omega) hinv'

theorem cwhile_terminates {σ : Type} (cond : σ → C.M (Bool × σ)) (body : σ → C.M σ)
    (Inv : Nat → C.Heap → σ → Prop) (Post : C.Heap → σ → Prop)
    (hstep : ∀ k h s, Inv k h s →
      ∃ c s' h1, C.run (cond s) h = .ok ((c, s'), h1) ∧
        (if c then ∃ k' s2 h2, C.run (body s') h1 = .ok (s2, h2) ∧ k' < k ∧ Inv k' h2 s2
         else Post h1 s'))
    {k : Nat} {h : C.Heap} {s : σ} (hlt : k < C.fuel) (hinv : Inv k h s) :
    ∃ s' h', C.run (C.cwhile cond body s) h = .ok (s', h') ∧ Post h' s' :=
  cwhile_go_terminates cond body Inv Post hstep C.fuel k h s hlt hinv

theorem cdoWhile_go_terminates {σ : Type} (body : σ → C.M σ) (cond : σ → C.M (Bool × σ))
    (Inv : Nat → C.Heap → σ → Prop) (Post : C.Heap → σ → Prop)
    (hstep : ∀ k h s, Inv k h s →
      ∃ s1 h1 c s2 h2,
        C.run (body s) h = .ok (s1, h1) ∧
        C.run (cond s1) h1 = .ok ((c, s2), h2) ∧
        (if c then ∃ k', k' < k ∧ Inv k' h2 s2 else Post h2 s2)) :
    ∀ n k h s, k < n → Inv k h s →
      ∃ s' h', C.run (C.cdoWhile.go body cond n s) h = .ok (s', h') ∧ Post h' s' := by
  intro n
  induction n with
  | zero =>
    intro k _ _ hlt _
    omega
  | succ n ih =>
    intro k h s hlt hinv
    obtain ⟨s1, h1, c, s2, h2, hbody, hcond, hrest⟩ := hstep k h s hinv
    unfold C.cdoWhile.go
    rw [C.run_bind, hbody]
    dsimp only
    rw [C.run_bind, hcond]
    dsimp only
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨s2, h2, rfl, hrest⟩
    | true =>
      simp only [↓reduceIte]
      obtain ⟨k', hk', hinv'⟩ := hrest
      exact ih k' h2 s2 (by omega) hinv'

theorem cdoWhile_terminates {σ : Type} (body : σ → C.M σ) (cond : σ → C.M (Bool × σ))
    (Inv : Nat → C.Heap → σ → Prop) (Post : C.Heap → σ → Prop)
    (hstep : ∀ k h s, Inv k h s →
      ∃ s1 h1 c s2 h2,
        C.run (body s) h = .ok (s1, h1) ∧
        C.run (cond s1) h1 = .ok ((c, s2), h2) ∧
        (if c then ∃ k', k' < k ∧ Inv k' h2 s2 else Post h2 s2))
    {k : Nat} {h : C.Heap} {s : σ} (hlt : k < C.fuel) (hinv : Inv k h s) :
    ∃ s' h', C.run (C.cdoWhile body cond s) h = .ok (s', h') ∧ Post h' s' :=
  cdoWhile_go_terminates body cond Inv Post hstep C.fuel k h s hlt hinv

/-! ## Heap environment invariant and primitive operation lemmas -/

/-- Live object-graph environment invariant for `next_marker` and `jpeg_resync_to_restart`. -/
def ResyncEnv (h : C.Heap) (bdc : Nat) (rerr : C.ErrRef) (rmrk : C.MarkerRef) (rs : C.SrcRef)
    (nwMax : Int) : Prop :=
  ∃ dcs errs mrks srcs,
    C.Space.get h (C.DecompRef.decomp bdc) = some dcs ∧ 0 < dcs.size ∧
    dcs[0]!.err = .ref rerr 0 ∧
    dcs[0]!.marker = .ref rmrk 0 ∧
    dcs[0]!.src = .ref rs 0 ∧
    C.Space.get h rerr = some errs ∧ 0 < errs.size ∧
    0 ≤ errs[0]!.numWarnings.toInt ∧ errs[0]!.numWarnings.toInt ≤ nwMax ∧
    C.Space.get h rmrk = some mrks ∧ 0 < mrks.size ∧
    C.Space.get h rs = some srcs ∧ 0 < srcs.size ∧
    (srcs[0]!.fillInputBuffer = .fn "suspend_input" ∨
      srcs[0]!.fillInputBuffer = .fn "fill_mem_input_buffer")

theorem resyncEnv_mono {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nw1 nw2 : Int} (hle : nw1 ≤ nw2)
    (henv : ResyncEnv h bdc rerr rmrk rs nw1) :
    ResyncEnv h bdc rerr rmrk rs nw2 := by
  obtain ⟨dcs, errs, mrks, srcs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := henv
  exact ⟨dcs, errs, mrks, srcs, h1, h2, h3, h4, h5, h6, h7, h8, Int.le_trans h9 hle, h10, h11, h12, h13, h14⟩

def SameBytes (h' h : C.Heap) : Prop :=
  h'.bytes = h.bytes ∧ h'.consts = h.consts

theorem sameBytes_refl (h : C.Heap) : SameBytes h h := ⟨rfl, rfl⟩

theorem sameBytes_trans {h3 h2 h1 : C.Heap} (h32 : SameBytes h3 h2) (h21 : SameBytes h2 h1) :
    SameBytes h3 h1 := ⟨h32.1.trans h21.1, h32.2.trans h21.2⟩

theorem resyncEnv_bytes_irrel {h h' : C.Heap} (hb : SameBytes h' h)
    {p : C.BPtr} {n : Nat} (hl : LiveBytes h p n) : LiveBytes h' p n := by
  obtain ⟨r, off, data, hp, hg, hle⟩ := hl
  refine ⟨r, off, data, hp, ?_, hle⟩
  cases r with
  | heap b => simp only [C.Space.get, C.Heap.getBytes] at hg ⊢; rw [hb.1]; exact hg
  | const b => simp only [C.Space.get, C.Heap.getBytes] at hg ⊢; rw [hb.2]; exact hg
  | const_eof => exact hg
  | str _ => exact hg

theorem resyncEnv_of_valid {h : C.Heap} {cinfo : C.DecompPtr}
    (hv : ValidDecompResyncInput h cinfo) :
    ∃ bdc rerr rmrk rs dcs errs srcs,
      cinfo = .ref (.decomp bdc) 0 ∧
      ResyncEnv h bdc rerr rmrk rs (2 ^ 63 - 1 - 2 ^ 30) ∧
      C.Space.get h (C.DecompRef.decomp bdc) = some dcs ∧ 0 < dcs.size ∧
      C.Space.get h rerr = some errs ∧ 0 < errs.size ∧
      C.Space.get h rs = some srcs ∧ 0 < srcs.size ∧
      srcs[0]!.bytesInBuffer.toNat < 2 ^ 20 ∧
      (srcs[0]!.bytesInBuffer = 0 ∨ LiveBytes h srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer.toNat) := by
  obtain ⟨hcore, rc, dcs, dc, rs, srcs, src, rerr, errs,
    hc, hgetdc, hszdc, hdc, hsrcp, hgetsrc, hszsrc, hsrc, herrp, hgeterr, hszerr,
    hnw0, hnwHi, hbibLt, hbibLive, hfill⟩ := hv
  obtain ⟨rc', dcs', dc', _rm, _mems, _rmas, _masters, _ric, _ics, rmrk, mrks,
    hc', hgetdc', hszdc', hdc', _herrV, _hmem, _hgetmem, _hszmem, _hmas, _hgetmas, _hszmas,
    _hin, _hgetin, _hszin, hmrk, hgetmrk, hszmrk, _⟩ := hcore
  subst hc
  have hrcEq : rc = rc' := by cases hc'; rfl
  subst hrcEq
  have hdcsEq : dcs = dcs' := Option.some.inj (hgetdc.symm.trans hgetdc')
  subst hdcsEq
  have hdcEq : dc = dc' := hdc.trans hdc'.symm
  subst hdcEq
  cases rc with | decomp bdc =>
  have hnwLe : errs[0]!.numWarnings.toInt ≤ 2 ^ 63 - 1 - 2 ^ 30 := by omega
  refine ⟨bdc, rerr, rmrk, rs, dcs, errs, srcs, rfl, ?_, hgetdc, hszdc, hgeterr, hszerr, hgetsrc, hszsrc,
    hsrc ▸ hbibLt, hsrc ▸ hbibLive⟩
  exact ⟨dcs, errs, mrks, srcs, hgetdc, hszdc,
    hdc ▸ herrp, hdc ▸ hmrk, hdc ▸ hsrcp,
    hgeterr, hszerr, hnw0, hnwLe,
    hgetmrk, hszmrk, hgetsrc, hszsrc,
    hsrc ▸ hfill⟩

private theorem warnms_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (hmw : nwMax + 1 < 2 ^ 63) (code : Int32)
    (henv : ResyncEnv h bdc rerr rmrk rs nwMax) :
    ∃ h',
      C.run (warnms (.ref rerr 0) code) h = .ok ((), h') ∧
      SameBytes h' h ∧
      h'.srcs = h.srcs ∧
      ResyncEnv h' bdc rerr rmrk rs (nwMax + 1) := by
  obtain ⟨dcs, errs, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp, hgeterr, hszerr,
    hnw0, hnwLe, hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩ := henv
  unfold warnms emitMessage i64Add checkI64
  have hgeterr' : C.Space.get h rerr = some errs := hgeterr
  have hro_err : C.Space.ro h rerr = false := by cases rerr; rfl
  let e1 := { errs[0] with msgCode := code }
  let errs1 := errs.set! 0 e1
  let h1 := C.Space.put h rerr errs1
  have hgeterr1 : C.Space.get h1 rerr = some errs1 := by cases rerr; simp [h1, C.Space.get, C.Space.put]
  have hszerr1 : 0 < errs1.size := by simp [errs1, hszerr]
  have hro_err1 : C.Space.ro h1 rerr = false := by cases rerr; rfl
  have he1_0 : errs1[0] = e1 := by simp [errs1, Array.set!_eq_setIfInBounds]
  have hnweq : errs[0].numWarnings = errs[0]!.numWarnings := by
    rw [← getElem!_pos errs 0 hszerr]
  have hone : (1 : Int64).toInt = 1 := rfl
  have hrange : -(2 ^ 63 : Int) ≤ e1.numWarnings.toInt + (1 : Int64).toInt ∧
      e1.numWarnings.toInt + (1 : Int64).toInt < 2 ^ 63 := by
    change -(2 ^ 63 : Int) ≤ errs[0].numWarnings.toInt + (1 : Int64).toInt ∧
      errs[0].numWarnings.toInt + (1 : Int64).toInt < 2 ^ 63
    rw [hnweq, hone]; omega
  let e2 := { e1 with numWarnings := Int64.ofInt (e1.numWarnings.toInt + (1 : Int64).toInt) }
  let errs2 := errs1.set! 0 e2
  let h2 := C.Space.put h1 rerr errs2
  have hb2 : SameBytes h2 h := by cases rerr; exact ⟨rfl, rfl⟩
  have hs2 : h2.srcs = h.srcs := by cases rerr; rfl
  refine ⟨h2, ?_, hb2, hs2, ?_⟩
  · rw [Ptr.load_bind h rerr 0 errs _ hgeterr' hszerr]
    rw [Ptr.store_bind h rerr 0 e1 errs _ hgeterr' hro_err hszerr]
    rw [Ptr.load_bind h1 rerr 0 errs1 _ hgeterr1 hszerr1, he1_0]
    have hlt : ((-1 : Int32) < 0) = true := by decide
    simp only [hlt, ↓reduceIte, hrange, and_self, pure_bind_m]
    simp only [C.run, Ptr.store, hgeterr1, hro_err1, hszerr1, ↓reduceIte,
      C.Space.modify_eq h1 rerr errs1 _ hgeterr1]
    rfl
  · have hnw2 : (errs2[0]!).numWarnings.toInt = errs[0]!.numWarnings.toInt + 1 := by
      have he2_0 : errs2[0]! = e2 := by
        rw [getElem!_pos _ 0 (by simp [errs2, hszerr1])]
        simp [errs2, Array.set!_eq_setIfInBounds]
      rw [he2_0]
      change (Int64.ofInt (errs[0].numWarnings.toInt + (1 : Int64).toInt)).toInt = errs[0]!.numWarnings.toInt + 1
      rw [hnweq, hone, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    cases rerr with | err berr =>
    refine ⟨dcs, errs2, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp,
      (by simp [h2, C.Space.get, C.Space.put]), (by simp [errs2, hszerr1]),
      (by omega), (by omega), hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩

theorem warnms2_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (hmw : nwMax + 1 < 2 ^ 63) (code p1 p2 : Int32)
    (henv : ResyncEnv h bdc rerr rmrk rs nwMax) :
    ∃ h',
      C.run (warnms2 (.ref rerr 0) code p1 p2) h = .ok ((), h') ∧
      SameBytes h' h ∧
      (h'.decomps = h.decomps ∧ h'.srcs = h.srcs) ∧
      ResyncEnv h' bdc rerr rmrk rs (nwMax + 1) := by
  obtain ⟨dcs, errs, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp, hgeterr, hszerr,
    hnw0, hnwLe, hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩ := henv
  unfold warnms2 emitMessage i64Add checkI64
  have hgeterr' : C.Space.get h rerr = some errs := hgeterr
  have hro_err : C.Space.ro h rerr = false := by cases rerr; rfl
  let parm := (errs[0].msgParmI.set! 0 p1).set! 1 p2
  let e1 := { errs[0] with msgCode := code, msgParmI := parm }
  let errs1 := errs.set! 0 e1
  let h1 := C.Space.put h rerr errs1
  have hgeterr1 : C.Space.get h1 rerr = some errs1 := by cases rerr; simp [h1, C.Space.get, C.Space.put]
  have hszerr1 : 0 < errs1.size := by simp [errs1, hszerr]
  have hro_err1 : C.Space.ro h1 rerr = false := by cases rerr; rfl
  have he1_0 : errs1[0] = e1 := by simp [errs1, Array.set!_eq_setIfInBounds]
  have hnweq : errs[0].numWarnings = errs[0]!.numWarnings := by
    rw [← getElem!_pos errs 0 hszerr]
  have hone : (1 : Int64).toInt = 1 := rfl
  have hrange : -(2 ^ 63 : Int) ≤ e1.numWarnings.toInt + (1 : Int64).toInt ∧
      e1.numWarnings.toInt + (1 : Int64).toInt < 2 ^ 63 := by
    change -(2 ^ 63 : Int) ≤ errs[0].numWarnings.toInt + (1 : Int64).toInt ∧
      errs[0].numWarnings.toInt + (1 : Int64).toInt < 2 ^ 63
    rw [hnweq, hone]; omega
  let e2 := { e1 with numWarnings := Int64.ofInt (e1.numWarnings.toInt + (1 : Int64).toInt) }
  let errs2 := errs1.set! 0 e2
  let h2 := C.Space.put h1 rerr errs2
  have hb2 : SameBytes h2 h := by cases rerr; exact ⟨rfl, rfl⟩
  have hds2 : h2.decomps = h.decomps ∧ h2.srcs = h.srcs := by cases rerr; exact ⟨rfl, rfl⟩
  refine ⟨h2, ?_, hb2, hds2, ?_⟩
  · rw [Ptr.load_bind h rerr 0 errs _ hgeterr' hszerr]
    rw [Ptr.store_bind h rerr 0 e1 errs _ hgeterr' hro_err hszerr]
    rw [Ptr.load_bind h1 rerr 0 errs1 _ hgeterr1 hszerr1, he1_0]
    have hlt : ((-1 : Int32) < 0) = true := by decide
    simp only [hlt, ↓reduceIte, hrange, and_self, pure_bind_m]
    simp only [C.run, Ptr.store, hgeterr1, hro_err1, hszerr1, ↓reduceIte,
      C.Space.modify_eq h1 rerr errs1 _ hgeterr1]
    rfl
  · have hnw2 : (errs2[0]!).numWarnings.toInt = errs[0]!.numWarnings.toInt + 1 := by
      have he2_0 : errs2[0]! = e2 := by
        rw [getElem!_pos _ 0 (by simp [errs2, hszerr1])]
        simp [errs2, Array.set!_eq_setIfInBounds]
      rw [he2_0]
      change (Int64.ofInt (errs[0].numWarnings.toInt + (1 : Int64).toInt)).toInt = errs[0]!.numWarnings.toInt + 1
      rw [hnweq, hone, Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    cases rerr with | err berr =>
    refine ⟨dcs, errs2, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp,
      (by simp [h2, C.Space.get, C.Space.put]), (by simp [errs2, hszerr1]),
      (by omega), (by omega), hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩

theorem tracems2_lvl4_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (code p1 p2 : Int32)
    (henv : ResyncEnv h bdc rerr rmrk rs nwMax) :
    ∃ h',
      C.run (tracems2 (.ref rerr 0) 4 code p1 p2) h = .ok ((), h') ∧
      SameBytes h' h ∧
      (h'.decomps = h.decomps ∧ h'.srcs = h.srcs) ∧
      ResyncEnv h' bdc rerr rmrk rs nwMax := by
  obtain ⟨dcs, errs, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp, hgeterr, hszerr,
    hnw0, hnwLe, hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩ := henv
  unfold tracems2 emitMessage
  have hgeterr' : C.Space.get h rerr = some errs := hgeterr
  have hro_err : C.Space.ro h rerr = false := by cases rerr; rfl
  let parm := (errs[0].msgParmI.set! 0 p1).set! 1 p2
  let e1 := { errs[0] with msgCode := code, msgParmI := parm }
  let errs1 := errs.set! 0 e1
  let h1 := C.Space.put h rerr errs1
  have hgeterr1 : C.Space.get h1 rerr = some errs1 := by cases rerr; simp [h1, C.Space.get, C.Space.put]
  have hszerr1 : 0 < errs1.size := by simp [errs1, hszerr]
  have he1_0 : errs1[0] = e1 := by simp [errs1, Array.set!_eq_setIfInBounds]
  have hb1 : SameBytes h1 h := by cases rerr; exact ⟨rfl, rfl⟩
  have hds1 : h1.decomps = h.decomps ∧ h1.srcs = h.srcs := by cases rerr; exact ⟨rfl, rfl⟩
  refine ⟨h1, ?_, hb1, hds1, ?_⟩
  · rw [Ptr.load_bind h rerr 0 errs _ hgeterr' hszerr]
    rw [Ptr.store_bind h rerr 0 e1 errs _ hgeterr' hro_err hszerr]
    rw [Ptr.load_bind h1 rerr 0 errs1 _ hgeterr1 hszerr1, he1_0]
    have hge0 : ((4 : Int32) < 0) = false := by decide
    simp only [hge0, Bool.false_eq_true, ↓reduceIte]
    rfl
  · have hnw1 : (errs1[0]!).numWarnings = errs[0]!.numWarnings := by
      have he1_bang : errs1[0]! = e1 := by
        rw [getElem!_pos _ 0 hszerr1]
        simp [errs1, Array.set!_eq_setIfInBounds]
      rw [he1_bang]
      dsimp [e1]
      rw [← getElem!_pos errs 0 hszerr]
    refine ⟨dcs, errs1, mrks, srcs, ?_, hszdc, herrp, hmrkp, hsrcp, ?_, hszerr1, ?_, ?_, ?_, hszmrk, ?_, hszsrc, hfill⟩
    · cases rerr; exact hgetdc
    · cases rerr; simp [h1, C.Space.get, C.Space.put]
    · rw [hnw1]; exact hnw0
    · rw [hnw1]; exact hnwLe
    · cases rerr; exact hgetmrk
    · cases rerr; exact hgetsrc

theorem inputSync_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (nib : C.BPtr) (bib : UInt64)
    (henv : ResyncEnv h bdc rerr rmrk rs nwMax) :
    ∃ h',
      C.run (inputSync (.ref (.decomp bdc) 0) nib bib) h = .ok ((), h') ∧
      SameBytes h' h ∧
      ResyncEnv h' bdc rerr rmrk rs nwMax := by
  obtain ⟨dcs, errs, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp, hgeterr, hszerr,
    hnw0, hnwLe, hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩ := henv
  unfold inputSync
  have hdc0 : dcs[0] = dcs[0]! := by rw [← getElem!_pos dcs 0 hszdc]
  have hgetsrc' : C.Space.get h rs = some srcs := hgetsrc
  have hro_src : C.Space.ro h rs = false := by cases rs; rfl
  let src1 := { srcs[0] with nextInputByte := nib, bytesInBuffer := bib }
  let srcs1 := srcs.set! 0 src1
  let h1 := C.Space.put h rs srcs1
  have hb1 : SameBytes h1 h := by cases rs; exact ⟨rfl, rfl⟩
  refine ⟨h1, ?_, hb1, ?_⟩
  · rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hsrcp]
    rw [Ptr.load_bind h rs 0 srcs _ hgetsrc' hszsrc]
    simp only [C.run, Ptr.store, hgetsrc', hro_src, hszsrc, ↓reduceIte,
      C.Space.modify_eq h rs srcs _ hgetsrc']
    rfl
  · have hfill1 : srcs1[0]!.fillInputBuffer = srcs[0]!.fillInputBuffer := by
      have hs1_0 : srcs1[0]! = src1 := by
        rw [getElem!_pos _ 0 (by simp [srcs1, hszsrc])]
        simp [srcs1, Array.set!_eq_setIfInBounds]
      rw [hs1_0]
      dsimp [src1]
      rw [← getElem!_pos srcs 0 hszsrc]
    refine ⟨dcs, errs, mrks, srcs1, ?_, hszdc, herrp, hmrkp, hsrcp, ?_, hszerr, hnw0, hnwLe, ?_, hszmrk, ?_, by simp [srcs1, hszsrc], ?_⟩
    · cases rs; exact hgetdc
    · cases rs; exact hgeterr
    · cases rs; exact hgetmrk
    · cases rs; simp [h1, C.Space.get, C.Space.put]
    · rw [hfill1]; exact hfill

theorem markerDiscardedInc_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (delta : UInt32)
    (henv : ResyncEnv h bdc rerr rmrk rs nwMax) :
    ∃ h',
      (∀ {α : Type} (k : C.M α),
        C.run (do
          let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
          let mrk ← Ptr.load dc.marker
          Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + delta }
          k) h = C.run k h') ∧
      SameBytes h' h ∧
      ResyncEnv h' bdc rerr rmrk rs nwMax := by
  obtain ⟨dcs, errs, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp, hgeterr, hszerr,
    hnw0, hnwLe, hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩ := henv
  have hdc0 : dcs[0] = dcs[0]! := by rw [← getElem!_pos dcs 0 hszdc]
  have hgetmrk' : C.Space.get h rmrk = some mrks := hgetmrk
  have hro_mrk : C.Space.ro h rmrk = false := by cases rmrk; rfl
  let mrk1 := { mrks[0] with discardedBytes := mrks[0].discardedBytes + delta }
  let mrks1 := mrks.set! 0 mrk1
  let h1 := C.Space.put h rmrk mrks1
  have hb1 : SameBytes h1 h := by cases rmrk; exact ⟨rfl, rfl⟩
  refine ⟨h1, ?_, hb1, ?_⟩
  · intro α k
    rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hmrkp]
    rw [Ptr.load_bind h rmrk 0 mrks _ hgetmrk' hszmrk]
    rw [Ptr.store_bind h rmrk 0 mrk1 mrks _ hgetmrk' hro_mrk hszmrk]
  · refine ⟨dcs, errs, mrks1, srcs, ?_, hszdc, herrp, hmrkp, hsrcp, ?_, hszerr, hnw0, hnwLe, ?_, by simp [mrks1, hszmrk], ?_, hszsrc, hfill⟩
    · cases rmrk; exact hgetdc
    · cases rmrk; exact hgeterr
    · cases rmrk; simp [h1, C.Space.get, C.Space.put]
    · cases rmrk; exact hgetsrc

theorem markerDiscardedZero_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (henv : ResyncEnv h bdc rerr rmrk rs nwMax) :
    ∃ h',
      (∀ {α : Type} (k : C.M α),
        C.run (do
          let mrk2 ← Ptr.load (.ref rmrk 0)
          Ptr.store (.ref rmrk 0) { mrk2 with discardedBytes := 0 }
          k) h = C.run k h') ∧
      SameBytes h' h ∧
      ResyncEnv h' bdc rerr rmrk rs nwMax := by
  obtain ⟨dcs, errs, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp, hgeterr, hszerr,
    hnw0, hnwLe, hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩ := henv
  have hgetmrk' : C.Space.get h rmrk = some mrks := hgetmrk
  have hro_mrk : C.Space.ro h rmrk = false := by cases rmrk; rfl
  let mrk1 := { mrks[0] with discardedBytes := 0 }
  let mrks1 := mrks.set! 0 mrk1
  let h1 := C.Space.put h rmrk mrks1
  have hb1 : SameBytes h1 h := by cases rmrk; exact ⟨rfl, rfl⟩
  refine ⟨h1, ?_, hb1, ?_⟩
  · intro α k
    rw [Ptr.load_bind h rmrk 0 mrks _ hgetmrk' hszmrk]
    rw [Ptr.store_bind h rmrk 0 mrk1 mrks _ hgetmrk' hro_mrk hszmrk]
  · refine ⟨dcs, errs, mrks1, srcs, ?_, hszdc, herrp, hmrkp, hsrcp, ?_, hszerr, hnw0, hnwLe, ?_, by simp [mrks1, hszmrk], ?_, hszsrc, hfill⟩
    · cases rmrk; exact hgetdc
    · cases rmrk; exact hgeterr
    · cases rmrk; simp [h1, C.Space.get, C.Space.put]
    · cases rmrk; exact hgetsrc

private theorem uint64_toNat_pos {x : UInt64} (hne : x ≠ 0) : 0 < x.toNat := by
  by_cases h : x.toNat = 0
  · exfalso; apply hne; exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)
  · exact Nat.pos_of_ne_zero h

private theorem uint64_toNat_sub_one {x : UInt64} (hne : x ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hpos : 0 < x.toNat := uint64_toNat_pos hne
  rw [UInt64.toNat_sub_of_le x 1 (UInt64.le_iff_toNat_le.mpr (by change 1 ≤ x.toNat; omega))]
  rfl

def SameConstEof (nib0 nib1 : C.BPtr) (bib0 bib1 : UInt64) : Prop :=
  (match nib1 with | .ref .const_eof _ => true | _ => false) =
    (match nib0 with | .ref .const_eof _ => true | _ => false) ∧
  (∀ off1, nib1 = .ref .const_eof off1 →
    ∃ off0, nib0 = .ref .const_eof off0 ∧ off0 + bib0.toNat = off1 + bib1.toNat)

theorem sameConstEof_refl (nib : C.BPtr) (bib : UInt64) : SameConstEof nib nib bib bib :=
  ⟨rfl, fun off1 h => ⟨off1, h, rfl⟩⟩

theorem sameConstEof_trans {n0 n1 n2 : C.BPtr} {b0 b1 b2 : UInt64}
    (h01 : SameConstEof n0 n1 b0 b1) (h12 : SameConstEof n1 n2 b1 b2) :
    SameConstEof n0 n2 b0 b2 := by
  refine ⟨h12.1.trans h01.1, fun off2 hn2 => ?_⟩
  obtain ⟨off1, hn1, hsum1⟩ := h12.2 off2 hn2
  obtain ⟨off0, hn0, hsum0⟩ := h01.2 off1 hn1
  exact ⟨off0, hn0, hsum0.trans hsum1⟩

theorem sameConstEof_fwd {n0 n1 : C.BPtr} {b0 b1 : UInt64}
    (hsce : SameConstEof n0 n1 b0 b1) {off0 : Nat} (hn0 : n0 = .ref .const_eof off0) :
    ∃ off1, n1 = .ref .const_eof off1 ∧ off1 + b1.toNat = off0 + b0.toNat := by
  have hm := hsce.1
  rw [hn0] at hm
  cases hn1 : n1 with
  | ref r off1 =>
    cases r with
    | const_eof =>
      obtain ⟨off0', hn0', hsum⟩ := hsce.2 off1 hn1
      have h0Eq : off0' = off0 := by cases hn0'.symm.trans hn0; rfl
      exact ⟨off1, rfl, by omega⟩
    | _ => simp [hn1] at hm
  | _ => simp [hn1] at hm

theorem inputByte_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (nib : C.BPtr) (bib : UInt64)
    (hmw : bib = 0 → nwMax + 1 < 2 ^ 63)
    (henv : ResyncEnv h bdc rerr rmrk rs nwMax)
    (hlive : bib = 0 ∨ LiveBytes h nib bib.toNat) :
    ∃ res h',
      C.run (inputByte (.ref (.decomp bdc) 0) nib bib) h = .ok (res, h') ∧
      SameBytes h' h ∧
      match res with
      | none =>
        bib = 0 ∧ h' = h ∧ ResyncEnv h' bdc rerr rmrk rs nwMax
      | some (c, nib1, bib1) =>
        if bib != 0 then
          bib1.toNat = bib.toNat - 1 ∧
          (bib1 = 0 ∨ LiveBytes h' nib1 bib1.toNat) ∧
          (nib = .ref .const_eof 1 → bib = 1 → c = 0xd9 ∧ nib1 = .ref .const_eof 2 ∧ bib1 = 0) ∧
          SameConstEof nib nib1 bib bib1 ∧
          h' = h ∧ ResyncEnv h' bdc rerr rmrk rs nwMax
        else
          c = 0xFF ∧ nib1 = .ref .const_eof 1 ∧ bib1 = 1 ∧
          LiveBytes h' nib1 1 ∧
          ResyncEnv h' bdc rerr rmrk rs (nwMax + 1) := by
  by_cases hzero : (bib != 0) = true
  · have hne : bib ≠ 0 := fun heq => by simp [heq] at hzero
    rcases hlive with rfl | ⟨r, off, data, hp, hg, hlen⟩
    · exact False.elim (hne rfl)
    · have hpos : 0 < bib.toNat := uint64_toNat_pos hne
      have hlt : off < data.size := by omega
      have haddBounds : off ≤ data.size ∧ 0 ≤ (off : Int) + 1 ∧ (off : Int) + 1 ≤ (data.size : Int) := by omega
      have hload : C.run (Ptr.load (.ref r off)) h = .ok (data[off], h) := by
        simp [C.run, Ptr.load, hg, hlt]
      have hadd : C.run (Ptr.add (.ref r off) 1) h = .ok (.ref r (off + 1), h) := by
        simp only [C.run, Ptr.add, hg, haddBounds, and_self, ↓reduceIte]
        rfl
      have hsub : (bib - 1).toNat = bib.toNat - 1 := uint64_toNat_sub_one hne
      have hrun : C.run (inputByte (.ref (.decomp bdc) 0) nib bib) h =
          .ok (some (Int32.ofNat (data[off]).toNat, .ref r (off + 1), bib - 1), h) := by
        unfold inputByte makeByteAvail
        simp only [hzero, ↓reduceIte, pure_bind_m, hp]
        rw [C.run_bind, hload]; dsimp only
        rw [C.run_bind, hadd]; rfl
      refine ⟨_, h, hrun, sameBytes_refl h, ?_⟩
      simp only [hzero, ↓reduceIte]
      refine ⟨hsub, ?_, ?_, ?_, (by first | rfl | trivial), henv⟩
      · by_cases hb1 : bib - 1 = 0
        · left; exact hb1
        · right; refine ⟨r, off + 1, data, rfl, hg, by omega⟩
      · intro hceof hbib1
        have hr : r = .const_eof ∧ off = 1 := by
          have : (.ref r off : C.BPtr) = .ref .const_eof 1 := hp.symm.trans hceof
          cases this; exact ⟨rfl, rfl⟩
        rcases hr with ⟨rfl, rfl⟩
        have hdata : data = #[0xff, 0xd9, 0, 0] := Option.some.inj (hg.symm.trans rfl)
        subst hdata
        subst hbib1
        have hbyte : (#[0xff, 0xd9, 0, 0] : Array UInt8)[1] = 0xd9 := rfl
        rw [hbyte]
        exact ⟨rfl, rfl, rfl⟩
      · refine ⟨?_, fun off1 h => ?_⟩
        · rw [hp]; cases r <;> rfl
        · cases h; exact ⟨off, hp, by omega⟩
  · have hbf : (bib != 0) = false := Bool.eq_false_iff.mpr hzero
    have hbib0 : bib = 0 := by simpa using hbf
    subst hbib0
    obtain ⟨dcs, errs, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp, hgeterr, hszerr,
      hnw0, hnwLe, hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩ := henv
    have henv0 : ResyncEnv h bdc rerr rmrk rs nwMax :=
      ⟨dcs, errs, mrks, srcs, hgetdc, hszdc, herrp, hmrkp, hsrcp, hgeterr, hszerr,
        hnw0, hnwLe, hgetmrk, hszmrk, hgetsrc, hszsrc, hfill⟩
    have hdc0 : dcs[0] = dcs[0]! := by rw [← getElem!_pos dcs 0 hszdc]
    have hsrc0 : srcs[0] = srcs[0]! := by rw [← getElem!_pos srcs 0 hszsrc]
    rcases hfill with hsusp | hfillm
    · have hrun : C.run (inputByte (.ref (.decomp bdc) 0) nib 0) h = .ok (none, h) := by
        unfold inputByte makeByteAvail
        simp only [hbf, Bool.false_eq_true, ↓reduceIte]
        rw [C.run_bind, Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hsrcp]
        rw [Ptr.load_bind h rs 0 srcs _ hgetsrc hszsrc, hsrc0, hsusp]
        rfl
      exact ⟨none, h, hrun, sameBytes_refl h, rfl, rfl, henv0⟩
    · obtain ⟨h1, hwarn, hb1, hsrceq1, henv1⟩ := warnms_resync_ok (hmw rfl) JWRN_JPEG_EOF henv0
      obtain ⟨dcs1, errs1, mrks1, srcs1, hgetdc1, hszdc1, herrp1, hmrkp1, hsrcp1, hgeterr1, hszerr1,
        hnw01, hnwLe1, hgetmrk1, hszmrk1, hgetsrc1, hszsrc1, _hfill1⟩ := henv1
      have hsrcsEq : srcs1 = srcs := Option.some.inj (by
        have ha : C.Space.get h1 rs = some srcs1 := hgetsrc1
        have hb : C.Space.get h1 rs = some srcs := by cases rs; simp only [C.Space.get, hsrceq1]; exact hgetsrc
        exact ha.symm.trans hb)
      have hro_src1 : C.Space.ro h1 rs = false := by cases rs; rfl
      let src2 := { srcs1[0] with nextInputByte := .ref .const_eof 0, bytesInBuffer := 2 }
      let srcs2 := srcs1.set! 0 src2
      let h2 := C.Space.put h1 rs srcs2
      have hb2 : SameBytes h2 h := by cases rs; exact hb1
      have hgetsrc2 : C.Space.get h2 rs = some srcs2 := by cases rs; simp [h2, C.Space.get, C.Space.put]
      have hszsrc2 : 0 < srcs2.size := by simp [srcs2, hszsrc1]
      have hsrc2_0 : srcs2[0] = src2 := by simp [srcs2, Array.set!_eq_setIfInBounds]
      have hfill2 : srcs2[0]!.fillInputBuffer = .fn "fill_mem_input_buffer" := by
        have hbang : srcs2[0]! = src2 := by
          rw [getElem!_pos _ 0 hszsrc2]; simp [srcs2, Array.set!_eq_setIfInBounds]
        rw [hbang]; dsimp [src2]; rw [← getElem!_pos srcs1 0 hszsrc1, hsrcsEq]; exact hfillm
      have hceof : C.Space.get h2 BRef.const_eof = some #[0xff, 0xd9, 0, 0] := rfl
      have hrun : C.run (inputByte (.ref (.decomp bdc) 0) nib 0) h =
          .ok (some (0xFF, .ref .const_eof 1, 1), h2) := by
        unfold inputByte makeByteAvail fill_mem_input_buffer
        simp only [hbf, Bool.false_eq_true, ↓reduceIte]
        rw [C.run_bind, Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hsrcp]
        rw [Ptr.load_bind h rs 0 srcs _ hgetsrc hszsrc, hsrc0, hfillm]
        simp only [beq_self_eq_true, ↓reduceIte, bind_assoc_m]
        rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, herrp, hsrcp]
        rw [C.run_bind, hwarn]; dsimp only
        rw [Ptr.load_bind h1 rs 0 srcs1 _ hgetsrc1 hszsrc1]
        rw [Ptr.store_bind h1 rs 0 src2 srcs1 _ hgetsrc1 hro_src1 hszsrc1]
        simp only [pure_bind_m]
        have htrue : (TRUE == 0) = false := by decide
        simp only [htrue, Bool.false_eq_true, ↓reduceIte]
        rw [Ptr.load_bind h2 rs 0 srcs2 _ hgetsrc2 hszsrc2, hsrc2_0]
        simp only [src2]
        have h2ne : ((2 : UInt64) == 0) = false := by decide
        simp only [h2ne, Bool.false_eq_true, ↓reduceIte]
        simp [C.run, Ptr.load, Ptr.add, hceof]
      refine ⟨_, h2, hrun, hb2, ?_⟩
      simp only [hbf, Bool.false_eq_true, ↓reduceIte]
      cases rs with | src bsrc =>
      exact ⟨trivial, trivial, trivial, ⟨.const_eof, 1, #[0xff, 0xd9, 0, 0], rfl, rfl, by decide⟩,
        ⟨dcs1, errs1, mrks1, srcs2, hgetdc1, hszdc1, herrp1, hmrkp1, hsrcp1,
          hgeterr1, hszerr1, hnw01, hnwLe1, hgetmrk1, hszmrk1,
          hgetsrc2, hszsrc2, Or.inr hfill2⟩⟩

private def skMeasure (bs : ByteScanState) : Nat :=
  if bs.susp || bs.c == 0xFF then 0
  else if bs.bib != 0 then bs.bib.toNat + 2
  else 1

theorem skipToFF_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (hmw : nwMax + 1 < 2 ^ 63)
    (bs0 : ByteScanState) (eof0 : Bool)
    (hsusp0 : bs0.susp = false)
    (hbib0Lt : bs0.bib.toNat < 2 ^ 20)
    (hlive0 : bs0.bib = 0 ∨ LiveBytes h bs0.nib bs0.bib.toNat)
    (hinv0 : if eof0 then bs0.c = 0xFF ∧ bs0.nib = .ref .const_eof 1 ∧ bs0.bib = 1 ∧
        ResyncEnv h bdc rerr rmrk rs (nwMax + 1)
      else ResyncEnv h bdc rerr rmrk rs nwMax) :
    ∃ bs1 h1 eof1,
      C.run (C.cwhile
        (fun (bs : ByteScanState) => pure (!bs.susp && bs.c != 0xFF, bs))
        (fun (bs : ByteScanState) => do
          let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
          let mrk ← Ptr.load dc.marker
          Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 1 }
          inputSync (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib
          match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
          | none => return { bs with susp := true }
          | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
        bs0) h = .ok (bs1, h1) ∧
      SameBytes h1 h ∧
      (if bs1.susp then eof1 = false ∧ ResyncEnv h1 bdc rerr rmrk rs nwMax
      else
        bs1.c = 0xFF ∧
        bs1.bib.toNat < 2 ^ 20 ∧
        (bs1.bib = 0 ∨ LiveBytes h1 bs1.nib bs1.bib.toNat) ∧
        (if eof1 then
          bs1.nib = .ref .const_eof 1 ∧ bs1.bib = 1 ∧ ResyncEnv h1 bdc rerr rmrk rs (nwMax + 1)
        else
          ResyncEnv h1 bdc rerr rmrk rs nwMax ∧ bs1.bib.toNat ≤ bs0.bib.toNat ∧
            SameConstEof bs0.nib bs1.nib bs0.bib bs1.bib ∧
            (bs0.c ≠ 0xFF → bs1.bib.toNat < bs0.bib.toNat))) := by
  let Inv : Nat → C.Heap → ByteScanState → Prop := fun k hx bs =>
    k = skMeasure bs ∧ SameBytes hx h ∧
    bs.bib.toNat < 2 ^ 20 ∧ (bs.bib = 0 ∨ LiveBytes hx bs.nib bs.bib.toNat) ∧
    ∃ eof : Bool,
      (if eof then bs.susp = false ∧ bs.c = 0xFF ∧ bs.nib = .ref .const_eof 1 ∧ bs.bib = 1 ∧
        ResyncEnv hx bdc rerr rmrk rs (nwMax + 1)
      else ResyncEnv hx bdc rerr rmrk rs nwMax ∧
        (bs.susp = false → bs.bib.toNat ≤ bs0.bib.toNat ∧
          SameConstEof bs0.nib bs.nib bs0.bib bs.bib ∧
          (bs.bib.toNat < bs0.bib.toNat ∨ (bs.bib = bs0.bib ∧ bs.c = bs0.c))))
  let Post : C.Heap → ByteScanState → Prop := fun hx bs =>
    SameBytes hx h ∧
    (if bs.susp then ResyncEnv hx bdc rerr rmrk rs nwMax
    else
      bs.c = 0xFF ∧ bs.bib.toNat < 2 ^ 20 ∧ (bs.bib = 0 ∨ LiveBytes hx bs.nib bs.bib.toNat) ∧
      ∃ eof1 : Bool,
        (if eof1 then bs.nib = .ref .const_eof 1 ∧ bs.bib = 1 ∧ ResyncEnv hx bdc rerr rmrk rs (nwMax + 1)
        else ResyncEnv hx bdc rerr rmrk rs nwMax ∧ bs.bib.toNat ≤ bs0.bib.toNat ∧
          SameConstEof bs0.nib bs.nib bs0.bib bs.bib ∧
          (bs0.c ≠ 0xFF → bs.bib.toNat < bs0.bib.toNat)))
  have hlt : skMeasure bs0 < C.fuel := by
    change skMeasure bs0 < 2 ^ 64
    dsimp [skMeasure]; split <;> first | omega | (split <;> omega)
  have hinvInit : Inv (skMeasure bs0) h bs0 := by
    refine ⟨rfl, sameBytes_refl h, hbib0Lt, hlive0, eof0, ?_⟩
    cases eof0
    · simp only [Bool.false_eq_true, ↓reduceIte] at hinv0 ⊢
      exact ⟨hinv0, fun _ => ⟨Nat.le_refl _, sameConstEof_refl _ _, Or.inr ⟨by simp, by simp⟩⟩⟩

    · simp only [↓reduceIte] at hinv0 ⊢
      exact ⟨hsusp0, hinv0⟩
  obtain ⟨bs1, h1, hrun, hpost⟩ := cwhile_terminates
    (fun (bs : ByteScanState) => pure (!bs.susp && bs.c != 0xFF, bs))
    (fun (bs : ByteScanState) => do
      let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
      let mrk ← Ptr.load dc.marker
      Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 1 }
      inputSync (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib
      match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
      | none => return { bs with susp := true }
      | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
    Inv Post (fun k hx bs hinv => by
      obtain ⟨rfl, hbx, hbibLt, hlive, eof, heof⟩ := hinv
      by_cases hcond : (!bs.susp && bs.c != 0xFF) = true
      · have hsF : bs.susp = false := by
          cases h : bs.susp <;> simp [h] at hcond; rfl
        have hcne : bs.c ≠ 0xFF := by
          cases h : bs.susp <;> simp [h] at hcond
          exact fun heq => by simp [heq] at hcond
        have heofF : eof = false := by
          cases eof with
          | false => rfl
          | true =>
            simp only [↓reduceIte] at heof
            exact False.elim (hcne heof.2.1)
        subst heofF
        simp only [Bool.false_eq_true, ↓reduceIte] at heof
        obtain ⟨henvx, hle0⟩ := heof
        obtain ⟨h1, hm1, hb1, henv1⟩ := markerDiscardedInc_resync_ok 1 henvx
        obtain ⟨h2, hs2, hb2, henv2⟩ := inputSync_resync_ok bs.nib bs.bib henv1
        have hlive2 : bs.bib = 0 ∨ LiveBytes h2 bs.nib bs.bib.toNat := by
          rcases hlive with hb0 | hl
          · left; exact hb0
          · right; exact resyncEnv_bytes_irrel (sameBytes_trans hb2 hb1) hl
        obtain ⟨res, h3, hi3, hb3, hres3⟩ := inputByte_resync_ok bs.nib bs.bib (fun _ => hmw) henv2 hlive2
        refine ⟨true, bs, hx, (by simp [C.run, hcond]), ?_⟩
        cases res with
        | none =>
          obtain ⟨hbibZ, hEq32, henv3⟩ := hres3
          have hbody : C.run (do
              let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
              let mrk ← Ptr.load dc.marker
              Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 1 }
              inputSync (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib
              match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
              | none => return { bs with susp := true }
              | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 }) hx =
              .ok ({ bs with susp := true }, h3) := by
            rw [hm1]
            rw [C.run_bind, hs2]; dsimp only
            rw [C.run_bind, hi3]; rfl
          have hneFF : (bs.c == 0xFF) = false := Bool.eq_false_iff.mpr fun h => hcne (by simpa using h)
          have hltMeas : skMeasure { bs with susp := true } < skMeasure bs := by
            simp [skMeasure, hsF, hneFF, hbibZ]
          refine ⟨skMeasure { bs with susp := true }, { bs with susp := true }, h3, hbody, hltMeas,
            rfl, sameBytes_trans hb3 (sameBytes_trans hb2 (sameBytes_trans hb1 hbx)), hbibLt, ?_, false, ?_⟩
          · rcases hlive with hb0 | hl
            · left; exact hb0
            · right; exact resyncEnv_bytes_irrel (sameBytes_trans hb3 (sameBytes_trans hb2 hb1)) hl
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨henv3, fun hc => False.elim (Bool.noConfusion hc)⟩
        | some triple =>
          rcases triple with ⟨c1, nib1, bib1⟩
          let bs' : ByteScanState := { susp := false, c := c1, nib := nib1, bib := bib1 }
          have hbody : C.run (do
              let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
              let mrk ← Ptr.load dc.marker
              Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 1 }
              inputSync (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib
              match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
              | none => return { bs with susp := true }
              | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 }) hx =
              .ok (bs', h3) := by
            rw [hm1]
            rw [C.run_bind, hs2]; dsimp only
            rw [C.run_bind, hi3]; rfl
          by_cases hzn : (bs.bib != 0) = true
          · simp only [hzn, ↓reduceIte] at hres3
            obtain ⟨hsub, hlive3, _, hsce3, hEq32, henv3⟩ := hres3
            have hltMeas : skMeasure bs' < skMeasure bs := by
              have hpos : 0 < bs.bib.toNat := uint64_toNat_pos fun hb0 => by simp [hb0] at hzn
              have hneFF : (bs.c == 0xFF) = false := Bool.eq_false_iff.mpr fun h => hcne (by simpa using h)
              have hsFF : skMeasure bs = bs.bib.toNat + 2 := by
                simp [skMeasure, hsF, hneFF, hzn]
              rw [hsFF]
              dsimp [skMeasure, bs']
              split <;> first | omega | (split <;> omega)
            refine ⟨skMeasure bs', bs', h3, hbody, hltMeas, rfl,
              sameBytes_trans hb3 (sameBytes_trans hb2 (sameBytes_trans hb1 hbx)),
              (by dsimp [bs']; omega), hlive3, false, ?_⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨henv3, fun _ => by
              dsimp [bs']; have hprev := hle0 hsF; have hble := hprev.1
              have hpos : 0 < bs.bib.toNat := uint64_toNat_pos fun hb0 => by simp [hb0] at hzn
              exact ⟨by omega, sameConstEof_trans hprev.2.1 hsce3, Or.inl (by omega)⟩⟩
          · simp only [hzn, Bool.false_eq_true, ↓reduceIte] at hres3
            obtain ⟨hc1, hnib1, hbib1, hlive3, henv3⟩ := hres3
            have hltMeas : skMeasure bs' < skMeasure bs := by
              have hbibZ : bs.bib = 0 := by simpa using Bool.eq_false_iff.mpr hzn
              have hneFF : (bs.c == 0xFF) = false := Bool.eq_false_iff.mpr fun h => hcne (by simpa using h)
              have hsFF : skMeasure bs = 1 := by simp [skMeasure, hsF, hneFF, hbibZ]
              have hcFF : (bs'.c == 0xFF) = true := by simp [bs', hc1]
              have hs'FF : skMeasure bs' = 0 := by simp [skMeasure, bs', hcFF]
              omega
            refine ⟨skMeasure bs', bs', h3, hbody, hltMeas, rfl,
              sameBytes_trans hb3 (sameBytes_trans hb2 (sameBytes_trans hb1 hbx)),
              (by dsimp [bs']; rw [hbib1]; decide), Or.inr (by dsimp [bs']; rw [hbib1]; exact hlive3), true, ?_⟩
            simp only [↓reduceIte]
            exact ⟨rfl, hc1, hnib1, hbib1, henv3⟩
      · have hcondF : (!bs.susp && bs.c != 0xFF) = false := Bool.eq_false_iff.mpr hcond
        refine ⟨false, bs, hx, (by simp [C.run, hcondF]), hbx, ?_⟩
        cases hs : bs.susp
        · simp only [hs] at hcondF ⊢
          have hcFF : bs.c = 0xFF := by simpa using hcondF
          refine ⟨hcFF, hbibLt, hlive, eof, ?_⟩
          cases eof with
          | true => simp only [↓reduceIte] at heof ⊢; exact heof.2.2
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at heof ⊢
            obtain ⟨henvF, hsStep⟩ := heof
            have hstep := hsStep hs
            refine ⟨henvF, hstep.1, hstep.2.1, fun hneFF => ?_⟩
            rcases hstep.2.2 with hlt' | ⟨_, hceq⟩
            · exact hlt'
            · exact absurd (hceq.symm.trans hcFF) hneFF
        · cases eof with
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at heof; exact heof.1
          | true => simp only [↓reduceIte] at heof; exact False.elim (Bool.noConfusion (hs.symm.trans heof.1)))
    hlt hinvInit
  rcases hpost with ⟨hb1, hrest⟩
  cases hs1 : bs1.susp
  · simp only [hs1] at hrest
    obtain ⟨hc1, hbib1Lt, hlive1, eof1, heof1⟩ := hrest
    exact ⟨bs1, h1, eof1, hrun, hb1, by simp [hs1, hc1, hbib1Lt, hlive1]; exact heof1⟩
  · simp only [hs1] at hrest
    exact ⟨bs1, h1, false, hrun, hb1, by simp [hs1]; exact hrest⟩

private def fdMeasure (bs : ByteScanState) : Nat :=
  if bs.nib == .ref .const_eof 1 && bs.bib == 1 then 1
  else if bs.bib != 0 then bs.bib.toNat + 3
  else 2

theorem findNonFF_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (hmw : nwMax + 1 < 2 ^ 63)
    (bs0 : ByteScanState) (eof0 : Bool)
    (hsusp0 : bs0.susp = false)
    (hbib0Lt : bs0.bib.toNat < 2 ^ 20)
    (hlive0 : bs0.bib = 0 ∨ LiveBytes h bs0.nib bs0.bib.toNat)
    (hinv0 : if eof0 then bs0.nib = .ref .const_eof 1 ∧ bs0.bib = 1 ∧
        ResyncEnv h bdc rerr rmrk rs (nwMax + 1)
      else ResyncEnv h bdc rerr rmrk rs nwMax) :
    ∃ bs1 h1 eof1,
      C.run (C.cdoWhile
        (fun (bs : ByteScanState) => do
          match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
          | none => return { bs with susp := true }
          | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
        (fun (bs : ByteScanState) => pure (!bs.susp && bs.c == 0xFF, bs))
        bs0) h = .ok (bs1, h1) ∧
      SameBytes h1 h ∧
      (if bs1.susp then eof1 = false ∧ ResyncEnv h1 bdc rerr rmrk rs nwMax
      else
        bs1.c ≠ 0xFF ∧
        bs1.bib.toNat < 2 ^ 20 ∧
        (bs1.bib = 0 ∨ LiveBytes h1 bs1.nib bs1.bib.toNat) ∧
        (if eof1 then
          bs1.c = M_EOI ∧ bs1.nib = .ref .const_eof 2 ∧ bs1.bib = 0 ∧
          ResyncEnv h1 bdc rerr rmrk rs (nwMax + 1)
        else
          eof0 = false ∧ ResyncEnv h1 bdc rerr rmrk rs nwMax ∧ bs1.bib.toNat < bs0.bib.toNat ∧
            SameConstEof bs0.nib bs1.nib bs0.bib bs1.bib ∧
            (bs0.nib = .ref .const_eof 1 → bs0.bib = 1 → bs1.c = M_EOI))) ∧
      (eof0 = true → bs1.susp = false ∧ eof1 = true) := by
  let Inv : Nat → C.Heap → ByteScanState → Prop := fun k hx bs =>
    k = fdMeasure bs ∧ SameBytes hx h ∧ bs.susp = false ∧
    bs.bib.toNat < 2 ^ 20 ∧ (bs.bib = 0 ∨ LiveBytes hx bs.nib bs.bib.toNat) ∧
    ∃ eof : Bool,
      (eof0 = true → eof = true) ∧
      (if eof then bs.nib = .ref .const_eof 1 ∧ bs.bib = 1 ∧ ResyncEnv hx bdc rerr rmrk rs (nwMax + 1)
      else ResyncEnv hx bdc rerr rmrk rs nwMax ∧ bs.bib.toNat ≤ bs0.bib.toNat ∧
        SameConstEof bs0.nib bs.nib bs0.bib bs.bib ∧
        (bs0.nib = .ref .const_eof 1 → bs0.bib = 1 → bs.nib = .ref .const_eof 1 ∧ bs.bib = 1))
  let Post : C.Heap → ByteScanState → Prop := fun hx bs =>
    SameBytes hx h ∧
    (if bs.susp then eof0 = false ∧ ResyncEnv hx bdc rerr rmrk rs nwMax
    else
      bs.c ≠ 0xFF ∧ bs.bib.toNat < 2 ^ 20 ∧ (bs.bib = 0 ∨ LiveBytes hx bs.nib bs.bib.toNat) ∧
      ∃ eof1 : Bool,
        (eof0 = true → eof1 = true) ∧
        (if eof1 then
          bs.c = M_EOI ∧ bs.nib = .ref .const_eof 2 ∧ bs.bib = 0 ∧
          ResyncEnv hx bdc rerr rmrk rs (nwMax + 1)
        else eof0 = false ∧ ResyncEnv hx bdc rerr rmrk rs nwMax ∧ bs.bib.toNat < bs0.bib.toNat ∧
          SameConstEof bs0.nib bs.nib bs0.bib bs.bib ∧
          (bs0.nib = .ref .const_eof 1 → bs0.bib = 1 → bs.c = M_EOI)))
  have hlt : fdMeasure bs0 < C.fuel := by
    change fdMeasure bs0 < 2 ^ 64
    dsimp [fdMeasure]; split <;> first | omega | (split <;> omega)
  have hinvInit : Inv (fdMeasure bs0) h bs0 := by
    refine ⟨rfl, sameBytes_refl h, hsusp0, hbib0Lt, hlive0, eof0, (fun h => h), ?_⟩
    cases eof0
    · simp only [Bool.false_eq_true, ↓reduceIte] at hinv0 ⊢
      exact ⟨hinv0, Nat.le_refl _, sameConstEof_refl _ _, fun hn hb => ⟨hn, hb⟩⟩
    · simp only [↓reduceIte] at hinv0 ⊢
      exact hinv0
  obtain ⟨bs1, h1, hrun, hpost⟩ := cdoWhile_terminates
    (fun (bs : ByteScanState) => do
      match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
      | none => return { bs with susp := true }
      | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
    (fun (bs : ByteScanState) => pure (!bs.susp && bs.c == 0xFF, bs))
    Inv Post (fun k hx bs hinv => by
      obtain ⟨rfl, hbx, _hsusp, hbibLt, hlive, eof, heof0, heof⟩ := hinv
      cases eof with
      | true =>
        simp only [↓reduceIte] at heof
        obtain ⟨hnibE, hbibE, henvx⟩ := heof
        have henvx' : ResyncEnv hx bdc rerr rmrk rs (nwMax + 1) := henvx
        obtain ⟨res, h1, hi1, hb1, hres1⟩ := inputByte_resync_ok bs.nib bs.bib (fun hb0 => by simp [hbibE] at hb0) henvx' hlive
        have hnz : (bs.bib != 0) = true := by simp [hbibE]
        cases res with
        | none =>
          obtain ⟨hb0, _⟩ := hres1; simp [hbibE] at hb0
        | some triple =>
          rcases triple with ⟨c1, nib1, bib1⟩
          simp only [hnz, ↓reduceIte] at hres1
          obtain ⟨_, _hlive1, hceof, _, hEq1x, _⟩ := hres1
          rw [hEq1x] at hi1
          obtain ⟨hc1, hnib1, hbib1⟩ := hceof hnibE hbibE
          let bs' : ByteScanState := { susp := false, c := c1, nib := nib1, bib := bib1 }
          have hbody : C.run (do
              match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
              | none => return { bs with susp := true }
              | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 }) hx =
              .ok (bs', hx) := by
            rw [C.run_bind, hi1]; rfl
          have hcondF : (!(false) && c1 == 0xFF) = false := by simp [hc1]
          refine ⟨bs', hx, false, bs', hx, hbody, (by simp [bs', C.run, hc1]), ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hbx, (by dsimp [bs']; rw [hc1]; decide), (by dsimp [bs']; rw [hbib1]; decide),
            Or.inl (by dsimp [bs']; exact hbib1), true, (fun _ => rfl),
            ⟨by simpa [M_EOI, bs'] using hc1, hnib1, hbib1, henvx⟩⟩
      | false =>
        have heof0F : eof0 = false := by
          cases h : eof0 with
          | false => rfl
          | true => exact False.elim (Bool.noConfusion (heof0 h))
        simp only [Bool.false_eq_true, ↓reduceIte] at heof
        obtain ⟨henvx, hle0, hsce0, hce0⟩ := heof
        obtain ⟨res, h1, hi1, hb1, hres1⟩ := inputByte_resync_ok bs.nib bs.bib (fun _ => hmw) henvx hlive
        cases res with
        | none =>
          obtain ⟨_hbibZ, _hEq1x, henv1⟩ := hres1
          let bs' : ByteScanState := { bs with susp := true }
          have hbody : C.run (do
              match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
              | none => return { bs with susp := true }
              | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 }) hx =
              .ok (bs', h1) := by
            rw [C.run_bind, hi1]; rfl
          refine ⟨bs', h1, false, bs', h1, hbody, (by simp [C.run, bs']), ?_⟩
          simp only [bs']
          exact ⟨sameBytes_trans hb1 hbx, heof0F, henv1⟩
        | some triple =>
          rcases triple with ⟨c1, nib1, bib1⟩
          let bs' : ByteScanState := { susp := false, c := c1, nib := nib1, bib := bib1 }
          have hbody : C.run (do
              match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
              | none => return { bs with susp := true }
              | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 }) hx =
              .ok (bs', h1) := by
            rw [C.run_bind, hi1]; rfl
          by_cases hnz : (bs.bib != 0) = true
          · simp only [hnz, ↓reduceIte] at hres1
            obtain ⟨hsub, hlive1, hceof, hsce1, hEq1x, henv1⟩ := hres1
            rw [hEq1x] at hbody hlive1 henv1
            have hpos : 0 < bs.bib.toNat := uint64_toNat_pos fun hb0 => by simp [hb0] at hnz
            by_cases hcFF : (c1 == 0xFF) = true
            · refine ⟨bs', hx, true, bs', hx, hbody, (by simp [C.run, bs', hcFF]), ?_⟩
              have hltMeas : fdMeasure bs' < fdMeasure bs := by
                by_cases hce : (bs.nib == .ref .const_eof 1 && bs.bib == 1) = true
                · simp only [Bool.and_eq_true, beq_iff_eq] at hce
                  have hc := (hceof hce.1 hce.2).1
                  simp [hc] at hcFF
                · have hceF : (bs.nib == .ref .const_eof 1 && bs.bib == 1) = false := Bool.eq_false_iff.mpr hce
                  have hmBs : fdMeasure bs = bs.bib.toNat + 3 := by simp [fdMeasure, hceF, hnz]
                  rw [hmBs]
                  dsimp [fdMeasure, bs']
                  split
                  · omega
                  · split <;> omega
              refine ⟨fdMeasure bs', hltMeas, rfl, hbx, rfl, (by dsimp [bs']; omega), hlive1, false,
                (fun h => False.elim (Bool.noConfusion (h.symm.trans heof0F))), ?_⟩
              simp only [Bool.false_eq_true, ↓reduceIte]
              refine ⟨henv1, (by dsimp [bs']; omega), sameConstEof_trans hsce0 hsce1, fun hn0 hb0 => ?_⟩
              obtain ⟨hnx, hbx1⟩ := hce0 hn0 hb0
              have hc := (hceof hnx hbx1).1
              simp [hc] at hcFF
            · have hcFFf : (c1 == 0xFF) = false := Bool.eq_false_iff.mpr hcFF
              refine ⟨bs', hx, false, bs', hx, hbody, (by simp [C.run, bs', hcFFf]), ?_⟩
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact ⟨hbx, (by dsimp [bs']; exact fun heq => hcFF (by simp [heq])),
                (by dsimp [bs']; omega), hlive1, false,
                (fun h => False.elim (Bool.noConfusion (h.symm.trans heof0F))),
                ⟨heof0F, henv1, (by dsimp [bs']; omega), sameConstEof_trans hsce0 hsce1,
                  fun hn0 hb0 => by
                    obtain ⟨hnx, hbx1⟩ := hce0 hn0 hb0
                    simpa [bs', M_EOI] using (hceof hnx hbx1).1⟩⟩
          · simp only [hnz, Bool.false_eq_true, ↓reduceIte] at hres1
            obtain ⟨hc1, hnib1, hbib1, hlive1, henv1⟩ := hres1
            have hcFF : (c1 == 0xFF) = true := by simp [hc1]
            refine ⟨bs', h1, true, bs', h1, hbody, (by simp [C.run, bs', hcFF]), ?_⟩
            have hltMeas : fdMeasure bs' < fdMeasure bs := by
              have hbibZ : bs.bib = 0 := by simpa using Bool.eq_false_iff.mpr hnz
              have hmbs' : fdMeasure bs' = 1 := by simp [fdMeasure, bs', hnib1, hbib1]
              have hmbs : fdMeasure bs = 2 := by
                simp [fdMeasure, hbibZ]
              omega
            refine ⟨fdMeasure bs', hltMeas, rfl, sameBytes_trans hb1 hbx, rfl, (by dsimp [bs']; rw [hbib1]; decide),
              Or.inr (by dsimp [bs']; rw [hbib1]; exact hlive1), true, (fun _ => rfl), ?_⟩
            simp only [↓reduceIte]
            exact ⟨hnib1, hbib1, henv1⟩)
    hlt hinvInit
  rcases hpost with ⟨hb1, hrest⟩
  cases hs1 : bs1.susp
  · simp only [hs1] at hrest
    obtain ⟨hc1, hbib1Lt, hlive1, eof1, he01, heof1⟩ := hrest
    refine ⟨bs1, h1, eof1, hrun, hb1, ?_, fun h => ⟨hs1, he01 h⟩⟩
    simp [hs1, hc1, hbib1Lt, hlive1]; exact heof1
  · simp only [hs1] at hrest
    refine ⟨bs1, h1, false, hrun, hb1, ?_, fun h => False.elim (Bool.noConfusion (h.symm.trans hrest.1))⟩
    simp [hs1]; exact hrest.2

private def nmMeasure (s : NextMarkerState) : Nat :=
  if s.done then 0 else s.bib.toNat + 1

theorem next_marker_resync_ok {h : C.Heap} {bdc : Nat} {rerr : C.ErrRef} {rmrk : C.MarkerRef}
    {rs : C.SrcRef} {nwMax : Int} (hmw : nwMax + 2 < 2 ^ 63)
    (henv : ResyncEnv h bdc rerr rmrk rs nwMax)
    (bib0 : UInt64) (nib0 : C.BPtr)
    (hsrc0 : ∃ srcs, C.Space.get h rs = some srcs ∧ 0 < srcs.size ∧
      srcs[0]!.bytesInBuffer = bib0 ∧ srcs[0]!.nextInputByte = nib0)
    (hbib0Lt : bib0.toNat < 2 ^ 20)
    (hlive0 : bib0 = 0 ∨ LiveBytes h nib0 bib0.toNat) :
    ∃ ret h',
      C.run (next_marker (.ref (.decomp bdc) 0)) h = .ok (ret, h') ∧
      SameBytes h' h ∧
      ResyncEnv h' bdc rerr rmrk rs (nwMax + 2) ∧
      (ret = FALSE ∨
        (ret = TRUE ∧
          ∃ dcs' srcs',
            C.Space.get h' (C.DecompRef.decomp bdc) = some dcs' ∧ 0 < dcs'.size ∧
            C.Space.get h' rs = some srcs' ∧ 0 < srcs'.size ∧
            srcs'[0]!.bytesInBuffer.toNat < 2 ^ 20 ∧
            (srcs'[0]!.bytesInBuffer = 0 ∨ LiveBytes h' srcs'[0]!.nextInputByte srcs'[0]!.bytesInBuffer.toNat) ∧
            ((dcs'[0]!.unreadMarker = M_EOI ∧
                srcs'[0]!.nextInputByte = .ref .const_eof 2 ∧ srcs'[0]!.bytesInBuffer = 0 ∧
                ResyncEnv h' bdc rerr rmrk rs (nwMax + 2)) ∨
             (srcs'[0]!.bytesInBuffer.toNat < bib0.toNat ∧
                SameConstEof nib0 srcs'[0]!.nextInputByte bib0 srcs'[0]!.bytesInBuffer ∧
                ResyncEnv h' bdc rerr rmrk rs (nwMax + 1) ∧
                (∀ off, nib0 = .ref .const_eof off → off + bib0.toNat ≤ 2 → dcs'[0]!.unreadMarker = M_EOI))))) := by
  obtain ⟨srcs0, hgetsrc0, hszsrc0, hbibEq, hnibEq⟩ := hsrc0
  obtain ⟨dcs0, _errs0, _mrks0, _srcs0', hgetdc0, hszdc0, _herr0, _hmrk0, hsrcp0, _⟩ := id henv
  have hdc0_0 : dcs0[0] = dcs0[0]! := by rw [← getElem!_pos dcs0 0 hszdc0]
  have hsrc0_0 : srcs0[0] = srcs0[0]! := by rw [← getElem!_pos srcs0 0 hszsrc0]
  let initSt : NextMarkerState :=
    { done := false, ret := TRUE, c := 0, nib := nib0, bib := bib0 }
  unfold next_marker
  rw [Ptr.load_bind h _ 0 dcs0 _ hgetdc0 hszdc0, hdc0_0, hsrcp0]
  rw [Ptr.load_bind h rs 0 srcs0 _ hgetsrc0 hszsrc0, hsrc0_0, hbibEq, hnibEq]
  let Inv : Nat → C.Heap → NextMarkerState → Prop := fun k hx s =>
    k = nmMeasure s ∧ SameBytes hx h ∧
    s.bib.toNat < 2 ^ 20 ∧ (s.bib = 0 ∨ LiveBytes hx s.nib s.bib.toNat) ∧
    (if s.done then
      (s.ret = 0 ∧ ResyncEnv hx bdc rerr rmrk rs (nwMax + 1)) ∨
      (s.ret != 0 ∧
        ((s.c = M_EOI ∧ s.nib = .ref .const_eof 2 ∧ s.bib = 0 ∧ ResyncEnv hx bdc rerr rmrk rs (nwMax + 1)) ∨
         (ResyncEnv hx bdc rerr rmrk rs nwMax ∧ s.bib.toNat < bib0.toNat ∧
           SameConstEof nib0 s.nib bib0 s.bib ∧
           (∀ off, nib0 = .ref .const_eof off → off + bib0.toNat ≤ 2 → s.c = M_EOI))))
    else ResyncEnv hx bdc rerr rmrk rs nwMax ∧ s.bib.toNat ≤ bib0.toNat ∧
      SameConstEof nib0 s.nib bib0 s.bib)
  let Post : C.Heap → NextMarkerState → Prop := fun hx s =>
    SameBytes hx h ∧
    s.bib.toNat < 2 ^ 20 ∧ (s.bib = 0 ∨ LiveBytes hx s.nib s.bib.toNat) ∧
    ((s.ret = 0 ∧ ResyncEnv hx bdc rerr rmrk rs (nwMax + 1)) ∨
      (s.ret != 0 ∧
        ((s.c = M_EOI ∧ s.nib = .ref .const_eof 2 ∧ s.bib = 0 ∧ ResyncEnv hx bdc rerr rmrk rs (nwMax + 1)) ∨
         (ResyncEnv hx bdc rerr rmrk rs nwMax ∧ s.bib.toNat < bib0.toNat ∧
           SameConstEof nib0 s.nib bib0 s.bib ∧
           (∀ off, nib0 = .ref .const_eof off → off + bib0.toNat ≤ 2 → s.c = M_EOI)))))
  have hlt : nmMeasure initSt < C.fuel := by
    change nmMeasure initSt < 2 ^ 64
    dsimp [nmMeasure, initSt]; omega
  have hinvInit : Inv (nmMeasure initSt) h initSt := by
    refine ⟨rfl, sameBytes_refl h, hbib0Lt, hlive0, ?_⟩
    simp [initSt, henv, sameConstEof_refl]
  let bodyFn : NextMarkerState → C.M NextMarkerState := fun s => do
    match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) s.nib s.bib) with
    | none => return { s with done := true, ret := FALSE }
    | some (c0, nib0, bib0) =>
      let sk0 : ByteScanState := { susp := false, c := c0, nib := nib0, bib := bib0 }
      let sk ← C.cwhile
        (fun (bs : ByteScanState) => pure (!bs.susp && bs.c != 0xFF, bs))
        (fun (bs : ByteScanState) => do
          let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
          let mrk ← Ptr.load dc.marker
          Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 1 }
          inputSync (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib
          match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
          | none => return { bs with susp := true }
          | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
        sk0
      if sk.susp then
        return { s with done := true, ret := FALSE }
      let fd0 : ByteScanState := { susp := false, c := sk.c, nib := sk.nib, bib := sk.bib }
      let fd ← C.cdoWhile
        (fun (bs : ByteScanState) => do
          match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
          | none => return { bs with susp := true }
          | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
        (fun (bs : ByteScanState) => pure (!bs.susp && bs.c == 0xFF, bs))
        fd0
      if fd.susp then
        return { s with done := true, ret := FALSE }
      if fd.c != 0 then
        return { done := true, ret := TRUE, c := fd.c, nib := fd.nib, bib := fd.bib }
      let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
      let mrk ← Ptr.load dc.marker
      Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 2 }
      inputSync (Ptr.ref (C.DecompRef.decomp bdc) 0) fd.nib fd.bib
      return { done := false, ret := TRUE, c := fd.c, nib := fd.nib, bib := fd.bib }
  obtain ⟨st, h1, houter, hpost⟩ := cwhile_terminates
    (fun (s : NextMarkerState) => pure (!s.done, s))
    bodyFn
    Inv Post (fun k hx s hinv => by
      obtain ⟨rfl, hbx, hsbibLt, hslive, hsrest⟩ := hinv
      by_cases hdone : s.done = false
      · simp only [hdone] at hsrest
        have hcond : (!s.done) = true := by simp [hdone]
        obtain ⟨henvx, hsle0, hsce0⟩ := hsrest
        refine ⟨true, s, hx, (by simp [C.run, hcond]), ?_⟩
        obtain ⟨resI, hI, hiI, hbI, hresI⟩ := inputByte_resync_ok s.nib s.bib (fun _ => by omega) henvx hslive
        cases resI with
        | none =>
          obtain ⟨_, hIx, henvI⟩ := hresI
          let s' : NextMarkerState := { s with done := true, ret := FALSE }
          refine ⟨nmMeasure s', s', hI, ?_, by simp [nmMeasure, s', hdone],
            rfl, sameBytes_trans hbI hbx, hsbibLt, ?_, Or.inl ⟨rfl, resyncEnv_mono (by omega : nwMax ≤ nwMax + 1) henvI⟩⟩
          · dsimp only [bodyFn]; rw [C.run_bind, hiI]; rfl
          · rw [hIx]; exact hslive
        | some triple =>
          rcases triple with ⟨c0, nib1, bib1⟩
          by_cases hzn : (s.bib != 0) = true
          · simp only [hzn, ↓reduceIte] at hresI
            obtain ⟨hsub1, hlive1, _, hsce1, hIx, henv1⟩ := hresI
            rw [hIx] at hiI hlive1 henv1
            have hspos : 0 < s.bib.toNat := uint64_toNat_pos fun hb0 => by simp [hb0] at hzn
            have hbib1Lt : bib1.toNat < 2 ^ 20 := by omega
            let sk0 : ByteScanState := { susp := false, c := c0, nib := nib1, bib := bib1 }
            have hsk0bib : sk0.bib.toNat = bib1.toNat := rfl
            obtain ⟨sk, h2, eof1, hskRun, hb2, hskPost⟩ := skipToFF_resync_ok (nwMax := nwMax) (by omega) sk0 false rfl
              hbib1Lt hlive1 (by simpa using henv1)
            cases hskSusp : sk.susp
            · simp only [hskSusp, Bool.false_eq_true, ↓reduceIte] at hskPost
              obtain ⟨hskFF, hskbibLt, hsklive, hskEof⟩ := hskPost
              let fd0 : ByteScanState := { susp := false, c := sk.c, nib := sk.nib, bib := sk.bib }
              have hfd0bib : fd0.bib.toNat = sk.bib.toNat := rfl
              have hfdEofIn : if eof1 then fd0.nib = .ref .const_eof 1 ∧ fd0.bib = 1 ∧
                  ResyncEnv h2 bdc rerr rmrk rs (nwMax + 1)
                else ResyncEnv h2 bdc rerr rmrk rs nwMax := by
                cases eof1 with
                | false => simp only [Bool.false_eq_true, ↓reduceIte] at hskEof ⊢; exact hskEof.1
                | true => simp only [↓reduceIte] at hskEof ⊢; exact hskEof
              obtain ⟨fd, h3, eof2, hfdRun, hb3, hfdPost, hfdEofImp⟩ := findNonFF_resync_ok (nwMax := nwMax) (by omega) fd0 eof1 rfl
                hskbibLt hsklive hfdEofIn
              cases hfdSusp : fd.susp
              · simp only [hfdSusp, Bool.false_eq_true, ↓reduceIte] at hfdPost
                obtain ⟨hfdNeFF, hfdbibLt, hfdlive, hfdEof⟩ := hfdPost
                by_cases hfc0 : (fd.c != 0) = true
                · have hceof2 : if eof2 then
                        fd.c = M_EOI ∧ fd.nib = .ref .const_eof 2 ∧ fd.bib = 0 ∧
                        ResyncEnv h3 bdc rerr rmrk rs (nwMax + 1)
                      else
                        ResyncEnv h3 bdc rerr rmrk rs nwMax ∧ fd.bib.toNat < bib0.toNat ∧
                        SameConstEof nib0 fd.nib bib0 fd.bib ∧
                        (∀ off, nib0 = .ref .const_eof off → off + bib0.toNat ≤ 2 → fd.c = M_EOI) := by
                    cases eof2 with
                    | true =>
                      simp only [↓reduceIte] at hfdEof
                      exact hfdEof
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte] at hfdEof
                      have heof1F : eof1 = false := by
                        cases h : eof1 with
                        | false => rfl
                        | true => exact False.elim (Bool.noConfusion (hfdEofImp h).2)
                      subst heof1F
                      simp only [Bool.false_eq_true, ↓reduceIte] at hskEof
                      obtain ⟨_hfe, henv3, hfdsLt, hsceFd, hfdCe⟩ := hfdEof
                      have hskLe : sk.bib.toNat ≤ sk0.bib.toNat := hskEof.2.1
                      have hfdLt : fd.bib.toNat < fd0.bib.toNat := hfdsLt
                      have hsceAll : SameConstEof nib0 fd.nib bib0 fd.bib :=
                        sameConstEof_trans hsce0 (sameConstEof_trans hsce1
                          (sameConstEof_trans hskEof.2.2.1 hsceFd))
                      refine ⟨henv3, (by omega), hsceAll, fun off hnib0 hle2 => ?_⟩
                      obtain ⟨offS, hsNib, hsumS⟩ := sameConstEof_fwd hsce0 hnib0
                      obtain ⟨off1, hnib1, hsum1⟩ := sameConstEof_fwd hsce1 hsNib
                      obtain ⟨offSk, hskNib, hsumSk⟩ := sameConstEof_fwd hskEof.2.2.1 hnib1
                      have hsPos : 0 < s.bib.toNat := hspos
                      have hsk1 : sk.bib.toNat = 1 := by omega
                      have hskEq1 : sk.bib = 1 := UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hsk1)
                      have hoffSk1 : offSk = 1 := by omega
                      rw [hoffSk1] at hskNib
                      exact hfdCe hskNib hskEq1
                  let s' : NextMarkerState := { done := true, ret := TRUE, c := fd.c, nib := fd.nib, bib := fd.bib }
                  refine ⟨nmMeasure s', s', h3, ?_, (by simp [nmMeasure, s', hdone]),
                    rfl, sameBytes_trans hb3 (sameBytes_trans hb2 hbx), hfdbibLt, hfdlive, Or.inr ⟨(by simp [s', TRUE]), ?_⟩⟩
                  · dsimp only [bodyFn]
                    rw [C.run_bind, hiI]; dsimp only
                    rw [C.run_bind, hskRun]; dsimp only
                    simp only [hskSusp, Bool.false_eq_true, ↓reduceIte]
                    rw [C.run_bind, hfdRun]; dsimp only
                    simp only [hfdSusp, Bool.false_eq_true, ↓reduceIte, hfc0, ↓reduceIte]
                    rfl
                  · cases eof2 with
                    | true => left; exact hceof2
                    | false => right; exact hceof2
                · have hfc0F : (fd.c != 0) = false := Bool.eq_false_iff.mpr hfc0
                  have hfdc0 : fd.c = 0 := by simpa using hfc0F
                  have heof2F : eof2 = false := by
                    cases eof2 with
                    | false => rfl
                    | true =>
                      simp only [↓reduceIte] at hfdEof
                      have : (0 : Int32) = M_EOI := hfdc0.symm.trans hfdEof.1
                      contradiction
                  have heof1F : eof1 = false := by
                    cases h : eof1 with
                    | false => rfl
                    | true => exact False.elim (Bool.noConfusion ((hfdEofImp h).2.symm.trans heof2F))
                  subst heof2F; subst heof1F
                  simp only [Bool.false_eq_true, ↓reduceIte] at hfdEof hskEof
                  obtain ⟨_hfe, henv3, hfdsLt, hsceFd, _⟩ := hfdEof
                  obtain ⟨h4, hm4, hb4, henv4⟩ := markerDiscardedInc_resync_ok 2 henv3
                  obtain ⟨h5, hs5, hb5, henv5⟩ := inputSync_resync_ok fd.nib fd.bib henv4
                  have hlive5 : fd.bib = 0 ∨ LiveBytes h5 fd.nib fd.bib.toNat := by
                    rcases hfdlive with hb0 | hl
                    · left; exact hb0
                    · right; exact resyncEnv_bytes_irrel (sameBytes_trans hb5 hb4) hl
                  let s' : NextMarkerState := { done := false, ret := TRUE, c := fd.c, nib := fd.nib, bib := fd.bib }
                  have hsk0bib : sk0.bib.toNat = bib1.toNat := rfl
                  have hfd0bib : fd0.bib.toNat = sk.bib.toNat := rfl
                  have hs'bib : s'.bib.toNat = fd.bib.toNat := rfl
                  have hleSk : sk.bib.toNat ≤ sk0.bib.toNat := hskEof.2.1
                  have hltFd : fd.bib.toNat < fd0.bib.toNat := hfdsLt
                  have hltMeas : nmMeasure s' < nmMeasure s := by
                    simp only [nmMeasure, s', hdone, Bool.false_eq_true, ↓reduceIte]
                    omega
                  have hsceAll : SameConstEof nib0 s'.nib bib0 s'.bib :=
                    sameConstEof_trans hsce0 (sameConstEof_trans hsce1
                      (sameConstEof_trans hskEof.2.2.1 hsceFd))
                  refine ⟨nmMeasure s', s', h5, ?_, hltMeas, rfl,
                    sameBytes_trans hb5 (sameBytes_trans hb4 (sameBytes_trans hb3 (sameBytes_trans hb2 hbx))),
                    hfdbibLt, hlive5, ?_⟩
                  · dsimp only [bodyFn]
                    rw [C.run_bind, hiI]; dsimp only
                    rw [C.run_bind, hskRun]; dsimp only
                    simp only [hskSusp, Bool.false_eq_true, ↓reduceIte]
                    rw [C.run_bind, hfdRun]; dsimp only
                    simp only [hfdSusp, hfc0F, Bool.false_eq_true, ↓reduceIte]
                    rw [hm4]
                    rw [C.run_bind, hs5]; rfl
                  · exact ⟨henv5, (by omega), hsceAll⟩
              · simp only [hfdSusp, ↓reduceIte] at hfdPost
                let s' : NextMarkerState := { s with done := true, ret := FALSE }
                refine ⟨nmMeasure s', s', h3, ?_, (by simp [nmMeasure, s', hdone]),
                  rfl, sameBytes_trans hb3 (sameBytes_trans hb2 hbx), hsbibLt, ?_,
                  Or.inl ⟨rfl, resyncEnv_mono (by omega : nwMax ≤ nwMax + 1) hfdPost.2⟩⟩
                · dsimp only [bodyFn]
                  rw [C.run_bind, hiI]; dsimp only
                  rw [C.run_bind, hskRun]; dsimp only
                  simp only [hskSusp, Bool.false_eq_true, ↓reduceIte]
                  rw [C.run_bind, hfdRun]; dsimp only
                  simp only [hfdSusp, ↓reduceIte]; rfl
                · rcases hslive with hb0 | hl
                  · left; exact hb0
                  · right; exact resyncEnv_bytes_irrel (sameBytes_trans hb3 hb2) hl
            · simp only [hskSusp, ↓reduceIte] at hskPost
              let s' : NextMarkerState := { s with done := true, ret := FALSE }
              refine ⟨nmMeasure s', s', h2, ?_, (by simp [nmMeasure, s', hdone]),
                rfl, sameBytes_trans hb2 hbx, hsbibLt, ?_,
                Or.inl ⟨rfl, resyncEnv_mono (by omega : nwMax ≤ nwMax + 1) hskPost.2⟩⟩
              · dsimp only [bodyFn]
                rw [C.run_bind, hiI]; dsimp only
                rw [C.run_bind, hskRun]; dsimp only
                simp only [hskSusp, ↓reduceIte]; rfl
              · rcases hslive with hb0 | hl
                · left; exact hb0
                · right; exact resyncEnv_bytes_irrel hb2 hl
          · simp only [hzn, Bool.false_eq_true, ↓reduceIte] at hresI
            obtain ⟨hc0, hnib1, hbib1, hlive1, henv1⟩ := hresI
            let sk0 : ByteScanState := { susp := false, c := c0, nib := nib1, bib := bib1 }
            have hskExit : C.run (C.cwhile
                (fun (bs : ByteScanState) => pure (!bs.susp && bs.c != 0xFF, bs))
                (fun (bs : ByteScanState) => do
                  let dc ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
                  let mrk ← Ptr.load dc.marker
                  Ptr.store dc.marker { mrk with discardedBytes := mrk.discardedBytes + 1 }
                  inputSync (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib
                  match (← inputByte (Ptr.ref (C.DecompRef.decomp bdc) 0) bs.nib bs.bib) with
                  | none => return { bs with susp := true }
                  | some (c1, nib1, bib1) => return { susp := false, c := c1, nib := nib1, bib := bib1 })
                sk0) hI = .ok (sk0, hI) := by
              unfold C.cwhile
              have hfuel : C.fuel = (2 ^ 64 - 1) + 1 := rfl
              rw [hfuel]
              unfold C.cwhile.go
              have hcf : (!sk0.susp && sk0.c != 0xFF) = false := by simp [sk0, hc0]
              simp only [C.run_bind, run_pure, hcf, Bool.false_eq_true, ↓reduceIte]
            let fd0 : ByteScanState := { susp := false, c := sk0.c, nib := sk0.nib, bib := sk0.bib }
            have hbib1Lt' : fd0.bib.toNat < 2 ^ 20 := by
              have : fd0.bib = 1 := hbib1
              rw [this]; decide
            obtain ⟨fd, h3, eof2, hfdRun, hb3, hfdPost, hfdEofImp⟩ := findNonFF_resync_ok (nwMax := nwMax) (by omega) fd0 true rfl
              hbib1Lt' (Or.inr (by dsimp [fd0, sk0]; rw [hbib1]; exact hlive1)) ⟨hnib1, hbib1, henv1⟩
            obtain ⟨hfdSuspF, heof2T⟩ := hfdEofImp rfl
            subst heof2T
            simp only [hfdSuspF, Bool.false_eq_true, ↓reduceIte] at hfdPost
            obtain ⟨_hne, hfdbibLt, hfdlive, hfcEoi, hnib2, hbib2, henv3⟩ := hfdPost
            have hfc0 : (fd.c != 0) = true := by simp [hfcEoi, M_EOI]
            let s' : NextMarkerState := { done := true, ret := TRUE, c := fd.c, nib := fd.nib, bib := fd.bib }
            refine ⟨nmMeasure s', s', h3, ?_, (by simp [nmMeasure, s', hdone]),
              rfl, sameBytes_trans hb3 (sameBytes_trans hbI hbx), hfdbibLt, hfdlive,
              Or.inr ⟨(by simp [s', TRUE]), Or.inl ⟨hfcEoi, hnib2, hbib2, henv3⟩⟩⟩
            dsimp only [bodyFn]
            rw [C.run_bind, hiI]; dsimp only
            rw [C.run_bind, hskExit]; dsimp only
            have hskf : sk0.susp = false := rfl
            simp only [hskf, Bool.false_eq_true, ↓reduceIte]
            rw [C.run_bind, hfdRun]; dsimp only
            simp only [hfdSuspF, Bool.false_eq_true, ↓reduceIte, hfc0, ↓reduceIte]; rfl
      · have hdoneT : s.done = true := by
          cases h : s.done with
          | false => exact False.elim (hdone h)
          | true => rfl
        simp only [hdoneT, ↓reduceIte] at hsrest
        have hcf : (!s.done) = false := by simp [hdoneT]
        exact ⟨false, s, hx, (by simp [C.run, hcf]), hbx, hsbibLt, hslive, hsrest⟩)
    hlt hinvInit
  rw [C.run_bind]
  erw [houter]
  dsimp only
  obtain ⟨hb1, hstbibLt, hstlive, hstRes⟩ := hpost
  rcases hstRes with ⟨hret0, henv1⟩ | ⟨hretNz, hstCase⟩
  · have hretCond : (st.ret == 0) = true := by simp [hret0]
    simp only [hretCond, ↓reduceIte]
    exact ⟨FALSE, h1, rfl, hb1, resyncEnv_mono (by omega : nwMax + 1 ≤ nwMax + 2) henv1, Or.inl rfl⟩
  · have hretCond : (st.ret == 0) = false := Bool.eq_false_iff.mpr fun h => by
      have : st.ret = 0 := by simpa using h
      simp [this] at hretNz
    simp only [hretCond, Bool.false_eq_true, ↓reduceIte]
    have hnw1 : ResyncEnv h1 bdc rerr rmrk rs (nwMax + 1) := by
      rcases hstCase with ⟨_, _, _, h1e⟩ | ⟨h1e, _, _, _⟩
      · exact h1e
      · exact resyncEnv_mono (by omega : nwMax ≤ nwMax + 1) h1e
    obtain ⟨dcs1, _errs1, mrks1, _srcs1, hgetdc1, hszdc1, herr1, hmrk1, hsrc1,
      _hge1, _hszE1, _hnw01, _hnwLe1, hgetmrk1, hszmrk1, _hgs1, _hszS1, _⟩ := id hnw1
    have hdc1_0 : dcs1[0] = dcs1[0]! := by rw [← getElem!_pos dcs1 0 hszdc1]
    have hmrk1_0 : mrks1[0] = mrks1[0]! := by rw [← getElem!_pos mrks1 0 hszmrk1]
    rw [Ptr.load_bind h1 _ 0 dcs1 _ hgetdc1 hszdc1, hdc1_0, hmrk1]
    rw [Ptr.load_bind h1 rmrk 0 mrks1 _ hgetmrk1 hszmrk1, hmrk1_0]
    have finishAfterWarn : ∀ h2,
        SameBytes h2 h1 →
        ((st.c = M_EOI ∧ st.nib = .ref .const_eof 2 ∧ st.bib = 0 ∧ ResyncEnv h2 bdc rerr rmrk rs (nwMax + 2)) ∨
         (ResyncEnv h2 bdc rerr rmrk rs (nwMax + 1) ∧ st.bib.toNat < bib0.toNat ∧
           SameConstEof nib0 st.nib bib0 st.bib ∧
           (∀ off, nib0 = .ref .const_eof off → off + bib0.toNat ≤ 2 → st.c = M_EOI))) →
        ∃ ret h',
          C.run (do
            let dc2 ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
            let src2 ← Ptr.load dc2.src
            Ptr.store dc2.src { src2 with nextInputByte := st.nib, bytesInBuffer := st.bib }
            Ptr.store (Ptr.ref (C.DecompRef.decomp bdc) 0) { dc2 with unreadMarker := st.c }
            pure TRUE) h2 = .ok (ret, h') ∧
          SameBytes h' h ∧
          ResyncEnv h' bdc rerr rmrk rs (nwMax + 2) ∧
          (ret = FALSE ∨
            (ret = TRUE ∧
              ∃ dcs' srcs',
                C.Space.get h' (C.DecompRef.decomp bdc) = some dcs' ∧ 0 < dcs'.size ∧
                C.Space.get h' rs = some srcs' ∧ 0 < srcs'.size ∧
                srcs'[0]!.bytesInBuffer.toNat < 2 ^ 20 ∧
                (srcs'[0]!.bytesInBuffer = 0 ∨ LiveBytes h' srcs'[0]!.nextInputByte srcs'[0]!.bytesInBuffer.toNat) ∧
                ((dcs'[0]!.unreadMarker = M_EOI ∧
                    srcs'[0]!.nextInputByte = .ref .const_eof 2 ∧ srcs'[0]!.bytesInBuffer = 0 ∧
                    ResyncEnv h' bdc rerr rmrk rs (nwMax + 2)) ∨
                 (srcs'[0]!.bytesInBuffer.toNat < bib0.toNat ∧
                    SameConstEof nib0 srcs'[0]!.nextInputByte bib0 srcs'[0]!.bytesInBuffer ∧
                    ResyncEnv h' bdc rerr rmrk rs (nwMax + 1) ∧
                    (∀ off, nib0 = .ref .const_eof off → off + bib0.toNat ≤ 2 → dcs'[0]!.unreadMarker = M_EOI))))) := by
      intro h2 hb2 hRes
      have henv2' : ResyncEnv h2 bdc rerr rmrk rs (nwMax + 2) := by
        rcases hRes with ⟨_, _, _, he⟩ | ⟨he, _, _, _⟩
        · exact he
        · exact resyncEnv_mono (by omega : nwMax + 1 ≤ nwMax + 2) he
      obtain ⟨dcs2, errs2, mrks2, srcs2, hgetdc2, hszdc2, herr2, hmrk2, hsrc2,
        hgeterr2, hszerr2, hnw02, hnwLe2, hgetmrk2, hszmrk2, hgetsrc2, hszsrc2, hfill2⟩ := henv2'
      have hdc2_0 : dcs2[0] = dcs2[0]! := by rw [← getElem!_pos dcs2 0 hszdc2]
      have hgetsrc2' : C.Space.get h2 rs = some srcs2 := hgetsrc2
      have hro_src2 : C.Space.ro h2 rs = false := by cases rs; rfl
      let src3 := { srcs2[0] with nextInputByte := st.nib, bytesInBuffer := st.bib }
      let srcs3 := srcs2.set! 0 src3
      let h3 := C.Space.put h2 rs srcs3
      have hgetsrc3 : C.Space.get h3 rs = some srcs3 := by cases rs; simp [h3, C.Space.get, C.Space.put]
      have hgetdc3 : C.Space.get h3 (C.DecompRef.decomp bdc) = some dcs2 := by cases rs; exact hgetdc2
      have hro_dc3 : C.Space.ro h3 (C.DecompRef.decomp bdc) = false := rfl
      let dc4 := { dcs2[0]! with src := .ref rs 0, unreadMarker := st.c }
      let dcs4 := dcs2.set! 0 dc4
      let h4 := C.Space.put h3 (C.DecompRef.decomp bdc) dcs4
      have hb4 : SameBytes h4 h :=
        have hb3 : SameBytes h3 h2 := by cases rs; exact ⟨rfl, rfl⟩
        sameBytes_trans ⟨rfl, rfl⟩ (sameBytes_trans hb3 (sameBytes_trans hb2 hb1))
      have hgetdc4 : C.Space.get h4 (C.DecompRef.decomp bdc) = some dcs4 := by simp [h4, C.Space.get, C.Space.put]
      have hszdc4 : 0 < dcs4.size := by simp [dcs4, hszdc2]
      have hgetsrc4 : C.Space.get h4 rs = some srcs3 := by cases rs; exact hgetsrc3
      have hszsrc4 : 0 < srcs3.size := by simp [srcs3, hszsrc2]
      have hdc4_bang : dcs4[0]! = dc4 := by
        rw [getElem!_pos _ 0 hszdc4]; simp [dcs4, Array.set!_eq_setIfInBounds]
      have hsrc3_bang : srcs3[0]! = src3 := by
        rw [getElem!_pos _ 0 hszsrc4]; simp [srcs3, Array.set!_eq_setIfInBounds]
      have mkEnv : ∀ (m : Int), ResyncEnv h2 bdc rerr rmrk rs m → ResyncEnv h4 bdc rerr rmrk rs m := by
        intro m hm
        obtain ⟨_d2, e3, _m2, _s2, _gdc, _szdc, _hr, _hm, _hs, hge3, hsze3, hnw03, hlem,
          _gmrk, _szmrk, _gs, _szs, _hf⟩ := hm
        refine ⟨dcs4, e3, mrks2, srcs3, hgetdc4, hszdc4, ?_, ?_, ?_,
          (by cases rs; exact hge3), hsze3, hnw03, hlem,
          (by cases rs; exact hgetmrk2), hszmrk2, hgetsrc4, hszsrc4, ?_⟩
        · rw [hdc4_bang]; exact herr2
        · rw [hdc4_bang]; exact hmrk2
        · rw [hdc4_bang]
        · rw [hsrc3_bang]; dsimp [src3]; rw [← getElem!_pos srcs2 0 hszsrc2]; exact hfill2
      have henv4 : ResyncEnv h4 bdc rerr rmrk rs (nwMax + 2) := by
        apply mkEnv (nwMax + 2)
        rcases hRes with ⟨_, _, _, he⟩ | ⟨he, _, _⟩
        · exact he
        · exact resyncEnv_mono (by omega : nwMax + 1 ≤ nwMax + 2) he
      refine ⟨TRUE, h4, ?_, hb4, henv4, Or.inr ⟨rfl, dcs4, srcs3, hgetdc4, hszdc4, hgetsrc4, hszsrc4, ?_, ?_, ?_⟩⟩
      · rw [Ptr.load_bind h2 _ 0 dcs2 _ hgetdc2 hszdc2, hdc2_0, hsrc2]
        rw [Ptr.load_bind h2 rs 0 srcs2 _ hgetsrc2' hszsrc2]
        rw [Ptr.store_bind h2 rs 0 src3 srcs2 _ hgetsrc2' hro_src2 hszsrc2]
        rw [Ptr.store_bind h3 (C.DecompRef.decomp bdc) 0 dc4 dcs2 _ hgetdc3 hro_dc3 hszdc2]
        rfl
      · rw [hsrc3_bang]; exact hstbibLt
      · rw [hsrc3_bang]
        rcases hstlive with hb0 | hl
        · left; exact hb0
        · right; exact resyncEnv_bytes_irrel (sameBytes_trans ⟨rfl, rfl⟩ (sameBytes_trans (by cases rs; exact ⟨rfl, rfl⟩) hb2)) hl
      · rcases hRes with ⟨hcEoi, hnibE, hbibE, _⟩ | ⟨he2, hbibLt, hsce, hceSt⟩
        · left; refine ⟨(by rw [hdc4_bang]; exact hcEoi), (by rw [hsrc3_bang]; exact hnibE),
            (by rw [hsrc3_bang]; exact hbibE), henv4⟩
        · right; refine ⟨(by rw [hsrc3_bang]; exact hbibLt), (by rw [hsrc3_bang]; exact hsce),
            mkEnv (nwMax + 1) he2, fun off hn hle => by rw [hdc4_bang]; exact hceSt off hn hle⟩
    by_cases hdis : (mrks1[0]!.discardedBytes != 0) = true
    · simp only [hdis, ↓reduceIte, herr1]
      have hResWarn : ∃ h1b,
          (∀ (k : C.M Int32),
            C.run (do
              let _ ← warnms2 (Ptr.ref rerr 0) JWRN_EXTRANEOUS_DATA
                (Int32.ofNat mrks1[0]!.discardedBytes.toNat) st.c
              let mrk2 ← Ptr.load (Ptr.ref rmrk 0)
              Ptr.store (Ptr.ref rmrk 0) { mrk2 with discardedBytes := 0 }
              k) h1 = C.run k h1b) ∧
          SameBytes h1b h1 ∧
          ((st.c = M_EOI ∧ st.nib = .ref .const_eof 2 ∧ st.bib = 0 ∧
              ResyncEnv h1b bdc rerr rmrk rs (nwMax + 2)) ∨
           (ResyncEnv h1b bdc rerr rmrk rs (nwMax + 1) ∧ st.bib.toNat < bib0.toNat ∧
              SameConstEof nib0 st.nib bib0 st.bib ∧
              (∀ off, nib0 = .ref .const_eof off → off + bib0.toNat ≤ 2 → st.c = M_EOI))) := by
        rcases hstCase with ⟨hcEoi, hnibE, hbibE, h1e⟩ | ⟨h1e, hbibLt, hsce, hceSt⟩
        · obtain ⟨h1a, hwa, hba, _, henv1a⟩ := warnms2_resync_ok (by omega : nwMax + 1 + 1 < 2 ^ 63)
            JWRN_EXTRANEOUS_DATA (Int32.ofNat mrks1[0]!.discardedBytes.toNat) st.c h1e
          obtain ⟨h1b, hmb, hbb, henv1b⟩ := markerDiscardedZero_resync_ok henv1a
          refine ⟨h1b, ?_, sameBytes_trans hbb hba, Or.inl ⟨hcEoi, hnibE, hbibE, resyncEnv_mono (by omega : nwMax + 1 + 1 ≤ nwMax + 2) henv1b⟩⟩
          intro k; rw [C.run_bind, hwa]; dsimp only; exact hmb k
        · obtain ⟨h1a, hwa, hba, _, henv1a⟩ := warnms2_resync_ok (by omega : nwMax + 1 < 2 ^ 63)
            JWRN_EXTRANEOUS_DATA (Int32.ofNat mrks1[0]!.discardedBytes.toNat) st.c h1e
          obtain ⟨h1b, hmb, hbb, henv1b⟩ := markerDiscardedZero_resync_ok henv1a
          refine ⟨h1b, ?_, sameBytes_trans hbb hba, Or.inr ⟨henv1b, hbibLt, hsce, hceSt⟩⟩
          intro k; rw [C.run_bind, hwa]; dsimp only; exact hmb k
      obtain ⟨h1b, hrun1b, hb1b, hres1b⟩ := hResWarn
      rw [hrun1b]
      exact finishAfterWarn h1b hb1b hres1b
    · have hdisF : (mrks1[0]!.discardedBytes != 0) = false := Bool.eq_false_iff.mpr hdis
      simp only [hdisF, Bool.false_eq_true, ↓reduceIte]
      have hResNoWarn :
          (st.c = M_EOI ∧ st.nib = .ref .const_eof 2 ∧ st.bib = 0 ∧
            ResyncEnv h1 bdc rerr rmrk rs (nwMax + 2)) ∨
          (ResyncEnv h1 bdc rerr rmrk rs (nwMax + 1) ∧ st.bib.toNat < bib0.toNat ∧
            SameConstEof nib0 st.nib bib0 st.bib ∧
            (∀ off, nib0 = .ref .const_eof off → off + bib0.toNat ≤ 2 → st.c = M_EOI)) := by
        rcases hstCase with ⟨hcEoi, hnibE, hbibE, h1e⟩ | ⟨h1e, hbibLt, hsce, hceSt⟩
        · exact Or.inl ⟨hcEoi, hnibE, hbibE, resyncEnv_mono (by omega : nwMax + 1 ≤ nwMax + 2) h1e⟩
        · exact Or.inr ⟨resyncEnv_mono (by omega : nwMax ≤ nwMax + 1) h1e, hbibLt, hsce, hceSt⟩
      exact finishAfterWarn h1 (sameBytes_refl h1) hResNoWarn

end MozjpegF.Proof.JdmarkerHelpers