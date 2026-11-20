import MozjpegF.Proof.«jdmarker.c.parsers»

/-!
# Marker parsers Step 2 (`jdmarker.c`, `MozjpegF`)

Proves safety, state preservation (`ParserEnv`, `CompSawZero`, `DecompHeaderStable`),
warning budget (`WarnPotOk`), and source progress (`SrcStrict` / `SrcMono`) for:
`first_marker`, `get_soi`, `get_dri`, `get_dac`, `examine_app0`, `examine_app14`,
`get_interesting_appn`, and `skip_variable`.
-/

set_option autoImplicit false

namespace MozjpegF.Proof.JdmarkerMarkers
open C MozjpegF.Spec Mozjpeg.Jerror Mozjpeg.JerrorH Mozjpeg.Jcomapi Mozjpeg.Jmemnobs
open Mozjpeg.Jmemmgr Mozjpeg.Jdatasrc Mozjpeg.Jdmarker Mozjpeg.JpeglibH Mozjpeg.MoreCfg
open MozjpegF.Proof.JdmarkerHelpers MozjpegF.Proof.JmemmgrHelpers MozjpegF.Proof.JdmarkerRead
open MozjpegF.Proof.JdmarkerParsers

/-! ## Shared parser state and progress predicates -/

def CompSawZero (ctx : IoCtx) (h : C.Heap) : Prop :=
  ∀ mrks dcs,
    C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
    C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
    mrks[0]!.sawSOF = 0 → dcs[0]!.compInfo = .null

def CompPreserve (h h' : C.Heap) : Prop :=
  ∀ (rcp : C.CompRef) (cs : Array C.JpegCompInfo) (i : Nat),
    C.Space.get h rcp = some cs → i < cs.size →
    ∃ cs', C.Space.get h' rcp = some cs' ∧ i < cs'.size ∧
      cs'[i]!.hSampFactor = cs[i]!.hSampFactor ∧
      cs'[i]!.vSampFactor = cs[i]!.vSampFactor ∧
      cs'[i]!.dctHScaledSize = cs[i]!.dctHScaledSize

def DecompHeaderStable (ctx : IoCtx) (h h' : C.Heap) : Prop :=
  (∀ dcs dcs',
    C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
    C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
    dcs'[0]!.compInfo = dcs[0]!.compInfo ∧
    dcs'[0]!.numComponents = dcs[0]!.numComponents ∧
    dcs'[0]!.imageWidth = dcs[0]!.imageWidth ∧
    dcs'[0]!.imageHeight = dcs[0]!.imageHeight ∧
    dcs'[0]!.maxHSampFactor = dcs[0]!.maxHSampFactor ∧
    dcs'[0]!.maxVSampFactor = dcs[0]!.maxVSampFactor ∧
    dcs'[0]!.entropyStartPass = dcs[0]!.entropyStartPass ∧
    dcs'[0]!.coefStartInputPass = dcs[0]!.coefStartInputPass ∧
    dcs'[0]!.coefConsumeData = dcs[0]!.coefConsumeData) ∧
  (∀ mrks mrks',
    C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
    C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
    mrks'[0]!.sawSOF = mrks[0]!.sawSOF) ∧
  CompPreserve h h'

theorem decompHeaderStable_refl (ctx : IoCtx) (h : C.Heap) : DecompHeaderStable ctx h h := by
  refine ⟨?_, ?_, ?_⟩
  · intro dcs dcs' h1 _ h2 _
    rw [Option.some.inj (h2.symm.trans h1)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro mrks mrks' h1 _ h2 _; rw [Option.some.inj (h2.symm.trans h1)]
  · intro rcp cs i hg hi; exact ⟨cs, hg, hi, rfl, rfl, rfl⟩

theorem decompHeaderStable_of_same {ctx : IoCtx} {h h' : C.Heap}
    (hd : h'.decomps = h.decomps) (hm : h'.markers = h.markers) (hc : h'.comps = h.comps) :
    DecompHeaderStable ctx h h' := by
  refine ⟨?_, ?_, ?_⟩
  · intro d1 d2 h1 _ h2 _
    simp only [C.Space.get] at h1 h2; rw [hd] at h2
    rw [Option.some.inj (h2.symm.trans h1)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro m1 m2 h1 _ h2 _
    rcases hrM : ctx.rmrk with ⟨bm⟩; simp only [C.Space.get, hrM, hm] at h1 h2
    rw [Option.some.inj (h2.symm.trans h1)]
  · intro rcp cs i hg hi; cases rcp; simp only [C.Space.get] at hg ⊢; rw [hc]
    exact ⟨cs, hg, hi, rfl, rfl, rfl⟩

theorem decompHeaderStable_trans {ctx : IoCtx} {h1 h2 h3 : C.Heap}
    (_hp1 : ParserEnv ctx h1) (hp2 : ParserEnv ctx h2)
    (h12 : DecompHeaderStable ctx h1 h2) (h23 : DecompHeaderStable ctx h2 h3) :
    DecompHeaderStable ctx h1 h3 := by
  rcases h12 with ⟨hd12, hm12, hc12⟩
  rcases h23 with ⟨hd23, hm23, hc23⟩
  refine ⟨?_, ?_, ?_⟩
  · intro dcs1 dcs3 hg1 hsz1 hg3 hsz3
    obtain ⟨dcs2, hg2, hsz2, _⟩ := parserEnv_get_dc hp2
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hd12 dcs1 dcs2 hg1 hsz1 hg2 hsz2
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hd23 dcs2 dcs3 hg2 hsz2 hg3 hsz3
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5,
      b6.trans a6, b7.trans a7, b8.trans a8, b9.trans a9⟩
  · intro mrks1 mrks3 hg1 hsz1 hg3 hsz3
    obtain ⟨mrks2, hg2, hsz2, _⟩ := parserEnv_get_mrk hp2
    exact (hm23 mrks2 mrks3 hg2 hsz2 hg3 hsz3).trans (hm12 mrks1 mrks2 hg1 hsz1 hg2 hsz2)
  · intro rcp cs1 i hg1 hi1
    obtain ⟨cs2, hg2, hi2, h1a, h1b, h1c⟩ := hc12 rcp cs1 i hg1 hi1
    obtain ⟨cs3, hg3, hi3, h2a, h2b, h2c⟩ := hc23 rcp cs2 i hg2 hi2
    exact ⟨cs3, hg3, hi3, h2a.trans h1a, h2b.trans h1b, h2c.trans h1c⟩

theorem compSawZero_of_stable {ctx : IoCtx} {h h' : C.Heap}
    (hsaw : CompSawZero ctx h) (hst : DecompHeaderStable ctx h h')
    (hp : ParserEnv ctx h) : CompSawZero ctx h' := by
  intro mrks' dcs' hgmrk' hszmrk' hgdc' hszdc' hsaw0
  obtain ⟨mrks, hgmrk, hszmrk, _⟩ := parserEnv_get_mrk hp
  obtain ⟨dcs, hgdc, hszdc, _⟩ := parserEnv_get_dc hp
  have hmeq := hst.2.1 mrks mrks' hgmrk hszmrk hgmrk' hszmrk'
  have hdeq := (hst.1 dcs dcs' hgdc hszdc hgdc' hszdc').1
  rw [hdeq]
  exact hsaw mrks dcs hgmrk hszmrk hgdc hszdc (hmeq ▸ hsaw0)

def SrcStrict (src0 src1 : C.JpegSourceMgr) : Prop :=
  (isConstEofPtr src0.nextInputByte = true → isConstEofPtr src1.nextInputByte = true) ∧
  (isConstEofPtr src0.nextInputByte = false →
    isConstEofPtr src1.nextInputByte = true ∨ src1.bytesInBuffer.toNat < src0.bytesInBuffer.toNat)

def SrcMono (src0 src1 : C.JpegSourceMgr) : Prop :=
  (isConstEofPtr src0.nextInputByte = true → isConstEofPtr src1.nextInputByte = true) ∧
  (isConstEofPtr src0.nextInputByte = false →
    isConstEofPtr src1.nextInputByte = true ∨ src1.bytesInBuffer.toNat ≤ src0.bytesInBuffer.toNat)

theorem srcMono_of_strict {s0 s1 : C.JpegSourceMgr} (h : SrcStrict s0 s1) : SrcMono s0 s1 :=
  ⟨h.1, fun hf => (h.2 hf).elim Or.inl (fun hlt => Or.inr (Nat.le_of_lt hlt))⟩

theorem srcMono_refl (s : C.JpegSourceMgr) : SrcMono s s :=
  ⟨id, fun _ => Or.inr (Nat.le_refl _)⟩

theorem srcMono_trans {s0 s1 s2 : C.JpegSourceMgr} (h01 : SrcMono s0 s1) (h12 : SrcMono s1 s2) :
    SrcMono s0 s2 := by
  refine ⟨fun ht0 => h12.1 (h01.1 ht0), fun hf0 => ?_⟩
  rcases h01.2 hf0 with ht1 | hle1
  · exact Or.inl (h12.1 ht1)
  · by_cases hf1 : isConstEofPtr s1.nextInputByte = false
    · rcases h12.2 hf1 with ht2 | hle2
      · exact Or.inl ht2
      · exact Or.inr (Nat.le_trans hle2 hle1)
    · have ht1 : isConstEofPtr s1.nextInputByte = true := by cases hc : isConstEofPtr s1.nextInputByte <;> simp_all
      exact Or.inl (h12.1 ht1)

theorem srcStrict_mono_trans {s0 s1 s2 : C.JpegSourceMgr} (h01 : SrcStrict s0 s1) (h12 : SrcMono s1 s2) :
    SrcStrict s0 s2 := by
  refine ⟨fun ht0 => h12.1 (h01.1 ht0), fun hf0 => ?_⟩
  rcases h01.2 hf0 with ht1 | hlt1
  · exact Or.inl (h12.1 ht1)
  · by_cases hf1 : isConstEofPtr s1.nextInputByte = false
    · rcases h12.2 hf1 with ht2 | hle2
      · exact Or.inl ht2
      · exact Or.inr (Nat.lt_of_le_of_lt hle2 hlt1)
    · have ht1 : isConstEofPtr s1.nextInputByte = true := by cases hc : isConstEofPtr s1.nextInputByte <;> simp_all
      exact Or.inl (h12.1 ht1)

def warnPotVal (errs : Array C.JpegErrorMgr) (srcs : Array C.JpegSourceMgr) : Int :=
  errs[0]!.numWarnings.toInt +
    if isConstEofPtr srcs[0]!.nextInputByte then (0 : Int) else 4 * (srcs[0]!.bytesInBuffer.toNat : Int)

def WarnPotOk (ctx : IoCtx) (h h' : C.Heap) (eofLimit : Int) : Prop :=
  ∀ errs errs' srcs0 srcs',
    C.Space.get h ctx.rerr = some errs → 0 < errs.size →
    C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
    C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
    C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
    (isConstEofPtr srcs'[0]!.nextInputByte = false →
      warnPotVal errs' srcs' ≤ warnPotVal errs srcs0) ∧
    (isConstEofPtr srcs'[0]!.nextInputByte = true →
      errs'[0]!.numWarnings.toInt ≤
        (if isConstEofPtr srcs0[0]!.nextInputByte then errs[0]!.numWarnings.toInt
         else warnPotVal errs srcs0) + eofLimit)

theorem warnPotOk_of_err_src_same {ctx : IoCtx} {h h' : C.Heap}
    (herr : h'.errMgrs = h.errMgrs) (hsrc : h'.srcs = h.srcs) : WarnPotOk ctx h h' 0 := by
  intro errs errs' srcs0 srcs' hg0 _ hg1 _ hs0 _ hs1 _
  rcases hrE : ctx.rerr with ⟨be⟩; simp only [C.Space.get, hrE, herr] at hg0 hg1
  rcases hrS : ctx.rs with ⟨bs⟩; simp only [C.Space.get, hrS, hsrc] at hs0 hs1
  have h1 := Option.some.inj (hg1.symm.trans hg0)
  have h2 := Option.some.inj (hs1.symm.trans hs0)
  subst h1; subst h2
  refine ⟨fun _ => Int.le_refl _, fun hc => ?_⟩
  simp [hc]

theorem warnPotOk_of_err_same_nw {ctx : IoCtx} {h h' : C.Heap}
    (hnw : ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs[0]!.numWarnings)
    (hsrc : h'.srcs = h.srcs) : WarnPotOk ctx h h' 0 := by
  intro errs errs' srcs0 srcs' hg0 hsz0 hg1 _ hs0 _ hs1 _
  have heq := (hnw errs errs' hg0 hsz0 hg1).2
  rcases hrS : ctx.rs with ⟨bs⟩; simp only [C.Space.get, hrS, hsrc] at hs0 hs1
  have h2 := Option.some.inj (hs1.symm.trans hs0); subst h2
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · simp [warnPotVal, heq, hc]
  · simp [heq, hc]

theorem warnPotOk_trans {ctx : IoCtx} {h1 h2 h3 : C.Heap} {l1 l2 : Int}
    (hm12 : ∀ srcs0 srcs1, C.Space.get h1 ctx.rs = some srcs0 → 0 < srcs0.size →
      C.Space.get h2 ctx.rs = some srcs1 → 0 < srcs1.size → SrcMono srcs0[0]! srcs1[0]!)
    (hm23 : ∀ srcs1 srcs2, C.Space.get h2 ctx.rs = some srcs1 → 0 < srcs1.size →
      C.Space.get h3 ctx.rs = some srcs2 → 0 < srcs2.size → SrcMono srcs1[0]! srcs2[0]!)
    (hw12 : WarnPotOk ctx h1 h2 l1) (hw23 : WarnPotOk ctx h2 h3 l2)
    (hl1 : 0 ≤ l1) (hp2 : ParserEnv ctx h2) :
    WarnPotOk ctx h1 h3 (l1 + l2) := by
  intro errs1 errs3 srcs1 srcs3 hg1 hsz1 hg3 hsz3 hs1 hszs1 hs3 hszs3
  obtain ⟨errs2, hg2, hsz2, _⟩ := parserEnv_get_err hp2
  obtain ⟨srcs2, hs2, hszs2, _⟩ := parserEnv_get_src hp2
  obtain ⟨w12f, w12t⟩ := hw12 errs1 errs2 srcs1 srcs2 hg1 hsz1 hg2 hsz2 hs1 hszs1 hs2 hszs2
  obtain ⟨w23f, w23t⟩ := hw23 errs2 errs3 srcs2 srcs3 hg2 hsz2 hg3 hsz3 hs2 hszs2 hs3 hszs3
  refine ⟨fun hc3 => ?_, fun hc3 => ?_⟩
  · have hc2 : isConstEofPtr srcs2[0]!.nextInputByte = false := by
      cases hxx : isConstEofPtr srcs2[0]!.nextInputByte
      · rfl
      · have ht3 := (hm23 srcs2 srcs3 hs2 hszs2 hs3 hszs3).1 hxx
        rw [hc3] at ht3; cases ht3
    exact Int.le_trans (w23f hc3) (w12f hc2)
  · have hle2 := w23t hc3
    by_cases hc2 : isConstEofPtr srcs2[0]!.nextInputByte = true
    · simp only [hc2, ↓reduceIte] at hle2
      have hle1 := w12t hc2
      omega
    · have hf2 : isConstEofPtr srcs2[0]!.nextInputByte = false := by cases hxx : isConstEofPtr srcs2[0]!.nextInputByte <;> simp_all
      simp only [hf2, Bool.false_eq_true, ↓reduceIte] at hle2
      have hf1 : isConstEofPtr srcs1[0]!.nextInputByte = false := by
        cases hxx : isConstEofPtr srcs1[0]!.nextInputByte
        · rfl
        · have ht2 := (hm12 srcs1 srcs2 hs1 hszs1 hs2 hszs2).1 hxx
          rw [hf2] at ht2; cases ht2
      have hle1 := w12f hf2
      simp only [hf1, Bool.false_eq_true, ↓reduceIte]
      omega

theorem warnPotOk_bd {ctx : IoCtx} {h0 h1 : C.Heap} {eofLim delta : Int}
    (hp0 : ParserEnv ctx h0) (hp1 : ParserEnv ctx h1) (hw : WarnPotOk ctx h0 h1 eofLim)
    (hhead : ∀ errs0 srcs0, C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + max eofLim 0 + delta < 2 ^ 63) :
    ∀ errs1, C.Space.get h1 ctx.rerr = some errs1 → 0 < errs1.size →
      errs1[0]!.numWarnings.toInt + delta < 2 ^ 63 := by
  intro errs1 hg1 hsz1
  obtain ⟨errs0, hg0, hsz0, _⟩ := parserEnv_get_err hp0
  obtain ⟨srcs0, hs0, hszs0, _⟩ := parserEnv_get_src hp0
  obtain ⟨srcs1, hs1, hszs1, _⟩ := parserEnv_get_src hp1
  obtain ⟨hf, ht⟩ := hw errs0 errs1 srcs0 srcs1 hg0 hsz0 hg1 hsz1 hs0 hszs0 hs1 hszs1
  have hhd := hhead errs0 srcs0 hg0 hsz0 hs0 hszs0
  by_cases hce0 : isConstEofPtr srcs0[0]!.nextInputByte = false
  · simp only [warnPotVal, hce0, Bool.false_eq_true, ↓reduceIte] at hhd
    by_cases hce1 : isConstEofPtr srcs1[0]!.nextInputByte = false
    · have h1 := hf hce1
      simp only [warnPotVal, hce1, hce0, Bool.false_eq_true, ↓reduceIte] at h1
      omega
    · have ht1 : isConstEofPtr srcs1[0]!.nextInputByte = true := by cases hc : isConstEofPtr srcs1[0]!.nextInputByte <;> simp_all
      have h2 := ht ht1
      simp only [warnPotVal, hce0, Bool.false_eq_true, ↓reduceIte] at h2
      omega
  · have ht0 : isConstEofPtr srcs0[0]!.nextInputByte = true := by cases hc : isConstEofPtr srcs0[0]!.nextInputByte <;> simp_all
    simp only [warnPotVal, ht0, ↓reduceIte] at hhd
    by_cases hce1 : isConstEofPtr srcs1[0]!.nextInputByte = false
    · have h1 := hf hce1
      simp only [warnPotVal, hce1, ht0, Bool.false_eq_true, ↓reduceIte] at h1
      omega
    · have ht1 : isConstEofPtr srcs1[0]!.nextInputByte = true := by cases hc : isConstEofPtr srcs1[0]!.nextInputByte <;> simp_all
      have h2 := ht ht1
      simp only [ht0, ↓reduceIte] at h2
      omega

/-! ## Stream cursor tracker (`NibBibTrack`) -/

def NibBibTrack (ctx : IoCtx) (h0 h : C.Heap) (nib : C.BPtr) (bib : UInt64)
    (nonEofDelta eofLim : Int) : Prop :=
  ∀ errs0 errs srcs0,
    C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
    C.Space.get h ctx.rerr = some errs → 0 < errs.size →
    C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
    (isConstEofPtr srcs0[0]!.nextInputByte = true → isConstEofPtr nib = true) ∧
    (isConstEofPtr nib = false →
      isConstEofPtr srcs0[0]!.nextInputByte = false ∧
      bib.toNat ≤ srcs0[0]!.bytesInBuffer.toNat ∧
      errs[0]!.numWarnings.toInt + 4 * (bib.toNat : Int) ≤
        warnPotVal errs0 srcs0 + nonEofDelta) ∧
    (isConstEofPtr nib = true →
      errs[0]!.numWarnings.toInt ≤
        (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
         else warnPotVal errs0 srcs0) + eofLim)

theorem nibBibTrack_init (ctx : IoCtx) (h : C.Heap) (srcs0 : Array C.JpegSourceMgr)
    (hs0 : C.Space.get h ctx.rs = some srcs0) :
    NibBibTrack ctx h h srcs0[0]!.nextInputByte srcs0[0]!.bytesInBuffer 0 0 := by
  intro errs0 errs srcs0' hg0 _ hg1 _ hs0' _
  have h1 := Option.some.inj (hg1.symm.trans hg0); subst h1
  have h2 := Option.some.inj (hs0'.symm.trans hs0); subst h2
  refine ⟨id, ?_, ?_⟩
  · intro hf; refine ⟨hf, Nat.le_refl _, ?_⟩
    simp [warnPotVal, hf]
  · intro ht; simp [ht]

theorem nibBibTrack_mono {ctx : IoCtx} {h0 h : C.Heap} {nib : C.BPtr} {bib : UInt64}
    {nd1 nd2 el1 el2 : Int} (ht : NibBibTrack ctx h0 h nib bib nd1 el1)
    (hnd : nd1 ≤ nd2) (hel : el1 ≤ el2) :
    NibBibTrack ctx h0 h nib bib nd2 el2 := by
  intro e0 e s0 he0 hse0 he hse hs0 hss0
  obtain ⟨a, b, c⟩ := ht e0 e s0 he0 hse0 he hse hs0 hss0
  refine ⟨a, fun hf => ?_, fun htr => ?_⟩
  · obtain ⟨b1, b2, b3⟩ := b hf; exact ⟨b1, b2, by omega⟩
  · have := c htr; omega

theorem nibBibTrack_err_nw_same {ctx : IoCtx} {h0 h h' : C.Heap} {nib : C.BPtr} {bib : UInt64}
    {nd el : Int} (hp : ParserEnv ctx h) (ht : NibBibTrack ctx h0 h nib bib nd el)
    (hnw : ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs[0]!.numWarnings) :
    NibBibTrack ctx h0 h' nib bib nd el := by
  intro e0 e' s0 he0 hse0 he' hse' hs0 hss0
  obtain ⟨e, he, hse, _⟩ := parserEnv_get_err hp
  have hweq := (hnw e e' he hse he').2
  obtain ⟨a, b, c⟩ := ht e0 e s0 he0 hse0 he hse hs0 hss0
  refine ⟨a, fun hf => ?_, fun htr => ?_⟩
  · obtain ⟨b1, b2, b3⟩ := b hf; exact ⟨b1, b2, by rw [hweq]; exact b3⟩
  · rw [hweq]; exact c htr

theorem nibBibTrack_err_warn1 {ctx : IoCtx} {h0 h h' : C.Heap} {nib : C.BPtr} {bib : UInt64}
    {nd el : Int} (hp : ParserEnv ctx h) (ht : NibBibTrack ctx h0 h nib bib nd el)
    (hnw : ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
      errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 1) :
    NibBibTrack ctx h0 h' nib bib (nd + 1) (el + 1) := by
  intro e0 e' s0 he0 hse0 he' hse' hs0 hss0
  obtain ⟨e, he, hse, _⟩ := parserEnv_get_err hp
  have hwle := (hnw e e' he hse he').2
  obtain ⟨a, b, c⟩ := ht e0 e s0 he0 hse0 he hse hs0 hss0
  refine ⟨a, fun hf => ?_, fun htr => ?_⟩
  · obtain ⟨b1, b2, b3⟩ := b hf; exact ⟨b1, b2, by omega⟩
  · have := c htr; omega

theorem nibBibTrack_err_same {ctx : IoCtx} {h0 h h' : C.Heap} {nib : C.BPtr} {bib : UInt64}
    {nd el : Int} (ht : NibBibTrack ctx h0 h nib bib nd el)
    (herr : h'.errMgrs = h.errMgrs) :
    NibBibTrack ctx h0 h' nib bib nd el := by
  intro e0 e' s0 he0 hse0 he' hse' hs0 hss0
  have he'' : C.Space.get h ctx.rerr = some e' := by
    rcases hrE : ctx.rerr with ⟨be⟩; simp only [C.Space.get, hrE, herr] at he' ⊢; exact he'
  exact ht e0 e' s0 he0 hse0 he'' hse' hs0 hss0

theorem nibBibTrack_bd {ctx : IoCtx} {h0 h : C.Heap} {nib : C.BPtr} {bib : UInt64}
    {nd el delta : Int} (hp0 : ParserEnv ctx h0) (_hp : ParserEnv ctx h)
    (ht : NibBibTrack ctx h0 h nib bib nd el) (hnd : nd ≤ 0)
    (hhead : ∀ errs0 srcs0, C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + max el 0 + delta < 2 ^ 63) :
    ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + delta < 2 ^ 63 := by
  intro errs hg hsz
  obtain ⟨errs0, hg0, hsz0, _⟩ := parserEnv_get_err hp0
  obtain ⟨srcs0, hs0, hszs0, _⟩ := parserEnv_get_src hp0
  obtain ⟨_, b, c⟩ := ht errs0 errs srcs0 hg0 hsz0 hg hsz hs0 hszs0
  have hhd := hhead errs0 srcs0 hg0 hsz0 hs0 hszs0
  by_cases hf0 : isConstEofPtr srcs0[0]!.nextInputByte = false
  · simp only [warnPotVal, hf0, Bool.false_eq_true, ↓reduceIte] at hhd
    by_cases hf : isConstEofPtr nib = false
    · obtain ⟨_, _, hle⟩ := b hf
      simp only [warnPotVal, hf0, Bool.false_eq_true, ↓reduceIte] at hle
      omega
    · have htr : isConstEofPtr nib = true := by cases hc : isConstEofPtr nib <;> simp_all
      have hle := c htr
      simp only [warnPotVal, hf0, Bool.false_eq_true, ↓reduceIte] at hle
      omega
  · have ht0 : isConstEofPtr srcs0[0]!.nextInputByte = true := by cases hc : isConstEofPtr srcs0[0]!.nextInputByte <;> simp_all
    simp only [warnPotVal, ht0, ↓reduceIte] at hhd
    by_cases hf : isConstEofPtr nib = false
    · obtain ⟨_, _, hle⟩ := b hf
      simp only [warnPotVal, ht0, ↓reduceIte] at hle
      omega
    · have htr : isConstEofPtr nib = true := by cases hc : isConstEofPtr nib <;> simp_all
      have hle := c htr
      simp only [ht0, ↓reduceIte] at hle
      omega

theorem nibBibTrack_inputByte_step {ctx : IoCtx} {h0 h h' : C.Heap}
    {nib nib' : C.BPtr} {bib bib' : UInt64} {nd el : Int}
    (hp0 : ParserEnv ctx h0) (hp : ParserEnv ctx h)
    (ht : NibBibTrack ctx h0 h nib bib nd el) (hnd : nd ≤ 0) (hel : 0 ≤ el)
    (hpost : if isConstEofPtr nib' = false then
      isConstEofPtr nib = false ∧ bib ≠ 0 ∧ bib'.toNat + 1 = bib.toNat ∧ h' = h
     else
      ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + (if bib == 0 then 1 else 0)) :
    NibBibTrack ctx h0 h' nib' bib' (nd - 4) (el + 1) ∧
    (∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      isConstEofPtr nib' = true ∨ bib'.toNat < srcs0[0]!.bytesInBuffer.toNat) := by
  refine ⟨fun e0 e' s0 he0 hse0 he' hse' hs0 hss0 => ?_, fun s0 hs0 hss0 => ?_⟩
  · obtain ⟨e, he, hse, _⟩ := parserEnv_get_err hp
    obtain ⟨ta, tb, tc⟩ := ht e0 e s0 he0 hse0 he hse hs0 hss0
    refine ⟨fun hs0t => ?_, fun hnf => ?_, fun hnt => ?_⟩
    · have hnt0 := ta hs0t
      by_cases hnf' : isConstEofPtr nib' = false
      · simp only [hnf', ↓reduceIte] at hpost; rw [hnt0] at hpost; exact False.elim (by cases hpost.1)
      · cases hc : isConstEofPtr nib' <;> simp_all
    · simp only [hnf, ↓reduceIte] at hpost
      rcases hpost with ⟨hnf0, _, hbib', hh⟩
      subst hh
      have heq := Option.some.inj (he'.symm.trans he); subst heq
      obtain ⟨b1, b2, b3⟩ := tb hnf0
      refine ⟨b1, by omega, by omega⟩
    · simp only [hnt, Bool.true_eq_false, ↓reduceIte] at hpost
      have hle := (hpost e e' he hse he').2
      by_cases hnf0 : isConstEofPtr nib = false
      · obtain ⟨hs0f, _, hbw⟩ := tb hnf0
        simp only [warnPotVal, hs0f, Bool.false_eq_true, ↓reduceIte] at hbw ⊢
        split at hle <;> omega
      · have hnt0 : isConstEofPtr nib = true := by cases hc : isConstEofPtr nib <;> simp_all
        have := tc hnt0
        by_cases hcs0 : isConstEofPtr s0[0]!.nextInputByte = true
        · simp only [hcs0, ↓reduceIte] at this ⊢; split at hle <;> omega
        · have hf0 : isConstEofPtr s0[0]!.nextInputByte = false := by cases hc : isConstEofPtr s0[0]!.nextInputByte <;> simp_all
          simp only [warnPotVal, hf0, Bool.false_eq_true, ↓reduceIte] at this ⊢; split at hle <;> omega
  · obtain ⟨e0, he0, hse0, _⟩ := parserEnv_get_err hp0
    obtain ⟨e, he, hse, _⟩ := parserEnv_get_err hp
    obtain ⟨_, tb, _⟩ := ht e0 e s0 he0 hse0 he hse hs0 hss0
    by_cases hnf' : isConstEofPtr nib' = false
    · right
      simp only [hnf', ↓reduceIte] at hpost
      rcases hpost with ⟨hnf0, _, hbib', _⟩
      have := (tb hnf0).2.1; omega
    · left; cases hc : isConstEofPtr nib' <;> simp_all

theorem nibBibTrack_input2Bytes_step {ctx : IoCtx} {h0 h h' : C.Heap}
    {nib nib' : C.BPtr} {bib bib' : UInt64} {nd el : Int}
    (hp0 : ParserEnv ctx h0) (hp : ParserEnv ctx h)
    (ht : NibBibTrack ctx h0 h nib bib nd el) (hnd : nd ≤ 0) (hel : 0 ≤ el)
    (hpost : if isConstEofPtr nib' = false then
      isConstEofPtr nib = false ∧ bib'.toNat + 2 = bib.toNat ∧ h' = h
     else
      ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 2) :
    NibBibTrack ctx h0 h' nib' bib' (nd - 8) (el + 2) ∧
    (∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      isConstEofPtr nib' = true ∨ bib'.toNat < srcs0[0]!.bytesInBuffer.toNat) := by
  refine ⟨fun e0 e' s0 he0 hse0 he' hse' hs0 hss0 => ?_, fun s0 hs0 hss0 => ?_⟩
  · obtain ⟨e, he, hse, _⟩ := parserEnv_get_err hp
    obtain ⟨ta, tb, tc⟩ := ht e0 e s0 he0 hse0 he hse hs0 hss0
    refine ⟨fun hs0t => ?_, fun hnf => ?_, fun hnt => ?_⟩
    · have hnt0 := ta hs0t
      by_cases hnf' : isConstEofPtr nib' = false
      · simp only [hnf', ↓reduceIte] at hpost; rw [hnt0] at hpost; exact False.elim (by cases hpost.1)
      · cases hc : isConstEofPtr nib' <;> simp_all
    · simp only [hnf, ↓reduceIte] at hpost
      rcases hpost with ⟨hnf0, hbib', hh⟩
      subst hh
      have heq := Option.some.inj (he'.symm.trans he); subst heq
      obtain ⟨b1, b2, b3⟩ := tb hnf0
      refine ⟨b1, by omega, by omega⟩
    · simp only [hnt, Bool.true_eq_false, ↓reduceIte] at hpost
      have hle := (hpost e e' he hse he').2
      by_cases hnf0 : isConstEofPtr nib = false
      · obtain ⟨hs0f, _, hbw⟩ := tb hnf0
        simp only [warnPotVal, hs0f, Bool.false_eq_true, ↓reduceIte] at hbw ⊢
        omega
      · have hnt0 : isConstEofPtr nib = true := by cases hc : isConstEofPtr nib <;> simp_all
        have := tc hnt0
        by_cases hcs0 : isConstEofPtr s0[0]!.nextInputByte = true
        · simp only [hcs0, ↓reduceIte] at this ⊢; omega
        · have hf0 : isConstEofPtr s0[0]!.nextInputByte = false := by cases hc : isConstEofPtr s0[0]!.nextInputByte <;> simp_all
          simp only [warnPotVal, hf0, Bool.false_eq_true, ↓reduceIte] at this ⊢; omega
  · obtain ⟨e0, he0, hse0, _⟩ := parserEnv_get_err hp0
    obtain ⟨e, he, hse, _⟩ := parserEnv_get_err hp
    obtain ⟨_, tb, _⟩ := ht e0 e s0 he0 hse0 he hse hs0 hss0
    by_cases hnf' : isConstEofPtr nib' = false
    · right
      simp only [hnf', ↓reduceIte] at hpost
      rcases hpost with ⟨hnf0, hbib', _⟩
      have := (tb hnf0).2.1; omega
    · left; cases hc : isConstEofPtr nib' <;> simp_all

theorem nibBibTrack_to_warnPotOk_src {ctx : IoCtx} {h0 h h' : C.Heap}
    {nib : C.BPtr} {bib : UInt64} {nd el : Int}
    (hp0 : ParserEnv ctx h0) (hp : ParserEnv ctx h)
    (ht : NibBibTrack ctx h0 h nib bib nd el) (hnd : nd ≤ 0)
    (herr : h'.errMgrs = h.errMgrs)
    (hsrc : ∀ srcs', C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size ∧
      srcs'[0]!.nextInputByte = nib ∧ srcs'[0]!.bytesInBuffer = bib) :
    WarnPotOk ctx h0 h' el ∧
    (∀ srcs0 srcs', C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size → SrcMono srcs0[0]! srcs'[0]!) := by
  refine ⟨?_, ?_⟩
  · intro errs0 errs' srcs0 srcs' hg0 hsz0 hg1 hsz1 hs0 hszs0 hs1 _
    have hg1' : C.Space.get h ctx.rerr = some errs' := by
      rcases hrE : ctx.rerr with ⟨be⟩; simp only [C.Space.get, hrE, herr] at hg1 ⊢; exact hg1
    obtain ⟨_, hnib, hbib⟩ := hsrc srcs' hs1
    obtain ⟨_, tb, tc⟩ := ht errs0 errs' srcs0 hg0 hsz0 hg1' hsz1 hs0 hszs0
    refine ⟨fun hf => ?_, fun htr => ?_⟩
    · rw [hnib] at hf
      obtain ⟨hf0, _, hle⟩ := tb hf
      simp only [warnPotVal, hnib, hbib, hf, hf0, Bool.false_eq_true, ↓reduceIte] at hle ⊢
      omega
    · rw [hnib] at htr; exact tc htr
  · intro srcs0 srcs' hs0 hszs0 hs1 _
    obtain ⟨errs0, hg0, hsz0, _⟩ := parserEnv_get_err hp0
    obtain ⟨errs, hg, hsz, _⟩ := parserEnv_get_err hp
    obtain ⟨ta, tb, _⟩ := ht errs0 errs srcs0 hg0 hsz0 hg hsz hs0 hszs0
    obtain ⟨_, hnib, hbib⟩ := hsrc srcs' hs1
    refine ⟨fun h => ?_, fun _ => ?_⟩
    · rw [hnib]; exact ta h
    · rw [hnib, hbib]
      by_cases hnf : isConstEofPtr nib = false
      · exact Or.inr (tb hnf).2.1
      · left; cases hc : isConstEofPtr nib <;> simp_all

theorem nibBibTrack_to_srcStrict {ctx : IoCtx} {h0 h h' : C.Heap}
    {nib : C.BPtr} {bib : UInt64} {nd el : Int}
    (hp0 : ParserEnv ctx h0) (hp : ParserEnv ctx h)
    (ht : NibBibTrack ctx h0 h nib bib nd el)
    (hstr : ∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      isConstEofPtr nib = true ∨ bib.toNat < srcs0[0]!.bytesInBuffer.toNat)
    (hsrc : ∀ srcs', C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size ∧
      srcs'[0]!.nextInputByte = nib ∧ srcs'[0]!.bytesInBuffer = bib) :
    ∀ srcs0 srcs', C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size → SrcStrict srcs0[0]! srcs'[0]! := by
  intro srcs0 srcs' hs0 hszs0 hs1 _
  obtain ⟨errs0, hg0, hsz0, _⟩ := parserEnv_get_err hp0
  obtain ⟨errs, hg, hsz, _⟩ := parserEnv_get_err hp
  obtain ⟨ta, _, _⟩ := ht errs0 errs srcs0 hg0 hsz0 hg hsz hs0 hszs0
  obtain ⟨_, hnib, hbib⟩ := hsrc srcs' hs1
  refine ⟨fun h => ?_, fun _ => ?_⟩
  · rw [hnib]; exact ta h
  · rw [hnib, hbib]; exact hstr srcs0 hs0 hszs0

/-! ## Local helpers for heap updates and error exits -/

theorem set0_bang_m {α : Type} [Inhabited α] (a : Array α) (h : 0 < a.size) (v : α) :
    (a.set! 0 v)[0]! = v := by
  simp only [Array.set!, Array.setIfInBounds, h, ↓reduceDIte]
  rw [getElem!_pos _ 0 (by simp [h])]
  exact Array.getElem_set_self h

theorem parserEnv_put_dc_same {ctx : IoCtx} {h : C.Heap}
    {dcs : Array C.JpegDecompressStruct} {dc' : C.JpegDecompressStruct}
    (hp : ParserEnv ctx h) (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (kerr : dc'.err = dcs[0]!.err) (kmem : dc'.mem = dcs[0]!.mem) (kmas : dc'.master = dcs[0]!.master)
    (kic : dc'.inputctl = dcs[0]!.inputctl) (kmrk : dc'.marker = dcs[0]!.marker) (ksrc : dc'.src = dcs[0]!.src)
    (kml : dc'.markerList = dcs[0]!.markerList)
    (kcomp : dc'.compInfo = dcs[0]!.compInfo) (knc : dc'.numComponents = dcs[0]!.numComponents)
    (kqt : dc'.quantTblPtrs = dcs[0]!.quantTblPtrs)
    (kdh : dc'.dcHuffTblPtrs = dcs[0]!.dcHuffTblPtrs)
    (kah : dc'.acHuffTblPtrs = dcs[0]!.acHuffTblPtrs)
    (kcc : dc'.curCompInfo = dcs[0]!.curCompInfo)
    (kisn : dc'.inputScanNumber = dcs[0]!.inputScanNumber) :
    ParserEnv ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) := by
  have hp0 := hp
  obtain ⟨_, _, dcs0, dc0, _, _, _, _, mrks, _,
    hgdc0, _, hdc0, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, hgmrk0, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, _, hsaw0, _, hqtSz0, hqt0, hdhSz0, hdh0, hahSz0, hah0, hccSz0, hisn0⟩ := hp0
  have hdEq : dcs = dcs0 := Option.some.inj (hg.symm.trans hgdc0)
  subst hdEq; subst hdc0
  refine parserEnv_put_dc hp hg hsz kerr kmem kmas kic kmrk ksrc (Or.inl kml) (Or.inl ⟨kcomp, knc⟩)
    ⟨by rw [kqt]; exact hqtSz0, fun i hi => by rw [kqt]; exact hqt0 i hi⟩
    ⟨by rw [kdh]; exact hdhSz0, fun i hi => by rw [kdh]; exact hdh0 i hi⟩
    ⟨by rw [kah]; exact hahSz0, fun i hi => by rw [kah]; exact hah0 i hi⟩
    (by rw [kcc]; exact hccSz0) (by rw [kisn]; exact hisn0)
    (fun mrks' hgmrk' _ => by
      have hmEq := Option.some.inj (hgmrk'.symm.trans hgmrk0); subst hmEq
      rw [kcomp]; exact hsaw0)

theorem parserEnv_put_mrk_sameCur {ctx : IoCtx} {h : C.Heap}
    {mrks : Array C.JpegMarkerReader} {mrk' : C.JpegMarkerReader}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.rmrk = some mrks) (hsz : 0 < mrks.size)
    (hrm : mrk'.readMarkers = mrks[0]!.readMarkers)
    (hrmr : mrk'.resetMarkerReader = mrks[0]!.resetMarkerReader)
    (hpcom : mrk'.processCOM = mrks[0]!.processCOM)
    (hpapp : mrk'.processAPPn = mrks[0]!.processAPPn)
    (hll : mrk'.lengthLimitAPPn = mrks[0]!.lengthLimitAPPn)
    (hcm : mrk'.curMarker = mrks[0]!.curMarker)
    (hbr : mrk'.bytesRead = mrks[0]!.bytesRead)
    (hsaw : mrk'.sawSOF = mrks[0]!.sawSOF) :
    ParserEnv ctx (C.Space.put h ctx.rmrk (mrks.set! 0 mrk')) := by
  have hp0 := hp
  obtain ⟨_, _, dcs0, dc0, _, _, _, _, mrks0, _,
    hgdc0, _, hdc0, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, hgmrk0, _, _, _, _, _, _, hllSz0,
    _, _, _, _, _, _, _, _, _,
    hcurm0, _, hsaw0, _⟩ := hp0
  have hmEq : mrks = mrks0 := Option.some.inj (hg.symm.trans hgmrk0)
  subst hmEq; subst hdc0
  refine parserEnv_put_mrk hp hg hsz hrm hrmr hpcom hpapp (by rw [hll]; exact hllSz0) ?_ ?_
  · rw [hcm, hbr]; exact hcurm0
  · intro dcs' hgdc' _ hne
    have hdEq := Option.some.inj (hgdc'.symm.trans hgdc0); subst hdEq
    exact hsaw0 (hsaw ▸ hne)

theorem errexit_stable_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code : Int32) :
    ∃ h', C.run (errexit (.ref ctx.rerr 0) code) h = .ok (.errExit code, h') ∧
      ParserEnv ctx h' ∧ DecompHeaderStable ctx h h' := by
  obtain ⟨h', hk, hp', hd, hmr, _, _, hcp, _⟩ := errMsgUpdate_cont_parser hp code (fun arr => arr)
  refine ⟨h', ?_, hp', decompHeaderStable_of_same hd hmr hcp⟩
  unfold errexit; exact hk (pure (JpegRes.errExit code))

theorem errexit1_stable_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code p1 : Int32) :
    ∃ h', C.run (errexit1 (.ref ctx.rerr 0) code p1) h = .ok (.errExit code, h') ∧
      ParserEnv ctx h' ∧ DecompHeaderStable ctx h h' := by
  obtain ⟨h', hk, hp', hd, hmr, _, _, hcp, _⟩ := errMsgUpdate_cont_parser hp code (fun arr => arr.set! 0 p1)
  refine ⟨h', ?_, hp', decompHeaderStable_of_same hd hmr hcp⟩
  unfold errexit1; exact hk (pure (JpegRes.errExit code))

theorem errexit2_stable_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (code p1 p2 : Int32) :
    ∃ h', C.run (errexit2 (.ref ctx.rerr 0) code p1 p2) h = .ok (.errExit code, h') ∧
      ParserEnv ctx h' ∧ DecompHeaderStable ctx h h' := by
  obtain ⟨h', hk, hp', hd, hmr, _, _, hcp, _⟩ := errMsgUpdate_cont_parser hp code (fun arr => (arr.set! 0 p1).set! 1 p2)
  refine ⟨h', ?_, hp', decompHeaderStable_of_same hd hmr hcp⟩
  unfold errexit2; exact hk (pure (JpegRes.errExit code))

theorem int32_toInt_ofNat_small {n : Nat} (hn : n < 2 ^ 31) :
    (Int32.ofNat n).toInt = (n : Int) := by
  rw [Int32.toInt_ofNat']
  have hsz : Int32.size = 2 ^ 32 := rfl
  rw [hsz]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-! ## `first_marker` and `get_soi` -/

theorem first_marker_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 < 2 ^ 63) :
    ∃ res h',
      C.run (first_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∃ dcs', C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' ∧ 0 < dcs'.size ∧
          dcs'[0]!.unreadMarker = M_SOI) ∧
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcStrict srcs0[0]! srcs'[0]!) ∧
        WarnPotOk ctx h h' 2
      | _ => True := by
  obtain ⟨dcs, hgdc, hszdc, kerr, _, _, _, _, ksrc⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _his, _hts, _hsip, _hrtr, _hfill, hcur0⟩ := parserEnv_get_src hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc hszsrc
  have htr0 := nibBibTrack_init ctx h srcs hgsrc
  have hbd0 : srcs[0]!.bytesInBuffer = 0 → ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
    nibBibTrack_bd hp hp htr0 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
  obtain ⟨res1, h1, hrun1, hp1, hd1, hmr1, _, hcp1, _, _, _, _, _, _, hpost1⟩ :=
    inputByte_parser hp srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer hcur0 hbd0
  have hst01 : DecompHeaderStable ctx h h1 := decompHeaderStable_of_same hd1 hmr1 hcp1
  cases res1 with
  | none =>
    refine ⟨.ok false, h1, ?_, hp1, hst01, trivial⟩
    unfold first_marker
    rw [C.run_bind, hldc]; dsimp only
    rw [ksrc, C.run_bind, hlsrc]; dsimp only
    rw [C.run_bind, hrun1]; rfl
  | some x =>
    rcases x with ⟨c1, nib1, bib1⟩
    rcases hpost1 with ⟨_, _, hcur1, hce1⟩
    obtain ⟨htr1, _⟩ := nibBibTrack_inputByte_step hp hp htr0 (by omega) (by omega) hce1
    have hbd1 : bib1 = 0 → ∀ errs, C.Space.get h1 ctx.rerr = some errs → 0 < errs.size →
        errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
      nibBibTrack_bd hp hp1 htr1 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
        have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
    obtain ⟨res2, h2, hrun2, hp2, hd2, hmr2, _, hcp2, _, _, _, _, _, _, hpost2⟩ :=
      inputByte_parser hp1 nib1 bib1 hcur1 hbd1
    have hst02 := decompHeaderStable_trans hp hp1 hst01 (decompHeaderStable_of_same hd2 hmr2 hcp2)
    cases res2 with
    | none =>
      refine ⟨.ok false, h2, ?_, hp2, hst02, trivial⟩
      unfold first_marker
      rw [C.run_bind, hldc]; dsimp only
      rw [ksrc, C.run_bind, hlsrc]; dsimp only
      rw [C.run_bind, hrun1]; dsimp only
      rw [C.run_bind, hrun2]; rfl
    | some y =>
      rcases y with ⟨c2, nib2, bib2⟩
      rcases hpost2 with ⟨_, _, hcur2, hce2⟩
      obtain ⟨htr2, hstr2⟩ := nibBibTrack_inputByte_step hp hp1 htr1 (by omega) (by omega) hce2
      by_cases hbad : (c1 != 0xFF || c2 != M_SOI) = true
      · obtain ⟨dcs2, hgdc2, _, kerr2, _⟩ := parserEnv_get_dc hp2
        obtain ⟨h_err, herr_run, hp_err, hstErr⟩ := errexit2_stable_parser hp2 JERR_NO_SOI c1 c2
        have herr_run' : C.run (errexit2 dcs[0]!.err JERR_NO_SOI c1 c2) h2 = .ok (.errExit JERR_NO_SOI, h_err) := by
          rw [kerr]; exact herr_run
        refine ⟨.errExit JERR_NO_SOI, h_err, ?_, hp_err, decompHeaderStable_trans hp hp2 hst02 hstErr, trivial⟩
        unfold first_marker
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind, hrun2]; dsimp only
        simp only [hbad, ↓reduceIte, C.run_bind, herr_run']; rfl
      · have hbadF : (c1 != 0xFF || c2 != M_SOI) = false := by cases hbb : (c1 != 0xFF || c2 != M_SOI) <;> simp_all
        have hc2Eq : c2 = M_SOI := by
          cases hne : (c2 == M_SOI)
          · have hb : (c2 != M_SOI) = true := by simp [bne, hne]
            simp [hb] at hbadF
          · exact eq_of_beq hne
        obtain ⟨dcs2, hgdc2, hszdc2, _⟩ := parserEnv_get_dc hp2
        have hldc2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc2 hszdc2
        have hroDc2 : C.Space.ro h2 (C.DecompRef.decomp ctx.bdc) = false := rfl
        let dc3 := { dcs2[0]! with unreadMarker := c2 }
        have hstDc := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc3) hgdc2 hroDc2 hszdc2
        let h3 := C.Space.put h2 (C.DecompRef.decomp ctx.bdc) (dcs2.set! 0 dc3)
        have hp3 : ParserEnv ctx h3 := parserEnv_put_dc_same hp2 hgdc2 hszdc2
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have htr3 : NibBibTrack ctx h h3 nib2 bib2 (-4 - 4) (1 + 1) :=
          nibBibTrack_err_same htr2 rfl
        obtain ⟨h4, hsync, hp4, hd4, hmr4, h_e4, _, hcp4, _, _, _, _, _, _, hsrc4⟩ :=
          inputSync_parser hp3 nib2 bib2 hcur2
        have hst23 : DecompHeaderStable ctx h2 h3 := by
          refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
            (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
          intro da db hga _ hgb _
          have ha := Option.some.inj (hga.symm.trans hgdc2)
          have hg3 : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dc3) := by
            simp [h3, C.Space.get, C.Space.put]
          have hb := Option.some.inj (hgb.symm.trans hg3)
          rw [ha, hb, set0_bang_m dcs2 hszdc2 dc3]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hst04 := decompHeaderStable_trans hp hp2 hst02
          (decompHeaderStable_trans hp2 hp3 hst23 (decompHeaderStable_of_same hd4 hmr4 hcp4))
        obtain ⟨hw, _⟩ := nibBibTrack_to_warnPotOk_src hp hp3 htr3 (by omega) h_e4 hsrc4
        have hstr := nibBibTrack_to_srcStrict hp hp3 htr3 hstr2 hsrc4
        refine ⟨.ok true, h4, ?_, hp4, hst04, ⟨?_, hstr, hw⟩⟩
        · unfold first_marker
          rw [C.run_bind, hldc]; dsimp only
          rw [ksrc, C.run_bind, hlsrc]; dsimp only
          rw [C.run_bind, hrun1]; dsimp only
          rw [C.run_bind, hrun2]; dsimp only
          simp only [hbadF, Bool.false_eq_true, ↓reduceIte]
          rw [C.run_bind, hldc2]; dsimp only
          rw [C.run_bind, hstDc]; dsimp only
          rw [C.run_bind, hsync]; rfl
        · have hgdc3 : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dc3) := by
            simp [h3, C.Space.get, C.Space.put]
          have hgdc4 : C.Space.get h4 (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dc3) := by
            simp only [C.Space.get, hd4]; exact hgdc3
          refine ⟨dcs2.set! 0 dc3, hgdc4, by simpa using hszdc2, ?_⟩
          rw [set0_bang_m dcs2 hszdc2 dc3]; exact hc2Eq

theorem get_soi_parser {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ res h',
      C.run (get_soi (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
        SrcMono srcs0[0]! srcs'[0]!) ∧
      WarnPotOk ctx h h' 0 := by
  obtain ⟨dcs, hgdc, hszdc, kerr, _, _, _, kmrk, _⟩ := parserEnv_get_dc hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  obtain ⟨h1, htr1, hp1, hd1, hmr1, hsr1, _, hcp1, _, _, _, _, _, _, hnw1⟩ :=
    tracems_nonneg_parser hp 1 JTRC_SOI (by decide)
  have hst01 : DecompHeaderStable ctx h h1 := decompHeaderStable_of_same hd1 hmr1 hcp1
  obtain ⟨mrks1, hgmrk1, hszmrk1, _⟩ := parserEnv_get_mrk hp1
  obtain ⟨dcs1, hgdc1, hszdc1, kerr1, _, _, _, kmrk1, _⟩ := parserEnv_get_dc hp1
  have hl1 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk1 hszmrk1
  have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc1
  have hw01 : WarnPotOk ctx h h1 0 := warnPotOk_of_err_same_nw hnw1 hsr1
  have hm01 : ∀ srcs0 srcs1, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      C.Space.get h1 ctx.rs = some srcs1 → 0 < srcs1.size → SrcMono srcs0[0]! srcs1[0]! := by
    intro s0 s1 h0 _ h1s _
    rcases hrS : ctx.rs with ⟨bs⟩; simp only [C.Space.get, hrS, hsr1] at h0 h1s
    rw [Option.some.inj (h1s.symm.trans h0)]; exact srcMono_refl _
  by_cases hsaw : (mrks1[0]!.sawSOI != 0) = true
  · obtain ⟨h_err, herr_run, hp_err, hstErr⟩ := errexit_stable_parser hp1 JERR_SOI_DUPLICATE
    have herr_run' : C.run (errexit dcs[0]!.err JERR_SOI_DUPLICATE) h1 = .ok (.errExit JERR_SOI_DUPLICATE, h_err) := by
      rw [kerr]; exact herr_run
    obtain ⟨h_e, hke, _, _, _, hsre, _, _, _, _, _, _, _, _, hnwe⟩ :=
      errMsgUpdate_cont_parser hp1 JERR_SOI_DUPLICATE (fun arr => arr)
    have hEq : h_err = h_e := by
      have he1 := herr_run; unfold errexit at he1
      rw [hke (pure (JpegRes.errExit JERR_SOI_DUPLICATE))] at he1
      exact (Prod.mk.inj (Except.ok.inj he1)).2.symm
    have hw1e : WarnPotOk ctx h1 h_err 0 := by rw [hEq]; exact warnPotOk_of_err_same_nw hnwe hsre
    have hm1e : ∀ s1 se, C.Space.get h1 ctx.rs = some s1 → 0 < s1.size →
        C.Space.get h_err ctx.rs = some se → 0 < se.size → SrcMono s1[0]! se[0]! := by
      intro s1 se h1s _ hes _
      rcases hrS : ctx.rs with ⟨bs⟩; simp only [C.Space.get, hrS, hEq, hsre] at h1s hes
      rw [Option.some.inj (hes.symm.trans h1s)]; exact srcMono_refl _
    refine ⟨.errExit JERR_SOI_DUPLICATE, h_err, ?_, hp_err,
      decompHeaderStable_trans hp hp1 hst01 hstErr,
      fun s0 se h0 hsz0 hes hsze => by
        obtain ⟨s1, hs1, hsz1, _⟩ := parserEnv_get_src hp1
        exact srcMono_trans (hm01 s0 s1 h0 hsz0 hs1 hsz1) (hm1e s1 se hs1 hsz1 hes hsze),
      by simpa using warnPotOk_trans hm01 hm1e hw01 hw1e (by omega) hp1⟩
    unfold get_soi
    rw [C.run_bind, hldc]; dsimp only
    rw [kerr, C.run_bind, htr1]; dsimp only
    rw [kmrk, C.run_bind, hl1]; dsimp only
    simp only [hsaw, ↓reduceIte, C.run_bind, herr_run]; rfl
  · have hsawF : (mrks1[0]!.sawSOI != 0) = false := by cases hc : (mrks1[0]!.sawSOI != 0) <;> simp_all
    have hroDc1 : C.Space.ro h1 (C.DecompRef.decomp ctx.bdc) = false := rfl
    let dc2 : C.JpegDecompressStruct := {
      dcs1[0]! with
      arithDcL := Array.replicate 16 0
      arithDcU := Array.replicate 16 1
      arithAcK := Array.replicate 16 5
      restartInterval := 0
      jpegColorSpace := JCS_UNKNOWN
      ccir601Sampling := FALSE
      sawJFIFMarker := FALSE
      jfifMajorVersion := 1
      jfifMinorVersion := 1
      densityUnit := 0
      xDensity := 1
      yDensity := 1
      sawAdobeMarker := FALSE
      adobeTransform := 0
    }
    have hstDc := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc2) hgdc1 hroDc1 hszdc1
    let h2 := C.Space.put h1 (C.DecompRef.decomp ctx.bdc) (dcs1.set! 0 dc2)
    have hp2 : ParserEnv ctx h2 := parserEnv_put_dc_same hp1 hgdc1 hszdc1
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨mrks2, hgmrk2, hszmrk2, _⟩ := parserEnv_get_mrk hp2
    have hmrkEq2 : dcs1[0]!.marker = .ref ctx.rmrk 0 := kmrk1
    have hl2 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk2 hszmrk2
    have hroMrk2 : C.Space.ro h2 ctx.rmrk = false := by cases ctx.rmrk; rfl
    let mrk3 := { mrks2[0]! with sawSOI := TRUE }
    have hstMrk := ptr_store_ok (r := ctx.rmrk) (off := 0) (v := mrk3) hgmrk2 hroMrk2 hszmrk2
    let h3 := C.Space.put h2 ctx.rmrk (mrks2.set! 0 mrk3)
    have hp3 : ParserEnv ctx h3 := parserEnv_put_mrk_sameCur hp2 hgmrk2 hszmrk2
      rfl rfl rfl rfl rfl rfl rfl rfl
    have hst12 : DecompHeaderStable ctx h1 h2 := by
      refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
        (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
      intro da db hga _ hgb _
      have ha := Option.some.inj (hga.symm.trans hgdc1)
      have hg2 : C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some (dcs1.set! 0 dc2) := by
        simp [h2, C.Space.get, C.Space.put]
      have hb := Option.some.inj (hgb.symm.trans hg2)
      rw [ha, hb, set0_bang_m dcs1 hszdc1 dc2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hst23 : DecompHeaderStable ctx h2 h3 := by
      refine ⟨(fun d1 d2 ha _ hb _ => by
        have hdeq : h3.decomps = h2.decomps := by cases ctx.rmrk; rfl
        simp only [C.Space.get] at ha hb; rw [hdeq] at hb; rw [Option.some.inj (hb.symm.trans ha)]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩), ?_, (fun rcp cs i hg hi => by
        have hceq : h3.comps = h2.comps := by cases ctx.rmrk; rfl
        cases rcp; simp only [C.Space.get] at hg ⊢; rw [hceq]; exact ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
      intro m1 m2 ha _ hb _
      have ha' := Option.some.inj (ha.symm.trans hgmrk2)
      have hg3 : C.Space.get h3 ctx.rmrk = some (mrks2.set! 0 mrk3) := by
        rcases hr : ctx.rmrk with ⟨bm⟩; simp [h3, C.Space.get, C.Space.put, hr]
      have hb' := Option.some.inj (hb.symm.trans hg3)
      rw [ha', hb', set0_bang_m mrks2 hszmrk2 mrk3]
    have hw13 : WarnPotOk ctx h1 h3 0 := warnPotOk_of_err_src_same
      (by rcases hr : ctx.rmrk with ⟨bm⟩; rfl)
      (by rcases hr : ctx.rmrk with ⟨bm⟩; rfl)
    have hsr3 : h3.srcs = h.srcs := by
      have hh : h3.srcs = h1.srcs := by rcases hr : ctx.rmrk with ⟨bm⟩; rfl
      exact hh.trans hsr1
    refine ⟨.ok true, h3, ?_, hp3,
      decompHeaderStable_trans hp hp1 hst01 (decompHeaderStable_trans hp1 hp2 hst12 hst23),
      fun s0 s3 h0 _ hs3 _ => by
        rcases hrS : ctx.rs with ⟨bs⟩; simp only [C.Space.get, hrS, hsr3] at h0 hs3
        rw [Option.some.inj (hs3.symm.trans h0)]; exact srcMono_refl _,
      by simpa using warnPotOk_trans hm01 (fun s1 s3 h1s _ hs3 _ => by
        rcases hrS : ctx.rs with ⟨bs⟩
        have hh : h3.srcs = h1.srcs := by rcases hr : ctx.rmrk with ⟨bm⟩; rfl
        simp only [C.Space.get, hrS, hh] at h1s hs3
        rw [Option.some.inj (hs3.symm.trans h1s)]; exact srcMono_refl _) hw01 hw13 (by omega) hp1⟩
    unfold get_soi
    rw [C.run_bind, hldc]; dsimp only
    rw [kerr, C.run_bind, htr1]; dsimp only
    rw [kmrk, C.run_bind, hl1]; dsimp only
    simp only [hsawF, Bool.false_eq_true, ↓reduceIte]
    rw [C.run_bind, hldc1]; dsimp only
    rw [C.run_bind, hstDc]; dsimp only
    rw [hmrkEq2, C.run_bind, hl2]; dsimp only; rw [C.run_bind, hstMrk]; rfl

/-! ## `get_dri` -/

theorem get_dri_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 4 < 2 ^ 63) :
    ∃ res h',
      C.run (get_dri (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcStrict srcs0[0]! srcs'[0]!) ∧
        WarnPotOk ctx h h' 4
      | _ => True := by
  obtain ⟨dcs, hgdc, hszdc, kerr, _, _, _, _, ksrc⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _, _, _, _, _, hcur0⟩ := parserEnv_get_src hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc hszsrc
  have htr0 := nibBibTrack_init ctx h srcs hgsrc
  have hbd0 : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
    nibBibTrack_bd hp hp htr0 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
  obtain ⟨res1, h1, hrun1, hp1, hd1, hmr1, _, hcp1, _, _, _, _, _, _, hpost1⟩ :=
    input2Bytes_parser hp srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer hcur0 hbd0
  have hst01 : DecompHeaderStable ctx h h1 := decompHeaderStable_of_same hd1 hmr1 hcp1
  cases res1 with
  | none =>
    refine ⟨.ok false, h1, ?_, hp1, hst01, trivial⟩
    unfold get_dri
    rw [C.run_bind, hldc]; dsimp only
    rw [ksrc, C.run_bind, hlsrc]; dsimp only
    rw [C.run_bind, hrun1]; rfl
  | some x =>
    rcases x with ⟨lenRaw, nib1, bib1⟩
    rcases hpost1 with ⟨_, _, hcur1, hce1⟩
    obtain ⟨htr1, _⟩ := nibBibTrack_input2Bytes_step hp hp htr0 (by omega) (by omega) hce1
    by_cases hbadLen : (lenRaw != 4) = true
    · obtain ⟨dcs1, hgdc1, _, kerr1, _⟩ := parserEnv_get_dc hp1
      obtain ⟨h_err, herr_run, hp_err, hstErr⟩ := errexit_stable_parser hp1 JERR_BAD_LENGTH
      have herr_run' : C.run (errexit dcs[0]!.err JERR_BAD_LENGTH) h1 = .ok (.errExit JERR_BAD_LENGTH, h_err) := by
        rw [kerr]; exact herr_run
      refine ⟨.errExit JERR_BAD_LENGTH, h_err, ?_, hp_err, decompHeaderStable_trans hp hp1 hst01 hstErr, trivial⟩
      unfold get_dri
      rw [C.run_bind, hldc]; dsimp only
      rw [ksrc, C.run_bind, hlsrc]; dsimp only
      rw [C.run_bind, hrun1]; dsimp only
      simp only [hbadLen, ↓reduceIte, C.run_bind, herr_run']; rfl
    · have hbadLenF : (lenRaw != 4) = false := by cases hc : (lenRaw != 4) <;> simp_all
      have hbd1 : ∀ errs, C.Space.get h1 ctx.rerr = some errs → 0 < errs.size →
          errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
        nibBibTrack_bd hp hp1 htr1 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
          have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
      obtain ⟨res2, h2, hrun2, hp2, hd2, hmr2, _, hcp2, _, _, _, _, _, _, hpost2⟩ :=
        input2Bytes_parser hp1 nib1 bib1 hcur1 hbd1
      have hst02 := decompHeaderStable_trans hp hp1 hst01 (decompHeaderStable_of_same hd2 hmr2 hcp2)
      cases res2 with
      | none =>
        refine ⟨.ok false, h2, ?_, hp2, hst02, trivial⟩
        unfold get_dri
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        simp only [hbadLenF, Bool.false_eq_true, ↓reduceIte]
        rw [C.run_bind, hrun2]; rfl
      | some y =>
        rcases y with ⟨tmp, nib2, bib2⟩
        rcases hpost2 with ⟨_, _, hcur2, hce2⟩
        obtain ⟨htr2, hstr2⟩ := nibBibTrack_input2Bytes_step hp hp1 htr1 (by omega) (by omega) hce2
        obtain ⟨dcs2, hgdc2, hszdc2, kerr2, _⟩ := parserEnv_get_dc hp2
        obtain ⟨h3, htr3_run, hp3, hd3, hmr3, _, _, hcp3, _, _, _, hby3, _, hco3, hnw3⟩ :=
          tracems1_nonneg_parser hp2 1 JTRC_DRI tmp (by decide)
        have htr3_run' : C.run (tracems1 dcs[0]!.err 1 JTRC_DRI tmp) h2 = .ok ((), h3) := by
          rw [kerr]; exact htr3_run
        have htr3 := nibBibTrack_err_nw_same hp2 htr2 hnw3
        have hst03 := decompHeaderStable_trans hp hp2 hst02 (decompHeaderStable_of_same hd3 hmr3 hcp3)
        obtain ⟨dcs3, hgdc3, hszdc3, _⟩ := parserEnv_get_dc hp3
        have hldc3 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc3 hszdc3
        have hroDc3 : C.Space.ro h3 (C.DecompRef.decomp ctx.bdc) = false := rfl
        let dc4 := { dcs3[0]! with restartInterval := UInt32.ofNat tmp.toInt.toNat }
        have hstDc := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc4) hgdc3 hroDc3 hszdc3
        let h4 := C.Space.put h3 (C.DecompRef.decomp ctx.bdc) (dcs3.set! 0 dc4)
        have hp4 : ParserEnv ctx h4 := parserEnv_put_dc_same hp3 hgdc3 hszdc3
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have htr4 := nibBibTrack_err_same htr3 rfl
        have hst34 : DecompHeaderStable ctx h3 h4 := by
          refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
            (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
          intro da db hga _ hgb _
          have ha := Option.some.inj (hga.symm.trans hgdc3)
          have hg4 : C.Space.get h4 (C.DecompRef.decomp ctx.bdc) = some (dcs3.set! 0 dc4) := by
            simp [h4, C.Space.get, C.Space.put]
          have hb := Option.some.inj (hgb.symm.trans hg4)
          rw [ha, hb, set0_bang_m dcs3 hszdc3 dc4]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨h5, hsync, hp5, hd5, hmr5, he5, _, hcp5, _, _, _, _, _, _, hsrc5⟩ :=
          inputSync_parser hp4 nib2 bib2 (curValid_bytes_irrel hby3 hco3 hcur2)
        have hst05 := decompHeaderStable_trans hp hp3 hst03
          (decompHeaderStable_trans hp3 hp4 hst34 (decompHeaderStable_of_same hd5 hmr5 hcp5))
        obtain ⟨hw, _⟩ := nibBibTrack_to_warnPotOk_src hp hp4 htr4 (by omega) he5 hsrc5
        have hstr := nibBibTrack_to_srcStrict hp hp4 htr4 hstr2 hsrc5
        refine ⟨.ok true, h5, ?_, hp5, hst05, ⟨hstr, by simpa using hw⟩⟩
        unfold get_dri
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        simp only [hbadLenF, Bool.false_eq_true, ↓reduceIte]
        rw [C.run_bind, hrun2]; dsimp only
        rw [C.run_bind, htr3_run']; dsimp only
        rw [C.run_bind, hldc3]; dsimp only
        rw [C.run_bind, hstDc]; dsimp only
        rw [C.run_bind, hsync]; rfl

/-! ## `get_dac` -/

theorem get_dac_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63) :
    ∃ res h',
      C.run (get_dac (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcStrict srcs0[0]! srcs'[0]!) ∧
        WarnPotOk ctx h h' (2 ^ 16)
      | _ => True := by
  obtain ⟨dcs, hgdc, hszdc, kerr, _, _, _, _, ksrc⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _, _, _, _, _, hcur0⟩ := parserEnv_get_src hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc hszsrc
  have htr0 := nibBibTrack_init ctx h srcs hgsrc
  have hbd0 : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
    nibBibTrack_bd hp hp htr0 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
  obtain ⟨res1, h1, hrun1, hp1, hd1, hmr1, _, hcp1, _, _, _, _, _, _, hpost1⟩ :=
    input2Bytes_parser hp srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer hcur0 hbd0
  have hst01 : DecompHeaderStable ctx h h1 := decompHeaderStable_of_same hd1 hmr1 hcp1
  cases res1 with
  | none =>
    refine ⟨.ok false, h1, ?_, hp1, hst01, trivial⟩
    unfold get_dac
    rw [C.run_bind, hldc]; dsimp only
    rw [ksrc, C.run_bind, hlsrc]; dsimp only
    rw [C.run_bind, hrun1]; rfl
  | some x =>
    rcases x with ⟨lenRaw, nib1, bib1⟩
    rcases hpost1 with ⟨hlen0, hlenHi, hcur1, hce1⟩
    obtain ⟨htr1, hstr1⟩ := nibBibTrack_input2Bytes_step hp hp htr0 (by omega) (by omega) hce1
    let initLen : Int64 := Int64.ofInt (lenRaw.toInt - 2)
    have hinitLen : initLen.toInt = lenRaw.toInt - 2 := by
      change (Int64.ofInt (lenRaw.toInt - 2)).toInt = lenRaw.toInt - 2
      rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    let Inv (k : Nat) (hCur : C.Heap) (s : DacLoopState) : Prop :=
      ParserEnv ctx hCur ∧
      DecompHeaderStable ctx h hCur ∧
      (s.done = true → s.ret ≠ .ok true) ∧
      (!s.done →
        -2 ≤ s.length.toInt ∧ s.length.toInt ≤ 65533 ∧
        k = (if s.length.toInt ≤ 0 then 0 else s.length.toInt.toNat + 1) ∧
        CurValid hCur s.nib s.bib ∧
        NibBibTrack ctx h hCur s.nib s.bib (-8) (if s.length.toInt = -2 then 2 else 2 + (65533 - s.length.toInt)) ∧
        (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          isConstEofPtr s.nib = true ∨ s.bib.toNat < srcs0[0]!.bytesInBuffer.toNat))
    let Post (hCur : C.Heap) (s : DacLoopState) : Prop :=
      ParserEnv ctx hCur ∧
      DecompHeaderStable ctx h hCur ∧
      (s.done = true → s.ret ≠ .ok true) ∧
      (!s.done →
        s.length.toInt ≤ 0 ∧
        CurValid hCur s.nib s.bib ∧
        NibBibTrack ctx h hCur s.nib s.bib (-8) 65536 ∧
        (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          isConstEofPtr s.nib = true ∨ s.bib.toNat < srcs0[0]!.bytesInBuffer.toNat))
    let s0 : DacLoopState := { done := false, ret := .ok true, length := initLen, nib := nib1, bib := bib1 }
    let k0 : Nat := if initLen.toInt ≤ 0 then 0 else initLen.toInt.toNat + 1
    have hinit : Inv k0 h1 s0 := by
      refine ⟨hp1, hst01, (fun h => by simp [s0] at h), fun _ => ⟨by rw [hinitLen]; omega, by rw [hinitLen]; omega, rfl, hcur1,
        nibBibTrack_mono htr1 (by omega) (by rw [hinitLen]; split <;> omega), hstr1⟩⟩
    have hk0Lt : k0 < C.fuel := by unfold C.fuel; dsimp only [k0]; split <;> omega
    obtain ⟨st, h2, hloop, hpost⟩ :=
      cwhile_terminates
        (fun (s : DacLoopState) => pure (!s.done && s.length > 0, s))
        (fun (s : DacLoopState) => do
          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
          | none => return { s with done := true, ret := .ok false }
          | some (index, nibA, bibA) =>
            match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
            | none => return { s with done := true, ret := .ok false }
            | some (val, nibB, bibB) =>
              let len' := Int64.ofInt (s.length.toInt - 2)
              let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
              tracems2 dcCur.err 1 JTRC_DAC index val
              if index < 0 || index ≥ 2 * NUM_ARITH_TBLS then
                let _ ← errexit1 dcCur.err JERR_DAC_INDEX index
                return { s with done := true, ret := .errExit JERR_DAC_INDEX }
              if index ≥ NUM_ARITH_TBLS then
                let idx := (index - NUM_ARITH_TBLS).toInt.toNat
                Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcCur with arithAcK := dcCur.arithAcK.set! idx (UInt8.ofNat val.toInt.toNat) }
              else
                let idx := index.toInt.toNat
                let lVal := UInt8.ofNat (val.toInt.toNat &&& 0x0F)
                let uVal := UInt8.ofNat (val.toInt.toNat >>> 4)
                let dcNew := {
                  dcCur with
                  arithDcL := dcCur.arithDcL.set! idx lVal
                  arithDcU := dcCur.arithDcU.set! idx uVal
                }
                Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) dcNew
                if lVal > uVal then
                  let _ ← errexit1 dcNew.err JERR_DAC_VALUE val
                  return { s with done := true, ret := .errExit JERR_DAC_VALUE }
              return { done := false, ret := .ok true, length := len', nib := nibB, bib := bibB })
        Inv Post
        (fun k hCur s ⟨hpC, hstC, hnrC, hactive⟩ => by
          by_cases hcond : (!s.done && s.length > 0) = true
          · refine ⟨true, s, hCur, by simp [hcond], ?_⟩
            simp only [↓reduceIte]
            have hdoneF : s.done = false := by cases hc : s.done <;> simp_all
            have hsgt : s.length > 0 := by
              by_cases hgt : s.length > 0
              · exact hgt
              · simp [hdoneF, hgt] at hcond
            have hspos : 0 < s.length.toInt := Int64.lt_iff_toInt_lt.mp hsgt
            obtain ⟨hsle2, hslenHi, hkEq, hcurS, htrS, _⟩ := hactive (by simp [hdoneF])
            have hbdA : s.bib = 0 → ∀ errs, C.Space.get hCur ctx.rerr = some errs → 0 < errs.size →
                errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
              nibBibTrack_bd hp hpC htrS (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
            obtain ⟨resA, hA, hrunA, hpA, hdA, hmrA, _, hcpA, _, _, _, _, _, _, hpostA⟩ :=
              inputByte_parser hpC s.nib s.bib hcurS hbdA
            have hstCA := decompHeaderStable_trans hp hpC hstC (decompHeaderStable_of_same hdA hmrA hcpA)
            cases resA with
            | none =>
              refine ⟨0, { s with done := true, ret := .ok false }, hA, ?_, ?_, hpA, hstCA,
                (fun _ hno => by cases hno), fun hno => by simp at hno⟩
              · rw [C.run_bind, hrunA]; rfl
              · simp only [hkEq, show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]; omega
            | some pA =>
              rcases pA with ⟨index, nibA, bibA⟩
              rcases hpostA with ⟨_, _, hcurA, hceA⟩
              obtain ⟨htrA, _⟩ := nibBibTrack_inputByte_step hp hpC htrS (by omega) (by omega) hceA
              have hbdB : bibA = 0 → ∀ errs, C.Space.get hA ctx.rerr = some errs → 0 < errs.size →
                  errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
                nibBibTrack_bd hp hpA htrA (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                  have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
              obtain ⟨resB, hB, hrunB, hpB, hdB, hmrB, _, hcpB, _, _, _, _, _, _, hpostB⟩ :=
                inputByte_parser hpA nibA bibA hcurA hbdB
              have hstCB := decompHeaderStable_trans hp hpA hstCA (decompHeaderStable_of_same hdB hmrB hcpB)
              cases resB with
              | none =>
                refine ⟨0, { s with done := true, ret := .ok false }, hB, ?_, ?_, hpB, hstCB,
                  (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                · rw [C.run_bind, hrunA]; dsimp only; rw [C.run_bind, hrunB]; rfl
                · simp only [hkEq, show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]; omega
              | some pB =>
                rcases pB with ⟨val, nibB, bibB⟩
                rcases hpostB with ⟨_, _, hcurB, hceB⟩
                obtain ⟨htrB, hstrB⟩ := nibBibTrack_inputByte_step hp hpA htrA (by omega) (by omega) hceB
                obtain ⟨dcsB, hgdcB, hszdcB, kerrB, _⟩ := parserEnv_get_dc hpB
                have hldcB := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcB hszdcB
                obtain ⟨hT, htrT_run, hpT, hdT, hmrT, _, _, hcpT, _, _, _, hbyT, _, hcoT, hnwT⟩ :=
                  tracems2_nonneg_parser hpB 1 JTRC_DAC index val (by decide)
                have htrT_run' : C.run (tracems2 dcsB[0]!.err 1 JTRC_DAC index val) hB = .ok ((), hT) := by
                  rw [kerrB]; exact htrT_run
                have hstCT := decompHeaderStable_trans hp hpB hstCB (decompHeaderStable_of_same hdT hmrT hcpT)
                have htrT := nibBibTrack_err_nw_same hpB htrB hnwT
                by_cases hidxBad : (index < 0 || index ≥ 2 * NUM_ARITH_TBLS) = true
                · obtain ⟨dcsT, hgdcT, _, kerrT, _⟩ := parserEnv_get_dc hpT
                  obtain ⟨hE, herr_run, hpE, hstTE⟩ := errexit1_stable_parser hpT JERR_DAC_INDEX index
                  have herr_run' : C.run (errexit1 dcsB[0]!.err JERR_DAC_INDEX index) hT = .ok (.errExit JERR_DAC_INDEX, hE) := by
                    rw [kerrB]; exact herr_run
                  refine ⟨0, { s with done := true, ret := .errExit JERR_DAC_INDEX }, hE, ?_, ?_, hpE,
                    decompHeaderStable_trans hp hpT hstCT hstTE, (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                  · rw [C.run_bind, hrunA]; dsimp only
                    rw [C.run_bind, hrunB]; dsimp only
                    rw [C.run_bind, hldcB]; dsimp only
                    rw [C.run_bind, htrT_run']; dsimp only
                    simp only [hidxBad, ↓reduceIte, C.run_bind, herr_run']; rfl
                  · simp only [hkEq, show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]; omega
                · have hidxGood : (index < 0 || index ≥ 2 * NUM_ARITH_TBLS) = false := by
                    cases hc : (index < 0 || index ≥ 2 * NUM_ARITH_TBLS) <;> simp_all
                  obtain ⟨dcsT, hgdcT, hszdcT, kerrT, _⟩ := parserEnv_get_dc hpT
                  have hdEqTB : dcsT = dcsB := by
                    simp only [C.Space.get] at hgdcB hgdcT; rw [hdT] at hgdcT
                    exact Option.some.inj (hgdcT.symm.trans hgdcB)
                  have hroDcT : C.Space.ro hT (C.DecompRef.decomp ctx.bdc) = false := rfl
                  let len' := Int64.ofInt (s.length.toInt - 2)
                  have hlen'To : len'.toInt = s.length.toInt - 2 := by
                    change (Int64.ofInt (s.length.toInt - 2)).toInt = s.length.toInt - 2
                    rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
                    exact Int.bmod_eq_of_le (by omega) (by omega)
                  let k' : Nat := if len'.toInt ≤ 0 then 0 else len'.toInt.toNat + 1
                  have hkLt : k' < k := by
                    dsimp only [k']
                    rw [hkEq]
                    simp only [show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]
                    rw [hlen'To]; split <;> omega
                  by_cases hge16 : index ≥ NUM_ARITH_TBLS
                  · let idx := (index - NUM_ARITH_TBLS).toInt.toNat
                    let dcNew := { dcsB[0]! with arithAcK := dcsB[0]!.arithAcK.set! idx (UInt8.ofNat val.toInt.toNat) }
                    have hstDc := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcNew)
                      (hdEqTB ▸ hgdcT) hroDcT (hdEqTB ▸ hszdcT)
                    let hU := C.Space.put hT (C.DecompRef.decomp ctx.bdc) (dcsB.set! 0 dcNew)
                    have hpU : ParserEnv ctx hU := parserEnv_put_dc_same hpT (hdEqTB ▸ hgdcT) (hdEqTB ▸ hszdcT)
                      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    have hstTU : DecompHeaderStable ctx hT hU := by
                      refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
                        (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
                      intro da db hga _ hgb _
                      have ha := Option.some.inj (hga.symm.trans (hdEqTB ▸ hgdcT))
                      have hgU : C.Space.get hU (C.DecompRef.decomp ctx.bdc) = some (dcsB.set! 0 dcNew) := by
                        simp [hU, C.Space.get, C.Space.put]
                      have hb := Option.some.inj (hgb.symm.trans hgU)
                      rw [ha, hb, set0_bang_m dcsB (hdEqTB ▸ hszdcT) dcNew]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                    have hcurU : CurValid hU nibB bibB := curValid_bytes_irrel hbyT hcoT hcurB
                    have htrU : NibBibTrack ctx h hU nibB bibB (-8) (if len'.toInt = -2 then 2 else 2 + (65533 - len'.toInt)) :=
                      nibBibTrack_mono (nibBibTrack_err_same htrT (by rfl)) (by omega) (by rw [hlen'To]; split <;> split <;> omega)
                    refine ⟨k', { done := false, ret := .ok true, length := len', nib := nibB, bib := bibB },
                      hU, ?_, hkLt, hpU, decompHeaderStable_trans hp hpT hstCT hstTU, (fun hno => by simp at hno), fun _ => ?_⟩
                    · rw [C.run_bind, hrunA]; dsimp only
                      rw [C.run_bind, hrunB]; dsimp only
                      rw [C.run_bind, hldcB]; dsimp only
                      rw [C.run_bind, htrT_run']; dsimp only
                      simp only [hidxGood, Bool.false_eq_true, ↓reduceIte, eq_true hge16]
                      rw [C.run_bind, hstDc]; rfl
                    · exact ⟨by rw [hlen'To]; omega, by rw [hlen'To]; omega, rfl, hcurU, htrU, hstrB⟩
                  · let idx := index.toInt.toNat
                    let lVal := UInt8.ofNat (val.toInt.toNat &&& 0x0F)
                    let uVal := UInt8.ofNat (val.toInt.toNat >>> 4)
                    let dcNew := {
                      dcsB[0]! with
                      arithDcL := dcsB[0]!.arithDcL.set! idx lVal
                      arithDcU := dcsB[0]!.arithDcU.set! idx uVal
                    }
                    have hstDc := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcNew)
                      (hdEqTB ▸ hgdcT) hroDcT (hdEqTB ▸ hszdcT)
                    let hU := C.Space.put hT (C.DecompRef.decomp ctx.bdc) (dcsB.set! 0 dcNew)
                    have hpU : ParserEnv ctx hU := parserEnv_put_dc_same hpT (hdEqTB ▸ hgdcT) (hdEqTB ▸ hszdcT)
                      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    have hstTU : DecompHeaderStable ctx hT hU := by
                      refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
                        (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
                      intro da db hga _ hgb _
                      have ha := Option.some.inj (hga.symm.trans (hdEqTB ▸ hgdcT))
                      have hgU : C.Space.get hU (C.DecompRef.decomp ctx.bdc) = some (dcsB.set! 0 dcNew) := by
                        simp [hU, C.Space.get, C.Space.put]
                      have hb := Option.some.inj (hgb.symm.trans hgU)
                      rw [ha, hb, set0_bang_m dcsB (hdEqTB ▸ hszdcT) dcNew]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                    have hstCU := decompHeaderStable_trans hp hpT hstCT hstTU
                    by_cases hlu : lVal > uVal
                    · dsimp only [lVal, uVal] at hlu
                      obtain ⟨dcsU, hgdcU, _, kerrU, _⟩ := parserEnv_get_dc hpU
                      obtain ⟨hE, herr_run, hpE, hstUE⟩ := errexit1_stable_parser hpU JERR_DAC_VALUE val
                      have herr_run' : C.run (errexit1 dcNew.err JERR_DAC_VALUE val) hU = .ok (.errExit JERR_DAC_VALUE, hE) := by
                        rw [show dcNew.err = .ref ctx.rerr 0 from kerrB]; exact herr_run
                      refine ⟨0, { s with done := true, ret := .errExit JERR_DAC_VALUE }, hE, ?_, ?_, hpE,
                        decompHeaderStable_trans hp hpU hstCU hstUE, (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                      · rw [C.run_bind, hrunA]; dsimp only
                        rw [C.run_bind, hrunB]; dsimp only
                        rw [C.run_bind, hldcB]; dsimp only
                        rw [C.run_bind, htrT_run']; dsimp only
                        simp only [hidxGood, Bool.false_eq_true, ↓reduceIte, eq_false hge16]
                        rw [C.run_bind, hstDc]; dsimp only
                        simp only [eq_true hlu, ↓reduceIte]
                        rw [C.run_bind]; erw [herr_run']; rfl
                      · simp only [hkEq, show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]; omega
                    · dsimp only [lVal, uVal] at hlu
                      have hcurU : CurValid hU nibB bibB := curValid_bytes_irrel hbyT hcoT hcurB
                      have htrU : NibBibTrack ctx h hU nibB bibB (-8) (if len'.toInt = -2 then 2 else 2 + (65533 - len'.toInt)) :=
                        nibBibTrack_mono (nibBibTrack_err_same htrT (by rfl)) (by omega) (by rw [hlen'To]; split <;> split <;> omega)
                      refine ⟨k', { done := false, ret := .ok true, length := len', nib := nibB, bib := bibB },
                        hU, ?_, hkLt, hpU, hstCU, (fun hno => by simp at hno), fun _ => ?_⟩
                      · rw [C.run_bind, hrunA]; dsimp only
                        rw [C.run_bind, hrunB]; dsimp only
                        rw [C.run_bind, hldcB]; dsimp only
                        rw [C.run_bind, htrT_run']; dsimp only
                        simp only [hidxGood, Bool.false_eq_true, ↓reduceIte, eq_false hge16]
                        rw [C.run_bind, hstDc]; dsimp only
                        simp only [eq_false hlu, ↓reduceIte]; rfl
                      · exact ⟨by rw [hlen'To]; omega, by rw [hlen'To]; omega, rfl, hcurU, htrU, hstrB⟩
          · have hcondF : (!s.done && s.length > 0) = false := by cases hc : (!s.done && s.length > 0) <;> simp_all
            refine ⟨false, s, hCur, (by simp only [C.run, pure, hcondF]), ?_⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨hpC, hstC, hnrC, fun hnd => ?_⟩
            obtain ⟨hsle2, _, _, hcurS, htrS, hstrS⟩ := hactive hnd
            have hle0 : s.length.toInt ≤ 0 := by
              have hnotgt : ¬(s.length > 0) := by
                have hdF : s.done = false := by cases hd : s.done <;> simp_all
                intro hgt; simp [hdF, hgt] at hcondF
              by_cases hpos : s.length.toInt ≤ 0
              · exact hpos
              · exact False.elim (hnotgt (Int64.lt_iff_toInt_lt.mpr (by change (0 : Int) < s.length.toInt; omega)))
            exact ⟨hle0, hcurS, nibBibTrack_mono htrS (by omega) (by by_cases hneg2 : s.length.toInt = -2 <;> simp [hneg2] <;> omega), hstrS⟩)
        hk0Lt hinit
    rcases hpost with ⟨hp2, hst02, hnr2, hfin⟩
    dsimp only [s0, initLen] at hloop
    by_cases hdone : st.done = true
    · refine ⟨st.ret, h2, ?_, hp2, hst02, ?_⟩
      · unfold get_dac
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind]; erw [hloop]; dsimp only
        simp only [hdone, ↓reduceIte]; rfl
      · cases hrt : st.ret with
        | errExit _ => trivial
        | ok b =>
          cases b with
          | false => trivial
          | true => exact absurd hrt (hnr2 hdone)
    · have hdoneF : st.done = false := by cases hc : st.done <;> simp_all
      obtain ⟨hstlen, hcurSt, htrSt, hstrSt⟩ := hfin (by simp [hdoneF])
      by_cases hne0 : (st.length != 0) = true
      · obtain ⟨dcs2, hgdc2, _, kerr2, _⟩ := parserEnv_get_dc hp2
        obtain ⟨h_err, herr_run, hp_err, hstErr⟩ := errexit_stable_parser hp2 JERR_BAD_LENGTH
        have herr_run' : C.run (errexit dcs2[0]!.err JERR_BAD_LENGTH) h2 = .ok (.errExit JERR_BAD_LENGTH, h_err) := by
          rw [kerr2]; exact herr_run
        refine ⟨.errExit JERR_BAD_LENGTH, h_err, ?_, hp_err, decompHeaderStable_trans hp hp2 hst02 hstErr, trivial⟩
        unfold get_dac
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind]; erw [hloop]; dsimp only
        simp only [hdoneF, Bool.false_eq_true, ↓reduceIte, hne0, C.run_bind, herr_run',
          ptr_load_ok hgdc2 ‹0 < dcs2.size›]; rfl
      · have hne0F : (st.length != 0) = false := by cases hc : (st.length != 0) <;> simp_all
        obtain ⟨h3, hsync, hp3, hd3, hmr3, he3, _, hcp3, _, _, _, _, _, _, hsrc3⟩ :=
          inputSync_parser hp2 st.nib st.bib hcurSt
        have hst03 := decompHeaderStable_trans hp hp2 hst02 (decompHeaderStable_of_same hd3 hmr3 hcp3)
        obtain ⟨hw, _⟩ := nibBibTrack_to_warnPotOk_src hp hp2 htrSt (by omega) he3 hsrc3
        have hstr := nibBibTrack_to_srcStrict hp hp2 htrSt hstrSt hsrc3
        refine ⟨.ok true, h3, ?_, hp3, hst03, ⟨hstr, ?_⟩⟩
        · unfold get_dac
          rw [C.run_bind, hldc]; dsimp only
          rw [ksrc, C.run_bind, hlsrc]; dsimp only
          rw [C.run_bind, hrun1]; dsimp only
          rw [C.run_bind]; erw [hloop]; dsimp only
          simp only [hdoneF, Bool.false_eq_true, ↓reduceIte, hne0F, C.run_bind, hsync]; rfl
        · intro e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
          obtain ⟨wf, wt⟩ := hw e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
          exact ⟨wf, fun ht => by have := wt ht; omega⟩

/-! ## `examine_app0`, `examine_app14`, `get_interesting_appn`, `skip_variable` -/

theorem examine_app0_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (data : Array UInt8) (datalen : UInt32) (remaining : Int64)
    (hbd : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63) :
    ∃ h',
      C.run (examine_app0 (.ref (.decomp ctx.bdc) 0) data datalen remaining) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      h'.srcs = h.srcs ∧ h'.consts = h.consts ∧ h'.bytes = h.bytes ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 1) := by
  obtain ⟨dcs, hgdc, hszdc, kerr, _⟩ := parserEnv_get_dc hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  let totallen : Int64 := Int64.ofInt (Int.ofNat datalen.toNat + remaining.toInt)
  by_cases hjfif : (datalen ≥ APP0_DATA_LEN &&
      data[0]! == 0x4A && data[1]! == 0x46 && data[2]! == 0x49 && data[3]! == 0x46 && data[4]! == 0) = true
  · let xDens := UInt16.ofNat ((data[8]!.toNat <<< 8) + data[9]!.toNat)
    let yDens := UInt16.ofNat ((data[10]!.toNat <<< 8) + data[11]!.toNat)
    let dc1 : C.JpegDecompressStruct := {
      dcs[0]! with
      sawJFIFMarker := TRUE
      jfifMajorVersion := data[5]!
      jfifMinorVersion := data[6]!
      densityUnit := data[7]!
      xDensity := xDens
      yDensity := yDens
    }
    have hroDc0 : C.Space.ro h (C.DecompRef.decomp ctx.bdc) = false := rfl
    have hstDc := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc1) hgdc hroDc0 hszdc
    let h1 := C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc1)
    have hp1 : ParserEnv ctx h1 := parserEnv_put_dc_same hp hgdc hszdc
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hst01 : DecompHeaderStable ctx h h1 := by
      refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
        (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
      intro da db hga _ hgb _
      have ha := Option.some.inj (hga.symm.trans hgdc)
      have hg1 : C.Space.get h1 (C.DecompRef.decomp ctx.bdc) = some (dcs.set! 0 dc1) := by
        simp [h1, C.Space.get, C.Space.put]
      have hb := Option.some.inj (hgb.symm.trans hg1)
      rw [ha, hb, set0_bang_m dcs hszdc dc1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hrunWarn : ∃ h2,
        C.run (if dc1.jfifMajorVersion != 1 then
          warnms2 dc1.err JWRN_JFIF_MAJOR (Int32.ofNat dc1.jfifMajorVersion.toNat) (Int32.ofNat dc1.jfifMinorVersion.toNat)
          else pure ()) h1 = .ok ((), h2) ∧
        ParserEnv ctx h2 ∧ DecompHeaderStable ctx h1 h2 ∧
        h2.srcs = h1.srcs ∧ h2.consts = h1.consts ∧ h2.bytes = h1.bytes ∧
        (∀ errs errs', C.Space.get h1 ctx.rerr = some errs → 0 < errs.size →
          C.Space.get h2 ctx.rerr = some errs' → 0 < errs'.size ∧
          errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 1) := by
      by_cases hmaj : (dc1.jfifMajorVersion != 1) = true
      · obtain ⟨dcs1, hgdc1, _, kerr1, _⟩ := parserEnv_get_dc hp1
        have hbd1 : ∀ errs, C.Space.get h1 ctx.rerr = some errs → 0 < errs.size →
            errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := by
          intro errs hge hsz; exact hbd errs hge hsz
        obtain ⟨h2, hw2, hp2, hd2, hmr2, hsr2, _, hcp2, _, _, _, hby2, _, hco2, hnw2⟩ :=
          warnms2_parser hp1 JWRN_JFIF_MAJOR (Int32.ofNat dc1.jfifMajorVersion.toNat) (Int32.ofNat dc1.jfifMinorVersion.toNat) hbd1
        have hw2' : C.run (warnms2 dc1.err JWRN_JFIF_MAJOR
            (Int32.ofNat dc1.jfifMajorVersion.toNat) (Int32.ofNat dc1.jfifMinorVersion.toNat)) h1 = .ok ((), h2) := by
          have kerr1' : dc1.err = dcs1[0]!.err := by
            have hg1 : C.Space.get h1 (C.DecompRef.decomp ctx.bdc) = some (dcs.set! 0 dc1) := by
              simp [h1, C.Space.get, C.Space.put]
            have heq := Option.some.inj (hgdc1.symm.trans hg1); rw [heq, set0_bang_m dcs hszdc dc1]
          rw [kerr1', kerr1]; exact hw2
        refine ⟨h2, ?_, hp2, decompHeaderStable_of_same hd2 hmr2 hcp2, hsr2, hco2, hby2, ?_⟩
        · simp only [hmaj, ↓reduceIte]; exact hw2'
        · intro errs errs' hg hsze hg'; obtain ⟨hsze', heq⟩ := hnw2 errs errs' hg hsze hg'; exact ⟨hsze', by omega⟩
      · have hmajF : (dc1.jfifMajorVersion != 1) = false := by cases hc : (dc1.jfifMajorVersion != 1) <;> simp_all
        refine ⟨h1, ?_, hp1, decompHeaderStable_refl ctx h1, rfl, rfl, rfl, ?_⟩
        · simp only [hmajF, Bool.false_eq_true, ↓reduceIte]; rfl
        · intro errs errs' hg hsze hg'; have := Option.some.inj (hg'.symm.trans hg); subst this; exact ⟨hsze, by omega⟩
    rcases hrunWarn with ⟨h2, hw2, hp2, hst12, hsr2, hco2, hby2, hnw2⟩
    have hst02 := decompHeaderStable_trans hp hp1 hst01 hst12
    obtain ⟨dcs2, hgdc2, _, kerr2, _⟩ := parserEnv_get_dc hp2
    obtain ⟨h3, htr3, hp3, hd3, hmr3, hsr3, _, hcp3, _, _, _, hby3, _, hco3, hnw3⟩ :=
      tracems5_nonneg_parser hp2 1 JTRC_JFIF
        (Int32.ofNat dc1.jfifMajorVersion.toNat) (Int32.ofNat dc1.jfifMinorVersion.toNat)
        (Int32.ofNat dc1.xDensity.toNat) (Int32.ofNat dc1.yDensity.toNat) (Int32.ofNat dc1.densityUnit.toNat) (by decide)
    have htr3' : C.run (tracems5 dc1.err 1 JTRC_JFIF
        (Int32.ofNat dc1.jfifMajorVersion.toNat) (Int32.ofNat dc1.jfifMinorVersion.toNat)
        (Int32.ofNat dc1.xDensity.toNat) (Int32.ofNat dc1.yDensity.toNat) (Int32.ofNat dc1.densityUnit.toNat)) h2 = .ok ((), h3) := by
      rw [show dc1.err = .ref ctx.rerr 0 from kerr]; exact htr3
    have hst03 := decompHeaderStable_trans hp hp2 hst02 (decompHeaderStable_of_same hd3 hmr3 hcp3)
    have hthumb1 : ∃ h4,
        C.run (if (data[12]! ||| data[13]!) != 0 then
          tracems2 dc1.err 1 JTRC_JFIF_THUMBNAIL (Int32.ofNat data[12]!.toNat) (Int32.ofNat data[13]!.toNat)
          else pure ()) h3 = .ok ((), h4) ∧
        ParserEnv ctx h4 ∧ DecompHeaderStable ctx h3 h4 ∧
        h4.srcs = h3.srcs ∧ h4.consts = h3.consts ∧ h4.bytes = h3.bytes ∧
        (∀ errs errs', C.Space.get h3 ctx.rerr = some errs → 0 < errs.size →
          C.Space.get h4 ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
      by_cases hth : ((data[12]! ||| data[13]!) != 0) = true
      · obtain ⟨dcs3, _, _, kerr3, _⟩ := parserEnv_get_dc hp3
        obtain ⟨h4, htr4, hp4, hd4, hmr4, hsr4, _, hcp4, _, _, _, hby4, _, hco4, hnw4⟩ :=
          tracems2_nonneg_parser hp3 1 JTRC_JFIF_THUMBNAIL (Int32.ofNat data[12]!.toNat) (Int32.ofNat data[13]!.toNat) (by decide)
        refine ⟨h4, ?_, hp4, decompHeaderStable_of_same hd4 hmr4 hcp4, hsr4, hco4, hby4, hnw4⟩
        simp only [hth, ↓reduceIte]; rw [show dc1.err = .ref ctx.rerr 0 from kerr]; exact htr4
      · have hthF : ((data[12]! ||| data[13]!) != 0) = false := by cases hc : ((data[12]! ||| data[13]!) != 0) <;> simp_all
        refine ⟨h3, ?_, hp3, decompHeaderStable_refl ctx h3, rfl, rfl, rfl, fun errs errs' hg hsz hg' => by
          rw [Option.some.inj (hg'.symm.trans hg)]; exact ⟨hsz, rfl⟩⟩
        simp only [hthF, Bool.false_eq_true, ↓reduceIte]; rfl
    rcases hthumb1 with ⟨h4, hth4, hp4, hst34, hsr4, hco4, hby4, hnw4⟩
    have hst04 := decompHeaderStable_trans hp hp3 hst03 hst34
    let remThumb : Int64 := Int64.ofInt (totallen.toInt - Int.ofNat APP0_DATA_LEN.toNat)
    have hthumb2 : ∃ h5,
        C.run (if remThumb.toInt != Int.ofNat data[12]!.toNat * Int.ofNat data[13]!.toNat * 3 then
          tracems1 dc1.err 1 JTRC_JFIF_BADTHUMBNAILSIZE (Int32.ofInt remThumb.toInt)
          else pure ()) h4 = .ok ((), h5) ∧
        ParserEnv ctx h5 ∧ DecompHeaderStable ctx h4 h5 ∧
        h5.srcs = h4.srcs ∧ h5.consts = h4.consts ∧ h5.bytes = h4.bytes ∧
        (∀ errs errs', C.Space.get h4 ctx.rerr = some errs → 0 < errs.size →
          C.Space.get h5 ctx.rerr = some errs' → 0 < errs'.size ∧ errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
      by_cases hbt : (remThumb.toInt != Int.ofNat data[12]!.toNat * Int.ofNat data[13]!.toNat * 3) = true
      · obtain ⟨dcs4, _, _, kerr4, _⟩ := parserEnv_get_dc hp4
        obtain ⟨h5, htr5, hp5, hd5, hmr5, hsr5, _, hcp5, _, _, _, hby5, _, hco5, hnw5⟩ :=
          tracems1_nonneg_parser hp4 1 JTRC_JFIF_BADTHUMBNAILSIZE (Int32.ofInt remThumb.toInt) (by decide)
        refine ⟨h5, ?_, hp5, decompHeaderStable_of_same hd5 hmr5 hcp5, hsr5, hco5, hby5, hnw5⟩
        simp only [hbt, ↓reduceIte]; rw [show dc1.err = .ref ctx.rerr 0 from kerr]; exact htr5
      · have hbtF : (remThumb.toInt != Int.ofNat data[12]!.toNat * Int.ofNat data[13]!.toNat * 3) = false := by
          cases hc : (remThumb.toInt != Int.ofNat data[12]!.toNat * Int.ofNat data[13]!.toNat * 3) <;> simp_all
        refine ⟨h4, ?_, hp4, decompHeaderStable_refl ctx h4, rfl, rfl, rfl, fun errs errs' hg hsz hg' => by
          rw [Option.some.inj (hg'.symm.trans hg)]; exact ⟨hsz, rfl⟩⟩
        simp only [hbtF, Bool.false_eq_true, ↓reduceIte]; rfl
    rcases hthumb2 with ⟨h5, hth5, hp5, hst45, hsr5, hco5, hby5, hnw5⟩
    have hst05 := decompHeaderStable_trans hp hp4 hst04 hst45
    refine ⟨h5, ?_, hp5, hst05, hsr5.trans (hsr4.trans (hsr3.trans hsr2)),
      hco5.trans (hco4.trans (hco3.trans hco2)), hby5.trans (hby4.trans (hby3.trans hby2)), ?_⟩
    · unfold examine_app0
      rw [C.run_bind, hldc]; dsimp only
      simp only [hjfif, ↓reduceIte]
      rw [C.run_bind, hstDc]; dsimp only
      dsimp only [dc1] at hw2 htr3' hth4 hth5
      -- `examine_app0` distributes subsequent statements into single-armed `if` branches:
      by_cases hmaj : (data[5]! != 1) = true
      · simp only [hmaj, ↓reduceIte] at hw2 ⊢
        rw [C.run_bind, hw2]; dsimp only
        rw [C.run_bind, htr3']; dsimp only
        by_cases hth : ((data[12]! ||| data[13]!) != 0) = true
        · simp only [hth, ↓reduceIte] at hth4 ⊢; rw [C.run_bind, hth4]; dsimp only; exact hth5
        · have hthF : ((data[12]! ||| data[13]!) != 0) = false := by cases hc : ((data[12]! ||| data[13]!) != 0) <;> simp_all
          simp only [hthF, Bool.false_eq_true, ↓reduceIte] at hth4 ⊢
          have hh4 : h4 = h3 := (Prod.mk.inj (Except.ok.inj hth4)).2.symm
          rw [← hh4]; exact hth5
      · have hmajF : (data[5]! != 1) = false := by cases hc : (data[5]! != 1) <;> simp_all
        simp only [hmajF, Bool.false_eq_true, ↓reduceIte] at hw2 ⊢
        have hh2 : h2 = h1 := (Prod.mk.inj (Except.ok.inj hw2)).2.symm
        dsimp only [h1] at htr3' hh2
        rw [← hh2, C.run_bind, htr3']; dsimp only
        by_cases hth : ((data[12]! ||| data[13]!) != 0) = true
        · simp only [hth, ↓reduceIte] at hth4 ⊢; rw [C.run_bind, hth4]; dsimp only; exact hth5
        · have hthF : ((data[12]! ||| data[13]!) != 0) = false := by cases hc : ((data[12]! ||| data[13]!) != 0) <;> simp_all
          simp only [hthF, Bool.false_eq_true, ↓reduceIte] at hth4 ⊢
          have hh4 : h4 = h3 := (Prod.mk.inj (Except.ok.inj hth4)).2.symm
          rw [← hh4]; exact hth5
    · intro errs errs' hg hsze hg'
      obtain ⟨errs2, hg2, hsz2, _⟩ := parserEnv_get_err hp2
      obtain ⟨errs3, hg3, hsz3, _⟩ := parserEnv_get_err hp3
      obtain ⟨errs4, hg4, hsz4, _⟩ := parserEnv_get_err hp4
      have hg1 : C.Space.get h1 ctx.rerr = some errs := hg
      obtain ⟨_, hw12⟩ := hnw2 errs errs2 hg1 hsze hg2
      obtain ⟨_, hw23⟩ := hnw3 errs2 errs3 hg2 hsz2 hg3
      obtain ⟨_, hw34⟩ := hnw4 errs3 errs4 hg3 hsz3 hg4
      obtain ⟨hsz5, hw45⟩ := hnw5 errs4 errs' hg4 hsz4 hg'
      exact ⟨hsz5, by rw [hw45, hw34, hw23]; exact hw12⟩
  · have hjfifF : (datalen ≥ APP0_DATA_LEN &&
        data[0]! == 0x4A && data[1]! == 0x46 && data[2]! == 0x49 && data[3]! == 0x46 && data[4]! == 0) = false := by
      cases hc : (datalen ≥ APP0_DATA_LEN &&
        data[0]! == 0x4A && data[1]! == 0x46 && data[2]! == 0x49 && data[3]! == 0x46 && data[4]! == 0) <;> simp_all
    by_cases hjfxx : (datalen ≥ 6 &&
        data[0]! == 0x4A && data[1]! == 0x46 && data[2]! == 0x58 && data[3]! == 0x58 && data[4]! == 0) = true
    · let tag := data[5]!
      let totI := Int32.ofInt totallen.toInt
      have hsub : ∃ h',
          C.run (if tag == 0x10 then tracems1 dcs[0]!.err 1 JTRC_THUMB_JPEG totI
            else if tag == 0x11 then tracems1 dcs[0]!.err 1 JTRC_THUMB_PALETTE totI
            else if tag == 0x13 then tracems1 dcs[0]!.err 1 JTRC_THUMB_RGB totI
            else tracems2 dcs[0]!.err 1 JTRC_JFIF_EXTENSION (Int32.ofNat tag.toNat) totI) h = .ok ((), h') ∧
          ParserEnv ctx h' ∧ DecompHeaderStable ctx h h' ∧
          h'.srcs = h.srcs ∧ h'.consts = h.consts ∧ h'.bytes = h.bytes ∧
          (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
            C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
            errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + 1) := by
        split
        · obtain ⟨h', hrun, hp', hd, hmr, hsr, _, hcp, _, _, _, hby, _, hco, hnw⟩ :=
            tracems1_nonneg_parser hp 1 JTRC_THUMB_JPEG totI (by decide)
          refine ⟨h', kerr ▸ hrun, hp', decompHeaderStable_of_same hd hmr hcp, hsr, hco, hby, fun e e' hg hsze hg' => by
            obtain ⟨hsz', heq⟩ := hnw e e' hg hsze hg'; rw [heq]; exact ⟨hsz', by omega⟩⟩
        · split
          · obtain ⟨h', hrun, hp', hd, hmr, hsr, _, hcp, _, _, _, hby, _, hco, hnw⟩ :=
              tracems1_nonneg_parser hp 1 JTRC_THUMB_PALETTE totI (by decide)
            refine ⟨h', kerr ▸ hrun, hp', decompHeaderStable_of_same hd hmr hcp, hsr, hco, hby, fun e e' hg hsze hg' => by
              obtain ⟨hsz', heq⟩ := hnw e e' hg hsze hg'; rw [heq]; exact ⟨hsz', by omega⟩⟩
          · split
            · obtain ⟨h', hrun, hp', hd, hmr, hsr, _, hcp, _, _, _, hby, _, hco, hnw⟩ :=
                tracems1_nonneg_parser hp 1 JTRC_THUMB_RGB totI (by decide)
              refine ⟨h', kerr ▸ hrun, hp', decompHeaderStable_of_same hd hmr hcp, hsr, hco, hby, fun e e' hg hsze hg' => by
                obtain ⟨hsz', heq⟩ := hnw e e' hg hsze hg'; rw [heq]; exact ⟨hsz', by omega⟩⟩
            · obtain ⟨h', hrun, hp', hd, hmr, hsr, _, hcp, _, _, _, hby, _, hco, hnw⟩ :=
                tracems2_nonneg_parser hp 1 JTRC_JFIF_EXTENSION (Int32.ofNat tag.toNat) totI (by decide)
              refine ⟨h', kerr ▸ hrun, hp', decompHeaderStable_of_same hd hmr hcp, hsr, hco, hby, fun e e' hg hsze hg' => by
                obtain ⟨hsz', heq⟩ := hnw e e' hg hsze hg'; rw [heq]; exact ⟨hsz', by omega⟩⟩
      rcases hsub with ⟨h', hrun', hp', hst', hsr', hco', hby', hnw'⟩
      refine ⟨h', ?_, hp', hst', hsr', hco', hby', hnw'⟩
      unfold examine_app0; rw [C.run_bind, hldc]; dsimp only
      simp only [hjfifF, Bool.false_eq_true, ↓reduceIte, hjfxx]; exact hrun'
    · have hjfxxF : (datalen ≥ 6 &&
          data[0]! == 0x4A && data[1]! == 0x46 && data[2]! == 0x58 && data[3]! == 0x58 && data[4]! == 0) = false := by
        cases hc : (datalen ≥ 6 &&
          data[0]! == 0x4A && data[1]! == 0x46 && data[2]! == 0x58 && data[3]! == 0x58 && data[4]! == 0) <;> simp_all
      obtain ⟨h', hrun', hp', hd', hmr', hsr', _, hcp', _, _, _, hby', _, hco', hnw'⟩ :=
        tracems1_nonneg_parser hp 1 JTRC_APP0 (Int32.ofInt totallen.toInt) (by decide)
      refine ⟨h', ?_, hp', decompHeaderStable_of_same hd' hmr' hcp', hsr', hco', hby', fun e e' hg hsze hg' => by
        obtain ⟨hsz', heq⟩ := hnw' e e' hg hsze hg'; rw [heq]; exact ⟨hsz', by omega⟩⟩
      unfold examine_app0; rw [C.run_bind, hldc]; dsimp only
      simp only [hjfifF, hjfxxF, Bool.false_eq_true, ↓reduceIte]; rw [kerr]; exact hrun'

theorem examine_app14_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (data : Array UInt8) (datalen : UInt32) (remaining : Int64) :
    ∃ h',
      C.run (examine_app14 (.ref (.decomp ctx.bdc) 0) data datalen remaining) h = .ok ((), h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      h'.srcs = h.srcs ∧ h'.consts = h.consts ∧ h'.bytes = h.bytes ∧
      (∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
        errs'[0]!.numWarnings = errs[0]!.numWarnings) := by
  obtain ⟨dcs, hgdc, hszdc, kerr, _⟩ := parserEnv_get_dc hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  by_cases had : (datalen ≥ APP14_DATA_LEN &&
      data[0]! == 0x41 && data[1]! == 0x64 && data[2]! == 0x6F && data[3]! == 0x62 && data[4]! == 0x65) = true
  · let ver := Int32.ofNat ((data[5]!.toNat <<< 8) + data[6]!.toNat)
    let fl0 := Int32.ofNat ((data[7]!.toNat <<< 8) + data[8]!.toNat)
    let fl1 := Int32.ofNat ((data[9]!.toNat <<< 8) + data[10]!.toNat)
    let xform := data[11]!
    obtain ⟨h1, htr1, hp1, hd1, hmr1, hsr1, _, hcp1, _, _, _, hby1, _, hco1, hnw1⟩ :=
      tracems4_nonneg_parser hp 1 JTRC_ADOBE ver fl0 fl1 (Int32.ofNat xform.toNat) (by decide)
    obtain ⟨dcs1, hgdc1, hszdc1, _⟩ := parserEnv_get_dc hp1
    have hroDc1 : C.Space.ro h1 (C.DecompRef.decomp ctx.bdc) = false := rfl
    let dc2 := { dcs1[0]! with sawAdobeMarker := TRUE, adobeTransform := xform }
    have hstDc := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc2) hgdc1 hroDc1 hszdc1
    let h2 := C.Space.put h1 (C.DecompRef.decomp ctx.bdc) (dcs1.set! 0 dc2)
    have hp2 : ParserEnv ctx h2 := parserEnv_put_dc_same hp1 hgdc1 hszdc1
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hst12 : DecompHeaderStable ctx h1 h2 := by
      refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
        (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
      intro da db hga _ hgb _
      have ha := Option.some.inj (hga.symm.trans hgdc1)
      have hg2 : C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some (dcs1.set! 0 dc2) := by
        simp [h2, C.Space.get, C.Space.put]
      have hb := Option.some.inj (hgb.symm.trans hg2)
      rw [ha, hb, set0_bang_m dcs1 hszdc1 dc2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hdEq : dcs1 = dcs := by
      simp only [C.Space.get] at hgdc hgdc1; rw [hd1] at hgdc1
      exact Option.some.inj (hgdc1.symm.trans hgdc)
    refine ⟨h2, ?_, hp2, decompHeaderStable_trans hp hp1 (decompHeaderStable_of_same hd1 hmr1 hcp1) hst12,
      hsr1, hco1, hby1, ?_⟩
    · unfold examine_app14
      rw [C.run_bind, hldc]; dsimp only
      simp only [had, ↓reduceIte]
      have htr1' : C.run (tracems4 dcs[0]!.err 1 JTRC_ADOBE ver fl0 fl1 (Int32.ofNat xform.toNat)) h = .ok ((), h1) := by
        rw [kerr]; exact htr1
      rw [C.run_bind, htr1']; dsimp only
      dsimp only [dc2, xform, h2] at hstDc ⊢
      rw [hdEq] at hstDc ⊢
      exact hstDc
    · intro errs errs' hg hsze hg'
      exact hnw1 errs errs' hg hsze hg'
  · have hadF : (datalen ≥ APP14_DATA_LEN &&
        data[0]! == 0x41 && data[1]! == 0x64 && data[2]! == 0x6F && data[3]! == 0x62 && data[4]! == 0x65) = false := by
      cases hc : (datalen ≥ APP14_DATA_LEN &&
        data[0]! == 0x41 && data[1]! == 0x64 && data[2]! == 0x6F && data[3]! == 0x62 && data[4]! == 0x65) <;> simp_all
    obtain ⟨h1, htr1, hp1, hd1, hmr1, hsr1, _, hcp1, _, _, _, hby1, _, hco1, hnw1⟩ :=
      tracems1_nonneg_parser hp 1 JTRC_APP14 (Int32.ofInt (Int.ofNat datalen.toNat + remaining.toInt)) (by decide)
    refine ⟨h1, ?_, hp1, decompHeaderStable_of_same hd1 hmr1 hcp1, hsr1, hco1, hby1, hnw1⟩
    unfold examine_app14
    rw [C.run_bind, hldc]; dsimp only
    simp only [hadF, Bool.false_eq_true, ↓reduceIte]
    rw [kerr]; exact htr1

theorem get_interesting_appn_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63) :
    ∃ res h',
      C.run (get_interesting_appn (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcStrict srcs0[0]! srcs'[0]!) ∧
        WarnPotOk ctx h h' (2 ^ 16)
      | _ => True := by
  obtain ⟨dcs, hgdc, hszdc, kerr, _, _, _, _, ksrc⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _, _, _, _, _, hcur0⟩ := parserEnv_get_src hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc hszsrc
  have htr0 := nibBibTrack_init ctx h srcs hgsrc
  have hbd0 : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
    nibBibTrack_bd hp hp htr0 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
  obtain ⟨res1, h1, hrun1, hp1, hd1, hmr1, _, hcp1, _, _, _, _, _, _, hpost1⟩ :=
    input2Bytes_parser hp srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer hcur0 hbd0
  have hst01 : DecompHeaderStable ctx h h1 := decompHeaderStable_of_same hd1 hmr1 hcp1
  cases res1 with
  | none =>
    refine ⟨.ok false, h1, ?_, hp1, hst01, trivial⟩
    unfold get_interesting_appn
    rw [C.run_bind, hldc]; dsimp only
    rw [ksrc, C.run_bind, hlsrc]; dsimp only
    rw [C.run_bind, hrun1]; rfl
  | some x =>
    rcases x with ⟨lenRaw, nib1, bib1⟩
    rcases hpost1 with ⟨hlen0, hlenHi, hcur1, hce1⟩
    obtain ⟨htr1, hstr1⟩ := nibBibTrack_input2Bytes_step hp hp htr0 (by omega) (by omega) hce1
    let lenInit : Int64 := Int64.ofInt (lenRaw.toInt - 2)
    have hlenInit : lenInit.toInt = lenRaw.toInt - 2 := by
      change (Int64.ofInt (lenRaw.toInt - 2)).toInt = lenRaw.toInt - 2
      rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    let numtoread : Nat :=
      if lenInit.toInt ≥ Int.ofNat APPN_DATA_LEN.toNat then APPN_DATA_LEN.toNat
      else if lenInit.toInt > 0 then lenInit.toInt.toNat
      else 0
    have hntrLe : numtoread ≤ 14 := by
      dsimp only [numtoread]
      have h14 : APPN_DATA_LEN.toNat = 14 := by decide
      have h14' : Int.ofNat 14 = (14 : Int) := rfl
      rw [h14, h14']
      split
      · omega
      · split <;> omega
    let Inv (i : Nat) (s : Array UInt8 × BPtr × UInt64 × Bool) (hCur : C.Heap) : Prop :=
      ParserEnv ctx hCur ∧
      DecompHeaderStable ctx h hCur ∧
      (!s.2.2.2 →
        CurValid hCur s.2.1 s.2.2.1 ∧
        NibBibTrack ctx h hCur s.2.1 s.2.2.1 (-8) (2 + (i : Int)) ∧
        (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          isConstEofPtr s.2.1 = true ∨ s.2.2.1.toNat < srcs0[0]!.bytesInBuffer.toNat))
    let sInit : Array UInt8 × BPtr × UInt64 × Bool := (Array.replicate APPN_DATA_LEN.toNat 0, nib1, bib1, false)
    have hInv0 : Inv 0 sInit h1 :=
      ⟨hp1, hst01, fun _ => ⟨hcur1, nibBibTrack_mono htr1 (by omega) (by omega), hstr1⟩⟩
    obtain ⟨sFin, h2, hfor, hInvFin⟩ := forIn_range_inv Inv
      (fun (i : Nat) (s : Array UInt8 × BPtr × UInt64 × Bool) => do
        if !s.2.2.2 then
          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.2.1 s.2.2.1) with
          | none => return .yield (s.1, s.2.1, s.2.2.1, true)
          | some (byteVal, n', bi') =>
            return .yield (s.1.set! i (UInt8.ofNat byteVal.toInt.toNat), n', bi', s.2.2.2)
        else
          return .yield (s.1, s.2.1, s.2.2.1, s.2.2.2))
      numtoread
      (fun i hi s hCur ⟨hpC, hstC, hact⟩ => by
        by_cases hns : (!s.2.2.2) = true
        · have hsF : s.2.2.2 = false := by cases hc : s.2.2.2 <;> simp_all
          obtain ⟨hcurS, htrS, _⟩ := hact (by simp [hsF])
          have hbdS : s.2.2.1 = 0 → ∀ errs, C.Space.get hCur ctx.rerr = some errs → 0 < errs.size →
              errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
            nibBibTrack_bd hp hpC htrS (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
              have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
          obtain ⟨resB, hB, hrunB, hpB, hdB, hmrB, _, hcpB, _, _, _, _, _, _, hpostB⟩ :=
            inputByte_parser hpC s.2.1 s.2.2.1 hcurS hbdS
          have hstCB := decompHeaderStable_trans hp hpC hstC (decompHeaderStable_of_same hdB hmrB hcpB)
          cases resB with
          | none =>
            refine ⟨.yield (s.1, s.2.1, s.2.2.1, true), hB, ?_, hpB, hstCB, fun hno => by simp at hno⟩
            simp only [hns, ↓reduceIte, C.run_bind, hrunB]; rfl
          | some y =>
            rcases y with ⟨bv, n', bi'⟩
            rcases hpostB with ⟨_, _, hcurB, hceB⟩
            obtain ⟨htrB, hstrB⟩ := nibBibTrack_inputByte_step hp hpC htrS (by omega) (by omega) hceB
            refine ⟨.yield (s.1.set! i (UInt8.ofNat bv.toInt.toNat), n', bi', s.2.2.2), hB, ?_, hpB, hstCB, fun _ => ?_⟩
            · simp only [hns, ↓reduceIte, C.run_bind, hrunB]; rfl
            · exact ⟨hcurB, nibBibTrack_mono htrB (by omega) (by omega), hstrB⟩
        · have hsT : (!s.2.2.2) = false := by cases hc : (!s.2.2.2) <;> simp_all
          refine ⟨.yield (s.1, s.2.1, s.2.2.1, s.2.2.2), hCur, ?_, hpC, hstC, fun hno => by simp [hsT] at hno⟩
          simp only [hsT, Bool.false_eq_true, ↓reduceIte]; rfl)
      hInv0
    rcases hInvFin with ⟨hp2, hst02, hact2⟩
    dsimp only [numtoread, lenInit, sInit] at hfor
    by_cases hsusp : sFin.2.2.2 = true
    · refine ⟨.ok false, h2, ?_, hp2, hst02, trivial⟩
      unfold get_interesting_appn
      rw [C.run_bind, hldc]; dsimp only
      rw [ksrc, C.run_bind, hlsrc]; dsimp only
      rw [C.run_bind, hrun1]; dsimp only
      rw [C.run_bind]; erw [hfor]; dsimp only
      simp only [hsusp, ↓reduceIte]; rfl
    · have hsuspF : sFin.2.2.2 = false := by cases hc : sFin.2.2.2 <;> simp_all
      obtain ⟨hcur2, htr2, hstr2⟩ := hact2 (by simp [hsuspF])
      have hnumNat : Int.ofNat numtoread = (numtoread : Int) := rfl
      let lenRem : Int64 := Int64.ofInt (lenInit.toInt - Int.ofNat numtoread)
      have hlenRemTo : lenRem.toInt = lenInit.toInt - (numtoread : Int) := by
        change (Int64.ofInt (lenInit.toInt - Int.ofNat numtoread)).toInt = lenInit.toInt - (numtoread : Int)
        rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, hnumNat, hlenInit]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      have hlenRemLe : lenRem.toInt ≤ 65535 := by rw [hlenRemTo, hlenInit]; omega
      obtain ⟨dcs2, hgdc2, hszdc2, kerr2, _⟩ := parserEnv_get_dc hp2
      have hldc2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc2 hszdc2
      have hfinSyncSkip : ∀ h3 (hp3 : ParserEnv ctx h3) (hst03 : DecompHeaderStable ctx h h3)
          (hby23 : h3.bytes = h2.bytes) (hco23 : h3.consts = h2.consts)
          (htr3 : NibBibTrack ctx h h3 sFin.2.1 sFin.2.2.1 (-7) 17),
          ∃ h',
            C.run (do
              inputSync (.ref (.decomp ctx.bdc) 0) sFin.2.1 sFin.2.2.1
              if lenRem > 0 then skipInputDataDispatch (.ref (.decomp ctx.bdc) 0) lenRem
              return (JpegRes.ok true)) h3 = Except.ok (JpegRes.ok true, h') ∧
            ParserEnv ctx h' ∧
            DecompHeaderStable ctx h h' ∧
            (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
              C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
              SrcStrict srcs0[0]! srcs'[0]!) ∧
            WarnPotOk ctx h h' (2 ^ 16) := by
        intro h3 hp3 hst03 hby23 hco23 htr3
        have hcur3 : CurValid h3 sFin.2.1 sFin.2.2.1 := curValid_bytes_irrel hby23 hco23 hcur2
        obtain ⟨h4, hsync4, hp4, hd4, hmr4, he4, _, hcp4, _, _, _, _, _, _, hsrc4⟩ :=
          inputSync_parser hp3 sFin.2.1 sFin.2.2.1 hcur3
        have hst04 := decompHeaderStable_trans hp hp3 hst03 (decompHeaderStable_of_same hd4 hmr4 hcp4)
        obtain ⟨hw04, _⟩ := nibBibTrack_to_warnPotOk_src hp hp3 htr3 (by omega) he4 hsrc4
        have hstr04 := nibBibTrack_to_srcStrict hp hp3 htr3 hstr2 hsrc4
        by_cases hlenPos : lenRem > 0
        · have hbd4 : ∀ errs, C.Space.get h4 ctx.rerr = some errs → 0 < errs.size →
              errs[0]!.numWarnings.toInt + 2 ^ 16 < 2 ^ 63 := by
            intro errs hg4 hsz4
            exact warnPotOk_bd hp hp4 hw04 (fun e0 s0 he0 hse0 hs0 hss0 => by
              have := hhead e0 s0 he0 hse0 hs0 hss0; omega) errs hg4 hsz4
          obtain ⟨h5, hsk5, hp5, hd5, hmr5, _, hcp5, _, _, _, _, _, _, hnw5, hsm5⟩ :=
            skipInputDataDispatch_parser hp4 lenRem hlenRemLe hbd4
          have hst05 := decompHeaderStable_trans hp hp4 hst04 (decompHeaderStable_of_same hd5 hmr5 hcp5)
          have hm04 : ∀ s0 s4, C.Space.get h ctx.rs = some s0 → 0 < s0.size →
              C.Space.get h4 ctx.rs = some s4 → 0 < s4.size → SrcMono s0[0]! s4[0]! :=
            fun s0 s4 h0 hsz0 h4s hsz4 => srcMono_of_strict (hstr04 s0 s4 h0 hsz0 h4s hsz4)
          have hm45 : ∀ s4 s5, C.Space.get h4 ctx.rs = some s4 → 0 < s4.size →
              C.Space.get h5 ctx.rs = some s5 → 0 < s5.size → SrcMono s4[0]! s5[0]! := by
            intro s4 s5 h4s hsz4 h5s hsz5
            obtain ⟨ht, hf⟩ := hsm5 s4 s5 h4s hsz4 h5s hsz5
            refine ⟨ht, fun hf4 => ?_⟩
            by_cases hc5 : isConstEofPtr s5[0]!.nextInputByte = false
            · exact Or.inr (hf hc5).2.1
            · left; cases hc : isConstEofPtr s5[0]!.nextInputByte <;> simp_all
          have hw45 : WarnPotOk ctx h4 h5 (1 + 65535 / 2) := by
            intro e4 e5 s4 s5 hg4 hsz4 hg5 hsz5 hs4 hszs4 hs5 hszs5
            obtain ⟨_, hf⟩ := hsm5 s4 s5 hs4 hszs4 hs5 hszs5
            refine ⟨fun hc5 => ?_, fun _ => ?_⟩
            · obtain ⟨hc4, hble, heeq⟩ := hf hc5
              have hweq := heeq e4 e5 hg4 hsz4 hg5 hsz5
              simp only [warnPotVal, hc5, hc4, Bool.false_eq_true, ↓reduceIte]
              omega
            · obtain ⟨_, hle⟩ := hnw5 e4 e5 hg4 hsz4 hg5
              have : (0 : Int) ≤ 4 * (s4[0]!.bytesInBuffer.toNat : Int) := by omega
              dsimp only [warnPotVal]; split <;> omega
          have hw05 := warnPotOk_trans hm04 hm45 hw04 hw45 (by omega) hp4
          refine ⟨h5, ?_, hp5, hst05, fun s0 s5 h0 hsz0 h5s hsz5 => ?_, ?_⟩
          · rw [C.run_bind, hsync4]; dsimp only
            dsimp only [lenRem, lenInit, numtoread] at hlenPos hsk5 ⊢
            simp only [eq_true hlenPos, ↓reduceIte, C.run_bind, hsk5]; rfl
          · obtain ⟨s4, hs4, hsz4, _⟩ := parserEnv_get_src hp4
            exact srcStrict_mono_trans (hstr04 s0 s4 h0 hsz0 hs4 hsz4) (hm45 s4 s5 hs4 hsz4 h5s hsz5)
          · intro e0 e5 s0 s5 hg0 hsz0 hg5 hsz5 hs0 hszs0 hs5 hszs5
            obtain ⟨wf, wt⟩ := hw05 e0 e5 s0 s5 hg0 hsz0 hg5 hsz5 hs0 hszs0 hs5 hszs5
            exact ⟨wf, fun ht => by have := wt ht; omega⟩
        · refine ⟨h4, ?_, hp4, hst04, hstr04, ?_⟩
          · rw [C.run_bind, hsync4]; dsimp only
            dsimp only [lenRem, lenInit, numtoread] at hlenPos ⊢
            simp only [eq_false hlenPos, ↓reduceIte]; rfl
          · intro e0 e4 s0 s4 hg0 hsz0 hg4 hsz4 hs0 hszs0 hs4 hszs4
            obtain ⟨wf, wt⟩ := hw04 e0 e4 s0 s4 hg0 hsz0 hg4 hsz4 hs0 hszs0 hs4 hszs4
            exact ⟨wf, fun ht => by have := wt ht; omega⟩
      by_cases hm0 : (dcs2[0]!.unreadMarker == M_APP0) = true
      · have hbdEx : ∀ errs, C.Space.get h2 ctx.rerr = some errs → 0 < errs.size →
            errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 :=
          nibBibTrack_bd hp hp2 htr2 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
            have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
        obtain ⟨h3, hex3, hp3, hst23, _, hco3, hby3, hnw3⟩ :=
          examine_app0_parser hp2 sFin.1 (UInt32.ofNat numtoread) lenRem hbdEx
        have hst03 := decompHeaderStable_trans hp hp2 hst02 hst23
        have h17 : (2 + (numtoread : Int) + 1 : Int) ≤ 17 := by omega
        have htr3 : NibBibTrack ctx h h3 sFin.2.1 sFin.2.2.1 (-7) 17 :=
          nibBibTrack_mono (nibBibTrack_err_warn1 hp2 htr2 hnw3) (by omega) h17
        obtain ⟨h', hss, hp', hst', hstr', hw'⟩ := hfinSyncSkip h3 hp3 hst03 hby3 hco3 htr3
        refine ⟨.ok true, h', ?_, hp', hst', ⟨hstr', hw'⟩⟩
        unfold get_interesting_appn
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind]; erw [hfor]; dsimp only
        simp only [hsuspF, Bool.false_eq_true, ↓reduceIte]
        rw [C.run_bind, hldc2]; dsimp only
        dsimp only [lenRem, lenInit, numtoread] at hex3 hss
        simp only [hm0, ↓reduceIte]
        rw [C.run_bind, hex3]; dsimp only; exact hss
      · have hm0F : (dcs2[0]!.unreadMarker == M_APP0) = false := by
          cases hc : (dcs2[0]!.unreadMarker == M_APP0) <;> simp_all
        by_cases hm14 : (dcs2[0]!.unreadMarker == M_APP14) = true
        · obtain ⟨h3, hex3, hp3, hst23, _, hco3, hby3, hnw3⟩ :=
            examine_app14_parser hp2 sFin.1 (UInt32.ofNat numtoread) lenRem
          have hst03 := decompHeaderStable_trans hp hp2 hst02 hst23
          have h17 : (2 + (numtoread : Int) : Int) ≤ 17 := by omega
          have htr3 : NibBibTrack ctx h h3 sFin.2.1 sFin.2.2.1 (-7) 17 :=
            nibBibTrack_mono (nibBibTrack_err_nw_same hp2 htr2 hnw3) (by omega) h17
          obtain ⟨h', hss, hp', hst', hstr', hw'⟩ := hfinSyncSkip h3 hp3 hst03 hby3 hco3 htr3
          refine ⟨.ok true, h', ?_, hp', hst', ⟨hstr', hw'⟩⟩
          unfold get_interesting_appn
          rw [C.run_bind, hldc]; dsimp only
          rw [ksrc, C.run_bind, hlsrc]; dsimp only
          rw [C.run_bind, hrun1]; dsimp only
          rw [C.run_bind]; erw [hfor]; dsimp only
          simp only [hsuspF, Bool.false_eq_true, ↓reduceIte]
          rw [C.run_bind, hldc2]; dsimp only
          dsimp only [lenRem, lenInit, numtoread] at hex3 hss
          simp only [hm0F, Bool.false_eq_true, ↓reduceIte, hm14]
          rw [C.run_bind, hex3]; dsimp only; exact hss
        · have hm14F : (dcs2[0]!.unreadMarker == M_APP14) = false := by
            cases hc : (dcs2[0]!.unreadMarker == M_APP14) <;> simp_all
          obtain ⟨h_err, herr_run, hp_err, hstErr⟩ := errexit1_stable_parser hp2 JERR_UNKNOWN_MARKER dcs2[0]!.unreadMarker
          have herr_run' : C.run (errexit1 dcs2[0]!.err JERR_UNKNOWN_MARKER dcs2[0]!.unreadMarker) h2 =
              .ok (.errExit JERR_UNKNOWN_MARKER, h_err) := by
            rw [kerr2]; exact herr_run
          refine ⟨.errExit JERR_UNKNOWN_MARKER, h_err, ?_, hp_err,
            decompHeaderStable_trans hp hp2 hst02 hstErr, trivial⟩
          unfold get_interesting_appn
          rw [C.run_bind, hldc]; dsimp only
          rw [ksrc, C.run_bind, hlsrc]; dsimp only
          rw [C.run_bind, hrun1]; dsimp only
          rw [C.run_bind]; erw [hfor]; dsimp only
          simp only [hsuspF, Bool.false_eq_true, ↓reduceIte]
          rw [C.run_bind, hldc2]; dsimp only
          simp only [hm0F, hm14F, Bool.false_eq_true, ↓reduceIte, C.run_bind, herr_run']; rfl

/-! ## `skip_variable` -/

theorem skip_variable_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63) :
    ∃ res h',
      C.run (skip_variable (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcStrict srcs0[0]! srcs'[0]!) ∧
        WarnPotOk ctx h h' (2 ^ 16)
      | _ => True := by
  obtain ⟨dcs, hgdc, hszdc, kerr, _, _, _, _, ksrc⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _, _, _, _, _, hcur0⟩ := parserEnv_get_src hp
  have hldc := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc hszdc
  have hlsrc := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc hszsrc
  have htr0 := nibBibTrack_init ctx h srcs hgsrc
  have hbd0 : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
    nibBibTrack_bd hp hp htr0 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
  obtain ⟨res1, h1, hrun1, hp1, hd1, hmr1, _, hcp1, _, _, _, _, _, _, hpost1⟩ :=
    input2Bytes_parser hp srcs[0]!.nextInputByte srcs[0]!.bytesInBuffer hcur0 hbd0
  have hst01 : DecompHeaderStable ctx h h1 := decompHeaderStable_of_same hd1 hmr1 hcp1
  cases res1 with
  | none =>
    refine ⟨.ok false, h1, ?_, hp1, hst01, trivial⟩
    unfold skip_variable
    rw [C.run_bind, hldc]; dsimp only
    rw [ksrc, C.run_bind, hlsrc]; dsimp only
    rw [C.run_bind, hrun1]; rfl
  | some x =>
    rcases x with ⟨lenRaw, nib1, bib1⟩
    rcases hpost1 with ⟨hlen0, hlenHi, hcur1, hce1⟩
    obtain ⟨htr1, hstr1⟩ := nibBibTrack_input2Bytes_step hp hp htr0 (by omega) (by omega) hce1
    let length : Int64 := Int64.ofInt (lenRaw.toInt - 2)
    have hlenTo : length.toInt = lenRaw.toInt - 2 := by
      change (Int64.ofInt (lenRaw.toInt - 2)).toInt = lenRaw.toInt - 2
      rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hlenLe : length.toInt ≤ 65535 := by rw [hlenTo]; omega
    obtain ⟨dcs1, hgdc1, _, kerr1, _⟩ := parserEnv_get_dc hp1
    obtain ⟨h2, htr2_run, hp2, hd2, hmr2, _, _, hcp2, _, _, _, hby2, _, hco2, hnw2⟩ :=
      tracems2_nonneg_parser hp1 1 JTRC_MISC_MARKER dcs[0]!.unreadMarker (Int32.ofInt length.toInt) (by decide)
    have htr2_run' : C.run (tracems2 dcs[0]!.err 1 JTRC_MISC_MARKER dcs[0]!.unreadMarker (Int32.ofInt length.toInt)) h1 =
        .ok ((), h2) := by
      rw [kerr]; exact htr2_run
    have hst02 := decompHeaderStable_trans hp hp1 hst01 (decompHeaderStable_of_same hd2 hmr2 hcp2)
    have htr2 := nibBibTrack_err_nw_same hp1 htr1 hnw2
    have hcur2 : CurValid h2 nib1 bib1 := curValid_bytes_irrel hby2 hco2 hcur1
    obtain ⟨h3, hsync3, hp3, hd3, hmr3, he3, _, hcp3, _, _, _, _, _, _, hsrc3⟩ :=
      inputSync_parser hp2 nib1 bib1 hcur2
    have hst03 := decompHeaderStable_trans hp hp2 hst02 (decompHeaderStable_of_same hd3 hmr3 hcp3)
    obtain ⟨hw03, _⟩ := nibBibTrack_to_warnPotOk_src hp hp2 htr2 (by omega) he3 hsrc3
    have hstr03 := nibBibTrack_to_srcStrict hp hp2 htr2 hstr1 hsrc3
    by_cases hlenPos : length > 0
    · have hbd3 : ∀ errs, C.Space.get h3 ctx.rerr = some errs → 0 < errs.size →
          errs[0]!.numWarnings.toInt + 2 ^ 16 < 2 ^ 63 := by
        intro errs hg3 hsz3
        exact warnPotOk_bd hp hp3 hw03 (fun e0 s0 he0 hse0 hs0 hss0 => by
          have := hhead e0 s0 he0 hse0 hs0 hss0; omega) errs hg3 hsz3
      obtain ⟨h4, hsk4, hp4, hd4, hmr4, _, hcp4, _, _, _, _, _, _, hnw4, hsm4⟩ :=
        skipInputDataDispatch_parser hp3 length hlenLe hbd3
      have hst04 := decompHeaderStable_trans hp hp3 hst03 (decompHeaderStable_of_same hd4 hmr4 hcp4)
      have hm03 : ∀ s0 s3, C.Space.get h ctx.rs = some s0 → 0 < s0.size →
          C.Space.get h3 ctx.rs = some s3 → 0 < s3.size → SrcMono s0[0]! s3[0]! :=
        fun s0 s3 h0 hsz0 h3s hsz3 => srcMono_of_strict (hstr03 s0 s3 h0 hsz0 h3s hsz3)
      have hm34 : ∀ s3 s4, C.Space.get h3 ctx.rs = some s3 → 0 < s3.size →
          C.Space.get h4 ctx.rs = some s4 → 0 < s4.size → SrcMono s3[0]! s4[0]! := by
        intro s3 s4 h3s hsz3 h4s hsz4
        obtain ⟨ht, hf⟩ := hsm4 s3 s4 h3s hsz3 h4s hsz4
        refine ⟨ht, fun hf3 => ?_⟩
        by_cases hc4 : isConstEofPtr s4[0]!.nextInputByte = false
        · exact Or.inr (hf hc4).2.1
        · left; cases hc : isConstEofPtr s4[0]!.nextInputByte <;> simp_all
      have hw34 : WarnPotOk ctx h3 h4 (1 + 65535 / 2) := by
        intro e3 e4 s3 s4 hg3 hsz3 hg4 hsz4 hs3 hszs3 hs4 hszs4
        obtain ⟨_, hf⟩ := hsm4 s3 s4 hs3 hszs3 hs4 hszs4
        refine ⟨fun hc4 => ?_, fun _ => ?_⟩
        · obtain ⟨hc3, hble, heeq⟩ := hf hc4
          have hweq := heeq e3 e4 hg3 hsz3 hg4 hsz4
          simp only [warnPotVal, hc4, hc3, Bool.false_eq_true, ↓reduceIte]
          omega
        · obtain ⟨_, hle⟩ := hnw4 e3 e4 hg3 hsz3 hg4
          have : (0 : Int) ≤ 4 * (s3[0]!.bytesInBuffer.toNat : Int) := by omega
          dsimp only [warnPotVal]; split <;> omega
      have hw04 := warnPotOk_trans hm03 hm34 hw03 hw34 (by omega) hp3
      refine ⟨.ok true, h4, ?_, hp4, hst04, fun s0 s4 h0 hsz0 h4s hsz4 => ?_, ?_⟩
      · unfold skip_variable
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind, htr2_run']; dsimp only
        rw [C.run_bind, hsync3]; dsimp only
        dsimp only [length] at hlenPos hsk4 ⊢
        simp only [eq_true hlenPos, ↓reduceIte, C.run_bind, hsk4]; rfl
      · obtain ⟨s3, hs3, hsz3, _⟩ := parserEnv_get_src hp3
        exact srcStrict_mono_trans (hstr03 s0 s3 h0 hsz0 hs3 hsz3) (hm34 s3 s4 hs3 hsz3 h4s hsz4)
      · intro e0 e4 s0 s4 hg0 hsz0 hg4 hsz4 hs0 hszs0 hs4 hszs4
        obtain ⟨wf, wt⟩ := hw04 e0 e4 s0 s4 hg0 hsz0 hg4 hsz4 hs0 hszs0 hs4 hszs4
        exact ⟨wf, fun ht => by have := wt ht; omega⟩
    · refine ⟨.ok true, h3, ?_, hp3, hst03, hstr03, ?_⟩
      · unfold skip_variable
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind, htr2_run']; dsimp only
        rw [C.run_bind, hsync3]; dsimp only
        dsimp only [length] at hlenPos
        simp only [eq_false hlenPos, ↓reduceIte]; rfl
      · intro e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
        obtain ⟨wf, wt⟩ := hw03 e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
        exact ⟨wf, fun ht => by have := wt ht; omega⟩

end MozjpegF.Proof.JdmarkerMarkers



