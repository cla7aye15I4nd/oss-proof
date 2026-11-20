import MozjpegF.Proof.«jdmarker.c.markers»

/-!
# Remaining marker parsers and `read_markers` proofs (`jdmarker.c`, `MozjpegF`)

Proves safety and state/source/warning preservation for `makeByteAvail`, `get_dht`, `get_dqt`,
`get_sof`, `get_sos`, `save_marker`, `callMarkerParser`, and `read_markers`.
-/

set_option autoImplicit false

namespace MozjpegF.Proof.JdmarkerReadMarkers
open C MozjpegF.Spec Mozjpeg.Jerror Mozjpeg.JerrorH Mozjpeg.Jcomapi Mozjpeg.Jmemnobs
open Mozjpeg.Jmemmgr Mozjpeg.Jdatasrc Mozjpeg.Jdmarker Mozjpeg.JpeglibH Mozjpeg.MoreCfg Mozjpeg.Jutils
open MozjpegF.Proof.JdmarkerHelpers MozjpegF.Proof.JmemmgrHelpers MozjpegF.Proof.JdmarkerRead
open MozjpegF.Proof.JdmarkerParsers MozjpegF.Proof.JdmarkerMarkers

/-! ## `makeByteAvail` -/

theorem makeByteAvail_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (nib : C.BPtr) (bib : UInt64)
    (hcur : CurValid h nib bib)
    (hbd : bib = 0 → ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63) :
    ∃ res h',
      C.run (makeByteAvail (.ref (.decomp ctx.bdc) 0) nib bib) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.masters = h.masters ∧
      h'.comps = h.comps ∧ h'.quants = h.quants ∧ h'.huffs = h.huffs ∧
      h'.savedMarkers = h.savedMarkers ∧ h'.bytes = h.bytes ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      match res with
      | none => h' = h
      | some (nib1, bib1) =>
        0 < bib1.toNat ∧
        CurValid h' nib1 bib1 ∧
        (if isConstEofPtr nib1 = false then
          nib1 = nib ∧ bib1 = bib ∧ bib ≠ 0 ∧ h' = h
         else
          ∀ errs errs', C.Space.get h ctx.rerr = some errs → 0 < errs.size →
            C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size ∧
            errs'[0]!.numWarnings.toInt ≤ errs[0]!.numWarnings.toInt + (if bib == 0 then 1 else 0)) := by
  have hp0 := hp
  obtain ⟨dcs, hgdc, hszdc, _, _, _, _, _, hsrcp⟩ := parserEnv_get_dc hp
  obtain ⟨srcs, hgsrc, hszsrc, _, _, _, _, hfill, _⟩ := parserEnv_get_src hp
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
      have hmba : C.run (makeByteAvail (.ref (.decomp ctx.bdc) 0) nib 0) h =
          .ok (some (.ref .const_eof 0, 2), h2) := by
        unfold makeByteAvail
        simp only [hn0, Bool.false_eq_true, ↓reduceIte, C.run_bind, hldc, hsrcp, hlsrc, hfne, hf2]
        have ht0 : (TRUE == 0) = false := by decide
        have hb2 : ((2 : UInt64) == 0) = false := by decide
        simp only [ht0, Bool.false_eq_true, ↓reduceIte, C.run_bind, hl2, hbib2, hb2]
        rw [hnib2]; rfl
      have hcv2 : CurValid h2 (.ref .const_eof 0) 2 := by
        refine ⟨by decide, Or.inr ⟨.const_eof, 0, #[0xFF, 0xD9, 0, 0], rfl, rfl, by decide⟩, ?_⟩
        intro o ho; cases ho; decide
      refine ⟨some (.ref .const_eof 0, 2), h2, hmba, hp2,
        hd2, hmr2, hma2, hcp2, hq2, hhu2, hsm2, hby2, hme2, hco2, by decide, hcv2, ?_⟩
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
      exact ⟨none, h, hmba, hp0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hne : (bib != 0) = true := by simp [bne, hbibZ]
    have hpos : 0 < bib.toNat := by
      by_cases hz : bib.toNat = 0
      · exact False.elim (hbibZ (by rcases bib with ⟨⟨bval⟩⟩; simp at hz; subst hz; rfl))
      · omega
    have hmba : C.run (makeByteAvail (.ref (.decomp ctx.bdc) 0) nib bib) h = .ok (some (nib, bib), h) := by
      unfold makeByteAvail; simp [hne, C.run]
    refine ⟨some (nib, bib), h, hmba, hp0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hpos, ⟨hbibLt, hbibLive, hce⟩, ?_⟩
    by_cases hc : isConstEofPtr nib = false
    · simp [hc]; exact hbibZ
    · have hct : isConstEofPtr nib = true := by cases hxx : isConstEofPtr nib <;> simp_all
      simp only [hct, Bool.true_eq_false, ↓reduceIte]
      intro errs1 errs2 hg1 hsz1 hg2
      rw [Option.some.inj (hg2.symm.trans hg1)]
      exact ⟨hsz1, by omega⟩

/-! ## Table-pointer `ParserEnv` helpers -/

private theorem arr_set_bang_self {α : Type} [Inhabited α] (a : Array α) {i : Nat} (hi : i < a.size) (v : α) :
    (a.set! i v)[i]! = v := by
  simp only [Array.set!, Array.setIfInBounds, hi, ↓reduceDIte]
  rw [getElem!_pos _ i (by simp [hi])]
  exact Array.getElem_set_self hi

private theorem arr_set_bang_ne {α : Type} [Inhabited α] (a : Array α) {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (hne : i ≠ j) (v : α) :
    (a.set! j v)[i]! = a[i]! := by
  simp only [Array.set!, Array.setIfInBounds, hj, ↓reduceDIte]
  rw [getElem!_pos _ i (by simp [hi]), getElem!_pos _ i hi]
  exact Array.getElem_set_ne hj hi (fun h => hne h.symm)

theorem parserEnv_get_huff_dc {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) {idx : Nat} (hi : idx < 4) :
    ∃ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧
      dcs[0]!.dcHuffTblPtrs.size = 4 ∧
      (dcs[0]!.dcHuffTblPtrs[idx]! = .null ∨
        ∃ rh off hs, dcs[0]!.dcHuffTblPtrs[idx]! = .ref rh off ∧ C.Space.get h rh = some hs ∧ off < hs.size) := by
  obtain ⟨_, _, dcs, dc, _, _, _, _, _, _, hgdc, hszdc, hdc,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdhSz, hdh, _⟩ := hp
  refine ⟨dcs, hgdc, hszdc, hdc ▸ hdhSz, hdc ▸ hdh idx hi⟩

theorem parserEnv_get_huff_ac {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) {idx : Nat} (hi : idx < 4) :
    ∃ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧
      dcs[0]!.acHuffTblPtrs.size = 4 ∧
      (dcs[0]!.acHuffTblPtrs[idx]! = .null ∨
        ∃ rh off hs, dcs[0]!.acHuffTblPtrs[idx]! = .ref rh off ∧ C.Space.get h rh = some hs ∧ off < hs.size) := by
  obtain ⟨_, _, dcs, dc, _, _, _, _, _, _, hgdc, hszdc, hdc,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hahSz, hah, _⟩ := hp
  refine ⟨dcs, hgdc, hszdc, hdc ▸ hahSz, hdc ▸ hah idx hi⟩

theorem parserEnv_get_quant_ptr {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) {idx : Nat} (hi : idx < 4) :
    ∃ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧
      dcs[0]!.quantTblPtrs.size = 4 ∧
      (dcs[0]!.quantTblPtrs[idx]! = .null ∨
        ∃ rq off qs, dcs[0]!.quantTblPtrs[idx]! = .ref rq off ∧ C.Space.get h rq = some qs ∧ off < qs.size) := by
  obtain ⟨_, _, dcs, dc, _, _, _, _, _, _, hgdc, hszdc, hdc,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, hqtSz, hqt, _⟩ := hp
  refine ⟨dcs, hgdc, hszdc, hdc ▸ hqtSz, hdc ▸ hqt idx hi⟩

theorem parserEnv_put_dc_huffTbl {ctx : IoCtx} {h : C.Heap}
    {dcs : Array C.JpegDecompressStruct}
    (hp : ParserEnv ctx h) (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (isAc : Bool) (idxNat : Nat) (hidx : idxNat < 4) (p : C.HuffPtr)
    {rh : C.HuffRef} {off : Nat} {hs : Array C.JHuffTbl}
    (hpEq : p = .ref rh off) (hgH : C.Space.get h rh = some hs) (hoffH : off < hs.size) :
    let dc' := if isAc then { dcs[0]! with acHuffTblPtrs := dcs[0]!.acHuffTblPtrs.set! idxNat p }
      else { dcs[0]! with dcHuffTblPtrs := dcs[0]!.dcHuffTblPtrs.set! idxNat p }
    ParserEnv ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) := by
  have hp0 := hp
  obtain ⟨_, _, dcs0, dc0, _, _, _, _, mrks0, _,
    hgdc0, _, hdc0, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, hgmrk0, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, _, hsaw0, _, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp0
  have hdEq : dcs = dcs0 := Option.some.inj (hg.symm.trans hgdc0)
  subst hdEq; subst hdc0
  intro dc'
  refine parserEnv_put_dc hp hg hsz
    (by dsimp [dc']; split <;> rfl) (by dsimp [dc']; split <;> rfl)
    (by dsimp [dc']; split <;> rfl) (by dsimp [dc']; split <;> rfl)
    (by dsimp [dc']; split <;> rfl) (by dsimp [dc']; split <;> rfl)
    (Or.inl (by dsimp [dc']; split <;> rfl))
    (Or.inl ⟨by dsimp [dc']; split <;> rfl, by dsimp [dc']; split <;> rfl⟩)
    ⟨by dsimp [dc']; split <;> exact hqtSz, fun i hi => by dsimp [dc']; split <;> exact hqt i hi⟩
    ⟨by dsimp [dc']; cases isAc with | true => exact hdhSz | false => simp [hdhSz],
     fun i hi => by
       cases isAc with
       | true => exact hdh i hi
       | false =>
         dsimp only [dc']; simp only [Bool.false_eq_true, ↓reduceIte]
         by_cases hij : i = idxNat
         · subst hij; right
           rw [arr_set_bang_self _ (by rw [hdhSz]; exact hidx)]
           exact ⟨rh, off, hs, hpEq, hgH, hoffH⟩
         · rw [arr_set_bang_ne _ (by rw [hdhSz]; exact hi) (by rw [hdhSz]; exact hidx) hij]
           exact hdh i hi⟩
    ⟨by dsimp [dc']; cases isAc with | false => exact hahSz | true => simp [hahSz],
     fun i hi => by
       cases isAc with
       | false => exact hah i hi
       | true =>
         dsimp only [dc']; simp only [↓reduceIte]
         by_cases hij : i = idxNat
         · subst hij; right
           rw [arr_set_bang_self _ (by rw [hahSz]; exact hidx)]
           exact ⟨rh, off, hs, hpEq, hgH, hoffH⟩
         · rw [arr_set_bang_ne _ (by rw [hahSz]; exact hi) (by rw [hahSz]; exact hidx) hij]
           exact hah i hi⟩
    (by dsimp [dc']; split <;> exact hccSz)
    (by dsimp [dc']; split <;> exact hisn0)
    (fun mrks' hgmrk' _ hsawNe => by
      have hmEq := Option.some.inj (hgmrk'.symm.trans hgmrk0); subst hmEq
      have := hsaw0 hsawNe
      dsimp [dc']; split <;> exact this)

theorem parserEnv_put_dc_quantTbl {ctx : IoCtx} {h : C.Heap}
    {dcs : Array C.JpegDecompressStruct}
    (hp : ParserEnv ctx h) (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (idxNat : Nat) (hidx : idxNat < 4) (p : C.QuantPtr)
    {rq : C.QuantRef} {off : Nat} {qs : Array C.JQuantTbl}
    (hpEq : p = .ref rq off) (hgQ : C.Space.get h rq = some qs) (hoffQ : off < qs.size) :
    let dc' := { dcs[0]! with quantTblPtrs := dcs[0]!.quantTblPtrs.set! idxNat p }
    ParserEnv ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) := by
  have hp0 := hp
  obtain ⟨_, _, dcs0, dc0, _, _, _, _, mrks0, _,
    hgdc0, _, hdc0, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, hgmrk0, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, _, hsaw0, _, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp0
  have hdEq : dcs = dcs0 := Option.some.inj (hg.symm.trans hgdc0)
  subst hdEq; subst hdc0
  intro dc'
  refine parserEnv_put_dc hp hg hsz rfl rfl rfl rfl rfl rfl (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩)
    ⟨by dsimp [dc']; simp [hqtSz], fun i hi => by
      dsimp only [dc']
      by_cases hij : i = idxNat
      · subst hij; right
        rw [arr_set_bang_self _ (by rw [hqtSz]; exact hidx)]
        exact ⟨rq, off, qs, hpEq, hgQ, hoffQ⟩
      · rw [arr_set_bang_ne _ (by rw [hqtSz]; exact hi) (by rw [hqtSz]; exact hidx) hij]
        exact hqt i hi⟩
    ⟨hdhSz, hdh⟩ ⟨hahSz, hah⟩ hccSz hisn0
    (fun mrks' hgmrk' _ hsawNe => by
      have hmEq := Option.some.inj (hgmrk'.symm.trans hgmrk0); subst hmEq
      exact hsaw0 hsawNe)

/-! ## `get_dht` -/

theorem get_dht_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63) :
    ∃ res h',
      C.run (get_dht (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
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
    unfold get_dht
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
    let Inv (k : Nat) (hCur : C.Heap) (s : DhtLoopState) : Prop :=
      ParserEnv ctx hCur ∧
      DecompHeaderStable ctx h hCur ∧
      (s.done = true → s.ret ≠ .ok true) ∧
      (!s.done →
        -2 ≤ s.length.toInt ∧ s.length.toInt ≤ 65533 ∧
        k = (if s.length.toInt ≤ 16 then 0 else s.length.toInt.toNat + 1) ∧
        CurValid hCur s.nib s.bib ∧
        NibBibTrack ctx h hCur s.nib s.bib (-8) (if s.length.toInt < 0 then 2 else 2 + (65533 - s.length.toInt)) ∧
        (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          isConstEofPtr s.nib = true ∨ s.bib.toNat < srcs0[0]!.bytesInBuffer.toNat))
    let Post (hCur : C.Heap) (s : DhtLoopState) : Prop :=
      ParserEnv ctx hCur ∧
      DecompHeaderStable ctx h hCur ∧
      (s.done = true → s.ret ≠ .ok true) ∧
      (!s.done →
        s.length.toInt ≤ 16 ∧
        CurValid hCur s.nib s.bib ∧
        NibBibTrack ctx h hCur s.nib s.bib (-8) 65535 ∧
        (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          isConstEofPtr s.nib = true ∨ s.bib.toNat < srcs0[0]!.bytesInBuffer.toNat))
    let s0 : DhtLoopState := { done := false, ret := .ok true, length := initLen, nib := nib1, bib := bib1 }
    let k0 : Nat := if initLen.toInt ≤ 16 then 0 else initLen.toInt.toNat + 1
    have hinit : Inv k0 h1 s0 := by
      refine ⟨hp1, hst01, (fun hno => by simp [s0] at hno), fun _ => ⟨by rw [hinitLen]; omega, by rw [hinitLen]; omega, rfl, hcur1,
        nibBibTrack_mono htr1 (by omega) (by rw [hinitLen]; split <;> omega), hstr1⟩⟩
    have hk0Lt : k0 < C.fuel := by unfold C.fuel; dsimp only [k0]; split <;> omega
    obtain ⟨st, h2, hloop, hpost⟩ :=
      cwhile_terminates
        (fun (s : DhtLoopState) => pure (!s.done && s.length > 16, s))
        (fun (s : DhtLoopState) => do
          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
          | none => return { s with done := true, ret := .ok false }
          | some (index, nibA, bibA) =>
            let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            tracems1 dcCur.err 1 JTRC_DHT index
            let mut bits : Array UInt8 := Array.replicate 17 0
            let mut count : Int32 := 0
            let mut curNib := nibA
            let mut curBib := bibA
            let mut susp := false
            for i in List.range 16 do
              if !susp then
                match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) curNib curBib) with
                | none => susp := true
                | some (b, n', bi') =>
                  let u := UInt8.ofNat b.toInt.toNat
                  bits := bits.set! (i + 1) u
                  count := count + Int32.ofNat u.toNat
                  curNib := n'
                  curBib := bi'
            if susp then
              return { s with done := true, ret := .ok false }
            let len' := Int64.ofInt (s.length.toInt - 17)
            tracems8 dcCur.err 2 JTRC_HUFFBITS
              (Int32.ofNat bits[1]!.toNat) (Int32.ofNat bits[2]!.toNat)
              (Int32.ofNat bits[3]!.toNat) (Int32.ofNat bits[4]!.toNat)
              (Int32.ofNat bits[5]!.toNat) (Int32.ofNat bits[6]!.toNat)
              (Int32.ofNat bits[7]!.toNat) (Int32.ofNat bits[8]!.toNat)
            tracems8 dcCur.err 2 JTRC_HUFFBITS
              (Int32.ofNat bits[9]!.toNat) (Int32.ofNat bits[10]!.toNat)
              (Int32.ofNat bits[11]!.toNat) (Int32.ofNat bits[12]!.toNat)
              (Int32.ofNat bits[13]!.toNat) (Int32.ofNat bits[14]!.toNat)
              (Int32.ofNat bits[15]!.toNat) (Int32.ofNat bits[16]!.toNat)
            if count > 256 || Int64.ofInt count.toInt > len' then
              let _ ← errexit dcCur.err JERR_BAD_HUFF_TABLE
              return { s with done := true, ret := .errExit JERR_BAD_HUFF_TABLE }
            let mut huffval : Array UInt8 := Array.replicate 256 0
            for i in List.range count.toInt.toNat do
              if !susp then
                match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) curNib curBib) with
                | none => susp := true
                | some (v, n', bi') =>
                  huffval := huffval.set! i (UInt8.ofNat v.toInt.toNat)
                  curNib := n'
                  curBib := bi'
            if susp then
              return { s with done := true, ret := .ok false }
            let len'' := Int64.ofInt (len'.toInt - count.toInt)
            let dcTbl ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            let isAc := (index &&& 0x10) != 0
            let tblIdx := if isAc then index - 0x10 else index
            if tblIdx < 0 || tblIdx ≥ NUM_HUFF_TBLS then
              let _ ← errexit1 dcTbl.err JERR_DHT_INDEX tblIdx
              return { s with done := true, ret := .errExit JERR_DHT_INDEX }
            let idxNat := tblIdx.toInt.toNat
            let existingPtr := if isAc then dcTbl.acHuffTblPtrs[idxNat]! else dcTbl.dcHuffTblPtrs[idxNat]!
            let tblPtr ←
              if existingPtr == .null then
                match (← jpeg_alloc_huff_table (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
                | .errExit code => return { s with done := true, ret := .errExit code }
                | .ok p =>
                  let dcU ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                  let dcU' :=
                    if isAc then { dcU with acHuffTblPtrs := dcU.acHuffTblPtrs.set! idxNat p }
                    else { dcU with dcHuffTblPtrs := dcU.dcHuffTblPtrs.set! idxNat p }
                  Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) dcU'
                  pure p
              else
                pure existingPtr
            let curTbl ← Ptr.load tblPtr
            Ptr.store tblPtr { curTbl with bits := bits, huffval := huffval }
            return { done := false, ret := .ok true, length := len'', nib := curNib, bib := curBib })
        Inv Post
        (fun k hCur s ⟨hpC, hstC, hnrC, hactive⟩ => by
          by_cases hcond : (!s.done && s.length > 16) = true
          · refine ⟨true, s, hCur, by simp [hcond], ?_⟩
            simp only [↓reduceIte]
            have hdoneF : s.done = false := by cases hc : s.done <;> simp_all
            have hsgt : s.length > 16 := by
              by_cases hgt : s.length > 16
              · exact hgt
              · simp [hdoneF, hgt] at hcond
            have hsgt16 : 16 < s.length.toInt := by
              have h16 : (16 : Int64).toInt = 16 := by decide
              have := Int64.lt_iff_toInt_lt.mp hsgt
              omega
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
              · simp only [hkEq, show ¬(s.length.toInt ≤ 16) from by omega, ↓reduceIte]; omega
            | some pA =>
              rcases pA with ⟨index, nibA, bibA⟩
              rcases hpostA with ⟨_, _, hcurA, hceA⟩
              obtain ⟨htrA, hstrA⟩ := nibBibTrack_inputByte_step hp hpC htrS (by omega) (by omega) hceA
              obtain ⟨dcsA, hgdcA, hszdcA, kerrA, _⟩ := parserEnv_get_dc hpA
              have hldcA := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcA hszdcA
              obtain ⟨hT, htrT_run, hpT, hdT, hmrT, _, _, hcpT, _, _, _, hbyT, _, hcoT, hnwT⟩ :=
                tracems1_nonneg_parser hpA 1 JTRC_DHT index (by decide)
              have htrT_run' : C.run (tracems1 dcsA[0]!.err 1 JTRC_DHT index) hA = .ok ((), hT) := by
                rw [kerrA]; exact htrT_run
              have hstCT := decompHeaderStable_trans hp hpA hstCA (decompHeaderStable_of_same hdT hmrT hcpT)
              have htrT := nibBibTrack_err_nw_same hpA htrA hnwT
              have hcurT : CurValid hT nibA bibA := curValid_bytes_irrel hbyT hcoT hcurA
              let Inv1 (i : Nat) (s1 : Array UInt8 × Int32 × C.BPtr × UInt64 × Bool) (hCur1 : C.Heap) : Prop :=
                ParserEnv ctx hCur1 ∧
                DecompHeaderStable ctx h hCur1 ∧
                0 ≤ s1.2.1.toInt ∧ s1.2.1.toInt ≤ (i : Int) * 255 ∧
                (!s1.2.2.2.2 →
                  CurValid hCur1 s1.2.2.1 s1.2.2.2.1 ∧
                  NibBibTrack ctx h hCur1 s1.2.2.1 s1.2.2.2.1 (-8) (2 + (65533 - s.length.toInt) + 1 + (i : Int)) ∧
                  (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
                    isConstEofPtr s1.2.2.1 = true ∨ s1.2.2.2.1.toNat < srcs0[0]!.bytesInBuffer.toNat))
              let s1Init : Array UInt8 × Int32 × C.BPtr × UInt64 × Bool :=
                (Array.replicate 17 0, 0, nibA, bibA, false)
              have hInv1_0 : Inv1 0 s1Init hT :=
                ⟨hpT, hstCT, (by dsimp [s1Init]; decide), (by dsimp [s1Init]; decide), fun _ => ⟨hcurT,
                  nibBibTrack_mono (by
                    have hsneg : ¬(s.length.toInt < 0) := by omega
                    simp only [eq_false hsneg, ↓reduceIte] at htrS
                    exact htrT) (by omega) (by omega), hstrA⟩⟩
              obtain ⟨s1Fin, h1F, hfor1, hInv1Fin⟩ := forIn_range_inv Inv1
                (fun (i : Nat) (s1 : Array UInt8 × Int32 × C.BPtr × UInt64 × Bool) => do
                  if !s1.2.2.2.2 then
                    match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s1.2.2.1 s1.2.2.2.1) with
                    | none => return .yield (s1.1, s1.2.1, s1.2.2.1, s1.2.2.2.1, true)
                    | some (b, n', bi') =>
                      let u := UInt8.ofNat b.toInt.toNat
                      return .yield (s1.1.set! (i + 1) u, s1.2.1 + Int32.ofNat u.toNat, n', bi', s1.2.2.2.2)
                  else
                    return .yield s1)
                16
                (fun i hi s1 hC1 ⟨hp1c, hst1c, hc0, hcHi, hact1⟩ => by
                  by_cases hns : (!s1.2.2.2.2) = true
                  · have hsF : s1.2.2.2.2 = false := by cases hc : s1.2.2.2.2 <;> simp_all
                    obtain ⟨hcur1s, htr1s, _⟩ := hact1 (by simp [hsF])
                    have hbd1 : s1.2.2.2.1 = 0 → ∀ errs, C.Space.get hC1 ctx.rerr = some errs → 0 < errs.size →
                        errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
                      nibBibTrack_bd hp hp1c htr1s (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                        have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
                    obtain ⟨res1b, h1b, hrun1b, hp1b, hd1b, hmr1b, _, hcp1b, _, _, _, _, _, _, hpost1b⟩ :=
                      inputByte_parser hp1c s1.2.2.1 s1.2.2.2.1 hcur1s hbd1
                    have hstC1b := decompHeaderStable_trans hp hp1c hst1c (decompHeaderStable_of_same hd1b hmr1b hcp1b)
                    cases res1b with
                    | none =>
                      refine ⟨.yield (s1.1, s1.2.1, s1.2.2.1, s1.2.2.2.1, true), h1b, ?_, hp1b, hstC1b,
                        hc0, by change s1.2.1.toInt ≤ ((i : Int) + 1) * 255; omega, fun hno => by simp at hno⟩
                      simp only [hns, ↓reduceIte, C.run_bind, hrun1b]; rfl
                    | some y =>
                      rcases y with ⟨b, n', bi'⟩
                      rcases hpost1b with ⟨_, _, hcur1b, hce1b⟩
                      obtain ⟨htr1b, hstr1b⟩ := nibBibTrack_inputByte_step hp hp1c htr1s (by omega) (by omega) hce1b
                      let u := UInt8.ofNat b.toInt.toNat
                      have huLt : u.toNat ≤ 255 := Nat.le_of_lt_succ (UInt8.toNat_lt u)
                      have hsumTo : (s1.2.1 + Int32.ofNat u.toNat).toInt = s1.2.1.toInt + (u.toNat : Int) := by
                        rw [Int32.toInt_add, int32_toInt_ofNat_small (by omega)]
                        exact Int.bmod_eq_of_le (by omega) (by omega)
                      refine ⟨.yield (s1.1.set! (i + 1) u, s1.2.1 + Int32.ofNat u.toNat, n', bi', s1.2.2.2.2),
                        h1b, ?_, hp1b, hstC1b, by rw [hsumTo]; omega,
                        by change (s1.2.1 + Int32.ofNat u.toNat).toInt ≤ ((i : Int) + 1) * 255; rw [hsumTo]; omega, fun _ => ?_⟩
                      · simp only [hns, ↓reduceIte, C.run_bind, hrun1b]; rfl
                      · exact ⟨hcur1b, nibBibTrack_mono htr1b (by omega) (by omega), hstr1b⟩
                  · have hsT : (!s1.2.2.2.2) = false := by cases hc : (!s1.2.2.2.2) <;> simp_all
                    refine ⟨.yield s1, hC1, ?_, hp1c, hst1c, hc0,
                      by change s1.2.1.toInt ≤ ((i : Int) + 1) * 255; omega, fun hno => by simp [hsT] at hno⟩
                    simp only [hsT, Bool.false_eq_true, ↓reduceIte]; rfl)
                hInv1_0
              rcases hInv1Fin with ⟨hp1F, hstC1F, hcnt0, hcntHi, hact1F⟩
              change s1Fin.2.1.toInt ≤ 4080 at hcntHi
              by_cases hsusp1 : s1Fin.2.2.2.2 = true
              · refine ⟨0, { s with done := true, ret := .ok false }, h1F, ?_, ?_, hp1F, hstC1F,
                  (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                · rw [C.run_bind, hrunA]; dsimp only
                  rw [C.run_bind, hldcA]; dsimp only
                  rw [C.run_bind, htrT_run']; dsimp only
                  rw [C.run_bind]; erw [hfor1]; dsimp only
                  simp only [hsusp1, ↓reduceIte]; rfl
                · simp only [hkEq, show ¬(s.length.toInt ≤ 16) from by omega, ↓reduceIte]; omega
              · have hsusp1F : s1Fin.2.2.2.2 = false := by cases hc : s1Fin.2.2.2.2 <;> simp_all
                obtain ⟨hcur1F, htr1F, hstr1F⟩ := hact1F (by simp [hsusp1F])
                let bits := s1Fin.1
                let count := s1Fin.2.1
                let len' : Int64 := Int64.ofInt (s.length.toInt - 17)
                have hlen'To : len'.toInt = s.length.toInt - 17 := by
                  change (Int64.ofInt (s.length.toInt - 17)).toInt = s.length.toInt - 17
                  rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
                  exact Int.bmod_eq_of_le (by omega) (by omega)
                obtain ⟨hM1, htrM1, hpM1, hdM1, hmrM1, _, _, hcpM1, _, _, _, hbyM1, _, hcoM1, hnwM1⟩ :=
                  tracems8_nonneg_parser hp1F 2 JTRC_HUFFBITS
                    (Int32.ofNat bits[1]!.toNat) (Int32.ofNat bits[2]!.toNat)
                    (Int32.ofNat bits[3]!.toNat) (Int32.ofNat bits[4]!.toNat)
                    (Int32.ofNat bits[5]!.toNat) (Int32.ofNat bits[6]!.toNat)
                    (Int32.ofNat bits[7]!.toNat) (Int32.ofNat bits[8]!.toNat) (by decide)
                have hstCM1 := decompHeaderStable_trans hp hp1F hstC1F (decompHeaderStable_of_same hdM1 hmrM1 hcpM1)
                have htrM1' := nibBibTrack_err_nw_same hp1F htr1F hnwM1
                obtain ⟨hM2, htrM2, hpM2, hdM2, hmrM2, _, _, hcpM2, _, _, _, hbyM2, _, hcoM2, hnwM2⟩ :=
                  tracems8_nonneg_parser hpM1 2 JTRC_HUFFBITS
                    (Int32.ofNat bits[9]!.toNat) (Int32.ofNat bits[10]!.toNat)
                    (Int32.ofNat bits[11]!.toNat) (Int32.ofNat bits[12]!.toNat)
                    (Int32.ofNat bits[13]!.toNat) (Int32.ofNat bits[14]!.toNat)
                    (Int32.ofNat bits[15]!.toNat) (Int32.ofNat bits[16]!.toNat) (by decide)
                have hstCM2 := decompHeaderStable_trans hp hpM1 hstCM1 (decompHeaderStable_of_same hdM2 hmrM2 hcpM2)
                have htrM2' := nibBibTrack_err_nw_same hpM1 htrM1' hnwM2
                have htrM1_run' : C.run (tracems8 dcsA[0]!.err 2 JTRC_HUFFBITS
                    (Int32.ofNat bits[1]!.toNat) (Int32.ofNat bits[2]!.toNat)
                    (Int32.ofNat bits[3]!.toNat) (Int32.ofNat bits[4]!.toNat)
                    (Int32.ofNat bits[5]!.toNat) (Int32.ofNat bits[6]!.toNat)
                    (Int32.ofNat bits[7]!.toNat) (Int32.ofNat bits[8]!.toNat)) h1F = .ok ((), hM1) := by
                  rw [kerrA]; exact htrM1
                have htrM2_run' : C.run (tracems8 dcsA[0]!.err 2 JTRC_HUFFBITS
                    (Int32.ofNat bits[9]!.toNat) (Int32.ofNat bits[10]!.toNat)
                    (Int32.ofNat bits[11]!.toNat) (Int32.ofNat bits[12]!.toNat)
                    (Int32.ofNat bits[13]!.toNat) (Int32.ofNat bits[14]!.toNat)
                    (Int32.ofNat bits[15]!.toNat) (Int32.ofNat bits[16]!.toNat)) hM1 = .ok ((), hM2) := by
                  rw [kerrA]; exact htrM2
                have hcurM2 : CurValid hM2 s1Fin.2.2.1 s1Fin.2.2.2.1 :=
                  curValid_bytes_irrel hbyM2 hcoM2 (curValid_bytes_irrel hbyM1 hcoM1 hcur1F)
                have hcntLe4080 : count.toInt ≤ 4080 := hcntHi
                have hcnt0' : 0 ≤ count.toInt := hcnt0
                have hcnt64 : (Int64.ofInt count.toInt).toInt = count.toInt := by
                  rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
                  exact Int.bmod_eq_of_le (by omega) (by omega)
                by_cases hbadCnt : (count > 256 || Int64.ofInt count.toInt > len') = true
                · obtain ⟨hE, herr_run, hpE, hstM2E⟩ := errexit_stable_parser hpM2 JERR_BAD_HUFF_TABLE
                  have herr_run' : C.run (errexit dcsA[0]!.err JERR_BAD_HUFF_TABLE) hM2 = .ok (.errExit JERR_BAD_HUFF_TABLE, hE) := by
                    rw [kerrA]; exact herr_run
                  refine ⟨0, { s with done := true, ret := .errExit JERR_BAD_HUFF_TABLE }, hE, ?_, ?_, hpE,
                    decompHeaderStable_trans hp hpM2 hstCM2 hstM2E, (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                  · rw [C.run_bind, hrunA]; dsimp only
                    rw [C.run_bind, hldcA]; dsimp only
                    rw [C.run_bind, htrT_run']; dsimp only
                    rw [C.run_bind]; erw [hfor1]; dsimp only
                    simp only [hsusp1F, Bool.false_eq_true, ↓reduceIte]
                    rw [C.run_bind, htrM1_run']; dsimp only
                    rw [C.run_bind, htrM2_run']; dsimp only
                    dsimp only [count, len'] at hbadCnt
                    simp only [hbadCnt, ↓reduceIte, C.run_bind, herr_run']; rfl
                  · simp only [hkEq, show ¬(s.length.toInt ≤ 16) from by omega, ↓reduceIte]; omega
                · have hgoodCnt : (count > 256 || Int64.ofInt count.toInt > len') = false :=
                    Bool.eq_false_iff.mpr hbadCnt
                  have hcntLe256 : count.toInt ≤ 256 := by
                    by_cases hgt : count > 256
                    · have : (count > 256 || Int64.ofInt count.toInt > len') = true := by
                        rw [Bool.or_eq_true]; left; exact decide_eq_true hgt
                      rw [this] at hgoodCnt; cases hgoodCnt
                    · have := Int32.le_iff_toInt_le.mp (Int32.not_lt.mp hgt)
                      have h256 : (256 : Int32).toInt = 256 := by decide
                      omega
                  have hcntLeLen' : count.toInt ≤ len'.toInt := by
                    by_cases hgt : Int64.ofInt count.toInt > len'
                    · have : (count > 256 || Int64.ofInt count.toInt > len') = true := by
                        rw [Bool.or_eq_true]; right; exact decide_eq_true hgt
                      rw [this] at hgoodCnt; cases hgoodCnt
                    · have := Int64.le_iff_toInt_le.mp (Int64.not_lt.mp hgt)
                      omega
                  dsimp only [count, len'] at hgoodCnt
                  let Inv2 (i : Nat) (s2 : C.BPtr × UInt64 × Bool × Array UInt8) (hC2 : C.Heap) : Prop :=
                    ParserEnv ctx hC2 ∧
                    DecompHeaderStable ctx h hC2 ∧
                    (!s2.2.2.1 →
                      CurValid hC2 s2.1 s2.2.1 ∧
                      NibBibTrack ctx h hC2 s2.1 s2.2.1 (-8) (2 + (65533 - s.length.toInt) + 17 + (i : Int)) ∧
                      (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
                        isConstEofPtr s2.1 = true ∨ s2.2.1.toNat < srcs0[0]!.bytesInBuffer.toNat))
                  have hInv2_0 : Inv2 0 (s1Fin.2.2.1, s1Fin.2.2.2.1, false, Array.replicate 256 0) hM2 :=
                    ⟨hpM2, hstCM2, fun _ => ⟨hcurM2, nibBibTrack_mono htrM2' (by omega) (by omega), hstr1F⟩⟩
                  obtain ⟨s2Fin, h2F, hfor2, hInv2Fin⟩ := forIn_range_inv Inv2
                    (fun (i : Nat) (s2 : C.BPtr × UInt64 × Bool × Array UInt8) => do
                      if !s2.2.2.1 then
                        match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s2.1 s2.2.1) with
                        | none => return .yield (s2.1, s2.2.1, true, s2.2.2.2)
                        | some (v, n', bi') =>
                          return .yield (n', bi', s2.2.2.1, s2.2.2.2.set! i (UInt8.ofNat v.toInt.toNat))
                      else
                        return .yield (s2.1, s2.2.1, s2.2.2.1, s2.2.2.2))
                    count.toInt.toNat
                    (fun i hi s2 hC2 ⟨hp2c, hst2c, hact2⟩ => by
                      by_cases hns : (!s2.2.2.1) = true
                      · have hsF : s2.2.2.1 = false := by cases hc : s2.2.2.1 <;> simp_all
                        obtain ⟨hcur2s, htr2s, _⟩ := hact2 (by simp [hsF])
                        have hbd2 : s2.2.1 = 0 → ∀ errs, C.Space.get hC2 ctx.rerr = some errs → 0 < errs.size →
                            errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
                          nibBibTrack_bd hp hp2c htr2s (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                            have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
                        obtain ⟨res2b, h2b, hrun2b, hp2b, hd2b, hmr2b, _, hcp2b, _, _, _, _, _, _, hpost2b⟩ :=
                          inputByte_parser hp2c s2.1 s2.2.1 hcur2s hbd2
                        have hstC2b := decompHeaderStable_trans hp hp2c hst2c (decompHeaderStable_of_same hd2b hmr2b hcp2b)
                        cases res2b with
                        | none =>
                          refine ⟨.yield (s2.1, s2.2.1, true, s2.2.2.2), h2b, ?_, hp2b, hstC2b, fun hno => by simp at hno⟩
                          simp only [hns, ↓reduceIte, C.run_bind, hrun2b]; rfl
                        | some y =>
                          rcases y with ⟨v, n', bi'⟩
                          rcases hpost2b with ⟨_, _, hcur2b, hce2b⟩
                          obtain ⟨htr2b, hstr2b⟩ := nibBibTrack_inputByte_step hp hp2c htr2s (by omega) (by omega) hce2b
                          refine ⟨.yield (n', bi', s2.2.2.1, s2.2.2.2.set! i (UInt8.ofNat v.toInt.toNat)),
                            h2b, ?_, hp2b, hstC2b, fun _ => ?_⟩
                          · simp only [hns, ↓reduceIte, C.run_bind, hrun2b]; rfl
                          · exact ⟨hcur2b, nibBibTrack_mono htr2b (by omega) (by omega), hstr2b⟩
                      · have hsT : (!s2.2.2.1) = false := by cases hc : (!s2.2.2.1) <;> simp_all
                        refine ⟨.yield (s2.1, s2.2.1, s2.2.2.1, s2.2.2.2), hC2, ?_, hp2c, hst2c, fun hno => by simp [hsT] at hno⟩
                        simp only [hsT, Bool.false_eq_true, ↓reduceIte]; rfl)
                    hInv2_0
                  rcases hInv2Fin with ⟨hp2F, hstC2F, hact2F⟩
                  by_cases hsusp2 : s2Fin.2.2.1 = true
                  · refine ⟨0, { s with done := true, ret := .ok false }, h2F, ?_, ?_, hp2F, hstC2F,
                      (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                    · rw [C.run_bind, hrunA]; dsimp only
                      rw [C.run_bind, hldcA]; dsimp only
                      rw [C.run_bind, htrT_run']; dsimp only
                      rw [C.run_bind]; erw [hfor1]; dsimp only
                      simp only [hsusp1F, Bool.false_eq_true, ↓reduceIte]
                      rw [C.run_bind, htrM1_run']; dsimp only
                      rw [C.run_bind, htrM2_run']; dsimp only
                      simp only [hgoodCnt, Bool.false_eq_true, ↓reduceIte]
                      rw [C.run_bind]; erw [hfor2]; dsimp only
                      simp only [hsusp2, ↓reduceIte]; rfl
                    · simp only [hkEq, show ¬(s.length.toInt ≤ 16) from by omega, ↓reduceIte]; omega
                  · have hsusp2F : s2Fin.2.2.1 = false := Bool.eq_false_iff.mpr hsusp2
                    obtain ⟨hcur2F, htr2F, hstr2F⟩ := hact2F (by simp [hsusp2F])
                    let len'' : Int64 := Int64.ofInt (len'.toInt - count.toInt)
                    have hlen''To : len''.toInt = len'.toInt - count.toInt := by
                      change (Int64.ofInt (len'.toInt - count.toInt)).toInt = len'.toInt - count.toInt
                      rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
                      exact Int.bmod_eq_of_le (by omega) (by omega)
                    have hlen''0 : 0 ≤ len''.toInt := by rw [hlen''To]; omega
                    let k' : Nat := if len''.toInt ≤ 16 then 0 else len''.toInt.toNat + 1
                    have hkLt : k' < k := by
                      dsimp only [k']; rw [hkEq]
                      simp only [show ¬(s.length.toInt ≤ 16) from by omega, ↓reduceIte]
                      rw [hlen''To, hlen'To]; split <;> omega
                    obtain ⟨dcs2F, hgdc2F, hszdc2F, kerr2F, kmem2F, kmas2F, kic2F, kmrk2F, ksrc2F⟩ := parserEnv_get_dc hp2F
                    have hldc2F := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc2F hszdc2F
                    let dcTbl := dcs2F[0]!
                    let isAc := (index &&& 0x10) != 0
                    let tblIdx := if isAc then index - 0x10 else index
                    by_cases hbadIdx : (tblIdx < 0 || tblIdx ≥ NUM_HUFF_TBLS) = true
                    · obtain ⟨hE, herr_run, hpE, hst2E⟩ := errexit1_stable_parser hp2F JERR_DHT_INDEX tblIdx
                      have herr_run' : C.run (errexit1 dcTbl.err JERR_DHT_INDEX tblIdx) h2F = .ok (.errExit JERR_DHT_INDEX, hE) := by
                        rw [kerr2F]; exact herr_run
                      refine ⟨0, { s with done := true, ret := .errExit JERR_DHT_INDEX }, hE, ?_, ?_, hpE,
                        decompHeaderStable_trans hp hp2F hstC2F hst2E, (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                      · rw [C.run_bind, hrunA]; dsimp only
                        rw [C.run_bind, hldcA]; dsimp only
                        rw [C.run_bind, htrT_run']; dsimp only
                        rw [C.run_bind]; erw [hfor1]; dsimp only
                        simp only [hsusp1F, Bool.false_eq_true, ↓reduceIte]
                        rw [C.run_bind, htrM1_run']; dsimp only
                        rw [C.run_bind, htrM2_run']; dsimp only
                        simp only [hgoodCnt, Bool.false_eq_true, ↓reduceIte]
                        rw [C.run_bind]; erw [hfor2]; dsimp only
                        simp only [hsusp2F, Bool.false_eq_true, ↓reduceIte]
                        rw [C.run_bind, hldc2F]; dsimp only
                        dsimp only [dcTbl, tblIdx, isAc] at herr_run' hbadIdx
                        simp only [hbadIdx, ↓reduceIte, C.run_bind, herr_run']; rfl
                      · simp only [hkEq, show ¬(s.length.toInt ≤ 16) from by omega, ↓reduceIte]; omega
                    · have hgoodIdx : (tblIdx < 0 || tblIdx ≥ NUM_HUFF_TBLS) = false :=
                        Bool.eq_false_iff.mpr hbadIdx
                      have hti0 : 0 ≤ tblIdx.toInt := by
                        by_cases hlt : tblIdx < 0
                        · have : (tblIdx < 0 || tblIdx ≥ NUM_HUFF_TBLS) = true := by
                            rw [Bool.or_eq_true]; left; exact decide_eq_true hlt
                          rw [this] at hgoodIdx; cases hgoodIdx
                        · exact Int32.le_iff_toInt_le.mp (Int32.not_lt.mp hlt)
                      have hti4 : tblIdx.toInt < 4 := by
                        by_cases hge : tblIdx ≥ NUM_HUFF_TBLS
                        · have : (tblIdx < 0 || tblIdx ≥ NUM_HUFF_TBLS) = true := by
                            rw [Bool.or_eq_true]; right; exact decide_eq_true hge
                          rw [this] at hgoodIdx; cases hgoodIdx
                        · have h4 : NUM_HUFF_TBLS.toInt = 4 := by decide
                          have := Int32.lt_iff_toInt_lt.mp (Int32.not_le.mp hge)
                          omega
                      dsimp only [tblIdx, isAc] at hgoodIdx
                      let idxNat := tblIdx.toInt.toNat
                      have hidxNatLt4 : idxNat < 4 := by omega
                      let existingPtr := if isAc then dcTbl.acHuffTblPtrs[idxNat]! else dcTbl.dcHuffTblPtrs[idxNat]!
                      have hstoreHuff : ∀ (tblPtr : C.HuffPtr) h3 (hp3 : ParserEnv ctx h3) (hstC3 : DecompHeaderStable ctx h h3)
                          (hby23 : h3.bytes = h2F.bytes) (hco23 : h3.consts = h2F.consts)
                          (herr23 : h3.errMgrs = h2F.errMgrs) (hsr23 : h3.srcs = h2F.srcs)
                          (htblLive : ∃ rh off hs, tblPtr = .ref rh off ∧ C.Space.get h3 rh = some hs ∧ off < hs.size),
                          ∃ h4,
                            C.run (do
                              let curTbl ← Ptr.load tblPtr
                              Ptr.store tblPtr ({ curTbl with bits := bits, huffval := s2Fin.2.2.2 } : C.JHuffTbl)
                              pure ({ done := false, ret := JpegRes.ok true, length := len'', nib := s2Fin.1, bib := s2Fin.2.1 } : DhtLoopState)) h3 =
                              .ok ({ done := false, ret := .ok true, length := len'', nib := s2Fin.1, bib := s2Fin.2.1 }, h4) ∧
                            ParserEnv ctx h4 ∧ DecompHeaderStable ctx h h4 ∧
                            CurValid h4 s2Fin.1 s2Fin.2.1 ∧
                            NibBibTrack ctx h h4 s2Fin.1 s2Fin.2.1 (-8) (2 + (65533 - len''.toInt)) ∧
                            (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
                              isConstEofPtr s2Fin.1 = true ∨ s2Fin.2.1.toNat < srcs0[0]!.bytesInBuffer.toNat) := by
                        intro tblPtr h3 hp3 hstC3 hby23 hco23 herr23 hsr23 ⟨rh, off, hs, htpEq, hgH, hoffH⟩
                        subst htpEq
                        have hlH := ptr_load_ok (r := rh) (off := off) hgH hoffH
                        have hroH : C.Space.ro h3 rh = false := by cases rh; rfl
                        let tblNew := { hs[off]! with bits := bits, huffval := s2Fin.2.2.2 }
                        have hsH := ptr_store_ok (r := rh) (off := off) (v := tblNew) hgH hroH hoffH
                        let h4 := C.Space.put h3 rh (hs.set! off tblNew)
                        have hp4 : ParserEnv ctx h4 := parserEnv_put_huff hp3 hgH
                        have hd34 : h4.decomps = h3.decomps := by cases rh; rfl
                        have hm34 : h4.markers = h3.markers := by cases rh; rfl
                        have hc34 : h4.comps = h3.comps := by cases rh; rfl
                        have hst34 := decompHeaderStable_of_same (ctx := ctx) hd34 hm34 hc34
                        have hstC4 := decompHeaderStable_trans hp hp3 hstC3 hst34
                        have hby34 : h4.bytes = h3.bytes := by cases rh; rfl
                        have hco34 : h4.consts = h3.consts := by cases rh; rfl
                        have he34 : h4.errMgrs = h3.errMgrs := by cases rh; rfl
                        have hcur4 : CurValid h4 s2Fin.1 s2Fin.2.1 :=
                          curValid_bytes_irrel (hby34.trans hby23) (hco34.trans hco23) hcur2F
                        have htr4 : NibBibTrack ctx h h4 s2Fin.1 s2Fin.2.1 (-8) (2 + (65533 - len''.toInt)) := by
                          have hcntEq : ((count.toInt.toNat : Nat) : Int) = count.toInt :=
                            Int.toNat_of_nonneg (by omega)
                          have heq2 : 2 + (65533 - s.length.toInt) + 17 + ((count.toInt.toNat : Nat) : Int) = 2 + (65533 - len''.toInt) := by
                            rw [hcntEq, hlen''To, hlen'To]; omega
                          rw [← heq2]
                          exact nibBibTrack_err_same (nibBibTrack_err_same htr2F herr23) he34
                        refine ⟨h4, ?_, hp4, hstC4, hcur4, htr4, hstr2F⟩
                        rw [C.run_bind, hlH]; dsimp only
                        rw [C.run_bind, hsH]; rfl
                      by_cases hexNull : (existingPtr == .null) = true
                      · obtain ⟨resAlloc, hAlloc, hrunAlloc, hpAlloc, hresAlloc⟩ := jpeg_alloc_huff_table_parser hp2F
                        cases resAlloc with
                        | errExit code =>
                          rcases hresAlloc with ⟨hdA, hmrA, hcpA⟩
                          refine ⟨0, { s with done := true, ret := .errExit code }, hAlloc, ?_, ?_, hpAlloc,
                            decompHeaderStable_trans hp hp2F hstC2F (decompHeaderStable_of_same hdA hmrA hcpA),
                            (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                          · rw [C.run_bind, hrunA]; dsimp only
                            rw [C.run_bind, hldcA]; dsimp only
                            rw [C.run_bind, htrT_run']; dsimp only
                            rw [C.run_bind]; erw [hfor1]; dsimp only
                            simp only [hsusp1F, Bool.false_eq_true, ↓reduceIte]
                            rw [C.run_bind, htrM1_run']; dsimp only
                            rw [C.run_bind, htrM2_run']; dsimp only
                            simp only [hgoodCnt, Bool.false_eq_true, ↓reduceIte]
                            rw [C.run_bind]; erw [hfor2]; dsimp only
                            simp only [hsusp2F, Bool.false_eq_true, ↓reduceIte]
                            rw [C.run_bind, hldc2F]; dsimp only
                            dsimp only [existingPtr, dcTbl, idxNat, tblIdx, isAc] at hexNull hgoodIdx
                            simp only [hgoodIdx, Bool.false_eq_true, ↓reduceIte, hexNull]
                            rw [C.run_bind, hrunAlloc]; rfl
                          · simp only [hkEq, show ¬(s.length.toInt ≤ 16) from by omega, ↓reduceIte]; omega
                        | ok p =>
                          rcases hresAlloc with ⟨hpne, hdA, hmrA, hsrA, heA, hmaA, hcpA, hqA, hsmA, hbyA, hcoA, rh, off, hs, hpEq, hgHA, hoffHA⟩
                          obtain ⟨dcsA2, hgdcA2, hszdcA2, _⟩ := parserEnv_get_dc hpAlloc
                          have hldcA2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcA2 hszdcA2
                          have hroDcA2 : C.Space.ro hAlloc (C.DecompRef.decomp ctx.bdc) = false := rfl
                          let dcU' := if isAc then { dcsA2[0]! with acHuffTblPtrs := dcsA2[0]!.acHuffTblPtrs.set! idxNat p }
                            else { dcsA2[0]! with dcHuffTblPtrs := dcsA2[0]!.dcHuffTblPtrs.set! idxNat p }
                          have hstDcU := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcU') hgdcA2 hroDcA2 hszdcA2
                          let h3 := C.Space.put hAlloc (C.DecompRef.decomp ctx.bdc) (dcsA2.set! 0 dcU')
                          have hstAlloc := decompHeaderStable_trans hp hp2F hstC2F (decompHeaderStable_of_same hdA hmrA hcpA)
                          have hp3 : ParserEnv ctx h3 :=
                            parserEnv_put_dc_huffTbl hpAlloc hgdcA2 hszdcA2 isAc idxNat hidxNatLt4 p hpEq hgHA hoffHA
                          have hst3 : DecompHeaderStable ctx hAlloc h3 := by
                            refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
                              (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
                            intro da db hga _ hgb _
                            have ha := Option.some.inj (hga.symm.trans hgdcA2)
                            have hg3 : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcsA2.set! 0 dcU') := by
                              simp [h3, C.Space.get, C.Space.put]
                            have hb := Option.some.inj (hgb.symm.trans hg3)
                            rw [ha, hb, set0_bang_m dcsA2 hszdcA2 dcU']
                            dsimp [dcU']; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                          have hstC3 := decompHeaderStable_trans hp hpAlloc hstAlloc hst3
                          obtain ⟨h4, hrun4, hp4, hstC4, hcur4, htr4, hstr4⟩ := hstoreHuff p h3 hp3 hstC3
                            hbyA hcoA heA hsrA ⟨rh, off, hs, hpEq, hgHA, hoffHA⟩
                          refine ⟨k', { done := false, ret := .ok true, length := len'', nib := s2Fin.1, bib := s2Fin.2.1 },
                            h4, ?_, hkLt, hp4, hstC4, (fun hno => by simp at hno), fun _ => ⟨by dsimp only; omega, by rw [hlen''To, hlen'To]; omega, rfl, hcur4,
                              (by simp only [eq_false (by omega : ¬(len''.toInt < 0)), ↓reduceIte]; exact htr4), hstr4⟩⟩
                          rw [C.run_bind, hrunA]; dsimp only
                          rw [C.run_bind, hldcA]; dsimp only
                          rw [C.run_bind, htrT_run']; dsimp only
                          rw [C.run_bind]; erw [hfor1]; dsimp only
                          simp only [hsusp1F, Bool.false_eq_true, ↓reduceIte]
                          rw [C.run_bind, htrM1_run']; dsimp only
                          rw [C.run_bind, htrM2_run']; dsimp only
                          simp only [hgoodCnt, Bool.false_eq_true, ↓reduceIte]
                          rw [C.run_bind]; erw [hfor2]; dsimp only
                          simp only [hsusp2F, Bool.false_eq_true, ↓reduceIte]
                          rw [C.run_bind, hldc2F]; dsimp only
                          dsimp only [existingPtr, dcTbl, idxNat, tblIdx, isAc] at hexNull hgoodIdx
                          simp only [hgoodIdx, Bool.false_eq_true, ↓reduceIte, hexNull]
                          rw [C.run_bind, hrunAlloc]; dsimp only
                          rw [C.run_bind, hldcA2]; dsimp only
                          rw [C.run_bind, hstDcU]; dsimp only
                          exact hrun4
                      · have hexNullF : (existingPtr == .null) = false := Bool.eq_false_iff.mpr hexNull
                        have hexNeNull : existingPtr ≠ .null := fun heq => by simp [heq] at hexNullF
                        have htblLive : ∃ rh off hs, existingPtr = .ref rh off ∧ C.Space.get h2F rh = some hs ∧ off < hs.size := by
                          cases hAc : isAc
                          · obtain ⟨dcsH, hgH, _, _, hdhH⟩ := parserEnv_get_huff_dc hp2F hidxNatLt4
                            have hdEq := Option.some.inj (hgdc2F.symm.trans hgH)
                            rcases hdhH with hn | hlive
                            · exact False.elim (hexNeNull (by dsimp [existingPtr]; rw [hAc]; simp [dcTbl, hdEq, hn]))
                            · rcases hlive with ⟨rh, off, hs, heq, hg, hoff⟩
                              dsimp [existingPtr]; rw [hAc]; simp only [dcTbl, hdEq]
                              exact ⟨rh, off, hs, heq, hg, hoff⟩
                          · obtain ⟨dcsH, hgH, _, _, hahH⟩ := parserEnv_get_huff_ac hp2F hidxNatLt4
                            have hdEq := Option.some.inj (hgdc2F.symm.trans hgH)
                            rcases hahH with hn | hlive
                            · exact False.elim (hexNeNull (by dsimp [existingPtr]; rw [hAc]; simp [dcTbl, hdEq, hn]))
                            · rcases hlive with ⟨rh, off, hs, heq, hg, hoff⟩
                              dsimp [existingPtr]; rw [hAc]; simp only [dcTbl, hdEq]
                              exact ⟨rh, off, hs, heq, hg, hoff⟩
                        obtain ⟨h4, hrun4, hp4, hstC4, hcur4, htr4, hstr4⟩ := hstoreHuff existingPtr h2F hp2F hstC2F
                          rfl rfl rfl rfl htblLive
                        refine ⟨k', { done := false, ret := .ok true, length := len'', nib := s2Fin.1, bib := s2Fin.2.1 },
                          h4, ?_, hkLt, hp4, hstC4, (fun hno => by simp at hno), fun _ => ⟨by dsimp only; omega, by rw [hlen''To, hlen'To]; omega, rfl, hcur4,
                            (by simp only [eq_false (by omega : ¬(len''.toInt < 0)), ↓reduceIte]; exact htr4), hstr4⟩⟩
                        rw [C.run_bind, hrunA]; dsimp only
                        rw [C.run_bind, hldcA]; dsimp only
                        rw [C.run_bind, htrT_run']; dsimp only
                        rw [C.run_bind]; erw [hfor1]; dsimp only
                        simp only [hsusp1F, Bool.false_eq_true, ↓reduceIte]
                        rw [C.run_bind, htrM1_run']; dsimp only
                        rw [C.run_bind, htrM2_run']; dsimp only
                        simp only [hgoodCnt, Bool.false_eq_true, ↓reduceIte]
                        rw [C.run_bind]; erw [hfor2]; dsimp only
                        simp only [hsusp2F, Bool.false_eq_true, ↓reduceIte]
                        rw [C.run_bind, hldc2F]; dsimp only
                        dsimp only [existingPtr, dcTbl, idxNat, tblIdx, isAc] at hexNullF hgoodIdx hrun4
                        simp only [hgoodIdx, Bool.false_eq_true, ↓reduceIte, hexNullF]
                        rw [C.run_bind]; dsimp only [C.run, pure]
                        exact hrun4
          · have hcondF : (!s.done && s.length > 16) = false := by cases hc : (!s.done && s.length > 16) <;> simp_all
            refine ⟨false, s, hCur, (by simp only [C.run, pure, hcondF]), ?_⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨hpC, hstC, hnrC, fun hnd => ?_⟩
            obtain ⟨_, _, _, hcurS, htrS, hstrS⟩ := hactive hnd
            have hle16 : s.length.toInt ≤ 16 := by
              have hnotgt : ¬(s.length > 16) := by
                have hdF : s.done = false := by cases hd : s.done <;> simp_all
                intro hgt; simp [hdF, hgt] at hcondF
              by_cases hpos : s.length.toInt ≤ 16
              · exact hpos
              · exact False.elim (hnotgt (Int64.lt_iff_toInt_lt.mpr (by change (16 : Int) < s.length.toInt; omega)))
            exact ⟨hle16, hcurS, nibBibTrack_mono htrS (by omega) (by split <;> omega), hstrS⟩)
        hk0Lt hinit
    rcases hpost with ⟨hp2, hst02, hnr2, hfin⟩
    dsimp only [s0, initLen] at hloop
    by_cases hdone : st.done = true
    · refine ⟨st.ret, h2, ?_, hp2, hst02, ?_⟩
      · unfold get_dht
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
    · have hdoneF : st.done = false := Bool.eq_false_iff.mpr hdone
      obtain ⟨hstlen, hcurSt, htrSt, hstrSt⟩ := hfin (by simp [hdoneF])
      by_cases hne0 : (st.length != 0) = true
      · obtain ⟨dcs2, hgdc2, hszdc2, kerr2, _⟩ := parserEnv_get_dc hp2
        obtain ⟨h_err, herr_run, hp_err, hstErr⟩ := errexit_stable_parser hp2 JERR_BAD_LENGTH
        have herr_run' : C.run (errexit dcs2[0]!.err JERR_BAD_LENGTH) h2 = .ok (.errExit JERR_BAD_LENGTH, h_err) := by
          rw [kerr2]; exact herr_run
        refine ⟨.errExit JERR_BAD_LENGTH, h_err, ?_, hp_err, decompHeaderStable_trans hp hp2 hst02 hstErr, trivial⟩
        unfold get_dht
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind]; erw [hloop]; dsimp only
        simp only [hdoneF, Bool.false_eq_true, ↓reduceIte, hne0, C.run_bind, herr_run',
          ptr_load_ok hgdc2 hszdc2]; rfl
      · have hne0F : (st.length != 0) = false := Bool.eq_false_iff.mpr hne0
        obtain ⟨h3, hsync, hp3, hd3, hmr3, he3, _, hcp3, _, _, _, _, _, _, hsrc3⟩ :=
          inputSync_parser hp2 st.nib st.bib hcurSt
        have hst03 := decompHeaderStable_trans hp hp2 hst02 (decompHeaderStable_of_same hd3 hmr3 hcp3)
        obtain ⟨hw, _⟩ := nibBibTrack_to_warnPotOk_src hp hp2 htrSt (by omega) he3 hsrc3
        have hstr := nibBibTrack_to_srcStrict hp hp2 htrSt hstrSt hsrc3
        refine ⟨.ok true, h3, ?_, hp3, hst03, ⟨hstr, ?_⟩⟩
        · unfold get_dht
          rw [C.run_bind, hldc]; dsimp only
          rw [ksrc, C.run_bind, hlsrc]; dsimp only
          rw [C.run_bind, hrun1]; dsimp only
          rw [C.run_bind]; erw [hloop]; dsimp only
          simp only [hdoneF, Bool.false_eq_true, ↓reduceIte, hne0F, C.run_bind, hsync]; rfl
        · intro e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
          obtain ⟨wf, wt⟩ := hw e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
          exact ⟨wf, fun ht => by have := wt ht; omega⟩

/-! ## `get_dqt` -/

private theorem int32_and15_bounds (x : Int32) :
    0 ≤ (x &&& (0x0F : Int32)).toInt ∧ (x &&& (0x0F : Int32)).toInt ≤ 15 := by
  have h15 : ((0x0F : Int32).toBitVec) = 15#32 := rfl
  have hnat : (x &&& (0x0F : Int32)).toBitVec.toNat < 16 := by
    change (x.toBitVec &&& (0x0F : Int32).toBitVec).toNat < 16
    rw [h15, BitVec.toNat_and]
    exact Nat.and_lt_two_pow x.toBitVec.toNat (by decide : (15 : Nat) < 2 ^ 4)
  have hEq : (x &&& (0x0F : Int32)).toInt = ((x &&& (0x0F : Int32)).toBitVec.toNat : Int) := by
    rw [Int32.toInt, BitVec.toInt_eq_toNat_cond]
    simp only [show 2 * (x &&& (0x0F : Int32)).toBitVec.toNat < 2 ^ 32 from by omega, ↓reduceIte]
  omega

theorem get_dqt_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63) :
    ∃ res h',
      C.run (get_dqt (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcStrict srcs0[0]! srcs'[0]!) ∧
        WarnPotOk ctx h h' 65664
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
    unfold get_dqt
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
    let Inv (k : Nat) (hCur : C.Heap) (s : DqtLoopState) : Prop :=
      ParserEnv ctx hCur ∧
      DecompHeaderStable ctx h hCur ∧
      (s.done = true → s.ret ≠ .ok true) ∧
      (!s.done →
        -128 ≤ s.length.toInt ∧ s.length.toInt ≤ 65533 ∧
        k = (if s.length.toInt ≤ 0 then 0 else s.length.toInt.toNat + 1) ∧
        CurValid hCur s.nib s.bib ∧
        NibBibTrack ctx h hCur s.nib s.bib (-8) (2 + (65533 - s.length.toInt)) ∧
        (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          isConstEofPtr s.nib = true ∨ s.bib.toNat < srcs0[0]!.bytesInBuffer.toNat))
    let Post (hCur : C.Heap) (s : DqtLoopState) : Prop :=
      ParserEnv ctx hCur ∧
      DecompHeaderStable ctx h hCur ∧
      (s.done = true → s.ret ≠ .ok true) ∧
      (!s.done →
        s.length.toInt ≤ 0 ∧ -128 ≤ s.length.toInt ∧
        CurValid hCur s.nib s.bib ∧
        NibBibTrack ctx h hCur s.nib s.bib (-8) 65664 ∧
        (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          isConstEofPtr s.nib = true ∨ s.bib.toNat < srcs0[0]!.bytesInBuffer.toNat))
    let s0 : DqtLoopState := { done := false, ret := .ok true, length := initLen, nib := nib1, bib := bib1 }
    let k0 : Nat := if initLen.toInt ≤ 0 then 0 else initLen.toInt.toNat + 1
    have hinit : Inv k0 h1 s0 := by
      refine ⟨hp1, hst01, (fun hno => by simp [s0] at hno), fun _ => ⟨by rw [hinitLen]; omega, by rw [hinitLen]; omega, rfl, hcur1,
        nibBibTrack_mono htr1 (by omega) (by rw [hinitLen]; omega), hstr1⟩⟩
    have hk0Lt : k0 < C.fuel := by unfold C.fuel; dsimp only [k0]; split <;> omega
    obtain ⟨st, h2, hloop, hpost⟩ :=
      cwhile_terminates
        (fun (s : DqtLoopState) => pure (!s.done && s.length > 0, s))
        (fun (s : DqtLoopState) => do
          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
          | none => return { s with done := true, ret := .ok false }
          | some (nRaw, nibA, bibA) =>
            let prec := nRaw >>> 4
            let n := nRaw &&& 0x0F
            let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            tracems2 dcCur.err 1 JTRC_DQT n prec
            if n ≥ NUM_QUANT_TBLS then
              let _ ← errexit1 dcCur.err JERR_DQT_INDEX n
              return { s with done := true, ret := .errExit JERR_DQT_INDEX }
            let nNat := n.toInt.toNat
            let qPtr ←
              if dcCur.quantTblPtrs[nNat]! == .null then
                match (← jpeg_alloc_quant_table (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
                | .errExit code => return { s with done := true, ret := .errExit code }
                | .ok p =>
                  let dcU ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                  Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcU with quantTblPtrs := dcU.quantTblPtrs.set! nNat p }
                  pure p
              else
                pure dcCur.quantTblPtrs[nNat]!
            let mut qTbl ← Ptr.load qPtr
            let mut qvals := qTbl.quantval
            let mut curNib := nibA
            let mut curBib := bibA
            let mut susp := false
            for i in List.range DCTSIZE2.toInt.toNat do
              if !susp then
                let res ←
                  if prec != 0 then input2Bytes (.ref (C.DecompRef.decomp ctx.bdc) 0) curNib curBib
                  else inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) curNib curBib
                match res with
                | none => susp := true
                | some (tmp, n', bi') =>
                  let z := jpeg_natural_order[i]!.toInt.toNat
                  qvals := qvals.set! z (UInt16.ofNat tmp.toInt.toNat)
                  curNib := n'
                  curBib := bi'
            if susp then
              return { s with done := true, ret := .ok false }
            Ptr.store qPtr { qTbl with quantval := qvals }
            let dcErr ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            let err ← Ptr.load dcErr.err
            if err.traceLevel ≥ 2 then
              for row in List.range 8 do
                let i := row * 8
                tracems8 dcErr.err 2 JTRC_QUANTVALS
                  (Int32.ofNat qvals[i]!.toNat) (Int32.ofNat qvals[i + 1]!.toNat)
                  (Int32.ofNat qvals[i + 2]!.toNat) (Int32.ofNat qvals[i + 3]!.toNat)
                  (Int32.ofNat qvals[i + 4]!.toNat) (Int32.ofNat qvals[i + 5]!.toNat)
                  (Int32.ofNat qvals[i + 6]!.toNat) (Int32.ofNat qvals[i + 7]!.toNat)
            let step := if prec != 0 then DCTSIZE2.toInt * 2 + 1 else DCTSIZE2.toInt + 1
            let len' := Int64.ofInt (s.length.toInt - step)
            return { done := false, ret := .ok true, length := len', nib := curNib, bib := curBib })
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
            have hsgt0 : 0 < s.length.toInt := by
              have hlt := Int64.lt_iff_toInt_lt.mp hsgt
              rw [show (0 : Int64).toInt = 0 from rfl] at hlt
              exact hlt
            obtain ⟨hsle128, hslenHi, hkEq, hcurS, htrS, _⟩ := hactive (by simp [hdoneF])
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
              rcases pA with ⟨nRaw, nibA, bibA⟩
              rcases hpostA with ⟨_, _, hcurA, hceA⟩
              obtain ⟨htrA, hstrA⟩ := nibBibTrack_inputByte_step hp hpC htrS (by omega) (by omega) hceA
              let prec := nRaw >>> 4
              let n := nRaw &&& 0x0F
              obtain ⟨hnLo, _⟩ := int32_and15_bounds nRaw
              obtain ⟨dcsA, hgdcA, hszdcA, kerrA, _, _, _, _, _⟩ := parserEnv_get_dc hpA
              have hldcA := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcA hszdcA
              obtain ⟨hT, htrT_run, hpT, hdT, hmrT, _, _, hcpT, _, _, _, hbyT, _, hcoT, hnwT⟩ :=
                tracems2_nonneg_parser hpA 1 JTRC_DQT n prec (by decide)
              have htrT_run' : C.run (tracems2 dcsA[0]!.err 1 JTRC_DQT n prec) hA = .ok ((), hT) := by
                rw [kerrA]; exact htrT_run
              have hstCT := decompHeaderStable_trans hp hpA hstCA (decompHeaderStable_of_same hdT hmrT hcpT)
              have htrT := nibBibTrack_err_nw_same hpA htrA hnwT
              have hcurT : CurValid hT nibA bibA := curValid_bytes_irrel hbyT hcoT hcurA
              by_cases hbadIdx : n ≥ NUM_QUANT_TBLS
              · obtain ⟨dcsT, _, _, kerrT, _⟩ := parserEnv_get_dc hpT
                obtain ⟨hE, herr_run, hpE, hstTE⟩ := errexit1_stable_parser hpT JERR_DQT_INDEX n
                have herr_run' : C.run (errexit1 dcsA[0]!.err JERR_DQT_INDEX n) hT = .ok (.errExit JERR_DQT_INDEX, hE) := by
                  have herrEq : dcsA[0]!.err = .ref ctx.rerr 0 := kerrA
                  rw [herrEq]; exact herr_run
                refine ⟨0, { s with done := true, ret := .errExit JERR_DQT_INDEX }, hE, ?_, ?_, hpE,
                  decompHeaderStable_trans hp hpT hstCT hstTE, (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                · rw [C.run_bind, hrunA]; dsimp only
                  rw [C.run_bind, hldcA]; dsimp only
                  rw [C.run_bind, htrT_run']; dsimp only
                  dsimp only [n, prec] at hbadIdx herr_run'
                  simp only [hbadIdx, ↓reduceIte, C.run_bind, herr_run']; rfl
                · simp only [hkEq, show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]; omega
              · have hnLt4 : n.toInt < 4 := by
                  have h4 : NUM_QUANT_TBLS.toInt = 4 := by decide
                  have := Int32.lt_iff_toInt_lt.mp (Int32.not_le.mp hbadIdx)
                  omega
                let nNat := n.toInt.toNat
                have hnNatLt4 : nNat < 4 := by omega
                let step : Int := if prec != 0 then DCTSIZE2.toInt * 2 + 1 else DCTSIZE2.toInt + 1
                have hstepDef : step = (if prec != 0 then 129 else 65) := rfl
                let len' : Int64 := Int64.ofInt (s.length.toInt - step)
                have hlen'To : len'.toInt = s.length.toInt - step := by
                  change (Int64.ofInt (s.length.toInt - step)).toInt = s.length.toInt - step
                  rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
                  exact Int.bmod_eq_of_le (by omega) (by omega)
                have hlen'Lo : -128 ≤ len'.toInt := by omega
                have hlen'Hi : len'.toInt ≤ 65533 := by omega
                let k' : Nat := if len'.toInt ≤ 0 then 0 else len'.toInt.toNat + 1
                have hkLt : k' < k := by
                  dsimp only [k']; rw [hkEq]
                  simp only [show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]
                  split <;> omega
                have hrunQ : ∀ (qPtr : C.QuantPtr) hQ (hpQ : ParserEnv ctx hQ) (hstCQ : DecompHeaderStable ctx h hQ)
                    (htrQ : NibBibTrack ctx h hQ nibA bibA (-8) (2 + (65533 - s.length.toInt) + 1))
                    (hcurQ : CurValid hQ nibA bibA)
                    (hstrQ : ∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
                      isConstEofPtr nibA = true ∨ bibA.toNat < srcs0[0]!.bytesInBuffer.toNat)
                    (hqLive : ∃ rq off qs, qPtr = .ref rq off ∧ C.Space.get hQ rq = some qs ∧ off < qs.size),
                    ∃ kNext stNext hDone,
                      C.run (do
                        let mut qTbl ← Ptr.load qPtr
                        let mut qvals := qTbl.quantval
                        let mut curNib := nibA
                        let mut curBib := bibA
                        let mut susp := false
                        for i in List.range DCTSIZE2.toInt.toNat do
                          if !susp then
                            let res ←
                              if prec != 0 then input2Bytes (.ref (C.DecompRef.decomp ctx.bdc) 0) curNib curBib
                              else inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) curNib curBib
                            match res with
                            | none => susp := true
                            | some (tmp, n', bi') =>
                              let z := jpeg_natural_order[i]!.toInt.toNat
                              qvals := qvals.set! z (UInt16.ofNat tmp.toInt.toNat)
                              curNib := n'
                              curBib := bi'
                        if susp then
                          return { s with done := true, ret := .ok false }
                        Ptr.store qPtr { qTbl with quantval := qvals }
                        let dcErr ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                        let err ← Ptr.load dcErr.err
                        if err.traceLevel ≥ 2 then
                          for row in List.range 8 do
                            let i := row * 8
                            tracems8 dcErr.err 2 JTRC_QUANTVALS
                              (Int32.ofNat qvals[i]!.toNat) (Int32.ofNat qvals[i + 1]!.toNat)
                              (Int32.ofNat qvals[i + 2]!.toNat) (Int32.ofNat qvals[i + 3]!.toNat)
                              (Int32.ofNat qvals[i + 4]!.toNat) (Int32.ofNat qvals[i + 5]!.toNat)
                              (Int32.ofNat qvals[i + 6]!.toNat) (Int32.ofNat qvals[i + 7]!.toNat)
                        let step := if prec != 0 then DCTSIZE2.toInt * 2 + 1 else DCTSIZE2.toInt + 1
                        let len' := Int64.ofInt (s.length.toInt - step)
                        return { done := false, ret := .ok true, length := len', nib := curNib, bib := curBib }) hQ =
                        .ok (stNext, hDone) ∧
                      kNext < k ∧ Inv kNext hDone stNext := by
                  intro qPtr hQ hpQ hstCQ htrQ hcurQ hstrQ ⟨rq, off, qs, hqpEq, hgQ, hoffQ⟩
                  subst hqpEq
                  have hlQ := ptr_load_ok (r := rq) (off := off) hgQ hoffQ
                  let perB : Int := if prec != 0 then 2 else 1
                  let Inv1 (i : Nat) (s1 : Array UInt16 × C.BPtr × UInt64 × Bool) (hC1 : C.Heap) : Prop :=
                    ParserEnv ctx hC1 ∧
                    DecompHeaderStable ctx h hC1 ∧
                    hC1.quants = hQ.quants ∧
                    (!s1.2.2.2 →
                      CurValid hC1 s1.2.1 s1.2.2.1 ∧
                      NibBibTrack ctx h hC1 s1.2.1 s1.2.2.1 (-8)
                        (2 + (65533 - s.length.toInt) + 1 + (i : Int) * perB) ∧
                      (∀ srcs0, C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
                        isConstEofPtr s1.2.1 = true ∨ s1.2.2.1.toNat < srcs0[0]!.bytesInBuffer.toNat))
                  let s1Init : Array UInt16 × C.BPtr × UInt64 × Bool := (qs[off]!.quantval, nibA, bibA, false)
                  have hInv1_0 : Inv1 0 s1Init hQ :=
                    ⟨hpQ, hstCQ, rfl, fun _ => ⟨hcurQ, nibBibTrack_mono htrQ (by omega) (by omega), hstrQ⟩⟩
                  have h64 : DCTSIZE2.toInt.toNat = 64 := by decide
                  obtain ⟨s1Fin, h1F, hfor1, hInv1Fin⟩ := forIn_range_inv Inv1
                    (fun (i : Nat) (s1 : Array UInt16 × C.BPtr × UInt64 × Bool) => do
                      if !s1.2.2.2 then
                        let res ←
                          if prec != 0 then input2Bytes (.ref (C.DecompRef.decomp ctx.bdc) 0) s1.2.1 s1.2.2.1
                          else inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s1.2.1 s1.2.2.1
                        match res with
                        | none => return .yield (s1.1, s1.2.1, s1.2.2.1, true)
                        | some (tmp, n', bi') =>
                          let z := jpeg_natural_order[i]!.toInt.toNat
                          return .yield (s1.1.set! z (UInt16.ofNat tmp.toInt.toNat), n', bi', s1.2.2.2)
                      else
                        return .yield s1)
                    DCTSIZE2.toInt.toNat
                    (fun i hi s1 hC1 ⟨hp1c, hst1c, hq1c, hact1⟩ => by
                      have hi64 : i < 64 := h64 ▸ hi
                      by_cases hns : (!s1.2.2.2) = true
                      · have hsF : s1.2.2.2 = false := by cases hc : s1.2.2.2 <;> simp_all
                        obtain ⟨hcur1s, htr1s, hstr1s⟩ := hact1 (by simp [hsF])
                        have hbd1 : ∀ errs, C.Space.get hC1 ctx.rerr = some errs → 0 < errs.size →
                            errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
                          nibBibTrack_bd hp hp1c htr1s (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                            have := hhead e0 s0 he0 hse0 hs0 hss0; dsimp [perB]; split <;> omega)
                        by_cases hpr : (prec != 0) = true
                        · have hprB : perB = 2 := by simp [perB, hpr]
                          rw [hprB] at htr1s
                          obtain ⟨res1b, h1b, hrun1b, hp1b, hd1b, hmr1b, _, hcp1b, hq1b, _, _, _, _, _, hpost1b⟩ :=
                            input2Bytes_parser hp1c s1.2.1 s1.2.2.1 hcur1s hbd1
                          have hstC1b := decompHeaderStable_trans hp hp1c hst1c (decompHeaderStable_of_same hd1b hmr1b hcp1b)
                          cases res1b with
                          | none =>
                            refine ⟨.yield (s1.1, s1.2.1, s1.2.2.1, true), h1b, ?_, hp1b, hstC1b, hq1b.trans hq1c,
                              fun hno => by simp at hno⟩
                            simp only [hns, ↓reduceIte, hpr, C.run_bind, hrun1b]; rfl
                          | some p1b =>
                            rcases p1b with ⟨tmp, n', bi'⟩
                            rcases hpost1b with ⟨_, _, hcur1b, hce1b⟩
                            obtain ⟨htr1b, hstr1b⟩ := nibBibTrack_input2Bytes_step hp hp1c htr1s (by omega) (by omega) hce1b
                            refine ⟨.yield (s1.1.set! (jpeg_natural_order[i]!.toInt.toNat) (UInt16.ofNat tmp.toInt.toNat), n', bi', s1.2.2.2),
                              h1b, ?_, hp1b, hstC1b, hq1b.trans hq1c, fun _ => ?_⟩
                            · simp only [hns, ↓reduceIte, hpr, C.run_bind, hrun1b]; rfl
                            · refine ⟨hcur1b, nibBibTrack_mono htr1b (by omega) ?_, hstr1b⟩
                              rw [hprB, show ((i + 1 : Nat) : Int) = (i : Int) + 1 from by omega]; omega
                        · have hprF : (prec != 0) = false := Bool.eq_false_iff.mpr hpr
                          have hprB : perB = 1 := by simp [perB, hprF]
                          rw [hprB] at htr1s
                          obtain ⟨res1b, h1b, hrun1b, hp1b, hd1b, hmr1b, _, hcp1b, hq1b, _, _, _, _, _, hpost1b⟩ :=
                            inputByte_parser hp1c s1.2.1 s1.2.2.1 hcur1s (fun _ errs hg hsz => by have := hbd1 errs hg hsz; omega)
                          have hstC1b := decompHeaderStable_trans hp hp1c hst1c (decompHeaderStable_of_same hd1b hmr1b hcp1b)
                          cases res1b with
                          | none =>
                            refine ⟨.yield (s1.1, s1.2.1, s1.2.2.1, true), h1b, ?_, hp1b, hstC1b, hq1b.trans hq1c,
                              fun hno => by simp at hno⟩
                            simp only [hns, ↓reduceIte, hprF, Bool.false_eq_true, C.run_bind, hrun1b]; rfl
                          | some p1b =>
                            rcases p1b with ⟨tmp, n', bi'⟩
                            rcases hpost1b with ⟨_, _, hcur1b, hce1b⟩
                            obtain ⟨htr1b, hstr1b⟩ := nibBibTrack_inputByte_step hp hp1c htr1s (by omega) (by omega) hce1b
                            refine ⟨.yield (s1.1.set! (jpeg_natural_order[i]!.toInt.toNat) (UInt16.ofNat tmp.toInt.toNat), n', bi', s1.2.2.2),
                              h1b, ?_, hp1b, hstC1b, hq1b.trans hq1c, fun _ => ?_⟩
                            · simp only [hns, ↓reduceIte, hprF, Bool.false_eq_true, C.run_bind, hrun1b]; rfl
                            · refine ⟨hcur1b, nibBibTrack_mono htr1b (by omega) ?_, hstr1b⟩
                              rw [hprB, show ((i + 1 : Nat) : Int) = (i : Int) + 1 from by omega]; omega
                      · have hsT : (!s1.2.2.2) = false := by cases hc : (!s1.2.2.2) <;> simp_all
                        refine ⟨.yield s1, hC1, ?_, hp1c, hst1c, hq1c, fun hno => by simp [hsT] at hno⟩
                        simp only [hsT, Bool.false_eq_true, ↓reduceIte]; rfl)
                    hInv1_0
                  rcases hInv1Fin with ⟨hp1F, hstC1F, hq1F, hact1F⟩
                  by_cases hsusp : s1Fin.2.2.2 = true
                  · refine ⟨0, { s with done := true, ret := .ok false }, h1F, ?_, ?_, hp1F, hstC1F,
                      (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                    · rw [C.run_bind, hlQ]; dsimp only
                      rw [C.run_bind]; erw [hfor1]; dsimp only
                      simp only [hsusp, ↓reduceIte]; rfl
                    · simp only [hkEq, show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]; omega
                  · have hsuspF : s1Fin.2.2.2 = false := Bool.eq_false_iff.mpr hsusp
                    obtain ⟨hcur1F, htr1F, hstr1F⟩ := hact1F (by simp [hsuspF])
                    have hg1F : C.Space.get h1F rq = some qs := by
                      simpa [C.Space.get, hq1F] using hgQ
                    have hroQ : C.Space.ro h1F rq = false := by cases rq; rfl
                    let qNew : C.JQuantTbl := { qs[off]! with quantval := s1Fin.1 }
                    have hstQ := ptr_store_ok (r := rq) (off := off) (v := qNew) hg1F hroQ hoffQ
                    let h2Q := C.Space.put h1F rq (qs.set! off qNew)
                    have hp2Q : ParserEnv ctx h2Q := parserEnv_put_quant hp1F hg1F
                    have hd2Q : h2Q.decomps = h1F.decomps := by cases rq; rfl
                    have hm2Q : h2Q.markers = h1F.markers := by cases rq; rfl
                    have hc2Q : h2Q.comps = h1F.comps := by cases rq; rfl
                    have hstC2Q := decompHeaderStable_trans hp hp1F hstC1F (decompHeaderStable_of_same hd2Q hm2Q hc2Q)
                    have hby2Q : h2Q.bytes = h1F.bytes := by cases rq; rfl
                    have hco2Q : h2Q.consts = h1F.consts := by cases rq; rfl
                    have he2Q : h2Q.errMgrs = h1F.errMgrs := by cases rq; rfl
                    have hcur2Q : CurValid h2Q s1Fin.2.1 s1Fin.2.2.1 := curValid_bytes_irrel hby2Q hco2Q hcur1F
                    have htr2Q : NibBibTrack ctx h h2Q s1Fin.2.1 s1Fin.2.2.1 (-8) (2 + (65533 - len'.toInt)) := by
                      have heqStep : 2 + (65533 - s.length.toInt) + 1 + ((64 : Nat) : Int) * perB = 2 + (65533 - len'.toInt) := by
                        rw [hlen'To, hstepDef]; dsimp [perB]; split <;> omega
                      rw [← heqStep]
                      exact nibBibTrack_err_same (h64 ▸ htr1F) he2Q
                    obtain ⟨dcs2Q, hgdc2Q, hszdc2Q, kerr2Q, _⟩ := parserEnv_get_dc hp2Q
                    obtain ⟨errs2Q, hgerr2Q, hszerr2Q, _⟩ := parserEnv_get_err hp2Q
                    have hldc2Q := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc2Q hszdc2Q
                    have hlerr2Q := ptr_load_ok (r := ctx.rerr) (off := 0) hgerr2Q hszerr2Q
                    by_cases htrLvl : errs2Q[0]!.traceLevel ≥ 2
                    · let InvT (_row : Nat) (u : PUnit) (hCT : C.Heap) : Prop :=
                        u = PUnit.unit ∧ ParserEnv ctx hCT ∧ DecompHeaderStable ctx h hCT ∧
                        CurValid hCT s1Fin.2.1 s1Fin.2.2.1 ∧
                        NibBibTrack ctx h hCT s1Fin.2.1 s1Fin.2.2.1 (-8) (2 + (65533 - len'.toInt))
                      obtain ⟨_uFin, hTF, hforT, hInvTF⟩ := forIn_range_inv InvT
                        (fun (row : Nat) (_u : PUnit) => do
                          let i := row * 8
                          tracems8 (Ptr.ref ctx.rerr 0) 2 JTRC_QUANTVALS
                            (Int32.ofNat s1Fin.1[i]!.toNat) (Int32.ofNat s1Fin.1[i + 1]!.toNat)
                            (Int32.ofNat s1Fin.1[i + 2]!.toNat) (Int32.ofNat s1Fin.1[i + 3]!.toNat)
                            (Int32.ofNat s1Fin.1[i + 4]!.toNat) (Int32.ofNat s1Fin.1[i + 5]!.toNat)
                            (Int32.ofNat s1Fin.1[i + 6]!.toNat) (Int32.ofNat s1Fin.1[i + 7]!.toNat)
                          return .yield PUnit.unit)
                        8
                        (fun row _hrow _u hCT ⟨_, hpCT, hstCT', hcurCT, htrCT'⟩ => by
                          obtain ⟨hCT', htrCT'_run, hpCT', hdCT', hmrCT', _, _, hcpCT', _, _, _, hbyCT', _, hcoCT', hnwCT'⟩ :=
                            tracems8_nonneg_parser hpCT 2 JTRC_QUANTVALS
                              (Int32.ofNat s1Fin.1[row * 8]!.toNat) (Int32.ofNat s1Fin.1[row * 8 + 1]!.toNat)
                              (Int32.ofNat s1Fin.1[row * 8 + 2]!.toNat) (Int32.ofNat s1Fin.1[row * 8 + 3]!.toNat)
                              (Int32.ofNat s1Fin.1[row * 8 + 4]!.toNat) (Int32.ofNat s1Fin.1[row * 8 + 5]!.toNat)
                              (Int32.ofNat s1Fin.1[row * 8 + 6]!.toNat) (Int32.ofNat s1Fin.1[row * 8 + 7]!.toNat) (by decide)
                          refine ⟨.yield PUnit.unit, hCT', ?_, rfl, hpCT',
                            decompHeaderStable_trans hp hpCT hstCT' (decompHeaderStable_of_same hdCT' hmrCT' hcpCT'),
                            curValid_bytes_irrel hbyCT' hcoCT' hcurCT, nibBibTrack_err_nw_same hpCT htrCT' hnwCT'⟩
                          rw [C.run_bind, htrCT'_run]; rfl)
                        ⟨rfl, hp2Q, hstC2Q, hcur2Q, htr2Q⟩
                      rcases hInvTF with ⟨_, hpTF, hstCTF, hcurTF, htrTF⟩
                      refine ⟨k', { done := false, ret := .ok true, length := len', nib := s1Fin.2.1, bib := s1Fin.2.2.1 },
                        hTF, ?_, hkLt, hpTF, hstCTF, (fun hno => by simp at hno),
                        fun _ => ⟨hlen'Lo, hlen'Hi, rfl, hcurTF, htrTF, hstr1F⟩⟩
                      rw [C.run_bind, hlQ]; dsimp only
                      rw [C.run_bind]; erw [hfor1]; dsimp only
                      simp only [hsuspF, Bool.false_eq_true, ↓reduceIte]
                      rw [C.run_bind, hstQ]; dsimp only
                      rw [C.run_bind, hldc2Q]; dsimp only
                      rw [kerr2Q, C.run_bind, hlerr2Q]; dsimp only
                      simp only [htrLvl, ↓reduceIte]
                      rw [C.run_bind]; erw [hforT]; rfl
                    · refine ⟨k', { done := false, ret := .ok true, length := len', nib := s1Fin.2.1, bib := s1Fin.2.2.1 },
                        h2Q, ?_, hkLt, hp2Q, hstC2Q, (fun hno => by simp at hno),
                        fun _ => ⟨hlen'Lo, hlen'Hi, rfl, hcur2Q, htr2Q, hstr1F⟩⟩
                      rw [C.run_bind, hlQ]; dsimp only
                      rw [C.run_bind]; erw [hfor1]; dsimp only
                      simp only [hsuspF, Bool.false_eq_true, ↓reduceIte]
                      rw [C.run_bind, hstQ]; dsimp only
                      rw [C.run_bind, hldc2Q]; dsimp only
                      rw [kerr2Q, C.run_bind, hlerr2Q]; dsimp only
                      simp only [htrLvl, ↓reduceIte]; rfl
                let qExisting := dcsA[0]!.quantTblPtrs[nNat]!
                by_cases hqNull : (qExisting == .null) = true
                · obtain ⟨resAlloc, hAlloc, hrunAlloc, hpAlloc, hresAlloc⟩ := jpeg_alloc_quant_table_parser hpT
                  cases resAlloc with
                  | errExit code =>
                    rcases hresAlloc with ⟨hdA, hmrA, hcpA⟩
                    refine ⟨0, { s with done := true, ret := .errExit code }, hAlloc, ?_, ?_, hpAlloc,
                      decompHeaderStable_trans hp hpT hstCT (decompHeaderStable_of_same hdA hmrA hcpA),
                      (fun _ hno => by cases hno), fun hno => by simp at hno⟩
                    · rw [C.run_bind, hrunA]; dsimp only
                      rw [C.run_bind, hldcA]; dsimp only
                      rw [C.run_bind, htrT_run']; dsimp only
                      dsimp only [n, prec, qExisting, nNat] at hbadIdx hqNull
                      simp only [hbadIdx, ↓reduceIte, hqNull, C.run_bind, hrunAlloc]; rfl
                    · simp only [hkEq, show ¬(s.length.toInt ≤ 0) from by omega, ↓reduceIte]; omega
                  | ok p =>
                    rcases hresAlloc with ⟨hpne, hdA, hmrA, hsrA, heA, hmaA, hcpA, _, hsmA, hbyA, hcoA, rq, off, qs, hpEq, hgQA, hoffQA⟩
                    obtain ⟨dcsA2, hgdcA2, hszdcA2, _⟩ := parserEnv_get_dc hpAlloc
                    have hldcA2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcA2 hszdcA2
                    have hroDcA2 : C.Space.ro hAlloc (C.DecompRef.decomp ctx.bdc) = false := rfl
                    let dcU' := { dcsA2[0]! with quantTblPtrs := dcsA2[0]!.quantTblPtrs.set! nNat p }
                    have hstDcU := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcU') hgdcA2 hroDcA2 hszdcA2
                    let h3 := C.Space.put hAlloc (C.DecompRef.decomp ctx.bdc) (dcsA2.set! 0 dcU')
                    have hstAlloc := decompHeaderStable_trans hp hpT hstCT (decompHeaderStable_of_same hdA hmrA hcpA)
                    have hp3 : ParserEnv ctx h3 :=
                      parserEnv_put_dc_quantTbl hpAlloc hgdcA2 hszdcA2 nNat hnNatLt4 p hpEq hgQA hoffQA
                    have hst3 : DecompHeaderStable ctx hAlloc h3 := by
                      refine ⟨?_, (fun m1 m2 ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
                        (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
                      intro da db hga _ hgb _
                      have ha := Option.some.inj (hga.symm.trans hgdcA2)
                      have hg3 : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcsA2.set! 0 dcU') := by
                        simp [h3, C.Space.get, C.Space.put]
                      have hb := Option.some.inj (hgb.symm.trans hg3)
                      rw [ha, hb, set0_bang_m dcsA2 hszdcA2 dcU']
                      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                    have hstC3 := decompHeaderStable_trans hp hpAlloc hstAlloc hst3
                    have hby3 : h3.bytes = hT.bytes := hbyA
                    have hco3 : h3.consts = hT.consts := hcoA
                    have he3 : h3.errMgrs = hT.errMgrs := heA
                    have htr3 := nibBibTrack_err_same htrT he3
                    have hcur3 : CurValid h3 nibA bibA := curValid_bytes_irrel hby3 hco3 hcurT
                    obtain ⟨kNext, stNext, hDone, hrunDone, hkNextLt, hInvNext⟩ :=
                      hrunQ p h3 hp3 hstC3 (nibBibTrack_mono htr3 (by omega) (by omega)) hcur3 hstrA ⟨rq, off, qs, hpEq, hgQA, hoffQA⟩
                    refine ⟨kNext, stNext, hDone, ?_, hkNextLt, hInvNext⟩
                    rw [C.run_bind, hrunA]; dsimp only
                    rw [C.run_bind, hldcA]; dsimp only
                    rw [C.run_bind, htrT_run']; dsimp only
                    dsimp only [n, prec, qExisting, nNat] at hbadIdx hqNull
                    simp only [hbadIdx, ↓reduceIte, hqNull]
                    rw [C.run_bind, hrunAlloc]; dsimp only
                    rw [C.run_bind, hldcA2]; dsimp only
                    rw [C.run_bind, hstDcU]; dsimp only
                    rw [C.run_bind]; dsimp only [C.run, pure]
                    exact hrunDone
                · have hqNullF : (qExisting == .null) = false := Bool.eq_false_iff.mpr hqNull
                  have hqNeNull : qExisting ≠ .null := fun heq => by simp [heq] at hqNullF
                  obtain ⟨dcsQ, hgQ0, _, _, hqPtrs⟩ := parserEnv_get_quant_ptr hpT hnNatLt4
                  have hgdcT : C.Space.get hT (C.DecompRef.decomp ctx.bdc) = some dcsA := by
                    simpa [C.Space.get, hdT] using hgdcA
                  have hdEq := Option.some.inj (hgdcT.symm.trans hgQ0)
                  have hqLive : ∃ rq off qs, qExisting = .ref rq off ∧ C.Space.get hT rq = some qs ∧ off < qs.size := by
                    rcases hqPtrs with hn | ⟨rq, off, qs, heq, hg, hoff⟩
                    · exact False.elim (hqNeNull (by dsimp [qExisting]; rw [hdEq, hn]))
                    · dsimp [qExisting]; rw [hdEq]; exact ⟨rq, off, qs, heq, hg, hoff⟩
                  obtain ⟨kNext, stNext, hDone, hrunDone, hkNextLt, hInvNext⟩ :=
                    hrunQ qExisting hT hpT hstCT (nibBibTrack_mono htrT (by omega) (by omega)) hcurT hstrA hqLive
                  refine ⟨kNext, stNext, hDone, ?_, hkNextLt, hInvNext⟩
                  rw [C.run_bind, hrunA]; dsimp only
                  rw [C.run_bind, hldcA]; dsimp only
                  rw [C.run_bind, htrT_run']; dsimp only
                  dsimp only [n, prec, qExisting, nNat] at hbadIdx hqNullF hrunDone
                  simp only [hbadIdx, ↓reduceIte, hqNullF, Bool.false_eq_true, C.run_bind]
                  dsimp only [C.run, pure]
                  exact hrunDone
          · have hcondF : (!s.done && s.length > 0) = false := by cases hc : (!s.done && s.length > 0) <;> simp_all
            refine ⟨false, s, hCur, (by simp only [C.run, pure, hcondF]), ?_⟩
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨hpC, hstC, hnrC, fun hnd => ?_⟩
            obtain ⟨hsle128, _, _, hcurS, htrS, hstrS⟩ := hactive hnd
            have hle0 : s.length.toInt ≤ 0 := by
              have hnotgt : ¬(s.length > 0) := by
                have hdF : s.done = false := by cases hd : s.done <;> simp_all
                intro hgt; simp [hdF, hgt] at hcondF
              by_cases hpos : s.length.toInt ≤ 0
              · exact hpos
              · exact False.elim (hnotgt (Int64.lt_iff_toInt_lt.mpr (by rw [show (0 : Int64).toInt = 0 from rfl]; omega)))
            exact ⟨hle0, hsle128, hcurS, nibBibTrack_mono htrS (by omega) (by omega), hstrS⟩)
        hk0Lt hinit
    rcases hpost with ⟨hp2, hst02, hnr2, hfin⟩
    dsimp only [s0, initLen] at hloop
    by_cases hdone : st.done = true
    · refine ⟨st.ret, h2, ?_, hp2, hst02, ?_⟩
      · unfold get_dqt
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
    · have hdoneF : st.done = false := Bool.eq_false_iff.mpr hdone
      obtain ⟨_, _, hcurSt, htrSt, hstrSt⟩ := hfin (by simp [hdoneF])
      by_cases hne0 : (st.length != 0) = true
      · obtain ⟨dcs2, hgdc2, hszdc2, kerr2, _⟩ := parserEnv_get_dc hp2
        obtain ⟨h_err, herr_run, hp_err, hstErr⟩ := errexit_stable_parser hp2 JERR_BAD_LENGTH
        have herr_run' : C.run (errexit dcs2[0]!.err JERR_BAD_LENGTH) h2 = .ok (.errExit JERR_BAD_LENGTH, h_err) := by
          rw [kerr2]; exact herr_run
        refine ⟨.errExit JERR_BAD_LENGTH, h_err, ?_, hp_err, decompHeaderStable_trans hp hp2 hst02 hstErr, trivial⟩
        unfold get_dqt
        rw [C.run_bind, hldc]; dsimp only
        rw [ksrc, C.run_bind, hlsrc]; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind]; erw [hloop]; dsimp only
        simp only [hdoneF, Bool.false_eq_true, ↓reduceIte, hne0, C.run_bind, herr_run',
          ptr_load_ok hgdc2 hszdc2]; rfl
      · have hne0F : (st.length != 0) = false := Bool.eq_false_iff.mpr hne0
        obtain ⟨h3, hsync, hp3, hd3, hmr3, he3, _, hcp3, _, _, _, _, _, _, hsrc3⟩ :=
          inputSync_parser hp2 st.nib st.bib hcurSt
        have hst03 := decompHeaderStable_trans hp hp2 hst02 (decompHeaderStable_of_same hd3 hmr3 hcp3)
        obtain ⟨hw, _⟩ := nibBibTrack_to_warnPotOk_src hp hp2 htrSt (by omega) he3 hsrc3
        have hstr := nibBibTrack_to_srcStrict hp hp2 htrSt hstrSt hsrc3
        refine ⟨.ok true, h3, ?_, hp3, hst03, ⟨hstr, ?_⟩⟩
        · unfold get_dqt
          rw [C.run_bind, hldc]; dsimp only
          rw [ksrc, C.run_bind, hlsrc]; dsimp only
          rw [C.run_bind, hrun1]; dsimp only
          rw [C.run_bind]; erw [hloop]; dsimp only
          simp only [hdoneF, Bool.false_eq_true, ↓reduceIte, hne0F, C.run_bind, hsync]; rfl
        · intro e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
          obtain ⟨wf, wt⟩ := hw e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
          exact ⟨wf, fun ht => by have := wt ht; omega⟩

/-! ## `get_sof` -/

private theorem parserEnv_put_dc_scalar {ctx : IoCtx} {h : C.Heap}
    {dcs : Array C.JpegDecompressStruct} (dc' : C.JpegDecompressStruct)
    (hp : ParserEnv ctx h) (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (kerr : dc'.err = dcs[0]!.err) (kmem : dc'.mem = dcs[0]!.mem) (kmas : dc'.master = dcs[0]!.master)
    (kic : dc'.inputctl = dcs[0]!.inputctl) (kmrk : dc'.marker = dcs[0]!.marker) (ksrc : dc'.src = dcs[0]!.src)
    (kml : dc'.markerList = dcs[0]!.markerList)
    (kcomp : dc'.compInfo = dcs[0]!.compInfo)
    (kcompNull : dc'.compInfo = .null)
    (kqt : dc'.quantTblPtrs = dcs[0]!.quantTblPtrs)
    (kdh : dc'.dcHuffTblPtrs = dcs[0]!.dcHuffTblPtrs)
    (kah : dc'.acHuffTblPtrs = dcs[0]!.acHuffTblPtrs)
    (kcc : dc'.curCompInfo = dcs[0]!.curCompInfo)
    (kisn : dc'.inputScanNumber = dcs[0]!.inputScanNumber) :
    ParserEnv ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) ∧
    CompSawZero ctx (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc')) := by
  have hp0 := hp
  obtain ⟨_, _, dcs0, dc0, _, _, _, _, mrks0, _,
    hgdc0, _, hdc0, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, hgmrk0, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, _, hsaw0, _, hqtSz, hqt, hdhSz, hdh, hahSz, hah, hccSz, hisn0⟩ := hp0
  have hdEq : dcs = dcs0 := Option.some.inj (hg.symm.trans hgdc0)
  subst hdEq; subst hdc0
  refine ⟨parserEnv_put_dc hp hg hsz kerr kmem kmas kic kmrk ksrc (Or.inl kml) (Or.inr (Or.inl kcompNull))
    ⟨kqt ▸ hqtSz, fun i hi => kqt ▸ hqt i hi⟩
    ⟨kdh ▸ hdhSz, fun i hi => kdh ▸ hdh i hi⟩
    ⟨kah ▸ hahSz, fun i hi => kah ▸ hah i hi⟩
    (kcc ▸ hccSz) (kisn ▸ hisn0)
    (fun mrks' hgmrk' _ hsawNe => by
      have hmEq := Option.some.inj (hgmrk'.symm.trans hgmrk0); subst hmEq
      exact kcomp ▸ hsaw0 hsawNe), ?_⟩
  intro mrks1 dcs1 hm1 _ hd1 hsz1 _
  have hd1Eq : dcs1 = dcs.set! 0 dc' := Option.some.inj (hd1.symm.trans (by simp [C.Space.get, C.Space.put]))
  rw [hd1Eq, set0_bang_m dcs hsz dc']
  exact kcompNull

private theorem parserEnv_put_mrk_sawSOF_true {ctx : IoCtx} {h : C.Heap}
    {mrks : Array C.JpegMarkerReader}
    (hp : ParserEnv ctx h) (hg : C.Space.get h ctx.rmrk = some mrks) (hsz : 0 < mrks.size)
    (hcompNN : ∀ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      dcs[0]!.compInfo ≠ .null) :
    let mrk' := { mrks[0]! with sawSOF := TRUE }
    ParserEnv ctx (C.Space.put h ctx.rmrk (mrks.set! 0 mrk')) ∧
    CompSawZero ctx (C.Space.put h ctx.rmrk (mrks.set! 0 mrk')) := by
  have hp0 := hp
  obtain ⟨_, _, _, _, _, _, _, _, mrks0, _,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, hgmrk0, _, hrm0, hrmr0, hpcom0, hpappSz0, hpapp0, hllSz0,
    _, _, _, _, _, _, _, _, _,
    hcurm0, _, _, _, _, _, _, _, _, _, _, _⟩ := hp0
  have hmEq : mrks = mrks0 := Option.some.inj (hg.symm.trans hgmrk0)
  subst hmEq
  intro mrk'
  refine ⟨parserEnv_put_mrk hp hg hsz rfl rfl rfl rfl hllSz0 hcurm0
    (fun dcs' hg' hsz' _ => hcompNN dcs' hg' hsz'), ?_⟩
  intro mrks1 dcs1 hm1 hszm1 _ _ hs0
  have hm1Eq : mrks1 = mrks.set! 0 mrk' := Option.some.inj (hm1.symm.trans (by simp [C.Space.get, C.Space.put]))
  rw [hm1Eq, set0_bang_m mrks hsz mrk'] at hs0
  have ht0 : (TRUE == 0) = false := by decide
  change (TRUE : Int32) = 0 at hs0
  rw [hs0] at ht0
  cases ht0

private theorem get_sof_loop_parser {ctx : IoCtx} {h0 h6 : C.Heap}
    (hp0 : ParserEnv ctx h0)
    (hhead : ∀ errs0 srcs0, C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63)
    (compP : C.CompPtr) (errRef : C.ErrPtr) (herrRef : errRef = .ref ctx.rerr 0)
    (nComps : Nat) (hnHi : nComps ≤ 255) (nib5 : C.BPtr) (bib5 : UInt64)
    (hp6 : ParserEnv ctx h6) (hLive6 : LiveCompArray h6 compP nComps)
    (hcur6 : CurValid h6 nib5 bib5) (htr6 : NibBibTrack ctx h0 h6 nib5 bib5 (-8) 8)
    (hstr5 : ∀ srcs, C.Space.get h0 ctx.rs = some srcs → 0 < srcs.size →
      isConstEofPtr nib5 = true ∨ bib5.toNat < srcs[0]!.bytesInBuffer.toNat) :
    ∃ st hL,
      C.run (cwhile
        (fun (s : SofLoopState) => pure (!s.done && s.ci < nComps, s))
        (fun (s : SofLoopState) => do
          let cp ← Ptr.add compP (Int.ofNat s.ci)
          let comp0 ← Ptr.load cp
          Ptr.store cp { comp0 with componentIndex := Int32.ofNat s.ci }
          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
          | none => return { s with done := true, ret := .ok false }
          | some (cid, nibA, bibA) =>
            let comp1 ← Ptr.load cp
            Ptr.store cp { comp1 with componentId := cid }
            match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
            | none => return { s with done := true, ret := .ok false }
            | some (cbyte, nibB, bibB) =>
              let comp2 ← Ptr.load cp
              Ptr.store cp {
                comp2 with
                hSampFactor := (cbyte >>> 4) &&& 15
                vSampFactor := cbyte &&& 15
              }
              match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibB bibB) with
              | none => return { s with done := true, ret := .ok false }
              | some (qno, nibC, bibC) =>
                let comp3 ← Ptr.load cp
                let comp4 := { comp3 with quantTblNo := qno }
                Ptr.store cp comp4
                tracems4 errRef 1 JTRC_SOF_COMPONENT
                  comp4.componentId comp4.hSampFactor comp4.vSampFactor comp4.quantTblNo
                return { done := false, ret := .ok true, ci := s.ci + 1, nib := nibC, bib := bibC })
        { done := false, ret := .ok true, ci := 0, nib := nib5, bib := bib5 }) h6 = .ok (st, hL) ∧
      ParserEnv ctx hL ∧
      hL.decomps = h6.decomps ∧
      (st.done = true → st.ret = .ok false) ∧
      (!st.done →
        CurValid hL st.nib st.bib ∧
        NibBibTrack ctx h0 hL st.nib st.bib (-8) 773 ∧
        (∀ srcs, C.Space.get h0 ctx.rs = some srcs → 0 < srcs.size →
          isConstEofPtr st.nib = true ∨ st.bib.toNat < srcs[0]!.bytesInBuffer.toNat)) := by
  subst herrRef
  let Inv (k : Nat) (hCur : C.Heap) (s : SofLoopState) : Prop :=
    ParserEnv ctx hCur ∧
    hCur.decomps = h6.decomps ∧
    LiveCompArray hCur compP nComps ∧
    (s.done = true → s.ret = .ok false) ∧
    (!s.done →
      s.ci ≤ nComps ∧ k = nComps - s.ci ∧
      CurValid hCur s.nib s.bib ∧
      NibBibTrack ctx h0 hCur s.nib s.bib (-8) (8 + (s.ci : Int) * 3) ∧
      (∀ srcs, C.Space.get h0 ctx.rs = some srcs → 0 < srcs.size →
        isConstEofPtr s.nib = true ∨ s.bib.toNat < srcs[0]!.bytesInBuffer.toNat))
  let Post (hCur : C.Heap) (s : SofLoopState) : Prop :=
    ParserEnv ctx hCur ∧
    hCur.decomps = h6.decomps ∧
    (s.done = true → s.ret = .ok false) ∧
    (!s.done →
      CurValid hCur s.nib s.bib ∧
      NibBibTrack ctx h0 hCur s.nib s.bib (-8) 773 ∧
      (∀ srcs, C.Space.get h0 ctx.rs = some srcs → 0 < srcs.size →
        isConstEofPtr s.nib = true ∨ s.bib.toNat < srcs[0]!.bytesInBuffer.toNat))
  let s0 : SofLoopState := { done := false, ret := .ok true, ci := 0, nib := nib5, bib := bib5 }
  have hinit : Inv nComps h6 s0 :=
    ⟨hp6, rfl, hLive6, (fun hno => by simp [s0] at hno),
      fun _ => ⟨Nat.zero_le _, rfl, hcur6, nibBibTrack_mono htr6 (by omega) (by omega), hstr5⟩⟩
  have hk0Lt : nComps < C.fuel := by unfold C.fuel; omega
  obtain ⟨st, hL, hloop, hpost⟩ :=
    cwhile_terminates
      (fun (s : SofLoopState) => pure (!s.done && s.ci < nComps, s))
      (fun (s : SofLoopState) => do
        let cp ← Ptr.add compP (Int.ofNat s.ci)
        let comp0 ← Ptr.load cp
        Ptr.store cp { comp0 with componentIndex := Int32.ofNat s.ci }
        match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
        | none => return { s with done := true, ret := .ok false }
        | some (cid, nibA, bibA) =>
          let comp1 ← Ptr.load cp
          Ptr.store cp { comp1 with componentId := cid }
          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
          | none => return { s with done := true, ret := .ok false }
          | some (cbyte, nibB, bibB) =>
            let comp2 ← Ptr.load cp
            Ptr.store cp {
              comp2 with
              hSampFactor := (cbyte >>> 4) &&& 15
              vSampFactor := cbyte &&& 15
            }
            match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibB bibB) with
            | none => return { s with done := true, ret := .ok false }
            | some (qno, nibC, bibC) =>
              let comp3 ← Ptr.load cp
              let comp4 := { comp3 with quantTblNo := qno }
              Ptr.store cp comp4
              tracems4 (.ref ctx.rerr 0) 1 JTRC_SOF_COMPONENT
                comp4.componentId comp4.hSampFactor comp4.vSampFactor comp4.quantTblNo
              return { done := false, ret := .ok true, ci := s.ci + 1, nib := nibC, bib := bibC })
      Inv Post
      (fun k hCur s ⟨hpC, hdC, hLiveC, hnrC, hactC⟩ => by
        by_cases hcond : (!s.done && s.ci < nComps) = true
        · refine ⟨true, s, hCur, by simp [hcond], ?_⟩
          simp only [↓reduceIte]
          have hdoneF : s.done = false := by cases hc : s.done <;> simp_all
          have hciLt : s.ci < nComps := by
            by_cases hlt : s.ci < nComps
            · exact hlt
            · simp [hdoneF, hlt] at hcond
          obtain ⟨_, hkEq, hcurS, htrS, _⟩ := hactC (by simp [hdoneF])
          rcases hLiveC with ⟨rcp, cs, hcpEq, hgC, hlenC⟩
          have hoffC : s.ci < cs.size := by omega
          have haddC : C.run (Ptr.add compP (Int.ofNat s.ci)) hCur = .ok (.ref rcp s.ci, hCur) := by
            have hadd0 := ptr_add_ok (r := rcp) (off := 0) (k := Int.ofNat s.ci) hgC
              (Nat.zero_le _) (by change (0 : Int) ≤ 0 + (s.ci : Int); omega)
              (by change (0 : Int) + (s.ci : Int) ≤ _; omega)
            have htn : (((0 : Nat) : Int) + Int.ofNat s.ci).toNat = s.ci := by
              change ((0 : Int) + (s.ci : Int)).toNat = s.ci
              rw [Int.zero_add]; rfl
            rw [htn] at hadd0
            rw [hcpEq]; exact hadd0
          have hlC0 := ptr_load_ok (r := rcp) (off := s.ci) hgC hoffC
          have hroC : C.Space.ro hCur rcp = false := by cases rcp; rfl
          let comp0' := { cs[s.ci]! with componentIndex := Int32.ofNat s.ci }
          have hstC0 := ptr_store_ok (r := rcp) (off := s.ci) (v := comp0') hgC hroC hoffC
          let hC0 := C.Space.put hCur rcp (cs.set! s.ci comp0')
          have hpC0 : ParserEnv ctx hC0 := parserEnv_put_comp hpC hgC
          have hcurC0 : CurValid hC0 s.nib s.bib := curValid_bytes_irrel (by cases rcp; rfl) (by cases rcp; rfl) hcurS
          have htrC0 := nibBibTrack_err_same htrS (by cases rcp; rfl : hC0.errMgrs = hCur.errMgrs)
          have hbdA : s.bib = 0 → ∀ errs, C.Space.get hC0 ctx.rerr = some errs → 0 < errs.size →
              errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
            nibBibTrack_bd hp0 hpC0 htrC0 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
              have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
          obtain ⟨resA, hA, hrunA, hpA, hdA, _, _, hcpA, _, _, _, _, _, _, hpostA⟩ :=
            inputByte_parser hpC0 s.nib s.bib hcurC0 hbdA
          cases resA with
          | none =>
            refine ⟨0, { s with done := true, ret := .ok false }, hA, ?_, ?_, hpA,
              hdA.trans (by cases rcp; exact hdC),
              ⟨rcp, cs.set! s.ci comp0', hcpEq,
                by cases rcp; dsimp only [C.Space.get]; rw [hcpA]; simp [hC0, C.Space.put],
                by simpa [Array.size_set!] using hlenC⟩,
              (fun _ => rfl), fun hno => by simp at hno⟩
            · rw [C.run_bind, haddC]; dsimp only
              rw [C.run_bind, hlC0]; dsimp only
              rw [C.run_bind, hstC0]; dsimp only
              rw [C.run_bind, hrunA]; rfl
            · omega
          | some pA =>
            rcases pA with ⟨cid, nibA, bibA⟩
            rcases hpostA with ⟨_, _, hcurA, hceA⟩
            obtain ⟨htrA, _⟩ := nibBibTrack_inputByte_step hp0 hpC0 htrC0 (by omega) (by omega) hceA
            have hgCA : C.Space.get hA rcp = some (cs.set! s.ci comp0') := by
              cases rcp; dsimp only [C.Space.get]; rw [hcpA]; simp [hC0, C.Space.put]
            have hoffA : s.ci < (cs.set! s.ci comp0').size := by simpa using hoffC
            have hlCA := ptr_load_ok (r := rcp) (off := s.ci) hgCA hoffA
            have hroCA : C.Space.ro hA rcp = false := by cases rcp; rfl
            let comp1' := { (cs.set! s.ci comp0')[s.ci]! with componentId := cid }
            have hstCA := ptr_store_ok (r := rcp) (off := s.ci) (v := comp1') hgCA hroCA hoffA
            let cs1 := (cs.set! s.ci comp0').set! s.ci comp1'
            let hA' := C.Space.put hA rcp cs1
            have hpA' : ParserEnv ctx hA' := parserEnv_put_comp hpA hgCA
            have hcurA' : CurValid hA' nibA bibA := curValid_bytes_irrel (by cases rcp; rfl) (by cases rcp; rfl) hcurA
            have htrA' := nibBibTrack_err_same htrA (by cases rcp; rfl : hA'.errMgrs = hA.errMgrs)
            have hbdB : bibA = 0 → ∀ errs, C.Space.get hA' ctx.rerr = some errs → 0 < errs.size →
                errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
              nibBibTrack_bd hp0 hpA' htrA' (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
            obtain ⟨resB, hB, hrunB, hpB, hdB, _, _, hcpB, _, _, _, _, _, _, hpostB⟩ :=
              inputByte_parser hpA' nibA bibA hcurA' hbdB
            cases resB with
            | none =>
              refine ⟨0, { s with done := true, ret := .ok false }, hB, ?_, ?_, hpB,
                hdB.trans (by cases rcp; exact hdA.trans hdC),
                ⟨rcp, cs1, hcpEq,
                  by cases rcp; dsimp only [C.Space.get]; rw [hcpB]; simp [hA', C.Space.put],
                  by simpa [cs1, Array.size_set!] using hlenC⟩,
                (fun _ => rfl), fun hno => by simp at hno⟩
              · rw [C.run_bind, haddC]; dsimp only
                rw [C.run_bind, hlC0]; dsimp only
                rw [C.run_bind, hstC0]; dsimp only
                rw [C.run_bind, hrunA]; dsimp only
                rw [C.run_bind, hlCA]; dsimp only
                rw [C.run_bind, hstCA]; dsimp only
                rw [C.run_bind, hrunB]; rfl
              · omega
            | some pB =>
              rcases pB with ⟨cbyte, nibB, bibB⟩
              rcases hpostB with ⟨_, _, hcurB, hceB⟩
              obtain ⟨htrB, _⟩ := nibBibTrack_inputByte_step hp0 hpA' htrA' (by omega) (by omega) hceB
              have hgCB : C.Space.get hB rcp = some cs1 := by
                cases rcp; dsimp only [C.Space.get]; rw [hcpB]; simp [hA', C.Space.put]
              have hoffB : s.ci < cs1.size := by simpa [cs1] using hoffC
              have hlCB := ptr_load_ok (r := rcp) (off := s.ci) hgCB hoffB
              have hroCB : C.Space.ro hB rcp = false := by cases rcp; rfl
              let comp2' := { cs1[s.ci]! with hSampFactor := (cbyte >>> 4) &&& 15, vSampFactor := cbyte &&& 15 }
              have hstCB := ptr_store_ok (r := rcp) (off := s.ci) (v := comp2') hgCB hroCB hoffB
              let cs2 := cs1.set! s.ci comp2'
              let hB' := C.Space.put hB rcp cs2
              have hpB' : ParserEnv ctx hB' := parserEnv_put_comp hpB hgCB
              have hcurB' : CurValid hB' nibB bibB := curValid_bytes_irrel (by cases rcp; rfl) (by cases rcp; rfl) hcurB
              have htrB' := nibBibTrack_err_same htrB (by cases rcp; rfl : hB'.errMgrs = hB.errMgrs)
              have hbdC : bibB = 0 → ∀ errs, C.Space.get hB' ctx.rerr = some errs → 0 < errs.size →
                  errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
                nibBibTrack_bd hp0 hpB' htrB' (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                  have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
              obtain ⟨resC, hC, hrunC, hpC2, hdC', _, _, hcpC', _, _, _, hbyC', _, hcoC', hpostC⟩ :=
                inputByte_parser hpB' nibB bibB hcurB' hbdC
              cases resC with
              | none =>
                refine ⟨0, { s with done := true, ret := .ok false }, hC, ?_, ?_, hpC2,
                  hdC'.trans (by cases rcp; exact hdB.trans (hdA.trans hdC)),
                  ⟨rcp, cs2, hcpEq,
                    by cases rcp; dsimp only [C.Space.get]; rw [hcpC']; simp [hB', C.Space.put],
                    by simpa [cs2, cs1, Array.size_set!] using hlenC⟩,
                  (fun _ => rfl), fun hno => by simp at hno⟩
                · rw [C.run_bind, haddC]; dsimp only
                  rw [C.run_bind, hlC0]; dsimp only
                  rw [C.run_bind, hstC0]; dsimp only
                  rw [C.run_bind, hrunA]; dsimp only
                  rw [C.run_bind, hlCA]; dsimp only
                  rw [C.run_bind, hstCA]; dsimp only
                  rw [C.run_bind, hrunB]; dsimp only
                  rw [C.run_bind, hlCB]; dsimp only
                  rw [C.run_bind, hstCB]; dsimp only
                  rw [C.run_bind, hrunC]; rfl
                · omega
              | some pC =>
                rcases pC with ⟨qno, nibC, bibC⟩
                rcases hpostC with ⟨_, _, hcurC, hceC⟩
                obtain ⟨htrC, hstrC⟩ := nibBibTrack_inputByte_step hp0 hpB' htrB' (by omega) (by omega) hceC
                have hgCC : C.Space.get hC rcp = some cs2 := by
                  cases rcp; dsimp only [C.Space.get]; rw [hcpC']; simp [hB', C.Space.put]
                have hoffC2 : s.ci < cs2.size := by simpa [cs2, cs1] using hoffC
                have hlCC := ptr_load_ok (r := rcp) (off := s.ci) hgCC hoffC2
                have hroCC : C.Space.ro hC rcp = false := by cases rcp; rfl
                let comp4 := { cs2[s.ci]! with quantTblNo := qno }
                have hstCC := ptr_store_ok (r := rcp) (off := s.ci) (v := comp4) hgCC hroCC hoffC2
                let cs3 := cs2.set! s.ci comp4
                let hC' := C.Space.put hC rcp cs3
                have hpC' : ParserEnv ctx hC' := parserEnv_put_comp hpC2 hgCC
                have hcurC' : CurValid hC' nibC bibC := curValid_bytes_irrel (by cases rcp; rfl) (by cases rcp; rfl) hcurC
                have htrC' := nibBibTrack_err_same htrC (by cases rcp; rfl : hC'.errMgrs = hC.errMgrs)
                obtain ⟨hTr, htrTr_run, hpTr, hdTr, _, _, _, hcpTr, _, _, _, hbyTr, _, hcoTr, hnwTr⟩ :=
                  tracems4_nonneg_parser hpC' 1 JTRC_SOF_COMPONENT
                    comp4.componentId comp4.hSampFactor comp4.vSampFactor comp4.quantTblNo (by decide)
                have htrTr' := nibBibTrack_err_nw_same hpC' htrC' hnwTr
                have hcurTr : CurValid hTr nibC bibC := curValid_bytes_irrel hbyTr hcoTr hcurC'
                have hdTr0 : hTr.decomps = h6.decomps :=
                  hdTr.trans (by cases rcp; exact hdC'.trans (hdB.trans (hdA.trans hdC)))
                have hLiveTr : LiveCompArray hTr compP nComps :=
                  ⟨rcp, cs3, hcpEq,
                    by cases rcp; dsimp only [C.Space.get]; rw [hcpTr]; simp [hC', C.Space.put],
                    by simpa [cs3, cs2, cs1, Array.size_set!] using hlenC⟩
                refine ⟨nComps - (s.ci + 1), { done := false, ret := .ok true, ci := s.ci + 1, nib := nibC, bib := bibC },
                  hTr, ?_, (by omega), hpTr, hdTr0, hLiveTr, (fun hno => by simp at hno), fun _ => ?_⟩
                · rw [C.run_bind, haddC]; dsimp only
                  rw [C.run_bind, hlC0]; dsimp only
                  rw [C.run_bind, hstC0]; dsimp only
                  rw [C.run_bind, hrunA]; dsimp only
                  rw [C.run_bind, hlCA]; dsimp only
                  rw [C.run_bind, hstCA]; dsimp only
                  rw [C.run_bind, hrunB]; dsimp only
                  rw [C.run_bind, hlCB]; dsimp only
                  rw [C.run_bind, hstCB]; dsimp only
                  rw [C.run_bind, hrunC]; dsimp only
                  rw [C.run_bind, hlCC]; dsimp only
                  rw [C.run_bind, hstCC]; dsimp only
                  rw [C.run_bind, htrTr_run]; rfl
                · dsimp only
                  refine ⟨by omega, rfl, hcurTr, nibBibTrack_mono htrTr' (by omega) ?_, hstrC⟩
                  rw [show ((s.ci + 1 : Nat) : Int) = (s.ci : Int) + 1 from by omega]; omega
        · have hcondF : (!s.done && s.ci < nComps) = false := by cases hc : (!s.done && s.ci < nComps) <;> simp_all
          refine ⟨false, s, hCur, (by simp only [C.run, pure, hcondF]), ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨hpC, hdC, hnrC, fun hnd => ?_⟩
          obtain ⟨_, _, hcurS, htrS, hstrS⟩ := hactC hnd
          exact ⟨hcurS, nibBibTrack_mono htrS (by omega) (by omega), hstrS⟩)
      hk0Lt hinit
  rcases hpost with ⟨hpL, hdL, hnrL, hfinL⟩
  exact ⟨st, hL, hloop, hpL, hdL, hnrL, hfinL⟩

theorem get_sof_parser {ctx : IoCtx} {h : C.Heap} (isProg isLossless isArith : Int32)
    (hp : ParserEnv ctx h) (hsaw0 : CompSawZero ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63) :
    ∃ res h',
      C.run (get_sof (.ref (.decomp ctx.bdc) 0) isProg isLossless isArith) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      (∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size → mrks[0]!.sawSOF ≠ 0 →
        DecompHeaderStable ctx h h') ∧
      match res with
      | .ok true =>
        CompSawZero ctx h' ∧
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcStrict srcs0[0]! srcs'[0]!) ∧
        WarnPotOk ctx h h' (2 ^ 16)
      | .errExit _ => CompSawZero ctx h'
      | .ok false => True := by
  obtain ⟨dcs0, hgdc0, hszdc0, kerr0, kmem0, kmas0, kic0, kmrk0, ksrc0⟩ := parserEnv_get_dc hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _, _, _, _, _, hcur0⟩ := parserEnv_get_src hp
  obtain ⟨mrks0, hgmrk0, hszmrk0, _⟩ := parserEnv_get_mrk hp
  obtain ⟨masters0, hgmas0, hszmas0⟩ := parserEnv_get_mas hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlsrc0 := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc0 hszsrc0
  have hlmrk0 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk0 hszmrk0
  by_cases hsawDup : (mrks0[0]!.sawSOF != 0) = true
  · have hsawNe0 : mrks0[0]!.sawSOF ≠ 0 := by simpa [bne] using hsawDup
    obtain ⟨hE, herr_run, hpE, hstE⟩ := errexit_stable_parser hp JERR_SOF_DUPLICATE
    have herr_run' : C.run (errexit dcs0[0]!.err JERR_SOF_DUPLICATE) h = .ok (.errExit JERR_SOF_DUPLICATE, hE) := by
      rw [kerr0]; exact herr_run
    refine ⟨.errExit JERR_SOF_DUPLICATE, hE, ?_, hpE, (fun _ _ _ _ => hstE), compSawZero_of_stable hsaw0 hstE hp⟩
    unfold get_sof
    rw [C.run_bind, hldc0]; dsimp only
    rw [ksrc0, C.run_bind, hlsrc0]; dsimp only
    rw [kmrk0, C.run_bind, hlmrk0]; dsimp only
    simp only [hsawDup, ↓reduceIte, C.run_bind, herr_run']; rfl
  · have hsawDupF : (mrks0[0]!.sawSOF != 0) = false := Bool.eq_false_iff.mpr hsawDup
    have hsawZ : mrks0[0]!.sawSOF = 0 := by
      by_cases hz : mrks0[0]!.sawSOF = 0
      · exact hz
      · have : (mrks0[0]!.sawSOF != 0) = true := by simp [bne, hz]
        rw [this] at hsawDupF; cases hsawDupF
    have hcompNull0 : dcs0[0]!.compInfo = .null := hsaw0 mrks0 dcs0 hgmrk0 hszmrk0 hgdc0 hszdc0 hsawZ
    have hroDc0 : C.Space.ro h (C.DecompRef.decomp ctx.bdc) = false := rfl
    let dc0' := { dcs0[0]! with progressiveMode := isProg, arithCode := isArith }
    have hst0' := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc0') hgdc0 hroDc0 hszdc0
    let h0' := C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs0.set! 0 dc0')
    obtain ⟨hp0', hsaw0'⟩ := parserEnv_put_dc_scalar dc0' hp hgdc0 hszdc0 rfl rfl rfl rfl rfl rfl rfl rfl
      hcompNull0 rfl rfl rfl rfl rfl
    have hlm0' : C.Space.get h0' ctx.rmas = some masters0 := hgmas0
    have hlmst := ptr_load_ok (r := ctx.rmas) (off := 0) hlm0' hszmas0
    have hroMst : C.Space.ro h0' ctx.rmas = false := rfl
    let mst0' := { masters0[0]! with lossless := isLossless }
    have hstMst := ptr_store_ok (r := ctx.rmas) (off := 0) (v := mst0') hlm0' hroMst hszmas0
    let h0'' := C.Space.put h0' ctx.rmas (masters0.set! 0 mst0')
    have hp0'' : ParserEnv ctx h0'' := parserEnv_put_mst hp0' hlm0' hszmas0 (Or.inl rfl)
    have hsaw0'' : CompSawZero ctx h0'' := by
      intro m d hm hszm hd hszd hs
      exact hsaw0' m d hm hszm hd hszd hs
    have hby0'' : h0''.bytes = h.bytes := rfl
    have hco0'' : h0''.consts = h.consts := rfl
    have he0'' : h0''.errMgrs = h.errMgrs := rfl
    have htr0 := nibBibTrack_init ctx h srcs0 hgsrc0
    have htr0'' := nibBibTrack_err_same htr0 he0''
    have hcur0'' : CurValid h0'' srcs0[0]!.nextInputByte srcs0[0]!.bytesInBuffer :=
      curValid_bytes_irrel hby0'' hco0'' hcur0
    have hbd0 : ∀ nrem : Int, nrem ≤ 8 →
        ∀ hX (trX : C.BPtr) (bibX : UInt64) (nwX : Int),
        ParserEnv ctx hX → NibBibTrack ctx h hX trX bibX (-8) nwX → nwX + nrem ≤ 8 →
        ∀ errs, C.Space.get hX ctx.rerr = some errs → 0 < errs.size →
          errs[0]!.numWarnings.toInt + nrem < 2 ^ 63 := fun nrem hnrem hX trX bibX nwX hpX htrX hnw =>
      nibBibTrack_bd hp hpX htrX (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
        have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
    have hstepByte : ∀ hX nibX bibX nwX (hpX : ParserEnv ctx hX) (hsawX : CompSawZero ctx hX)
        (htrX : NibBibTrack ctx h hX nibX bibX (-8) nwX) (hnw0 : 0 ≤ nwX) (hnw : nwX ≤ 7) (hcurX : CurValid hX nibX bibX),
        ∃ resY hY, C.run (inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibX bibX) hX = .ok (resY, hY) ∧
          ParserEnv ctx hY ∧ CompSawZero ctx hY ∧ hY.decomps = hX.decomps ∧ hY.markers = hX.markers ∧
          match resY with
          | none => True
          | some (b, nibY, bibY) =>
            0 ≤ b.toInt ∧ b.toInt ≤ 255 ∧ CurValid hY nibY bibY ∧
            NibBibTrack ctx h hY nibY bibY (-8) (nwX + 1) ∧
            (∀ srcs, C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
              isConstEofPtr nibY = true ∨ bibY.toNat < srcs[0]!.bytesInBuffer.toNat) := by
      intro hX nibX bibX nwX hpX hsawX htrX hnw0 hnw hcurX
      have hbdX : bibX = 0 → ∀ errs, C.Space.get hX ctx.rerr = some errs → 0 < errs.size →
          errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ => hbd0 1 (by omega) hX nibX bibX nwX hpX htrX (by omega)
      obtain ⟨resY, hY, hrunY, hpY, hdY, hmrY, _, _, _, _, _, _, _, _, hpostY⟩ :=
        inputByte_parser hpX nibX bibX hcurX hbdX
      have hsawY : CompSawZero ctx hY := fun m d hm hszm hd hszd hs =>
        hsawX m d (by dsimp only [C.Space.get] at hm ⊢; rw [hmrY] at hm; exact hm) hszm
          (by dsimp only [C.Space.get] at hd ⊢; rw [hdY] at hd; exact hd) hszd hs
      refine ⟨resY, hY, hrunY, hpY, hsawY, hdY, hmrY, ?_⟩
      cases resY with
      | none => trivial
      | some p =>
        rcases p with ⟨b, nibY, bibY⟩
        rcases hpostY with ⟨hb0, hbHi, hcurY, hceY⟩
        obtain ⟨htrY, hstrY⟩ := nibBibTrack_inputByte_step hp hpX htrX (by omega) hnw0 hceY
        exact ⟨hb0, hbHi, hcurY, nibBibTrack_mono htrY (by omega) (by omega), hstrY⟩
    have hstep2Bytes : ∀ hX nibX bibX ndX nwX (hpX : ParserEnv ctx hX) (hsawX : CompSawZero ctx hX)
        (htrX : NibBibTrack ctx h hX nibX bibX ndX nwX) (hndLo : -8 ≤ ndX) (hndX : ndX ≤ 0) (hnw0 : 0 ≤ nwX) (hnw : nwX ≤ 6) (hcurX : CurValid hX nibX bibX),
        ∃ resY hY, C.run (input2Bytes (.ref (C.DecompRef.decomp ctx.bdc) 0) nibX bibX) hX = .ok (resY, hY) ∧
          ParserEnv ctx hY ∧ CompSawZero ctx hY ∧ hY.decomps = hX.decomps ∧ hY.markers = hX.markers ∧
          match resY with
          | none => True
          | some (b, nibY, bibY) =>
            0 ≤ b.toInt ∧ b.toInt ≤ 65535 ∧ CurValid hY nibY bibY ∧
            NibBibTrack ctx h hY nibY bibY (-8) (nwX + 2) ∧
            (∀ srcs, C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
              isConstEofPtr nibY = true ∨ bibY.toNat < srcs[0]!.bytesInBuffer.toNat) := by
      intro hX nibX bibX ndX nwX hpX hsawX htrX hndLo hndX hnw0 hnw hcurX
      have hbdX : ∀ errs, C.Space.get hX ctx.rerr = some errs → 0 < errs.size →
          errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
        nibBibTrack_bd hp hpX htrX (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
          have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
      obtain ⟨resY, hY, hrunY, hpY, hdY, hmrY, _, _, _, _, _, _, _, _, hpostY⟩ :=
        input2Bytes_parser hpX nibX bibX hcurX hbdX
      have hsawY : CompSawZero ctx hY := fun m d hm hszm hd hszd hs =>
        hsawX m d (by dsimp only [C.Space.get] at hm ⊢; rw [hmrY] at hm; exact hm) hszm
          (by dsimp only [C.Space.get] at hd ⊢; rw [hdY] at hd; exact hd) hszd hs
      refine ⟨resY, hY, hrunY, hpY, hsawY, hdY, hmrY, ?_⟩
      cases resY with
      | none => trivial
      | some p =>
        rcases p with ⟨b, nibY, bibY⟩
        rcases hpostY with ⟨hb0, hbHi, hcurY, hceY⟩
        obtain ⟨htrY, hstrY⟩ := nibBibTrack_input2Bytes_step hp hpX htrX hndX hnw0 hceY
        exact ⟨hb0, hbHi, hcurY, nibBibTrack_mono htrY (by omega) (by omega), hstrY⟩
    have hputScalar : ∀ hX (hpX : ParserEnv ctx hX) (hsawX : CompSawZero ctx hX) (hmrX : hX.markers = h.markers)
        (nibX : C.BPtr) (bibX : UInt64) (nwX : Int)
        (htrX : NibBibTrack ctx h hX nibX bibX (-8) nwX) (hcurX : CurValid hX nibX bibX)
        (upd : C.JpegDecompressStruct → C.JpegDecompressStruct)
        (kerrU : ∀ d, (upd d).err = d.err) (kmemU : ∀ d, (upd d).mem = d.mem) (kmasU : ∀ d, (upd d).master = d.master)
        (kicU : ∀ d, (upd d).inputctl = d.inputctl) (kmrkU : ∀ d, (upd d).marker = d.marker) (ksrcU : ∀ d, (upd d).src = d.src)
        (kmlU : ∀ d, (upd d).markerList = d.markerList) (kcompU : ∀ d, (upd d).compInfo = d.compInfo)
        (kqtU : ∀ d, (upd d).quantTblPtrs = d.quantTblPtrs) (kdhU : ∀ d, (upd d).dcHuffTblPtrs = d.dcHuffTblPtrs)
        (kahU : ∀ d, (upd d).acHuffTblPtrs = d.acHuffTblPtrs) (kccU : ∀ d, (upd d).curCompInfo = d.curCompInfo)
        (kisnU : ∀ d, (upd d).inputScanNumber = d.inputScanNumber),
        ∃ dcsX,
          C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX ∧ 0 < dcsX.size ∧
          let dcX' := upd dcsX[0]!
          let hY := C.Space.put hX (C.DecompRef.decomp ctx.bdc) (dcsX.set! 0 dcX')
          C.run (Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)) hX = .ok (dcsX[0]!, hX) ∧
          C.run (Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) dcX') hX = .ok ((), hY) ∧
          ParserEnv ctx hY ∧ CompSawZero ctx hY ∧ hY.markers = h.markers ∧
          CurValid hY nibX bibX ∧ NibBibTrack ctx h hY nibX bibX (-8) nwX := by
      intro hX hpX hsawX hmrX nibX bibX nwX htrX hcurX upd
        kerrU kmemU kmasU kicU kmrkU ksrcU kmlU kcompU kqtU kdhU kahU kccU kisnU
      obtain ⟨dcsX, hgdcX, hszdcX, _⟩ := parserEnv_get_dc hpX
      have hldcX := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcX hszdcX
      have hroX : C.Space.ro hX (C.DecompRef.decomp ctx.bdc) = false := rfl
      have hstX := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := upd dcsX[0]!) hgdcX hroX hszdcX
      have hgmrkX : C.Space.get hX ctx.rmrk = some mrks0 := by
        dsimp only [C.Space.get]; rw [hmrX]; exact hgmrk0
      have hcompNullX : (upd dcsX[0]!).compInfo = .null := by
        rw [kcompU]
        exact hsawX mrks0 dcsX hgmrkX hszmrk0 hgdcX hszdcX hsawZ
      have hgdcY : C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX := hgdcX
      obtain ⟨hpY, hsawY⟩ := parserEnv_put_dc_scalar (upd dcsX[0]!) hpX hgdcY hszdcX
        (kerrU _) (kmemU _) (kmasU _) (kicU _) (kmrkU _) (ksrcU _)
        (kmlU _) (kcompU _) hcompNullX (kqtU _) (kdhU _) (kahU _) (kccU _) (kisnU _)
      refine ⟨dcsX, hgdcX, hszdcX, hldcX, hstX, hpY, hsawY, hmrX,
        curValid_bytes_irrel rfl rfl hcurX, nibBibTrack_err_same htrX rfl⟩
    obtain ⟨res1, h1, hrun1, hp1, hsaw1, _, hmr1, hpost1⟩ :=
      hstep2Bytes h0'' srcs0[0]!.nextInputByte srcs0[0]!.bytesInBuffer 0 0 hp0'' hsaw0''
        htr0'' (by omega) (by omega) (by omega) (by omega) hcur0''
    have hmr1_0 : h1.markers = h.markers := hmr1
    have hlsrc0' : C.run (Ptr.load dcs0[0]!.src) h = .ok (srcs0[0]!, h) := by rw [ksrc0]; exact hlsrc0
    have hlmrk0' : C.run (Ptr.load dcs0[0]!.marker) h = .ok (mrks0[0]!, h) := by rw [kmrk0]; exact hlmrk0
    have hlmst' : C.run (Ptr.load dcs0[0]!.master) h0' = .ok (masters0[0]!, h0') := by rw [kmas0]; exact hlmst
    have hstMst' : C.run (Ptr.store dcs0[0]!.master mst0') h0' = .ok ((), h0'') := by rw [kmas0]; exact hstMst
    have hvac : ∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size → mrks[0]!.sawSOF ≠ 0 →
        False := fun mrks hg _ hm => hm (Option.some.inj (hg.symm.trans hgmrk0) ▸ hsawZ)
    cases res1 with
    | none =>
      refine ⟨.ok false, h1, ?_, hp1, (fun mrks hg hsz hm => False.elim (hvac mrks hg hsz hm)), trivial⟩
      unfold get_sof
      rw [C.run_bind, hldc0]; dsimp only
      rw [C.run_bind, hlsrc0']; dsimp only
      rw [C.run_bind, hlmrk0']; dsimp only
      simp only [hsawDupF, Bool.false_eq_true, ↓reduceIte]
      rw [C.run_bind, hst0']; dsimp only
      rw [C.run_bind, hlmst']; dsimp only
      rw [C.run_bind, hstMst']; dsimp only
      rw [C.run_bind, hrun1]; rfl
    | some p1 =>
      rcases p1 with ⟨lenRaw, nib1, bib1⟩
      rcases hpost1 with ⟨hlenRaw0, hlenRawHi, hcur1, htr1, _⟩
      obtain ⟨res2, h2, hrun2, hp2, hsaw2, _, hmr2, hpost2⟩ :=
        hstepByte h1 nib1 bib1 2 hp1 hsaw1 htr1 (by omega) (by omega) hcur1
      have hmr2_0 : h2.markers = h.markers := hmr2.trans hmr1_0
      cases res2 with
      | none =>
        refine ⟨.ok false, h2, ?_, hp2, (fun mrks hg hsz hm => False.elim (hvac mrks hg hsz hm)), trivial⟩
        unfold get_sof
        rw [C.run_bind, hldc0]; dsimp only
        rw [C.run_bind, hlsrc0']; dsimp only
        rw [C.run_bind, hlmrk0']; dsimp only
        simp only [hsawDupF, Bool.false_eq_true, ↓reduceIte]
        rw [C.run_bind, hst0']; dsimp only
        rw [C.run_bind, hlmst']; dsimp only
        rw [C.run_bind, hstMst']; dsimp only
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind, hrun2]; rfl
      | some p2 =>
        rcases p2 with ⟨dp, nib2, bib2⟩
        rcases hpost2 with ⟨_, _, hcur2, htr2, _⟩
        obtain ⟨dcs2, _, _, hldc2, hst2, hp2', hsaw2', hmr2', hcur2', htr2'⟩ :=
          hputScalar h2 hp2 hsaw2 hmr2_0 nib2 bib2 3 htr2 hcur2 (fun d => { d with dataPrecision := dp })
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        let h2' := C.Space.put h2 (C.DecompRef.decomp ctx.bdc) (dcs2.set! 0 { dcs2[0]! with dataPrecision := dp })
        obtain ⟨res3, h3, hrun3, hp3, hsaw3, _, hmr3, hpost3⟩ :=
          hstep2Bytes h2' nib2 bib2 (-8) 3 hp2' hsaw2' htr2' (by omega) (by omega) (by omega) (by omega) hcur2'
        have hmr3_0 : h3.markers = h.markers := hmr3.trans hmr2'
        cases res3 with
        | none =>
          refine ⟨.ok false, h3, ?_, hp3, (fun mrks hg hsz hm => False.elim (hvac mrks hg hsz hm)), trivial⟩
          unfold get_sof
          rw [C.run_bind, hldc0]; dsimp only
          rw [C.run_bind, hlsrc0']; dsimp only
          rw [C.run_bind, hlmrk0']; dsimp only
          simp only [hsawDupF, Bool.false_eq_true, ↓reduceIte]
          rw [C.run_bind, hst0']; dsimp only
          rw [C.run_bind, hlmst']; dsimp only
          rw [C.run_bind, hstMst']; dsimp only
          rw [C.run_bind, hrun1]; dsimp only
          rw [C.run_bind, hrun2]; dsimp only
          rw [C.run_bind, hldc2]; dsimp only
          rw [C.run_bind, hst2]; dsimp only
          rw [C.run_bind, hrun3]; rfl
        | some p3 =>
          rcases p3 with ⟨ih, nib3, bib3⟩
          rcases hpost3 with ⟨_, _, hcur3, htr3, _⟩
          obtain ⟨dcs3, _, _, hldc3, hst3, hp3', hsaw3', hmr3', hcur3', htr3'⟩ :=
            hputScalar h3 hp3 hsaw3 hmr3_0 nib3 bib3 5 htr3 hcur3
              (fun d => { d with imageHeight := UInt32.ofNat ih.toInt.toNat })
              (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
              (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          let h3' := C.Space.put h3 (C.DecompRef.decomp ctx.bdc)
            (dcs3.set! 0 { dcs3[0]! with imageHeight := UInt32.ofNat ih.toInt.toNat })
          obtain ⟨res4, h4, hrun4, hp4, hsaw4, _, hmr4, hpost4⟩ :=
            hstep2Bytes h3' nib3 bib3 (-8) 5 hp3' hsaw3' htr3' (by omega) (by omega) (by omega) (by omega) hcur3'
          have hmr4_0 : h4.markers = h.markers := hmr4.trans hmr3'
          cases res4 with
          | none =>
            refine ⟨.ok false, h4, ?_, hp4, (fun mrks hg hsz hm => False.elim (hvac mrks hg hsz hm)), trivial⟩
            unfold get_sof
            rw [C.run_bind, hldc0]; dsimp only
            rw [C.run_bind, hlsrc0']; dsimp only
            rw [C.run_bind, hlmrk0']; dsimp only
            simp only [hsawDupF, Bool.false_eq_true, ↓reduceIte]
            rw [C.run_bind, hst0']; dsimp only
            rw [C.run_bind, hlmst']; dsimp only
            rw [C.run_bind, hstMst']; dsimp only
            rw [C.run_bind, hrun1]; dsimp only
            rw [C.run_bind, hrun2]; dsimp only
            rw [C.run_bind, hldc2]; dsimp only
            rw [C.run_bind, hst2]; dsimp only
            rw [C.run_bind, hrun3]; dsimp only
            rw [C.run_bind, hldc3]; dsimp only
            rw [C.run_bind, hst3]; dsimp only
            rw [C.run_bind, hrun4]; rfl
          | some p4 =>
            rcases p4 with ⟨iw, nib4, bib4⟩
            rcases hpost4 with ⟨_, _, hcur4, htr4, _⟩
            obtain ⟨dcs4, _, _, hldc4, hst4, hp4', hsaw4', hmr4', hcur4', htr4'⟩ :=
              hputScalar h4 hp4 hsaw4 hmr4_0 nib4 bib4 7 htr4 hcur4
                (fun d => { d with imageWidth := UInt32.ofNat iw.toInt.toNat })
                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            let h4' := C.Space.put h4 (C.DecompRef.decomp ctx.bdc)
              (dcs4.set! 0 { dcs4[0]! with imageWidth := UInt32.ofNat iw.toInt.toNat })
            obtain ⟨res5, h5, hrun5, hp5, hsaw5, _, hmr5, hpost5⟩ :=
              hstepByte h4' nib4 bib4 7 hp4' hsaw4' htr4' (by omega) (by omega) hcur4'
            have hmr5_0 : h5.markers = h.markers := hmr5.trans hmr4'
            cases res5 with
            | none =>
              refine ⟨.ok false, h5, ?_, hp5, (fun mrks hg hsz hm => False.elim (hvac mrks hg hsz hm)), trivial⟩
              unfold get_sof
              rw [C.run_bind, hldc0]; dsimp only
              rw [C.run_bind, hlsrc0']; dsimp only
              rw [C.run_bind, hlmrk0']; dsimp only
              simp only [hsawDupF, Bool.false_eq_true, ↓reduceIte]
              rw [C.run_bind, hst0']; dsimp only
              rw [C.run_bind, hlmst']; dsimp only
              rw [C.run_bind, hstMst']; dsimp only
              rw [C.run_bind, hrun1]; dsimp only
              rw [C.run_bind, hrun2]; dsimp only
              rw [C.run_bind, hldc2]; dsimp only
              rw [C.run_bind, hst2]; dsimp only
              rw [C.run_bind, hrun3]; dsimp only
              rw [C.run_bind, hldc3]; dsimp only
              rw [C.run_bind, hst3]; dsimp only
              rw [C.run_bind, hrun4]; dsimp only
              rw [C.run_bind, hldc4]; dsimp only
              rw [C.run_bind, hst4]; dsimp only
              rw [C.run_bind, hrun5]; rfl
            | some p5 =>
              rcases p5 with ⟨nc, nib5, bib5⟩
              rcases hpost5 with ⟨hnc0, hncHi, hcur5, htr5, hstr5⟩
              obtain ⟨dcs5, hgdc5, hszdc5, hldc5, hst5, hp5', hsaw5', hmr5', hcur5', htr5'⟩ :=
                hputScalar h5 hp5 hsaw5 hmr5_0 nib5 bib5 8 htr5 hcur5
                  (fun d => { d with numComponents := nc })
                  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
              let dc5' := { dcs5[0]! with numComponents := nc }
              let h5' := C.Space.put h5 (C.DecompRef.decomp ctx.bdc) (dcs5.set! 0 dc5')
              let length : Int64 := Int64.ofInt (lenRaw.toInt - 8)
              have hlenTo : length.toInt = lenRaw.toInt - 8 := by
                change (Int64.ofInt (lenRaw.toInt - 8)).toInt = lenRaw.toInt - 8
                rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
                exact Int.bmod_eq_of_le (by omega) (by omega)
              obtain ⟨dcs5a, hgdc5a, _, kerr5a, _⟩ := parserEnv_get_dc hp5
              have kerr5 : dcs5[0]!.err = .ref ctx.rerr 0 :=
                Option.some.inj (hgdc5a.symm.trans hgdc5) ▸ kerr5a
              have hdc5'err : dc5'.err = .ref ctx.rerr 0 := kerr5
              obtain ⟨hT, htrT_run, hpT, hdT, hmrT, _, _, hcpT, _, _, _, hbyT, _, hcoT, hnwT⟩ :=
                tracems4_nonneg_parser hp5' 1 JTRC_SOF dc5'.unreadMarker
                  (Int32.ofNat dc5'.imageWidth.toNat) (Int32.ofNat dc5'.imageHeight.toNat) dc5'.numComponents (by decide)
              have htrT_run' : C.run (tracems4 dc5'.err 1 JTRC_SOF dc5'.unreadMarker
                  (Int32.ofNat dc5'.imageWidth.toNat) (Int32.ofNat dc5'.imageHeight.toNat) dc5'.numComponents) h5' = .ok ((), hT) := by
                rw [hdc5'err]; exact htrT_run
              have htrT := nibBibTrack_err_nw_same hp5' htr5' hnwT
              have hcurT : CurValid hT nib5 bib5 := curValid_bytes_irrel hbyT hcoT hcur5'
              have hmrT0 : hT.markers = h.markers := hmrT.trans hmr5'
              have hsawT : CompSawZero ctx hT := fun m d hm hszm hd hszd hs =>
                hsaw5' m d (by dsimp only [C.Space.get] at hm ⊢; rw [hmrT] at hm; exact hm) hszm
                  (by dsimp only [C.Space.get] at hd ⊢; rw [hdT] at hd; exact hd) hszd hs
              have hpre5Eq : C.run (get_sof (.ref (.decomp ctx.bdc) 0) isProg isLossless isArith) h =
                  C.run (do
                    if dc5'.imageHeight == 0 || dc5'.imageWidth == 0 || dc5'.numComponents ≤ 0 then
                      let _ ← errexit dc5'.err JERR_EMPTY_IMAGE
                      return .errExit JERR_EMPTY_IMAGE
                    if length.toInt != dc5'.numComponents.toInt * 3 then
                      let _ ← errexit dc5'.err JERR_BAD_LENGTH
                      return .errExit JERR_BAD_LENGTH
                    let dc5 ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                    if dc5.compInfo == (Ptr.null : C.CompPtr) then
                      let nComps := dc5.numComponents.toInt.toNat
                      match (← alloc_small_comps (.ref (C.DecompRef.decomp ctx.bdc) 0) JPOOL_IMAGE nComps
                          (UInt64.ofNat nComps * sizeof_jpeg_component_info)) with
                      | .errExit code => return .errExit code
                      | .ok compP =>
                        let dc6 ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                        Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dc6 with compInfo := compP }
                    let dc7 ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                    let nComps := dc7.numComponents.toInt.toNat
                    let st ← cwhile
                      (fun (s : SofLoopState) => pure (!s.done && s.ci < nComps, s))
                      (fun (s : SofLoopState) => do
                        let cp ← Ptr.add dc7.compInfo (Int.ofNat s.ci)
                        let comp0 ← Ptr.load cp
                        Ptr.store cp { comp0 with componentIndex := Int32.ofNat s.ci }
                        match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
                        | none => return { s with done := true, ret := .ok false }
                        | some (cid, nibA, bibA) =>
                          let comp1 ← Ptr.load cp
                          Ptr.store cp { comp1 with componentId := cid }
                          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
                          | none => return { s with done := true, ret := .ok false }
                          | some (cbyte, nibB, bibB) =>
                            let comp2 ← Ptr.load cp
                            Ptr.store cp {
                              comp2 with
                              hSampFactor := (cbyte >>> 4) &&& 15
                              vSampFactor := cbyte &&& 15
                            }
                            match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibB bibB) with
                            | none => return { s with done := true, ret := .ok false }
                            | some (qno, nibC, bibC) =>
                              let comp3 ← Ptr.load cp
                              let comp4 := { comp3 with quantTblNo := qno }
                              Ptr.store cp comp4
                              tracems4 dc7.err 1 JTRC_SOF_COMPONENT
                                comp4.componentId comp4.hSampFactor comp4.vSampFactor comp4.quantTblNo
                              return { done := false, ret := .ok true, ci := s.ci + 1, nib := nibC, bib := bibC })
                      { done := false, ret := .ok true, ci := 0, nib := nib5, bib := bib5 }
                    if st.done then
                      return st.ret
                    let dcEnd ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                    let mrkEnd ← Ptr.load dcEnd.marker
                    Ptr.store dcEnd.marker { mrkEnd with sawSOF := TRUE }
                    inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib
                    return .ok true) hT := by
                unfold get_sof
                rw [C.run_bind, hldc0]; dsimp only
                rw [C.run_bind, hlsrc0']; dsimp only
                rw [C.run_bind, hlmrk0']; dsimp only
                simp only [hsawDupF, Bool.false_eq_true, ↓reduceIte]
                rw [C.run_bind, hst0']; dsimp only
                rw [C.run_bind, hlmst']; dsimp only
                rw [C.run_bind, hstMst']; dsimp only
                rw [C.run_bind, hrun1]; dsimp only
                rw [C.run_bind, hrun2]; dsimp only
                rw [C.run_bind, hldc2]; dsimp only
                rw [C.run_bind, hst2]; dsimp only
                rw [C.run_bind, hrun3]; dsimp only
                rw [C.run_bind, hldc3]; dsimp only
                rw [C.run_bind, hst3]; dsimp only
                rw [C.run_bind, hrun4]; dsimp only
                rw [C.run_bind, hldc4]; dsimp only
                rw [C.run_bind, hst4]; dsimp only
                rw [C.run_bind, hrun5]; dsimp only
                rw [C.run_bind, hldc5]; dsimp only
                rw [C.run_bind, hst5]; dsimp only
                rw [C.run_bind, htrT_run']; rfl
              by_cases hEmpty : (dc5'.imageHeight == 0 || dc5'.imageWidth == 0 || dc5'.numComponents ≤ 0) = true
              · obtain ⟨hE, herr_run, hpE, hstTE⟩ := errexit_stable_parser hpT JERR_EMPTY_IMAGE
                have herr_run' : C.run (errexit dc5'.err JERR_EMPTY_IMAGE) hT = .ok (.errExit JERR_EMPTY_IMAGE, hE) := by
                  rw [hdc5'err]; exact herr_run
                refine ⟨.errExit JERR_EMPTY_IMAGE, hE, ?_, hpE,
                  (fun mrks hg _ hm => False.elim (hm (Option.some.inj (hg.symm.trans hgmrk0) ▸ hsawZ))),
                  compSawZero_of_stable hsawT hstTE hpT⟩
                rw [hpre5Eq]
                simp only [hEmpty, ↓reduceIte, C.run_bind, herr_run']; rfl
              · have hEmptyF : (dc5'.imageHeight == 0 || dc5'.imageWidth == 0 || dc5'.numComponents ≤ 0) = false :=
                  Bool.eq_false_iff.mpr hEmpty
                have hncPos : 0 < nc.toInt := by
                  by_cases hle : dc5'.numComponents ≤ 0
                  · have : (dc5'.imageHeight == 0 || dc5'.imageWidth == 0 || dc5'.numComponents ≤ 0) = true := by
                      simp [hle]
                    rw [this] at hEmptyF; cases hEmptyF
                  · exact Int32.lt_iff_toInt_lt.mp (Int32.not_le.mp hle)
                by_cases hBadLen : (length.toInt != dc5'.numComponents.toInt * 3) = true
                · obtain ⟨hE, herr_run, hpE, hstTE⟩ := errexit_stable_parser hpT JERR_BAD_LENGTH
                  have herr_run' : C.run (errexit dc5'.err JERR_BAD_LENGTH) hT = .ok (.errExit JERR_BAD_LENGTH, hE) := by
                    rw [hdc5'err]; exact herr_run
                  refine ⟨.errExit JERR_BAD_LENGTH, hE, ?_, hpE,
                    (fun mrks hg _ hm => False.elim (hm (Option.some.inj (hg.symm.trans hgmrk0) ▸ hsawZ))),
                    compSawZero_of_stable hsawT hstTE hpT⟩
                  rw [hpre5Eq]
                  simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte]
                  simp only [hBadLen, ↓reduceIte, C.run_bind, herr_run']; rfl
                · have hBadLenF : (length.toInt != dc5'.numComponents.toInt * 3) = false :=
                    Bool.eq_false_iff.mpr hBadLen
                  have hgdc5' : C.Space.get h5' (C.DecompRef.decomp ctx.bdc) = some (dcs5.set! 0 dc5') := by
                    simp [h5', C.Space.get, C.Space.put]
                  have hgdcT : C.Space.get hT (C.DecompRef.decomp ctx.bdc) = some (dcs5.set! 0 dc5') := by
                    dsimp only [C.Space.get]; rw [hdT]; exact hgdc5'
                  have hszdcT : 0 < (dcs5.set! 0 dc5').size := by simpa using hszdc5
                  have hldcT := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcT hszdcT
                  have hdcT0 : (dcs5.set! 0 dc5')[0]! = dc5' := set0_bang_m dcs5 hszdc5 dc5'
                  have hcompNullT : dc5'.compInfo = .null := by
                    have hgmrkT : C.Space.get hT ctx.rmrk = some mrks0 := by
                      dsimp only [C.Space.get]; rw [hmrT0]; exact hgmrk0
                    rw [← hdcT0]
                    exact hsawT mrks0 (dcs5.set! 0 dc5') hgmrkT hszmrk0 hgdcT hszdcT hsawZ
                  have hcompNullEq : (dc5'.compInfo == .null) = true := by simp [hcompNullT]
                  let nComps : Nat := dc5'.numComponents.toInt.toNat
                  have hnCompsHi : nComps ≤ 255 := by dsimp [nComps, dc5']; omega
                  obtain ⟨resA, hA, hrunA, hpA, hresA⟩ := alloc_small_comps_parser hpT nComps (by omega)
                  cases resA with
                  | errExit code =>
                    rcases hresA with ⟨hdA, hmrA⟩
                    have hsawA : CompSawZero ctx hA := fun m d hm hszm hd hszd hs =>
                      hsawT m d (by dsimp only [C.Space.get] at hm ⊢; rw [hmrA] at hm; exact hm) hszm
                        (by dsimp only [C.Space.get] at hd ⊢; rw [hdA] at hd; exact hd) hszd hs
                    refine ⟨.errExit code, hA, ?_, hpA,
                      (fun mrks hg _ hm => False.elim (hm (Option.some.inj (hg.symm.trans hgmrk0) ▸ hsawZ))), hsawA⟩
                    rw [hpre5Eq]
                    simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte]
                    simp only [hBadLenF, Bool.false_eq_true, ↓reduceIte, C.run_bind, hldcT]
                    rw [hdcT0]; simp only [hcompNullEq, ↓reduceIte, C.run_bind]
                    dsimp only [nComps] at hrunA; rw [hrunA]; rfl
                  | ok compP =>
                    rcases hresA with ⟨hcompPNe, hdA, hmrA, hsrA, heA, hmaA, hquA, hhuA, hsmA, hbyA, hcoA, hLiveA⟩
                    have hgdcA : C.Space.get hA (C.DecompRef.decomp ctx.bdc) = some (dcs5.set! 0 dc5') := by
                      dsimp only [C.Space.get]; rw [hdA]; exact hgdcT
                    have hldcA := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcA hszdcT
                    have hroA : C.Space.ro hA (C.DecompRef.decomp ctx.bdc) = false := rfl
                    let dc6' := { dc5' with compInfo := compP }
                    have hstA := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc6') hgdcA hroA hszdcT
                    rw [hdcT0] at hldcA
                    let h6 := C.Space.put hA (C.DecompRef.decomp ctx.bdc) ((dcs5.set! 0 dc5').set! 0 dc6')
                    have hgmrkA : C.Space.get hA ctx.rmrk = some mrks0 := by
                      dsimp only [C.Space.get]; rw [hmrA, hmrT0]; exact hgmrk0
                    have hp6 : ParserEnv ctx h6 := by
                      have hpA0 := hpA
                      obtain ⟨_, _, dcsA0, dcA0, _, _, _, _, mrksA0, _,
                        hgdcA0, _, hdcA0, _, _, _, _, _,
                        _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                        _, _, _, _, _, _, _, _,
                        _, hgmrkA0, _, _, _, _, _, _, _,
                        _, _, _, _, _, _, _, _, _,
                        _, _, hsawA0, _, hqtSzA, hqtA, hdhSzA, hdhA, hahSzA, hahA, hccSzA, hisnA⟩ := hpA0
                      have hdAEq : dcs5.set! 0 dc5' = dcsA0 := Option.some.inj (hgdcA.symm.trans hgdcA0)
                      subst hdAEq; subst hdcA0
                      have hdc5Eq : dc5' = (dcs5.set! 0 dc5')[0]! := hdcT0.symm
                      refine parserEnv_put_dc hpA hgdcA hszdcT
                        (by dsimp only [dc6']; rw [← hdc5Eq]) (by dsimp only [dc6']; rw [← hdc5Eq]) (by dsimp only [dc6']; rw [← hdc5Eq])
                        (by dsimp only [dc6']; rw [← hdc5Eq]) (by dsimp only [dc6']; rw [← hdc5Eq]) (by dsimp only [dc6']; rw [← hdc5Eq])
                        (Or.inl (by dsimp only [dc6']; rw [← hdc5Eq]))
                        (Or.inr (Or.inr ⟨by dsimp only [dc6']; omega, hLiveA⟩))
                        ⟨by dsimp only [dc6']; rw [hdc5Eq]; exact hqtSzA, fun i hi => by dsimp only [dc6']; rw [hdc5Eq]; exact hqtA i hi⟩
                        ⟨by dsimp only [dc6']; rw [hdc5Eq]; exact hdhSzA, fun i hi => by dsimp only [dc6']; rw [hdc5Eq]; exact hdhA i hi⟩
                        ⟨by dsimp only [dc6']; rw [hdc5Eq]; exact hahSzA, fun i hi => by dsimp only [dc6']; rw [hdc5Eq]; exact hahA i hi⟩
                        (by dsimp only [dc6']; rw [hdc5Eq]; exact hccSzA)
                        (by dsimp only [dc6']; rw [hdc5Eq]; exact hisnA)
                        (fun _ _ _ _ => hcompPNe)
                    have hgdc6 : C.Space.get h6 (C.DecompRef.decomp ctx.bdc) = some ((dcs5.set! 0 dc5').set! 0 dc6') := by
                      simp [h6, C.Space.get, C.Space.put]
                    have hszdc6 : 0 < ((dcs5.set! 0 dc5').set! 0 dc6').size := by simpa using hszdcT
                    have hldc6 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc6 hszdc6
                    have hdc6Eq : ((dcs5.set! 0 dc5').set! 0 dc6')[0]! = dc6' := set0_bang_m (dcs5.set! 0 dc5') hszdcT dc6'
                    rw [hdc6Eq] at hldc6
                    have htr6 := nibBibTrack_err_same htrT heA
                    have hcur6 : CurValid h6 nib5 bib5 := curValid_bytes_irrel hbyA hcoA hcurT
                    have hLive6 : LiveCompArray h6 compP nComps := hLiveA
                    have hkerr5' : dc5'.err = .ref ctx.rerr 0 := hdc5'err
                    have hkerr6 : dc6'.err = .ref ctx.rerr 0 := hkerr5'
                    obtain ⟨st, hL, hloop, hpL, hdL, hnrL, hfinL⟩ :=
                      get_sof_loop_parser hp hhead compP dc6'.err hkerr6 nComps hnCompsHi nib5 bib5 hp6 hLive6
                        hcur6 (nibBibTrack_mono htr6 (by omega) (by omega)) hstr5
                    have hpre6Eq : C.run (get_sof (.ref (.decomp ctx.bdc) 0) isProg isLossless isArith) h =
                        C.run (do
                          if st.done then
                            return st.ret
                          let dcEnd ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                          let mrkEnd ← Ptr.load dcEnd.marker
                          Ptr.store dcEnd.marker { mrkEnd with sawSOF := TRUE }
                          inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib
                          return .ok true) hL := by
                      rw [hpre5Eq]
                      simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte]
                      simp only [hBadLenF, Bool.false_eq_true, ↓reduceIte, C.run_bind, hldcT]
                      rw [hdcT0]; simp only [hcompNullEq, ↓reduceIte, C.run_bind]
                      dsimp only [nComps] at hrunA; rw [hrunA]; dsimp only
                      rw [C.run_bind, hldcA]; dsimp only
                      rw [C.run_bind, hstA]; dsimp only
                      rw [C.run_bind, hldc6]; dsimp only
                      dsimp only [dc6']
                      rw [C.run_bind]; erw [hloop]
                    by_cases hdone : st.done = true
                    · refine ⟨st.ret, hL, ?_, hpL,
                        (fun mrks hg _ hm => False.elim (hm (Option.some.inj (hg.symm.trans hgmrk0) ▸ hsawZ))), ?_⟩
                      · rw [hpre6Eq]; simp only [hdone, ↓reduceIte]; rfl
                      · rw [hnrL hdone]; trivial
                    · have hdoneF : st.done = false := Bool.eq_false_iff.mpr hdone
                      obtain ⟨hcurSt, htrSt, hstrSt⟩ := hfinL (by simp [hdoneF])
                      obtain ⟨dcsEnd, hgdcEnd, hszdcEnd, _, _, _, _, kmrkEnd, _⟩ := parserEnv_get_dc hpL
                      have hldcEnd := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcEnd hszdcEnd
                      obtain ⟨mrksEnd, hgmrkEnd, hszmrkEnd, _⟩ := parserEnv_get_mrk hpL
                      have hlmrkEnd := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrkEnd hszmrkEnd
                      have hroMrk : C.Space.ro hL ctx.rmrk = false := rfl
                      let mrkNew := { mrksEnd[0]! with sawSOF := TRUE }
                      have hstMrk := ptr_store_ok (r := ctx.rmrk) (off := 0) (v := mrkNew) hgmrkEnd hroMrk hszmrkEnd
                      let hEnd := C.Space.put hL ctx.rmrk (mrksEnd.set! 0 mrkNew)
                      have hcompNN : ∀ dcsE, C.Space.get hL (C.DecompRef.decomp ctx.bdc) = some dcsE → 0 < dcsE.size →
                          dcsE[0]!.compInfo ≠ .null := by
                        intro dcsE hgE _
                        have hgL6 : C.Space.get hL (C.DecompRef.decomp ctx.bdc) = some ((dcs5.set! 0 dc5').set! 0 dc6') := by
                          dsimp only [C.Space.get]; rw [hdL]; exact hgdc6
                        have hEqE := Option.some.inj (hgE.symm.trans hgL6)
                        rw [hEqE, hdc6Eq]
                        exact hcompPNe
                      obtain ⟨hpEnd, hsawEnd⟩ := parserEnv_put_mrk_sawSOF_true hpL hgmrkEnd hszmrkEnd hcompNN
                      have htrEnd := nibBibTrack_err_same htrSt (rfl : hEnd.errMgrs = hL.errMgrs)
                      have hcurEnd : CurValid hEnd st.nib st.bib := curValid_bytes_irrel rfl rfl hcurSt
                      obtain ⟨h3, hsync, hp3, hd3, hmr3, he3, _, _, _, _, _, _, _, _, hsrc3⟩ :=
                        inputSync_parser hpEnd st.nib st.bib hcurEnd
                      have hsaw3 : CompSawZero ctx h3 := fun m d hm hszm hd' hszd hs =>
                        hsawEnd m d (by dsimp only [C.Space.get] at hm ⊢; rw [hmr3] at hm; exact hm) hszm
                          (by dsimp only [C.Space.get] at hd' ⊢; rw [hd3] at hd'; exact hd') hszd hs
                      obtain ⟨hw, _⟩ := nibBibTrack_to_warnPotOk_src hp hpEnd htrEnd (by omega) he3 hsrc3
                      have hstr := nibBibTrack_to_srcStrict hp hpEnd htrEnd hstrSt hsrc3
                      refine ⟨.ok true, h3, ?_, hp3,
                        (fun mrks hg _ hm => False.elim (hm (Option.some.inj (hg.symm.trans hgmrk0) ▸ hsawZ))),
                        hsaw3, hstr, ?_⟩
                      · rw [hpre6Eq]
                        simp only [hdoneF, Bool.false_eq_true, ↓reduceIte]
                        rw [C.run_bind, hldcEnd]; dsimp only
                        rw [kmrkEnd, C.run_bind, hlmrkEnd]; dsimp only
                        rw [C.run_bind, hstMrk]; dsimp only
                        rw [C.run_bind, hsync]; rfl
                      · intro e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
                        obtain ⟨wf, wt⟩ := hw e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
                        exact ⟨wf, fun ht => by have := wt ht; omega⟩

/-! ## `PostSofBase`, `get_sos` -/

/-- Header and component-table bounds established before scan markers, preserved across
header-stable parsers and extended to `MultiScanReady` by `get_sos`. -/
def PostSofBase (h : C.Heap) (dc : C.JpegDecompressStruct) : Prop :=
  dc.entropyStartPass = .fn "noop" ∧
  dc.coefStartInputPass = .fn "noop" ∧
  dc.coefConsumeData = .fn "dummy_consume_data" ∧
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
        0 ≤ (cs[j]!).dctHScaledSize.toInt ∧ (cs[j]!).dctHScaledSize.toInt ≤ DCTSIZE.toInt)

theorem postSofBase_of_multiScanReady {h : C.Heap} {dc : C.JpegDecompressStruct}
    (hm : MultiScanReady h dc) : PostSofBase h dc := by
  rcases hm with ⟨e1, e2, e3, _, _, _, m1, m2, m3, m4, w1, h1, nc1, nc2, mk, cp, _⟩
  exact ⟨e1, e2, e3, m1, m2, m3, m4, w1, h1, nc1, nc2, mk, cp⟩

private theorem parserEnv_get_compLive {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h) :
    ∃ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs ∧ 0 < dcs.size ∧
      (∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size → mrks[0]!.sawSOF ≠ 0 →
        dcs[0]!.compInfo ≠ .null) ∧
      (dcs[0]!.compInfo ≠ .null →
        0 ≤ dcs[0]!.numComponents.toInt ∧
        LiveCompArray h dcs[0]!.compInfo dcs[0]!.numComponents.toInt.toNat) ∧
      dcs[0]!.curCompInfo.size = 4 := by
  obtain ⟨_, _, dcs, dc, _, _, _, _, mrks0, _, hgdc, hszdc, hdc,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hgmrk0, hszmrk0, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, _, hsaw0, hcl0, _, _, _, _, _, _, hccSz0, _⟩ := hp
  refine ⟨dcs, hgdc, hszdc, fun mrks hgm _ hm => ?_, hdc ▸ hcl0, hdc ▸ hccSz0⟩
  have hmEq := Option.some.inj (hgm.symm.trans hgmrk0)
  subst hmEq; exact hdc ▸ hsaw0 hm

theorem postSofBase_of_decompHeaderStable {ctx : IoCtx} {h h' : C.Heap}
    (hp : ParserEnv ctx h) (hp' : ParserEnv ctx h') (hst : DecompHeaderStable ctx h h')
    {dcs dcs' : Array C.JpegDecompressStruct}
    (hg : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hsz : 0 < dcs.size)
    (hg' : C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs') (hsz' : 0 < dcs'.size)
    (hpost : PostSofBase h dcs[0]!) :
    PostSofBase h' dcs'[0]! := by
  rcases hst with ⟨hd, hm, hcp⟩
  obtain ⟨hci, hnc, hiw, hih, hmh, hmv, hesp, hcsip, hccd⟩ := hd dcs dcs' hg hsz hg' hsz'
  obtain ⟨dcsP, hgdcP, _, _, _, _, _, kmrk, _⟩ := parserEnv_get_dc hp
  have hdEq := Option.some.inj (hgdcP.symm.trans hg)
  rw [hdEq] at kmrk
  obtain ⟨dcsP', hgdcP', _, _, _, _, _, kmrk', _⟩ := parserEnv_get_dc hp'
  have hdEq' := Option.some.inj (hgdcP'.symm.trans hg')
  rw [hdEq'] at kmrk'
  obtain ⟨mrks, hgmrk, hszmrk, _⟩ := parserEnv_get_mrk hp
  obtain ⟨mrks', hgmrk', hszmrk', _⟩ := parserEnv_get_mrk hp'
  have hsawEq := hm mrks mrks' hgmrk hszmrk hgmrk' hszmrk'
  rcases hpost with ⟨e1, e2, e3, m1, m2, m3, m4, w1, h1, nc1, nc2, ⟨rmrk0, mrks0, kr0, hgr0, hszr0, hs0⟩, hc⟩
  have hrmEq : rmrk0 = ctx.rmrk := by
    injection (kmrk.symm.trans kr0) with h1; exact h1.symm
  subst hrmEq
  have hmEq0 : mrks = mrks0 := Option.some.inj (hgmrk.symm.trans hgr0)
  subst hmEq0
  refine ⟨hesp.trans e1, hcsip.trans e2, hccd.trans e3, hmh.symm ▸ m1, hmh.symm ▸ m2,
    hmv.symm ▸ m3, hmv.symm ▸ m4, hiw.symm ▸ w1, hih.symm ▸ h1, hnc.symm ▸ nc1, hnc.symm ▸ nc2,
    ⟨ctx.rmrk, mrks', kmrk', hgmrk', hszmrk', hsawEq.symm ▸ hs0⟩, ?_⟩
  rcases hc with hncZ | ⟨rcp, cs, hci0, hgcs, hle, hcomp⟩
  · left; exact hnc.symm ▸ hncZ
  · right
    have hci' : dcs'[0]!.compInfo = .ref rcp 0 := hci.trans hci0
    obtain ⟨dcsL', hgdcL', _, _, hcl', _⟩ := parserEnv_get_compLive hp'
    have hEqL' := Option.some.inj (hgdcL'.symm.trans hg')
    rw [hEqL'] at hcl'
    have hneL' : dcs'[0]!.compInfo ≠ .null := by rw [hci']; simp
    obtain ⟨_, rcp', cs', hci'', hgcs', hle'⟩ := hcl' hneL'
    have hrcpEq : rcp' = rcp := by
      injection (hci'.symm.trans hci'') with h1; exact h1.symm
    rw [hrcpEq] at hci'' hgcs'
    refine ⟨rcp, cs', hci', hgcs', hle', fun j hj => ?_⟩
    have hj0 : j < dcs[0]!.numComponents.toInt.toNat := by rw [← hnc]; exact hj
    obtain ⟨cs'', hgcs'', _, hh, hv, hdct⟩ :=
      hcp rcp cs j hgcs (Nat.lt_of_lt_of_le hj0 hle)
    have hcsEq := Option.some.inj (hgcs''.symm.trans hgcs')
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcomp j hj0
    rw [← hcsEq, hh, hv, hdct]
    exact ⟨h1, h2, h3, h4, h5, h6⟩

private theorem get_sos_loop_parser {ctx : IoCtx} {h0 h2 : C.Heap} (hp0 : ParserEnv ctx h0)
    (hhead : ∀ errs0 srcs0, C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63)
    (errRef : C.ErrPtr) (herrRef : errRef = .ref ctx.rerr 0)
    (rcp : C.CompRef) (nNat : Nat) (hn1 : 1 ≤ nNat) (hn4 : nNat ≤ 4)
    (nib2 : C.BPtr) (bib2 : UInt64)
    (hp2 : ParserEnv ctx h2) (_hcp2 : CompPreserve h0 h2)
    {dcs2 : Array C.JpegDecompressStruct} {cs2 : Array C.JpegCompInfo}
    (hgdc2 : C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2) (hszdc2 : 0 < dcs2.size)
    (hci2 : dcs2[0]!.compInfo = .ref rcp 0) (hgcs2 : C.Space.get h2 rcp = some cs2)
    (hnc0_2 : 0 ≤ dcs2[0]!.numComponents.toInt) (hle2 : dcs2[0]!.numComponents.toInt.toNat ≤ cs2.size)
    (hccSz2 : dcs2[0]!.curCompInfo.size = 4) (herr2 : dcs2[0]!.err = errRef)
    (_hmr2 : h2.markers = h0.markers)
    (hcur2 : CurValid h2 nib2 bib2) (htr2 : NibBibTrack ctx h0 h2 nib2 bib2 (-12) 3)
    (hstr2 : ∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      isConstEofPtr nib2 = true ∨ bib2.toNat + 3 ≤ srcs0[0]!.bytesInBuffer.toNat) :
    ∃ st hL,
      C.run (cwhile
        (fun (s : SosLoopState) => pure (!s.done && s.i < nNat, s))
        (fun (s : SosLoopState) => do
          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
          | none => return { s with done := true, ret := .ok false }
          | some (cc, nibA, bibA) =>
            match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
            | none => return { s with done := true, ret := .ok false }
            | some (cbyte, nibB, bibB) =>
              let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
              let lim := min dcCur.numComponents.toInt.toNat MAX_COMPS_IN_SCAN.toInt.toNat
              let mut found : Option C.CompPtr := none
              for ci in List.range lim do
                if found.isNone then
                  let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
                  let comp ← Ptr.load cp
                  if cc == comp.componentId && dcCur.curCompInfo[ci]! == .null then
                    found := some cp
              match found with
              | none =>
                let _ ← errexit1 dcCur.err JERR_BAD_COMPONENT_ID cc
                return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
              | some cp =>
                Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0)
                  { dcCur with curCompInfo := dcCur.curCompInfo.set! s.i cp }
                let comp ← Ptr.load cp
                let comp' := { comp with dcTblNo := (cbyte >>> 4) &&& 15, acTblNo := cbyte &&& 15 }
                Ptr.store cp comp'
                tracems3 dcCur.err 1 JTRC_SOS_COMPONENT cc comp'.dcTblNo comp'.acTblNo
                let dcChk ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                for pi in List.range s.i do
                  if dcChk.curCompInfo[pi]! == cp then
                    let _ ← errexit1 dcChk.err JERR_BAD_COMPONENT_ID cc
                    return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
                return { done := false, ret := .ok true, i := s.i + 1, nib := nibB, bib := bibB })
        { done := false, ret := .ok true, i := 0, nib := nib2, bib := bib2 }) h2 = .ok (st, hL) ∧
      ParserEnv ctx hL ∧
      DecompHeaderStable ctx h2 hL ∧
      (st.done = true → st.ret ≠ .ok true) ∧
      (!st.done →
        CurValid hL st.nib st.bib ∧
        NibBibTrack ctx h0 hL st.nib st.bib (-12) 11 ∧
        (∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
          isConstEofPtr st.nib = true ∨ st.bib.toNat + 5 ≤ srcs0[0]!.bytesInBuffer.toNat) ∧
        (∀ dcsL, C.Space.get hL (C.DecompRef.decomp ctx.bdc) = some dcsL → 0 < dcsL.size →
          dcsL[0]!.compsInScan = dcs2[0]!.compsInScan ∧
          dcsL[0]!.curCompInfo.size = 4 ∧
          dcsL[0]!.inputScanNumber = dcs2[0]!.inputScanNumber ∧
          ∀ k < nNat, ∃ off csL, dcsL[0]!.curCompInfo[k]! = .ref rcp off ∧
            C.Space.get hL rcp = some csL ∧ off < csL.size ∧ off < dcsL[0]!.numComponents.toInt.toNat)) := by
  obtain ⟨dcs0_a, hgdc0_a, hszdc0_a, _⟩ := parserEnv_get_dc hp0
  let Inv : Nat → C.Heap → SosLoopState → Prop := fun k hC s =>
    ParserEnv ctx hC ∧ DecompHeaderStable ctx h2 hC ∧
    (s.done = true → k = 0 ∧ s.ret ≠ .ok true) ∧
    (!s.done →
      k + s.i = nNat ∧ s.i ≤ nNat ∧
      CurValid hC s.nib s.bib ∧
      NibBibTrack ctx h0 hC s.nib s.bib (-12) (3 + 2 * (s.i : Int)) ∧
      (∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
        isConstEofPtr s.nib = true ∨ s.bib.toNat + 3 + 2 * s.i ≤ srcs0[0]!.bytesInBuffer.toNat) ∧
      ∀ dcsC, C.Space.get hC (C.DecompRef.decomp ctx.bdc) = some dcsC → 0 < dcsC.size →
        dcsC[0]!.compInfo = .ref rcp 0 ∧
        dcsC[0]!.numComponents = dcs2[0]!.numComponents ∧
        dcsC[0]!.compsInScan = dcs2[0]!.compsInScan ∧
        dcsC[0]!.curCompInfo.size = 4 ∧
        dcsC[0]!.err = errRef ∧
        dcsC[0]!.inputScanNumber = dcs2[0]!.inputScanNumber ∧
        ∀ j < s.i, ∃ off csC, dcsC[0]!.curCompInfo[j]! = .ref rcp off ∧
          C.Space.get hC rcp = some csC ∧ off < csC.size ∧ off < dcsC[0]!.numComponents.toInt.toNat)
  let k0 := nNat
  have hk0Lt : k0 < C.fuel := by unfold C.fuel; dsimp only [k0]; omega
  have hinit : Inv k0 h2 { done := false, ret := .ok true, i := 0, nib := nib2, bib := bib2 } := by
    refine ⟨hp2, decompHeaderStable_refl ctx h2, (fun hd => by cases hd), fun _ =>
      ⟨rfl, Nat.zero_le nNat, hcur2, htr2, fun s0 hs0 hss0 => by simpa using hstr2 s0 hs0 hss0,
       fun dcsC hgC _ => ?_⟩⟩
    have hEqC := Option.some.inj (hgC.symm.trans hgdc2); subst hEqC
    exact ⟨hci2, rfl, rfl, hccSz2, herr2, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  obtain ⟨st, hL, hloop, hpost⟩ :=
    cwhile_terminates
      (fun (s : SosLoopState) => pure (!s.done && s.i < nNat, s))
      (fun (s : SosLoopState) => do
        match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
        | none => return { s with done := true, ret := .ok false }
        | some (cc, nibA, bibA) =>
          match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
          | none => return { s with done := true, ret := .ok false }
          | some (cbyte, nibB, bibB) =>
            let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            let lim := min dcCur.numComponents.toInt.toNat MAX_COMPS_IN_SCAN.toInt.toNat
            let mut found : Option C.CompPtr := none
            for ci in List.range lim do
              if found.isNone then
                let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
                let comp ← Ptr.load cp
                if cc == comp.componentId && dcCur.curCompInfo[ci]! == .null then
                  found := some cp
            match found with
            | none =>
              let _ ← errexit1 dcCur.err JERR_BAD_COMPONENT_ID cc
              return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
            | some cp =>
              Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0)
                { dcCur with curCompInfo := dcCur.curCompInfo.set! s.i cp }
              let comp ← Ptr.load cp
              let comp' := { comp with dcTblNo := (cbyte >>> 4) &&& 15, acTblNo := cbyte &&& 15 }
              Ptr.store cp comp'
              tracems3 dcCur.err 1 JTRC_SOS_COMPONENT cc comp'.dcTblNo comp'.acTblNo
              let dcChk ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
              for pi in List.range s.i do
                if dcChk.curCompInfo[pi]! == cp then
                  let _ ← errexit1 dcChk.err JERR_BAD_COMPONENT_ID cc
                  return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
              return { done := false, ret := .ok true, i := s.i + 1, nib := nibB, bib := bibB })
      Inv
      (fun hL st =>
        ParserEnv ctx hL ∧ DecompHeaderStable ctx h2 hL ∧
        (st.done = true → st.ret ≠ .ok true) ∧
        (!st.done →
          CurValid hL st.nib st.bib ∧
          NibBibTrack ctx h0 hL st.nib st.bib (-12) 11 ∧
          (∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
            isConstEofPtr st.nib = true ∨ st.bib.toNat + 5 ≤ srcs0[0]!.bytesInBuffer.toNat) ∧
          (∀ dcsL, C.Space.get hL (C.DecompRef.decomp ctx.bdc) = some dcsL → 0 < dcsL.size →
            dcsL[0]!.compsInScan = dcs2[0]!.compsInScan ∧
            dcsL[0]!.curCompInfo.size = 4 ∧
            dcsL[0]!.inputScanNumber = dcs2[0]!.inputScanNumber ∧
            ∀ k < nNat, ∃ off csL, dcsL[0]!.curCompInfo[k]! = .ref rcp off ∧
              C.Space.get hL rcp = some csL ∧ off < csL.size ∧ off < dcsL[0]!.numComponents.toInt.toNat)))
      (fun k hCur s hinv => by
        rcases hinv with ⟨hpC, hstC, hdC, hactC⟩
        by_cases hcond : (!s.done && s.i < nNat) = true
        · refine ⟨true, s, hCur, (by simp only [C.run, pure, hcond]), ?_⟩
          simp only [↓reduceIte]
          have hsDoneF : s.done = false := by cases hc : s.done <;> simp_all
          have hsiLt : s.i < nNat := by simp [hsDoneF] at hcond; exact hcond
          obtain ⟨hkEq, _, hcurS, htrS, hstrS, hdcS⟩ := hactC (by simp [hsDoneF])
          have hbdA : s.bib = 0 → ∀ errs, C.Space.get hCur ctx.rerr = some errs → 0 < errs.size →
              errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
            nibBibTrack_bd hp0 hpC htrS (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
              have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
          obtain ⟨resA, hA, hrunA, hpA, hdA, hmrA, _, hcpA, _, _, _, hbyA, _, hcoA, hpostA⟩ :=
            inputByte_parser hpC s.nib s.bib hcurS hbdA
          have hstCA := decompHeaderStable_trans hp2 hpC hstC (decompHeaderStable_of_same hdA hmrA hcpA)
          cases resA with
          | none =>
            refine ⟨0, { s with done := true, ret := .ok false }, hA, ?_, by omega, hpA, hstCA,
              fun _ => ⟨rfl, by simp⟩, fun hno => by simp at hno⟩
            rw [C.run_bind, hrunA]; rfl
          | some pA =>
            rcases pA with ⟨cc, nibA, bibA⟩
            rcases hpostA with ⟨_, _, hcurA, hceA⟩
            obtain ⟨htrA, hstrA⟩ := nibBibTrack_inputByte_step hp0 hpC htrS (by omega) (by omega) hceA
            have hstrA' : ∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
                isConstEofPtr nibA = true ∨ bibA.toNat + 3 + 2 * s.i + 1 ≤ srcs0[0]!.bytesInBuffer.toNat := by
              intro s0 hs0 hss0
              by_cases hnfA : isConstEofPtr nibA = false
              · simp only [hnfA, ↓reduceIte] at hceA
                rcases hceA with ⟨hnfS, _, hbibA, _⟩
                rcases hstrS s0 hs0 hss0 with htr | hleS
                · rw [hnfS] at htr; cases htr
                · right; omega
              · left; cases hc : isConstEofPtr nibA <;> simp_all
            have hbdB : bibA = 0 → ∀ errs, C.Space.get hA ctx.rerr = some errs → 0 < errs.size →
                errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
              nibBibTrack_bd hp0 hpA htrA (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
            obtain ⟨resB, hB, hrunB, hpB, hdB, hmrB, _, hcpB, _, _, _, hbyB, _, hcoB, hpostB⟩ :=
              inputByte_parser hpA nibA bibA hcurA hbdB
            have hstCB := decompHeaderStable_trans hp2 hpA hstCA (decompHeaderStable_of_same hdB hmrB hcpB)
            cases resB with
            | none =>
              refine ⟨0, { s with done := true, ret := .ok false }, hB, ?_, by omega, hpB, hstCB,
                fun _ => ⟨rfl, by simp⟩, fun hno => by simp at hno⟩
              rw [C.run_bind, hrunA]; dsimp only
              rw [C.run_bind, hrunB]; rfl
            | some pB =>
              rcases pB with ⟨cbyte, nibB, bibB⟩
              rcases hpostB with ⟨_, _, hcurB, hceB⟩
              obtain ⟨htrB, hstrB⟩ := nibBibTrack_inputByte_step hp0 hpA htrA (by omega) (by omega) hceB
              have hstrB' : ∀ srcs0, C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
                  isConstEofPtr nibB = true ∨ bibB.toNat + 3 + 2 * (s.i + 1) ≤ srcs0[0]!.bytesInBuffer.toNat := by
                intro s0 hs0 hss0
                by_cases hnfB : isConstEofPtr nibB = false
                · simp only [hnfB, ↓reduceIte] at hceB
                  rcases hceB with ⟨hnfA, _, hbibB, _⟩
                  rcases hstrA' s0 hs0 hss0 with htr | hleA
                  · rw [hnfA] at htr; cases htr
                  · right; omega
                · left; cases hc : isConstEofPtr nibB <;> simp_all
              obtain ⟨dcsB, hgdcB, hszdcB, hcompB_ne, hclB, _⟩ := parserEnv_get_compLive hpB
              have hgdcAB : C.Space.get hB (C.DecompRef.decomp ctx.bdc) = some dcsB := hgdcB
              -- Relate dcsB[0]! back to hCur via hdA, hdB
              have hgdc_cur : C.Space.get hCur (C.DecompRef.decomp ctx.bdc) = some dcsB := by
                dsimp only [C.Space.get] at hgdcB ⊢; rw [hdB, hdA] at hgdcB; exact hgdcB
              obtain ⟨hciB, hncB, hcisB, hccSzB, herrB, hisnB, hprevB⟩ := hdcS dcsB hgdc_cur hszdcB
              have hldcB := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcB hszdcB
              obtain ⟨_, rcpB, csB, hrefB, hgcsB, hlecsB⟩ := hclB (by rw [hciB]; simp)
              have hrcpEqB : rcpB = rcp := by
                injection (hciB.symm.trans hrefB) with h1; exact h1.symm
              rw [hrcpEqB] at hgcsB hrefB
              let lim := min dcsB[0]!.numComponents.toInt.toNat MAX_COMPS_IN_SCAN.toInt.toNat
              have hlimLe : lim ≤ dcsB[0]!.numComponents.toInt.toNat := Nat.min_le_left _ _
              let FindInv : Nat → Option C.CompPtr → C.Heap → Prop := fun _ found hF =>
                hF = hB ∧ (found = none ∨ ∃ off, off < lim ∧ found = some (.ref rcp off))
              obtain ⟨found, hF, hforFind, hFindInv⟩ := forIn_range_inv FindInv
                (fun (ci : Nat) (found0 : Option C.CompPtr) => do
                  if found0.isNone then
                    let cp ← Ptr.add dcsB[0]!.compInfo (Int.ofNat ci)
                    let comp ← Ptr.load cp
                    if cc == comp.componentId && dcsB[0]!.curCompInfo[ci]! == .null then
                      return .yield (some cp)
                    else
                      return .yield found0
                  else
                    return .yield found0)
                lim
                (fun ci hci found0 hF0 ⟨hFEq, hFval⟩ => by
                  rw [hFEq]
                  cases found0 with
                  | none =>
                    have hciCs : ci < csB.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hci hlimLe) hlecsB
                    have hadd := ptr_add_ok (r := rcp) (xs := csB) (off := 0) (k := Int.ofNat ci) hgcsB
                      (Nat.zero_le _) (by rw [Int.ofNat_eq_natCast]; omega)
                      (by rw [Int.ofNat_eq_natCast]; omega)
                    have hlcp := ptr_load_ok (r := rcp) (off := ci) hgcsB hciCs
                    have hzero : (((0 : Nat) : Int) + Int.ofNat ci).toNat = ci := by
                      change ((0 : Int) + (ci : Int)).toNat = ci; omega
                    by_cases hmatch : (cc == csB[ci]!.componentId && dcsB[0]!.curCompInfo[ci]! == .null) = true
                    · refine ⟨.yield (some (.ref rcp ci)), hB, ?_, rfl, Or.inr ⟨ci, hci, rfl⟩⟩
                      simp only [Option.isNone, ↓reduceIte]
                      rw [hciB, C.run_bind, hadd]; dsimp only
                      rw [hzero, C.run_bind, hlcp]; dsimp only
                      simp only [hmatch, ↓reduceIte]; rfl
                    · have hmatchF : (cc == csB[ci]!.componentId && dcsB[0]!.curCompInfo[ci]! == .null) = false :=
                        Bool.eq_false_iff.mpr hmatch
                      refine ⟨.yield none, hB, ?_, rfl, Or.inl rfl⟩
                      simp only [Option.isNone, ↓reduceIte]
                      rw [hciB, C.run_bind, hadd]; dsimp only
                      rw [hzero, C.run_bind, hlcp]; dsimp only
                      simp only [hmatchF, Bool.false_eq_true, ↓reduceIte]; rfl
                  | some cp0 =>
                    refine ⟨.yield (some cp0), hB, rfl, rfl, hFval⟩)
                ⟨rfl, Or.inl rfl⟩
              rcases hFindInv with ⟨hFEq, hFval⟩
              rw [hFEq] at hforFind
              cases found with
              | none =>
                obtain ⟨hE, herr_run, hpE, hstBE⟩ := errexit1_stable_parser hpB JERR_BAD_COMPONENT_ID cc
                have herr_run' : C.run (errexit1 dcsB[0]!.err JERR_BAD_COMPONENT_ID cc) hB =
                    .ok (.errExit JERR_BAD_COMPONENT_ID, hE) := by
                  rw [herrB, herrRef]; exact herr_run
                have hstCE := decompHeaderStable_trans hp2 hpB hstCB hstBE
                refine ⟨0, { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }, hE, ?_, by omega, hpE, hstCE,
                  fun _ => ⟨rfl, by simp⟩, fun hno => by simp at hno⟩
                rw [C.run_bind, hrunA]; dsimp only
                rw [C.run_bind, hrunB]; dsimp only
                rw [C.run_bind, hldcB]; dsimp only
                rw [C.run_bind]; erw [hforFind]; dsimp only
                rw [C.run_bind, herr_run']; rfl
              | some cp =>
                rcases hFval with hAbs | ⟨off, hoffLim, hcpEq⟩
                · cases hAbs
                have hcpEq' : cp = .ref rcp off := by injection hcpEq
                subst hcpEq'
                have hoffCs : off < csB.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hoffLim hlimLe) hlecsB
                have hoffNc : off < dcsB[0]!.numComponents.toInt.toNat := Nat.lt_of_lt_of_le hoffLim hlimLe
                have hsiCc : s.i < dcsB[0]!.curCompInfo.size := by rw [hccSzB]; omega
                have hroDc : C.Space.ro hB (C.DecompRef.decomp ctx.bdc) = false := rfl
                let dcNew := { dcsB[0]! with curCompInfo := dcsB[0]!.curCompInfo.set! s.i (.ref rcp off) }
                have hstDc := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcNew) hgdcB hroDc hszdcB
                let hD := C.Space.put hB (C.DecompRef.decomp ctx.bdc) (dcsB.set! 0 dcNew)
                have hpD : ParserEnv ctx hD := by
                  have hpB0 := hpB
                  obtain ⟨_, _, dcsB0, dcB0, _, _, _, _, mrksB0, _,
                    hgdcB0, _, hdcB0, _, _, _, _, _,
                    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                    _, _, _, _, _, _, _, _,
                    _, hgmrkB0, _, _, _, _, _, _, _,
                    _, _, _, _, _, _, _, _, _,
                    _, _, hsawB0, _, hqtSzB, hqtB, hdhSzB, hdhB, hahSzB, hahB, hccSzB0, hisnB0⟩ := hpB0
                  have hdBEq : dcsB = dcsB0 := Option.some.inj (hgdcB.symm.trans hgdcB0)
                  subst hdcB0
                  rw [← hdBEq] at hqtSzB hqtB hdhSzB hdhB hahSzB hahB hccSzB0 hisnB0 hsawB0
                  refine parserEnv_put_dc hpB hgdcB hszdcB rfl rfl rfl rfl rfl rfl (Or.inl rfl)
                    (Or.inl ⟨rfl, rfl⟩)
                    ⟨hqtSzB, hqtB⟩ ⟨hdhSzB, hdhB⟩ ⟨hahSzB, hahB⟩
                    (by dsimp only [dcNew]; simp [hccSzB0])
                    hisnB0
                    (fun mrks' hgm' _ hsne => by
                      have hmEq := Option.some.inj (hgm'.symm.trans hgmrkB0); subst hmEq
                      exact hsawB0 hsne)
                have hstBD : DecompHeaderStable ctx hB hD := by
                  refine ⟨fun d1 d2 h1 _ h2 _ => ?_, fun m1 m2 h1 _ h2 _ => ?_, fun r c i hrc hi => ?_⟩
                  · have hd1Eq := Option.some.inj (h1.symm.trans hgdcB); rw [hd1Eq]
                    have hgD : C.Space.get hD (C.DecompRef.decomp ctx.bdc) = some (dcsB.set! 0 dcNew) := by
                      simp [hD, C.Space.get, C.Space.put]
                    have hd2Eq := Option.some.inj (h2.symm.trans hgD); rw [hd2Eq]
                    rw [set0_bang_m dcsB hszdcB dcNew]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                  · have hmD : hD.markers = hB.markers := rfl
                    dsimp only [C.Space.get] at h1 h2; rw [hmD] at h2
                    rw [Option.some.inj (h2.symm.trans h1)]
                  · exact ⟨c, hrc, hi, rfl, rfl, rfl⟩
                have hgcsD : C.Space.get hD rcp = some csB := hgcsB
                have hlcpD := ptr_load_ok (r := rcp) (off := off) hgcsD hoffCs
                have hroCp : C.Space.ro hD rcp = false := rfl
                let compOld := csB[off]!
                let compNew := { compOld with dcTblNo := (cbyte >>> 4) &&& 15, acTblNo := cbyte &&& 15 }
                have hstCp := ptr_store_ok (r := rcp) (off := off) (v := compNew) hgcsD hroCp hoffCs
                let hCp := C.Space.put hD rcp (csB.set! off compNew)
                have hpCp : ParserEnv ctx hCp := parserEnv_put_comp hpD hgcsD
                have hstDCp : DecompHeaderStable ctx hD hCp := by
                  refine ⟨fun d1 d2 h1 _ h2 _ => ?_, fun m1 m2 h1 _ h2 _ => ?_, fun r c i hrc hi => ?_⟩
                  · have hdCp : hCp.decomps = hD.decomps := rfl
                    dsimp only [C.Space.get] at h1 h2; rw [hdCp] at h2
                    rw [Option.some.inj (h2.symm.trans h1)]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                  · have hmCp : hCp.markers = hD.markers := rfl
                    dsimp only [C.Space.get] at h1 h2; rw [hmCp] at h2
                    rw [Option.some.inj (h2.symm.trans h1)]
                  · by_cases hrcEq : r = rcp
                    · rw [hrcEq] at hrc ⊢
                      have hcsEq := Option.some.inj (hrc.symm.trans hgcsD)
                      have hgetCp : C.Space.get hCp rcp = some (csB.set! off compNew) := by
                        simp [hCp, C.Space.get, C.Space.put]
                      refine ⟨csB.set! off compNew, hgetCp, by rw [hcsEq] at hi; simpa using hi, ?_⟩
                      rw [hcsEq]
                      by_cases hio : i = off
                      · rw [hio, arr_set_bang_self _ hoffCs]; exact ⟨rfl, rfl, rfl⟩
                      · rw [arr_set_bang_ne _ (hcsEq ▸ hi) hoffCs hio]; exact ⟨rfl, rfl, rfl⟩
                    · have hgetCp : C.Space.get hCp r = C.Space.get hD r := by
                        cases r; rcases rcp with ⟨bc⟩
                        simp only [hCp, C.Space.get, C.Space.put]
                        exact C.upd_ne _ _ _ _ (fun h => hrcEq (congrArg C.CompRef.comp h))
                      rw [hgetCp]; exact ⟨c, hrc, hi, rfl, rfl, rfl⟩
                have htr3_bd : C.Space.get hCp ctx.rerr = C.Space.get hB ctx.rerr := rfl
                obtain ⟨hTr, htr3_run, hpTr, hdTr, hmrTr, _, _, hcpTr, _, _, _, hbyTr, _, hcoTr, hnwTr⟩ :=
                  tracems3_nonneg_parser hpCp 1 JTRC_SOS_COMPONENT cc compNew.dcTblNo compNew.acTblNo (by decide)
                have htr3_run' : C.run (tracems3 dcsB[0]!.err 1 JTRC_SOS_COMPONENT cc compNew.dcTblNo compNew.acTblNo) hCp =
                    .ok ((), hTr) := by
                  rw [herrB, herrRef]; exact htr3_run
                have hstCpTr : DecompHeaderStable ctx hCp hTr := decompHeaderStable_of_same hdTr hmrTr hcpTr
                have hstBTr : DecompHeaderStable ctx hB hTr :=
                  decompHeaderStable_trans hpB hpCp (decompHeaderStable_trans hpB hpD hstBD hstDCp) hstCpTr
                have hstCTr := decompHeaderStable_trans hp2 hpB hstCB hstBTr
                have hgdcD : C.Space.get hD (C.DecompRef.decomp ctx.bdc) = some (dcsB.set! 0 dcNew) := by
                  simp [hD, C.Space.get, C.Space.put]
                have hgdcTr : C.Space.get hTr (C.DecompRef.decomp ctx.bdc) = some (dcsB.set! 0 dcNew) := by
                  dsimp only [C.Space.get]; rw [hdTr]; exact hgdcD
                have hszdcTr : 0 < (dcsB.set! 0 dcNew).size := by simpa using hszdcB
                have hldcTr := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcTr hszdcTr
                have hdcNewEq : (dcsB.set! 0 dcNew)[0]! = dcNew := set0_bang_m dcsB hszdcB dcNew
                let DupInv : Nat → Option SosLoopState × Unit → C.Heap → Prop := fun idx res hX =>
                  ParserEnv ctx hX ∧ DecompHeaderStable ctx hTr hX ∧
                  ((res.1 = none ∧ hX = hTr) ∨
                    (idx = s.i ∧ ∃ stErr, res.1 = some stErr ∧ stErr.done = true ∧ stErr.ret ≠ .ok true))
                obtain ⟨dupRes, hDup, hforDup, hDupInv⟩ := forIn_range_inv DupInv
                  (fun (pi : Nat) (_ : Option SosLoopState × Unit) =>
                    if (dcNew.curCompInfo[pi]! == .ref rcp off) = true then do
                      let _ ← errexit1 dcNew.err JERR_BAD_COMPONENT_ID cc
                      pure (ForInStep.done (some { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }, ()))
                    else
                      pure (ForInStep.yield (none, ())))
                  s.i
                  (fun pi hpi res0 hX0 hXinv => by
                    rcases hXinv with ⟨hpX0, hstX0, ⟨hresN, hXEq⟩ | ⟨hpiEq, _⟩⟩
                    · rw [hXEq]
                      by_cases heq : (dcNew.curCompInfo[pi]! == .ref rcp off) = true
                      · obtain ⟨hE, herr_run, hpE, hstXE⟩ := errexit1_stable_parser hpTr JERR_BAD_COMPONENT_ID cc
                        have hdcNewErr : dcNew.err = .ref ctx.rerr 0 := by
                          dsimp only [dcNew]; rw [herrB, herrRef]
                        have herr_run' : C.run (errexit1 dcNew.err JERR_BAD_COMPONENT_ID cc) hTr =
                            .ok (.errExit JERR_BAD_COMPONENT_ID, hE) := by
                          rw [hdcNewErr]; exact herr_run
                        refine ⟨.done (some { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }, ()), hE, ?_,
                          hpE, hstXE, Or.inr ⟨rfl, _, rfl, rfl, by simp⟩⟩
                        simp only [heq, ↓reduceIte, C.run_bind, herr_run']; rfl
                      · have hne : (dcNew.curCompInfo[pi]! == .ref rcp off) = false := Bool.eq_false_iff.mpr heq
                        refine ⟨.yield (none, ()), hTr, ?_, hpTr, decompHeaderStable_refl ctx hTr,
                          Or.inl ⟨(rfl : ((none : Option SosLoopState), ()).1 = none), rfl⟩⟩
                        simp only [hne, Bool.false_eq_true, ↓reduceIte]; rfl
                    · exact absurd hpiEq (by omega))
                  ⟨hpTr, decompHeaderStable_refl ctx hTr,
                    Or.inl ⟨(rfl : ((none : Option SosLoopState), ()).1 = none), rfl⟩⟩
                rcases dupRes with ⟨dupFst, ⟨⟩⟩
                rcases hDupInv with ⟨hpDup, hstTrDup, ⟨hdupN, hDupEq⟩ | ⟨_, stErr, hdupS, hstErrD, hstErrNe⟩⟩
                · rw [hDupEq] at hforDup
                  have htrTr := nibBibTrack_err_nw_same hpCp htrB hnwTr
                  have hcurTr : CurValid hTr nibB bibB := curValid_bytes_irrel hbyTr hcoTr hcurB
                  have hrunStep : C.run ((do
                      match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
                      | none => return { s with done := true, ret := .ok false }
                      | some (cc, nibA, bibA) =>
                        match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
                        | none => return { s with done := true, ret := .ok false }
                        | some (cbyte, nibB, bibB) =>
                          let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                          let lim := min dcCur.numComponents.toInt.toNat MAX_COMPS_IN_SCAN.toInt.toNat
                          let mut found : Option C.CompPtr := none
                          for ci in List.range lim do
                            if found.isNone then
                              let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
                              let comp ← Ptr.load cp
                              if cc == comp.componentId && dcCur.curCompInfo[ci]! == .null then
                                found := some cp
                          match found with
                          | none =>
                            let _ ← errexit1 dcCur.err JERR_BAD_COMPONENT_ID cc
                            return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
                          | some cp =>
                            Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0)
                              { dcCur with curCompInfo := dcCur.curCompInfo.set! s.i cp }
                            let comp ← Ptr.load cp
                            let comp' := { comp with dcTblNo := (cbyte >>> 4) &&& 15, acTblNo := cbyte &&& 15 }
                            Ptr.store cp comp'
                            tracems3 dcCur.err 1 JTRC_SOS_COMPONENT cc comp'.dcTblNo comp'.acTblNo
                            let dcChk ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                            for pi in List.range s.i do
                              if dcChk.curCompInfo[pi]! == cp then
                                let _ ← errexit1 dcChk.err JERR_BAD_COMPONENT_ID cc
                                return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
                            return { done := false, ret := .ok true, i := s.i + 1, nib := nibB, bib := bibB }) :
                      C.M SosLoopState) hCur =
                      .ok ({ done := false, ret := .ok true, i := s.i + 1, nib := nibB, bib := bibB }, hTr) := by
                    rw [C.run_bind, hrunA]; dsimp only
                    rw [C.run_bind, hrunB]; dsimp only
                    rw [C.run_bind, hldcB]; dsimp only
                    rw [C.run_bind]; erw [hforFind]; dsimp only
                    rw [C.run_bind, hstDc]; dsimp only
                    rw [C.run_bind, hlcpD]; dsimp only
                    rw [C.run_bind, hstCp]; dsimp only
                    rw [C.run_bind, htr3_run']; dsimp only
                    rw [C.run_bind, hldcTr]; dsimp only
                    rw [hdcNewEq, C.run_bind]; erw [hforDup]; dsimp only
                    dsimp only at hdupN; rw [hdupN]; rfl
                  refine ⟨k - 1, { done := false, ret := .ok true, i := s.i + 1, nib := nibB, bib := bibB },
                    hTr, hrunStep, by omega, hpTr, hstCTr, (fun hd => by cases hd), fun _ => ?_⟩
                  · refine ⟨by dsimp only; omega, by dsimp only; omega, hcurTr, nibBibTrack_mono htrTr (by omega) ?_, hstrB', fun dcsT hgT _ => ?_⟩
                    · rw [show ((s.i + 1 : Nat) : Int) = (s.i : Int) + 1 from by omega]; omega
                    · have hEqT := Option.some.inj (hgT.symm.trans hgdcTr); subst hEqT
                      rw [hdcNewEq]
                      refine ⟨by dsimp only [dcNew]; exact hciB, hncB, hcisB, by dsimp only [dcNew]; simp [hccSzB],
                        by dsimp only [dcNew]; exact herrB, hisnB, fun j hj => ?_⟩
                      have hgcsTr : C.Space.get hTr rcp = some (csB.set! off compNew) := by
                        rcases hrC : rcp with ⟨bc⟩
                        have hgcC : C.Space.get hCp rcp = some (csB.set! off compNew) := by
                          simp [hCp, C.Space.get, C.Space.put]
                        have hcpEq : hTr.comps = hCp.comps := hcpTr
                        simp only [C.Space.get, hrC, hcpEq] at hgcC ⊢; exact hgcC
                      by_cases hjs : j = s.i
                      · subst hjs; dsimp only [dcNew]
                        rw [arr_set_bang_self _ hsiCc]
                        exact ⟨off, csB.set! off compNew, rfl, hgcsTr, by simpa using hoffCs, hoffNc⟩
                      · have hjlt : j < s.i := by dsimp only at hj; omega
                        dsimp only [dcNew]
                        rw [arr_set_bang_ne _ (by rw [hccSzB]; omega) hsiCc hjs]
                        obtain ⟨offJ, csJ, hrefJ, hgcsJ, hoffJ, hoffJNc⟩ := hprevB j hjlt
                        have hgcsB_cur : C.Space.get hCur rcp = some csB := by
                          rcases hrC' : rcp with ⟨bc'⟩
                          simp only [C.Space.get, hrC'] at hgcsB ⊢; rw [hcpB, hcpA] at hgcsB; exact hgcsB
                        have hcsJEq := Option.some.inj (hgcsJ.symm.trans hgcsB_cur)
                        exact ⟨offJ, csB.set! off compNew, hrefJ, hgcsTr, by rw [← hcsJEq]; simpa using hoffJ, hoffJNc⟩
                · dsimp only at hdupS; subst hdupS
                  have hstCDup := decompHeaderStable_trans hp2 hpTr hstCTr hstTrDup
                  have hrunStep : C.run ((do
                      match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
                      | none => return { s with done := true, ret := .ok false }
                      | some (cc, nibA, bibA) =>
                        match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
                        | none => return { s with done := true, ret := .ok false }
                        | some (cbyte, nibB, bibB) =>
                          let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                          let lim := min dcCur.numComponents.toInt.toNat MAX_COMPS_IN_SCAN.toInt.toNat
                          let mut found : Option C.CompPtr := none
                          for ci in List.range lim do
                            if found.isNone then
                              let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
                              let comp ← Ptr.load cp
                              if cc == comp.componentId && dcCur.curCompInfo[ci]! == .null then
                                found := some cp
                          match found with
                          | none =>
                            let _ ← errexit1 dcCur.err JERR_BAD_COMPONENT_ID cc
                            return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
                          | some cp =>
                            Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0)
                              { dcCur with curCompInfo := dcCur.curCompInfo.set! s.i cp }
                            let comp ← Ptr.load cp
                            let comp' := { comp with dcTblNo := (cbyte >>> 4) &&& 15, acTblNo := cbyte &&& 15 }
                            Ptr.store cp comp'
                            tracems3 dcCur.err 1 JTRC_SOS_COMPONENT cc comp'.dcTblNo comp'.acTblNo
                            let dcChk ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                            for pi in List.range s.i do
                              if dcChk.curCompInfo[pi]! == cp then
                                let _ ← errexit1 dcChk.err JERR_BAD_COMPONENT_ID cc
                                return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
                            return { done := false, ret := .ok true, i := s.i + 1, nib := nibB, bib := bibB }) :
                      C.M SosLoopState) hCur = .ok (stErr, hDup) := by
                    rw [C.run_bind, hrunA]; dsimp only
                    rw [C.run_bind, hrunB]; dsimp only
                    rw [C.run_bind, hldcB]; dsimp only
                    rw [C.run_bind]; erw [hforFind]; dsimp only
                    rw [C.run_bind, hstDc]; dsimp only
                    rw [C.run_bind, hlcpD]; dsimp only
                    rw [C.run_bind, hstCp]; dsimp only
                    rw [C.run_bind, htr3_run']; dsimp only
                    rw [C.run_bind, hldcTr]; dsimp only
                    rw [hdcNewEq, C.run_bind]; erw [hforDup]; rfl
                  refine ⟨0, stErr, hDup, hrunStep, by omega, hpDup, hstCDup, (fun _ => ⟨rfl, hstErrNe⟩),
                    fun hno => by simp [hstErrD] at hno⟩
        · have hcondF : (!s.done && s.i < nNat) = false := by cases hc : (!s.done && s.i < nNat) <;> simp_all
          refine ⟨false, s, hCur, (by simp only [C.run, pure, hcondF]), ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨hpC, hstC, fun hd => (hdC hd).2, fun hnd => ?_⟩
          have hsDoneF : s.done = false := by cases hc : s.done <;> simp_all
          have hsiEq : s.i = nNat := by
            obtain ⟨_, hle, _⟩ := hactC hnd
            simp [hsDoneF] at hcondF
            omega
          obtain ⟨_, _, hcurS, htrS, hstrS, hdcS⟩ := hactC hnd
          refine ⟨hcurS, nibBibTrack_mono htrS (by omega) (by omega), fun s0 hs0 hss0 => ?_, fun dcsL hgL hszL => ?_⟩
          · rcases hstrS s0 hs0 hss0 with ht | hle
            · left; exact ht
            · right; rw [hsiEq] at hle; omega
          · obtain ⟨hciL, _, hcisL, hccSzL, _, hisnL, hprevL⟩ := hdcS dcsL hgL hszL
            refine ⟨hcisL, hccSzL, hisnL, fun j hj => ?_⟩
            rw [← hsiEq] at hj
            exact hprevL j hj)
      hk0Lt hinit
  rcases hpost with ⟨hpL, hstL, hnrL, hfinL⟩
  exact ⟨st, hL, hloop, hpL, hstL, hnrL, hfinL⟩

def ScanCompsInRange (h : C.Heap) (dc : C.JpegDecompressStruct) : Prop :=
  0 ≤ dc.compsInScan.toInt ∧ dc.compsInScan.toInt ≤ 4 ∧ dc.curCompInfo.size = 4 ∧
  (∀ i < dc.compsInScan.toInt.toNat,
    ∃ rcp offI cs, dc.compInfo = .ref rcp 0 ∧ C.Space.get h rcp = some cs ∧
      offI < dc.numComponents.toInt.toNat ∧ offI < cs.size ∧
      dc.curCompInfo[i]! = .ref rcp offI)

theorem get_sos_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63)
    (hscan : ∀ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      dcs[0]!.inputScanNumber.toInt + 1 < 2 ^ 31) :
    ∃ res h',
      C.run (get_sos (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcStrict srcs0[0]! srcs'[0]! ∧
          (isConstEofPtr srcs'[0]!.nextInputByte = true ∨
            srcs'[0]!.bytesInBuffer.toNat + 8 ≤ srcs0[0]!.bytesInBuffer.toNat)) ∧
        (∀ dcs0 dcs', C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
          C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
          dcs'[0]!.inputScanNumber.toInt = dcs0[0]!.inputScanNumber.toInt + 1 ∧
          ScanCompsInRange h' dcs'[0]! ∧
          (PostSofBase h dcs0[0]! → MultiScanReady h' dcs'[0]!)) ∧
        WarnPotOk ctx h h' (2 ^ 16)
      | _ => True := by
  have hp0 := hp
  obtain ⟨dcs0, hgdc0, hszdc0, kerr0, _, _, _, kmrk0, ksrc0⟩ := parserEnv_get_dc hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _, _, _, _, _, hcur0⟩ := parserEnv_get_src hp
  obtain ⟨mrks0, hgmrk0, hszmrk0, _⟩ := parserEnv_get_mrk hp
  obtain ⟨dcsP, hgdcP, _, hcomp0_ne, hcl0, _⟩ := parserEnv_get_compLive hp
  have hdEq0 := Option.some.inj (hgdcP.symm.trans hgdc0)
  rw [hdEq0] at hcomp0_ne hcl0
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlsrc0 := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc0 hszsrc0
  have hlmrk0 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk0 hszmrk0
  have hlsrc0' : C.run (Ptr.load dcs0[0]!.src) h = .ok (srcs0[0]!, h) := by rw [ksrc0]; exact hlsrc0
  have hlmrk0' : C.run (Ptr.load dcs0[0]!.marker) h = .ok (mrks0[0]!, h) := by rw [kmrk0]; exact hlmrk0
  by_cases hsaw : (mrks0[0]!.sawSOF == 0) = true
  · obtain ⟨hE, herr_run, hpE, hst0E⟩ := errexit_stable_parser hp JERR_SOS_NO_SOF
    have herr_run' : C.run (errexit dcs0[0]!.err JERR_SOS_NO_SOF) h = .ok (.errExit JERR_SOS_NO_SOF, hE) := by
      rw [kerr0]; exact herr_run
    refine ⟨.errExit JERR_SOS_NO_SOF, hE, ?_, hpE, hst0E, trivial⟩
    unfold get_sos
    rw [C.run_bind, hldc0]; dsimp only
    rw [C.run_bind, hlsrc0']; dsimp only
    rw [C.run_bind, hlmrk0']; dsimp only
    simp only [hsaw, ↓reduceIte, C.run_bind, herr_run']; rfl
  · have hsawF : (mrks0[0]!.sawSOF == 0) = false := Bool.eq_false_iff.mpr hsaw
    have hsawNe : mrks0[0]!.sawSOF ≠ 0 := by
      intro h0; simp [h0] at hsawF
    have hcompP0 : dcs0[0]!.compInfo ≠ .null := hcomp0_ne mrks0 hgmrk0 hszmrk0 hsawNe
    obtain ⟨_, rcp, cs0, href0, _, _⟩ := hcl0 hcompP0
    have htr0 := nibBibTrack_init ctx h srcs0 hgsrc0
    have hbd1 : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
        errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
      nibBibTrack_bd hp hp htr0 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
        have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
    obtain ⟨res1, h1, hrun1, hp1, hd1, hmr1, _, hcp1, _, _, _, _, _, _, hpost1⟩ :=
      input2Bytes_parser hp srcs0[0]!.nextInputByte srcs0[0]!.bytesInBuffer hcur0 hbd1
    have hst01 : DecompHeaderStable ctx h h1 := decompHeaderStable_of_same hd1 hmr1 hcp1
    cases res1 with
    | none =>
      refine ⟨.ok false, h1, ?_, hp1, hst01, trivial⟩
      unfold get_sos
      rw [C.run_bind, hldc0]; dsimp only
      rw [C.run_bind, hlsrc0']; dsimp only
      rw [C.run_bind, hlmrk0']; dsimp only
      simp only [hsawF, Bool.false_eq_true, ↓reduceIte, C.run_bind, hrun1]; rfl
    | some p1 =>
      rcases p1 with ⟨lenRaw, nib1, bib1⟩
      rcases hpost1 with ⟨_, _, hcur1, hce1⟩
      obtain ⟨htr1, _⟩ := nibBibTrack_input2Bytes_step hp hp htr0 (by omega) (by omega) hce1
      have hstr1' : ∀ srcs, C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
          isConstEofPtr nib1 = true ∨ bib1.toNat + 2 ≤ srcs[0]!.bytesInBuffer.toNat := by
        intro s0 hs0 _
        by_cases hnf : isConstEofPtr nib1 = false
        · simp only [hnf, ↓reduceIte] at hce1
          have hEq := Option.some.inj (hs0.symm.trans hgsrc0); subst hEq
          right; omega
        · left; cases hc : isConstEofPtr nib1 <;> simp_all
      have hbd2 : bib1 = 0 → ∀ errs, C.Space.get h1 ctx.rerr = some errs → 0 < errs.size →
          errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
        nibBibTrack_bd hp hp1 htr1 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
          have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
      obtain ⟨res2, h2, hrun2, hp2, hd2, hmr2, _, hcp2, _, _, _, _, _, _, hpost2⟩ :=
        inputByte_parser hp1 nib1 bib1 hcur1 hbd2
      have hst02 := decompHeaderStable_trans hp hp1 hst01 (decompHeaderStable_of_same hd2 hmr2 hcp2)
      cases res2 with
      | none =>
        refine ⟨.ok false, h2, ?_, hp2, hst02, trivial⟩
        unfold get_sos
        rw [C.run_bind, hldc0]; dsimp only
        rw [C.run_bind, hlsrc0']; dsimp only
        rw [C.run_bind, hlmrk0']; dsimp only
        simp only [hsawF, Bool.false_eq_true, ↓reduceIte]
        rw [C.run_bind, hrun1]; dsimp only
        rw [C.run_bind, hrun2]; rfl
      | some p2 =>
        rcases p2 with ⟨n, nib2, bib2⟩
        rcases hpost2 with ⟨_, _, hcur2, hce2⟩
        obtain ⟨htr2, _⟩ := nibBibTrack_inputByte_step hp hp1 htr1 (by omega) (by omega) hce2
        have hstr2' : ∀ srcs, C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
            isConstEofPtr nib2 = true ∨ bib2.toNat + 3 ≤ srcs[0]!.bytesInBuffer.toNat := by
          intro s0 hs0 hss0
          by_cases hnf2 : isConstEofPtr nib2 = false
          · simp only [hnf2, ↓reduceIte] at hce2
            rcases hce2 with ⟨hnf1, _, _, _⟩
            rcases hstr1' s0 hs0 hss0 with htr | hle1
            · rw [hnf1] at htr; cases htr
            · right; omega
          · left; cases hc : isConstEofPtr nib2 <;> simp_all
        obtain ⟨h2T, htrT_run, hp2T, hd2T, hmr2T, _, _, hcp2T, _, _, _, hby2T, _, hco2T, hnw2T⟩ :=
          tracems1_nonneg_parser hp2 1 JTRC_SOS n (by decide)
        have htrT_run' : C.run (tracems1 dcs0[0]!.err 1 JTRC_SOS n) h2 = .ok ((), h2T) := by
          rw [kerr0]; exact htrT_run
        have hst02T := decompHeaderStable_trans hp hp2 hst02 (decompHeaderStable_of_same hd2T hmr2T hcp2T)
        have htr2T := nibBibTrack_err_nw_same hp2 htr2 hnw2T
        have hcur2T : CurValid h2T nib2 bib2 := curValid_bytes_irrel hby2T hco2T hcur2
        have hpreEq : C.run (get_sos (.ref (C.DecompRef.decomp ctx.bdc) 0)) h =
            C.run (do
              if lenRaw.toInt != n.toInt * 2 + 6 || n < 1 || n > MAX_COMPS_IN_SCAN then
                let _ ← errexit dcs0[0]!.err JERR_BAD_LENGTH
                return .errExit JERR_BAD_LENGTH
              let dc1 ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
              Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0)
                { dc1 with compsInScan := n, curCompInfo := Array.replicate 4 .null }
              let nNat := n.toInt.toNat
              let st ← cwhile
                (fun (s : SosLoopState) => pure (!s.done && s.i < nNat, s))
                (fun (s : SosLoopState) => do
                  match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
                  | none => return { s with done := true, ret := .ok false }
                  | some (cc, nibA, bibA) =>
                    match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibA bibA) with
                    | none => return { s with done := true, ret := .ok false }
                    | some (cbyte, nibB, bibB) =>
                      let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                      let lim := min dcCur.numComponents.toInt.toNat MAX_COMPS_IN_SCAN.toInt.toNat
                      let mut found : Option C.CompPtr := none
                      for ci in List.range lim do
                        if found.isNone then
                          let cp ← Ptr.add dcCur.compInfo (Int.ofNat ci)
                          let comp ← Ptr.load cp
                          if cc == comp.componentId && dcCur.curCompInfo[ci]! == .null then
                            found := some cp
                      match found with
                      | none =>
                        let _ ← errexit1 dcCur.err JERR_BAD_COMPONENT_ID cc
                        return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
                      | some cp =>
                        Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0)
                          { dcCur with curCompInfo := dcCur.curCompInfo.set! s.i cp }
                        let comp ← Ptr.load cp
                        let comp' := { comp with dcTblNo := (cbyte >>> 4) &&& 15, acTblNo := cbyte &&& 15 }
                        Ptr.store cp comp'
                        tracems3 dcCur.err 1 JTRC_SOS_COMPONENT cc comp'.dcTblNo comp'.acTblNo
                        let dcChk ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                        for pi in List.range s.i do
                          if dcChk.curCompInfo[pi]! == cp then
                            let _ ← errexit1 dcChk.err JERR_BAD_COMPONENT_ID cc
                            return { s with done := true, ret := .errExit JERR_BAD_COMPONENT_ID }
                        return { done := false, ret := .ok true, i := s.i + 1, nib := nibB, bib := bibB })
                { done := false, ret := .ok true, i := 0, nib := nib2, bib := bib2 }
              if st.done then
                return st.ret
              match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib) with
              | none => return .ok false
              | some (ssVal, nibS, bibS) =>
                let dcS ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcS with ss := ssVal }
                match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibS bibS) with
                | none => return .ok false
                | some (seVal, nibE, bibE) =>
                  let dcE ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                  Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcE with se := seVal }
                  match (← inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibE bibE) with
                  | none => return .ok false
                  | some (ahAl, nibEnd, bibEnd) =>
                    let dcF ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                    let dcF' := { dcF with ah := (ahAl >>> 4) &&& 15, al := ahAl &&& 15 }
                    Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) dcF'
                    tracems4 dcF'.err 1 JTRC_SOS_PARAMS dcF'.ss dcF'.se dcF'.ah dcF'.al
                    let mrkF ← Ptr.load dcF'.marker
                    Ptr.store dcF'.marker { mrkF with nextRestartNum := 0 }
                    let isn ← i32Add dcF'.inputScanNumber 1
                    let dcF2 ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                    Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcF2 with inputScanNumber := isn }
                    inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) nibEnd bibEnd
                    return .ok true) h2T := by
          unfold get_sos
          rw [C.run_bind, hldc0]; dsimp only
          rw [C.run_bind, hlsrc0']; dsimp only
          rw [C.run_bind, hlmrk0']; dsimp only
          simp only [hsawF, Bool.false_eq_true, ↓reduceIte]
          rw [C.run_bind, hrun1]; dsimp only
          rw [C.run_bind, hrun2]; dsimp only
          rw [C.run_bind, htrT_run']; rfl
        by_cases hBad : (lenRaw.toInt != n.toInt * 2 + 6 || n < 1 || n > MAX_COMPS_IN_SCAN) = true
        · obtain ⟨hE, herr_run, hpE, hstTE⟩ := errexit_stable_parser hp2T JERR_BAD_LENGTH
          have herr_run' : C.run (errexit dcs0[0]!.err JERR_BAD_LENGTH) h2T = .ok (.errExit JERR_BAD_LENGTH, hE) := by
            rw [kerr0]; exact herr_run
          refine ⟨.errExit JERR_BAD_LENGTH, hE, ?_, hpE, decompHeaderStable_trans hp hp2T hst02T hstTE, trivial⟩
          rw [hpreEq]; simp only [hBad, ↓reduceIte, C.run_bind, herr_run']; rfl
        · have hBadF : (lenRaw.toInt != n.toInt * 2 + 6 || n < 1 || n > MAX_COMPS_IN_SCAN) = false :=
            Bool.eq_false_iff.mpr hBad
          have hn1 : 1 ≤ n.toInt.toNat := by
            by_cases hlt : n < 1
            · have : (lenRaw.toInt != n.toInt * 2 + 6 || n < 1 || n > MAX_COMPS_IN_SCAN) = true := by simp [hlt]
              rw [this] at hBadF; cases hBadF
            · have hle1 : (1 : Int32) ≤ n := Int32.not_lt.mp hlt
              have hle1' : (1 : Int32).toInt ≤ n.toInt := Int32.le_iff_toInt_le.mp hle1
              have h1 : (1 : Int32).toInt = 1 := by decide
              omega
          have hn4 : n.toInt.toNat ≤ 4 := by
            by_cases hgt : n > MAX_COMPS_IN_SCAN
            · have : (lenRaw.toInt != n.toInt * 2 + 6 || n < 1 || n > MAX_COMPS_IN_SCAN) = true := by simp [hgt]
              rw [this] at hBadF; cases hBadF
            · have hleM : n ≤ MAX_COMPS_IN_SCAN := Int32.not_lt.mp hgt
              have hleM' : n.toInt ≤ MAX_COMPS_IN_SCAN.toInt := Int32.le_iff_toInt_le.mp hleM
              have hmax : MAX_COMPS_IN_SCAN.toInt = 4 := by decide
              omega
          obtain ⟨dcsT, hgdcT, hszdcT, kerrT, _⟩ := parserEnv_get_dc hp2T
          have hgdc0_T : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcsT := by
            have hd0T : h2T.decomps = h.decomps := hd2T.trans (hd2.trans hd1)
            dsimp only [C.Space.get] at hgdcT ⊢; rw [hd0T] at hgdcT; exact hgdcT
          have hdcsTEq : dcsT = dcs0 := Option.some.inj (hgdc0_T.symm.trans hgdc0)
          rw [hdcsTEq] at hgdcT hszdcT
          have hldcT := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcT hszdcT
          have hroT : C.Space.ro h2T (C.DecompRef.decomp ctx.bdc) = false := rfl
          let dc1' := { dcs0[0]! with compsInScan := n, curCompInfo := Array.replicate 4 .null }
          have hst1' := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc1') hgdcT hroT hszdcT
          let h1' := C.Space.put h2T (C.DecompRef.decomp ctx.bdc) (dcs0.set! 0 dc1')
          have hp1' : ParserEnv ctx h1' := by
            have hp2T0 := hp2T
            obtain ⟨_, _, dcs20, dc20, _, _, _, _, mrks20, _, hgdc20, _, hdc20, _, _, _, _, _,
              _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
              _, hgmrk20, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
              _, _, hsaw20, _, hqtSz2, hqt2, hdhSz2, hdh2, hahSz2, hah2, _, hisn2⟩ := hp2T0
            have h2Eq := Option.some.inj (hgdcT.symm.trans hgdc20)
            subst hdc20
            rw [← h2Eq] at hqtSz2 hqt2 hdhSz2 hdh2 hahSz2 hah2 hisn2 hsaw20
            refine parserEnv_put_dc hp2T hgdcT hszdcT rfl rfl rfl rfl rfl rfl (Or.inl rfl)
              (Or.inl ⟨rfl, rfl⟩)
              ⟨hqtSz2, hqt2⟩ ⟨hdhSz2, hdh2⟩ ⟨hahSz2, hah2⟩
              (by dsimp only [dc1']; simp)
              hisn2
              (fun mrks' hgm' _ hsne => by
                have hmEq := Option.some.inj (hgm'.symm.trans hgmrk20); subst hmEq
                exact hsaw20 hsne)
          have hstT1' : DecompHeaderStable ctx h2T h1' := by
            refine ⟨fun d1 d2 h1d _ h2d _ => ?_, fun m1 m2 h1m _ h2m _ => ?_, fun r c i hrc hi => ?_⟩
            · have h1dEq := Option.some.inj (h1d.symm.trans hgdcT); rw [h1dEq]
              have hgD : C.Space.get h1' (C.DecompRef.decomp ctx.bdc) = some (dcs0.set! 0 dc1') := by
                simp [h1', C.Space.get, C.Space.put]
              have h2dEq := Option.some.inj (h2d.symm.trans hgD); rw [h2dEq]
              rw [set0_bang_m dcs0 hszdcT dc1']; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            · have hm1' : h1'.markers = h2T.markers := rfl
              dsimp only [C.Space.get] at h1m h2m; rw [hm1'] at h2m
              rw [Option.some.inj (h2m.symm.trans h1m)]
            · exact ⟨c, hrc, hi, rfl, rfl, rfl⟩
          have hst01' := decompHeaderStable_trans hp hp2T hst02T hstT1'
          have hcp01' : CompPreserve h h1' := hst01'.2.2
          obtain ⟨dcs1', hgdc1', hszdc1', _, hcl1', _⟩ := parserEnv_get_compLive hp1'
          have hgdc1'_val : C.Space.get h1' (C.DecompRef.decomp ctx.bdc) = some (dcs0.set! 0 dc1') := by
            simp [h1', C.Space.get, C.Space.put]
          have hdcs1Eq : dcs1' = dcs0.set! 0 dc1' := Option.some.inj (hgdc1'.symm.trans hgdc1'_val)
          rw [hdcs1Eq] at hszdc1' hcl1' hgdc1'
          have hdc1'0 : (dcs0.set! 0 dc1')[0]! = dc1' := set0_bang_m dcs0 hszdcT dc1'
          have hcompP1' : (dcs0.set! 0 dc1')[0]!.compInfo ≠ .null := by rw [hdc1'0]; exact hcompP0
          obtain ⟨hnc0_1', rcp1', cs1', href1', hgcs1', hle1'⟩ := hcl1' hcompP1'
          have href1'_0 : dc1'.compInfo = .ref rcp1' 0 := by rw [← hdc1'0]; exact href1'
          have hrcpEq : rcp1' = rcp := by
            injection (href0.symm.trans href1'_0) with h1; exact h1.symm
          rw [hrcpEq] at href1'_0 hgcs1'
          have hhmr1' : h1'.markers = h.markers := hmr2T.trans (hmr2.trans hmr1)
          obtain ⟨st, hL, hloop, hpL, hst1L, hnrL, hfinL⟩ :=
            get_sos_loop_parser hp hhead (.ref ctx.rerr 0) rfl rcp n.toInt.toNat hn1 hn4 nib2 bib2
              hp1' hcp01' hgdc1' hszdc1' (by rw [hdc1'0]; exact href1'_0) hgcs1' hnc0_1' hle1'
              (by rw [hdc1'0]; dsimp only [dc1']; simp) (by rw [hdc1'0]; exact kerr0)
              hhmr1' hcur2T (nibBibTrack_mono htr2T (by omega) (by omega)) hstr2'
          have hst0L := decompHeaderStable_trans hp hp1' hst01' hst1L
          by_cases hdone : st.done = true
          · refine ⟨st.ret, hL, ?_, hpL, hst0L, ?_⟩
            · rw [hpreEq]; simp only [hBadF, Bool.false_eq_true, ↓reduceIte]
              rw [C.run_bind, hldcT]; dsimp only
              rw [C.run_bind, hst1']; dsimp only
              rw [C.run_bind]; erw [hloop]; dsimp only
              simp only [hdone, ↓reduceIte]; rfl
            · cases hr : st.ret with
              | ok b =>
                cases b
                · trivial
                · exact False.elim ((hnrL hdone) hr)
              | errExit _ => trivial
          · have hdoneF : st.done = false := Bool.eq_false_iff.mpr hdone
            obtain ⟨hcurSt, htrSt, hstrSt, hccSt⟩ := hfinL (by simp [hdoneF])
            have hstepTailByte : ∀ hX nibX bibX nwX (hpX : ParserEnv ctx hX) (hstX : DecompHeaderStable ctx h hX)
                (htrX : NibBibTrack ctx h hX nibX bibX (-12) nwX) (hnw0 : 0 ≤ nwX) (hnw : nwX ≤ 13)
                (hcurX : CurValid hX nibX bibX),
                ∃ resY hY, C.run (inputByte (.ref (C.DecompRef.decomp ctx.bdc) 0) nibX bibX) hX = .ok (resY, hY) ∧
                  ParserEnv ctx hY ∧ DecompHeaderStable ctx h hY ∧
                  hY.decomps = hX.decomps ∧ hY.comps = hX.comps ∧
                  match resY with
                  | none => True
                  | some (b, nibY, bibY) =>
                    0 ≤ b.toInt ∧ b.toInt ≤ 255 ∧ CurValid hY nibY bibY ∧
                    NibBibTrack ctx h hY nibY bibY (-12) (nwX + 1) ∧
                    (∀ s0, C.Space.get h ctx.rs = some s0 → 0 < s0.size →
                      (isConstEofPtr nibX = true → isConstEofPtr nibY = true) ∧
                      (isConstEofPtr nibY = false → isConstEofPtr nibX = false ∧ bibY.toNat + 1 = bibX.toNat)) := by
              intro hX nibX bibX nwX hpX hstX htrX hnw0 hnw hcurX
              have hbdX : bibX = 0 → ∀ errs, C.Space.get hX ctx.rerr = some errs → 0 < errs.size →
                  errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
                nibBibTrack_bd hp hpX htrX (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
                  have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
              obtain ⟨resY, hY, hrunY, hpY, hdY, hmrY, _, hcpY, _, _, _, _, _, _, hpostY⟩ :=
                inputByte_parser hpX nibX bibX hcurX hbdX
              have hstXY := decompHeaderStable_trans hp hpX hstX (decompHeaderStable_of_same hdY hmrY hcpY)
              refine ⟨resY, hY, hrunY, hpY, hstXY, hdY, hcpY, ?_⟩
              cases resY with
              | none => trivial
              | some p =>
                rcases p with ⟨b, nibY, bibY⟩
                rcases hpostY with ⟨hb0, hbHi, hcurY, hceY⟩
                obtain ⟨htrY, _⟩ := nibBibTrack_inputByte_step hp hpX htrX (by omega) hnw0 hceY
                refine ⟨hb0, hbHi, hcurY, nibBibTrack_mono htrY (by omega) (by omega), fun s0 _ _ => ⟨fun htx => ?_, fun hfy => ?_⟩⟩
                · by_cases hfy : isConstEofPtr nibY = false
                  · simp only [hfy, ↓reduceIte] at hceY; rw [htx] at hceY; cases hceY.1
                  · cases hc : isConstEofPtr nibY <;> simp_all
                · simp only [hfy, ↓reduceIte] at hceY; exact ⟨hceY.1, hceY.2.2.1⟩
            have hputDcTail : ∀ hX (hpX : ParserEnv ctx hX) (hstX : DecompHeaderStable ctx h hX)
                (upd : C.JpegDecompressStruct → C.JpegDecompressStruct)
                (kerrU : ∀ d, (upd d).err = d.err) (kmemU : ∀ d, (upd d).mem = d.mem) (kmasU : ∀ d, (upd d).master = d.master)
                (kicU : ∀ d, (upd d).inputctl = d.inputctl) (kmrkU : ∀ d, (upd d).marker = d.marker) (ksrcU : ∀ d, (upd d).src = d.src)
                (kmlU : ∀ d, (upd d).markerList = d.markerList) (kcompU : ∀ d, (upd d).compInfo = d.compInfo)
                (kncU : ∀ d, (upd d).numComponents = d.numComponents) (kiwU : ∀ d, (upd d).imageWidth = d.imageWidth)
                (kihU : ∀ d, (upd d).imageHeight = d.imageHeight) (kmhU : ∀ d, (upd d).maxHSampFactor = d.maxHSampFactor)
                (kmvU : ∀ d, (upd d).maxVSampFactor = d.maxVSampFactor) (kespU : ∀ d, (upd d).entropyStartPass = d.entropyStartPass)
                (kcsipU : ∀ d, (upd d).coefStartInputPass = d.coefStartInputPass) (kccdU : ∀ d, (upd d).coefConsumeData = d.coefConsumeData)
                (kqtU : ∀ d, (upd d).quantTblPtrs = d.quantTblPtrs) (kdhU : ∀ d, (upd d).dcHuffTblPtrs = d.dcHuffTblPtrs)
                (kahU : ∀ d, (upd d).acHuffTblPtrs = d.acHuffTblPtrs) (kccU : ∀ d, (upd d).curCompInfo = d.curCompInfo)
                (kisnU : ∀ d, 0 ≤ d.inputScanNumber.toInt → 0 ≤ (upd d).inputScanNumber.toInt),
                ∃ dcsX,
                  C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX ∧ 0 < dcsX.size ∧
                  C.run (Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)) hX = .ok (dcsX[0]!, hX) ∧
                  C.run (Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) (upd dcsX[0]!)) hX =
                    .ok ((), C.Space.put hX (C.DecompRef.decomp ctx.bdc) (dcsX.set! 0 (upd dcsX[0]!))) ∧
                  ParserEnv ctx (C.Space.put hX (C.DecompRef.decomp ctx.bdc) (dcsX.set! 0 (upd dcsX[0]!))) ∧
                  DecompHeaderStable ctx h (C.Space.put hX (C.DecompRef.decomp ctx.bdc) (dcsX.set! 0 (upd dcsX[0]!))) := by
              intro hX hpX hstX upd kerrU kmemU kmasU kicU kmrkU ksrcU kmlU kcompU kncU kiwU kihU kmhU kmvU kespU kcsipU kccdU kqtU kdhU kahU kccU kisnU
              have hpX0 := hpX
              obtain ⟨_, _, dcsX, dcX, _, _, _, _, mrksX, _,
                hgdcX, hszdcX, hdcX, _, _, _, _, _,
                _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                _, _, _, _, _, _, _, _,
                _, hgmrkX, _, _, _, _, _, _, _,
                _, _, _, _, _, _, _, _, _,
                _, _, hsawX, _, hqtSzX, hqtX, hdhSzX, hdhX, hahSzX, hahX, hccSzX, hisnX⟩ := hpX0
              subst hdcX
              have hldcX := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcX hszdcX
              have hroX : C.Space.ro hX (C.DecompRef.decomp ctx.bdc) = false := rfl
              have hstX' := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := upd dcsX[0]!) hgdcX hroX hszdcX
              let hY := C.Space.put hX (C.DecompRef.decomp ctx.bdc) (dcsX.set! 0 (upd dcsX[0]!))
              have hpY := parserEnv_put_dc hpX hgdcX hszdcX
                (kerrU _) (kmemU _) (kmasU _) (kicU _) (kmrkU _) (ksrcU _)
                (Or.inl (kmlU _))
                (Or.inl ⟨kcompU _, kncU _⟩)
                ⟨by rw [kqtU]; exact hqtSzX, fun i hi => by rw [kqtU]; exact hqtX i hi⟩
                ⟨by rw [kdhU]; exact hdhSzX, fun i hi => by rw [kdhU]; exact hdhX i hi⟩
                ⟨by rw [kahU]; exact hahSzX, fun i hi => by rw [kahU]; exact hahX i hi⟩
                (by rw [kccU]; exact hccSzX)
                (kisnU _ hisnX)
                (fun mrks' hgmrk' _ hsawNe => by
                  have hmEq := Option.some.inj (hgmrk'.symm.trans hgmrkX); subst hmEq
                  rw [kcompU]; exact hsawX hsawNe)
              have hstXY : DecompHeaderStable ctx hX hY := by
                refine ⟨fun d1 d2 h1d _ h2d _ => ?_, fun m1 m2 h1m _ h2m _ => ?_, fun r c i hrc hi => ⟨c, hrc, hi, rfl, rfl, rfl⟩⟩
                · have h1Eq := Option.some.inj (h1d.symm.trans hgdcX); rw [h1Eq]
                  have hgY : C.Space.get hY (C.DecompRef.decomp ctx.bdc) = some (dcsX.set! 0 (upd dcsX[0]!)) := by
                    simp [hY, C.Space.get, C.Space.put]
                  have h2Eq := Option.some.inj (h2d.symm.trans hgY); rw [h2Eq]
                  rw [set0_bang_m dcsX hszdcX (upd dcsX[0]!)]
                  exact ⟨kcompU _, kncU _, kiwU _, kihU _, kmhU _, kmvU _, kespU _, kcsipU _, kccdU _⟩
                · have hmY : hY.markers = hX.markers := rfl
                  dsimp only [C.Space.get] at h1m h2m; rw [hmY] at h2m
                  rw [Option.some.inj (h2m.symm.trans h1m)]
              exact ⟨dcsX, hgdcX, hszdcX, hldcX, hstX', hpY, decompHeaderStable_trans hp hpX hstX hstXY⟩
            obtain ⟨resS, hS, hrunS, hpS, hst0S, hdS, hcpS, hpostS⟩ := hstepTailByte hL st.nib st.bib 11 hpL hst0L htrSt (by omega) (by omega) hcurSt
            cases resS with
            | none =>
              refine ⟨.ok false, hS, ?_, hpS, hst0S, trivial⟩
              rw [hpreEq]; simp only [hBadF, Bool.false_eq_true, ↓reduceIte]
              rw [C.run_bind, hldcT]; dsimp only
              rw [C.run_bind, hst1']; dsimp only
              rw [C.run_bind]; erw [hloop]; dsimp only
              simp only [hdoneF, Bool.false_eq_true, ↓reduceIte]
              rw [C.run_bind, hrunS]; rfl
            | some pS =>
              rcases pS with ⟨ssVal, nibS, bibS⟩
              rcases hpostS with ⟨_, _, hcurS, htrS, hstepS⟩
              obtain ⟨dcsS, hgdcS, hszdcS, hldcS, hstS, hpS', hst0S'⟩ :=
                hputDcTail hS hpS hst0S (fun d => { d with ss := ssVal })
                  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                  (fun _ => rfl) (fun _ => rfl) (fun _ hi => hi)
              let hS' := C.Space.put hS (C.DecompRef.decomp ctx.bdc) (dcsS.set! 0 { dcsS[0]! with ss := ssVal })
              obtain ⟨resE, hE, hrunE, hpE, hst0E, hdE, hcpE, hpostE⟩ :=
                hstepTailByte hS' nibS bibS 12 hpS' hst0S' (nibBibTrack_err_same htrS rfl) (by omega) (by omega)
                  (curValid_bytes_irrel rfl rfl hcurS)
              cases resE with
              | none =>
                refine ⟨.ok false, hE, ?_, hpE, hst0E, trivial⟩
                rw [hpreEq]; simp only [hBadF, Bool.false_eq_true, ↓reduceIte]
                rw [C.run_bind, hldcT]; dsimp only
                rw [C.run_bind, hst1']; dsimp only
                rw [C.run_bind]; erw [hloop]; dsimp only
                simp only [hdoneF, Bool.false_eq_true, ↓reduceIte]
                rw [C.run_bind, hrunS]; dsimp only
                rw [C.run_bind, hldcS]; dsimp only
                rw [C.run_bind, hstS]; dsimp only
                rw [C.run_bind, hrunE]; rfl
              | some pE =>
                rcases pE with ⟨seVal, nibE, bibE⟩
                rcases hpostE with ⟨_, _, hcurE, htrE, hstepE⟩
                obtain ⟨dcsE, hgdcE, hszdcE, hldcE, hstE, hpE', hst0E'⟩ :=
                  hputDcTail hE hpE hst0E (fun d => { d with se := seVal })
                    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                    (fun _ => rfl) (fun _ => rfl) (fun _ hi => hi)
                let hE' := C.Space.put hE (C.DecompRef.decomp ctx.bdc) (dcsE.set! 0 { dcsE[0]! with se := seVal })
                obtain ⟨resA, hA, hrunA, hpA, hst0A, hdA, hcpA, hpostA⟩ :=
                  hstepTailByte hE' nibE bibE 13 hpE' hst0E' (nibBibTrack_err_same htrE rfl) (by omega) (by omega)
                    (curValid_bytes_irrel rfl rfl hcurE)
                cases resA with
                | none =>
                  refine ⟨.ok false, hA, ?_, hpA, hst0A, trivial⟩
                  rw [hpreEq]; simp only [hBadF, Bool.false_eq_true, ↓reduceIte]
                  rw [C.run_bind, hldcT]; dsimp only
                  rw [C.run_bind, hst1']; dsimp only
                  rw [C.run_bind]; erw [hloop]; dsimp only
                  simp only [hdoneF, Bool.false_eq_true, ↓reduceIte]
                  rw [C.run_bind, hrunS]; dsimp only
                  rw [C.run_bind, hldcS]; dsimp only
                  rw [C.run_bind, hstS]; dsimp only
                  rw [C.run_bind, hrunE]; dsimp only
                  rw [C.run_bind, hldcE]; dsimp only
                  rw [C.run_bind, hstE]; dsimp only
                  rw [C.run_bind, hrunA]; rfl
                | some pA =>
                  rcases pA with ⟨ahAl, nibEnd, bibEnd⟩
                  rcases hpostA with ⟨_, _, hcurA, htrA, hstepA⟩
                  let updF : C.JpegDecompressStruct → C.JpegDecompressStruct := fun d =>
                    { d with ah := (ahAl >>> 4) &&& 15, al := ahAl &&& 15 }
                  obtain ⟨dcsF, hgdcF, hszdcF, hldcF, hstF, hpF', hst0F'⟩ :=
                    hputDcTail hA hpA hst0A updF
                      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                      (fun _ => rfl) (fun _ => rfl) (fun _ hi => hi)
                  let dcF' := updF dcsF[0]!
                  let hF' := C.Space.put hA (C.DecompRef.decomp ctx.bdc) (dcsF.set! 0 dcF')
                  obtain ⟨dcsF_p, hgdcF_p, _, kerrF', _, _, _, kmrkF', _⟩ := parserEnv_get_dc hpF'
                  have hgdcF' : C.Space.get hF' (C.DecompRef.decomp ctx.bdc) = some (dcsF.set! 0 dcF') := by
                    simp [hF', C.Space.get, C.Space.put]
                  have hEqF_p := Option.some.inj (hgdcF_p.symm.trans hgdcF')
                  rw [hEqF_p] at kerrF' kmrkF'
                  have hdcF'Eq : (dcsF.set! 0 dcF')[0]! = dcF' := set0_bang_m dcsF hszdcF dcF'
                  have hszdcF' : 0 < (dcsF.set! 0 dcF').size := by simpa using hszdcF
                  have kerrF_eq : dcF'.err = .ref ctx.rerr 0 := by rw [← hdcF'Eq]; exact kerrF'
                  have kmrkF_eq : dcF'.marker = .ref ctx.rmrk 0 := by rw [← hdcF'Eq]; exact kmrkF'
                  obtain ⟨hTr, htr4_run, hpTr, hdTr, hmrTr, hsrTr, _, hcpTr, _, _, _, hbyTr, _, hcoTr, hnwTr⟩ :=
                    tracems4_nonneg_parser hpF' 1 JTRC_SOS_PARAMS dcF'.ss dcF'.se dcF'.ah dcF'.al (by decide)
                  have htr4_run' : C.run (tracems4 dcF'.err 1 JTRC_SOS_PARAMS dcF'.ss dcF'.se dcF'.ah dcF'.al) hF' =
                      .ok ((), hTr) := by
                    rw [kerrF_eq]; exact htr4_run
                  have hst0Tr := decompHeaderStable_trans hp hpF' hst0F' (decompHeaderStable_of_same hdTr hmrTr hcpTr)
                  obtain ⟨mrksTr, hgmrkTr, hszmrkTr, _, _, _, _, _⟩ := parserEnv_get_mrk hpTr
                  have hlmrkTr := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrkTr hszmrkTr
                  have hlmrkTr' : C.run (Ptr.load dcF'.marker) hTr = .ok (mrksTr[0]!, hTr) := by
                    rw [kmrkF_eq]; exact hlmrkTr
                  have hroMrk : C.Space.ro hTr ctx.rmrk = false := rfl
                  let mrkNew := { mrksTr[0]! with nextRestartNum := 0 }
                  have hstMrk := ptr_store_ok (r := ctx.rmrk) (off := 0) (v := mrkNew) hgmrkTr hroMrk hszmrkTr
                  have hstMrk' : C.run (Ptr.store dcF'.marker mrkNew) hTr =
                      .ok ((), C.Space.put hTr ctx.rmrk (mrksTr.set! 0 mrkNew)) := by
                    rw [kmrkF_eq]; exact hstMrk
                  let hM := C.Space.put hTr ctx.rmrk (mrksTr.set! 0 mrkNew)
                  have hpM : ParserEnv ctx hM :=
                    parserEnv_put_mrk_sameCur hpTr hgmrkTr hszmrkTr rfl rfl rfl rfl rfl rfl rfl rfl
                  have hstTrM : DecompHeaderStable ctx hTr hM := by
                    refine ⟨fun d1 d2 h1d _ h2d _ => ?_, fun m1 m2 h1m _ h2m _ => ?_, fun r c i hrc hi => ⟨c, hrc, hi, rfl, rfl, rfl⟩⟩
                    · have hdM : hM.decomps = hTr.decomps := rfl
                      dsimp only [C.Space.get] at h1d h2d; rw [hdM] at h2d
                      rw [Option.some.inj (h2d.symm.trans h1d)]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                    · have h1Eq := Option.some.inj (h1m.symm.trans hgmrkTr); rw [h1Eq]
                      have hgM : C.Space.get hM ctx.rmrk = some (mrksTr.set! 0 mrkNew) := by
                        simp [hM, C.Space.get, C.Space.put]
                      have h2Eq := Option.some.inj (h2m.symm.trans hgM); rw [h2Eq]
                      rw [set0_bang_m mrksTr hszmrkTr mrkNew]
                  have hst0M := decompHeaderStable_trans hp hpTr hst0Tr hstTrM
                  have hdcS_L : C.Space.get hL (C.DecompRef.decomp ctx.bdc) = some dcsS := by
                    dsimp only [C.Space.get] at hgdcS ⊢; rw [hdS] at hgdcS; exact hgdcS
                  obtain ⟨hcisL, hccSzL, hisnL, hccL⟩ := hccSt dcsS hdcS_L hszdcS
                  have hgdcS' : C.Space.get hS' (C.DecompRef.decomp ctx.bdc) =
                      some (dcsS.set! 0 { dcsS[0]! with ss := ssVal }) := by
                    simp [hS', C.Space.get, C.Space.put]
                  have hdcE_S' : C.Space.get hS' (C.DecompRef.decomp ctx.bdc) = some dcsE := by
                    dsimp only [C.Space.get] at hgdcE ⊢; rw [hdE] at hgdcE; exact hgdcE
                  have hEqE := Option.some.inj (hdcE_S'.symm.trans hgdcS')
                  have hdcE0 : dcsE[0]! = { dcsS[0]! with ss := ssVal } := by
                    rw [hEqE]; exact set0_bang_m dcsS hszdcS _
                  have hgdcE' : C.Space.get hE' (C.DecompRef.decomp ctx.bdc) =
                      some (dcsE.set! 0 { dcsE[0]! with se := seVal }) := by
                    simp [hE', C.Space.get, C.Space.put]
                  have hdcF_E' : C.Space.get hE' (C.DecompRef.decomp ctx.bdc) = some dcsF := by
                    dsimp only [C.Space.get] at hgdcF ⊢; rw [hdA] at hgdcF; exact hgdcF
                  have hEqF := Option.some.inj (hdcF_E'.symm.trans hgdcE')
                  have hdcF0 : dcsF[0]! = { dcsE[0]! with se := seVal } := by
                    rw [hEqF]; exact set0_bang_m dcsE hszdcE _
                  have hisnF : dcF'.inputScanNumber = dcs0[0]!.inputScanNumber := by
                    dsimp only [dcF', updF]; rw [hdcF0, hdcE0]; exact hisnL.trans (by rw [hdc1'0])
                  have hisnBound := hscan dcs0 hgdc0 hszdc0
                  have hisn0 : 0 ≤ dcF'.inputScanNumber.toInt := by
                    obtain ⟨_, _, dcs0_x, dc0_x, _, _, _, _, _, _, hgdc0_x, _, hdc0_x, _, _, _, _, _,
                      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                      _, _, _, _, _, _, _, _, _, hisn0⟩ := hp0
                    have hEq0x := Option.some.inj (hgdc0_x.symm.trans hgdc0)
                    rw [hisnF, ← hEq0x, ← hdc0_x]; exact hisn0
                  have h1to : (1 : Int32).toInt = 1 := by decide
                  let isn := Int32.ofInt (dcF'.inputScanNumber.toInt + 1)
                  have hlo : (-2 ^ 31 : Int) ≤ dcF'.inputScanNumber.toInt + 1 := by omega
                  have hhi : dcF'.inputScanNumber.toInt + 1 < 2 ^ 31 := by rw [hisnF]; omega
                  have haddRun : C.run (i32Add dcF'.inputScanNumber 1) hM = .ok (isn, hM) := by
                    simp only [C.run, i32Add, checkI32, h1to, hlo, hhi, and_self, ↓reduceIte]; rfl
                  have hisnTo : isn.toInt = dcF'.inputScanNumber.toInt + 1 := by
                    dsimp only [isn]
                    rw [Int32.toInt_ofInt, show Int32.size = 2 ^ 32 from rfl]
                    refine Int.bmod_eq_of_le (by omega) (by rw [hisnF]; omega)
                  have hisnNonneg : 0 ≤ isn.toInt := by rw [hisnTo]; omega
                  obtain ⟨dcsM, hgdcM, hszdcM, hldcM, hstM, hpM', hst0M'⟩ :=
                    hputDcTail hM hpM hst0M (fun d => { d with inputScanNumber := isn })
                      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                      (fun _ => rfl) (fun _ => rfl) (fun _ _ => hisnNonneg)
                  let dcM' := { dcsM[0]! with inputScanNumber := isn }
                  let hM' := C.Space.put hM (C.DecompRef.decomp ctx.bdc) (dcsM.set! 0 dcM')
                  have htrM' := nibBibTrack_err_nw_same hpF' (nibBibTrack_err_same htrA rfl) hnwTr
                  have htrM'' := nibBibTrack_err_same htrM' (rfl : hM'.errMgrs = hM.errMgrs)
                  have hcurM' : CurValid hM' nibEnd bibEnd :=
                    curValid_bytes_irrel (by exact rfl) (by exact rfl) (curValid_bytes_irrel hbyTr hcoTr hcurA)
                  obtain ⟨h3, hsync, hp3, hd3, hmr3, he3, _, hcp3, _, _, _, _, _, _, hsrc3⟩ :=
                    inputSync_parser hpM' nibEnd bibEnd hcurM'
                  have hst03 := decompHeaderStable_trans hp hpM' hst0M' (decompHeaderStable_of_same hd3 hmr3 hcp3)
                  obtain ⟨hw, _⟩ := nibBibTrack_to_warnPotOk_src hp hpM' htrM'' (by omega) he3 hsrc3
                  have hstr3_step : ∀ srcs, C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
                      isConstEofPtr nibEnd = true ∨ bibEnd.toNat + 8 ≤ srcs[0]!.bytesInBuffer.toNat := by
                    intro s0 hs0 hss0
                    by_cases hnfA : isConstEofPtr nibEnd = false
                    · obtain ⟨hnfE, hbibA⟩ := (hstepA s0 hs0 hss0).2 hnfA
                      obtain ⟨hnfS, hbibE⟩ := (hstepE s0 hs0 hss0).2 hnfE
                      obtain ⟨hnfSt, hbibS⟩ := (hstepS s0 hs0 hss0).2 hnfS
                      rcases hstrSt s0 hs0 hss0 with htrSt' | hleSt
                      · rw [hnfSt] at htrSt'; cases htrSt'
                      · right; omega
                    · left
                      cases hc : isConstEofPtr nibEnd
                      · exact absurd hc hnfA
                      · rfl
                  have hstr3 : ∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
                      C.Space.get h3 ctx.rs = some srcs' → 0 < srcs'.size →
                      SrcStrict srcs0[0]! srcs'[0]! ∧
                      (isConstEofPtr srcs'[0]!.nextInputByte = true ∨
                        srcs'[0]!.bytesInBuffer.toNat + 8 ≤ srcs0[0]!.bytesInBuffer.toNat) := by
                    intro s0 s' hs0 hss0 hs' _
                    refine ⟨nibBibTrack_to_srcStrict hp hpM' htrM'' (fun ss0 hss0' hs0' => ?_) hsrc3 s0 s' hs0 hss0 hs' (hsrc3 s' hs').1, ?_⟩
                    · rcases hstr3_step ss0 hss0' hs0' with ht | hle
                      · left; exact ht
                      · right; omega
                    · obtain ⟨_, hnib3, hbib3⟩ := hsrc3 s' hs'
                      rw [hnib3, hbib3]; exact hstr3_step s0 hs0 hss0
                  have hpreMidEq : C.run (get_sos (.ref (C.DecompRef.decomp ctx.bdc) 0)) h =
                      C.run (do
                        let dcF ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                        let dcF' := { dcF with ah := (ahAl >>> 4) &&& 15, al := ahAl &&& 15 }
                        Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) dcF'
                        tracems4 dcF'.err 1 JTRC_SOS_PARAMS dcF'.ss dcF'.se dcF'.ah dcF'.al
                        let mrkF ← Ptr.load dcF'.marker
                        Ptr.store dcF'.marker { mrkF with nextRestartNum := 0 }
                        let isn ← i32Add dcF'.inputScanNumber 1
                        let dcF2 ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                        Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcF2 with inputScanNumber := isn }
                        inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) nibEnd bibEnd
                        return .ok true) hA := by
                    rw [hpreEq]; simp only [hBadF, Bool.false_eq_true, ↓reduceIte]
                    rw [C.run_bind, hldcT]; dsimp only
                    rw [C.run_bind, hst1']; dsimp only
                    rw [C.run_bind]; erw [hloop]; dsimp only
                    simp only [hdoneF, Bool.false_eq_true, ↓reduceIte]
                    rw [C.run_bind, hrunS]; dsimp only
                    rw [C.run_bind, hldcS]; dsimp only
                    rw [C.run_bind, hstS]; dsimp only
                    rw [C.run_bind, hrunE]; dsimp only
                    rw [C.run_bind, hldcE]; dsimp only
                    rw [C.run_bind, hstE]; dsimp only
                    rw [C.run_bind, hrunA]
                  have hrunFinal : C.run (get_sos (.ref (C.DecompRef.decomp ctx.bdc) 0)) h = .ok (.ok true, h3) := by
                    rw [hpreMidEq]
                    rw [C.run_bind, hldcF]; dsimp only
                    rw [C.run_bind, hstF]; dsimp only
                    rw [C.run_bind, htr4_run']; dsimp only
                    rw [C.run_bind, hlmrkTr']; dsimp only
                    rw [C.run_bind, hstMrk']; dsimp only
                    rw [C.run_bind, haddRun]; dsimp only
                    rw [C.run_bind, hldcM]; dsimp only
                    rw [C.run_bind, hstM]; dsimp only
                    rw [C.run_bind, hsync]; rfl
                  refine ⟨.ok true, h3, hrunFinal, hp3, hst03, hstr3, fun dcs0' dcs3 hg0' hsz0' hg3' hsz3' => ?_, ?_⟩
                  · have hgdcM' : C.Space.get hM' (C.DecompRef.decomp ctx.bdc) = some (dcsM.set! 0 dcM') := by
                      simp [hM', C.Space.get, C.Space.put]
                    have hg3M' : C.Space.get hM' (C.DecompRef.decomp ctx.bdc) = some dcs3 := by
                      dsimp only [C.Space.get] at hg3' ⊢; rw [hd3] at hg3'; exact hg3'
                    have hEq3 := Option.some.inj (hg3M'.symm.trans hgdcM')
                    have hdcM_tr : dcsM[0]! = dcF' := by
                      have hgML : C.Space.get hTr (C.DecompRef.decomp ctx.bdc) = some dcsM := hgdcM
                      have hgTrF' : C.Space.get hF' (C.DecompRef.decomp ctx.bdc) = some dcsM := by
                        dsimp only [C.Space.get] at hgML ⊢; rw [hdTr] at hgML; exact hgML
                      have hEqM := Option.some.inj (hgTrF'.symm.trans hgdcF')
                      rw [hEqM, hdcF'Eq]
                    have hcis3 : dcs3[0]!.compsInScan = n := by
                      rw [hEq3, set0_bang_m dcsM hszdcM dcM']
                      show dcsM[0]!.compsInScan = n
                      rw [hdcM_tr]; dsimp only [dcF', updF]; rw [hdcF0, hdcE0]
                      exact hcisL.trans (by rw [hdc1'0])
                    have hcc3 : dcs3[0]!.curCompInfo = dcF'.curCompInfo := by
                      rw [hEq3, set0_bang_m dcsM hszdcM dcM']
                      show dcsM[0]!.curCompInfo = dcF'.curCompInfo
                      rw [hdcM_tr]
                    have hcc3_L : dcF'.curCompInfo = dcsS[0]!.curCompInfo := by
                      dsimp only [dcF', updF]; rw [hdcF0, hdcE0]
                    have hcpL3 : h3.comps = hL.comps := by
                      have h1 : h3.comps = hM'.comps := hcp3
                      have h2 : hM'.comps = hTr.comps := rfl
                      have h3' : hTr.comps = hF'.comps := hcpTr
                      have h4 : hF'.comps = hA.comps := rfl
                      have h5 : hA.comps = hE'.comps := hcpA
                      have h6 : hE'.comps = hE.comps := rfl
                      have h7 : hE.comps = hS'.comps := hcpE
                      have h8 : hS'.comps = hS.comps := rfl
                      have h9 : hS.comps = hL.comps := hcpS
                      exact h1.trans (h2.trans (h3'.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans h9)))))))
                    have hci0_3 : dcs3[0]!.compInfo = dcs0[0]!.compInfo :=
                      (hst03.1 _ _ hgdc0 hszdc0 hg3' hsz3').1
                    have hncS_0 : dcsS[0]!.numComponents = dcs0[0]!.numComponents :=
                      (hst0S.1 _ _ hgdc0 hszdc0 hgdcS hszdcS).2.1
                    have hnc3_0 : dcs3[0]!.numComponents = dcs0[0]!.numComponents :=
                      (hst03.1 _ _ hgdc0 hszdc0 hg3' hsz3').2.1
                    have hscanComps3 : ScanCompsInRange h3 dcs3[0]! := by
                      refine ⟨by rw [hcis3]; omega, by rw [hcis3]; omega, by rw [hcc3, hcc3_L]; exact hccSzL, ?_⟩
                      intro i hi
                      rw [hcis3] at hi
                      obtain ⟨offI, csL, hccI, hgL_rcp, hoffI, hoffI_nc⟩ := hccL i hi
                      have hccVal : dcs3[0]!.curCompInfo[i]! = .ref rcp offI := by
                        rw [hcc3, hcc3_L]; exact hccI
                      have hg3_rcp : C.Space.get h3 rcp = some csL := by
                        rcases hrC : rcp with ⟨bc⟩
                        simp only [C.Space.get, hrC, hcpL3] at hgL_rcp ⊢; exact hgL_rcp
                      have hoffI_nc3 : offI < dcs3[0]!.numComponents.toInt.toNat := by
                        rw [hnc3_0, ← hncS_0]; exact hoffI_nc
                      exact ⟨rcp, offI, csL, hci0_3.trans href0, hg3_rcp, hoffI_nc3, hoffI, hccVal⟩
                    refine ⟨?_, hscanComps3, ?_⟩
                    · have hEq0' := Option.some.inj (hg0'.symm.trans hgdc0)
                      rw [hEq3, set0_bang_m dcsM hszdcM dcM']
                      change dcM'.inputScanNumber.toInt = dcs0'[0]!.inputScanNumber.toInt + 1
                      rw [show dcM'.inputScanNumber = isn from rfl, hisnTo, hisnF, ← hEq0']
                    · intro hpost0
                      have hEq0' := Option.some.inj (hg0'.symm.trans hgdc0)
                      rw [hEq0'] at hpost0
                      have hpb3 := postSofBase_of_decompHeaderStable hp hp3 hst03 hgdc0 hszdc0 hg3' hsz3' hpost0
                      rcases hpb3 with ⟨pe1, pe2, pe3, pm1, pm2, pm3, pm4, pw1, ph1, pnc1, pnc2, pmrk3, pcomp3⟩
                      refine ⟨pe1, pe2, pe3, hscanComps3.1, hscanComps3.2.1, hscanComps3.2.2.1,
                        pm1, pm2, pm3, pm4, pw1, ph1, pnc1, pnc2, pmrk3, pcomp3, ?_⟩
                      intro i hi
                      obtain ⟨rcpI, offI, csL, hci3I, hg3_rcp, hoffI_nc3, hoffI, hccVal⟩ := hscanComps3.2.2.2 i hi
                      have hrcpEq : rcpI = rcp := by
                        have := hci3I.symm.trans (hci0_3.trans href0); cases this; rfl
                      rw [hrcpEq] at hg3_rcp hccVal
                      rcases pcomp3 with pnc0 | ⟨rcp3, cs3, hci3, hgcs3, hle3, hcb3⟩
                      · exfalso; rw [pnc0] at hoffI_nc3; simp at hoffI_nc3
                      · have hrcp3Eq : rcp3 = rcp := by
                          cases (hci3.symm.trans (hci0_3.trans href0)); rfl
                        rw [hrcp3Eq] at hgcs3
                        have hcs3Eq := Option.some.inj (hgcs3.symm.trans hg3_rcp)
                        have hbounds := hcb3 offI hoffI_nc3
                        rw [hcs3Eq] at hbounds
                        exact ⟨rcp, offI, csL, csL[offI]!, hccVal, hg3_rcp, hoffI, rfl, hbounds⟩
                  · intro e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
                    obtain ⟨wf, wt⟩ := hw e0 e3 s0 s3 hg0 hsz0 hg3 hsz3 hs0 hszs0 hs3 hszs3
                    exact ⟨wf, fun ht => Int.le_trans (wt ht) (Int.add_le_add_left (by decide) _)⟩

/-! ## `save_marker`, `callMarkerParser`, `next_marker_parser`, and `read_markers_parser` -/

private theorem nibBibTrack_copy_step {ctx : IoCtx} {h0 h : C.Heap}
    {nib nib' : C.BPtr} {bib bib' : UInt64} {nd el : Int} {bd : Nat}
    {arr : Array UInt8} {idx : Nat} {v : UInt8}
    (_hp : ParserEnv ctx h) (ht : NibBibTrack ctx h0 h nib bib nd el)
    (hpost : if isConstEofPtr nib' = false then
      isConstEofPtr nib = false ∧ bib'.toNat + 1 = bib.toNat
     else
      isConstEofPtr nib = true) :
    NibBibTrack ctx h0 (C.Space.put h (C.BRef.heap bd) (arr.set! idx v)) nib' bib' (nd - 4) el := by
  let h' := C.Space.put h (C.BRef.heap bd) (arr.set! idx v)
  have herr : h'.errMgrs = h.errMgrs := rfl
  have htr' := nibBibTrack_err_same ht herr
  intro e0 e' s0 he0 hse0 he' hse' hs0 hss0
  obtain ⟨ta, tb, tc⟩ := htr' e0 e' s0 he0 hse0 he' hse' hs0 hss0
  refine ⟨fun hs0t => ?_, fun hnf => ?_, fun hnt => ?_⟩
  · have hnt0 := ta hs0t
    by_cases hnf' : isConstEofPtr nib' = false
    · simp only [hnf', ↓reduceIte] at hpost; rw [hnt0] at hpost; exact False.elim (by cases hpost.1)
    · cases hc : isConstEofPtr nib' <;> simp_all
  · simp only [hnf, ↓reduceIte] at hpost
    obtain ⟨b1, b2, b3⟩ := tb hpost.1
    refine ⟨b1, by omega, by omega⟩
  · simp only [hnt, Bool.true_eq_false, ↓reduceIte] at hpost
    exact tc hpost

private theorem save_marker_copy_parser {ctx : IoCtx} {h0 h : C.Heap}
    (_hp0 : ParserEnv ctx h0) (hp : ParserEnv ctx h)
    {br0 dataLength : UInt32} (hbrLe : br0 ≤ dataLength) (hdlLe : dataLength.toNat ≤ 65535)
    {bd offD : Nat} {arrD : Array UInt8} (hbd : h.bytes bd = some arrD)
    (hwb : offD + dataLength.toNat ≤ arrD.size)
    {n1 : C.BPtr} {bi1 : UInt64} (hcur1 : CurValid h n1 bi1) (hbi1Pos : 0 < bi1.toNat)
    {dp0 : C.BPtr} (hdp0 : dp0 = .ref (.heap bd) (offD + br0.toNat))
    {nd0 el0 : Int} (htr1 : NibBibTrack ctx h0 h n1 bi1 nd0 el0) :
    ∃ cs h',
      C.run (cwhile
        (fun (c : SaveMarkerCopyState) => pure (c.br < dataLength && c.bb > 0, c))
        (fun (c : SaveMarkerCopyState) => do
          let b ← Ptr.load c.nb
          Ptr.store c.dp b
          let dp' ← Ptr.add c.dp 1
          let nb' ← Ptr.add c.nb 1
          return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
        { br := br0, nb := n1, bb := bi1, dp := dp0 }) h = .ok (cs, h') ∧
      ParserEnv ctx h' ∧
      h'.decomps = h.decomps ∧ h'.markers = h.markers ∧ h'.masters = h.masters ∧
      h'.comps = h.comps ∧ h'.quants = h.quants ∧ h'.huffs = h.huffs ∧
      h'.savedMarkers = h.savedMarkers ∧ h'.srcs = h.srcs ∧ h'.errMgrs = h.errMgrs ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∃ arrD', h'.bytes bd = some arrD' ∧ arrD'.size = arrD.size) ∧
      br0.toNat ≤ cs.br.toNat ∧ cs.br ≤ dataLength ∧
      (br0 < dataLength → br0.toNat < cs.br.toNat) ∧
      cs.dp = .ref (.heap bd) (offD + cs.br.toNat) ∧
      CurValid h' cs.nb cs.bb ∧
      NibBibTrack ctx h0 h' cs.nb cs.bb (nd0 - 4 * (cs.br.toNat - br0.toNat : Int)) el0 := by
  let Inv : Nat → C.Heap → SaveMarkerCopyState → Prop := fun k hx c =>
    k = c.bb.toNat ∧
    ParserEnv ctx hx ∧
    hx.decomps = h.decomps ∧ hx.markers = h.markers ∧ hx.masters = h.masters ∧
    hx.comps = h.comps ∧ hx.quants = h.quants ∧ hx.huffs = h.huffs ∧
    hx.savedMarkers = h.savedMarkers ∧ hx.srcs = h.srcs ∧ hx.errMgrs = h.errMgrs ∧
    hx.mems = h.mems ∧ hx.consts = h.consts ∧
    (∃ arrX, hx.bytes bd = some arrX ∧ arrX.size = arrD.size) ∧
    br0.toNat ≤ c.br.toNat ∧ c.br ≤ dataLength ∧
    (br0 < dataLength → br0.toNat < c.br.toNat ∨ c.bb = bi1) ∧
    c.dp = .ref (.heap bd) (offD + c.br.toNat) ∧
    CurValid hx c.nb c.bb ∧
    NibBibTrack ctx h0 hx c.nb c.bb (nd0 - 4 * (c.br.toNat - br0.toNat : Int)) el0
  let Post : C.Heap → SaveMarkerCopyState → Prop := fun hx c =>
    ParserEnv ctx hx ∧
    hx.decomps = h.decomps ∧ hx.markers = h.markers ∧ hx.masters = h.masters ∧
    hx.comps = h.comps ∧ hx.quants = h.quants ∧ hx.huffs = h.huffs ∧
    hx.savedMarkers = h.savedMarkers ∧ hx.srcs = h.srcs ∧ hx.errMgrs = h.errMgrs ∧
    hx.mems = h.mems ∧ hx.consts = h.consts ∧
    (∃ arrX, hx.bytes bd = some arrX ∧ arrX.size = arrD.size) ∧
    br0.toNat ≤ c.br.toNat ∧ c.br ≤ dataLength ∧
    (br0 < dataLength → br0.toNat < c.br.toNat) ∧
    c.dp = .ref (.heap bd) (offD + c.br.toNat) ∧
    CurValid hx c.nb c.bb ∧
    NibBibTrack ctx h0 hx c.nb c.bb (nd0 - 4 * (c.br.toNat - br0.toNat : Int)) el0
  have hbi1Lt : bi1.toNat < C.fuel := by
    have := hcur1.1; unfold C.fuel; omega
  have htrInit : NibBibTrack ctx h0 h n1 bi1 (nd0 - 4 * (br0.toNat - br0.toNat : Int)) el0 := by
    simpa using htr1
  obtain ⟨cs, h', hrun, hpost⟩ := cwhile_terminates
    (fun (c : SaveMarkerCopyState) => pure (c.br < dataLength && c.bb > 0, c))
    (fun (c : SaveMarkerCopyState) => do
      let b ← Ptr.load c.nb
      Ptr.store c.dp b
      let dp' ← Ptr.add c.dp 1
      let nb' ← Ptr.add c.nb 1
      return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
    Inv Post
    (fun k hx c ⟨hk, hpx, hdx, hmx, hmax, hcx, hqx, hhx, hsmx, hsrx, hex, hmex, hcox,
        ⟨arrX, hbdX, hszX⟩, hbrLo, hbrHi, hbrProg, hdpX, hcurX, htrX⟩ => by
      by_cases hcnd : (c.br < dataLength && c.bb > 0) = true
      · refine ⟨true, c, hx, (by simp only [C.run, pure, hcnd]), ?_⟩
        simp only [↓reduceIte]
        have hcbrLt : c.br < dataLength := by
          by_cases h1 : c.br < dataLength <;> simp_all
        have hcbbPos : c.bb > 0 := by
          by_cases h2 : c.bb > 0 <;> simp_all
        have hcbrNat : c.br.toNat < dataLength.toNat := hcbrLt
        have hcbbNat : 0 < c.bb.toNat := hcbbPos
        have hbbNe0 : c.bb ≠ 0 := fun hz => by rw [hz] at hcbbNat; simp at hcbbNat
        rcases hcurX with ⟨hbibLtX, hbibLiveX, hceX⟩
        have hliveX : LiveBytes hx c.nb c.bb.toNat := by
          rcases hbibLiveX with hz | hlv
          · exact False.elim (hbbNe0 hz)
          · exact hlv
        rcases hliveX with ⟨rnb, offnb, bsnb, hcnb, hgnb, hnbBnd⟩
        have hnbLt : offnb < bsnb.size := by omega
        have hlnb := ptr_load_ok (r := rnb) (off := offnb) hgnb hnbLt
        have hlnb' : C.run (Ptr.load c.nb) hx = .ok (bsnb[offnb]!, hx) := by rw [hcnb]; exact hlnb
        have hdpIdx : offD + c.br.toNat < arrX.size := by omega
        have hroD : C.Space.ro hx (C.BRef.heap bd) = false := rfl
        have hstDp := ptr_store_ok (r := C.BRef.heap bd) (off := offD + c.br.toNat) (v := bsnb[offnb]!) hbdX hroD hdpIdx
        have hstDp' : C.run (Ptr.store c.dp bsnb[offnb]!) hx =
            .ok ((), C.Space.put hx (C.BRef.heap bd) (arrX.set! (offD + c.br.toNat) bsnb[offnb]!)) := by
          rw [hdpX]; exact hstDp
        let hx' := C.Space.put hx (C.BRef.heap bd) (arrX.set! (offD + c.br.toNat) bsnb[offnb]!)
        have hbdX' : C.Space.get hx' (C.BRef.heap bd) = some (arrX.set! (offD + c.br.toNat) bsnb[offnb]!) := by
          dsimp [hx', C.Space.get, C.Space.put]; exact C.upd_same _ _ _
        have hbdX'raw : hx'.bytes bd = some (arrX.set! (offD + c.br.toNat) bsnb[offnb]!) := hbdX'
        have hszX' : (arrX.set! (offD + c.br.toNat) bsnb[offnb]!).size = arrD.size := by
          simpa using hszX
        have haddDp := ptr_add_ok (r := C.BRef.heap bd) (xs := arrX.set! (offD + c.br.toNat) bsnb[offnb]!)
          (off := offD + c.br.toNat) (k := 1) hbdX' (by simp; omega)
          (by omega) (by simp [hszX]; omega)
        have haddDp' : C.run (Ptr.add c.dp 1) hx' =
            .ok (.ref (.heap bd) (offD + c.br.toNat + 1), hx') := by
          rw [hdpX]
          have h1 : ((offD + c.br.toNat : Int) + 1).toNat = offD + c.br.toNat + 1 := by omega
          simpa [h1] using haddDp
        let bsnb' : Array UInt8 :=
          match rnb with
          | .heap bnb => if bnb = bd then arrX.set! (offD + c.br.toNat) bsnb[offnb]! else bsnb
          | .const _ => bsnb
          | .const_eof => bsnb
          | .str _ => bsnb
        have hgnb' : C.Space.get hx' rnb = some bsnb' := by
          cases rnb with
          | heap bnb =>
            dsimp only [bsnb']
            by_cases hbe : bnb = bd
            · subst hbe
              have hEqB := Option.some.inj (hbdX.symm.trans hgnb); subst hEqB
              simp only [↓reduceIte]; exact hbdX'
            · simp only [hbe, ↓reduceIte]
              dsimp only [hx', C.Space.get, C.Space.put, C.Heap.putBytes, C.Heap.getBytes] at hgnb ⊢
              rw [C.upd_ne _ _ _ _ hbe]; exact hgnb
          | const _ => exact hgnb
          | const_eof => exact hgnb
          | str _ => exact hgnb
        have hbsnbSz' : bsnb'.size = bsnb.size := by
          cases rnb with
          | heap bnb =>
            dsimp only [bsnb']
            by_cases hbe : bnb = bd
            · subst hbe
              have hEqB := Option.some.inj (hbdX.symm.trans hgnb); subst hEqB
              simp
            · simp [hbe]
          | const _ => rfl
          | const_eof => rfl
          | str _ => rfl
        have haddNb := ptr_add_ok (r := rnb) (xs := bsnb')
          (off := offnb) (k := 1) hgnb' (by rw [hbsnbSz']; omega) (by omega) (by rw [hbsnbSz']; omega)
        have haddNb' : C.run (Ptr.add c.nb 1) hx' = .ok (.ref rnb (offnb + 1), hx') := by
          rw [hcnb]
          have h1 : ((offnb : Int) + 1).toNat = offnb + 1 := by omega
          simpa [h1] using haddNb
        have hpx' : ParserEnv ctx hx' := parserEnv_put_byte hpx hbdX
        have hbbSub : (c.bb - 1).toNat = c.bb.toNat - 1 := by
          have h1n : (1 : UInt64).toNat = 1 := rfl
          have h1le : (1 : UInt64) ≤ c.bb := UInt64.le_iff_toNat_le.mpr (by rw [h1n]; omega)
          rw [UInt64.toNat_sub_of_le c.bb 1 h1le, h1n]
        have hcurX' : CurValid hx' (.ref rnb (offnb + 1)) (c.bb - 1) := by
          have hcv0 := curValid_set_byte (idx := offD + c.br.toNat) (v := bsnb[offnb]!) hbdX ⟨hbibLtX, hbibLiveX, hceX⟩
          rcases hcv0 with ⟨h1', h2', h3'⟩
          refine ⟨by rw [hbbSub]; omega, ?_, ?_⟩
          · by_cases hzero : c.bb - 1 = 0
            · exact Or.inl hzero
            · exact Or.inr ⟨rnb, offnb + 1, bsnb', rfl, hgnb', by rw [hbsnbSz', hbbSub]; omega⟩
          · intro o ho
            rw [hcnb] at hceX
            injection ho with hrb; cases hrb
            have := hceX offnb rfl
            rw [hbbSub]; omega
        have hbrAddTo : (c.br + 1).toNat = c.br.toNat + 1 := by
          rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        have htrX' : NibBibTrack ctx h0 hx' (.ref rnb (offnb + 1)) (c.bb - 1)
            (nd0 - 4 * ((c.br + 1).toNat - br0.toNat : Int)) el0 := by
          have hstepTr := nibBibTrack_copy_step hpx htrX (bd := bd) (arr := arrX) (idx := offD + c.br.toNat)
            (v := bsnb[offnb]!) (nib' := .ref rnb (offnb + 1)) (bib' := c.bb - 1) (by
              rw [hcnb]
              cases rnb <;> simp [isConstEofPtr, hbbSub] <;> omega)
          refine nibBibTrack_mono hstepTr ?_ (Int.le_refl _)
          rw [hbrAddTo]; omega
        have hbbDec : (c.bb - 1).toNat < k := by rw [hbbSub]; omega
        let cNext : SaveMarkerCopyState :=
          { br := c.br + 1, nb := .ref rnb (offnb + 1), bb := c.bb - 1,
            dp := .ref (.heap bd) (offD + c.br.toNat + 1) }
        refine ⟨(c.bb - 1).toNat, cNext, hx', ?_, hbbDec,
          rfl, hpx', hdx, hmx, hmax, hcx, hqx, hhx, hsmx, hsrx, hex, hmex, hcox,
          ⟨arrX.set! (offD + c.br.toNat) bsnb[offnb]!, hbdX'raw, hszX'⟩,
          by rw [hbrAddTo]; omega, UInt32.le_iff_toNat_le.mpr (by rw [hbrAddTo]; omega),
          fun _ => Or.inl (by rw [hbrAddTo]; omega), by rw [hbrAddTo]; rfl, hcurX', htrX'⟩
        rw [C.run_bind, hlnb']; dsimp only
        rw [C.run_bind, hstDp']; dsimp only
        rw [C.run_bind, haddDp']; dsimp only
        rw [C.run_bind, haddNb']; rfl
      · have hcndF : (c.br < dataLength && c.bb > 0) = false := by
          cases hc : (c.br < dataLength && c.bb > 0) <;> simp_all
        refine ⟨false, c, hx, (by simp only [C.run, pure, hcndF]), ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hprog' : br0 < dataLength → br0.toNat < c.br.toNat := by
          intro hlt
          rcases hbrProg hlt with hgt | hbeq
          · exact hgt
          · have hbbPos : c.bb > 0 := by rw [hbeq]; exact hbi1Pos
            cases hcb : decide (c.br < dataLength)
            · have hle : dataLength.toNat ≤ c.br.toNat :=
                Nat.not_lt.mp (fun h => by have : decide (c.br < dataLength) = true := decide_eq_true (UInt32.lt_iff_toNat_lt.mpr h); rw [this] at hcb; cases hcb)
              have hltNat : br0.toNat < dataLength.toNat := hlt
              exact Nat.lt_of_lt_of_le hltNat hle
            · have hlt1 : c.br < dataLength := of_decide_eq_true hcb
              have : (c.br < dataLength && c.bb > 0) = true := by simp [hlt1, hbbPos]
              rw [this] at hcndF; cases hcndF
        exact ⟨hpx, hdx, hmx, hmax, hcx, hqx, hhx, hsmx, hsrx, hex, hmex, hcox,
          ⟨arrX, hbdX, hszX⟩, hbrLo, hbrHi, hprog', hdpX, hcurX, htrX⟩)
    hbi1Lt
    (s := { br := br0, nb := n1, bb := bi1, dp := dp0 })
    ⟨rfl, hp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨arrD, hbd, rfl⟩,
      Nat.le_refl _, hbrLe, fun _ => Or.inr rfl, hdp0, hcur1, htrInit⟩
  exact ⟨cs, h', hrun, hpost⟩

private theorem parserEnv_compInfo_of_sawSOF {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h)
    {dcs : Array C.JpegDecompressStruct} {mrks : Array C.JpegMarkerReader}
    (hgdc : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs)
    (hgmrk : C.Space.get h ctx.rmrk = some mrks)
    (hsaw : mrks[0]!.sawSOF ≠ 0) : dcs[0]!.compInfo ≠ .null := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, _errs, _mems, _masters, _ics, _mrks, _srcs,
    _hgdc, _hszdc, _hdc, _herrp, _hgerr, _hszerr, _hrem, _hnw0,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    _hcurm, _hmlEnd, hsawOld, _⟩ := hp
  have hEq := Option.some.inj (hgmrk.symm.trans _hgmrk); subst hEq
  have hEqD := Option.some.inj (hgdc.symm.trans _hgdc); subst hEqD
  rw [← _hdc]; exact hsawOld hsaw

private theorem parserEnv_get_mlEnd {ctx : IoCtx} {h : C.Heap} (hp : ParserEnv ctx h)
    {dcs : Array C.JpegDecompressStruct} {masters : Array C.JpegDecompMaster}
    (hgdc : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs)
    (hgmas : C.Space.get h ctx.rmas = some masters) :
    dcs[0]!.markerList = .null ∨ masters[0]!.markerListEnd = .null ∨
      ∃ rsm off sms, masters[0]!.markerListEnd = .ref rsm off ∧
        C.Space.get h rsm = some sms ∧ off < sms.size := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, _errs, _mems, _masters, _ics, _mrks, _srcs,
    _hgdc, _hszdc, _hdc, _herrp, _hgerr, _hszerr, _hrem, _hnw0,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    _hcurm, hmlEnd, _⟩ := hp
  have hEqM := Option.some.inj (hgmas.symm.trans _hgmas); subst hEqM
  have hEqD := Option.some.inj (hgdc.symm.trans _hgdc); subst hEqD
  simpa [← _hdc] using hmlEnd

private theorem save_marker_loop_parser {ctx : IoCtx} {h0 h : C.Heap}
    (hp0 : ParserEnv ctx h0) (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63)
    (hstd0 : DecompHeaderStable ctx h0 h)
    {br0 dataLength : UInt32} (hbrLe : br0 ≤ dataLength) (hdlLe : dataLength.toNat ≤ 65535)
    {rsm : C.SavedMarkerRef} {offSm : Nat} {sms0 : Array C.JpegSavedMarker}
    (hgsm0 : C.Space.get h rsm = some sms0) (hoffSm : offSm < sms0.size)
    (hcurM0 : ∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
      0 < dataLength.toNat → mrks[0]!.curMarker = .ref rsm offSm ∧
      sms0[offSm]!.dataLength = dataLength ∧ sms0[offSm]!.originalLength.toNat ≤ 65535)
    {bd offD : Nat} {arrD : Array UInt8}
    (hdpSpec : 0 < dataLength.toNat →
      sms0[offSm]!.data = .ref (.heap bd) offD ∧ h.bytes bd = some arrD ∧ offD + dataLength.toNat ≤ arrD.size)
    {curNib : C.BPtr} {curBib : UInt64} (hcur0 : CurValid h curNib curBib)
    {dataPtr : C.BPtr} (hdp0 : 0 < dataLength.toNat → dataPtr = .ref (.heap bd) (offD + br0.toNat))
    {nd0 el0 : Int} (hel0Lo : 0 ≤ el0) (hel0 : el0 ≤ 2) (hnd0 : nd0 ≤ 0)
    (htr0 : NibBibTrack ctx h0 h curNib curBib nd0 el0) :
    ∃ st h',
      C.run (cwhile
        (fun (s : SaveMarkerState) => pure (!s.done && s.bytesRead < dataLength, s))
        (fun (s : SaveMarkerState) => do
          inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib
          let dcS ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
          let mrkS ← Ptr.load dcS.marker
          Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
          match (← makeByteAvail (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
          | none => return { s with done := true, susp := true }
          | some (n1, bi1) =>
            let cs ← cwhile
              (fun (c : SaveMarkerCopyState) => pure (c.br < dataLength && c.bb > 0, c))
              (fun (c : SaveMarkerCopyState) => do
                let b ← Ptr.load c.nb
                Ptr.store c.dp b
                let dp' ← Ptr.add c.dp 1
                let nb' ← Ptr.add c.nb 1
                return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
              { br := s.bytesRead, nb := n1, bb := bi1, dp := s.dp }
            return { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp })
        { done := false, susp := false, bytesRead := br0, nib := curNib, bib := curBib, dp := dataPtr }) h =
        .ok (st, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h0 h' ∧
      h'.decomps = h.decomps ∧ h'.masters = h.masters ∧ h'.comps = h.comps ∧
      h'.quants = h.quants ∧ h'.huffs = h.huffs ∧ h'.savedMarkers = h.savedMarkers ∧
      h'.mems = h.mems ∧ h'.consts = h.consts ∧
      (∀ arrX, h.bytes bd = some arrX → ∃ arrX', h'.bytes bd = some arrX' ∧ arrX'.size = arrX.size) ∧
      (st.susp = false →
        br0.toNat ≤ st.bytesRead.toNat ∧ st.bytesRead = dataLength ∧
        CurValid h' st.nib st.bib ∧
        NibBibTrack ctx h0 h' st.nib st.bib
          (nd0 - 4 * (dataLength.toNat - br0.toNat : Int))
          (el0 + (dataLength.toNat - br0.toNat : Int))) := by
  let Inv : Nat → C.Heap → SaveMarkerState → Prop := fun k hx s =>
    ParserEnv ctx hx ∧
    DecompHeaderStable ctx h0 hx ∧
    hx.decomps = h.decomps ∧ hx.masters = h.masters ∧ hx.comps = h.comps ∧
    hx.quants = h.quants ∧ hx.huffs = h.huffs ∧ hx.savedMarkers = h.savedMarkers ∧
    hx.mems = h.mems ∧ hx.consts = h.consts ∧
    (∀ arrX, h.bytes bd = some arrX → ∃ arrX', hx.bytes bd = some arrX' ∧ arrX'.size = arrX.size) ∧
    (s.done = true → k = 0 ∧ s.susp = true) ∧
    (s.done = false →
      s.susp = false ∧
      k = dataLength.toNat - s.bytesRead.toNat ∧
      br0.toNat ≤ s.bytesRead.toNat ∧ s.bytesRead ≤ dataLength ∧
      CurValid hx s.nib s.bib ∧
      NibBibTrack ctx h0 hx s.nib s.bib
        (nd0 - 4 * (s.bytesRead.toNat - br0.toNat : Int))
        (el0 + (s.bytesRead.toNat - br0.toNat : Int)) ∧
      (0 < dataLength.toNat →
        s.dp = .ref (.heap bd) (offD + s.bytesRead.toNat) ∧
        ∃ mrksX, C.Space.get hx ctx.rmrk = some mrksX ∧ 0 < mrksX.size ∧
          mrksX[0]!.curMarker = .ref rsm offSm))
  let Post : C.Heap → SaveMarkerState → Prop := fun hx s =>
    ParserEnv ctx hx ∧
    DecompHeaderStable ctx h0 hx ∧
    hx.decomps = h.decomps ∧ hx.masters = h.masters ∧ hx.comps = h.comps ∧
    hx.quants = h.quants ∧ hx.huffs = h.huffs ∧ hx.savedMarkers = h.savedMarkers ∧
    hx.mems = h.mems ∧ hx.consts = h.consts ∧
    (∀ arrX, h.bytes bd = some arrX → ∃ arrX', hx.bytes bd = some arrX' ∧ arrX'.size = arrX.size) ∧
    (s.susp = false →
      br0.toNat ≤ s.bytesRead.toNat ∧ s.bytesRead = dataLength ∧
      CurValid hx s.nib s.bib ∧
      NibBibTrack ctx h0 hx s.nib s.bib
        (nd0 - 4 * (dataLength.toNat - br0.toNat : Int))
        (el0 + (dataLength.toNat - br0.toNat : Int)))
  have hk0Lt : dataLength.toNat - br0.toNat < C.fuel := by
    unfold C.fuel; omega
  have htrInit : NibBibTrack ctx h0 h curNib curBib
      (nd0 - 4 * (br0.toNat - br0.toNat : Int))
      (el0 + (br0.toNat - br0.toNat : Int)) := by
    simpa using htr0
  obtain ⟨st, h', hrun, hpost⟩ := cwhile_terminates
    (fun (s : SaveMarkerState) => pure (!s.done && s.bytesRead < dataLength, s))
    (fun (s : SaveMarkerState) => do
      inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib
      let dcS ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
      let mrkS ← Ptr.load dcS.marker
      Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
      match (← makeByteAvail (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
      | none => return { s with done := true, susp := true }
      | some (n1, bi1) =>
        let cs ← cwhile
          (fun (c : SaveMarkerCopyState) => pure (c.br < dataLength && c.bb > 0, c))
          (fun (c : SaveMarkerCopyState) => do
            let b ← Ptr.load c.nb
            Ptr.store c.dp b
            let dp' ← Ptr.add c.dp 1
            let nb' ← Ptr.add c.nb 1
            return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
          { br := s.bytesRead, nb := n1, bb := bi1, dp := s.dp }
        return { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp })
    Inv Post
    (fun k hx s ⟨hpX, hstX, hdX, hmaX, hcpX, hqX, hhuX, hsmX, hmeX, hcoX, hbyX, hdoneX, hactX⟩ => by
      by_cases hcnd : (!s.done && s.bytesRead < dataLength) = true
      · refine ⟨true, s, hx, (by simp only [C.run, pure, hcnd]), ?_⟩
        simp only [↓reduceIte]
        have hsDoneF : s.done = false := by cases hc : s.done <;> simp_all
        have hbrLt : s.bytesRead < dataLength := by
          by_cases h1 : s.bytesRead < dataLength <;> simp_all
        have hbrLtNat : s.bytesRead.toNat < dataLength.toNat := hbrLt
        have hdlPos : 0 < dataLength.toNat := by omega
        obtain ⟨hsSuspF, hkEq, hbrLo, hbrHi, hcurS, htrS, hdlInfo⟩ := hactX hsDoneF
        obtain ⟨hdpS, mrksS, hgmrkS, hszmrkS, hcurMrkS⟩ := hdlInfo hdlPos
        obtain ⟨hdatEq, hbd0, hwb0⟩ := hdpSpec hdlPos
        obtain ⟨arrX, hbdX, hszArrX⟩ := hbyX arrD hbd0
        obtain ⟨h1, hsync1, hp1, hd1, hmr1, he1, hma1, hcp1, hq1, hhu1, hsm1, hby1, hme1, hco1, _⟩ :=
          inputSync_parser hpX s.nib s.bib hcurS
        have hst1 := decompHeaderStable_trans hp0 hpX hstX (decompHeaderStable_of_same hd1 hmr1 hcp1)
        obtain ⟨dcs1, hgdc1, hszdc1, _, _, _, _, kmrk1, _⟩ := parserEnv_get_dc hp1
        have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc1
        obtain ⟨mrks1, hgmrk1, hszmrk1, _, _, _, _, _, hllSz1⟩ := parserEnv_get_mrk hp1
        have hlmrk1 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk1 hszmrk1
        have hlmrk1' : C.run (Ptr.load dcs1[0]!.marker) h1 = .ok (mrks1[0]!, h1) := by
          rw [kmrk1]; exact hlmrk1
        have hroM : C.Space.ro h1 ctx.rmrk = false := rfl
        let mrkNew := { mrks1[0]! with bytesRead := s.bytesRead }
        have hstMrk := ptr_store_ok (r := ctx.rmrk) (off := 0) (v := mrkNew) hgmrk1 hroM hszmrk1
        have hstMrk' : C.run (Ptr.store dcs1[0]!.marker mrkNew) h1 =
            .ok ((), C.Space.put h1 ctx.rmrk (mrks1.set! 0 mrkNew)) := by
          rw [kmrk1]; exact hstMrk
        let h2 := C.Space.put h1 ctx.rmrk (mrks1.set! 0 mrkNew)
        have hmrk1Eq : mrks1 = mrksS := by
          rcases hrM : ctx.rmrk with ⟨bm⟩
          simp only [C.Space.get, hrM, hmr1] at hgmrk1 hgmrkS
          exact Option.some.inj (hgmrk1.symm.trans hgmrkS)
        have hgsm1 : C.Space.get h1 rsm = some sms0 := by
          rcases hrS : rsm with ⟨bsm⟩
          simp only [C.Space.get, hrS, hsm1, hsmX] at hgsm0 ⊢; exact hgsm0
        have hby1Arr : h1.bytes bd = some arrX := by rw [hby1]; exact hbdX
        have hm1_0 : mrks1[0]!.curMarker = .ref rsm offSm := by rw [hmrk1Eq]; exact hcurMrkS
        obtain ⟨mrks_0, hgmrk0_0, hszmrk0_0, _⟩ := parserEnv_get_mrk hp
        have hcurM0' := hcurM0 mrks_0 hgmrk0_0 hszmrk0_0 hdlPos
        have hp2 : ParserEnv ctx h2 := by
          refine parserEnv_put_mrk hp1 hgmrk1 hszmrk1 rfl rfl rfl rfl hllSz1 ?_
            (fun dcs hg hsz hne => parserEnv_compInfo_of_sawSOF hp1 hg hgmrk1 hne)
          right
          refine ⟨rsm, offSm, sms0, sms0[offSm]!, hm1_0, hgsm1, hoffSm, rfl, ?_, hcurM0'.2.2, ?_, ?_⟩
          · rw [hcurM0'.2.1]; exact hdlLe
          · refine ⟨bd, offD, arrX, hdatEq, hby1Arr, ?_⟩; rw [hcurM0'.2.1, hszArrX]; exact hwb0
          · rw [hcurM0'.2.1]; exact hbrHi
        have hst12 : DecompHeaderStable ctx h1 h2 := by
          refine ⟨(fun da db hga _ hgb _ => by
            have hd2 : h2.decomps = h1.decomps := rfl
            dsimp only [C.Space.get] at hga hgb; rw [hd2] at hgb; rw [Option.some.inj (hgb.symm.trans hga)]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩), ?_, (fun _ _ _ hg hi => ⟨_, hg, hi, rfl, rfl, rfl⟩)⟩
          intro ma mb hga _ hgb _
          have hg2m : C.Space.get h2 ctx.rmrk = some (mrks1.set! 0 mrkNew) := by
            simp [h2, C.Space.get, C.Space.put]
          rw [Option.some.inj (hga.symm.trans hgmrk1), Option.some.inj (hgb.symm.trans hg2m),
            set0_bang_m mrks1 hszmrk1 mrkNew]
        have hst2 := decompHeaderStable_trans hp0 hp1 hst1 hst12
        have hcur2 : CurValid h2 s.nib s.bib := curValid_bytes_irrel hby1 hco1 hcurS
        have htr2 : NibBibTrack ctx h0 h2 s.nib s.bib
            (nd0 - 4 * (s.bytesRead.toNat - br0.toNat : Int))
            (el0 + (s.bytesRead.toNat - br0.toNat : Int)) :=
          nibBibTrack_err_same (nibBibTrack_err_same htrS he1) rfl
        have hbd2 : s.bib = 0 → ∀ errs, C.Space.get h2 ctx.rerr = some errs → 0 < errs.size →
            errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 := fun _ =>
          nibBibTrack_bd hp0 hp2 htr2 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
            have h1' := hhead e0 s0 he0 hse0 hs0 hss0
            have : s.bytesRead.toNat < dataLength.toNat := hbrLt
            have : max (el0 + (s.bytesRead.toNat - br0.toNat : Int)) 0 ≤ 65537 := by omega
            omega)
        obtain ⟨resMba, h3, hmba3, hp3, hd3, hmr3, hma3, hcp3, hq3, hhu3, hsm3, hby3, hme3, hco3, hpostMba⟩ :=
          makeByteAvail_parser hp2 s.nib s.bib hcur2 hbd2
        have hst3 := decompHeaderStable_trans hp0 hp2 hst2 (decompHeaderStable_of_same hd3 hmr3 hcp3)
        have hEqPre : ∀ {α : Type} (k : Option (C.BPtr × UInt64) → C.M α),
            C.run (do
              inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib
              let dcS ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
              let mrkS ← Ptr.load dcS.marker
              Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
              let res ← makeByteAvail (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib
              k res) hx = C.run (k resMba) h3 := by
          intro _ k
          rw [C.run_bind, hsync1]; dsimp only
          rw [C.run_bind, hldc1]; dsimp only
          rw [C.run_bind, hlmrk1']; dsimp only
          rw [C.run_bind, hstMrk']; dsimp only
          rw [C.run_bind, hmba3]
        have hby2 : h2.bytes = h1.bytes := rfl
        cases resMba with
        | none =>
          obtain hEq3 := hpostMba
          have hbyX3 : ∀ aX, h.bytes bd = some aX → ∃ aX', h3.bytes bd = some aX' ∧ aX'.size = aX.size := by
            intro aX hba
            obtain ⟨aX', hx', hsz'⟩ := hbyX aX hba
            exact ⟨aX', by rw [hby3, hby2, hby1]; exact hx', hsz'⟩
          refine ⟨0, { s with done := true, susp := true }, h3, ?_, by omega, hp3, hst3,
            hd3.trans hd1 |>.trans hdX, hma3.trans hma1 |>.trans hmaX, hcp3.trans hcp1 |>.trans hcpX,
            hq3.trans hq1 |>.trans hqX, hhu3.trans hhu1 |>.trans hhuX, hsm3.trans hsm1 |>.trans hsmX,
            hme3.trans hme1 |>.trans hmeX, hco3.trans hco1 |>.trans hcoX, hbyX3,
            (fun _ => ⟨rfl, rfl⟩), (fun hno => by simp at hno)⟩
          exact (hEqPre _).trans rfl
        | some pMba =>
          rcases pMba with ⟨n1, bi1⟩
          rcases hpostMba with ⟨hbi1Pos, hcur3, hce3⟩
          have htr3 : NibBibTrack ctx h0 h3 n1 bi1
              (nd0 - 4 * (s.bytesRead.toNat - br0.toNat : Int))
              (el0 + (s.bytesRead.toNat - br0.toNat : Int) + 1) := by
            intro e0 e3 s0 he0 hse0 he3 hse3 hs0 hss0
            obtain ⟨e2, he2, hse2, _⟩ := parserEnv_get_err hp2
            obtain ⟨ta, tb, tc⟩ := htr2 e0 e2 s0 he0 hse0 he2 hse2 hs0 hss0
            by_cases hnf3 : isConstEofPtr n1 = false
            · simp only [hnf3, ↓reduceIte] at hce3
              rcases hce3 with ⟨hn1Eq, hbi1Eq, _, hh3⟩
              subst hh3
              have heEq := Option.some.inj (he3.symm.trans he2); subst heEq
              rw [hn1Eq, hbi1Eq]
              obtain ⟨b1, b2, b3⟩ := tb (by rw [← hn1Eq]; exact hnf3)
              exact ⟨(fun hs0t => by rw [hn1Eq, ta hs0t] at hnf3; cases hnf3),
                ⟨(fun _ => ⟨b1, b2, b3⟩), (fun htr => by rw [← hn1Eq] at htr; rw [htr] at hnf3; cases hnf3)⟩⟩
            · have ht3 : isConstEofPtr n1 = true := by cases hc : isConstEofPtr n1 <;> simp_all
              simp only [ht3, Bool.true_eq_false, ↓reduceIte] at hce3
              have hnw3 := (hce3 e2 e3 he2 hse2 he3).2
              refine ⟨(fun _ => ht3), ⟨(fun hno => by rw [ht3] at hno; cases hno), (fun _ => ?_)⟩⟩
              by_cases hnf2 : isConstEofPtr s.nib = false
              · obtain ⟨hs0f, _, hbw2⟩ := tb hnf2
                simp only [warnPotVal, hs0f, Bool.false_eq_true, ↓reduceIte] at hbw2 ⊢
                split at hnw3 <;> omega
              · have ht2 : isConstEofPtr s.nib = true := by cases hc : isConstEofPtr s.nib <;> simp_all
                have := tc ht2
                by_cases hs0 : isConstEofPtr s0[0]!.nextInputByte = true
                · simp only [hs0, ↓reduceIte] at this ⊢; split at hnw3 <;> omega
                · simp only [hs0, Bool.false_eq_true, ↓reduceIte] at this ⊢; split at hnw3 <;> omega
          have hbd3 : h3.bytes bd = some arrX := by
            rw [hby3, hby2]; exact hby1Arr
          have hwb3 : offD + dataLength.toNat ≤ arrX.size := by rw [hszArrX]; exact hwb0
          obtain ⟨cs, h4, hcopy, hp4, hd4, hmr4, hma4, hcp4, hq4, hhu4, hsm4, hsr4, he4, hme4, hco4,
              ⟨arr4, hbd4, hsz4⟩, hbrLo4, hbrHi4, hbrProg4, hdp4, hcur4, htr4⟩ :=
            save_marker_copy_parser hp0 hp3 hbrHi hdlLe hbd3 hwb3 hcur3 hbi1Pos hdpS htr3
          have hst4 := decompHeaderStable_trans hp0 hp3 hst3 (decompHeaderStable_of_same hd4 hmr4 hcp4)
          have hbyX4 : ∀ aX, h.bytes bd = some aX → ∃ aX', h4.bytes bd = some aX' ∧ aX'.size = aX.size := by
            intro aX hba
            obtain ⟨aX0, hx0, hsz0⟩ := hbyX aX hba
            have haEq : aX0 = arrX := Option.some.inj (hx0.symm.trans hbdX)
            exact ⟨arr4, hbd4, by rw [hsz4, ← haEq, hsz0]⟩
          have hstepProg : s.bytesRead.toNat < cs.br.toNat := hbrProg4 hbrLt
          have hdec : dataLength.toNat - cs.br.toNat < k := by
            have : cs.br.toNat ≤ dataLength.toNat := hbrHi4
            omega
          have hmrk4Eq : ∃ mrks4, C.Space.get h4 ctx.rmrk = some mrks4 ∧ 0 < mrks4.size ∧
              mrks4[0]!.curMarker = .ref rsm offSm := by
            have hg2 : C.Space.get h2 ctx.rmrk = some (mrks1.set! 0 mrkNew) := by
              simp [h2, C.Space.get, C.Space.put]
            have hg4 : C.Space.get h4 ctx.rmrk = some (mrks1.set! 0 mrkNew) := by
              rcases hrM : ctx.rmrk with ⟨bm⟩
              simp only [C.Space.get, hrM, hmr4, hmr3] at hg2 ⊢; exact hg2
            refine ⟨mrks1.set! 0 mrkNew, hg4, by simpa using hszmrk1, ?_⟩
            rw [set0_bang_m mrks1 hszmrk1 mrkNew]
            exact hm1_0
          refine ⟨dataLength.toNat - cs.br.toNat,
            { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp },
            h4, ?_, hdec, hp4, hst4,
            hd4.trans (hd3.trans (hd1.trans hdX)),
            hma4.trans (hma3.trans (hma1.trans hmaX)),
            hcp4.trans (hcp3.trans (hcp1.trans hcpX)),
            hq4.trans (hq3.trans (hq1.trans hqX)),
            hhu4.trans (hhu3.trans (hhu1.trans hhuX)),
            hsm4.trans (hsm3.trans (hsm1.trans hsmX)),
            hme4.trans (hme3.trans (hme1.trans hmeX)),
            hco4.trans (hco3.trans (hco1.trans hcoX)),
            hbyX4, (fun hd => by cases hd), fun _ => ⟨rfl, rfl, by dsimp only; omega, hbrHi4, hcur4, ?_, fun _ => ⟨hdp4, hmrk4Eq⟩⟩⟩
          · rw [hEqPre]; dsimp only
            rw [C.run_bind]; erw [hcopy]; rfl
          · refine nibBibTrack_mono htr4 (by dsimp only; omega) (by dsimp only; omega)
      · have hcndF : (!s.done && s.bytesRead < dataLength) = false := by
          cases hc : (!s.done && s.bytesRead < dataLength) <;> simp_all
        refine ⟨false, s, hx, (by simp only [C.run, pure, hcndF]), ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨hpX, hstX, hdX, hmaX, hcpX, hqX, hhuX, hsmX, hmeX, hcoX, hbyX, fun hsuspF => ?_⟩
        have hsDoneF : s.done = false := by
          cases hc : s.done
          · rfl
          · rw [(hdoneX hc).2] at hsuspF; cases hsuspF
        obtain ⟨_, _, hbrLo, hbrHi, hcurS, htrS, _⟩ := hactX hsDoneF
        have hbrGe : dataLength.toNat ≤ s.bytesRead.toNat := by
          simp [hsDoneF] at hcndF
          exact UInt32.le_iff_toNat_le.mp hcndF
        have hbrEq : s.bytesRead = dataLength := by
          have hhi : s.bytesRead.toNat ≤ dataLength.toNat := hbrHi
          have heqNat : s.bytesRead.toNat = dataLength.toNat := Nat.le_antisymm hhi hbrGe
          rcases h1 : s.bytesRead with ⟨bv1⟩
          rcases h2 : dataLength with ⟨bv2⟩
          rw [h1, h2] at heqNat
          congr 1
          exact BitVec.eq_of_toNat_eq heqNat
        refine ⟨hbrLo, hbrEq, hcurS, ?_⟩
        rw [← hbrEq]; exact htrS)
    hk0Lt
    (s := { done := false, susp := false, bytesRead := br0, nib := curNib, bib := curBib, dp := dataPtr })
    ⟨hp, hstd0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => ⟨_, h, rfl⟩,
      (fun hd => False.elim (Bool.noConfusion hd)), fun _ => ⟨rfl, rfl, Nat.le_refl _, hbrLe, hcur0, htrInit,
      fun hdl => ⟨hdp0 hdl, by obtain ⟨mrks, hg, hsz, _⟩ := parserEnv_get_mrk hp; exact ⟨mrks, hg, hsz, (hcurM0 mrks hg hsz hdl).1⟩⟩⟩⟩
  exact ⟨st, h', hrun, hpost⟩

private theorem parserEnv_put_sm_next {ctx : IoCtx} {h : C.Heap}
    {rsmTail : C.SavedMarkerRef} {smsTail : Array C.JpegSavedMarker} {offTail : Nat}
    {curMarker : C.SavedMarkerPtr}
    (hp : ParserEnv ctx h) (hg : C.Space.get h rsmTail = some smsTail) (hoff : offTail < smsTail.size) :
    ParserEnv ctx (C.Space.put h rsmTail (smsTail.set! offTail { smsTail[offTail]! with next := curMarker })) := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, _errs, _mems, _masters, _ics, mrks0, _srcs,
    _hgdc, _hszdc, _hdc, _herrp, _hgerr, _hszerr, _hrem, _hnw0,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, hgmrk0, _hszmrk0, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    hcurm0, _⟩ := id hp
  refine parserEnv_put_sm hp hg hoff (fun mrks hgmrk _ hcur => ?_)
  have hmEq := Option.some.inj (hgmrk.symm.trans hgmrk0)
  subst hmEq
  rcases hcurm0 with hnull | ⟨rsm0, off0, sms0, sm0, hcm0, hg0, hoff0, hsm0, hdl0, hol0, hwb0, hbr0⟩
  · rw [hnull] at hcur; cases hcur
  · have hrc := hcm0.symm.trans hcur
    injection hrc with hrr hoo
    cases hrr; subst hoo
    have hsEq := Option.some.inj (hg0.symm.trans hg)
    subst hsEq
    have hsmEq : sms0[off0]! = sm0 := hsm0.symm
    change ({ sms0[off0]! with next := curMarker }.dataLength.toNat ≤ 65535 ∧
      { sms0[off0]! with next := curMarker }.originalLength.toNat ≤ 65535 ∧
      WritableBytes h { sms0[off0]! with next := curMarker }.data
        { sms0[off0]! with next := curMarker }.dataLength.toNat ∧
      mrks[0]!.bytesRead ≤ { sms0[off0]! with next := curMarker }.dataLength)
    dsimp only
    rw [hsmEq]
    exact ⟨hdl0, hol0, hwb0, hbr0⟩

private theorem parserEnv_put_dc_and_mst {ctx : IoCtx} {h : C.Heap}
    {dcs : Array C.JpegDecompressStruct} {masters : Array C.JpegDecompMaster}
    {dc' : C.JpegDecompressStruct} {mst' : C.JpegDecompMaster}
    (hp : ParserEnv ctx h) (hgdc : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (hszdc : 0 < dcs.size)
    (hgmas : C.Space.get h ctx.rmas = some masters) (hszmas : 0 < masters.size)
    (kerr : dc'.err = dcs[0]!.err) (kmem : dc'.mem = dcs[0]!.mem) (kmas : dc'.master = dcs[0]!.master)
    (kic : dc'.inputctl = dcs[0]!.inputctl) (kmrk : dc'.marker = dcs[0]!.marker) (ksrc : dc'.src = dcs[0]!.src)
    (hcomp : dc'.compInfo = dcs[0]!.compInfo ∧ dc'.numComponents = dcs[0]!.numComponents)
    (hqtEq : dc'.quantTblPtrs = dcs[0]!.quantTblPtrs)
    (hdhEq : dc'.dcHuffTblPtrs = dcs[0]!.dcHuffTblPtrs)
    (hahEq : dc'.acHuffTblPtrs = dcs[0]!.acHuffTblPtrs)
    (hcc : dc'.curCompInfo = dcs[0]!.curCompInfo)
    (hisn : dc'.inputScanNumber = dcs[0]!.inputScanNumber)
    (hml : mst'.markerListEnd = .null ∨
      ∃ rsm off sms, mst'.markerListEnd = .ref rsm off ∧ C.Space.get h rsm = some sms ∧ off < sms.size) :
    ParserEnv ctx
      (C.Space.put (C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 dc'))
        ctx.rmas (masters.set! 0 mst')) := by
  obtain ⟨hcore, hfr, dcs0, dc0, errs, mems, masters0, ics, mrks, srcs,
    hgdc0, hszdc0, hdc0, herrp, hgerr, hszerr, hrem, hnw0,
    hmemp, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    hmasp, hgmas0, hszmas0, hicp, hgic, hszic, hric, hci,
    hmrkp, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    hsrcp, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, _hmlEnd, hsawOld, hcompLiveOld, hqtSz, hqtP, hdhSz, hdhP, hahSz, hahP, hccSz, hisn0⟩ := hp
  have hdEq := Option.some.inj (hgdc.symm.trans hgdc0); subst hdEq
  have hmEq := Option.some.inj (hgmas.symm.trans hgmas0); subst hmEq
  rcases ctx with ⟨bdc, rerr, rmem, rmas, ric, rmrk, rs⟩
  rcases rmas with ⟨bm0⟩
  let h1 := C.Space.put h (C.DecompRef.decomp bdc) (dcs.set! 0 dc')
  let h2 := C.Space.put h1 (C.MasterRef.master bm0) (masters.set! 0 mst')
  have hgdc2 : C.Space.get h2 (C.DecompRef.decomp bdc) = some (dcs.set! 0 dc') := by
    simp [h2, h1, C.Space.get, C.Space.put, C.upd_same]
  have hgmas2 : C.Space.get h2 (C.MasterRef.master bm0) = some (masters.set! 0 mst') := by
    simp [h2, h1, C.Space.get, C.Space.put, C.upd_same]
  have hszdc2 : 0 < (dcs.set! 0 dc').size := by simpa using hszdc
  have hszmas2 : 0 < (masters.set! 0 mst').size := by simpa using hszmas
  have hdc2 : (dcs.set! 0 dc')[0]! = dc' := set0_bang_m dcs hszdc dc'
  have hmas2 : (masters.set! 0 mst')[0]! = mst' := set0_bang_m masters hszmas mst'
  have hcore2 : ValidDecompCore h2 (.ref (.decomp bdc) 0) := by
    apply validDecompCore_of_sameGraph hcore
    · refine ⟨dcs, dcs[0]!, dcs.set! 0 dc', dc', hgdc0, hszdc0, rfl, hgdc2, hszdc2, hdc2.symm,
        kerr, kmem, kmas, kic, kmrk⟩
    · intro r a hga hsza; exact ⟨a, hga, hsza⟩
    · intro r a hga hsza
      rcases r with ⟨bm⟩
      by_cases heq : bm = bm0
      · subst heq; exact ⟨masters.set! 0 mst', hgmas2, hszmas2⟩
      · exact ⟨a, by dsimp only [h2, h1, C.Space.get, C.Space.put] at hga ⊢; rw [C.upd_ne _ _ _ _ heq]; exact hga, hsza⟩
    · intro r a hga hsza; exact ⟨a, hga, hsza⟩
    · intro r a hga hsza; exact ⟨a, hga, hsza⟩
    · intro rm mems hgm hszm hpa; exact ⟨mems, hgm, hszm, hpa, rfl⟩
  have hfr2 : FreshNextBlk h2 := by
    intro k hk
    obtain ⟨hb, hi, hme, hma, hmr, hic, hsr, hcp, hq, hhu, hsm⟩ := hfr k hk
    refine ⟨hb, hi, hme, ?_, hmr, hic, hsr, hcp, hq, hhu, hsm⟩
    by_cases heq : k = bm0
    · subst heq; simp only [C.Space.get] at hgmas0; rw [hma] at hgmas0; cases hgmas0
    · dsimp only [h2, h1, C.Space.get, C.Space.put]; rw [C.upd_ne _ _ _ _ heq]; exact hma
  refine ⟨hcore2, hfr2, dcs.set! 0 dc', dc', errs, mems, masters.set! 0 mst', ics, mrks, srcs,
    hgdc2, hszdc2, hdc2.symm, ?_, hgerr, hszerr, hrem, hnw0,
    ?_, hgmem, hszmem, has, hfp, hsd, hlpSz, hlp0, hlp1, hpaSz, hpm, hpi, hpmk, hps,
    ?_, hgmas2, hszmas2, ?_, hgic, hszic, hric, hci,
    ?_, hgmrk, hszmrk, hrm, hrmr, hpcom, hpappSz, hpapp, hllSz,
    ?_, hgsrc, hszsrc, his, hts, hsip, hrtr, hfill, hcurv,
    hcurm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kerr, ← hdc0]; exact herrp
  · rw [kmem, ← hdc0]; exact hmemp
  · rw [kmas, ← hdc0]; exact hmasp
  · rw [kic, ← hdc0]; exact hicp
  · rw [kmrk, ← hdc0]; exact hmrkp
  · rw [ksrc, ← hdc0]; exact hsrcp
  · rw [hmas2]; right; exact hml
  · intro hsaw; rw [hcomp.1, ← hdc0]; exact hsawOld hsaw
  · intro hne
    have hne0 : dc0.compInfo ≠ .null := by rw [hdc0, ← hcomp.1]; exact hne
    obtain ⟨hn0, hlv⟩ := hcompLiveOld hne0
    refine ⟨by rw [hcomp.2, ← hdc0]; exact hn0, ?_⟩
    rcases hlv with ⟨r1, cs1, hp1, hg1, hsz1⟩
    exact ⟨r1, cs1, by rw [hcomp.1, ← hdc0]; exact hp1, hg1, by rw [hcomp.2, ← hdc0]; exact hsz1⟩
  · rw [hqtEq, ← hdc0]; exact hqtSz
  · rw [hqtEq, ← hdc0]; exact hqtP
  · rw [hdhEq, ← hdc0]; exact hdhSz
  · rw [hdhEq, ← hdc0]; exact hdhP
  · rw [hahEq, ← hdc0]; exact hahSz
  · rw [hahEq, ← hdc0]; exact hahP
  · rw [hcc, ← hdc0]; exact hccSz
  · rw [hisn, ← hdc0]; exact hisn0

private theorem save_marker_finish_parser {ctx : IoCtx} {h0 hS : C.Heap}
    (hp0 : ParserEnv ctx h0) (hpS : ParserEnv ctx hS)
    (hhead : ∀ errs0 srcs0, C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 18 < 2 ^ 63)
    (hst0S : DecompHeaderStable ctx h0 hS)
    (curMarker : C.SavedMarkerPtr) (dataLength : UInt32) (st : SaveMarkerState)
    (hdlLe : dataLength.toNat ≤ 65535)
    (hcurLive : curMarker ≠ .null →
      ∃ rsm offSm sms sm, curMarker = .ref rsm offSm ∧ C.Space.get hS rsm = some sms ∧ offSm < sms.size ∧
        sm = sms[offSm]! ∧ sm.dataLength = dataLength ∧ sm.originalLength.toNat ≤ 65535 ∧
        WritableBytes hS sm.data dataLength.toNat)
    (hcurS : CurValid hS st.nib st.bib)
    {ndS elS : Int} (hndS : ndS ≤ 0) (helSLo : 0 ≤ elS) (helS : elS ≤ 65536)
    (htrS : NibBibTrack ctx h0 hS st.nib st.bib ndS elS) :
    ∃ h',
      C.run (do
        let mut remLength : Int64 := 0
        let mut dataArr : Array UInt8 := #[]
        if curMarker != .null then
          let sm ← Ptr.load curMarker
          let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
          let mst ← Ptr.load dcCur.master
          if dcCur.markerList == .null || mst.markerListEnd == .null then
            Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcCur with markerList := curMarker }
            Ptr.store dcCur.master { mst with markerListEnd := curMarker }
          else
            let tail ← Ptr.load mst.markerListEnd
            Ptr.store mst.markerListEnd { tail with next := curMarker }
            Ptr.store dcCur.master { mst with markerListEnd := curMarker }
          remLength := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat dataLength.toNat)
          for k in List.range dataLength.toNat do
            let bp ← Ptr.add sm.data (Int.ofNat k)
            let v ← Ptr.load bp
            dataArr := dataArr.push v
        let dcA ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
        let mrkA ← Ptr.load dcA.marker
        Ptr.store dcA.marker { mrkA with curMarker := .null }
        if dcA.unreadMarker == M_APP0 then
          examine_app0 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr dataLength remLength
        else if dcA.unreadMarker == M_APP14 then
          examine_app14 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr dataLength remLength
        else
          tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
            (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt))
        inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib
        if remLength > 0 then
          skipInputDataDispatch (.ref (C.DecompRef.decomp ctx.bdc) 0) remLength
        return (JpegRes.ok true)) hS = Except.ok (JpegRes.ok true, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h0 h' ∧
      (∀ srcs0 srcs', C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
        SrcMono srcs0[0]! srcs'[0]!) ∧
      (∀ errs0 errs' srcs0 srcs',
        C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
        C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
        (isConstEofPtr srcs'[0]!.nextInputByte = false →
          warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + (if ndS ≤ -1 then 0 else 1)) ∧
        (isConstEofPtr srcs'[0]!.nextInputByte = true →
          errs'[0]!.numWarnings.toInt ≤
            (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
             else warnPotVal errs0 srcs0) + elS + 32770)) := by
  have hstep1 : ∃ remLength dataArr h1,
      (∀ {α : Type} (k : Int64 → Array UInt8 → C.M α),
        C.run (do
          let mut remLength : Int64 := 0
          let mut dataArr : Array UInt8 := #[]
          if curMarker != .null then
            let sm ← Ptr.load curMarker
            let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            let mst ← Ptr.load dcCur.master
            if dcCur.markerList == .null || mst.markerListEnd == .null then
              Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcCur with markerList := curMarker }
              Ptr.store dcCur.master { mst with markerListEnd := curMarker }
            else
              let tail ← Ptr.load mst.markerListEnd
              Ptr.store mst.markerListEnd { tail with next := curMarker }
              Ptr.store dcCur.master { mst with markerListEnd := curMarker }
            remLength := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat dataLength.toNat)
            for k in List.range dataLength.toNat do
              let bp ← Ptr.add sm.data (Int.ofNat k)
              let v ← Ptr.load bp
              dataArr := dataArr.push v
          k remLength dataArr) hS = C.run (k remLength dataArr) h1) ∧
      remLength.toInt ≤ 65535 ∧
      ParserEnv ctx h1 ∧ DecompHeaderStable ctx h0 h1 ∧
      h1.srcs = hS.srcs ∧ h1.errMgrs = hS.errMgrs ∧ h1.bytes = hS.bytes ∧ h1.consts = hS.consts := by
    by_cases hcmN : curMarker = .null
    · have hcmF : (curMarker != .null) = false := by simp [hcmN]
      refine ⟨0, #[], hS, (fun k => by simp [hcmF]), by decide, hpS, hst0S, rfl, rfl, rfl, rfl⟩
    · have hcmT : (curMarker != .null) = true := by simp [hcmN]
      obtain ⟨rsm, offSm, sms, sm, hcmEq, hgsm, hoffSm, hsmEq, _, holSm, hwbSm⟩ := hcurLive hcmN
      have hlsm := ptr_load_ok (r := rsm) (off := offSm) hgsm hoffSm
      have hlsm' : C.run (Ptr.load curMarker) hS = .ok (sm, hS) := by rw [hcmEq, hsmEq]; exact hlsm
      obtain ⟨dcsS, hgdcS, hszdcS, _, _, kmasS, _, _, _⟩ := parserEnv_get_dc hpS
      have hldcS := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcS hszdcS
      obtain ⟨mastersS, hgmasS, hszmasS⟩ := parserEnv_get_mas hpS
      have hlmasS := ptr_load_ok (r := ctx.rmas) (off := 0) hgmasS hszmasS
      have hlmasS' : C.run (Ptr.load dcsS[0]!.master) hS = .ok (mastersS[0]!, hS) := by
        rw [kmasS]; exact hlmasS
      have hroMas : C.Space.ro hS ctx.rmas = false := rfl
      have hroDc : C.Space.ro hS (C.DecompRef.decomp ctx.bdc) = false := rfl
      let remL : Int64 := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat dataLength.toNat)
      have hremLTo : remL.toInt = (sm.originalLength.toNat : Int) - (dataLength.toNat : Int) := by
        have hlenSm : Int.ofNat sm.originalLength.toNat = (sm.originalLength.toNat : Int) := rfl
        have hlenDl : Int.ofNat dataLength.toNat = (dataLength.toNat : Int) := rfl
        dsimp only [remL]; rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl, hlenSm, hlenDl]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      have hremLLe : remL.toInt ≤ 65535 := by rw [hremLTo]; omega
      have hloopStep : ∀ (hM : C.Heap) (hwbM : WritableBytes hM sm.data dataLength.toNat),
          ∃ arrM hF,
            C.run (forIn (List.range dataLength.toNat) #[] fun k dataArr => do
              let bp ← Ptr.add sm.data (Int.ofNat k)
              let v ← Ptr.load bp
              return ForInStep.yield (dataArr.push v)) hM = .ok (arrM, hF) ∧
            hF = hM := by
        intro hM hwbM
        rcases hwbM with ⟨bd, offD, bsD, hdatEq, hbdM, hwbLe⟩
        let ForInv : Nat → Array UInt8 → C.Heap → Prop := fun _ _ hX => hX = hM
        obtain ⟨arrF, hF, hfor, hFEq⟩ := forIn_range_inv ForInv
          (fun k dataArr => do
            let bp ← Ptr.add sm.data (Int.ofNat k)
            let v ← Ptr.load bp
            return ForInStep.yield (dataArr.push v))
          dataLength.toNat
          (fun k hk dataArr hX hXEq => by
            rw [hXEq]
            have hgB : C.Space.get hM (C.BRef.heap bd) = some bsD := hbdM
            have hkNat : k < dataLength.toNat := hk
            have hkI : Int.ofNat k = (k : Int) := rfl
            have hadd := ptr_add_ok (r := C.BRef.heap bd) (xs := bsD) (off := offD)
              (k := Int.ofNat k) hgB (by omega)
              (by rw [hkI]; omega)
              (by rw [hkI]; omega)
            have hadd' : C.run (Ptr.add sm.data (Int.ofNat k)) hM =
                .ok (.ref (.heap bd) (offD + k), hM) := by
              rw [hdatEq]
              have h1 : ((offD : Int) + (k : Int)).toNat = offD + k := by omega
              simpa [h1] using hadd
            have hlB := ptr_load_ok (r := C.BRef.heap bd) (off := offD + k) hgB (by omega)
            refine ⟨ForInStep.yield (dataArr.push bsD[offD + k]!), hM, ?_, rfl⟩
            rw [C.run_bind, hadd']; dsimp only
            rw [C.run_bind, hlB]; rfl)
          rfl
        rw [hFEq] at hfor
        exact ⟨arrF, hM, hfor, rfl⟩
      have hmlEndS := parserEnv_get_mlEnd hpS hgdcS hgmasS
      by_cases hmlN : (dcsS[0]!.markerList == .null || mastersS[0]!.markerListEnd == .null) = true
      · let dc1 := { dcsS[0]! with markerList := curMarker }
        let mst1 := { mastersS[0]! with markerListEnd := curMarker }
        have hstDc1 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dc1) hgdcS hroDc hszdcS
        let hA := C.Space.put hS (C.DecompRef.decomp ctx.bdc) (dcsS.set! 0 dc1)
        have hgmasA : C.Space.get hA ctx.rmas = some mastersS := hgmasS
        have hroMasA : C.Space.ro hA ctx.rmas = false := rfl
        have hstMas1 := ptr_store_ok (r := ctx.rmas) (off := 0) (v := mst1) hgmasA hroMasA hszmasS
        have hstMas1' : C.run (Ptr.store dcsS[0]!.master mst1) hA =
            .ok ((), C.Space.put hA ctx.rmas (mastersS.set! 0 mst1)) := by
          rw [kmasS]; exact hstMas1
        let hB := C.Space.put hA ctx.rmas (mastersS.set! 0 mst1)
        have hgsmB : C.Space.get hB rsm = some sms := by
          cases rsm with
          | savedMarker bs =>
            dsimp only [hB, hA, C.Space.get, C.Space.put] at hgsm ⊢; exact hgsm
        have hpB : ParserEnv ctx hB :=
          parserEnv_put_dc_and_mst hpS hgdcS hszdcS hgmasS hszmasS
            rfl rfl rfl rfl rfl rfl ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
            (Or.inr ⟨rsm, offSm, sms, hcmEq, hgsmB, hoffSm⟩)
        have hstSB : DecompHeaderStable ctx hS hB := by
          refine ⟨fun da db ha _ hb _ => ?_, (fun ma mb ha _ hb _ => by
            have hmB : hB.markers = hS.markers := rfl
            dsimp only [C.Space.get] at ha hb; rw [hmB] at hb; rw [Option.some.inj (hb.symm.trans ha)]),
            fun _ _ _ hg hi => ⟨_, hg, hi, rfl, rfl, rfl⟩⟩
          have hgdcB : C.Space.get hB (C.DecompRef.decomp ctx.bdc) = some (dcsS.set! 0 dc1) := by
            simp [hB, hA, C.Space.get, C.Space.put, C.upd_same]
          rw [Option.some.inj (ha.symm.trans hgdcS), Option.some.inj (hb.symm.trans hgdcB),
            set0_bang_m dcsS hszdcS dc1]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hst0B := decompHeaderStable_trans hp0 hpS hst0S hstSB
        obtain ⟨arrF, hF, hforF, hFEq⟩ := hloopStep hB hwbSm
        rw [hFEq] at hforF
        refine ⟨remL, arrF, hB, ?_, hremLLe, hpB, hst0B, rfl, rfl, rfl, rfl⟩
        intro _ kFn
        simp only [hcmT, ↓reduceIte]
        rw [C.run_bind, hlsm']; dsimp only
        rw [C.run_bind, hldcS]; dsimp only
        rw [C.run_bind, hlmasS']; dsimp only
        simp only [hmlN, ↓reduceIte]
        rw [C.run_bind, hstDc1]; dsimp only
        rw [C.run_bind, hstMas1']; dsimp only
        rw [C.run_bind, hforF]
      · have hmlF : (dcsS[0]!.markerList == .null || mastersS[0]!.markerListEnd == .null) = false := by
          cases hc : (dcsS[0]!.markerList == .null || mastersS[0]!.markerListEnd == .null) <;> simp_all
        have hmlNe : mastersS[0]!.markerListEnd ≠ .null := by intro hz; simp [hz] at hmlF
        have hdmlNe : dcsS[0]!.markerList ≠ .null := by intro hz; simp [hz] at hmlF
        rcases hmlEndS with h1 | h2 | ⟨rsmT, offT, smsT, hmleEq, hgT, hoffT⟩
        · exact absurd h1 hdmlNe
        · exact absurd h2 hmlNe
        · have hlTail := ptr_load_ok (r := rsmT) (off := offT) hgT hoffT
          have hlTail' : C.run (Ptr.load mastersS[0]!.markerListEnd) hS = .ok (smsT[offT]!, hS) := by
            rw [hmleEq]; exact hlTail
          have hroSmT : C.Space.ro hS rsmT = false := by cases rsmT; rfl
          let smTailNew := { smsT[offT]! with next := curMarker }
          have hstTail := ptr_store_ok (r := rsmT) (off := offT) (v := smTailNew) hgT hroSmT hoffT
          have hstTail' : C.run (Ptr.store mastersS[0]!.markerListEnd smTailNew) hS =
              .ok ((), C.Space.put hS rsmT (smsT.set! offT smTailNew)) := by
            rw [hmleEq]; exact hstTail
          let hA := C.Space.put hS rsmT (smsT.set! offT smTailNew)
          have hpA : ParserEnv ctx hA := parserEnv_put_sm_next hpS hgT hoffT
          have hgmasA : C.Space.get hA ctx.rmas = some mastersS := hgmasS
          have hroMasA : C.Space.ro hA ctx.rmas = false := rfl
          let mst1 := { mastersS[0]! with markerListEnd := curMarker }
          have hstMas1 := ptr_store_ok (r := ctx.rmas) (off := 0) (v := mst1) hgmasA hroMasA hszmasS
          have hstMas1' : C.run (Ptr.store dcsS[0]!.master mst1) hA =
              .ok ((), C.Space.put hA ctx.rmas (mastersS.set! 0 mst1)) := by
            rw [kmasS]; exact hstMas1
          let hB := C.Space.put hA ctx.rmas (mastersS.set! 0 mst1)
          have hgsmB : C.Space.get hB rsm = some (if rsm = rsmT then smsT.set! offT smTailNew else sms) := by
            cases rsm with
            | savedMarker b1 =>
              cases rsmT with
              | savedMarker b2 =>
                by_cases hbeq : b1 = b2
                · subst hbeq
                  have hEqR := Option.some.inj (hgT.symm.trans hgsm); subst hEqR
                  simp [hB, hA, C.Space.get, C.Space.put, C.upd_same]
                · dsimp only [hB, hA, C.Space.get, C.Space.put] at hgsm ⊢
                  split
                  · next heqR => cases heqR; exact False.elim (hbeq rfl)
                  · rw [C.upd_ne _ _ _ _ hbeq]; exact hgsm
          have hszB : offSm < (if rsm = rsmT then smsT.set! offT smTailNew else sms).size := by
            split
            · next heqR =>
              subst heqR
              have hEqR := Option.some.inj (hgT.symm.trans hgsm); subst hEqR
              simpa using hoffSm
            · simpa using hoffSm
          have hpB : ParserEnv ctx hB :=
            parserEnv_put_mst hpA hgmasA hszmasS (Or.inr (Or.inr ⟨rsm, offSm, _, hcmEq, hgsmB, hszB⟩))
          have hst0B := decompHeaderStable_trans hp0 hpS hst0S (decompHeaderStable_of_same rfl rfl rfl)
          obtain ⟨arrF, hF, hforF, hFEq⟩ := hloopStep hB hwbSm
          rw [hFEq] at hforF
          refine ⟨remL, arrF, hB, ?_, hremLLe, hpB, hst0B, rfl, rfl, rfl, rfl⟩
          intro _ kFn
          simp only [hcmT, ↓reduceIte]
          rw [C.run_bind, hlsm']; dsimp only
          rw [C.run_bind, hldcS]; dsimp only
          rw [C.run_bind, hlmasS']; dsimp only
          simp only [hmlF, Bool.false_eq_true, ↓reduceIte]
          rw [C.run_bind, hlTail']; dsimp only
          rw [C.run_bind, hstTail']; dsimp only
          rw [C.run_bind, hstMas1']; dsimp only
          rw [C.run_bind, hforF]
  rcases hstep1 with ⟨remLength, dataArr, h1, hrun1, hremLe, hp1, hst01, hsr1, he1, hby1, hco1⟩
  obtain ⟨dcs1, hgdc1, hszdc1, kerr1, _, _, _, kmrk1, _⟩ := parserEnv_get_dc hp1
  obtain ⟨mrks1, hgmrk1, hszmrk1, hrm1, hrmr1, hpcom1, _, hpapp1, hllSz1⟩ := parserEnv_get_mrk hp1
  have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc1
  have hlmrk1 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk1 hszmrk1
  have hlmrk1' : C.run (Ptr.load dcs1[0]!.marker) h1 = .ok (mrks1[0]!, h1) := by
    rw [kmrk1]; exact hlmrk1
  have hroM1 : C.Space.ro h1 ctx.rmrk = false := rfl
  let mrk2 := { mrks1[0]! with curMarker := .null }
  have hstMrk1 := ptr_store_ok (r := ctx.rmrk) (off := 0) (v := mrk2) hgmrk1 hroM1 hszmrk1
  have hstMrk1' : C.run (Ptr.store dcs1[0]!.marker mrk2) h1 =
      .ok ((), C.Space.put h1 ctx.rmrk (mrks1.set! 0 mrk2)) := by
    rw [kmrk1]; exact hstMrk1
  let h2 := C.Space.put h1 ctx.rmrk (mrks1.set! 0 mrk2)
  have hp2 : ParserEnv ctx h2 :=
    parserEnv_put_mrk hp1 hgmrk1 hszmrk1 rfl rfl rfl rfl hllSz1 (Or.inl rfl)
      (fun dcs hg hsz hne => parserEnv_compInfo_of_sawSOF hp1 hg hgmrk1 hne)
  have hst12 : DecompHeaderStable ctx h1 h2 := by
    refine ⟨(fun da db ha _ hb _ => by
      have hd2 : h2.decomps = h1.decomps := rfl
      dsimp only [C.Space.get] at ha hb; rw [hd2] at hb; rw [Option.some.inj (hb.symm.trans ha)]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩), ?_, (fun _ _ _ hg hi => ⟨_, hg, hi, rfl, rfl, rfl⟩)⟩
    intro ma mb ha _ hb _
    have hg2' : C.Space.get h2 ctx.rmrk = some (mrks1.set! 0 mrk2) := by
      simp [h2, C.Space.get, C.Space.put]
    rw [Option.some.inj (ha.symm.trans hgmrk1), Option.some.inj (hb.symm.trans hg2'),
      set0_bang_m mrks1 hszmrk1 mrk2]
  have hst02 := decompHeaderStable_trans hp0 hp1 hst01 hst12
  have htr2 : NibBibTrack ctx h0 h2 st.nib st.bib ndS elS :=
    nibBibTrack_err_same (nibBibTrack_err_same htrS he1) rfl
  have hbdEx : ∀ errs, C.Space.get h2 ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 1 < 2 ^ 63 :=
    nibBibTrack_bd hp0 hp2 htr2 hndS (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
  have hstep2 : ∃ h3,
      C.run (if dcs1[0]!.unreadMarker == M_APP0 then
        examine_app0 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr dataLength remLength
      else if dcs1[0]!.unreadMarker == M_APP14 then
        examine_app14 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr dataLength remLength
      else
        tracems2 dcs1[0]!.err 1 JTRC_MISC_MARKER dcs1[0]!.unreadMarker
          (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt))) h2 = .ok ((), h3) ∧
      ParserEnv ctx h3 ∧ DecompHeaderStable ctx h0 h3 ∧
      h3.srcs = h2.srcs ∧ h3.consts = h2.consts ∧ h3.bytes = h2.bytes ∧
      (∀ errs2 errs3, C.Space.get h2 ctx.rerr = some errs2 → 0 < errs2.size →
        C.Space.get h3 ctx.rerr = some errs3 → 0 < errs3.size ∧
        errs3[0]!.numWarnings.toInt ≤ errs2[0]!.numWarnings.toInt + 1) := by
    by_cases hm0 : (dcs1[0]!.unreadMarker == M_APP0) = true
    · obtain ⟨h3, hex, hp3, hst23, hsr3, hco3, hby3, hnw3⟩ :=
        examine_app0_parser hp2 dataArr dataLength remLength hbdEx
      refine ⟨h3, ?_, hp3, decompHeaderStable_trans hp0 hp2 hst02 hst23, hsr3, hco3, hby3, hnw3⟩
      simp only [hm0, ↓reduceIte]; exact hex
    · have hm0F : (dcs1[0]!.unreadMarker == M_APP0) = false := by
        cases hc : (dcs1[0]!.unreadMarker == M_APP0) <;> simp_all
      by_cases hm14 : (dcs1[0]!.unreadMarker == M_APP14) = true
      · obtain ⟨h3, hex, hp3, hst23, hsr3, hco3, hby3, hnw3⟩ :=
          examine_app14_parser hp2 dataArr dataLength remLength
        refine ⟨h3, ?_, hp3, decompHeaderStable_trans hp0 hp2 hst02 hst23, hsr3, hco3, hby3, fun e2 e3 hg2 hsz2 hg3 => ?_⟩
        · simp only [hm0F, hm14, Bool.false_eq_true, ↓reduceIte]; exact hex
        · obtain ⟨hsz3, heq3⟩ := hnw3 e2 e3 hg2 hsz2 hg3
          have heq3' : e3[0]!.numWarnings.toInt = e2[0]!.numWarnings.toInt := congrArg Int64.toInt heq3
          exact ⟨hsz3, by omega⟩
      · have hm14F : (dcs1[0]!.unreadMarker == M_APP14) = false := by
          cases hc : (dcs1[0]!.unreadMarker == M_APP14) <;> simp_all
        obtain ⟨h3, htr3, hp3, hd3, hmr3, hsr3, _, hcp3, _, _, _, hby3, _, hco3, hnw3⟩ :=
          tracems2_nonneg_parser hp2 1 JTRC_MISC_MARKER dcs1[0]!.unreadMarker
            (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt)) (by decide)
        refine ⟨h3, ?_, hp3, decompHeaderStable_trans hp0 hp2 hst02 (decompHeaderStable_of_same hd3 hmr3 hcp3),
          hsr3, hco3, hby3, fun e2 e3 hg2 hsz2 hg3 => ?_⟩
        · simp only [hm0F, hm14F, Bool.false_eq_true, ↓reduceIte]; rw [kerr1]; exact htr3
        · obtain ⟨hsz3, heq3⟩ := hnw3 e2 e3 hg2 hsz2 hg3
          have heq3' : e3[0]!.numWarnings.toInt = e2[0]!.numWarnings.toInt := congrArg Int64.toInt heq3
          exact ⟨hsz3, by omega⟩
  rcases hstep2 with ⟨h3, hex3, hp3, hst03, hsr3, hco3, hby3, hnw3⟩
  have hcur3 : CurValid h3 st.nib st.bib :=
    curValid_bytes_irrel (hby3.trans (by exact hby1)) (hco3.trans (by exact hco1)) hcurS
  obtain ⟨h4, hsync4, hp4, hd4, hmr4, he4, _, hcp4, _, _, _, _, _, _, hsrc4⟩ :=
    inputSync_parser hp3 st.nib st.bib hcur3
  have hst04 := decompHeaderStable_trans hp0 hp3 hst03 (decompHeaderStable_of_same hd4 hmr4 hcp4)
  have htr3 : NibBibTrack ctx h0 h3 st.nib st.bib (ndS + 1) (elS + 1) :=
    nibBibTrack_err_warn1 hp2 htr2 hnw3
  have htr4 : NibBibTrack ctx h0 h4 st.nib st.bib (ndS + 1) (elS + 1) :=
    nibBibTrack_err_same htr3 he4
  have hrunPre4 : C.run (do
      let mut remLength : Int64 := 0
      let mut dataArr : Array UInt8 := #[]
      if curMarker != .null then
        let sm ← Ptr.load curMarker
        let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
        let mst ← Ptr.load dcCur.master
        if dcCur.markerList == .null || mst.markerListEnd == .null then
          Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcCur with markerList := curMarker }
          Ptr.store dcCur.master { mst with markerListEnd := curMarker }
        else
          let tail ← Ptr.load mst.markerListEnd
          Ptr.store mst.markerListEnd { tail with next := curMarker }
          Ptr.store dcCur.master { mst with markerListEnd := curMarker }
        remLength := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat dataLength.toNat)
        for k in List.range dataLength.toNat do
          let bp ← Ptr.add sm.data (Int.ofNat k)
          let v ← Ptr.load bp
          dataArr := dataArr.push v
      let dcA ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
      let mrkA ← Ptr.load dcA.marker
      Ptr.store dcA.marker { mrkA with curMarker := .null }
      if dcA.unreadMarker == M_APP0 then
        examine_app0 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr dataLength remLength
      else if dcA.unreadMarker == M_APP14 then
        examine_app14 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr dataLength remLength
      else
        tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
          (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt))
      inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib
      if remLength > 0 then
        skipInputDataDispatch (.ref (C.DecompRef.decomp ctx.bdc) 0) remLength
      return (JpegRes.ok true)) hS =
      C.run (do
        if remLength > 0 then
          skipInputDataDispatch (.ref (C.DecompRef.decomp ctx.bdc) 0) remLength
        return (JpegRes.ok true)) h4 := by
    rw [hrun1 (fun remLength dataArr => do
      let dcA ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
      let mrkA ← Ptr.load dcA.marker
      Ptr.store dcA.marker { mrkA with curMarker := .null }
      if dcA.unreadMarker == M_APP0 then
        examine_app0 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr dataLength remLength
      else if dcA.unreadMarker == M_APP14 then
        examine_app14 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr dataLength remLength
      else
        tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
          (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt))
      inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib
      if remLength > 0 then
        skipInputDataDispatch (.ref (C.DecompRef.decomp ctx.bdc) 0) remLength
      return (JpegRes.ok true))]
    dsimp only
    rw [C.run_bind, hldc1]; dsimp only
    rw [C.run_bind, hlmrk1']; dsimp only
    rw [C.run_bind, hstMrk1']; dsimp only
    by_cases hm0 : (dcs1[0]!.unreadMarker == M_APP0) = true
    · simp only [hm0, ↓reduceIte] at hex3 ⊢
      rw [C.run_bind, hex3]; dsimp only
      rw [C.run_bind, hsync4]
    · have hm0F : (dcs1[0]!.unreadMarker == M_APP0) = false := by
        cases hc : (dcs1[0]!.unreadMarker == M_APP0)
        · rfl
        · exact False.elim (hm0 hc)
      simp only [hm0F, Bool.false_eq_true, ↓reduceIte] at hex3 ⊢
      by_cases hm14 : (dcs1[0]!.unreadMarker == M_APP14) = true
      · simp only [hm14, ↓reduceIte] at hex3 ⊢
        rw [C.run_bind, hex3]; dsimp only
        rw [C.run_bind, hsync4]
      · have hm14F : (dcs1[0]!.unreadMarker == M_APP14) = false := by
          cases hc : (dcs1[0]!.unreadMarker == M_APP14)
          · rfl
          · exact False.elim (hm14 hc)
        simp only [hm14F, Bool.false_eq_true, ↓reduceIte] at hex3 ⊢
        rw [C.run_bind, hex3]; dsimp only
        rw [C.run_bind, hsync4]
  have hm04 : ∀ s0 s4, C.Space.get h0 ctx.rs = some s0 → 0 < s0.size →
      C.Space.get h4 ctx.rs = some s4 → 0 < s4.size → SrcMono s0[0]! s4[0]! := by
    intro s0 s4 hs0 hss0 hs4 hss4
    obtain ⟨e0, he0, hse0, _⟩ := parserEnv_get_err hp0
    obtain ⟨e4, he4', hse4, _⟩ := parserEnv_get_err hp4
    obtain ⟨ta, tb, _⟩ := htr4 e0 e4 s0 he0 hse0 he4' hse4 hs0 hss0
    obtain ⟨_, hn4, hb4⟩ := hsrc4 s4 hs4
    refine ⟨fun ht0 => by rw [hn4]; exact ta ht0, fun _ => ?_⟩
    by_cases hnf : isConstEofPtr s4[0]!.nextInputByte = false
    · right; rw [hn4] at hnf; rw [hb4]; exact (tb hnf).2.1
    · left; cases hc : isConstEofPtr s4[0]!.nextInputByte; exact False.elim (hnf hc); rfl
  have hw04 : ∀ errs0 errs4 srcs0 srcs4,
      C.Space.get h0 ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h4 ctx.rerr = some errs4 → 0 < errs4.size →
      C.Space.get h0 ctx.rs = some srcs0 → 0 < srcs0.size →
      C.Space.get h4 ctx.rs = some srcs4 → 0 < srcs4.size →
      (isConstEofPtr srcs4[0]!.nextInputByte = false →
        warnPotVal errs4 srcs4 ≤ warnPotVal errs0 srcs0 + (if ndS ≤ -1 then 0 else 1)) ∧
      (isConstEofPtr srcs4[0]!.nextInputByte = true →
        errs4[0]!.numWarnings.toInt ≤
          (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
           else warnPotVal errs0 srcs0) + elS + 1) := by
    intro e0 e4 s0 s4 he0 hse0 he4' hse4 hs0 hss0 hs4 hss4
    obtain ⟨_, tb, tc⟩ := htr4 e0 e4 s0 he0 hse0 he4' hse4 hs0 hss0
    obtain ⟨_, hn4, hb4⟩ := hsrc4 s4 hs4
    refine ⟨fun hf4 => ?_, fun ht4 => ?_⟩
    · rw [hn4] at hf4
      obtain ⟨hs0f, _, hbw⟩ := tb hf4
      simp only [warnPotVal, hs0f, hf4, hn4, hb4, Bool.false_eq_true, ↓reduceIte] at hbw ⊢
      by_cases hneg : ndS ≤ -1
      · simp only [hneg, ↓reduceIte]; omega
      · simp only [hneg, ↓reduceIte]; omega
    · rw [hn4] at ht4
      have := tc ht4
      omega
  by_cases hremPos : remLength > 0
  · have hbd4 : ∀ errs, C.Space.get h4 ctx.rerr = some errs → 0 < errs.size →
        errs[0]!.numWarnings.toInt + 2 ^ 16 < 2 ^ 63 := by
      intro errs4 hg4 hsz4
      obtain ⟨e0, he0, hse0, _⟩ := parserEnv_get_err hp0
      obtain ⟨s0, hs0, hss0, _⟩ := parserEnv_get_src hp0
      obtain ⟨s4, hs4, hss4, _⟩ := parserEnv_get_src hp4
      obtain ⟨w4f, w4t⟩ := hw04 e0 errs4 s0 s4 he0 hse0 hg4 hsz4 hs0 hss0 hs4 hss4
      have hhd := hhead e0 s0 he0 hse0 hs0 hss0
      by_cases hnf4 : isConstEofPtr s4[0]!.nextInputByte = false
      · have hw4 := w4f hnf4
        have hnf0 : isConstEofPtr s0[0]!.nextInputByte = false := by
          cases hc : isConstEofPtr s0[0]!.nextInputByte
          · rfl
          · rw [(hm04 s0 s4 hs0 hss0 hs4 hss4).1 hc] at hnf4; cases hnf4
        simp only [warnPotVal, hnf0, hnf4, Bool.false_eq_true, ↓reduceIte] at hw4 hhd
        omega
      · have htr4' : isConstEofPtr s4[0]!.nextInputByte = true := by
          cases hc : isConstEofPtr s4[0]!.nextInputByte
          · exact False.elim (hnf4 hc)
          · rfl
        have hw4 := w4t htr4'
        by_cases hnf0 : isConstEofPtr s0[0]!.nextInputByte = true
        · simp only [warnPotVal, hnf0, ↓reduceIte] at hw4 hhd; omega
        · simp only [warnPotVal, hnf0, Bool.false_eq_true, ↓reduceIte] at hw4 hhd; omega
    obtain ⟨h5, hsk5, hp5, hd5, hmr5, _, hcp5, _, _, _, _, _, _, hnw5, hsm5⟩ :=
      skipInputDataDispatch_parser hp4 remLength hremLe hbd4
    have hst05 := decompHeaderStable_trans hp0 hp4 hst04 (decompHeaderStable_of_same hd5 hmr5 hcp5)
    refine ⟨h5, ?_, hp5, hst05, fun s0 s5 hs0 hss0 hs5 hss5 => ?_, fun e0 e5 s0 s5 he0 hse0 he5 hse5 hs0 hss0 hs5 hss5 => ?_⟩
    · rw [hrunPre4]; simp only [hremPos, ↓reduceIte, C.run_bind, hsk5]; rfl
    · obtain ⟨s4, hs4, hss4, _⟩ := parserEnv_get_src hp4
      obtain ⟨ht, hf⟩ := hsm5 s4 s5 hs4 hss4 hs5 hss5
      exact srcMono_trans (hm04 s0 s4 hs0 hss0 hs4 hss4)
        ⟨ht, fun hf4 => by
          by_cases hc5 : isConstEofPtr s5[0]!.nextInputByte = false
          · exact Or.inr (hf hc5).2.1
          · exact Or.inl (by cases hc : isConstEofPtr s5[0]!.nextInputByte; exact False.elim (hc5 hc); rfl)⟩
    · obtain ⟨e4, he4', hse4, _⟩ := parserEnv_get_err hp4
      obtain ⟨s4, hs4, hss4, _⟩ := parserEnv_get_src hp4
      obtain ⟨w4f, w4t⟩ := hw04 e0 e4 s0 s4 he0 hse0 he4' hse4 hs0 hss0 hs4 hss4
      obtain ⟨_, hf5⟩ := hsm5 s4 s5 hs4 hss4 hs5 hss5
      have hnw5' := (hnw5 e4 e5 he4' hse4 he5).2
      refine ⟨fun hnf5 => ?_, fun ht5 => ?_⟩
      · obtain ⟨hnf4, hble, heeq⟩ := hf5 hnf5
        have hee := heeq e4 e5 he4' hse4 he5
        have := w4f hnf4
        simp only [warnPotVal, hnf4, hnf5, Bool.false_eq_true, ↓reduceIte] at this ⊢
        omega
      · by_cases hc4 : isConstEofPtr s4[0]!.nextInputByte = true
        · have := w4t hc4; omega
        · have hnf4 : isConstEofPtr s4[0]!.nextInputByte = false := by
            cases hc : isConstEofPtr s4[0]!.nextInputByte; rfl; exact False.elim (hc4 hc)
          have h4f := w4f hnf4
          have hf0 : isConstEofPtr s0[0]!.nextInputByte = false := by
            cases hc : isConstEofPtr s0[0]!.nextInputByte
            · rfl
            · rw [(hm04 s0 s4 hs0 hss0 hs4 hss4).1 hc] at hnf4; cases hnf4
          simp only [warnPotVal, hf0, hnf4, Bool.false_eq_true, ↓reduceIte] at h4f ⊢
          omega
  · refine ⟨h4, ?_, hp4, hst04, hm04, fun e0 e4 s0 s4 he0 hse0 he4' hse4 hs0 hss0 hs4 hss4 => ?_⟩
    · rw [hrunPre4]; simp only [eq_false hremPos, ↓reduceIte]; rfl
    · obtain ⟨w4f, w4t⟩ := hw04 e0 e4 s0 s4 he0 hse0 he4' hse4 hs0 hss0 hs4 hss4
      exact ⟨w4f, fun ht4 => by have := w4t ht4; omega⟩

private theorem alloc_large_saved_marker_curValid {ctx : IoCtx} {h1 h2 : C.Heap}
    {limit : Nat} {smP : C.SavedMarkerPtr} {dP : C.BPtr}
    (hp1 : ParserEnv ctx h1)
    (hal : C.run (alloc_large_saved_marker (.ref (C.DecompRef.decomp ctx.bdc) 0) JPOOL_IMAGE limit) h1 =
      .ok (.ok (smP, dP), h2))
    {nib : C.BPtr} {bib : UInt64} (hcv : CurValid h1 nib bib) :
    CurValid h2 nib bib := by
  have hfr1 := hp1.2.1
  obtain ⟨dcs1, hgdc1, hszdc1, kerr1, kmem1, _⟩ := parserEnv_get_dc hp1
  obtain ⟨mems1, hgmem1, hszmem1, _⟩ := parserEnv_get_mem hp1
  have hl0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc1
  unfold alloc_large_saved_marker at hal
  rw [C.run_bind, hl0] at hal; dsimp only at hal
  split at hal
  · cases hoom : C.run (out_of_memory (.ref (C.DecompRef.decomp ctx.bdc) 0) 8) h1 <;>
      rw [C.run_bind, hoom] at hal <;> cases hal
  · split at hal
    · cases hoom : C.run (out_of_memory (.ref (C.DecompRef.decomp ctx.bdc) 0) 3) h1 <;>
        rw [C.run_bind, hoom] at hal <;> cases hal
    · split at hal
      · cases herr : C.run (errexit1 dcs1[0]!.err JERR_BAD_POOL_ID JPOOL_IMAGE) h1 <;>
          rw [C.run_bind, herr] at hal <;> cases hal
      · unfold Mozjpeg.Jmemnobs.jpeg_get_large_saved_marker at hal
        rw [C.run_bind] at hal
        by_cases ha : h1.allocOk h1.nalloc = true
        · simp only [C.run, allocSavedMarkerData, ha, ↓reduceIte] at hal
          have hneNull : ((.ref (.savedMarker h1.nextBlk) 0 : C.SavedMarkerPtr) == .null) = false := rfl
          simp only [hneNull, Bool.false_eq_true, ↓reduceIte] at hal
          let hA : C.Heap := {
            h1 with
            savedMarkers := C.upd h1.savedMarkers h1.nextBlk (some #[default])
            bytes := C.upd h1.bytes (h1.nextBlk + 1) (some (Array.replicate limit 0))
            nextBlk := h1.nextBlk + 2
            nalloc := h1.nalloc + 1
          }
          change C.run (do
            let dc2 ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            let mem2 ← Ptr.load dc2.mem
            let pa := mem2.poolAllocs[JPOOL_IMAGE.toInt.toNat]!
            let pa' := {
              pa with
              savedMarkers := pa.savedMarkers.push h1.nextBlk
              bytes := pa.bytes.push (h1.nextBlk + 1)
            }
            Ptr.store dc2.mem {
              mem2 with
              poolAllocs := mem2.poolAllocs.set! JPOOL_IMAGE.toInt.toNat pa'
              totalSpaceAllocated := mem2.totalSpaceAllocated +
                (round_up_pow2 (sizeof_jpeg_marker_struct.toInt.toNat.toUInt64 + UInt64.ofNat limit) ALIGN_SIZE) +
                sizeof_small_pool_hdr + ALIGN_SIZE - 1
            }
            return C.JpegRes.ok (C.Ptr.ref (C.SavedMarkerRef.savedMarker h1.nextBlk) 0,
              C.Ptr.ref (C.BRef.heap (h1.nextBlk + 1)) 0)) hA = .ok (.ok (smP, dP), h2) at hal
          have hcvA : CurValid hA nib bib :=
            curValid_bytes_irrel rfl rfl (curValid_alloc_byte (hfr1 (h1.nextBlk + 1) (by omega)).1 hcv)
          have hgdcA : C.Space.get hA (C.DecompRef.decomp ctx.bdc) = some dcs1 := hgdc1
          have hlA := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcA hszdc1
          have hgmemA : C.Space.get hA ctx.rmem = some mems1 := by
            cases hr : ctx.rmem; simp only [C.Space.get, hr] at hgmem1 ⊢; exact hgmem1
          have hlM := ptr_load_ok (r := ctx.rmem) (off := 0) hgmemA hszmem1
          have hlM' : C.run (Ptr.load dcs1[0]!.mem) hA = .ok (mems1[0]!, hA) := by rw [kmem1]; exact hlM
          rw [C.run_bind, hlA] at hal; dsimp only at hal
          rw [C.run_bind, hlM'] at hal; dsimp only at hal
          rw [C.run_bind] at hal
          have hroM : C.Space.ro hA ctx.rmem = false := by cases ctx.rmem; rfl
          have hstM := ptr_store_ok (r := ctx.rmem) (off := 0)
            (v := { mems1[0]! with
              poolAllocs := mems1[0]!.poolAllocs.set! JPOOL_IMAGE.toInt.toNat
                { mems1[0]!.poolAllocs[JPOOL_IMAGE.toInt.toNat]! with
                  savedMarkers := mems1[0]!.poolAllocs[JPOOL_IMAGE.toInt.toNat]!.savedMarkers.push h1.nextBlk
                  bytes := mems1[0]!.poolAllocs[JPOOL_IMAGE.toInt.toNat]!.bytes.push (h1.nextBlk + 1) }
              totalSpaceAllocated := mems1[0]!.totalSpaceAllocated +
                (round_up_pow2 (sizeof_jpeg_marker_struct.toInt.toNat.toUInt64 + UInt64.ofNat limit) ALIGN_SIZE) +
                sizeof_small_pool_hdr + ALIGN_SIZE - 1 })
            hgmemA hroM hszmem1
          rw [kmem1] at hal
          rw [hstM] at hal
          cases hal
          refine curValid_bytes_irrel ?_ ?_ hcvA <;> (cases ctx.rmem; rfl)
        · simp only [C.run, allocSavedMarkerData, ha, Bool.false_eq_true, ↓reduceIte] at hal
          have heqNull : ((C.Ptr.null : C.SavedMarkerPtr) == .null) = true := rfl
          simp only [heqNull, ↓reduceIte] at hal
          change C.run (do
            let _ ← out_of_memory (.ref (C.DecompRef.decomp ctx.bdc) 0) 4
            pure (C.JpegRes.errExit JERR_OUT_OF_MEMORY)) { h1 with nalloc := h1.nalloc + 1 } =
              .ok (.ok (smP, dP), h2) at hal
          cases hoom : C.run (out_of_memory (.ref (C.DecompRef.decomp ctx.bdc) 0) 4) { h1 with nalloc := h1.nalloc + 1 } <;>
            rw [C.run_bind, hoom] at hal <;> cases hal

private theorem save_marker_new_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 18 < 2 ^ 63)
    {mrks0 : Array C.JpegMarkerReader}
    (hgmrk0 : C.Space.get h ctx.rmrk = some mrks0) (hszmrk0 : 0 < mrks0.size)
    (hcmN : mrks0[0]!.curMarker = .null) :
    ∃ res h',
      C.run (save_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcMono srcs0[0]! srcs'[0]!) ∧
        (∀ errs0 errs' srcs0 srcs',
          C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
          C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
          C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          (isConstEofPtr srcs'[0]!.nextInputByte = false →
            warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
          (isConstEofPtr srcs'[0]!.nextInputByte = true →
            errs'[0]!.numWarnings.toInt ≤
              (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
               else warnPotVal errs0 srcs0) + 2 ^ 17))
      | _ => True := by
  obtain ⟨dcs0, hgdc0, hszdc0, _, _, _, _, kmrk0, ksrc0⟩ := parserEnv_get_dc hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _, _, _, _, _, hcur0⟩ := parserEnv_get_src hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlmrk0 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk0 hszmrk0
  have hlmrk0' : C.run (Ptr.load dcs0[0]!.marker) h = .ok (mrks0[0]!, h) := by rw [kmrk0]; exact hlmrk0
  have hlsrc0 := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc0 hszsrc0
  have hlsrc0' : C.run (Ptr.load dcs0[0]!.src) h = .ok (srcs0[0]!, h) := by rw [ksrc0]; exact hlsrc0
  have htr0 := nibBibTrack_init ctx h srcs0 hgsrc0
  have hcmT : (mrks0[0]!.curMarker == .null) = true := by simp [hcmN]
  have hbd0 : ∀ errs, C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      errs[0]!.numWarnings.toInt + 2 < 2 ^ 63 :=
    nibBibTrack_bd hp hp htr0 (by omega) (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
  obtain ⟨res1, h1, hrun1, hp1, hd1, hmr1, _, hcp1, _, _, _, _, _, _, hpost1⟩ :=
    input2Bytes_parser hp srcs0[0]!.nextInputByte srcs0[0]!.bytesInBuffer hcur0 hbd0
  have hst01 : DecompHeaderStable ctx h h1 := decompHeaderStable_of_same hd1 hmr1 hcp1
  cases res1 with
  | none =>
    refine ⟨.ok false, h1, ?_, hp1, hst01, trivial⟩
    unfold save_marker
    rw [C.run_bind, hldc0]; dsimp only
    rw [C.run_bind, hlmrk0']; dsimp only
    rw [C.run_bind, hlsrc0']; dsimp only
    simp only [hcmT, ↓reduceIte, C.run_bind, hrun1]; rfl
  | some p1 =>
    rcases p1 with ⟨lenRaw, nib1, bib1⟩
    rcases hpost1 with ⟨hlen0, hlenHi, hcur1, hce1⟩
    obtain ⟨htr1, _⟩ := nibBibTrack_input2Bytes_step hp hp htr0 (by omega) (by omega) hce1
    let length : Int64 := Int64.ofInt (lenRaw.toInt - 2)
    have hlenTo : length.toInt = lenRaw.toInt - 2 := by
      dsimp only [length]; rw [Int64.toInt_ofInt, show Int64.size = 2 ^ 64 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    by_cases hlenGe : length ≥ 0
    · let limit0 : UInt32 :=
        if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
        else
          let idx := (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat
          if idx < 16 then mrks0[0]!.lengthLimitAPPn[idx]! else 0
      let lenU : UInt32 := UInt32.ofNat length.toInt.toNat
      let limit : UInt32 := if lenU < limit0 then lenU else limit0
      have hlenUTo : lenU.toNat = length.toInt.toNat := by
        dsimp only [lenU]; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      have hlimLeU : limit.toNat ≤ lenU.toNat := by
        dsimp only [limit]
        by_cases hlt : lenU < limit0
        · simp [hlt]
        · simp only [hlt, ↓reduceIte]
          exact Nat.not_lt.mp (fun hltN => hlt (UInt32.lt_iff_toNat_lt.mpr hltN))
      have hlimLe : limit.toNat ≤ 65535 := by omega
      obtain ⟨resAl, h2, hal2, hp2, hpostAl⟩ := alloc_large_saved_marker_parser hp1 limit.toNat hlimLe
      cases resAl with
      | errExit code =>
        rcases hpostAl with ⟨hd2, hmr2, hcp2⟩
        have hst02 := decompHeaderStable_trans hp hp1 hst01 (decompHeaderStable_of_same hd2 hmr2 hcp2)
        refine ⟨.errExit code, h2, ?_, hp2, hst02, trivial⟩
        unfold save_marker
        rw [C.run_bind, hldc0]; dsimp only
        rw [C.run_bind, hlmrk0']; dsimp only
        rw [C.run_bind, hlsrc0']; dsimp only
        simp only [hcmT, ↓reduceIte]
        rw [C.run_bind, hrun1]; dsimp only
        have hlenGe' : Int64.ofInt (lenRaw.toInt - 2) ≥ 0 := hlenGe
        simp only [hlenGe', ↓reduceIte]
        by_cases hlt : lenU < limit0
        · have hlt' : UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat <
              (if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
               else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                 mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0) := hlt
          simp only [hlt', ↓reduceIte]
          have hlim : limit = UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat := by
            dsimp only [limit]; simp only [hlt, ↓reduceIte]; rfl
          have hal2' : C.run (alloc_large_saved_marker (.ref (C.DecompRef.decomp ctx.bdc) 0) JPOOL_IMAGE
              (UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat).toNat) h1 = .ok (.errExit code, h2) := by
            rw [← hlim]; exact hal2
          rw [C.run_bind, hal2']; rfl
        · have hlt' : ¬ UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat <
              (if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
               else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                 mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0) := hlt
          simp only [hlt', ↓reduceIte]
          have hlim : limit = if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
              else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0 := by
            dsimp only [limit]; simp only [hlt, ↓reduceIte]; rfl
          have hal2' : C.run (alloc_large_saved_marker (.ref (C.DecompRef.decomp ctx.bdc) 0) JPOOL_IMAGE
              (if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
               else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                 mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0).toNat) h1 =
              .ok (.errExit code, h2) := by
            rw [← hlim]; exact hal2
          rw [C.run_bind, hal2']; rfl
      | ok pAl =>
        rcases pAl with ⟨smP, dP⟩
        rcases hpostAl with ⟨hd2, hmr2, hsr2, he2, hma2, hcp2, hq2, hhu2, hco2,
          rsm, sms2, hsmPEq, hgsm2, hszsm2, hwb2⟩
        have hst02 := decompHeaderStable_trans hp hp1 hst01 (decompHeaderStable_of_same hd2 hmr2 hcp2)
        have hroSm2 : C.Space.ro h2 rsm = false := by cases rsm; rfl
        let smNew : C.JpegSavedMarker := {
          next := .null
          marker := UInt8.ofNat dcs0[0]!.unreadMarker.toInt.toNat
          originalLength := lenU
          dataLength := limit
          data := dP
        }
        have hstSm2 := ptr_store_ok (r := rsm) (off := 0) (v := smNew) hgsm2 hroSm2 hszsm2
        have hstSm2' : C.run (Ptr.store smP smNew) h2 = .ok ((), C.Space.put h2 rsm (sms2.set! 0 smNew)) := by
          rw [hsmPEq]; exact hstSm2
        let h3 := C.Space.put h2 rsm (sms2.set! 0 smNew)
        have hp3 : ParserEnv ctx h3 := by
          refine parserEnv_put_sm hp2 hgsm2 hszsm2 (fun mrks hgmrk _ hcur => ?_)
          have hmr0_3 : C.Space.get h2 ctx.rmrk = some mrks0 := by
            rcases hrM : ctx.rmrk with ⟨bm⟩
            simp only [C.Space.get, hrM, hmr2, hmr1] at hgmrk0 ⊢; exact hgmrk0
          have hmEq := Option.some.inj (hgmrk.symm.trans hmr0_3)
          rw [hmEq, hcmN] at hcur; cases hcur
        obtain ⟨dcs3, hgdc3, hszdc3, _, _, _, _, kmrk3, _⟩ := parserEnv_get_dc hp3
        obtain ⟨mrks3, hgmrk3, hszmrk3, _, _, _, _, _, hllSz3⟩ := parserEnv_get_mrk hp3
        have hldc3 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc3 hszdc3
        have hlmrk3 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk3 hszmrk3
        have hlmrk3' : C.run (Ptr.load dcs3[0]!.marker) h3 = .ok (mrks3[0]!, h3) := by
          rw [kmrk3]; exact hlmrk3
        have hroM3 : C.Space.ro h3 ctx.rmrk = false := rfl
        let mrk4 := { mrks3[0]! with curMarker := smP, bytesRead := 0 }
        have hstM3 := ptr_store_ok (r := ctx.rmrk) (off := 0) (v := mrk4) hgmrk3 hroM3 hszmrk3
        have hstM3' : C.run (Ptr.store dcs3[0]!.marker mrk4) h3 =
            .ok ((), C.Space.put h3 ctx.rmrk (mrks3.set! 0 mrk4)) := by
          rw [kmrk3]; exact hstM3
        let h4 := C.Space.put h3 ctx.rmrk (mrks3.set! 0 mrk4)
        have hgsm3 : C.Space.get h3 rsm = some (sms2.set! 0 smNew) := by
          rcases hrS : rsm with ⟨bs⟩; simp [h3, C.Space.get, C.Space.put, hrS, C.upd_same]
        have hszsm3 : 0 < (sms2.set! 0 smNew).size := by simpa using hszsm2
        rcases hwb2 with ⟨bd, offD, arrD, hdPEq, hbd2, hwbLe2⟩
        have hbd3 : h3.bytes bd = some arrD := hbd2
        have hp4 : ParserEnv ctx h4 := by
          refine parserEnv_put_mrk hp3 hgmrk3 hszmrk3 rfl rfl rfl rfl hllSz3 ?_
            (fun dcs hg hsz hne => parserEnv_compInfo_of_sawSOF hp3 hg hgmrk3 hne)
          right
          refine ⟨rsm, 0, sms2.set! 0 smNew, smNew, hsmPEq, hgsm3, hszsm3,
            (set0_bang_m sms2 hszsm2 smNew).symm, hlimLe, by dsimp only [smNew]; omega,
            ⟨bd, offD, arrD, hdPEq, hbd3, hwbLe2⟩, by change 0 ≤ limit.toNat; omega⟩
        have hst24 : DecompHeaderStable ctx h2 h4 := by
          refine ⟨(fun da db ha _ hb _ => by
            have hd4 : h4.decomps = h2.decomps := rfl
            dsimp only [C.Space.get] at ha hb; rw [hd4] at hb; rw [Option.some.inj (hb.symm.trans ha)]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩), ?_, (fun _ _ _ hg hi => ⟨_, hg, hi, rfl, rfl, rfl⟩)⟩
          intro ma mb ha _ hb _
          have hmr23 : h3.markers = h2.markers := rfl
          have hg2m : C.Space.get h3 ctx.rmrk = some mrks3 := hgmrk3
          have hg4m : C.Space.get h4 ctx.rmrk = some (mrks3.set! 0 mrk4) := by
            simp [h4, C.Space.get, C.Space.put]
          have ha3 : C.Space.get h3 ctx.rmrk = some ma := by
            rcases hrM : ctx.rmrk with ⟨bm⟩; simp only [C.Space.get, hrM, hmr23] at ha ⊢; exact ha
          rw [Option.some.inj (ha3.symm.trans hg2m), Option.some.inj (hb.symm.trans hg4m),
            set0_bang_m mrks3 hszmrk3 mrk4]
        have hst04 := decompHeaderStable_trans hp hp2 hst02 hst24
        have hcur2 : CurValid h2 nib1 bib1 := alloc_large_saved_marker_curValid hp1 hal2 hcur1
        have hcur4 : CurValid h4 nib1 bib1 := curValid_bytes_irrel rfl rfl (curValid_bytes_irrel rfl rfl hcur2)
        have htr4 : NibBibTrack ctx h h4 nib1 bib1 (-8) 2 :=
          nibBibTrack_err_same (nibBibTrack_err_same (nibBibTrack_err_same htr1 he2) rfl) rfl
        have hgsm4 : C.Space.get h4 rsm = some (sms2.set! 0 smNew) := hgsm3
        have hsm4_0 : (sms2.set! 0 smNew)[0]! = smNew := set0_bang_m sms2 hszsm2 smNew
        have hpreLoopEq : C.run (save_marker (.ref (C.DecompRef.decomp ctx.bdc) 0)) h =
            C.run (do
              let st ← cwhile
                (fun (s : SaveMarkerState) => pure (!s.done && s.bytesRead < limit, s))
                (fun (s : SaveMarkerState) => do
                  inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib
                  let dcS ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                  let mrkS ← Ptr.load dcS.marker
                  Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
                  match (← makeByteAvail (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
                  | none => return { s with done := true, susp := true }
                  | some (n1, bi1) =>
                    let cs ← cwhile
                      (fun (c : SaveMarkerCopyState) => pure (c.br < limit && c.bb > 0, c))
                      (fun (c : SaveMarkerCopyState) => do
                        let b ← Ptr.load c.nb
                        Ptr.store c.dp b
                        let dp' ← Ptr.add c.dp 1
                        let nb' ← Ptr.add c.nb 1
                        return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
                      { br := s.bytesRead, nb := n1, bb := bi1, dp := s.dp }
                    return { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp })
                { done := false, susp := false, bytesRead := 0, nib := nib1, bib := bib1, dp := dP }
              if st.susp then return .ok false
              let mut remLength : Int64 := 0
              let mut dataArr : Array UInt8 := #[]
              if smP != .null then
                let sm ← Ptr.load smP
                let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                let mst ← Ptr.load dcCur.master
                if dcCur.markerList == .null || mst.markerListEnd == .null then
                  Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcCur with markerList := smP }
                  Ptr.store dcCur.master { mst with markerListEnd := smP }
                else
                  let tail ← Ptr.load mst.markerListEnd
                  Ptr.store mst.markerListEnd { tail with next := smP }
                  Ptr.store dcCur.master { mst with markerListEnd := smP }
                remLength := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat limit.toNat)
                for k in List.range limit.toNat do
                  let bp ← Ptr.add sm.data (Int.ofNat k)
                  let v ← Ptr.load bp
                  dataArr := dataArr.push v
              let dcA ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
              let mrkA ← Ptr.load dcA.marker
              Ptr.store dcA.marker { mrkA with curMarker := .null }
              if dcA.unreadMarker == M_APP0 then
                examine_app0 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr limit remLength
              else if dcA.unreadMarker == M_APP14 then
                examine_app14 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr limit remLength
              else
                tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
                  (Int32.ofInt (Int.ofNat limit.toNat + remLength.toInt))
              inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib
              if remLength > 0 then
                skipInputDataDispatch (.ref (C.DecompRef.decomp ctx.bdc) 0) remLength
              return .ok true) h4 := by
          unfold save_marker
          rw [C.run_bind, hldc0]; dsimp only
          rw [C.run_bind, hlmrk0']; dsimp only
          rw [C.run_bind, hlsrc0']; dsimp only
          simp only [hcmT, ↓reduceIte]
          rw [C.run_bind, hrun1]; dsimp only
          have hlenGe' : Int64.ofInt (lenRaw.toInt - 2) ≥ 0 := hlenGe
          simp only [hlenGe', ↓reduceIte]
          by_cases hlt : lenU < limit0
          · have hlt' : UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat <
                (if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
                 else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                   mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0) := hlt
            simp only [hlt', ↓reduceIte]
            have hlim : limit = UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat := by
              dsimp only [limit]; simp only [hlt, ↓reduceIte]; rfl
            have hal2' : C.run (alloc_large_saved_marker (.ref (C.DecompRef.decomp ctx.bdc) 0) JPOOL_IMAGE
                (UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat).toNat) h1 =
                .ok (.ok (smP, dP), h2) := by rw [← hlim]; exact hal2
            have hstSm2'' : C.run (Ptr.store smP {
                next := .null
                marker := UInt8.ofNat dcs0[0]!.unreadMarker.toInt.toNat
                originalLength := UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat
                dataLength := UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat
                data := dP
              }) h2 = .ok ((), C.Space.put h2 rsm (sms2.set! 0 smNew)) := by
              have heq : ({
                  next := .null
                  marker := UInt8.ofNat dcs0[0]!.unreadMarker.toInt.toNat
                  originalLength := UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat
                  dataLength := UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat
                  data := dP
                } : C.JpegSavedMarker) = smNew := by
                dsimp only [smNew, lenU, length]; rw [hlim]
              rw [heq]; exact hstSm2'
            rw [C.run_bind, hal2']; dsimp only
            rw [C.run_bind, hstSm2'']; dsimp only
            rw [C.run_bind, hldc3]; dsimp only
            rw [C.run_bind, hlmrk3']; dsimp only
            rw [C.run_bind, hstM3']
            simp only [hlim]; rfl
          · have hlt' : ¬ UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat <
                (if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
                 else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                   mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0) := hlt
            simp only [hlt', ↓reduceIte]
            have hlim : limit = if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
                else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                  mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0 := by
              dsimp only [limit]; simp only [hlt, ↓reduceIte]; rfl
            have hal2' : C.run (alloc_large_saved_marker (.ref (C.DecompRef.decomp ctx.bdc) 0) JPOOL_IMAGE
                (if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
                 else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                   mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0).toNat) h1 =
                .ok (.ok (smP, dP), h2) := by rw [← hlim]; exact hal2
            have hstSm2'' : C.run (Ptr.store smP {
                next := .null
                marker := UInt8.ofNat dcs0[0]!.unreadMarker.toInt.toNat
                originalLength := UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat
                dataLength := if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
                  else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                    mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0
                data := dP
              }) h2 = .ok ((), C.Space.put h2 rsm (sms2.set! 0 smNew)) := by
              have heq : ({
                  next := .null
                  marker := UInt8.ofNat dcs0[0]!.unreadMarker.toInt.toNat
                  originalLength := UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat
                  dataLength := if dcs0[0]!.unreadMarker == M_COM then mrks0[0]!.lengthLimitCOM
                    else if (dcs0[0]!.unreadMarker - M_APP0).toInt.toNat < 16 then
                      mrks0[0]!.lengthLimitAPPn[(dcs0[0]!.unreadMarker - M_APP0).toInt.toNat]! else 0
                  data := dP
                } : C.JpegSavedMarker) = smNew := by
                dsimp only [smNew, limit0, lenU, length]; rw [hlim]
              rw [heq]; exact hstSm2'
            rw [C.run_bind, hal2']; dsimp only
            rw [C.run_bind, hstSm2'']; dsimp only
            rw [C.run_bind, hldc3]; dsimp only
            rw [C.run_bind, hlmrk3']; dsimp only
            rw [C.run_bind, hstM3']
            simp only [hlim]; rfl
        have hhead17 : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
            C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
            warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63 := fun e0 s0 he0 hse0 hs0 hss0 => by
          have := hhead e0 s0 he0 hse0 hs0 hss0; omega
        have hlimLe' : limit.toNat ≤ 65533 := by omega
        have hz0 : (0 : UInt32).toNat = 0 := rfl
        obtain ⟨st, hS, hloop, hpS, hst0S, _hdS, _hmaS, _hcpS, _hqS, _hhuS, hsmS, _hmeS, _hcoS, hbyS, hloopRes⟩ :=
          save_marker_loop_parser hp hp4 hhead17 hst04 (UInt32.le_iff_toNat_le.mpr (by rw [hz0]; omega))
            hlimLe hgsm4 hszsm3
            (fun mrks hg4' _ _ => by
              have hg4'' : C.Space.get h4 ctx.rmrk = some (mrks3.set! 0 mrk4) := by
                simp [h4, C.Space.get, C.Space.put]
              rw [Option.some.inj (hg4'.symm.trans hg4''), set0_bang_m mrks3 hszmrk3 mrk4, hsm4_0]
              exact ⟨hsmPEq, rfl, by dsimp only [smNew]; omega⟩)
            (bd := bd) (offD := offD) (arrD := arrD) (fun _ => ⟨by rw [hsm4_0]; exact hdPEq, hbd3, hwbLe2⟩)
            hcur4 (dataPtr := dP) (fun _ => by rw [hdPEq, hz0]; rfl) (by decide) (by decide) (by decide) htr4
        by_cases hsusp : st.susp = true
        · refine ⟨.ok false, hS, ?_, hpS, hst0S, trivial⟩
          rw [hpreLoopEq, C.run_bind]; erw [hloop]; dsimp only; simp only [hsusp, ↓reduceIte]; rfl
        · have hsuspF : st.susp = false := by cases hc : st.susp <;> simp_all
          obtain ⟨_, _, hcurS, htrS⟩ := hloopRes hsuspF
          have hgsmS : C.Space.get hS rsm = some (sms2.set! 0 smNew) := by
            rcases hrS : rsm with ⟨bs⟩; simp only [C.Space.get, hrS, hsmS] at hgsm4 ⊢; exact hgsm4
          obtain ⟨arrS, hbdS, hszArrS⟩ := hbyS arrD hbd3
          obtain ⟨hFin, hrunFin, hpFin, hstFin, hmFin, hwFin⟩ :=
            save_marker_finish_parser hp hpS hhead hst0S smP limit st hlimLe
              (fun _ => ⟨rsm, 0, sms2.set! 0 smNew, smNew, hsmPEq, hgsmS, hszsm3, hsm4_0.symm, rfl,
                by dsimp only [smNew]; omega, ⟨bd, offD, arrS, hdPEq, hbdS, by rw [hszArrS]; exact hwbLe2⟩⟩)
              hcurS (by rw [hz0]; omega) (by rw [hz0]; omega) (by rw [hz0]; omega) htrS
          refine ⟨.ok true, hFin, ?_, hpFin, hstFin, hmFin, fun e0 eF s0 sF he0 hse0 heF hseF hs0 hss0 hsF hssF => ?_⟩
          · rw [hpreLoopEq, C.run_bind]; erw [hloop]; dsimp only; simp only [hsuspF, Bool.false_eq_true, ↓reduceIte]; exact hrunFin
          · obtain ⟨wf, wt⟩ := hwFin e0 eF s0 sF he0 hse0 heF hseF hs0 hss0 hsF hssF
            exact ⟨fun hnf => Int.le_trans (wf hnf) (by split <;> omega), fun ht => Int.le_trans (wt ht) (by omega)⟩
    · have hlenF : (decide (length ≥ 0)) = false := by
        cases hc : decide (length ≥ 0)
        · rfl
        · exact False.elim (hlenGe (of_decide_eq_true hc))
      have hcur1_dummy : True := trivial
      have hpreLoopEq : C.run (save_marker (.ref (C.DecompRef.decomp ctx.bdc) 0)) h =
          C.run (do
            let st ← cwhile
              (fun (s : SaveMarkerState) => pure (!s.done && s.bytesRead < (0 : UInt32), s))
              (fun (s : SaveMarkerState) => do
                inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib
                let dcS ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                let mrkS ← Ptr.load dcS.marker
                Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
                match (← makeByteAvail (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
                | none => return { s with done := true, susp := true }
                | some (n1, bi1) =>
                  let cs ← cwhile
                    (fun (c : SaveMarkerCopyState) => pure (c.br < 0 && c.bb > 0, c))
                    (fun (c : SaveMarkerCopyState) => do
                      let b ← Ptr.load c.nb
                      Ptr.store c.dp b
                      let dp' ← Ptr.add c.dp 1
                      let nb' ← Ptr.add c.nb 1
                      return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
                    { br := s.bytesRead, nb := n1, bb := bi1, dp := s.dp }
                  return { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp })
              { done := false, susp := false, bytesRead := 0, nib := nib1, bib := bib1, dp := .null }
            if st.susp then return .ok false
            let mut remLength : Int64 := 0
            let mut dataArr : Array UInt8 := #[]
            if (.null : C.SavedMarkerPtr) != .null then
              let sm ← Ptr.load (.null : C.SavedMarkerPtr)
              let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
              let mst ← Ptr.load dcCur.master
              if dcCur.markerList == .null || mst.markerListEnd == .null then
                Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcCur with markerList := .null }
                Ptr.store dcCur.master { mst with markerListEnd := .null }
              else
                let tail ← Ptr.load mst.markerListEnd
                Ptr.store mst.markerListEnd { tail with next := .null }
                Ptr.store dcCur.master { mst with markerListEnd := .null }
              remLength := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat (0 : UInt32).toNat)
              for k in List.range (0 : UInt32).toNat do
                let bp ← Ptr.add sm.data (Int.ofNat k)
                let v ← Ptr.load bp
                dataArr := dataArr.push v
            let dcA ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            let mrkA ← Ptr.load dcA.marker
            Ptr.store dcA.marker { mrkA with curMarker := .null }
            if dcA.unreadMarker == M_APP0 then
              examine_app0 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr 0 remLength
            else if dcA.unreadMarker == M_APP14 then
              examine_app14 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr 0 remLength
            else
              tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
                (Int32.ofInt (Int.ofNat (0 : UInt32).toNat + remLength.toInt))
            inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib
            if remLength > 0 then
              skipInputDataDispatch (.ref (C.DecompRef.decomp ctx.bdc) 0) remLength
            return .ok true) h1 := by
        unfold save_marker
        rw [C.run_bind, hldc0]; dsimp only
        rw [C.run_bind, hlmrk0']; dsimp only
        rw [C.run_bind, hlsrc0']; dsimp only
        simp only [hcmT, ↓reduceIte]
        rw [C.run_bind, hrun1]; dsimp only
        have hlenGeF : ¬ Int64.ofInt (lenRaw.toInt - 2) ≥ 0 := hlenGe
        simp only [hlenGeF, ↓reduceIte, hcmN]; rfl
      have hcondLoopF : (!false && (0 : UInt32) < 0) = false := rfl
      have hloopZ : C.run (cwhile
          (fun (s : SaveMarkerState) => pure (!s.done && s.bytesRead < (0 : UInt32), s))
          (fun (s : SaveMarkerState) => do
            inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib
            let dcS ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            let mrkS ← Ptr.load dcS.marker
            Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
            match (← makeByteAvail (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
            | none => return { s with done := true, susp := true }
            | some (n1, bi1) =>
              let cs ← cwhile
                (fun (c : SaveMarkerCopyState) => pure (c.br < 0 && c.bb > 0, c))
                (fun (c : SaveMarkerCopyState) => do
                  let b ← Ptr.load c.nb
                  Ptr.store c.dp b
                  let dp' ← Ptr.add c.dp 1
                  let nb' ← Ptr.add c.nb 1
                  return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
                { br := s.bytesRead, nb := n1, bb := bi1, dp := s.dp }
              return { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp })
          { done := false, susp := false, bytesRead := 0, nib := nib1, bib := bib1, dp := .null }) h1 =
          .ok ({ done := false, susp := false, bytesRead := 0, nib := nib1, bib := bib1, dp := .null }, h1) := by
        rw [show C.cwhile = fun cond body init => C.cwhile.go cond body C.fuel init from rfl]
        dsimp only
        rw [show C.fuel = (2 ^ 64 - 1) + 1 from rfl, C.cwhile.go.eq_def, C.run_bind]
        simp only [C.run, pure, hcondLoopF, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hFin, hrunFin, hpFin, hstFin, hmFin, hwFin⟩ :=
        save_marker_finish_parser hp hp1 hhead hst01 .null 0
          { done := false, susp := false, bytesRead := 0, nib := nib1, bib := bib1, dp := .null }
          (by decide) (fun hne => absurd rfl hne) hcur1 (by omega) (by omega) (by omega) htr1
      refine ⟨.ok true, hFin, ?_, hpFin, hstFin, hmFin, fun e0 eF s0 sF he0 hse0 heF hseF hs0 hss0 hsF hssF => ?_⟩
      · rw [hpreLoopEq, C.run_bind, hloopZ]; dsimp only; simp only [Bool.false_eq_true, ↓reduceIte]; exact hrunFin
      · obtain ⟨wf, wt⟩ := hwFin e0 eF s0 sF he0 hse0 heF hseF hs0 hss0 hsF hssF
        exact ⟨fun hnf => Int.le_trans (wf hnf) (by split <;> omega), fun ht => Int.le_trans (wt ht) (by omega)⟩

private theorem save_marker_resume_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 18 < 2 ^ 63)
    {mrks0 : Array C.JpegMarkerReader}
    (hgmrk0 : C.Space.get h ctx.rmrk = some mrks0) (hszmrk0 : 0 < mrks0.size)
    (hcmN : mrks0[0]!.curMarker ≠ .null) :
    ∃ res h',
      C.run (save_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcMono srcs0[0]! srcs'[0]!) ∧
        (∀ errs0 errs' srcs0 srcs',
          C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
          C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
          C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          (isConstEofPtr srcs'[0]!.nextInputByte = false →
            warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
          (isConstEofPtr srcs'[0]!.nextInputByte = true →
            errs'[0]!.numWarnings.toInt ≤
              (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
               else warnPotVal errs0 srcs0) + 2 ^ 17))
      | _ => True := by
  obtain ⟨_hcore, _hfr, _dcs, _dc, _errs, _mems, _masters, _ics, _mrks, _srcs,
    _hgdc, _hszdc, _hdc, _herrp, _hgerr, _hszerr, _hrem, _hnw0,
    _hmemp, _hgmem, _hszmem, _has, _hfp, _hsd, _hlpSz, _hlp0, _hlp1, _hpaSz, _hpm, _hpi, _hpmk, _hps,
    _hmasp, _hgmas, _hszmas, _hicp, _hgic, _hszic, _hric, _hci,
    _hmrkp, _hgmrk, _hszmrk, _hrm, _hrmr, _hpcom, _hpappSz, _hpapp, _hllSz,
    _hsrcp, _hgsrc, _hszsrc, _his, _hts, _hsip, _hrtr, _hfill, _hcurv,
    hcurm0, _⟩ := id hp
  obtain ⟨dcs0, hgdc0, hszdc0, _, _, _, _, kmrk0, ksrc0⟩ := parserEnv_get_dc hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _, _, _, _, _, hcur0⟩ := parserEnv_get_src hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlmrk0 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk0 hszmrk0
  have hlmrk0' : C.run (Ptr.load dcs0[0]!.marker) h = .ok (mrks0[0]!, h) := by rw [kmrk0]; exact hlmrk0
  have hlsrc0 := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc0 hszsrc0
  have hlsrc0' : C.run (Ptr.load dcs0[0]!.src) h = .ok (srcs0[0]!, h) := by rw [ksrc0]; exact hlsrc0
  have htr0 := nibBibTrack_init ctx h srcs0 hgsrc0
  have hcmF : (mrks0[0]!.curMarker == .null) = false := by
    cases hc : (mrks0[0]!.curMarker == .null)
    · rfl
    · exact False.elim (hcmN (by simpa using hc))
  have hmrk0Eq : mrks0 = _mrks := Option.some.inj (hgmrk0.symm.trans _hgmrk)
  rw [← hmrk0Eq] at hcurm0
  rcases hcurm0 with hnull | ⟨rsm, offSm, sms, sm, hcmEq, hgsm, hoffSm, hsmEq, hdlLe, holLe, hwb, hbrLe⟩
  · exact absurd hnull hcmN
  · have hlsm := ptr_load_ok (r := rsm) (off := offSm) hgsm hoffSm
    have hlsm' : C.run (Ptr.load mrks0[0]!.curMarker) h = .ok (sm, h) := by rw [hcmEq, hsmEq]; exact hlsm
    rcases hwb with ⟨bd, offD, arrD, hdEq, hbd, hwbLe⟩
    have hbrNat : mrks0[0]!.bytesRead.toNat ≤ sm.dataLength.toNat := hbrLe
    have hbi : Int.ofNat mrks0[0]!.bytesRead.toNat = (mrks0[0]!.bytesRead.toNat : Int) := rfl
    have hadd := ptr_add_ok (r := C.BRef.heap bd) (xs := arrD) (off := offD) (k := Int.ofNat mrks0[0]!.bytesRead.toNat)
      hbd (by omega) (by rw [hbi]; omega) (by rw [hbi]; omega)
    have hadd' : C.run (Ptr.add sm.data (Int.ofNat mrks0[0]!.bytesRead.toNat)) h =
        .ok (.ref (.heap bd) (offD + mrks0[0]!.bytesRead.toNat), h) := by
      rw [hdEq]
      have h1 : ((offD : Int) + (mrks0[0]!.bytesRead.toNat : Int)).toNat = offD + mrks0[0]!.bytesRead.toNat := by omega
      simpa [h1] using hadd
    let dp0 : C.BPtr := C.Ptr.ref (.heap bd) (offD + mrks0[0]!.bytesRead.toNat)
    have hpreLoopEq : C.run (save_marker (.ref (C.DecompRef.decomp ctx.bdc) 0)) h =
        C.run (do
          let st ← cwhile
            (fun (s : SaveMarkerState) => pure (!s.done && s.bytesRead < sm.dataLength, s))
            (fun (s : SaveMarkerState) => do
              inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib
              let dcS ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
              let mrkS ← Ptr.load dcS.marker
              Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
              match (← makeByteAvail (.ref (C.DecompRef.decomp ctx.bdc) 0) s.nib s.bib) with
              | none => return { s with done := true, susp := true }
              | some (n1, bi1) =>
                let cs ← cwhile
                  (fun (c : SaveMarkerCopyState) => pure (c.br < sm.dataLength && c.bb > 0, c))
                  (fun (c : SaveMarkerCopyState) => do
                    let b ← Ptr.load c.nb
                    Ptr.store c.dp b
                    let dp' ← Ptr.add c.dp 1
                    let nb' ← Ptr.add c.nb 1
                    return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
                  { br := s.bytesRead, nb := n1, bb := bi1, dp := s.dp }
                return { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp })
            { done := false, susp := false, bytesRead := mrks0[0]!.bytesRead,
              nib := srcs0[0]!.nextInputByte, bib := srcs0[0]!.bytesInBuffer, dp := dp0 }
          if st.susp then return .ok false
          let mut remLength : Int64 := 0
          let mut dataArr : Array UInt8 := #[]
          if mrks0[0]!.curMarker != .null then
            let sm' ← Ptr.load mrks0[0]!.curMarker
            let dcCur ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            let mst ← Ptr.load dcCur.master
            if dcCur.markerList == .null || mst.markerListEnd == .null then
              Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcCur with markerList := mrks0[0]!.curMarker }
              Ptr.store dcCur.master { mst with markerListEnd := mrks0[0]!.curMarker }
            else
              let tail ← Ptr.load mst.markerListEnd
              Ptr.store mst.markerListEnd { tail with next := mrks0[0]!.curMarker }
              Ptr.store dcCur.master { mst with markerListEnd := mrks0[0]!.curMarker }
            remLength := Int64.ofInt (Int.ofNat sm'.originalLength.toNat - Int.ofNat sm.dataLength.toNat)
            for k in List.range sm.dataLength.toNat do
              let bp ← Ptr.add sm'.data (Int.ofNat k)
              let v ← Ptr.load bp
              dataArr := dataArr.push v
          let dcA ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
          let mrkA ← Ptr.load dcA.marker
          Ptr.store dcA.marker { mrkA with curMarker := .null }
          if dcA.unreadMarker == M_APP0 then
            examine_app0 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr sm.dataLength remLength
          else if dcA.unreadMarker == M_APP14 then
            examine_app14 (.ref (C.DecompRef.decomp ctx.bdc) 0) dataArr sm.dataLength remLength
          else
            tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
              (Int32.ofInt (Int.ofNat sm.dataLength.toNat + remLength.toInt))
          inputSync (.ref (C.DecompRef.decomp ctx.bdc) 0) st.nib st.bib
          if remLength > 0 then
            skipInputDataDispatch (.ref (C.DecompRef.decomp ctx.bdc) 0) remLength
          return .ok true) h := by
      unfold save_marker
      rw [C.run_bind, hldc0]; dsimp only
      rw [C.run_bind, hlmrk0']; dsimp only
      rw [C.run_bind, hlsrc0']; dsimp only
      simp only [hcmF, Bool.false_eq_true, ↓reduceIte]
      rw [C.run_bind, hlsm']; dsimp only
      rw [C.run_bind, hadd']; rfl
    have hhead17 : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
        C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
        warnPotVal errs0 srcs0 + 2 ^ 17 < 2 ^ 63 := fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega
    obtain ⟨st, hS, hloop, hpS, hst0S, _hdS, _hmaS, _hcpS, _hqS, _hhuS, hsmS, _hmeS, _hcoS, hbyS, hloopRes⟩ :=
      save_marker_loop_parser hp hp hhead17 (decompHeaderStable_refl ctx h) hbrLe hdlLe hgsm hoffSm
        (fun mrks hg' _ _ => by
          rw [Option.some.inj (hg'.symm.trans hgmrk0)]
          exact ⟨hcmEq, by rw [← hsmEq], by rw [← hsmEq]; exact holLe⟩)
        (bd := bd) (offD := offD) (arrD := arrD) (fun _ => ⟨hsmEq ▸ hdEq, hbd, hwbLe⟩)
        hcur0 (dataPtr := dp0) (fun _ => rfl) (Int.le_refl 0) (by decide) (Int.le_refl 0) htr0
    by_cases hsusp : st.susp = true
    · refine ⟨.ok false, hS, ?_, hpS, hst0S, trivial⟩
      rw [hpreLoopEq, C.run_bind]; erw [hloop]; dsimp only; simp only [hsusp, ↓reduceIte]; rfl
    · have hsuspF : st.susp = false := by cases hc : st.susp; rfl; exact False.elim (hsusp hc)
      obtain ⟨_, _, hcurS, htrS⟩ := hloopRes hsuspF
      have hgsmS : C.Space.get hS rsm = some sms := by
        rcases hrS : rsm with ⟨bs⟩; simp only [C.Space.get, hrS, hsmS] at hgsm ⊢; exact hgsm
      obtain ⟨arrS, hbdS, hszArrS⟩ := hbyS arrD hbd
      obtain ⟨hFin, hrunFin, hpFin, hstFin, hmFin, hwFin⟩ :=
        save_marker_finish_parser hp hpS hhead hst0S mrks0[0]!.curMarker sm.dataLength st hdlLe
          (fun _ => ⟨rsm, offSm, sms, sm, hcmEq, hgsmS, hoffSm, hsmEq, rfl, holLe,
            ⟨bd, offD, arrS, hdEq, hbdS, by rw [hszArrS]; exact hwbLe⟩⟩)
          hcurS (by omega) (by omega) (by omega) htrS
      refine ⟨.ok true, hFin, ?_, hpFin, hstFin, hmFin, fun e0 eF s0 sF he0 hse0 heF hseF hs0 hss0 hsF hssF => ?_⟩
      · rw [hpreLoopEq, C.run_bind]; erw [hloop]; dsimp only; simp only [hsuspF, Bool.false_eq_true, ↓reduceIte]; exact hrunFin
      · obtain ⟨wf, wt⟩ := hwFin e0 eF s0 sF he0 hse0 heF hseF hs0 hss0 hsF hssF
        exact ⟨fun hnf => Int.le_trans (wf hnf) (by split <;> omega), fun ht => Int.le_trans (wt ht) (by omega)⟩

theorem save_marker_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 18 < 2 ^ 63) :
    ∃ res h',
      C.run (save_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcMono srcs0[0]! srcs'[0]!) ∧
        (∀ errs0 errs' srcs0 srcs',
          C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
          C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
          C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          (isConstEofPtr srcs'[0]!.nextInputByte = false →
            warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
          (isConstEofPtr srcs'[0]!.nextInputByte = true →
            errs'[0]!.numWarnings.toInt ≤
              (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
               else warnPotVal errs0 srcs0) + 2 ^ 17))
      | _ => True := by
  obtain ⟨mrks0, hgmrk0, hszmrk0, _⟩ := parserEnv_get_mrk hp
  by_cases hcmN : mrks0[0]!.curMarker = .null
  · exact save_marker_new_parser hp hhead hgmrk0 hszmrk0 hcmN
  · exact save_marker_resume_parser hp hhead hgmrk0 hszmrk0 hcmN

theorem callMarkerParser_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (fn : FnPtr)
    (hfn : fn = .fn "save_marker" ∨ fn = .fn "skip_variable" ∨ fn = .fn "get_interesting_appn")
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 18 < 2 ^ 63) :
    ∃ res h',
      C.run (callMarkerParser (.ref (.decomp ctx.bdc) 0) fn) h = .ok (res, h') ∧
      ParserEnv ctx h' ∧
      DecompHeaderStable ctx h h' ∧
      match res with
      | .ok true =>
        (∀ srcs0 srcs', C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          SrcMono srcs0[0]! srcs'[0]!) ∧
        (∀ errs0 errs' srcs0 srcs',
          C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
          C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
          C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          (isConstEofPtr srcs'[0]!.nextInputByte = false →
            warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
          (isConstEofPtr srcs'[0]!.nextInputByte = true →
            errs'[0]!.numWarnings.toInt ≤
              (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
               else warnPotVal errs0 srcs0) + 2 ^ 17))
      | _ => True := by
  rcases hfn with hsv | hsk | happ
  · subst hsv
    obtain ⟨res, h', hrun, hp', hst', hpost⟩ := save_marker_parser hp hhead
    refine ⟨res, h', ?_, hp', hst', hpost⟩
    unfold callMarkerParser
    have hf1 : (FnPtr.fn "save_marker" == FnPtr.fn "skip_variable") = false := rfl
    have hf2 : (FnPtr.fn "save_marker" == FnPtr.fn "save_marker") = true := rfl
    simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte]; exact hrun
  · subst hsk
    obtain ⟨res, h', hrun, hp', hst', hpost⟩ := skip_variable_parser hp (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
    refine ⟨res, h', ?_, hp', hst', ?_⟩
    · unfold callMarkerParser
      have hf1 : (FnPtr.fn "skip_variable" == FnPtr.fn "skip_variable") = true := rfl
      simp only [hf1, ↓reduceIte]; exact hrun
    · cases res with
      | ok b =>
        cases b with
        | true =>
          rcases hpost with ⟨hstr, hw⟩
          refine ⟨fun s0 s' hs0 hss0 hs' hss' => srcMono_of_strict (hstr s0 s' hs0 hss0 hs' hss'),
            fun e0 e' s0 s' he0 hse0 he' hse' hs0 hss0 hs' hss' => ?_⟩
          obtain ⟨wf, wt⟩ := hw e0 e' s0 s' he0 hse0 he' hse' hs0 hss0 hs' hss'
          exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩
        | false => trivial
      | errExit _ => trivial
  · subst happ
    obtain ⟨res, h', hrun, hp', hst', hpost⟩ := get_interesting_appn_parser hp (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hhead e0 s0 he0 hse0 hs0 hss0; omega)
    refine ⟨res, h', ?_, hp', hst', ?_⟩
    · unfold callMarkerParser
      have hf1 : (FnPtr.fn "get_interesting_appn" == FnPtr.fn "skip_variable") = false := rfl
      have hf2 : (FnPtr.fn "get_interesting_appn" == FnPtr.fn "save_marker") = false := rfl
      have hf3 : (FnPtr.fn "get_interesting_appn" == FnPtr.fn "get_interesting_appn") = true := rfl
      simp only [hf1, hf2, hf3, Bool.false_eq_true, ↓reduceIte]; exact hrun
    · cases res with
      | ok b =>
        cases b with
        | true =>
          rcases hpost with ⟨hstr, hw⟩
          refine ⟨fun s0 s' hs0 hss0 hs' hss' => srcMono_of_strict (hstr s0 s' hs0 hss0 hs' hss'),
            fun e0 e' s0 s' he0 hse0 he' hse' hs0 hss0 hs' hss' => ?_⟩
          obtain ⟨wf, wt⟩ := hw e0 e' s0 s' he0 hse0 he' hse' hs0 hss0 hs' hss'
          exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩
        | false => trivial
      | errExit _ => trivial

/-! ## `next_marker_parser` and `read_markers_parser` -/

/-- Decompressor scan/callback fields preserved across all `read_markers` helpers before `get_sos`,
paired with monotonicity of `mrk.sawSOI ≠ 0`. -/
def RmFrame (ctx : IoCtx) (h h' : C.Heap) : Prop :=
  (∀ dcs dcs',
    C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
    C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
    dcs'[0]!.inputScanNumber = dcs[0]!.inputScanNumber ∧
    dcs'[0]!.entropyStartPass = dcs[0]!.entropyStartPass ∧
    dcs'[0]!.coefStartInputPass = dcs[0]!.coefStartInputPass ∧
    dcs'[0]!.coefConsumeData = dcs[0]!.coefConsumeData) ∧
  (∀ mrks mrks',
    C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
    C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
    mrks[0]!.sawSOI ≠ 0 → mrks'[0]!.sawSOI ≠ 0)

theorem rmFrame_refl (ctx : IoCtx) (h : C.Heap) : RmFrame ctx h h := by
  refine ⟨fun dcs dcs' h1 _ h2 _ => ?_, fun m1 m2 h1 _ h2 _ hm => ?_⟩
  · rw [Option.some.inj (h2.symm.trans h1)]; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [Option.some.inj (h2.symm.trans h1)]; exact hm

theorem rmFrame_trans (ctx : IoCtx) {a b c : C.Heap}
    (hab : RmFrame ctx a b) (hbc : RmFrame ctx b c)
    (hpB : ParserEnv ctx b) : RmFrame ctx a c := by
  obtain ⟨dcsB, hgdcB, hszdcB, _⟩ := parserEnv_get_dc hpB
  obtain ⟨mrksB, hgmrkB, hszmrkB, _⟩ := parserEnv_get_mrk hpB
  refine ⟨fun dcsA dcsC hgA hszA hgC hszC => ?_, fun mA mC hmA hszA hmC hszC hne => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hab.1 dcsA dcsB hgA hszA hgdcB hszdcB
    obtain ⟨g1, g2, g3, g4⟩ := hbc.1 dcsB dcsC hgdcB hszdcB hgC hszC
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4⟩
  · exact hbc.2 mrksB mC hgmrkB hszmrkB hmC hszC (hab.2 mA mrksB hmA hszA hgmrkB hszmrkB hne)

private def RmFrameStrong (ctx : IoCtx) (h h' : C.Heap) : Prop :=
  (∀ dcs, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
    ∃ dcs', C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' ∧ 0 < dcs'.size ∧
      dcs'[0]!.inputScanNumber = dcs[0]!.inputScanNumber ∧
      dcs'[0]!.entropyStartPass = dcs[0]!.entropyStartPass ∧
      dcs'[0]!.coefStartInputPass = dcs[0]!.coefStartInputPass ∧
      dcs'[0]!.coefConsumeData = dcs[0]!.coefConsumeData) ∧
  (∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
    ∃ mrks', C.Space.get h' ctx.rmrk = some mrks' ∧ 0 < mrks'.size ∧
      (mrks[0]!.sawSOI ≠ 0 → mrks'[0]!.sawSOI ≠ 0))

private theorem rmFrame_of_strong {ctx : IoCtx} {h h' : C.Heap} (hs : RmFrameStrong ctx h h') :
    RmFrame ctx h h' := by
  refine ⟨fun dcs dcs' hg hsz hg' _ => ?_, fun mrks mrks' hm hsz hm' _ hne => ?_⟩
  · obtain ⟨dcs1, hg1, _, h1, h2, h3, h4⟩ := hs.1 dcs hg hsz
    rw [Option.some.inj (hg'.symm.trans hg1)]
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨mrks1, hm1, _, hs1⟩ := hs.2 mrks hm hsz
    rw [Option.some.inj (hm'.symm.trans hm1)]
    exact hs1 hne

private theorem rmFrameStrong_refl (ctx : IoCtx) (h : C.Heap) : RmFrameStrong ctx h h :=
  ⟨fun dcs hg hsz => ⟨dcs, hg, hsz, rfl, rfl, rfl, rfl⟩,
   fun mrks hm hsz => ⟨mrks, hm, hsz, id⟩⟩

private theorem rmFrameStrong_of_same {ctx : IoCtx} {h h' : C.Heap}
    (hd : h'.decomps = h.decomps) (hm : h'.markers = h.markers) : RmFrameStrong ctx h h' := by
  refine ⟨fun dcs hg hsz => ⟨dcs, ?_, hsz, rfl, rfl, rfl, rfl⟩,
    fun mrks hgm hsz => ⟨mrks, ?_, hsz, id⟩⟩
  · simp only [C.Space.get]; rw [hd]; exact hg
  · cases hmrk : ctx.rmrk with | marker bm => simp only [C.Space.get, hmrk, hm] at hgm ⊢; exact hgm

private theorem rmFrameStrong_trans {ctx : IoCtx} {a b c : C.Heap}
    (hab : RmFrameStrong ctx a b) (hbc : RmFrameStrong ctx b c) : RmFrameStrong ctx a c := by
  refine ⟨fun dcsA hgA hszA => ?_, fun mA hmA hszA => ?_⟩
  · obtain ⟨dcsB, hgB, hszB, h1, h2, h3, h4⟩ := hab.1 dcsA hgA hszA
    obtain ⟨dcsC, hgC, hszC, g1, g2, g3, g4⟩ := hbc.1 dcsB hgB hszB
    exact ⟨dcsC, hgC, hszC, g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4⟩
  · obtain ⟨mB, hmB, hszB, hb1⟩ := hab.2 mA hmA hszA
    obtain ⟨mC, hmC, hszC, hb2⟩ := hbc.2 mB hmB hszB
    exact ⟨mC, hmC, hszC, fun h => hb2 (hb1 h)⟩

private theorem rmFrameStrong_bind {α β : Type} {ctx : IoCtx} {m1 : C.M α} {m2 : α → C.M β}
    (hm1 : ∀ h a h', C.run m1 h = .ok (a, h') → RmFrameStrong ctx h h')
    (hm2 : ∀ a h b h', C.run (m2 a) h = .ok (b, h') → RmFrameStrong ctx h h') :
    ∀ h b h', C.run (m1 >>= m2) h = .ok (b, h') → RmFrameStrong ctx h h' := by
  intro h b h' hrun
  cases h1 : C.run m1 h with
  | error e => rw [C.run_bind, h1] at hrun; cases hrun
  | ok p1 =>
    rcases p1 with ⟨a, ha⟩
    rw [C.run_bind, h1] at hrun
    exact rmFrameStrong_trans (hm1 h a ha h1) (hm2 a ha b h' hrun)

private theorem rmFrameStrong_cwhile {σ : Type} {ctx : IoCtx}
    (cond : σ → C.M (Bool × σ)) (body : σ → C.M σ)
    (hc : ∀ s h c s' h', C.run (cond s) h = .ok ((c, s'), h') → RmFrameStrong ctx h h')
    (hb : ∀ s h s' h', C.run (body s) h = .ok (s', h') → RmFrameStrong ctx h h') :
    ∀ s h s' h', C.run (C.cwhile cond body s) h = .ok (s', h') → RmFrameStrong ctx h h' :=
  fun _ _ _ _ hrun =>
    cwhile_preserves cond body (RmFrameStrong ctx) (fun a b => rmFrameStrong_trans a b) hc hb hrun

private theorem rmFrameStrong_forIn_range {σ : Type} {ctx : IoCtx}
    (l : List Nat) (body : Nat → σ → C.M (ForInStep σ))
    (hb : ∀ a s h step h', C.run (body a s) h = .ok (step, h') → RmFrameStrong ctx h h') :
    ∀ init h s' h', C.run (ForIn.forIn l init body) h = .ok (s', h') → RmFrameStrong ctx h h' := by
  induction l with
  | nil =>
    intro init h s' h' hrun
    simp only [ForIn.forIn, C.run] at hrun
    cases hrun; exact rmFrameStrong_refl ctx _
  | cons a tl ih =>
    intro init h s' h' hrun
    simp only [ForIn.forIn, List.forIn'_cons] at hrun
    cases h1 : C.run (body a init) h with
    | error e => rw [C.run_bind, h1] at hrun; cases hrun
    | ok p1 =>
      rcases p1 with ⟨step, h1'⟩
      rw [C.run_bind, h1] at hrun; dsimp only at hrun
      cases step with
      | done r =>
        obtain ⟨rfl, rfl⟩ := by simpa [C.run] using hrun
        exact hb a init h (.done _) h1' h1
      | yield r =>
        exact rmFrameStrong_trans (hb a init h (.yield r) h1' h1) (ih r h1' s' h' hrun)

private theorem rmFrameStrong_store_dc {ctx : IoCtx} {h h' : C.Heap}
    (p : C.DecompPtr) (v : C.JpegDecompressStruct)
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h'))
    (hsame : ∀ dcs, p = .ref (C.DecompRef.decomp ctx.bdc) 0 →
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      v.inputScanNumber = dcs[0]!.inputScanNumber ∧
      v.entropyStartPass = dcs[0]!.entropyStartPass ∧
      v.coefStartInputPass = dcs[0]!.coefStartInputPass ∧
      v.coefConsumeData = dcs[0]!.coefConsumeData) :
    RmFrameStrong ctx h h' := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩
    simp only [C.run, C.Ptr.store] at hrun
    cases hsp : C.Space.get h (C.DecompRef.decomp b) with
    | none => simp [hsp] at hrun
    | some dcs =>
      simp only [hsp] at hrun
      split at hrun
      · simp at hrun
      · split at hrun
        · next hlt =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, rfl⟩ := hrun
          refine ⟨fun dcs0 hg0 hsz0 => ?_, fun mrks hm hsz => ⟨mrks, hm, hsz, id⟩⟩
          by_cases hbd : b = ctx.bdc
          · subst hbd
            have heq0 := Option.some.inj (hg0.symm.trans hsp)
            subst heq0
            refine ⟨dcs0.set! off v, by rw [C.Space.modify_eq h _ dcs0 _ hsp]; simp [C.Space.get, C.Space.put], by simpa using hsz0, ?_⟩
            by_cases hoff : off = 0
            · subst hoff
              rw [set0_bang_m dcs0 hsz0 v]
              exact hsame dcs0 rfl hsp hsz0
            · have hne : (0 : Nat) ≠ off := Ne.symm hoff
              have hi : (dcs0.set! off v)[0]! = dcs0[0]! := by
                have hgt : 0 < (dcs0.set! off v).size := by simpa using hsz0
                have hset : (dcs0.set! off v)[0] = dcs0[0] := by
                  simp [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hsz0, hne.symm]
                rw [getElem!_pos _ 0 hgt, getElem!_pos dcs0 0 hsz0, hset]
              rw [hi]; exact ⟨rfl, rfl, rfl, rfl⟩
          · refine ⟨dcs0, ?_, hsz0, rfl, rfl, rfl, rfl⟩
            rw [C.Space.modify_eq h _ dcs _ hsp]
            simpa [C.Space.get, C.Space.put, C.upd_ne _ _ _ _ (Ne.symm hbd)] using hg0
        · simp at hrun

private theorem rmFrameStrong_store_mrk {ctx : IoCtx} {h h' : C.Heap}
    (p : C.MarkerPtr) (v : C.JpegMarkerReader)
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h'))
    (hsame : ∀ mrks, p = .ref ctx.rmrk 0 →
      C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
      mrks[0]!.sawSOI ≠ 0 → v.sawSOI ≠ 0) :
    RmFrameStrong ctx h h' := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩
    simp only [C.run, C.Ptr.store] at hrun
    cases hsp : C.Space.get h (C.MarkerRef.marker b) with
    | none => simp [hsp] at hrun
    | some mrks =>
      simp only [hsp] at hrun
      split at hrun
      · simp at hrun
      · split at hrun
        · next hlt =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, rfl⟩ := hrun
          refine ⟨fun dcs hg hsz => ⟨dcs, hg, hsz, rfl, rfl, rfl, rfl⟩, fun mrks0 hm0 hsz0 => ?_⟩
          rcases hrmEq : ctx.rmrk with ⟨bm⟩
          by_cases hbd : b = bm
          · subst hbd
            simp only [C.Space.get, hrmEq] at hsp hm0
            have heq0 := Option.some.inj (hm0.symm.trans hsp)
            subst heq0
            refine ⟨mrks0.set! off v, by rw [C.Space.modify_eq h _ mrks0 _ hsp]; simp [C.Space.get, C.Space.put], by simpa using hsz0, ?_⟩
            by_cases hoff : off = 0
            · subst hoff
              rw [set0_bang_m mrks0 hsz0 v]
              exact hsame mrks0 (by rw [hrmEq]) (by simp only [C.Space.get, hrmEq]; exact hsp) hsz0
            · have hne : (0 : Nat) ≠ off := Ne.symm hoff
              have hi : (mrks0.set! off v)[0]! = mrks0[0]! := by
                have hgt : 0 < (mrks0.set! off v).size := by simpa using hsz0
                have hset : (mrks0.set! off v)[0] = mrks0[0] := by
                  simp [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hsz0, hne.symm]
                rw [getElem!_pos _ 0 hgt, getElem!_pos mrks0 0 hsz0, hset]
              rw [hi]; exact id
          · refine ⟨mrks0, ?_, hsz0, id⟩
            rw [C.Space.modify_eq h _ mrks _ hsp]
            simpa [C.Space.get, hrmEq, C.Space.put, C.upd_ne _ _ _ _ (Ne.symm hbd)] using hm0
        · simp at hrun

private theorem ptr_load_heap_eq' {R T : Type} [C.Space C.Heap R T] {p : C.Ptr R}
    {h : C.Heap} {v : T} {h' : C.Heap}
    (hrun : C.run (C.Ptr.load p) h = .ok (v, h')) : h' = h := by
  cases p with
  | null => simp [C.run, C.Ptr.load] at hrun
  | ref r off =>
    simp only [C.run, C.Ptr.load] at hrun
    cases hg : C.Space.get h r <;> simp [hg] at hrun
    split at hrun <;> simp at hrun
    exact hrun.2.symm

private theorem rmFrameStrong_decomps_markers_same :
    ∀ (p : C.ErrPtr) (v : C.JpegErrorMgr) h h',
      C.run (C.Ptr.store p v) h = .ok ((), h') → h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  intro p v h h' hrun
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩
    simp only [C.run, C.Ptr.store] at hrun
    cases hsp : C.Space.get h (C.ErrRef.err b) with
    | none => simp [hsp] at hrun
    | some a =>
      simp only [hsp] at hrun
      split at hrun; simp at hrun
      split at hrun <;> simp at hrun
      obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_errexit {ctx : IoCtx} (ep : C.ErrPtr) (code : Int32) :
    ∀ h r h', C.run (errexit ep code) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold errexit at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1 =>
    rcases p1 with ⟨err, h1'⟩
    have heq1 := ptr_load_heap_eq' h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2 =>
      rcases p2 with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr; cases hr
      have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h' h2
      exact rmFrameStrong_of_same hd hm

private theorem rmFrameStrong_errexit1 {ctx : IoCtx} (ep : C.ErrPtr) (code p1 : Int32) :
    ∀ h r h', C.run (errexit1 ep code p1) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold errexit1 at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1' =>
    rcases p1' with ⟨err, h1'⟩
    have heq1 := ptr_load_heap_eq' h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code, msgParmI := err.msgParmI.set! 0 p1 }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2 =>
      rcases p2 with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr; cases hr
      have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h' h2
      exact rmFrameStrong_of_same hd hm

private theorem rmFrameStrong_emitMessage (ep : C.ErrPtr) (lvl : Int32) :
    ∀ h r h', C.run (emitMessage ep lvl) h = .ok (r, h') → h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  intro h r h' hr; unfold emitMessage at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1 =>
    rcases p1 with ⟨err, h1'⟩
    have heq1 := ptr_load_heap_eq' h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    by_cases hl : lvl < 0
    · simp only [hl, ↓reduceIte] at hr
      cases h2 : C.run (i64Add err.numWarnings 1) h1' with
      | error e => rw [C.run_bind, h2] at hr; cases hr
      | ok p2 =>
        rcases p2 with ⟨nw, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr
        have heq2 : h2' = h1' := by
          unfold i64Add checkI64 at h2
          split at h2
          · cases h2; rfl
          · cases h2
        subst heq2; exact rmFrameStrong_decomps_markers_same ep _ h2' h' hr
    · simp only [hl, ↓reduceIte] at hr; cases hr; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_tracems1 {ctx : IoCtx} (ep : C.ErrPtr) (lvl code p1 : Int32) :
    ∀ h r h', C.run (tracems1 ep lvl code p1) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold tracems1 at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1' =>
    rcases p1' with ⟨err, h1'⟩
    have heq1 := ptr_load_heap_eq' h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code, msgParmI := err.msgParmI.set! 0 p1 }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2 =>
      rcases p2 with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr
      have ⟨hd1, hm1⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h2' h2
      have ⟨hd2, hm2⟩ := rmFrameStrong_emitMessage ep lvl h2' r h' hr
      exact rmFrameStrong_of_same (hd2.trans hd1) (hm2.trans hm1)

private theorem rmFrameStrong_tracems2 {ctx : IoCtx} (ep : C.ErrPtr) (lvl code p1 p2 : Int32) :
    ∀ h r h', C.run (tracems2 ep lvl code p1 p2) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold tracems2 at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1' =>
    rcases p1' with ⟨err, h1'⟩
    have heq1 := ptr_load_heap_eq' h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code, msgParmI := (err.msgParmI.set! 0 p1).set! 1 p2 }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2' =>
      rcases p2' with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr
      have ⟨hd1, hm1⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h2' h2
      have ⟨hd2, hm2⟩ := rmFrameStrong_emitMessage ep lvl h2' r h' hr
      exact rmFrameStrong_of_same (hd2.trans hd1) (hm2.trans hm1)

private theorem rmFrameStrong_tracems8 {ctx : IoCtx} (ep : C.ErrPtr) (lvl code p1 p2 p3 p4 p5 p6 p7 p8 : Int32) :
    ∀ h r h', C.run (tracems8 ep lvl code p1 p2 p3 p4 p5 p6 p7 p8) h = .ok (r, h') → RmFrameStrong ctx h h' :=
  fun h r h' hr => by
  unfold tracems8 at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1' =>
    rcases p1' with ⟨err, h1'⟩
    have heq1 := ptr_load_heap_eq' h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code, msgParmI := #[p1, p2, p3, p4, p5, p6, p7, p8] }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2' =>
      rcases p2' with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr
      have ⟨hd1, hm1⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h2' h2
      have ⟨hd2, hm2⟩ := rmFrameStrong_emitMessage ep lvl h2' r h' hr
      exact rmFrameStrong_of_same (hd2.trans hd1) (hm2.trans hm1)

private theorem rmFrameStrong_warnms {ctx : IoCtx} (ep : C.ErrPtr) (code : Int32) :
    ∀ h r h', C.run (warnms ep code) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold warnms at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1' =>
    rcases p1' with ⟨err, h1'⟩
    have heq1 := ptr_load_heap_eq' h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2' =>
      rcases p2' with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr
      have ⟨hd1, hm1⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h2' h2
      have ⟨hd2, hm2⟩ := rmFrameStrong_emitMessage ep (-1) h2' r h' hr
      exact rmFrameStrong_of_same (hd2.trans hd1) (hm2.trans hm1)

private theorem rmFrameStrong_inputSync {ctx : IoCtx} (cinfo : C.DecompPtr) (nib : C.BPtr) (bib : UInt64) :
    ∀ h r h', C.run (inputSync cinfo nib bib) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold inputSync at hr
  cases h1 : C.run (Ptr.load cinfo) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1 =>
    rcases p1 with ⟨dc, h1'⟩
    have heq1 := ptr_load_heap_eq' h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.load dc.src) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2 =>
      rcases p2 with ⟨src, h2'⟩
      have heq2 := ptr_load_heap_eq' h2; subst heq2
      rw [C.run_bind, h2] at hr; dsimp only at hr
      cases hsp : C.Ptr.store dc.src { src with nextInputByte := nib, bytesInBuffer := bib } h2' with
      | error e => simp [C.run, hsp] at hr
      | ok p3 =>
        rcases p3 with ⟨_, h3⟩; simp only [C.run, hsp, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨_, rfl⟩ := hr
        have : h3.decomps = h2'.decomps ∧ h3.markers = h2'.markers := by
          revert hsp; cases dc.src with
          | null => intro hsp; simp only [C.Ptr.store] at hsp; cases hsp
          | ref r off =>
            rcases r with ⟨b⟩; intro hsp; simp only [C.Ptr.store] at hsp
            cases hg : C.Space.get h2' (C.SrcRef.src b) with
            | none => simp only [hg] at hsp; cases hsp
            | some _ =>
              simp only [hg] at hsp; split at hsp; simp at hsp
              split at hsp <;> simp at hsp; obtain ⟨_, rfl⟩ := hsp; exact ⟨rfl, rfl⟩
        exact rmFrameStrong_of_same this.1 this.2

private theorem rmFrameStrong_makeByteAvail {ctx : IoCtx} (cinfo : C.DecompPtr) (nib : C.BPtr) (bib : UInt64) :
    ∀ h r h', C.run (makeByteAvail cinfo nib bib) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold makeByteAvail at hr
  split at hr
  · cases hr; exact rmFrameStrong_refl ctx h
  · refine rmFrameStrong_bind (fun h a h' h1 => by rw [ptr_load_heap_eq' h1]; exact rmFrameStrong_refl ctx _) (fun dc h b h' hr => ?_) h r h' hr
    refine rmFrameStrong_bind (fun h a h' h1 => by rw [ptr_load_heap_eq' h1]; exact rmFrameStrong_refl ctx _) (fun src h b h' hr => ?_) h b h' hr
    split at hr
    · refine rmFrameStrong_bind (fun h res h' h1 => by
        unfold Mozjpeg.Jdatasrc.fill_mem_input_buffer at h1
        refine rmFrameStrong_bind (fun h a h' h2 => by rw [ptr_load_heap_eq' h2]; exact rmFrameStrong_refl ctx _) (fun dc1 h b h' h1 => ?_) h res h' h1
        refine rmFrameStrong_bind (rmFrameStrong_warnms dc1.err JWRN_JPEG_EOF) (fun _ h b h' h1 => ?_) h b h' h1
        refine rmFrameStrong_bind (fun h a h' h2 => by rw [ptr_load_heap_eq' h2]; exact rmFrameStrong_refl ctx _) (fun src1 h b h' h1 => ?_) h b h' h1
        refine rmFrameStrong_bind (fun h a h' h2 => ?_) (fun _ h b h' h1 => by cases h1; exact rmFrameStrong_refl ctx _) h b h' h1
        revert h2; cases dc1.src with
        | null => intro h2; simp only [C.run, C.Ptr.store] at h2; cases h2
        | ref rr oo =>
          rcases rr with ⟨bb⟩; intro h2; simp only [C.run, C.Ptr.store] at h2
          cases hg : C.Space.get h (C.SrcRef.src bb) with
          | none => simp only [hg] at h2; cases h2
          | some _ =>
            simp only [hg] at h2; split at h2; simp at h2
            split at h2 <;> simp at h2; obtain ⟨_, rfl⟩ := h2; exact rmFrameStrong_of_same rfl rfl)
        (fun ok _ _ _ h1 => by
          split at h1
          · cases h1; exact rmFrameStrong_refl ctx _
          · refine rmFrameStrong_bind (fun h a h' h2 => by rw [ptr_load_heap_eq' h2]; exact rmFrameStrong_refl ctx _) (fun src' _ _ _ h1 => by
              split at h1 <;> cases h1 <;> exact rmFrameStrong_refl ctx _) _ _ _ h1) _ _ _ hr
    · split at hr
      · cases hr; exact rmFrameStrong_refl ctx h
      · unfold C.ub at hr; cases hr

private theorem ptr_load_heap_eq {R α : Type} [C.Space C.Heap R α] {p : C.Ptr R}
    {h : C.Heap} {v : α} {h' : C.Heap} (hrun : C.run (C.Ptr.load p) h = .ok (v, h')) :
    h' = h := by
  cases p with
  | null => simp [C.run, C.Ptr.load] at hrun
  | ref r off =>
    simp only [C.run, C.Ptr.load] at hrun
    cases hg : C.Space.get h r <;> simp [hg] at hrun
    split at hrun <;> simp at hrun
    exact hrun.2.symm

private theorem dc_load_ref0_eq {bdc : Nat} {h : C.Heap} {dc : C.JpegDecompressStruct} {h' : C.Heap}
    (hrun : C.run (C.Ptr.load (.ref (C.DecompRef.decomp bdc) 0)) h = .ok (dc, h')) :
    h' = h ∧ ∀ dcs, C.Space.get h (C.DecompRef.decomp bdc) = some dcs → 0 < dcs.size → dc = dcs[0]! := by
  refine ⟨ptr_load_heap_eq hrun, fun dcs hg hsz => ?_⟩
  simp only [C.run, C.Ptr.load, hg] at hrun
  split at hrun
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun; rw [← hrun.1, getElem!_pos dcs 0 hsz]
  · contradiction

private theorem mrk_load_ref0_eq {rmrk : C.MarkerRef} {h : C.Heap} {mrk : C.JpegMarkerReader} {h' : C.Heap}
    (hrun : C.run (C.Ptr.load (.ref rmrk 0)) h = .ok (mrk, h')) :
    h' = h ∧ ∀ mrks, C.Space.get h rmrk = some mrks → 0 < mrks.size → mrk = mrks[0]! := by
  refine ⟨ptr_load_heap_eq hrun, fun mrks hg hsz => ?_⟩
  simp only [C.run, C.Ptr.load, hg] at hrun
  split at hrun
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun; rw [← hrun.1, getElem!_pos mrks 0 hsz]
  · contradiction

private theorem rmFrameStrong_bind_load {R α : Type} [C.Space C.Heap R α] {p : C.Ptr R}
    {ctx : IoCtx} {β : Type} (m2 : α → C.M β)
    (hm2 : ∀ {b} a h h', C.run (m2 a) h = .ok (b, h') → C.run (Ptr.load p) h = .ok (a, h) → RmFrameStrong ctx h h') :
    ∀ h b h', C.run (C.Ptr.load p >>= m2) h = .ok (b, h') → RmFrameStrong ctx h h' := by
  intro h b h' hrun
  cases h1 : C.run (C.Ptr.load p) h with
  | error e => rw [C.run_bind, h1] at hrun; cases hrun
  | ok p1 =>
    rcases p1 with ⟨a, h1'⟩
    have heq := ptr_load_heap_eq h1
    subst heq
    rw [C.run_bind, h1] at hrun; dsimp only at hrun
    exact hm2 a h1' h' hrun h1

private theorem rmFrameStrong_bind_load_here {R α : Type} [C.Space C.Heap R α] {p : C.Ptr R}
    {ctx : IoCtx} {β : Type} {h : C.Heap} (m2 : α → C.M β)
    (hm2 : ∀ {b} a h', C.run (m2 a) h = .ok (b, h') → C.run (Ptr.load p) h = .ok (a, h) → RmFrameStrong ctx h h') :
    ∀ b h', C.run (C.Ptr.load p >>= m2) h = .ok (b, h') → RmFrameStrong ctx h h' := by
  intro b h' hrun
  cases h1 : C.run (C.Ptr.load p) h with
  | error e => rw [C.run_bind, h1] at hrun; cases hrun
  | ok p1 =>
    rcases p1 with ⟨a, h1'⟩
    have heq := ptr_load_heap_eq h1
    subst heq
    rw [C.run_bind, h1] at hrun; dsimp only at hrun
    exact hm2 a h' hrun h1

private theorem rmFrameStrong_bind_here {α β : Type} {ctx : IoCtx} {m1 : C.M α} {m2 : α → C.M β} {h : C.Heap}
    (hm1 : ∀ a h1, C.run m1 h = .ok (a, h1) → RmFrameStrong ctx h h1)
    (hm2 : ∀ a h1 b h', C.run (m2 a) h1 = .ok (b, h') → RmFrameStrong ctx h1 h') :
    ∀ b h', C.run (m1 >>= m2) h = .ok (b, h') → RmFrameStrong ctx h h' := by
  intro b h' hrun
  cases h1 : C.run m1 h with
  | error e => rw [C.run_bind, h1] at hrun; cases hrun
  | ok p1 =>
    rcases p1 with ⟨a, ha⟩
    rw [C.run_bind, h1] at hrun
    exact rmFrameStrong_trans (hm1 a ha h1) (hm2 a ha b h' hrun)

private theorem rmFrameStrong_bind_load_store_mrk {ctx : IoCtx} {β : Type} (p : C.MarkerPtr)
    (f : C.JpegMarkerReader → C.JpegMarkerReader)
    (hf : ∀ m, m.sawSOI ≠ 0 → (f m).sawSOI ≠ 0)
    (k : C.M β) (hk : ∀ h r h', C.run k h = .ok (r, h') → RmFrameStrong ctx h h') :
    ∀ h r h', C.run (do let m ← Ptr.load p; Ptr.store p (f m); k) h = .ok (r, h') → RmFrameStrong ctx h h' := by
  intro h r h' hr
  refine rmFrameStrong_bind_load _ (fun m _ _ hst hl => ?_) h r h' hr
  refine rmFrameStrong_bind_here (fun _ _ hst' => ?_) (fun _ _ _ _ hk' => hk _ _ _ hk') _ _ hst
  refine rmFrameStrong_store_mrk p (f m) hst' (fun mrks hp hgm hsz hne => ?_)
  subst hp
  have hmEq := (mrk_load_ref0_eq hl).2 mrks hgm hsz
  exact hf m (by rw [hmEq]; exact hne)

private theorem rmFrameStrong_decomps_markers_eq_of_store_src {p : C.SrcPtr} {v : C.JpegSourceMgr} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) :
    h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩; simp only [C.run, C.Ptr.store] at hrun
    cases hg : C.Space.get h (C.SrcRef.src b) with
    | none => simp only [hg] at hrun; cases hrun
    | some _ =>
      simp only [hg] at hrun; split at hrun; simp at hrun
      split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_decomps_markers_eq_of_store_mem {p : C.MemPtr} {v : C.JpegMemMgr} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) :
    h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩; simp only [C.run, C.Ptr.store] at hrun
    cases hg : C.Space.get h (C.MemRef.mem b) with
    | none => simp only [hg] at hrun; cases hrun
    | some _ =>
      simp only [hg] at hrun; split at hrun; simp at hrun
      split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_decomps_markers_eq_of_store_master {p : C.MasterPtr} {v : C.JpegDecompMaster} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) :
    h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩; simp only [C.run, C.Ptr.store] at hrun
    cases hg : C.Space.get h (C.MasterRef.master b) with
    | none => simp only [hg] at hrun; cases hrun
    | some _ =>
      simp only [hg] at hrun; split at hrun; simp at hrun
      split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_decomps_markers_eq_of_store_quant {p : C.QuantPtr} {v : C.JQuantTbl} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) :
    h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩; simp only [C.run, C.Ptr.store] at hrun
    cases hg : C.Space.get h (C.QuantRef.quant b) with
    | none => simp only [hg] at hrun; cases hrun
    | some _ =>
      simp only [hg] at hrun; split at hrun; simp at hrun
      split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_decomps_markers_eq_of_store_huff {p : C.HuffPtr} {v : C.JHuffTbl} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) :
    h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩; simp only [C.run, C.Ptr.store] at hrun
    cases hg : C.Space.get h (C.HuffRef.huff b) with
    | none => simp only [hg] at hrun; cases hrun
    | some _ =>
      simp only [hg] at hrun; split at hrun; simp at hrun
      split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_decomps_markers_eq_of_store_comp {p : C.CompPtr} {v : C.JpegCompInfo} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) :
    h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩; simp only [C.run, C.Ptr.store] at hrun
    cases hg : C.Space.get h (C.CompRef.comp b) with
    | none => simp only [hg] at hrun; cases hrun
    | some _ =>
      simp only [hg] at hrun; split at hrun; simp at hrun
      split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_decomps_markers_eq_of_store_sm {p : C.SavedMarkerPtr} {v : C.JpegSavedMarker} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) :
    h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩; simp only [C.run, C.Ptr.store] at hrun
    cases hg : C.Space.get h (C.SavedMarkerRef.savedMarker b) with
    | none => simp only [hg] at hrun; cases hrun
    | some _ =>
      simp only [hg] at hrun; split at hrun; simp at hrun
      split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem rmFrameStrong_decomps_markers_eq_of_store_byte {p : C.BPtr} {v : UInt8} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) :
    h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    simp only [C.run, C.Ptr.store] at hrun
    cases r with
    | heap b =>
      cases hg : C.Space.get h (C.BRef.heap b) with
      | none => simp only [hg] at hrun; cases hrun
      | some _ =>
        simp only [hg] at hrun; split at hrun; simp at hrun
        split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩
    | const b =>
      cases hg : C.Space.get h (C.BRef.const b) with
      | none => simp only [hg] at hrun; cases hrun
      | some _ =>
        simp only [hg] at hrun; split at hrun; simp at hrun
        split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩
    | const_eof =>
      cases hg : C.Space.get h C.BRef.const_eof with
      | none => simp only [hg] at hrun; cases hrun
      | some _ =>
        simp only [hg] at hrun; split at hrun; simp at hrun
        split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩
    | str i =>
      cases hg : C.Space.get h (C.BRef.str i) with
      | none => simp only [hg] at hrun; cases hrun
      | some _ =>
        simp only [hg] at hrun; split at hrun; simp at hrun
        split at hrun <;> simp at hrun; obtain ⟨_, rfl⟩ := hrun; exact ⟨rfl, rfl⟩

private theorem ptr_add_bptr_heap_eq {p : C.BPtr} {k : Int} {h : C.Heap} {p' : C.BPtr} {h' : C.Heap}
    (hrun : C.run (C.Ptr.add p k) h = .ok (p', h')) : h' = h := by
  cases p with
  | null => simp [C.run, C.Ptr.add] at hrun
  | ref r off =>
    simp only [C.run, C.Ptr.add] at hrun
    cases hg : C.Space.get h r <;> simp [hg] at hrun
    split at hrun <;> simp at hrun
    exact hrun.2.symm

private theorem ptr_add_comp_heap_eq {p : C.CompPtr} {k : Int} {h : C.Heap} {p' : C.CompPtr} {h' : C.Heap}
    (hrun : C.run (C.Ptr.add p k) h = .ok (p', h')) : h' = h := by
  cases p with
  | null => simp [C.run, C.Ptr.add] at hrun
  | ref r off =>
    simp only [C.run, C.Ptr.add] at hrun
    cases hg : C.Space.get h r <;> simp [hg] at hrun
    split at hrun <;> simp at hrun
    exact hrun.2.symm

private theorem rmFrameStrong_inputByte {ctx : IoCtx} (cinfo : C.DecompPtr) (nib : C.BPtr) (bib : UInt64) :
    ∀ h r h', C.run (inputByte cinfo nib bib) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold inputByte at hr
  refine rmFrameStrong_bind (rmFrameStrong_makeByteAvail cinfo nib bib) (fun x h b h' hr => ?_) h r h' hr
  cases x with
  | none => cases hr; exact rmFrameStrong_refl ctx h
  | some p =>
    refine rmFrameStrong_bind_load _ (fun _ h _ hr _ => ?_) h b h' hr
    cases h2 : C.run (C.Ptr.add p.1 1) h with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok q =>
      rw [C.run_bind, h2] at hr; dsimp only at hr
      have := ptr_add_bptr_heap_eq h2
      rw [this] at hr; cases hr; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_input2Bytes {ctx : IoCtx} (cinfo : C.DecompPtr) (nib : C.BPtr) (bib : UInt64) :
    ∀ h r h', C.run (input2Bytes cinfo nib bib) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold input2Bytes at hr
  refine rmFrameStrong_bind (rmFrameStrong_inputByte cinfo nib bib) (fun x h b h' hr => ?_) h r h' hr
  cases x with
  | none => cases hr; exact rmFrameStrong_refl ctx h
  | some p =>
    refine rmFrameStrong_bind (rmFrameStrong_inputByte cinfo p.2.1 p.2.2) (fun y h b h' hr => ?_) h b h' hr
    cases y with
    | none => cases hr; exact rmFrameStrong_refl ctx h
    | some q => cases hr; exact rmFrameStrong_refl ctx h

private theorem rmFrameStrong_skipInputDataDispatch {ctx : IoCtx} (cinfo : C.DecompPtr) (n : Int64) :
    ∀ h r h', C.run (skipInputDataDispatch cinfo n) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold skipInputDataDispatch at hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun src _ _ hr _ => ?_) _ _ _ hr
  split at hr
  · unfold Mozjpeg.Jdatasrc.skip_input_data at hr
    refine rmFrameStrong_bind_load _ (fun dc _ _ hr _ => ?_) _ _ _ hr
    split at hr
    · refine rmFrameStrong_bind (rmFrameStrong_cwhile _ _ ?_ ?_ _) (fun rem _ _ _ hr => ?_) _ _ _ hr
      · intro nb _ _ _ _ hr
        exact rmFrameStrong_bind_load _ (fun _ _ _ hr _ => by split at hr <;> cases hr <;> exact rmFrameStrong_refl ctx _) _ _ _ hr
      · intro nb _ _ _ hr
        refine rmFrameStrong_bind_load _ (fun src _ _ hr _ => ?_) _ _ _ hr
        split at hr
        · refine rmFrameStrong_bind ?_ (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
          intro _ _ _ h1
          unfold Mozjpeg.Jdatasrc.fill_mem_input_buffer at h1
          refine rmFrameStrong_bind_load _ (fun dc1 _ _ h1 _ => ?_) _ _ _ h1
          refine rmFrameStrong_bind (rmFrameStrong_warnms dc1.err JWRN_JPEG_EOF) (fun _ _ _ _ h1 => ?_) _ _ _ h1
          refine rmFrameStrong_bind_load _ (fun src1 _ _ h1 _ => ?_) _ _ _ h1
          refine rmFrameStrong_bind ?_ (fun _ _ _ _ h2 => by cases h2; exact rmFrameStrong_refl ctx _) _ _ _ h1
          intro _ _ _ h2
          have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_src h2
          exact rmFrameStrong_of_same hd hm
        · unfold C.ub at hr; cases hr
      · refine rmFrameStrong_bind_load _ (fun src _ _ hr _ => ?_) _ _ _ hr
        cases ha : C.run (C.Ptr.add src.nextInputByte (Int.ofNat rem.toInt.toNat)) _ with
        | error _ => rw [C.run_bind, ha] at hr; cases hr
        | ok q =>
          rcases q with ⟨nextP, hq⟩; dsimp only at hr
          have heq : hq = _ := ptr_add_bptr_heap_eq ha; subst heq
          rw [C.run_bind, ha] at hr; dsimp only at hr
          have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_src hr
          exact rmFrameStrong_of_same hd hm
    · cases hr; exact rmFrameStrong_refl ctx _
  · split at hr
    · cases hr; exact rmFrameStrong_refl ctx _
    · unfold C.ub at hr; cases hr

private theorem rmFrameStrong_out_of_memory {ctx : IoCtx} (cinfo : C.DecompPtr) (which : Int32) :
    ∀ h r h', C.run (Mozjpeg.Jmemmgr.out_of_memory cinfo which) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold Mozjpeg.Jmemmgr.out_of_memory at hr
  exact rmFrameStrong_bind_load _ (fun dc _ _ hr _ => rmFrameStrong_errexit1 dc.err JERR_OUT_OF_MEMORY which _ _ _ hr) h r h' hr

private theorem rmFrameStrong_allocSlopRetry {R : Type} [DecidableEq R] {ctx : IoCtx}
    (cinfo : C.DecompPtr) (allocFn : C.M (C.Ptr R))
    (ha : ∀ h p h', C.run allocFn h = .ok (p, h') → RmFrameStrong ctx h h') :
    ∀ k slop h r h', C.run (Mozjpeg.Jmemmgr.allocSlopRetry cinfo allocFn k slop) h = .ok (r, h') →
      RmFrameStrong ctx h h' := by
  intro k
  induction k with
  | zero =>
    intro slop h r h' hr
    unfold Mozjpeg.Jmemmgr.allocSlopRetry at hr
    exact rmFrameStrong_bind (rmFrameStrong_out_of_memory cinfo 2)
      (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
  | succ k ih =>
    intro slop h r h' hr
    unfold Mozjpeg.Jmemmgr.allocSlopRetry at hr
    refine rmFrameStrong_bind ha (fun p _ _ _ hr => ?_) _ _ _ hr
    split at hr
    · cases hr; exact rmFrameStrong_refl ctx _
    · dsimp (config := { zetaHave := true }) only at hr
      split at hr
      · exact rmFrameStrong_bind (rmFrameStrong_out_of_memory cinfo 2)
          (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
      · exact ih _ _ _ _ hr

private theorem rmFrameStrong_allocSmallCore {R : Type} [DecidableEq R] {ctx : IoCtx}
    (cinfo : C.DecompPtr) (pool_id : Int32) (sizeofobject : UInt64)
    (allocFn : C.M (C.Ptr R))
    (ha : ∀ h p h', C.run allocFn h = .ok (p, h') → RmFrameStrong ctx h h')
    (pushPool : C.PoolAllocs → C.Ptr R → C.PoolAllocs) :
    ∀ h r h', C.run (Mozjpeg.Jmemmgr.allocSmallCore cinfo pool_id sizeofobject allocFn pushPool) h = .ok (r, h') →
      RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold Mozjpeg.Jmemmgr.allocSmallCore at hr
  refine rmFrameStrong_bind_load _ (fun dc _ _ hr _ => ?_) h r h' hr
  dsimp (config := { zetaHave := true }) only at hr
  split at hr
  · exact rmFrameStrong_bind (rmFrameStrong_out_of_memory cinfo 7) (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
  · split at hr
    · exact rmFrameStrong_bind (rmFrameStrong_out_of_memory cinfo 1) (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
    · split at hr
      · refine rmFrameStrong_bind (rmFrameStrong_errexit1 dc.err JERR_BAD_POOL_ID pool_id)
          (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
      · refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
        refine rmFrameStrong_bind (rmFrameStrong_allocSlopRetry cinfo allocFn ha 16 _) (fun res _ _ _ hr => ?_) _ _ _ hr
        cases res with
        | errExit _ => cases hr; exact rmFrameStrong_refl ctx _
        | ok p =>
          refine rmFrameStrong_bind_load _ (fun dc2 _ _ hr _ => ?_) _ _ _ hr
          refine rmFrameStrong_bind_load _ (fun mem2 _ _ hr _ => ?_) _ _ _ hr
          refine rmFrameStrong_bind (fun _ _ _ h1 => by
            have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_mem h1
            exact rmFrameStrong_of_same hd hm) (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr

private theorem rmFrameStrong_alloc_large_saved_marker {ctx : IoCtx}
    (cinfo : C.DecompPtr) (pool_id : Int32) (limit : Nat) :
    ∀ h r h', C.run (Mozjpeg.Jmemmgr.alloc_large_saved_marker cinfo pool_id limit) h = .ok (r, h') →
      RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold Mozjpeg.Jmemmgr.alloc_large_saved_marker at hr
  refine rmFrameStrong_bind_load _ (fun dc _ _ hr _ => ?_) h r h' hr
  dsimp (config := { zetaHave := true }) only at hr
  split at hr
  · exact rmFrameStrong_bind (rmFrameStrong_out_of_memory cinfo 8) (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
  · split at hr
    · exact rmFrameStrong_bind (rmFrameStrong_out_of_memory cinfo 3) (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
    · split at hr
      · refine rmFrameStrong_bind (rmFrameStrong_errexit1 dc.err JERR_BAD_POOL_ID pool_id)
          (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
      · refine rmFrameStrong_bind (fun h0 p h1 hget => by
          unfold Mozjpeg.Jmemnobs.jpeg_get_large_saved_marker at hget
          simp only [C.run] at hget
          cases ha : h0.allocOk h0.nalloc <;> simp only [ha, C.allocSavedMarkerData, ↓reduceIte, Bool.false_eq_true] at hget
          · cases hget; exact rmFrameStrong_of_same rfl rfl
          · cases hget; exact rmFrameStrong_of_same rfl rfl)
          (fun ptr _ _ _ hr => by
            split at hr
            · exact rmFrameStrong_bind (rmFrameStrong_out_of_memory cinfo 4) (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
            · refine rmFrameStrong_bind_load _ (fun dc2 _ _ hr _ => ?_) _ _ _ hr
              refine rmFrameStrong_bind_load _ (fun mem2 _ _ hr _ => ?_) _ _ _ hr
              refine rmFrameStrong_bind (fun _ _ _ h1 => by
                have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_mem h1
                exact rmFrameStrong_of_same hd hm) (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr) _ _ _ hr

private theorem tracems4_decomps_markers_eq (ep : C.ErrPtr) (lvl code p1 p2 p3 p4 : Int32) :
    ∀ h r h', C.run (tracems4 ep lvl code p1 p2 p3 p4) h = .ok (r, h') →
      h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  intro h r h' hr; unfold tracems4 at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1' =>
    rcases p1' with ⟨err, h1'⟩; have heq1 := ptr_load_heap_eq h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code, msgParmI := (((err.msgParmI.set! 0 p1).set! 1 p2).set! 2 p3).set! 3 p4 }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2' =>
      rcases p2' with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr
      have ⟨hd1, hm1⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h2' h2
      have ⟨hd2, hm2⟩ := rmFrameStrong_emitMessage ep lvl h2' r h' hr
      exact ⟨hd2.trans hd1, hm2.trans hm1⟩

private theorem tracems5_decomps_markers_eq (ep : C.ErrPtr) (lvl code p1 p2 p3 p4 p5 : Int32) :
    ∀ h r h', C.run (tracems5 ep lvl code p1 p2 p3 p4 p5) h = .ok (r, h') →
      h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  intro h r h' hr; unfold tracems5 at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1' =>
    rcases p1' with ⟨err, h1'⟩; have heq1 := ptr_load_heap_eq h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code, msgParmI := ((((err.msgParmI.set! 0 p1).set! 1 p2).set! 2 p3).set! 3 p4).set! 4 p5 }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2' =>
      rcases p2' with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr
      have ⟨hd1, hm1⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h2' h2
      have ⟨hd2, hm2⟩ := rmFrameStrong_emitMessage ep lvl h2' r h' hr
      exact ⟨hd2.trans hd1, hm2.trans hm1⟩

private theorem rmFrameStrong_warnms2 {ctx : IoCtx} (ep : C.ErrPtr) (code p1 p2 : Int32) :
    ∀ h r h', C.run (warnms2 ep code p1 p2) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold warnms2 at hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind (fun _ _ _ h2 => by
    have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_same ep _ _ _ h2; exact rmFrameStrong_of_same hd hm)
    (fun _ _ _ _ h2 => by have ⟨hd, hm⟩ := rmFrameStrong_emitMessage ep (-1) _ _ _ h2; exact rmFrameStrong_of_same hd hm) _ _ _ hr

private theorem rmFrameStrong_examine_app0_tail {ctx : IoCtx} (ep : C.ErrPtr)
    (data : Array UInt8) (totallen : Int64) (vMaj vMin dUnit : UInt8) (xD yD : UInt16) :
    ∀ h r h', C.run (do
      tracems5 ep 1 JTRC_JFIF
        (Int32.ofNat vMaj.toNat) (Int32.ofNat vMin.toNat)
        (Int32.ofNat xD.toNat) (Int32.ofNat yD.toNat) (Int32.ofNat dUnit.toNat)
      if (data[12]! ||| data[13]!) != 0 then
        tracems2 ep 1 JTRC_JFIF_THUMBNAIL (Int32.ofNat data[12]!.toNat) (Int32.ofNat data[13]!.toNat)
      let remThumb : Int64 := Int64.ofInt (totallen.toInt - Int.ofNat APP0_DATA_LEN.toNat)
      if remThumb.toInt != Int.ofNat data[12]!.toNat * Int.ofNat data[13]!.toNat * 3 then
        tracems1 ep 1 JTRC_JFIF_BADTHUMBNAILSIZE (Int32.ofInt remThumb.toInt)) h = .ok (r, h') →
      RmFrameStrong ctx h h' := fun h r h' hr => by
  refine rmFrameStrong_bind ?_ (fun _ _ _ _ hr => ?_) h r h' hr
  · intro _ _ _ h2; have ⟨hd, hm⟩ := tracems5_decomps_markers_eq _ _ _ _ _ _ _ _ _ _ _ h2; exact rmFrameStrong_of_same hd hm
  · split at hr
    · refine rmFrameStrong_bind (rmFrameStrong_tracems2 _ 1 JTRC_JFIF_THUMBNAIL _ _) (fun _ _ _ _ hr => ?_) _ _ _ hr
      dsimp (config := { zetaHave := true }) only at hr
      split at hr
      · exact rmFrameStrong_tracems1 _ 1 JTRC_JFIF_BADTHUMBNAILSIZE _ _ _ _ hr
      · cases hr; exact rmFrameStrong_refl ctx _
    · dsimp (config := { zetaHave := true }) only at hr
      split at hr
      · exact rmFrameStrong_tracems1 _ 1 JTRC_JFIF_BADTHUMBNAILSIZE _ _ _ _ hr
      · cases hr; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_examine_app0 {ctx : IoCtx}
    (data : Array UInt8) (datalen : UInt32) (remaining : Int64) :
    ∀ h r h', C.run (examine_app0 (.ref (.decomp ctx.bdc) 0) data datalen remaining) h = .ok (r, h') →
      RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold examine_app0 at hr
  refine rmFrameStrong_bind_load _ (fun dc h _ hr hl => ?_) h r h' hr
  have hdcEq := (dc_load_ref0_eq hl).2
  dsimp (config := { zetaHave := true }) only at hr
  split at hr
  · refine rmFrameStrong_bind_here (fun _ h1 hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
      rw [← hdcEq dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) (fun _ _ _ _ hr => ?_) _ _ hr
    split at hr
    · refine rmFrameStrong_bind (rmFrameStrong_warnms2 _ _ _ _) (fun _ _ _ _ hr =>
        rmFrameStrong_examine_app0_tail _ _ _ _ _ _ _ _ _ _ _ hr) _ _ _ hr
    · exact rmFrameStrong_examine_app0_tail _ _ _ _ _ _ _ _ _ _ _ hr
  · split at hr
    · split at hr
      · exact rmFrameStrong_tracems1 dc.err 1 JTRC_THUMB_JPEG _ _ _ _ hr
      · split at hr
        · exact rmFrameStrong_tracems1 dc.err 1 JTRC_THUMB_PALETTE _ _ _ _ hr
        · split at hr
          · exact rmFrameStrong_tracems1 dc.err 1 JTRC_THUMB_RGB _ _ _ _ hr
          · exact rmFrameStrong_tracems2 dc.err 1 JTRC_JFIF_EXTENSION _ _ _ _ _ hr
    · exact rmFrameStrong_tracems1 dc.err 1 JTRC_APP0 _ _ _ _ hr

private theorem rmFrameStrong_examine_app14 {ctx : IoCtx}
    (data : Array UInt8) (datalen : UInt32) (remaining : Int64) :
    ∀ h r h', C.run (examine_app14 (.ref (.decomp ctx.bdc) 0) data datalen remaining) h = .ok (r, h') →
      RmFrameStrong ctx h h' := fun h r h' hr => by
  unfold examine_app14 at hr
  refine rmFrameStrong_bind_load _ (fun dc h _ hr hl => ?_) h r h' hr
  have hdcEq := (dc_load_ref0_eq hl).2
  split at hr
  · cases htr : C.run (tracems4 dc.err 1 JTRC_ADOBE _ _ _ _) h with
    | error e => rw [C.run_bind, htr] at hr; cases hr
    | ok p1 =>
      rcases p1 with ⟨_, h1⟩; rw [C.run_bind, htr] at hr
      have ⟨hd1, hm1⟩ := tracems4_decomps_markers_eq dc.err 1 JTRC_ADOBE _ _ _ _ h () h1 htr
      refine rmFrameStrong_trans (rmFrameStrong_of_same hd1 hm1)
        (rmFrameStrong_store_dc _ _ hr (fun dcs _ hg hsz => by
          have hg0 : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs := by
            simp only [C.Space.get] at hg ⊢; rw [hd1] at hg; exact hg
          rw [← hdcEq dcs hg0 hsz]; exact ⟨rfl, rfl, rfl, rfl⟩))
  · exact rmFrameStrong_tracems1 dc.err 1 JTRC_APP14 _ _ _ _ hr

private theorem rmFrameStrong_first_marker {ctx : IoCtx} {h r h'}
    (hr : C.run (first_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold first_marker at hr
  refine rmFrameStrong_bind_load _ (fun dc0 _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun src0 _ _ hr _ => ?_) _ _ _ hr
  refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
  cases x with
  | none => cases hr; exact rmFrameStrong_refl ctx _
  | some p =>
    refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun y _ _ _ hr => ?_) _ _ _ hr
    cases y with
    | none => cases hr; exact rmFrameStrong_refl ctx _
    | some q =>
      rcases q with ⟨c1, nib1, bib1⟩; dsimp only at hr
      split at hr
      · refine rmFrameStrong_bind (rmFrameStrong_errexit2 _ _ _ _) ?_ _ _ _ hr
        intro _ _ _ _ h1; cases h1; exact rmFrameStrong_refl ctx _
      · refine rmFrameStrong_bind_load _ (fun dc1 _ _ hr hl1 => ?_) _ _ _ hr
        have hdc1 := (dc_load_ref0_eq hl1).2
        refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
          rw [← hdc1 dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩))
          (fun _ _ _ _ hr => rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _)
            (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr) _ _ hr
where
  rmFrameStrong_errexit2 (ep : C.ErrPtr) (code p1 p2 : Int32) :
      ∀ h r h', C.run (errexit2 ep code p1 p2) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
    unfold errexit2 at hr
    refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) h r h' hr
    refine rmFrameStrong_bind ?_ ?_ _ _ _ hr
    · intro _ _ _ h2; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_same ep _ _ _ h2; exact rmFrameStrong_of_same hd hm
    · intro _ _ _ _ h2; cases h2; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_get_soi {ctx : IoCtx} {h r h'}
    (hr : C.run (get_soi (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold get_soi at hr
  refine rmFrameStrong_bind_load _ (fun dc0 _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind ?_ (fun _ _ _ _ hr => ?_) _ _ _ hr
  · intro _ _ _ h1
    unfold tracems at h1
    refine rmFrameStrong_bind_load _ (fun _ _ _ h1 _ => ?_) _ _ _ h1
    refine rmFrameStrong_bind ?_ ?_ _ _ _ h1
    · intro _ _ _ h2; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_same _ _ _ _ h2; exact rmFrameStrong_of_same hd hm
    · intro _ _ _ _ h2; have ⟨hd, hm⟩ := rmFrameStrong_emitMessage _ _ _ _ _ h2; exact rmFrameStrong_of_same hd hm
  · refine rmFrameStrong_bind_load _ (fun mrk0 _ _ hr _ => ?_) _ _ _ hr
    split at hr
    · refine rmFrameStrong_bind (rmFrameStrong_errexit dc0.err JERR_SOI_DUPLICATE) ?_ _ _ _ hr
      intro _ _ _ _ h1; cases h1; exact rmFrameStrong_refl ctx _
    · refine rmFrameStrong_bind_load _ (fun dc' _ _ hr hldc => ?_) _ _ _ hr
      have hdc' := (dc_load_ref0_eq hldc).2
      refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
        rw [← hdc' dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩))
        (fun _ _ _ _ hr => rmFrameStrong_bind_load _ (fun mrk' _ _ hr _ => ?_) _ _ _ hr) _ _ hr
      refine rmFrameStrong_bind ?_ (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr
      intro _ _ _ hst
      exact rmFrameStrong_store_mrk _ _ hst (fun _ _ _ _ _ => (by decide : (TRUE : Int32) ≠ 0))

private theorem get_soi_sawSOI_true {ctx : IoCtx} {h h' : C.Heap}
    (hp : ParserEnv ctx h)
    (hrun : C.run (get_soi (.ref (.decomp ctx.bdc) 0)) h = .ok (.ok true, h')) :
    ∃ mrks', C.Space.get h' ctx.rmrk = some mrks' ∧ 0 < mrks'.size ∧ mrks'[0]!.sawSOI ≠ 0 := by
  obtain ⟨dcs0, hgdc0, hszdc0, kerr0, _, _, _, kmrk0, _⟩ := parserEnv_get_dc hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  unfold get_soi at hrun
  rw [C.run_bind, hldc0] at hrun; dsimp only at hrun
  obtain ⟨h1, htr1, hp1, hd1, hmr1, _, _, _, _, _, _, _, _, _, _⟩ :=
    tracems_nonneg_parser hp 1 JTRC_SOI (by decide)
  have htr1' : C.run (tracems dcs0[0]!.err 1 JTRC_SOI) h = .ok ((), h1) := by rw [kerr0]; exact htr1
  rw [C.run_bind, htr1'] at hrun; dsimp only at hrun
  obtain ⟨mrks1, hgmrk1, hszmrk1, _⟩ := parserEnv_get_mrk hp1
  have hlmrk1 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk1 hszmrk1
  have hlmrk1' : C.run (Ptr.load dcs0[0]!.marker) h1 = .ok (mrks1[0]!, h1) := by rw [kmrk0]; exact hlmrk1
  rw [C.run_bind, hlmrk1'] at hrun; dsimp only at hrun
  split at hrun
  · cases herr : C.run (errexit dcs0[0]!.err JERR_SOI_DUPLICATE) h1 <;>
      rw [C.run_bind, herr] at hrun <;> cases hrun
  · obtain ⟨dcs1, hgdc1, hszdc1, _, _, _, _, kmrk1, _⟩ := parserEnv_get_dc hp1
    have hldc1 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc1 hszdc1
    rw [C.run_bind, hldc1] at hrun; dsimp only at hrun
    have hroDc1 : C.Space.ro h1 (C.DecompRef.decomp ctx.bdc) = false := rfl
    let dc1' := { dcs1[0]! with
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
        adobeTransform := 0 }
    have hstDc1 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0)
      (v := dc1') hgdc1 hroDc1 hszdc1
    rw [C.run_bind, hstDc1] at hrun; dsimp only at hrun
    let h2 := C.Space.put h1 (C.DecompRef.decomp ctx.bdc) (dcs1.set! 0 dc1')
    have hgmrk2 : C.Space.get h2 ctx.rmrk = some mrks1 := by
      simpa [h2, C.Space.get, C.Space.put] using hgmrk1
    have hlmrk2 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrk2 hszmrk1
    have kmrk2 : dcs1[0]!.marker = .ref ctx.rmrk 0 := kmrk1
    have hlmrk2' : C.run (Ptr.load dcs1[0]!.marker) h2 = .ok (mrks1[0]!, h2) := by
      rw [kmrk2]; exact hlmrk2
    rw [C.run_bind, hlmrk2'] at hrun; dsimp only at hrun
    have hroM2 : C.Space.ro h2 ctx.rmrk = false := by cases ctx.rmrk; rfl
    have hstM2 := ptr_store_ok (r := ctx.rmrk) (off := 0)
      (v := { mrks1[0]! with sawSOI := TRUE }) hgmrk2 hroM2 hszmrk1
    rw [kmrk2, C.run_bind, hstM2] at hrun
    cases hrun
    refine ⟨mrks1.set! 0 { mrks1[0]! with sawSOI := TRUE }, ?_, by simpa using hszmrk1, ?_⟩
    · cases hrm : ctx.rmrk with | marker bm => simp [C.Space.get, C.Space.put]
    · rw [set0_bang_m mrks1 hszmrk1 _]
      exact (by decide : (TRUE : Int32) ≠ 0)

private theorem tracems8_decomps_markers_eq (ep : C.ErrPtr) (lvl code p1 p2 p3 p4 p5 p6 p7 p8 : Int32) :
    ∀ h r h', C.run (tracems8 ep lvl code p1 p2 p3 p4 p5 p6 p7 p8) h = .ok (r, h') →
      h'.decomps = h.decomps ∧ h'.markers = h.markers := by
  intro h r h' hr; unfold tracems8 at hr
  cases h1 : C.run (Ptr.load ep) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1' =>
    rcases p1' with ⟨err, h1'⟩; have heq1 := ptr_load_heap_eq h1; subst heq1
    rw [C.run_bind, h1] at hr; dsimp only at hr
    cases h2 : C.run (Ptr.store ep { err with msgCode := code, msgParmI := #[p1, p2, p3, p4, p5, p6, p7, p8] }) h1' with
    | error e => rw [C.run_bind, h2] at hr; cases hr
    | ok p2' =>
      rcases p2' with ⟨_, h2'⟩; rw [C.run_bind, h2] at hr; dsimp only at hr
      have ⟨hd1, hm1⟩ := rmFrameStrong_decomps_markers_same ep _ h1' h2' h2
      have ⟨hd2, hm2⟩ := rmFrameStrong_emitMessage ep lvl h2' r h' hr
      exact ⟨hd2.trans hd1, hm2.trans hm1⟩

private theorem rmFrameStrong_get_sof {ctx : IoCtx} (isP isL isA : Int32) {h r h'}
    (hr : C.run (get_sof (.ref (.decomp ctx.bdc) 0) isP isL isA) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold get_sof at hr
  refine rmFrameStrong_bind_load _ (fun dc0 _ _ hr hl0 => ?_) h r h' hr
  have hdc0 := (dc_load_ref0_eq hl0).2
  refine rmFrameStrong_bind_load_here _ (fun _ _ hr _ => ?_) _ _ hr
  refine rmFrameStrong_bind_load_here _ (fun _ _ hr _ => ?_) _ _ hr
  split at hr
  · refine rmFrameStrong_bind (rmFrameStrong_errexit dc0.err JERR_SOF_DUPLICATE) ?_ _ _ _ hr
    intro _ _ _ _ h1; cases h1; exact rmFrameStrong_refl ctx _
  · refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
      rw [← hdc0 dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) (fun _ _ _ _ hr => ?_) _ _ hr
    refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
    refine rmFrameStrong_bind ?_ (fun _ _ _ _ hr => ?_) _ _ _ hr
    · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_master hst; exact rmFrameStrong_of_same hd hm
    · refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
      cases x with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
      refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun y _ _ _ hr => ?_) _ _ _ hr
      cases y with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
      refine rmFrameStrong_bind_load _ (fun dc1 _ _ hr hl1 => ?_) _ _ _ hr
      have hdc1 := (dc_load_ref0_eq hl1).2
      refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
        rw [← hdc1 dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) (fun _ _ _ _ hr => ?_) _ _ hr
      refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun z _ _ _ hr => ?_) _ _ _ hr
      cases z with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
      refine rmFrameStrong_bind_load _ (fun dc2 _ _ hr hl2 => ?_) _ _ _ hr
      have hdc2 := (dc_load_ref0_eq hl2).2
      refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
        rw [← hdc2 dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) (fun _ _ _ _ hr => ?_) _ _ hr
      refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun w _ _ _ hr => ?_) _ _ _ hr
      cases w with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
      refine rmFrameStrong_bind_load _ (fun dc3 _ _ hr hl3 => ?_) _ _ _ hr
      have hdc3 := (dc_load_ref0_eq hl3).2
      refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
        rw [← hdc3 dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) (fun _ _ _ _ hr => ?_) _ _ hr
      refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun u _ _ _ hr => ?_) _ _ _ hr
      cases u with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
      refine rmFrameStrong_bind_load _ (fun dc4 _ _ hr hl4 => ?_) _ _ _ hr
      have hdc4 := (dc_load_ref0_eq hl4).2
      refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
        rw [← hdc4 dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) (fun _ _ _ _ hr => ?_) _ _ hr
      refine rmFrameStrong_bind ?_ (fun _ _ _ _ hr => ?_) _ _ _ hr
      · intro h0 _ h1 htr; have ⟨hd, hm⟩ := tracems4_decomps_markers_eq _ _ _ _ _ _ _ h0 () h1 htr; exact rmFrameStrong_of_same hd hm
      · split at hr
        · refine rmFrameStrong_bind (rmFrameStrong_errexit _ _) ?_ _ _ _ hr
          intro _ _ _ _ h1; cases h1; exact rmFrameStrong_refl ctx _
        · split at hr
          · refine rmFrameStrong_bind (rmFrameStrong_errexit _ _) ?_ _ _ _ hr
            intro _ _ _ _ h1; cases h1; exact rmFrameStrong_refl ctx _
          · refine rmFrameStrong_bind_load _ (fun dc5 _ _ hr _ => ?_) _ _ _ hr
            dsimp (config := { zetaHave := true }) only at hr
            split at hr
            · unfold Mozjpeg.Jmemmgr.alloc_small_comps at hr
              refine rmFrameStrong_bind (rmFrameStrong_allocSmallCore _ _ _ _ ?_ _) (fun res _ _ _ hr => ?_) _ _ _ hr
              · intro h0 _ h1 ha
                simp only [C.run, C.allocComps] at ha
                cases hok : h0.allocOk h0.nalloc <;> simp only [hok, ↓reduceIte, Bool.false_eq_true] at ha <;>
                  (cases ha; exact rmFrameStrong_of_same rfl rfl)
              · cases res with
                | errExit _ => cases hr; exact rmFrameStrong_refl ctx _
                | ok cp =>
                  refine rmFrameStrong_bind_load _ (fun dc6 _ _ hr hl6 => ?_) _ _ _ hr
                  have hdc6 := (dc_load_ref0_eq hl6).2
                  refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
                    rw [← hdc6 dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩))
                    (fun _ _ _ _ hr => ?_) _ _ hr
                  refine rmFrameStrong_bind_load _ (fun dc7 _ _ hr _ => ?_) _ _ _ hr
                  refine rmFrameStrong_bind (rmFrameStrong_cwhile _ _ ?_ ?_ _) (fun st _ _ _ hr => ?_) _ _ _ hr
                  · intro _ _ _ _ _ hc; cases hc; exact rmFrameStrong_refl ctx _
                  · intro s h _ _ hb
                    cases ha : C.run (C.Ptr.add dc7.compInfo (Int.ofNat s.ci)) h with
                    | error _ => rw [C.run_bind, ha] at hb; cases hb
                    | ok qa =>
                      have haeq := ptr_add_comp_heap_eq ha; subst haeq
                      rw [C.run_bind, ha] at hb
                      refine rmFrameStrong_bind_load _ (fun comp0 _ _ hb _ => ?_) _ _ _ hb
                      refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
                      · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_comp hst; exact rmFrameStrong_of_same hd hm
                      · refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r1 _ _ _ hb => ?_) _ _ _ hb
                        cases r1 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
                        refine rmFrameStrong_bind_load _ (fun comp1 _ _ hb _ => ?_) _ _ _ hb
                        refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
                        · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_comp hst; exact rmFrameStrong_of_same hd hm
                        · refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r2 _ _ _ hb => ?_) _ _ _ hb
                          cases r2 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
                          refine rmFrameStrong_bind_load _ (fun comp2 _ _ hb _ => ?_) _ _ _ hb
                          refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
                          · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_comp hst; exact rmFrameStrong_of_same hd hm
                          · refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r3 _ _ _ hb => ?_) _ _ _ hb
                            cases r3 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
                            refine rmFrameStrong_bind_load _ (fun comp3 _ _ hb _ => ?_) _ _ _ hb
                            refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
                            · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_comp hst; exact rmFrameStrong_of_same hd hm
                            · refine rmFrameStrong_bind ?_ (fun _ _ _ _ hend => by cases hend; exact rmFrameStrong_refl ctx _) _ _ _ hb
                              intro h0 _ h1 htr
                              have ⟨hd, hm⟩ := tracems4_decomps_markers_eq _ _ _ _ _ _ _ h0 () h1 htr
                              exact rmFrameStrong_of_same hd hm
                  · split at hr
                    · cases hr; exact rmFrameStrong_refl ctx _
                    · refine rmFrameStrong_bind_load _ (fun dcEnd _ _ hr _ => ?_) _ _ _ hr
                      exact rmFrameStrong_bind_load_store_mrk dcEnd.marker (fun m => { m with sawSOF := TRUE }) (fun _ hm => hm) _
                        (fun _ _ _ hr => rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _)
                          (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr) _ _ _ hr
            · refine rmFrameStrong_bind_load _ (fun dc7 _ _ hr _ => ?_) _ _ _ hr
              refine rmFrameStrong_bind (rmFrameStrong_cwhile _ _ ?_ ?_ _) (fun st _ _ _ hr => ?_) _ _ _ hr
              · intro _ _ _ _ _ hc; cases hc; exact rmFrameStrong_refl ctx _
              · intro s h _ _ hb
                cases ha : C.run (C.Ptr.add dc7.compInfo (Int.ofNat s.ci)) h with
                | error _ => rw [C.run_bind, ha] at hb; cases hb
                | ok qa =>
                  have haeq := ptr_add_comp_heap_eq ha; subst haeq
                  rw [C.run_bind, ha] at hb
                  refine rmFrameStrong_bind_load _ (fun comp0 _ _ hb _ => ?_) _ _ _ hb
                  refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
                  · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_comp hst; exact rmFrameStrong_of_same hd hm
                  · refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r1 _ _ _ hb => ?_) _ _ _ hb
                    cases r1 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
                    refine rmFrameStrong_bind_load _ (fun comp1 _ _ hb _ => ?_) _ _ _ hb
                    refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
                    · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_comp hst; exact rmFrameStrong_of_same hd hm
                    · refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r2 _ _ _ hb => ?_) _ _ _ hb
                      cases r2 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
                      refine rmFrameStrong_bind_load _ (fun comp2 _ _ hb _ => ?_) _ _ _ hb
                      refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
                      · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_comp hst; exact rmFrameStrong_of_same hd hm
                      · refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r3 _ _ _ hb => ?_) _ _ _ hb
                        cases r3 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
                        refine rmFrameStrong_bind_load _ (fun comp3 _ _ hb _ => ?_) _ _ _ hb
                        refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
                        · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_comp hst; exact rmFrameStrong_of_same hd hm
                        · refine rmFrameStrong_bind ?_ (fun _ _ _ _ hend => by cases hend; exact rmFrameStrong_refl ctx _) _ _ _ hb
                          intro h0 _ h1 htr
                          have ⟨hd, hm⟩ := tracems4_decomps_markers_eq _ _ _ _ _ _ _ h0 () h1 htr
                          exact rmFrameStrong_of_same hd hm
              · split at hr
                · cases hr; exact rmFrameStrong_refl ctx _
                · refine rmFrameStrong_bind_load _ (fun dcEnd _ _ hr _ => ?_) _ _ _ hr
                  exact rmFrameStrong_bind_load_store_mrk dcEnd.marker (fun m => { m with sawSOF := TRUE }) (fun _ hm => hm) _
                    (fun _ _ _ hr => rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _)
                      (fun _ _ _ _ h1 => by cases h1; exact rmFrameStrong_refl ctx _) _ _ _ hr) _ _ _ hr

private theorem rmFrameStrong_get_dac {ctx : IoCtx} {h r h'}
    (hr : C.run (get_dac (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold get_dac at hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
  cases x with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
  refine rmFrameStrong_bind (rmFrameStrong_cwhile _ _ ?_ ?_ _) (fun st _ _ _ hr => ?_) _ _ _ hr
  · intro _ _ _ _ _ hc; cases hc; exact rmFrameStrong_refl ctx _
  · intro s h0 _ _ hb
    refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r1 _ _ _ hb => ?_) _ _ _ hb
    cases r1 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
    refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r2 _ _ _ hb => ?_) _ _ _ hb
    cases r2 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
    refine rmFrameStrong_bind_load _ (fun dcCur hLoad _ hb hl => ?_) _ _ _ hb
    have hdc := (dc_load_ref0_eq hl).2
    dsimp (config := { zetaHave := true }) only at hb
    cases htr : C.run (tracems2 dcCur.err 1 JTRC_DAC _ _) _ with
    | error e => rw [C.run_bind, htr] at hb; cases hb
    | ok p1 =>
      rcases p1 with ⟨_, h1⟩; rw [C.run_bind, htr] at hb
      have htrF := @rmFrameStrong_tracems2 ctx dcCur.err 1 JTRC_DAC _ _ _ () h1 htr
      refine rmFrameStrong_trans htrF ?_
      have hdEq : h1.decomps = hLoad.decomps := by
        unfold tracems2 at htr
        cases hlE : C.run (Ptr.load dcCur.err) _ with
        | error _ => rw [C.run_bind, hlE] at htr; cases htr
        | ok pe =>
          rcases pe with ⟨errE, hE0⟩; have heqe := ptr_load_heap_eq hlE; subst heqe
          rw [C.run_bind, hlE] at htr
          dsimp (config := { zetaHave := true }) only at htr
          cases hsE : C.run (Ptr.store dcCur.err _) _ with
          | error _ => rw [C.run_bind, hsE] at htr; cases htr
          | ok ps =>
            rcases ps with ⟨_, hsE'⟩; rw [C.run_bind, hsE] at htr
            have h1s := (rmFrameStrong_decomps_markers_same dcCur.err _ _ hsE' hsE).1
            have h2s := (rmFrameStrong_emitMessage dcCur.err 1 hsE' () h1 htr).1
            exact h2s.trans (h1s.trans (congrArg C.Heap.decomps (ptr_load_heap_eq hlE)))
      dsimp (config := { zetaHave := true }) only at hb
      split at hb
      · refine rmFrameStrong_bind (rmFrameStrong_errexit1 dcCur.err JERR_DAC_INDEX _) ?_ _ _ _ hb
        intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
      · split at hb
        · refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
            have hg0 : C.Space.get hLoad (C.DecompRef.decomp ctx.bdc) = some dcs := by
              simp only [C.Space.get] at hg ⊢; rw [hdEq] at hg; exact hg
            rw [← hdc dcs hg0 hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ hb
        · refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
            have hg0 : C.Space.get hLoad (C.DecompRef.decomp ctx.bdc) = some dcs := by
              simp only [C.Space.get] at hg ⊢; rw [hdEq] at hg; exact hg
            rw [← hdc dcs hg0 hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) (fun _ _ _ _ hb => by
              split at hb
              · refine rmFrameStrong_bind (rmFrameStrong_errexit1 _ JERR_DAC_VALUE _) ?_ _ _ _ hb
                intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
              · cases hb; exact rmFrameStrong_refl ctx _) _ _ hb
  · split at hr
    · cases hr; exact rmFrameStrong_refl ctx _
    · split at hr
      · refine rmFrameStrong_bind_load _ (fun dcE _ _ hr _ => ?_) _ _ _ hr
        refine rmFrameStrong_bind (rmFrameStrong_errexit dcE.err JERR_BAD_LENGTH) ?_ _ _ _ hr
        intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
      · refine rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _) ?_ _ _ _ hr
        intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_jpeg_alloc_huff_table {ctx : IoCtx} {h r h'}
    (hr : C.run (Mozjpeg.Jcomapi.jpeg_alloc_huff_table (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold Mozjpeg.Jcomapi.jpeg_alloc_huff_table Mozjpeg.Jmemmgr.alloc_small_huff at hr
  refine rmFrameStrong_bind (rmFrameStrong_allocSmallCore _ _ _ _ ?_ _) (fun res _ _ _ hr => ?_) h r h' hr
  · intro h0 _ h1 ha
    simp only [C.run, C.allocHuff] at ha
    cases hok : h0.allocOk h0.nalloc <;> simp only [hok, ↓reduceIte, Bool.false_eq_true] at ha <;>
      (cases ha; exact rmFrameStrong_of_same rfl rfl)
  · cases res with
    | errExit _ => cases hr; exact rmFrameStrong_refl ctx _
    | ok _ =>
      refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
      refine rmFrameStrong_bind (fun _ _ _ hst => by
        have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_huff hst
        exact rmFrameStrong_of_same hd hm) (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hr

private theorem rmFrameStrong_get_dht {ctx : IoCtx} {h r h'}
    (hr : C.run (get_dht (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold get_dht at hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
  cases x with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
  refine rmFrameStrong_bind (rmFrameStrong_cwhile _ _ ?_ ?_ _) (fun st _ _ _ hr => ?_) _ _ _ hr
  · intro _ _ _ _ _ hc; cases hc; exact rmFrameStrong_refl ctx _
  · intro s _ _ _ hb
    refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r1 _ _ _ hb => ?_) _ _ _ hb
    cases r1 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
    refine rmFrameStrong_bind_load _ (fun dcCur _ _ hb _ => ?_) _ _ _ hb
    refine rmFrameStrong_bind (rmFrameStrong_tracems1 dcCur.err 1 JTRC_DHT _) (fun _ _ _ _ hb => ?_) _ _ _ hb
    refine rmFrameStrong_bind (rmFrameStrong_forIn_range _ _ ?_ _) (fun _ _ _ _ hb => ?_) _ _ _ hb
    · intro _ _ _ _ _ hstep
      dsimp (config := { zetaHave := true }) only at hstep
      split at hstep
      · refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r2 _ _ _ hstep => ?_) _ _ _ hstep
        cases r2 <;> cases hstep <;> exact rmFrameStrong_refl ctx _
      · cases hstep; exact rmFrameStrong_refl ctx _
    · dsimp (config := { zetaHave := true }) only at hb
      split at hb
      · cases hb; exact rmFrameStrong_refl ctx _
      · refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
        · intro h0 _ h1 ht; have ⟨hd, hm⟩ := tracems8_decomps_markers_eq _ _ _ _ _ _ _ _ _ _ _ h0 () h1 ht; exact rmFrameStrong_of_same hd hm
        · refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
          · intro h0 _ h1 ht; have ⟨hd, hm⟩ := tracems8_decomps_markers_eq _ _ _ _ _ _ _ _ _ _ _ h0 () h1 ht; exact rmFrameStrong_of_same hd hm
          · split at hb
            · refine rmFrameStrong_bind (rmFrameStrong_errexit dcCur.err JERR_BAD_HUFF_TABLE) ?_ _ _ _ hb
              intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
            · refine rmFrameStrong_bind (rmFrameStrong_forIn_range _ _ ?_ _) (fun _ _ _ _ hb => ?_) _ _ _ hb
              · intro _ _ _ _ _ hstep
                split at hstep
                · exact rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r2 _ _ _ hstep => by
                    cases r2 <;> cases hstep <;> exact rmFrameStrong_refl ctx _) _ _ _ hstep
                · cases hstep; exact rmFrameStrong_refl ctx _
              · split at hb
                · cases hb; exact rmFrameStrong_refl ctx _
                · refine rmFrameStrong_bind_load _ (fun dcTbl _ _ hb _ => ?_) _ _ _ hb
                  split at hb <;> split at hb
                  all_goals first
                  | exact rmFrameStrong_bind (rmFrameStrong_errexit1 dcTbl.err JERR_DHT_INDEX _)
                      (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hb
                  | {
                      split at hb
                      · refine rmFrameStrong_bind (fun _ _ _ hh => rmFrameStrong_jpeg_alloc_huff_table hh) (fun res _ _ _ hb => ?_) _ _ _ hb
                        cases res with
                        | errExit _ => cases hb; exact rmFrameStrong_refl ctx _
                        | ok p =>
                          refine rmFrameStrong_bind_load _ (fun dcU _ _ hb hlU => ?_) _ _ _ hb
                          have hdcU := (dc_load_ref0_eq hlU).2
                          refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
                            rw [← hdcU dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩))
                            (fun _ _ _ _ hb => by
                              rw [pure_bind_m] at hb
                              refine rmFrameStrong_bind_load _ (fun _ _ _ hb _ => ?_) _ _ _ hb
                              refine rmFrameStrong_bind ?_ (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hb
                              intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_huff hst; exact rmFrameStrong_of_same hd hm)
                            _ _ hb
                      · rw [pure_bind_m] at hb
                        refine rmFrameStrong_bind_load _ (fun _ _ _ hb _ => ?_) _ _ _ hb
                        refine rmFrameStrong_bind ?_ (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hb
                        intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_huff hst; exact rmFrameStrong_of_same hd hm
                    }
  · split at hr
    · cases hr; exact rmFrameStrong_refl ctx _
    · split at hr
      · refine rmFrameStrong_bind_load _ (fun dcE _ _ hr _ => ?_) _ _ _ hr
        refine rmFrameStrong_bind (rmFrameStrong_errexit dcE.err JERR_BAD_LENGTH) ?_ _ _ _ hr
        intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
      · refine rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _) ?_ _ _ _ hr
        intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_get_dqt_tail {ctx : IoCtx} (cinfo : C.DecompPtr) (qPtr : C.QuantPtr)
    (prec : Int32) (nibA : C.BPtr) (bibA : UInt64) (s : DqtLoopState) :
    ∀ h r h', C.run (do
      let qTbl ← Ptr.load qPtr
      let __s ←
        forIn (List.range DCTSIZE2.toInt.toNat) (qTbl.quantval, nibA, bibA, false) fun i __s =>
          if (!__s.snd.snd.snd) = true then
            if (prec != 0) = true then do
              let res ← input2Bytes cinfo __s.snd.fst __s.snd.snd.fst
              match res with
              | none => pure (ForInStep.yield (__s.fst, __s.snd.fst, __s.snd.snd.fst, true))
              | some (tmp, n', bi') =>
                pure (ForInStep.yield (__s.fst.set! jpeg_natural_order[i]!.toInt.toNat (UInt16.ofNat tmp.toInt.toNat), n', bi', __s.snd.snd.snd))
            else do
              let res ← inputByte cinfo __s.snd.fst __s.snd.snd.fst
              match res with
              | none => pure (ForInStep.yield (__s.fst, __s.snd.fst, __s.snd.snd.fst, true))
              | some (tmp, n', bi') =>
                pure (ForInStep.yield (__s.fst.set! jpeg_natural_order[i]!.toInt.toNat (UInt16.ofNat tmp.toInt.toNat), n', bi', __s.snd.snd.snd))
          else pure (ForInStep.yield (__s.fst, __s.snd.fst, __s.snd.snd.fst, __s.snd.snd.snd))
      if __s.snd.snd.snd = true then
        pure { done := true, ret := JpegRes.ok false, length := s.length, nib := s.nib, bib := s.bib : DqtLoopState }
      else do
        Ptr.store qPtr { quantval := __s.fst, sentTable := qTbl.sentTable }
        let dcErr ← Ptr.load cinfo
        let err ← Ptr.load dcErr.err
        if err.traceLevel ≥ 2 then do
          forIn (List.range 8) PUnit.unit fun row _ => do
            tracems8 dcErr.err 2 JTRC_QUANTVALS
              (Int32.ofNat __s.fst[row * 8]!.toNat) (Int32.ofNat __s.fst[row * 8 + 1]!.toNat)
              (Int32.ofNat __s.fst[row * 8 + 2]!.toNat) (Int32.ofNat __s.fst[row * 8 + 3]!.toNat)
              (Int32.ofNat __s.fst[row * 8 + 4]!.toNat) (Int32.ofNat __s.fst[row * 8 + 5]!.toNat)
              (Int32.ofNat __s.fst[row * 8 + 6]!.toNat) (Int32.ofNat __s.fst[row * 8 + 7]!.toNat)
            pure (ForInStep.yield PUnit.unit)
          pure ({
            done := false
            ret := .ok true
            length := Int64.ofInt (s.length.toInt - (if (prec != 0) = true then DCTSIZE2.toInt * 2 + 1 else DCTSIZE2.toInt + 1))
            nib := __s.snd.fst
            bib := __s.snd.snd.fst
          } : DqtLoopState)
        else
          pure ({
            done := false
            ret := .ok true
            length := Int64.ofInt (s.length.toInt - (if (prec != 0) = true then DCTSIZE2.toInt * 2 + 1 else DCTSIZE2.toInt + 1))
            nib := __s.snd.fst
            bib := __s.snd.snd.fst
          } : DqtLoopState)) h = .ok (r, h') →
      RmFrameStrong ctx h h' := fun h r h' hb => by
  refine rmFrameStrong_bind_load _ (fun qTbl _ _ hb _ => ?_) h r h' hb
  refine rmFrameStrong_bind (rmFrameStrong_forIn_range _ _ ?_ _) (fun _ _ _ _ hb => ?_) _ _ _ hb
  · intro _ _ _ _ _ hstep
    split at hstep
    · split at hstep
      · exact rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun y _ _ _ he => by
          cases y <;> cases he <;> exact rmFrameStrong_refl ctx _) _ _ _ hstep
      · exact rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun y _ _ _ he => by
          cases y <;> cases he <;> exact rmFrameStrong_refl ctx _) _ _ _ hstep
    · cases hstep; exact rmFrameStrong_refl ctx _
  · split at hb
    · cases hb; exact rmFrameStrong_refl ctx _
    · refine rmFrameStrong_bind ?_ (fun _ _ _ _ hb => ?_) _ _ _ hb
      · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_quant hst; exact rmFrameStrong_of_same hd hm
      · refine rmFrameStrong_bind_load _ (fun dcErr _ _ hb _ => ?_) _ _ _ hb
        refine rmFrameStrong_bind_load _ (fun err _ _ hb _ => ?_) _ _ _ hb
        split at hb
        · refine rmFrameStrong_bind (rmFrameStrong_forIn_range _ _ ?_ _) (fun _ _ _ _ he => by
            cases he; exact rmFrameStrong_refl ctx _) _ _ _ hb
          intro _ _ _ _ _ hstep
          refine rmFrameStrong_bind ?_ (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hstep
          intro h0 _ h1 ht
          have ⟨hd, hm⟩ := tracems8_decomps_markers_eq _ _ _ _ _ _ _ _ _ _ _ h0 () h1 ht
          exact rmFrameStrong_of_same hd hm
        · cases hb; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_jpeg_alloc_quant_table {ctx : IoCtx} {h r h'}
    (hr : C.run (Mozjpeg.Jcomapi.jpeg_alloc_quant_table (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold Mozjpeg.Jcomapi.jpeg_alloc_quant_table Mozjpeg.Jmemmgr.alloc_small_quant at hr
  refine rmFrameStrong_bind (rmFrameStrong_allocSmallCore _ _ _ _ ?_ _) (fun res _ _ _ hr => ?_) h r h' hr
  · intro h0 _ h1 ha
    simp only [C.run, C.allocQuant] at ha
    cases hok : h0.allocOk h0.nalloc <;> simp only [hok, ↓reduceIte, Bool.false_eq_true] at ha <;>
      (cases ha; exact rmFrameStrong_of_same rfl rfl)
  · cases res with
    | errExit _ => cases hr; exact rmFrameStrong_refl ctx _
    | ok _ =>
      refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
      refine rmFrameStrong_bind (fun _ _ _ hst => by
        have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_quant hst
        exact rmFrameStrong_of_same hd hm) (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hr

private theorem rmFrameStrong_get_dqt {ctx : IoCtx} {h r h'}
    (hr : C.run (get_dqt (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold get_dqt at hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
  cases x with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
  refine rmFrameStrong_bind (rmFrameStrong_cwhile _ _ ?_ ?_ _) (fun st _ _ _ hr => ?_) _ _ _ hr
  · intro _ _ _ _ _ hc; cases hc; exact rmFrameStrong_refl ctx _
  · intro s _ _ _ hb
    refine rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r1 _ _ _ hb => ?_) _ _ _ hb
    cases r1 with | none => cases hb; exact rmFrameStrong_refl ctx _ | some _ => ?_
    refine rmFrameStrong_bind_load _ (fun dcCur _ _ hb _ => ?_) _ _ _ hb
    refine rmFrameStrong_bind (rmFrameStrong_tracems2 dcCur.err 1 JTRC_DQT _ _) (fun _ _ _ _ hb => ?_) _ _ _ hb
    split at hb
    · refine rmFrameStrong_bind (rmFrameStrong_errexit1 dcCur.err JERR_DQT_INDEX _) ?_ _ _ _ hb
      intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
    · dsimp (config := { zetaHave := true }) only at hb
      split at hb
      · refine rmFrameStrong_bind (fun _ _ _ hq => rmFrameStrong_jpeg_alloc_quant_table hq) (fun res _ _ _ hb => ?_) _ _ _ hb
        cases res with
        | errExit _ => cases hb; exact rmFrameStrong_refl ctx _
        | ok p =>
          refine rmFrameStrong_bind_load _ (fun dcU _ _ hb hlU => ?_) _ _ _ hb
          have hdcU := (dc_load_ref0_eq hlU).2
          exact rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
            rw [← hdcU dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩))
            (fun _ _ _ _ hb => by
              rw [pure_bind_m] at hb
              exact rmFrameStrong_get_dqt_tail _ p _ _ _ s _ _ _ hb) _ _ hb
      · rw [pure_bind_m] at hb; exact rmFrameStrong_get_dqt_tail _ _ _ _ _ s _ _ _ hb
  · split at hr
    · cases hr; exact rmFrameStrong_refl ctx _
    · split at hr
      · refine rmFrameStrong_bind_load _ (fun dcE _ _ hr _ => ?_) _ _ _ hr
        refine rmFrameStrong_bind (rmFrameStrong_errexit dcE.err JERR_BAD_LENGTH) ?_ _ _ _ hr
        intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
      · refine rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _) ?_ _ _ _ hr
        intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_get_dri {ctx : IoCtx} {h r h'}
    (hr : C.run (get_dri (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold get_dri at hr
  refine rmFrameStrong_bind_load _ (fun dc0 _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
  cases x with | none => cases hr; exact rmFrameStrong_refl ctx _ | some q => ?_
  rcases q with ⟨len, nib1, bib1⟩; dsimp only at hr
  split at hr
  · refine rmFrameStrong_bind (rmFrameStrong_errexit dc0.err JERR_BAD_LENGTH) ?_ _ _ _ hr
    intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
  · refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun y _ _ _ hr => ?_) _ _ _ hr
    cases y with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
    refine rmFrameStrong_bind (rmFrameStrong_tracems1 dc0.err 1 JTRC_DRI _) (fun _ _ _ _ hr => ?_) _ _ _ hr
    refine rmFrameStrong_bind_load _ (fun dc1 _ _ hr hl1 => ?_) _ _ _ hr
    have hdc1 := (dc_load_ref0_eq hl1).2
    refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
      rw [← hdc1 dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩))
      (fun _ _ _ _ hr => rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _)
        (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hr) _ _ hr

private theorem rmFrameStrong_skip_variable {ctx : IoCtx} {h r h'}
    (hr : C.run (skip_variable (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold skip_variable at hr
  refine rmFrameStrong_bind_load _ (fun dc0 _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
  cases x with | none => cases hr; exact rmFrameStrong_refl ctx _ | some _ => ?_
  refine rmFrameStrong_bind (rmFrameStrong_tracems2 dc0.err 1 JTRC_MISC_MARKER _ _) (fun _ _ _ _ hr => ?_) _ _ _ hr
  refine rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _) (fun _ _ _ _ hr => ?_) _ _ _ hr
  dsimp (config := { zetaHave := true }) only at hr
  split at hr
  · refine rmFrameStrong_bind (rmFrameStrong_skipInputDataDispatch _ _) ?_ _ _ _ hr
    intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _
  · cases hr; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_sync_and_opt_skip {ctx : IoCtx} (nib : C.BPtr) (bib : UInt64) (len : Int64) :
    ∀ h r h', C.run (do
      inputSync (.ref (.decomp ctx.bdc) 0) nib bib
      if len > 0 then
        skipInputDataDispatch (.ref (.decomp ctx.bdc) 0) len
      return (JpegRes.ok true)) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  refine rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _) (fun _ _ _ _ hr => ?_) h r h' hr
  by_cases hlen : len > 0
  · rw [ite_eq_left hlen] at hr
    exact rmFrameStrong_bind (rmFrameStrong_skipInputDataDispatch _ _)
      (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hr
  · rw [ite_eq_right hlen] at hr; cases hr; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_get_interesting_appn {ctx : IoCtx} {h r h'}
    (hr : C.run (get_interesting_appn (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold get_interesting_appn at hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
  cases x with | none => cases hr; exact rmFrameStrong_refl ctx _ | some q => ?_
  rcases q with ⟨lenRaw, nib1, bib1⟩; dsimp only at hr
  refine rmFrameStrong_bind (rmFrameStrong_forIn_range _ _ ?_ _) (fun _ _ _ _ hr => ?_) _ _ _ hr
  · intro _ _ _ _ _ hstep
    split at hstep
    · exact rmFrameStrong_bind (rmFrameStrong_inputByte _ _ _) (fun r2 _ _ _ hstep => by
        cases r2 <;> cases hstep <;> exact rmFrameStrong_refl ctx _) _ _ _ hstep
    · cases hstep; exact rmFrameStrong_refl ctx _
  · split at hr
    · cases hr; exact rmFrameStrong_refl ctx _
    · refine rmFrameStrong_bind_load _ (fun dc1 _ _ hr _ => ?_) _ _ _ hr
      split at hr
      · refine rmFrameStrong_bind (rmFrameStrong_examine_app0 _ _ _) (fun _ _ _ _ hr =>
          rmFrameStrong_sync_and_opt_skip _ _ _ _ _ _ hr) _ _ _ hr
      · split at hr
        · refine rmFrameStrong_bind (rmFrameStrong_examine_app14 _ _ _) (fun _ _ _ _ hr =>
            rmFrameStrong_sync_and_opt_skip _ _ _ _ _ _ hr) _ _ _ hr
        · refine rmFrameStrong_bind (rmFrameStrong_errexit1 dc1.err JERR_UNKNOWN_MARKER _) ?_ _ _ _ hr
          intro _ _ _ _ he; cases he; exact rmFrameStrong_refl ctx _

private theorem rmFrameStrong_save_marker_end {ctx : IoCtx}
    (dataArr : Array UInt8) (dataLength : UInt32) (remLength : Int64) (nib : C.BPtr) (bib : UInt64) :
    ∀ h r h', C.run (do
      let cinfo : C.DecompPtr := .ref (.decomp ctx.bdc) 0
      let dcA ← Ptr.load cinfo
      let mrkA ← Ptr.load dcA.marker
      Ptr.store dcA.marker { mrkA with curMarker := .null }
      if dcA.unreadMarker == M_APP0 then
        examine_app0 cinfo dataArr dataLength remLength
      else if dcA.unreadMarker == M_APP14 then
        examine_app14 cinfo dataArr dataLength remLength
      else
        tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
          (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt))
      inputSync cinfo nib bib
      if remLength > 0 then
        skipInputDataDispatch cinfo remLength
      return (JpegRes.ok true)) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  refine rmFrameStrong_bind_load _ (fun dcA _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load_store_mrk dcA.marker (fun m => { m with curMarker := .null }) (fun _ hm => hm) _
    (fun _ _ _ hr => ?_) _ _ _ hr
  dsimp (config := { zetaHave := true }) only at hr
  have hsync : ∀ h r h', C.run (do
      inputSync (.ref (.decomp ctx.bdc) 0) nib bib
      if remLength > 0 then
        skipInputDataDispatch (.ref (.decomp ctx.bdc) 0) remLength
      return (JpegRes.ok true)) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr =>
    rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _) (fun _ _ _ _ hr => by
      dsimp (config := { zetaHave := true }) only at hr
      split at hr
      · exact rmFrameStrong_bind (rmFrameStrong_skipInputDataDispatch _ _)
          (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hr
      · cases hr; exact rmFrameStrong_refl ctx _) h r h' hr
  by_cases ha0 : (dcA.unreadMarker == M_APP0) = true
  · simp only [ha0, ↓reduceIte] at hr
    exact rmFrameStrong_bind (rmFrameStrong_examine_app0 _ _ _) (fun _ _ _ _ hr => hsync _ _ _ hr) _ _ _ hr
  · have ha0f : (dcA.unreadMarker == M_APP0) = false := by cases hc : (dcA.unreadMarker == M_APP0) <;> simp_all
    simp only [ha0f, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases ha14 : (dcA.unreadMarker == M_APP14) = true
    · simp only [ha14, ↓reduceIte] at hr
      exact rmFrameStrong_bind (rmFrameStrong_examine_app14 _ _ _) (fun _ _ _ _ hr => hsync _ _ _ hr) _ _ _ hr
    · have ha14f : (dcA.unreadMarker == M_APP14) = false := by cases hc : (dcA.unreadMarker == M_APP14) <;> simp_all
      simp only [ha14f, Bool.false_eq_true, ↓reduceIte] at hr
      exact rmFrameStrong_bind (rmFrameStrong_tracems2 _ 1 JTRC_MISC_MARKER _ _) (fun _ _ _ _ hr => hsync _ _ _ hr) _ _ _ hr

private theorem rmFrameStrong_save_marker_mid {ctx : IoCtx}
    (sm : C.JpegSavedMarker) (dataLength : UInt32) (nib : C.BPtr) (bib : UInt64) :
    ∀ h r h', C.run (do
      let cinfo : C.DecompPtr := .ref (.decomp ctx.bdc) 0
      let remLength : Int64 := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat dataLength.toNat)
      let mut dataArr : Array UInt8 := #[]
      for k in List.range dataLength.toNat do
        let bp ← Ptr.add sm.data (Int.ofNat k)
        let v ← Ptr.load bp
        dataArr := dataArr.push v
      let dcA ← Ptr.load cinfo
      let mrkA ← Ptr.load dcA.marker
      Ptr.store dcA.marker { mrkA with curMarker := .null }
      if dcA.unreadMarker == M_APP0 then
        examine_app0 cinfo dataArr dataLength remLength
      else if dcA.unreadMarker == M_APP14 then
        examine_app14 cinfo dataArr dataLength remLength
      else
        tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
          (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt))
      inputSync cinfo nib bib
      if remLength > 0 then
        skipInputDataDispatch cinfo remLength
      return (JpegRes.ok true)) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  refine rmFrameStrong_bind (rmFrameStrong_forIn_range _ _ ?_ _)
    (fun dataArr _ _ _ hr => rmFrameStrong_save_marker_end dataArr _ _ _ _ _ _ _ hr) h r h' hr
  intro _ _ _ _ _ hstep
  cases ha : C.run (C.Ptr.add sm.data _) _ with
  | error _ => rw [C.run_bind, ha] at hstep; cases hstep
  | ok qa =>
    rcases qa with ⟨_, _⟩
    have heq := ptr_add_bptr_heap_eq ha; subst heq
    rw [C.run_bind, ha] at hstep; dsimp only at hstep
    exact rmFrameStrong_bind_load _ (fun _ _ _ he _ => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hstep

private theorem rmFrameStrong_save_marker_tail {ctx : IoCtx}
    (curMarker : C.SavedMarkerPtr) (bytesRead dataLength : UInt32) (dataPtr curNib : C.BPtr) (curBib : UInt64) :
    ∀ h r h', C.run (do
      let cinfo : C.DecompPtr := .ref (.decomp ctx.bdc) 0
      let st ← cwhile
        (fun (s : SaveMarkerState) => pure (!s.done && s.bytesRead < dataLength, s))
        (fun (s : SaveMarkerState) => do
          inputSync cinfo s.nib s.bib
          let dcS ← Ptr.load cinfo
          let mrkS ← Ptr.load dcS.marker
          Ptr.store dcS.marker { mrkS with bytesRead := s.bytesRead }
          match (← makeByteAvail cinfo s.nib s.bib) with
          | none => return { s with done := true, susp := true }
          | some (n1, bi1) =>
            let cs ← cwhile
              (fun (c : SaveMarkerCopyState) => pure (c.br < dataLength && c.bb > 0, c))
              (fun (c : SaveMarkerCopyState) => do
                let b ← Ptr.load c.nb
                Ptr.store c.dp b
                let dp' ← Ptr.add c.dp 1
                let nb' ← Ptr.add c.nb 1
                return { br := c.br + 1, nb := nb', bb := c.bb - 1, dp := dp' })
              { br := s.bytesRead, nb := n1, bb := bi1, dp := s.dp }
            return { done := false, susp := false, bytesRead := cs.br, nib := cs.nb, bib := cs.bb, dp := cs.dp })
        { done := false, susp := false, bytesRead := bytesRead, nib := curNib, bib := curBib, dp := dataPtr }
      if st.susp then
        return (JpegRes.ok false)
      let mut remLength : Int64 := 0
      let mut dataArr : Array UInt8 := #[]
      if curMarker != .null then
        let sm ← Ptr.load curMarker
        let dcCur ← Ptr.load cinfo
        let mst ← Ptr.load dcCur.master
        if dcCur.markerList == .null || mst.markerListEnd == .null then
          Ptr.store cinfo { dcCur with markerList := curMarker }
          Ptr.store dcCur.master { mst with markerListEnd := curMarker }
        else
          let tail ← Ptr.load mst.markerListEnd
          Ptr.store mst.markerListEnd { tail with next := curMarker }
          Ptr.store dcCur.master { mst with markerListEnd := curMarker }
        remLength := Int64.ofInt (Int.ofNat sm.originalLength.toNat - Int.ofNat dataLength.toNat)
        for k in List.range dataLength.toNat do
          let bp ← Ptr.add sm.data (Int.ofNat k)
          let v ← Ptr.load bp
          dataArr := dataArr.push v
      let dcA ← Ptr.load cinfo
      let mrkA ← Ptr.load dcA.marker
      Ptr.store dcA.marker { mrkA with curMarker := .null }
      if dcA.unreadMarker == M_APP0 then
        examine_app0 cinfo dataArr dataLength remLength
      else if dcA.unreadMarker == M_APP14 then
        examine_app14 cinfo dataArr dataLength remLength
      else
        tracems2 dcA.err 1 JTRC_MISC_MARKER dcA.unreadMarker
          (Int32.ofInt (Int.ofNat dataLength.toNat + remLength.toInt))
      inputSync cinfo st.nib st.bib
      if remLength > 0 then
        skipInputDataDispatch cinfo remLength
      return (JpegRes.ok true)) h = .ok (r, h') → RmFrameStrong ctx h h' := fun h r h' hr => by
  dsimp only at hr
  refine rmFrameStrong_bind (rmFrameStrong_cwhile _ _ ?_ ?_ _) (fun st _ _ _ hr => ?_) h r h' hr
  · intro _ _ _ _ _ hc; cases hc; exact rmFrameStrong_refl ctx _
  · intro s _ _ _ hb
    refine rmFrameStrong_bind (rmFrameStrong_inputSync _ _ _) (fun _ _ _ _ hb => ?_) _ _ _ hb
    refine rmFrameStrong_bind_load _ (fun dcS _ _ hb _ => ?_) _ _ _ hb
    exact rmFrameStrong_bind_load_store_mrk dcS.marker (fun m => { m with bytesRead := s.bytesRead })
      (fun _ hm => hm) _ (fun _ _ _ hb => by
        refine rmFrameStrong_bind (rmFrameStrong_makeByteAvail _ _ _) (fun ma _ _ _ hb => ?_) _ _ _ hb
        cases ma with
        | none => cases hb; exact rmFrameStrong_refl ctx _
        | some _ =>
          refine rmFrameStrong_bind (rmFrameStrong_cwhile _ _ ?_ ?_ _)
            (fun _ _ _ _ he => by cases he; exact rmFrameStrong_refl ctx _) _ _ _ hb
          · intro _ _ _ _ _ hc; cases hc; exact rmFrameStrong_refl ctx _
          · intro c _ _ _ hcb
            refine rmFrameStrong_bind_load _ (fun _ _ _ hcb _ => ?_) _ _ _ hcb
            refine rmFrameStrong_bind ?_ (fun _ _ _ _ hcb => ?_) _ _ _ hcb
            · intro _ _ _ hst; have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_byte hst; exact rmFrameStrong_of_same hd hm
            · cases h1 : C.run (C.Ptr.add c.dp 1) _ with
              | error _ => rw [C.run_bind, h1] at hcb; cases hcb
              | ok q1 =>
                rcases q1 with ⟨_, _⟩
                have heq1 := ptr_add_bptr_heap_eq h1; subst heq1
                rw [C.run_bind, h1] at hcb; dsimp only at hcb
                cases h2 : C.run (C.Ptr.add c.nb 1) _ with
                | error _ => rw [C.run_bind, h2] at hcb; cases hcb
                | ok q2 =>
                  rcases q2 with ⟨_, _⟩
                  have heq2 := ptr_add_bptr_heap_eq h2; subst heq2
                  rw [C.run_bind, h2] at hcb; cases hcb; exact rmFrameStrong_refl ctx _) _ _ _ hb
  · split at hr
    · cases hr; exact rmFrameStrong_refl ctx _
    · split at hr
      · refine rmFrameStrong_bind_load _ (fun sm _ _ hr _ => ?_) _ _ _ hr
        refine rmFrameStrong_bind_load _ (fun dcCur _ _ hr hlC => ?_) _ _ _ hr
        have hdcC := (dc_load_ref0_eq hlC).2
        refine rmFrameStrong_bind_load_here _ (fun mst _ hr _ => ?_) _ _ hr
        split at hr
        · refine rmFrameStrong_bind_here (fun _ _ hst => rmFrameStrong_store_dc _ _ hst (fun dcs _ hg hsz => by
            rw [← hdcC dcs hg hsz]; exact ⟨rfl, rfl, rfl, rfl⟩)) ?_ _ _ hr
          intro _ _ _ _ hr
          exact rmFrameStrong_bind (fun _ _ _ hst => by
            have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_master hst; exact rmFrameStrong_of_same hd hm)
            (fun _ _ _ _ hr => rmFrameStrong_save_marker_mid sm _ _ _ _ _ _ hr) _ _ _ hr
        · refine rmFrameStrong_bind_load _ (fun tail _ _ hr _ => ?_) _ _ _ hr
          refine rmFrameStrong_bind (fun _ _ _ hst => by
            have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_sm hst; exact rmFrameStrong_of_same hd hm)
            (fun _ _ _ _ hr => rmFrameStrong_bind (fun _ _ _ hst => by
              have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_master hst; exact rmFrameStrong_of_same hd hm)
              (fun _ _ _ _ hr => rmFrameStrong_save_marker_mid sm _ _ _ _ _ _ hr) _ _ _ hr) _ _ _ hr
      · exact rmFrameStrong_save_marker_end _ _ _ _ _ _ _ _ hr

private theorem rmFrameStrong_save_marker {ctx : IoCtx} {h r h'}
    (hr : C.run (save_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold save_marker at hr
  refine rmFrameStrong_bind_load _ (fun dc0 _ _ hr _ => ?_) h r h' hr
  refine rmFrameStrong_bind_load _ (fun mrk0 _ _ hr _ => ?_) _ _ _ hr
  refine rmFrameStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  dsimp (config := { zetaHave := true }) only at hr
  by_cases hnil : (mrk0.curMarker == .null) = true
  · rw [ite_eq_left hnil] at hr
    refine rmFrameStrong_bind (rmFrameStrong_input2Bytes _ _ _) (fun x _ _ _ hr => ?_) _ _ _ hr
    cases x with | none => cases hr; exact rmFrameStrong_refl ctx _ | some q => ?_
    rcases q with ⟨lenRaw, nib1, bib1⟩; dsimp only at hr
    by_cases hlen : Int64.ofInt (lenRaw.toInt - 2) ≥ 0
    · rw [ite_eq_left hlen] at hr
      by_cases hlim : UInt32.ofNat (Int64.ofInt (lenRaw.toInt - 2)).toInt.toNat <
          if (dc0.unreadMarker == M_COM) = true then mrk0.lengthLimitCOM
          else if (dc0.unreadMarker - M_APP0).toInt.toNat < 16 then mrk0.lengthLimitAPPn[(dc0.unreadMarker - M_APP0).toInt.toNat]! else 0
      · rw [ite_eq_left hlim] at hr
        refine rmFrameStrong_bind (rmFrameStrong_alloc_large_saved_marker _ _ _) (fun res _ _ _ hr => ?_) _ _ _ hr
        cases res with
        | errExit _ => cases hr; exact rmFrameStrong_refl ctx _
        | ok _ =>
          refine rmFrameStrong_bind (fun _ _ _ hst => by
            have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_sm hst; exact rmFrameStrong_of_same hd hm)
            (fun _ _ _ _ hr => rmFrameStrong_bind_load _ (fun dc1 _ _ hr _ =>
              rmFrameStrong_bind_load_store_mrk dc1.marker (fun m => { m with curMarker := _, bytesRead := 0 })
                (fun _ hm => hm) _
                (fun _ _ _ hr => rmFrameStrong_save_marker_tail _ _ _ _ _ _ _ _ _ hr) _ _ _ hr) _ _ _ hr) _ _ _ hr
      · rw [ite_eq_right hlim] at hr
        refine rmFrameStrong_bind (rmFrameStrong_alloc_large_saved_marker _ _ _) (fun res _ _ _ hr => ?_) _ _ _ hr
        cases res with
        | errExit _ => cases hr; exact rmFrameStrong_refl ctx _
        | ok _ =>
          refine rmFrameStrong_bind (fun _ _ _ hst => by
            have ⟨hd, hm⟩ := rmFrameStrong_decomps_markers_eq_of_store_sm hst; exact rmFrameStrong_of_same hd hm)
            (fun _ _ _ _ hr => rmFrameStrong_bind_load _ (fun dc1 _ _ hr _ =>
              rmFrameStrong_bind_load_store_mrk dc1.marker (fun m => { m with curMarker := _, bytesRead := 0 })
                (fun _ hm => hm) _
                (fun _ _ _ hr => rmFrameStrong_save_marker_tail _ _ _ _ _ _ _ _ _ hr) _ _ _ hr) _ _ _ hr) _ _ _ hr
    · rw [ite_eq_right hlen] at hr
      exact rmFrameStrong_save_marker_tail _ _ _ _ _ _ _ _ _ hr
  · rw [ite_eq_right hnil] at hr
    refine rmFrameStrong_bind_load _ (fun sm _ _ hr _ => ?_) _ _ _ hr
    cases ha : C.run (C.Ptr.add sm.data (Int.ofNat mrk0.bytesRead.toNat)) _ with
    | error _ => rw [C.run_bind, ha] at hr; cases hr
    | ok qa =>
      rcases qa with ⟨_, _⟩
      have heq := ptr_add_bptr_heap_eq ha; subst heq
      rw [C.run_bind, ha] at hr
      exact rmFrameStrong_save_marker_tail _ _ _ _ _ _ _ _ _ hr

private theorem rmFrameStrong_callMarkerParser {ctx : IoCtx} (fn : FnPtr) {h r h'}
    (hr : C.run (callMarkerParser (.ref (.decomp ctx.bdc) 0) fn) h = .ok (r, h')) :
    RmFrameStrong ctx h h' := by
  unfold callMarkerParser at hr
  split at hr
  · exact rmFrameStrong_skip_variable hr
  · split at hr
    · exact rmFrameStrong_save_marker hr
    · split at hr
      · exact rmFrameStrong_get_interesting_appn hr
      · unfold C.ub at hr; cases hr

theorem next_marker_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw0 : CompSawZero ctx h)
    (hhead : ∀ errs0 srcs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
      warnPotVal errs0 srcs0 + 2 ^ 23 < 2 ^ 63)
    (hscan : ∀ dcs srcs,
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
      scanLimit dcs[0]! srcs[0]! < 2 ^ 31) :
    ∃ ret h',
      C.run (next_marker (.ref (.decomp ctx.bdc) 0)) h = .ok (ret, h') ∧
      (ret = FALSE ∨
       ret = TRUE ∧ ∃ dcs' srcs' srcs0,
         C.Space.get h ctx.rs = some srcs0 ∧ 0 < srcs0.size ∧
         C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' ∧ 0 < dcs'.size ∧
         C.Space.get h' ctx.rs = some srcs' ∧ 0 < srcs'.size ∧
         ParserEnv ctx h' ∧
         CompSawZero ctx h' ∧
         RmFrame ctx h h' ∧
         DecompHeaderStable ctx h h' ∧
         ((dcs'[0]!.unreadMarker = M_EOI ∧
           ∀ errs' srcs'', C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
             C.Space.get h' ctx.rs = some srcs'' → 0 < srcs''.size →
             ∀ errs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
             errs'[0]!.numWarnings.toInt ≤ errs0[0]!.numWarnings.toInt + 2 ^ 22 + 2 ^ 17 + 2) ∨
          (dcs'[0]!.unreadMarker ≠ M_EOI ∧
           isConstEofPtr srcs0[0]!.nextInputByte = false ∧
           srcRank srcs'[0]! < srcRank srcs0[0]! ∧
           ∀ errs' srcs'', C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
             C.Space.get h' ctx.rs = some srcs'' → 0 < srcs''.size →
             ∀ errs0, C.Space.get h ctx.rerr = some errs0 → 0 < errs0.size →
             srcPotential errs'[0]! srcs''[0]! ≤ warnPotVal errs0 srcs0 + 2 ^ 17))) := by
  obtain ⟨errs0, hgerr0, hszerr0, _⟩ := parserEnv_get_err hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
  obtain ⟨srcs0P, hgsrc0P, _, _, _, _, _, _, hbib0Lt, _⟩ := parserEnv_get_src hp
  have hbib0Lt' : srcs0[0]!.bytesInBuffer.toNat < 2 ^ 20 := by
    rw [Option.some.inj (hgsrc0.symm.trans hgsrc0P)]; exact hbib0Lt
  obtain ⟨dcs0, hgdc0, hszdc0, kerr0, _, _, _, kmrk0, ksrc0⟩ := parserEnv_get_dc hp
  have hs : IoState ctx h (srcPotential errs0[0]! srcs0[0]!) := by
    refine ioState_of_parserEnv hp (fun dcs mrks hgd hszd hgm hszm => ?_)
      (fun errs srcs hge _ hgs _ => ?_) hscan
    · by_cases hsz : mrks[0]!.sawSOF = 0
      · exact Or.inl ⟨hsaw0 mrks dcs hgm hszm hgd hszd hsz, hsz⟩
      · right; obtain ⟨dcsP, hgdP, _, hcn0, _, _⟩ := parserEnv_get_compLive hp
        have hdEq := Option.some.inj (hgd.symm.trans hgdP)
        rw [← hdEq] at hcn0
        exact ⟨hcn0 mrks hgm hszm hsz, hsz⟩
    · rw [Option.some.inj (hge.symm.trans hgerr0), Option.some.inj (hgs.symm.trans hgsrc0)]
      exact ⟨Int.le_refl _, by
        unfold srcPotential warnPotVal at *
        have hhd := hhead errs0 srcs0 hgerr0 hszerr0 hgsrc0 hszsrc0
        split at hhd <;> split <;> omega⟩
  have hbd : srcPotential errs0[0]! srcs0[0]! + 2 + 2 ^ 17 < 2 ^ 63 := by
    have hhd := hhead errs0 srcs0 hgerr0 hszerr0 hgsrc0 hszsrc0
    unfold srcPotential warnPotVal at *
    split at hhd <;> split <;> omega
  obtain ⟨ret, h', hrun, hret⟩ := next_marker_io hs hbd
  have hhas : HasDcPtrs ctx h := ⟨dcs0, hgdc0, hszdc0, ksrc0, kerr0, kmrk0⟩
  have hf := next_marker_frame hhas hrun
  refine ⟨ret, h', hrun, ?_⟩
  rcases hret with rfl | ⟨rfl, dcs', srcs', srcs0', hgsrc0', hszsrc0', hgdc', hszdc', hgsrc', hszsrc', hcase⟩
  · left; rfl
  · have hrm : RmFrame ctx h h' := by
      rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, dcbF, _, _, mrF, _, _⟩
      refine ⟨fun d0 d1 h0 s0 h1 _ => ?_, fun m0 m1 h0 s0 h1 _ hne => ?_⟩
      · obtain ⟨d1', h1', _, hdEq⟩ := dcbF ctx.bdc d0 h0 s0 rfl
        rw [Option.some.inj (h1.symm.trans h1')]
        have hd := congrArg C.JpegDecompressStruct.inputScanNumber hdEq
        have he := congrArg C.JpegDecompressStruct.entropyStartPass hdEq
        have hc := congrArg C.JpegDecompressStruct.coefStartInputPass hdEq
        have hd2 := congrArg C.JpegDecompressStruct.coefConsumeData hdEq
        exact ⟨hd, he, hc, hd2⟩
      · obtain ⟨m1', h1', _, hmEq⟩ := mrF m0 h0 s0
        rw [Option.some.inj (h1.symm.trans h1')]
        have hs := congrArg C.JpegMarkerReader.sawSOI hmEq
        dsimp only at hs; rw [hs]; exact hne
    have hst : DecompHeaderStable ctx h h' := by
      rcases hf with ⟨_, _, _, _, _, _, hcp, _, _, _, _, _, _, dcbF, _, _, mrF, _, _⟩
      refine ⟨fun d0 d1 h0 s0 h1 _ => ?_, fun m0 m1 h0 s0 h1 _ => ?_, ?_⟩
      · obtain ⟨d1', h1', _, hdEq⟩ := dcbF ctx.bdc d0 h0 s0 rfl
        rw [Option.some.inj (h1.symm.trans h1')]
        have h1e := congrArg C.JpegDecompressStruct.compInfo hdEq
        have h2e := congrArg C.JpegDecompressStruct.numComponents hdEq
        have h3e := congrArg C.JpegDecompressStruct.imageWidth hdEq
        have h4e := congrArg C.JpegDecompressStruct.imageHeight hdEq
        have h5e := congrArg C.JpegDecompressStruct.maxHSampFactor hdEq
        have h6e := congrArg C.JpegDecompressStruct.maxVSampFactor hdEq
        have h7e := congrArg C.JpegDecompressStruct.entropyStartPass hdEq
        have h8e := congrArg C.JpegDecompressStruct.coefStartInputPass hdEq
        have h9e := congrArg C.JpegDecompressStruct.coefConsumeData hdEq
        exact ⟨h1e, h2e, h3e, h4e, h5e, h6e, h7e, h8e, h9e⟩
      · obtain ⟨m1', h1', _, hmEq⟩ := mrF m0 h0 s0
        rw [Option.some.inj (h1.symm.trans h1')]
        simpa using congrArg C.JpegMarkerReader.sawSOF hmEq
      · intro rcp cs i hg hi; cases rcp; simp only [C.Space.get] at hg ⊢; rw [hcp]; exact ⟨cs, hg, hi, rfl, rfl, rfl⟩
    right
    rcases hcase with ⟨hEoi, hsN⟩ | ⟨hNe, hnf0, hrank, hsN⟩
    · have hp' := parserEnv_of_ioState hsN
      have hsaw' := compSawZero_of_stable hsaw0 hst hp
      refine ⟨rfl, dcs', srcs', srcs0', hgsrc0', hszsrc0', hgdc', hszdc', hgsrc', hszsrc', hp', hsaw', hrm, hst, Or.inl ⟨hEoi, ?_⟩⟩
      intro errs' srcs'' hge' _ hgs'' _ errsA hgeA _
      have heA := Option.some.inj (hgeA.symm.trans hgerr0)
      subst heA
      obtain ⟨_, _, _, _, errsN, _, _, _, _, srcsN, _, _, _, _, hgerrN, _, _, _, hpotN, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgsrcN, _⟩ := hsN
      rw [Option.some.inj (hge'.symm.trans hgerrN)]
      unfold srcPotential at hpotN
      split at hpotN <;> split at hpotN <;> omega
    · have hp' := parserEnv_of_ioState hsN
      have hsaw' := compSawZero_of_stable hsaw0 hst hp
      refine ⟨rfl, dcs', srcs', srcs0', hgsrc0', hszsrc0', hgdc', hszdc', hgsrc', hszsrc', hp', hsaw', hrm, hst,
        Or.inr ⟨hNe, hnf0, hrank, ?_⟩⟩
      intro errs' srcs'' hge' _ hgs'' _ errsA hgeA _
      have heA := Option.some.inj (hgeA.symm.trans hgerr0)
      subst heA
      obtain ⟨_, _, _, _, errsN, _, _, _, _, srcsN, _, _, _, _, hgerrN, _, _, _, hpotN, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgsrcN, _⟩ := hsN
      rw [Option.some.inj (hge'.symm.trans hgerrN), Option.some.inj (hgs''.symm.trans hgsrcN)]
      have hs0Eq : srcs0' = srcs0 := Option.some.inj (hgsrc0'.symm.trans hgsrc0)
      rw [hs0Eq] at hnf0 ⊢
      unfold srcPotential at hpotN ⊢; unfold warnPotVal
      rw [hnf0] at hpotN ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hpotN ⊢
      exact hpotN

def rmSrcWeight (src : C.JpegSourceMgr) : Nat :=
  if isConstEofPtr src.nextInputByte then 0 else 4 * (src.bytesInBuffer.toNat + 2 ^ 20)

def rmRank (dc : C.JpegDecompressStruct) (mrk : C.JpegMarkerReader) (src : C.JpegSourceMgr) : Nat :=
  rmSrcWeight src + (if mrk.sawSOI == 0 then 2 else 0) + (if dc.unreadMarker != 0 then 1 else 0) + 1

def rmWarnPot (errs : Array C.JpegErrorMgr) (srcs : Array C.JpegSourceMgr)
    (dc : C.JpegDecompressStruct) : Int :=
  warnPotVal errs srcs +
    if isConstEofPtr srcs[0]!.nextInputByte then (if dc.unreadMarker != 0 then 2 ^ 17 else 0)
    else 2 ^ 18

private theorem rmSrcWeight_mono {s0 s1 : C.JpegSourceMgr} (hm : SrcMono s0 s1) :
    rmSrcWeight s1 ≤ rmSrcWeight s0 := by
  unfold rmSrcWeight
  by_cases hc0 : isConstEofPtr s0.nextInputByte = true
  · have hc1 := hm.1 hc0; simp only [hc1, hc0, ↓reduceIte]; exact Nat.le_refl 0
  · have hf0 : isConstEofPtr s0.nextInputByte = false := by cases hc : isConstEofPtr s0.nextInputByte <;> simp_all
    simp only [hf0, Bool.false_eq_true, ↓reduceIte]
    rcases hm.2 hf0 with hc1 | hle1
    · simp only [hc1, ↓reduceIte]; exact Nat.zero_le _
    · by_cases hc1 : isConstEofPtr s1.nextInputByte = true
      · simp only [hc1, ↓reduceIte]; exact Nat.zero_le _
      · have hf1 : isConstEofPtr s1.nextInputByte = false := by cases hc : isConstEofPtr s1.nextInputByte <;> simp_all
        simp only [hf1, Bool.false_eq_true, ↓reduceIte]; omega

private theorem rmSrcWeight_lt_of_srcRank_lt {s0 s1 : C.JpegSourceMgr}
    (hnf : isConstEofPtr s0.nextInputByte = false) (hlt : srcRank s1 < srcRank s0) :
    rmSrcWeight s1 + 4 ≤ rmSrcWeight s0 := by
  unfold rmSrcWeight
  simp only [hnf, Bool.false_eq_true, ↓reduceIte]
  by_cases hc1 : isConstEofPtr s1.nextInputByte = true
  · simp only [hc1, ↓reduceIte]; omega
  · have hf1 : isConstEofPtr s1.nextInputByte = false := by cases hc : isConstEofPtr s1.nextInputByte <;> simp_all
    simp only [hf1, Bool.false_eq_true, ↓reduceIte]
    unfold srcRank at hlt
    simp only [hnf, hf1, Bool.false_eq_true, ↓reduceIte] at hlt
    omega

private theorem rmSawSoi_mono {m0 m1 : C.JpegMarkerReader} (hm : m0.sawSOI ≠ 0 → m1.sawSOI ≠ 0) :
    (if m1.sawSOI == 0 then (2 : Nat) else 0) ≤ (if m0.sawSOI == 0 then 2 else 0) := by
  by_cases h0 : m0.sawSOI = 0
  · have : (m0.sawSOI == 0) = true := by simp [h0]
    simp only [this, ↓reduceIte]; split <;> omega
  · have h1 := hm h0
    have ha : (m0.sawSOI == 0) = false := by cases hc : (m0.sawSOI == 0); rfl; exact False.elim (h0 (by simpa using hc))
    have hb : (m1.sawSOI == 0) = false := by cases hc : (m1.sawSOI == 0); rfl; exact False.elim (h1 (by simpa using hc))
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte]; exact Nat.le_refl 0

private theorem scanLimit_lt_of_scanBd {dc : C.JpegDecompressStruct} {src : C.JpegSourceMgr}
    (hbib : src.bytesInBuffer.toNat < 2 ^ 20)
    (hbd : dc.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31) :
    scanLimit dc src < 2 ^ 31 := by
  unfold scanLimit
  split <;> (try split) <;> omega

private theorem warnPotVal_bound_of_rmWarnPot {errs : Array C.JpegErrorMgr} {srcs : Array C.JpegSourceMgr}
    {dc : C.JpegDecompressStruct} {mrk : C.JpegMarkerReader} {potBd : Int}
    (hle : rmWarnPot errs srcs dc + (rmRank dc mrk srcs[0]! : Int) ≤ potBd)
    (hhi : potBd + 2 ^ 23 < 2 ^ 63) :
    warnPotVal errs srcs + 2 ^ 23 < 2 ^ 63 := by
  unfold rmWarnPot at hle
  split at hle
  · split at hle <;> omega
  · omega

private theorem appn_idx_lt_16 {um : Int32}
    (hle : (um ≥ M_APP0 && um ≤ M_APP15) = true) :
    (um - M_APP0).toInt.toNat < 16 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hle
  rcases hle with ⟨hlo, hhi⟩
  change M_APP0 ≤ um at hlo
  rw [Int32.le_iff_toInt_le] at hlo hhi
  have hm0 : M_APP0.toInt = 224 := by decide
  have hm15 : M_APP15.toInt = 239 := by decide
  have hsub : (um - M_APP0).toInt = um.toInt - 224 := by
    rw [Int32.toInt_sub, hm0]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  omega

private theorem read_markers_clear_unread {ctx : IoCtx} {hInit h2 : C.Heap} {k0 : Nat} {potBd : Int}
    (hp2 : ParserEnv ctx h2) (hsaw2 : CompSawZero ctx h2)
    (hrm02 : RmFrame ctx hInit h2)
    (hst02 : ∀ dcs0 dcs2, C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
      C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
      PostSofBase hInit dcs0[0]! → PostSofBase h2 dcs2[0]!)
    (hscan2 : ∀ dcs2, C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
      dcs2[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31)
    (hrankDrop : ∀ dcs2 mrks2 srcs2 errs2,
      C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
      C.Space.get h2 ctx.rmrk = some mrks2 → 0 < mrks2.size →
      C.Space.get h2 ctx.rs = some srcs2 → 0 < srcs2.size →
      C.Space.get h2 ctx.rerr = some errs2 → 0 < errs2.size →
      rmWarnPot errs2 srcs2 { dcs2[0]! with unreadMarker := 0 } +
        (rmRank { dcs2[0]! with unreadMarker := 0 } mrks2[0]! srcs2[0]! : Int) ≤ potBd ∧
      rmRank { dcs2[0]! with unreadMarker := 0 } mrks2[0]! srcs2[0]! < k0) :
    ∃ (k' : Nat) (s' : ReadMarkersState) (h' : C.Heap),
      C.run (do let dcEnd ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcEnd with unreadMarker := 0 }
                return { done := false, ret := .ok JPEG_SUSPENDED }) h2 = .ok (s', h') ∧
      k' < k0 ∧ !s'.done = true ∧
      ParserEnv ctx h' ∧ CompSawZero ctx h' ∧ RmFrame ctx hInit h' ∧
      (∀ dcs' mrks' srcs' errs',
        C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
        C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
        C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
        C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
        rmWarnPot errs' srcs' dcs'[0]! + (rmRank dcs'[0]! mrks'[0]! srcs'[0]! : Int) ≤ potBd ∧
        dcs'[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 ∧
        rmRank dcs'[0]! mrks'[0]! srcs'[0]! = k') ∧
      (∀ dcs0 dcs', C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
        C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
        PostSofBase hInit dcs0[0]! → PostSofBase h' dcs'[0]!) := by
  obtain ⟨dcs2, hgdc2, hszdc2, _⟩ := parserEnv_get_dc hp2
  obtain ⟨mrks2, hgmrk2, hszmrk2, _⟩ := parserEnv_get_mrk hp2
  obtain ⟨srcs2, hgsrc2, hszsrc2, _⟩ := parserEnv_get_src hp2
  obtain ⟨errs2, hgerr2, hszerr2, _⟩ := parserEnv_get_err hp2
  have hldc2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc2 hszdc2
  have hro2 : C.Space.ro h2 (C.DecompRef.decomp ctx.bdc) = false := rfl
  let dcNew := { dcs2[0]! with unreadMarker := 0 }
  have hstDc2 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcNew) hgdc2 hro2 hszdc2
  let h3 := C.Space.put h2 (C.DecompRef.decomp ctx.bdc) (dcs2.set! 0 dcNew)
  have hp3 : ParserEnv ctx h3 := parserEnv_put_dc_same hp2 hgdc2 hszdc2
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hst23 : DecompHeaderStable ctx h2 h3 := by
    refine ⟨(fun da db hga _ hgb _ => by
      have ha := Option.some.inj (hga.symm.trans hgdc2)
      have hg3 : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dcNew) := by
        simp [h3, C.Space.get, C.Space.put]
      have hb := Option.some.inj (hgb.symm.trans hg3)
      rw [ha, hb, set0_bang_m dcs2 hszdc2 dcNew]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩),
      (fun ma mb ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
      (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
  have hsaw3 := compSawZero_of_stable hsaw2 hst23 hp2
  have hrm23 : RmFrame ctx h2 h3 := by
    refine ⟨fun da db hga _ hgb _ => ?_, fun ma mb ha _ hb _ hm => by rw [Option.some.inj (hb.symm.trans ha)]; exact hm⟩
    have ha := Option.some.inj (hga.symm.trans hgdc2)
    have hg3 : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dcNew) := by
      simp [h3, C.Space.get, C.Space.put]
    have hb := Option.some.inj (hgb.symm.trans hg3)
    rw [ha, hb, set0_bang_m dcs2 hszdc2 dcNew]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hrm03 : RmFrame ctx hInit h3 := rmFrame_trans ctx hrm02 hrm23 hp2
  obtain ⟨hwp3, hrk3⟩ := hrankDrop dcs2 mrks2 srcs2 errs2 hgdc2 hszdc2 hgmrk2 hszmrk2 hgsrc2 hszsrc2 hgerr2 hszerr2
  refine ⟨rmRank dcNew mrks2[0]! srcs2[0]!, { done := false, ret := .ok JPEG_SUSPENDED }, h3, ?_, hrk3, rfl, hp3, hsaw3, hrm03, ?_, ?_⟩
  · rw [C.run_bind, hldc2]; dsimp only; rw [C.run_bind, hstDc2]; rfl
  · intro dcs' mrks' srcs' errs' hgd' _ hgm' _ hgs' _ hge' _
    have hgdc3 : C.Space.get h3 (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dcNew) := by
      simp [h3, C.Space.get, C.Space.put]
    rw [Option.some.inj (hgd'.symm.trans hgdc3), set0_bang_m dcs2 hszdc2 dcNew,
      Option.some.inj (hgm'.symm.trans hgmrk2), Option.some.inj (hgs'.symm.trans hgsrc2),
      Option.some.inj (hge'.symm.trans hgerr2)]
    refine ⟨hwp3, ?_, rfl⟩
    change dcs2[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31
    exact hscan2 dcs2 hgdc2 hszdc2
  · intro dcs0 dcs3 hgd0 hsz0 hgd3 hsz3 hps0
    have hps2 := hst02 dcs0 dcs2 hgd0 hsz0 hgdc2 hszdc2 hps0
    exact postSofBase_of_decompHeaderStable hp2 hp3 hst23 hgdc2 hszdc2 hgd3 hsz3 hps2

private theorem rmBudget_after_dispatch_step {ctx : IoCtx} {hX h2 : C.Heap} {k0 : Nat} {potBd : Int}
    (hbdX : ∀ dcsX mrksX srcsX errsX,
      C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
      C.Space.get hX ctx.rmrk = some mrksX → 0 < mrksX.size →
      C.Space.get hX ctx.rs = some srcsX → 0 < srcsX.size →
      C.Space.get hX ctx.rerr = some errsX → 0 < errsX.size →
      rmRank { dcsX[0]! with unreadMarker := 0 } mrksX[0]! srcsX[0]! < k0 ∧
      warnPotVal errsX srcsX + (if isConstEofPtr srcsX[0]!.nextInputByte then (2 ^ 17 : Int) else 2 ^ 18 + 1) +
        (rmRank { dcsX[0]! with unreadMarker := 0 } mrksX[0]! srcsX[0]! : Int) ≤ potBd)
    (hpX : ParserEnv ctx hX) (_hp2 : ParserEnv ctx h2)
    (hmMrk : ∀ mrks0 mrks', C.Space.get hX ctx.rmrk = some mrks0 → 0 < mrks0.size →
      C.Space.get h2 ctx.rmrk = some mrks' → 0 < mrks'.size → mrks0[0]!.sawSOI ≠ 0 → mrks'[0]!.sawSOI ≠ 0)
    (hmSrc : ∀ srcs0 srcs', C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
      C.Space.get h2 ctx.rs = some srcs' → 0 < srcs'.size → SrcMono srcs0[0]! srcs'[0]!)
    (hwOk : ∀ errs0 errs' srcs0 srcs',
      C.Space.get hX ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get h2 ctx.rerr = some errs' → 0 < errs'.size →
      C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
      C.Space.get h2 ctx.rs = some srcs' → 0 < srcs'.size →
      (isConstEofPtr srcs'[0]!.nextInputByte = false → warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
      (isConstEofPtr srcs'[0]!.nextInputByte = true →
        errs'[0]!.numWarnings.toInt ≤ (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
          else warnPotVal errs0 srcs0) + 2 ^ 17)) :
    ∀ dcs2 mrks2 srcs2 errs2,
      C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
      C.Space.get h2 ctx.rmrk = some mrks2 → 0 < mrks2.size →
      C.Space.get h2 ctx.rs = some srcs2 → 0 < srcs2.size →
      C.Space.get h2 ctx.rerr = some errs2 → 0 < errs2.size →
      rmWarnPot errs2 srcs2 { dcs2[0]! with unreadMarker := 0 } +
        (rmRank { dcs2[0]! with unreadMarker := 0 } mrks2[0]! srcs2[0]! : Int) ≤ potBd ∧
      rmRank { dcs2[0]! with unreadMarker := 0 } mrks2[0]! srcs2[0]! < k0 := by
  intro dcs2 mrks2 srcs2 errs2 _ _ hgm2 hszm2 hgs2 hszs2 hge2 hsze2
  obtain ⟨dcsX, hgdcX, hszdcX, _⟩ := parserEnv_get_dc hpX
  obtain ⟨mrksX, hgmrkX, hszmrkX, _⟩ := parserEnv_get_mrk hpX
  obtain ⟨srcsX, hgsrcX, hszsrcX, _⟩ := parserEnv_get_src hpX
  obtain ⟨errsX, hgerrX, hszerrX, _⟩ := parserEnv_get_err hpX
  obtain ⟨hrkLt, hwpX⟩ := hbdX dcsX mrksX srcsX errsX hgdcX hszdcX hgmrkX hszmrkX hgsrcX hszsrcX hgerrX hszerrX
  have hsm := hmSrc srcsX srcs2 hgsrcX hszsrcX hgs2 hszs2
  have hrmW := rmSrcWeight_mono hsm
  have hrmS := rmSawSoi_mono (hmMrk mrksX mrks2 hgmrkX hszmrkX hgm2 hszm2)
  have hu2 : (({ dcs2[0]! with unreadMarker := 0 } : C.JpegDecompressStruct).unreadMarker != 0) = false := rfl
  have huX : (({ dcsX[0]! with unreadMarker := 0 } : C.JpegDecompressStruct).unreadMarker != 0) = false := rfl
  have hrk2 : rmRank { dcs2[0]! with unreadMarker := 0 } mrks2[0]! srcs2[0]! < k0 := by
    unfold rmRank at hrkLt ⊢; simp only [huX, Bool.false_eq_true, ↓reduceIte] at hrkLt; simp only [hu2, Bool.false_eq_true, ↓reduceIte]; omega
  obtain ⟨wf, wt⟩ := hwOk errsX errs2 srcsX srcs2 hgerrX hszerrX hge2 hsze2 hgsrcX hszsrcX hgs2 hszs2
  refine ⟨?_, hrk2⟩
  unfold rmWarnPot
  simp only [hu2, Bool.false_eq_true, ↓reduceIte]
  unfold rmRank at hwpX ⊢
  simp only [hu2, Bool.false_eq_true, ↓reduceIte] at hwpX ⊢
  by_cases hc2 : isConstEofPtr srcs2[0]!.nextInputByte = false
  · have hcX : isConstEofPtr srcsX[0]!.nextInputByte = false := by
      cases hc : isConstEofPtr srcsX[0]!.nextInputByte
      · rfl
      · have := hsm.1 hc; rw [this] at hc2; cases hc2
    have wle := wf hc2
    simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hwpX ⊢
    simp only [hcX, Bool.false_eq_true, ↓reduceIte] at hwpX
    omega
  · have ht2 : isConstEofPtr srcs2[0]!.nextInputByte = true := by
      cases hc : isConstEofPtr srcs2[0]!.nextInputByte <;> simp_all
    have wle := wt ht2
    simp only [ht2, ↓reduceIte] at hwpX ⊢
    unfold warnPotVal at wle hwpX ⊢
    simp only [ht2, ↓reduceIte]
    by_cases hcX : isConstEofPtr srcsX[0]!.nextInputByte = true
    · simp only [hcX, ↓reduceIte] at wle hwpX; omega
    · have hfX : isConstEofPtr srcsX[0]!.nextInputByte = false := by
        cases hc : isConstEofPtr srcsX[0]!.nextInputByte <;> simp_all
      simp only [hfX, Bool.false_eq_true, ↓reduceIte] at wle hwpX; omega

private theorem read_markers_parser_step {ctx : IoCtx} {hInit hX : C.Heap} {k0 : Nat} {potBd : Int}
    (parser : C.M (C.JpegRes Bool))
    (hres : ∃ res h2,
      C.run parser hX = .ok (res, h2) ∧
      (match res with
       | .ok true =>
         ParserEnv ctx h2 ∧ CompSawZero ctx h2 ∧ RmFrame ctx hX h2 ∧ DecompHeaderStable ctx hX h2 ∧
         (∀ srcs0 srcs', C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
           C.Space.get h2 ctx.rs = some srcs' → 0 < srcs'.size → SrcMono srcs0[0]! srcs'[0]!) ∧
         (∀ errs0 errs' srcs0 srcs',
           C.Space.get hX ctx.rerr = some errs0 → 0 < errs0.size →
           C.Space.get h2 ctx.rerr = some errs' → 0 < errs'.size →
           C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
           C.Space.get h2 ctx.rs = some srcs' → 0 < srcs'.size →
           (isConstEofPtr srcs'[0]!.nextInputByte = false → warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
           (isConstEofPtr srcs'[0]!.nextInputByte = true →
             errs'[0]!.numWarnings.toInt ≤ (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
               else warnPotVal errs0 srcs0) + 2 ^ 17))
       | _ => True))
    (hpX : ParserEnv ctx hX) (hrmX : RmFrame ctx hInit hX)
    (hscanX : ∀ dcsX, C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
      dcsX[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31)
    (hpsX : ∀ dcs0 dcsX, C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
      C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
      PostSofBase hInit dcs0[0]! → PostSofBase hX dcsX[0]!)
    (hbdX : ∀ dcsX mrksX srcsX errsX,
      C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
      C.Space.get hX ctx.rmrk = some mrksX → 0 < mrksX.size →
      C.Space.get hX ctx.rs = some srcsX → 0 < srcsX.size →
      C.Space.get hX ctx.rerr = some errsX → 0 < errsX.size →
      rmRank { dcsX[0]! with unreadMarker := 0 } mrksX[0]! srcsX[0]! < k0 ∧
      warnPotVal errsX srcsX + (if isConstEofPtr srcsX[0]!.nextInputByte then (2 ^ 17 : Int) else 2 ^ 18 + 1) +
        (rmRank { dcsX[0]! with unreadMarker := 0 } mrksX[0]! srcsX[0]! : Int) ≤ potBd) :
    ∃ (k' : Nat) (s' : ReadMarkersState) (h' : C.Heap),
      C.run (do match (← parser) with
                | .errExit code => return { done := true, ret := .errExit code }
                | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
                | .ok true => pure ()
                let dcEnd ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcEnd with unreadMarker := 0 }
                return { done := false, ret := .ok JPEG_SUSPENDED }) hX = .ok (s', h') ∧
      (if s'.done then k' = 0 ∧ (s'.ret = .ok JPEG_SUSPENDED ∨ ∃ c, s'.ret = .errExit c)
       else k' < k0 ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧ RmFrame ctx hInit h' ∧
         (∀ dcs' mrks' srcs' errs',
           C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
           C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
           C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
           C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
           rmWarnPot errs' srcs' dcs'[0]! + (rmRank dcs'[0]! mrks'[0]! srcs'[0]! : Int) ≤ potBd ∧
           dcs'[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 ∧
           rmRank dcs'[0]! mrks'[0]! srcs'[0]! = k') ∧
         (∀ dcs0 dcs', C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
           C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
           PostSofBase hInit dcs0[0]! → PostSofBase h' dcs'[0]!)) := by
  obtain ⟨res, h2, hrun, hpost⟩ := hres
  cases res with
  | errExit code =>
    refine ⟨0, { done := true, ret := .errExit code }, h2, ?_, rfl, Or.inr ⟨code, rfl⟩⟩
    rw [C.run_bind, hrun]; rfl
  | ok b =>
    cases b with
    | false =>
      refine ⟨0, { done := true, ret := .ok JPEG_SUSPENDED }, h2, ?_, rfl, Or.inl rfl⟩
      rw [C.run_bind, hrun]; rfl
    | true =>
      rcases hpost with ⟨hp2, hsaw2, hrm2, hst2, hmSrc, hwOk⟩
      obtain ⟨dcsX, hgdcX, hszdcX, _⟩ := parserEnv_get_dc hpX
      have hscan2 : ∀ dcs2, C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
          dcs2[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 := fun dcs2 hgd2 hsz2 => by
        rw [(hrm2.1 dcsX dcs2 hgdcX hszdcX hgd2 hsz2).1]; exact hscanX dcsX hgdcX hszdcX
      have hps02 : ∀ dcs0 dcs2, C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
          C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
          PostSofBase hInit dcs0[0]! → PostSofBase h2 dcs2[0]! := fun dcs0 dcs2 hgd0 hsz0 hgd2 hsz2 hps0 =>
        postSofBase_of_decompHeaderStable hpX hp2 hst2 hgdcX hszdcX hgd2 hsz2 (hpsX dcs0 dcsX hgd0 hsz0 hgdcX hszdcX hps0)
      have hdrop := rmBudget_after_dispatch_step hbdX hpX hp2 hrm2.2 hmSrc hwOk
      obtain ⟨k', s', h', hrunCl, hltK, hnd, hp', hsaw', hrm', hbd', hps'⟩ :=
        read_markers_clear_unread hp2 hsaw2 (rmFrame_trans ctx hrmX hrm2 hpX) hps02 hscan2 hdrop
      have hndF : s'.done = false := by cases hc : s'.done <;> simp_all
      refine ⟨k', s', h', ?_, ?_⟩
      · rw [C.run_bind, hrun]; exact hrunCl
      · simp only [hndF, Bool.false_eq_true, ↓reduceIte]; exact ⟨hltK, hp', hsaw', hrm', hbd', hps'⟩

private theorem get_sos_ok_sawSOF {ctx : IoCtx} {h h' : C.Heap}
    (hp : ParserEnv ctx h)
    (hrun : C.run (get_sos (.ref (C.DecompRef.decomp ctx.bdc) 0)) h = .ok (.ok true, h')) :
    ∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size → mrks[0]!.sawSOF ≠ 0 := by
  intro mrks hgm hsz hs0
  obtain ⟨dcs0, hgdc0, hszdc0, _, _, _, _, kmrk0, ksrc0⟩ := parserEnv_get_dc hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
  have hldc0 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc0 hszdc0
  have hlsrc0 := ptr_load_ok (r := ctx.rs) (off := 0) hgsrc0 hszsrc0
  have hlmrk0 := ptr_load_ok (r := ctx.rmrk) (off := 0) hgm hsz
  have hlsrc0' : C.run (Ptr.load dcs0[0]!.src) h = .ok (srcs0[0]!, h) := by rw [ksrc0]; exact hlsrc0
  have hlmrk0' : C.run (Ptr.load dcs0[0]!.marker) h = .ok (mrks[0]!, h) := by rw [kmrk0]; exact hlmrk0
  unfold get_sos at hrun
  rw [C.run_bind, hldc0] at hrun; dsimp only at hrun
  rw [C.run_bind, hlsrc0'] at hrun; dsimp only at hrun
  rw [C.run_bind, hlmrk0'] at hrun; dsimp only at hrun
  have h0b : (mrks[0]!.sawSOF == 0) = true := by simp [hs0]
  simp only [h0b, ↓reduceIte] at hrun
  cases hE : C.run (errexit dcs0[0]!.err JERR_SOS_NO_SOF) h <;> rw [C.run_bind, hE] at hrun <;> cases hrun

private theorem multiScanReady_put_dc_unread {ctx : IoCtx} {h : C.Heap}
    (dcs : Array C.JpegDecompressStruct)
    (_hgdc : C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs) (_hsz : 0 < dcs.size)
    (hm : MultiScanReady h dcs[0]!) :
    let h' := C.Space.put h (C.DecompRef.decomp ctx.bdc) (dcs.set! 0 { dcs[0]! with unreadMarker := 0 })
    MultiScanReady h' { dcs[0]! with unreadMarker := 0 } := by
  rcases hm with ⟨e1, e2, e3, c1, c2, cs, m1, m2, m3, m4, w1, h1, nc1, nc2, ⟨rmrk, mrks, km, hgm, hszm, hsof⟩, hc, hcur⟩
  refine ⟨e1, e2, e3, c1, c2, cs, m1, m2, m3, m4, w1, h1, nc1, nc2,
    ⟨rmrk, mrks, km, ?_, hszm, hsof⟩, ?_, ?_⟩
  · cases rmrk; exact hgm
  · rcases hc with h0 | ⟨rcp, cs0, kc, hgc, hszc, hfc⟩
    · exact Or.inl h0
    · refine Or.inr ⟨rcp, cs0, kc, ?_, hszc, hfc⟩; cases rcp; exact hgc
  · intro i hi
    obtain ⟨rcp, off, cs0, ci, hci, hgc, hoff, hceq, h1a, h1b, h2a, h2b, h3a, h3b⟩ := hcur i hi
    refine ⟨rcp, off, cs0, ci, hci, ?_, hoff, hceq, h1a, h1b, h2a, h2b, h3a, h3b⟩
    cases rcp; exact hgc

private def MrkSoiStrong (ctx : IoCtx) (h h' : C.Heap) : Prop :=
  ∀ mrks, C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
    ∃ mrks', C.Space.get h' ctx.rmrk = some mrks' ∧ 0 < mrks'.size ∧ (mrks[0]!.sawSOI ≠ 0 → mrks'[0]!.sawSOI ≠ 0)

private theorem mrkSoiStrong_refl (ctx : IoCtx) (h : C.Heap) : MrkSoiStrong ctx h h :=
  fun mrks hm hsz => ⟨mrks, hm, hsz, id⟩

private theorem mrkSoiStrong_trans {ctx : IoCtx} {a b c : C.Heap}
    (hab : MrkSoiStrong ctx a b) (hbc : MrkSoiStrong ctx b c) : MrkSoiStrong ctx a c := fun mrks hm hsz => by
  obtain ⟨m1, hm1, hsz1, hf1⟩ := hab mrks hm hsz
  obtain ⟨m2, hm2, hsz2, hf2⟩ := hbc m1 hm1 hsz1
  exact ⟨m2, hm2, hsz2, fun h => hf2 (hf1 h)⟩

private theorem mrkSoiStrong_bind {α β : Type} {ctx : IoCtx} {m1 : C.M α} {m2 : α → C.M β}
    (hm1 : ∀ h a h', C.run m1 h = .ok (a, h') → MrkSoiStrong ctx h h')
    (hm2 : ∀ a h b h', C.run (m2 a) h = .ok (b, h') → MrkSoiStrong ctx h h') :
    ∀ h b h', C.run (m1 >>= m2) h = .ok (b, h') → MrkSoiStrong ctx h h' := fun h b h' hr => by
  cases h1 : C.run m1 h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1 => rcases p1 with ⟨a, ha⟩; rw [C.run_bind, h1] at hr; exact mrkSoiStrong_trans (hm1 h a ha h1) (hm2 a ha b h' hr)

private theorem mrkSoiStrong_bind_here {α β : Type} {ctx : IoCtx} {m1 : C.M α} {m2 : α → C.M β} {h : C.Heap}
    (hm1 : ∀ a h1, C.run m1 h = .ok (a, h1) → MrkSoiStrong ctx h h1)
    (hm2 : ∀ a h1 b h', C.run (m2 a) h1 = .ok (b, h') → MrkSoiStrong ctx h1 h') :
    ∀ b h', C.run (m1 >>= m2) h = .ok (b, h') → MrkSoiStrong ctx h h' := fun b h' hr => by
  cases h1 : C.run m1 h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1 => rcases p1 with ⟨a, ha⟩; rw [C.run_bind, h1] at hr; exact mrkSoiStrong_trans (hm1 a ha h1) (hm2 a ha b h' hr)

private theorem mrkSoiStrong_bind_load {R α : Type} [C.Space C.Heap R α] {p : C.Ptr R}
    {ctx : IoCtx} {β : Type} (m2 : α → C.M β)
    (hm2 : ∀ {b} a h h', C.run (m2 a) h = .ok (b, h') → C.run (Ptr.load p) h = .ok (a, h) → MrkSoiStrong ctx h h') :
    ∀ h b h', C.run (C.Ptr.load p >>= m2) h = .ok (b, h') → MrkSoiStrong ctx h h' := fun h b h' hr => by
  cases h1 : C.run (C.Ptr.load p) h with
  | error e => rw [C.run_bind, h1] at hr; cases hr
  | ok p1 => rcases p1 with ⟨a, h1'⟩; have heq := ptr_load_heap_eq h1; subst heq; rw [C.run_bind, h1] at hr; dsimp only at hr; exact hm2 a h1' h' hr h1

private theorem mrkSoiStrong_of_markers_eq {ctx : IoCtx} {h h' : C.Heap} (hm : h'.markers = h.markers) :
    MrkSoiStrong ctx h h' := fun mrks hgm hsz =>
  ⟨mrks, by cases hrm : ctx.rmrk with | marker bm => simp only [C.Space.get, hrm, hm] at hgm ⊢; exact hgm, hsz, id⟩

private theorem mrkSoiStrong_store_dc_any {ctx : IoCtx} {p : C.DecompPtr} {v : C.JpegDecompressStruct} {h h' : C.Heap}
    (hrun : C.run (C.Ptr.store p v) h = .ok ((), h')) : MrkSoiStrong ctx h h' := by
  cases p with
  | null => simp [C.run, C.Ptr.store] at hrun
  | ref r off =>
    rcases r with ⟨b⟩
    simp only [C.run, C.Ptr.store] at hrun
    cases hg : C.Space.get h (C.DecompRef.decomp b) with
    | none => simp [hg] at hrun
    | some _ =>
      simp only [hg] at hrun
      split at hrun
      · simp at hrun
      · split at hrun
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, rfl⟩ := hrun
          exact mrkSoiStrong_of_markers_eq rfl
        · simp at hrun

private theorem mrkSoiStrong_tracems3 {ctx : IoCtx} (ep : C.ErrPtr) (lvl code p1 p2 p3 : Int32) :
    ∀ h r h', C.run (tracems3 ep lvl code p1 p2 p3) h = .ok (r, h') → MrkSoiStrong ctx h h' := fun h r h' hr => by
  unfold tracems3 at hr
  refine mrkSoiStrong_bind_load _ (fun err h1 h' hr _ => ?_) h r h' hr
  dsimp (config := { zetaHave := true }) only at hr
  refine mrkSoiStrong_bind ?_ ?_ h1 _ h' hr
  · intro h0 _ h2 h2'; exact mrkSoiStrong_of_markers_eq (rmFrameStrong_decomps_markers_same ep _ h0 h2 h2').2
  · intro _ h2 _ h3 h3'; exact mrkSoiStrong_of_markers_eq (rmFrameStrong_emitMessage ep lvl h2 _ h3 h3').2

private theorem mrkSoiStrong_forIn_range {σ : Type} {ctx : IoCtx}
    (l : List Nat) (body : Nat → σ → C.M (ForInStep σ))
    (hb : ∀ a s h step h', C.run (body a s) h = .ok (step, h') → MrkSoiStrong ctx h h') :
    ∀ init h s' h', C.run (ForIn.forIn l init body) h = .ok (s', h') → MrkSoiStrong ctx h h' := by
  induction l with
  | nil => intro init h s' h' hrun; simp only [ForIn.forIn, C.run] at hrun; cases hrun; exact mrkSoiStrong_refl ctx _
  | cons a tl ih =>
    intro init h s' h' hrun
    simp only [ForIn.forIn, List.forIn'_cons] at hrun
    cases h1 : C.run (body a init) h with
    | error e => rw [C.run_bind, h1] at hrun; cases hrun
    | ok p1 =>
      rcases p1 with ⟨step, h1'⟩
      rw [C.run_bind, h1] at hrun; dsimp only at hrun
      cases step with
      | done r =>
        obtain ⟨rfl, rfl⟩ := by simpa [C.run] using hrun
        exact hb a init h (.done _) h1' h1
      | yield r => exact mrkSoiStrong_trans (hb a init h (.yield r) h1' h1) (ih r h1' s' h' (by simpa [C.run] using hrun))

private theorem mrkSoiStrong_get_sos {ctx : IoCtx} {h r h'}
    (hr : C.run (get_sos (.ref (C.DecompRef.decomp ctx.bdc) 0)) h = .ok (r, h')) :
    MrkSoiStrong ctx h h' := by
  unfold get_sos at hr
  refine mrkSoiStrong_bind_load _ (fun dc0 _ _ hr _ => ?_) h r h' hr
  refine mrkSoiStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  refine mrkSoiStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
  split at hr
  · refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_errexit _ _ _ _ _ h1).2) ?_ _ _ _ hr
    intro _ _ _ _ h1; cases h1; exact mrkSoiStrong_refl ctx _
  · refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_input2Bytes _ _ _ _ _ _ h1).2) (fun x _ _ _ hr => ?_) _ _ _ hr
    cases x with | none => cases hr; exact mrkSoiStrong_refl ctx _ | some _ => ?_
    refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_inputByte _ _ _ _ _ _ h1).2) (fun y _ _ _ hr => ?_) _ _ _ hr
    cases y with | none => cases hr; exact mrkSoiStrong_refl ctx _ | some _ => ?_
    refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_tracems1 _ _ _ _ _ _ _ h1).2) (fun _ _ _ _ hr => ?_) _ _ _ hr
    split at hr
    · refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_errexit _ _ _ _ _ h1).2) ?_ _ _ _ hr
      intro _ _ _ _ h1; cases h1; exact mrkSoiStrong_refl ctx _
    · refine mrkSoiStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
      refine mrkSoiStrong_bind (fun _ _ _ hst => mrkSoiStrong_store_dc_any hst) (fun _ _ _ _ hr => ?_) _ _ _ hr
      refine mrkSoiStrong_bind (fun _ _ _ hc =>
        cwhile_preserves _ _ (MrkSoiStrong ctx) (fun a b => mrkSoiStrong_trans a b)
          (fun _ _ _ _ _ h1 => by cases h1; exact mrkSoiStrong_refl ctx _)
          (fun s _ _ _ hb => by
            refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_inputByte _ _ _ _ _ _ h1).2) (fun r1 _ _ _ hb => ?_) _ _ _ hb
            cases r1 with | none => cases hb; exact mrkSoiStrong_refl ctx _ | some _ => ?_
            refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_inputByte _ _ _ _ _ _ h1).2) (fun r2 _ _ _ hb => ?_) _ _ _ hb
            cases r2 with | none => cases hb; exact mrkSoiStrong_refl ctx _ | some _ => ?_
            refine mrkSoiStrong_bind_load _ (fun dcCur _ _ hb _ => ?_) _ _ _ hb
            refine mrkSoiStrong_bind (mrkSoiStrong_forIn_range _ _ ?_ _) (fun found _ _ _ hb => ?_) _ _ _ hb
            · intro _ _ _ _ _ hs
              dsimp (config := { zetaHave := true }) only at hs
              split at hs
              · cases ha : C.run (C.Ptr.add dcCur.compInfo _) _ with
                | error _ => rw [C.run_bind, ha] at hs; cases hs
                | ok qa =>
                  rcases qa with ⟨cp, h1'⟩
                  have heq := ptr_add_comp_heap_eq ha; subst heq
                  rw [C.run_bind, ha] at hs
                  exact mrkSoiStrong_bind_load _ (fun _ _ _ h1 _ => by split at h1 <;> cases h1 <;> exact mrkSoiStrong_refl ctx _) _ _ _ hs
              · cases hs; exact mrkSoiStrong_refl ctx _
            · cases found with
              | none =>
                refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_errexit1 _ _ _ _ _ _ h1).2) ?_ _ _ _ hb
                intro _ _ _ _ h1; cases h1; exact mrkSoiStrong_refl ctx _
              | some cp =>
                refine mrkSoiStrong_bind (fun _ _ _ hst => mrkSoiStrong_store_dc_any hst) (fun _ _ _ _ hb => ?_) _ _ _ hb
                refine mrkSoiStrong_bind_load _ (fun comp _ _ hb _ => ?_) _ _ _ hb
                refine mrkSoiStrong_bind (fun _ _ _ hst => mrkSoiStrong_of_markers_eq (rmFrameStrong_decomps_markers_eq_of_store_comp hst).2)
                  (fun _ _ _ _ hb => ?_) _ _ _ hb
                refine mrkSoiStrong_bind (mrkSoiStrong_tracems3 dcCur.err 1 JTRC_SOS_COMPONENT _ _ _)
                  (fun _ _ _ _ hb => ?_) _ _ _ hb
                refine mrkSoiStrong_bind_load _ (fun dcChk _ _ hb _ => ?_) _ _ _ hb
                refine mrkSoiStrong_bind (mrkSoiStrong_forIn_range _ _ ?_ _) (fun stF _ _ _ hb => ?_) _ _ _ hb
                · intro _ _ _ _ _ hs
                  split at hs
                  · exact mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_errexit1 _ _ _ _ _ _ h1).2)
                      (fun _ _ _ _ h1 => by cases h1; exact mrkSoiStrong_refl ctx _) _ _ _ hs
                  · cases hs; exact mrkSoiStrong_refl ctx _
                · rcases stF with ⟨rOpt, _⟩; cases rOpt <;> cases hb <;> exact mrkSoiStrong_refl ctx _)
          hc)
        (fun st _ _ _ hr => by
          split at hr
          · cases hr; exact mrkSoiStrong_refl ctx _
          · refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_inputByte _ _ _ _ _ _ h1).2) (fun rS _ _ _ hr => ?_) _ _ _ hr
            cases rS with | none => cases hr; exact mrkSoiStrong_refl ctx _ | some _ => ?_
            refine mrkSoiStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
            refine mrkSoiStrong_bind (fun _ _ _ hst => mrkSoiStrong_store_dc_any hst) (fun _ _ _ _ hr => ?_) _ _ _ hr
            refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_inputByte _ _ _ _ _ _ h1).2) (fun rE _ _ _ hr => ?_) _ _ _ hr
            cases rE with | none => cases hr; exact mrkSoiStrong_refl ctx _ | some _ => ?_
            refine mrkSoiStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
            refine mrkSoiStrong_bind (fun _ _ _ hst => mrkSoiStrong_store_dc_any hst) (fun _ _ _ _ hr => ?_) _ _ _ hr
            refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_inputByte _ _ _ _ _ _ h1).2) (fun rA _ _ _ hr => ?_) _ _ _ hr
            cases rA with | none => cases hr; exact mrkSoiStrong_refl ctx _ | some _ => ?_
            refine mrkSoiStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
            refine mrkSoiStrong_bind (fun _ _ _ hst => mrkSoiStrong_store_dc_any hst) (fun _ _ _ _ hr => ?_) _ _ _ hr
            refine mrkSoiStrong_bind (fun _ _ _ ht => mrkSoiStrong_of_markers_eq (tracems4_decomps_markers_eq _ _ _ _ _ _ _ _ _ _ ht).2)
              (fun _ _ _ _ hr => ?_) _ _ _ hr
            refine mrkSoiStrong_bind_load _ (fun mrkF _ _ hr hlm => ?_) _ _ _ hr
            refine mrkSoiStrong_bind_here ?_ (fun _ _ _ _ hr => ?_) _ _ hr
            · intro _ _ hst
              refine (rmFrameStrong_store_mrk _ _ hst ?_).2
              intro mrks hpeq hgm hsz hsaw
              rw [hpeq] at hlm; rw [← (mrk_load_ref0_eq hlm).2 mrks hgm hsz] at hsaw; exact hsaw
            · refine mrkSoiStrong_bind ?_ (fun isn _ _ _ hr => ?_) _ _ _ hr
              · intro _ _ _ h1
                unfold C.i32Add C.checkI32 at h1; split at h1 <;> cases h1 <;> exact mrkSoiStrong_refl ctx _
              · refine mrkSoiStrong_bind_load _ (fun _ _ _ hr _ => ?_) _ _ _ hr
                refine mrkSoiStrong_bind (fun _ _ _ hst => mrkSoiStrong_store_dc_any hst) (fun _ _ _ _ hr => ?_) _ _ _ hr
                refine mrkSoiStrong_bind (fun _ _ _ h1 => (rmFrameStrong_inputSync _ _ _ _ _ _ h1).2)
                  (fun _ _ _ _ he => by cases he; exact mrkSoiStrong_refl ctx _) _ _ _ hr) _ _ _ hr

private theorem read_markers_dispatch_ok {ctx : IoCtx} {hInit hX : C.Heap} {k0 : Nat} {potBd : Int}
    (hpX : ParserEnv ctx hX) (hsawX : CompSawZero ctx hX) (hrmX : RmFrame ctx hInit hX)
    (hpotHi : potBd + 2 ^ 23 < 2 ^ 63)
    (hscanX : ∀ dcsX, C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
      dcsX[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31)
    (hpsX : ∀ dcs0 dcsX, C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
      C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
      PostSofBase hInit dcs0[0]! → PostSofBase hX dcsX[0]!)
    (hbdX : ∀ dcsX mrksX srcsX errsX,
      C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
      C.Space.get hX ctx.rmrk = some mrksX → 0 < mrksX.size →
      C.Space.get hX ctx.rs = some srcsX → 0 < srcsX.size →
      C.Space.get hX ctx.rerr = some errsX → 0 < errsX.size →
      rmRank { dcsX[0]! with unreadMarker := 0 } mrksX[0]! srcsX[0]! < k0 ∧
      warnPotVal errsX srcsX + (if isConstEofPtr srcsX[0]!.nextInputByte then (2 ^ 17 : Int) else 2 ^ 18 + 1) +
        (rmRank { dcsX[0]! with unreadMarker := 0 } mrksX[0]! srcsX[0]! : Int) ≤ potBd) :
    ∃ (k' : Nat) (s' : ReadMarkersState) (h' : C.Heap),
      C.run (do
        let dc ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
        let um := dc.unreadMarker
        if um == M_SOI then
          match (← get_soi (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_SOF0 || um == M_SOF1 then
          match (← get_sof (.ref (C.DecompRef.decomp ctx.bdc) 0) FALSE FALSE FALSE) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_SOF2 then
          match (← get_sof (.ref (C.DecompRef.decomp ctx.bdc) 0) TRUE FALSE FALSE) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_SOF3 then
          match (← get_sof (.ref (C.DecompRef.decomp ctx.bdc) 0) FALSE TRUE FALSE) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_SOF9 then
          match (← get_sof (.ref (C.DecompRef.decomp ctx.bdc) 0) FALSE FALSE TRUE) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_SOF10 then
          match (← get_sof (.ref (C.DecompRef.decomp ctx.bdc) 0) TRUE FALSE TRUE) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_SOF11 then
          match (← get_sof (.ref (C.DecompRef.decomp ctx.bdc) 0) FALSE TRUE TRUE) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_SOF5 || um == M_SOF6 || um == M_SOF7 || um == M_JPG ||
            um == M_SOF13 || um == M_SOF14 || um == M_SOF15 then
          let _ ← errexit1 dc.err JERR_SOF_UNSUPPORTED um
          return { done := true, ret := .errExit JERR_SOF_UNSUPPORTED }
        else if um == M_SOS then
          match (← get_sos (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true =>
            let dcSos ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
            Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcSos with unreadMarker := 0 }
            return { done := true, ret := .ok JPEG_REACHED_SOS }
        else if um == M_EOI then
          tracems dc.err 1 JTRC_EOI
          Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dc with unreadMarker := 0 }
          return { done := true, ret := .ok JPEG_REACHED_EOI }
        else if um == M_DAC then
          match (← get_dac (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_DHT then
          match (← get_dht (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_DQT then
          match (← get_dqt (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_DRI then
          match (← get_dri (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um ≥ M_APP0 && um ≤ M_APP15 then
          let mrk ← Ptr.load dc.marker
          let idx := (um - M_APP0).toInt.toNat
          match (← callMarkerParser (.ref (C.DecompRef.decomp ctx.bdc) 0) (mrk.processAPPn[idx]!)) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if um == M_COM then
          let mrk ← Ptr.load dc.marker
          match (← callMarkerParser (.ref (C.DecompRef.decomp ctx.bdc) 0) mrk.processCOM) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else if (um ≥ M_RST0 && um ≤ M_RST7) || um == M_TEM then
          tracems1 dc.err 1 JTRC_PARMLESS_MARKER um
        else if um == M_DNL then
          match (← skip_variable (.ref (C.DecompRef.decomp ctx.bdc) 0)) with
          | .errExit code => return { done := true, ret := .errExit code }
          | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
          | .ok true => pure ()
        else
          let _ ← errexit1 dc.err JERR_UNKNOWN_MARKER um
          return { done := true, ret := .errExit JERR_UNKNOWN_MARKER }
        let dcEnd ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
        Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcEnd with unreadMarker := 0 }
        return { done := false, ret := .ok JPEG_SUSPENDED }) hX = .ok (s', h') ∧
      (if s'.done then
        k' = 0 ∧
        match s'.ret with
        | .ok val =>
          (val = JPEG_REACHED_SOS ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
            (∀ mrks', C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size → mrks'[0]!.sawSOF ≠ 0) ∧
            (∀ dcs0 dcs', C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
              C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
              dcs'[0]!.inputScanNumber.toInt = dcs0[0]!.inputScanNumber.toInt + 1 ∧
              dcs'[0]!.entropyStartPass = dcs0[0]!.entropyStartPass ∧
              dcs'[0]!.coefStartInputPass = dcs0[0]!.coefStartInputPass ∧
              dcs'[0]!.coefConsumeData = dcs0[0]!.coefConsumeData ∧
              ScanCompsInRange h' dcs'[0]! ∧
              (PostSofBase hInit dcs0[0]! → MultiScanReady h' dcs'[0]!)) ∧
            (∀ dcs' mrks' srcs' errs', C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
              C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
              C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
              C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
              rmWarnPot errs' srcs' dcs'[0]! + (rmRank dcs'[0]! mrks'[0]! srcs'[0]! : Int) ≤ potBd ∧
              dcs'[0]!.unreadMarker = 0 ∧
              (∀ dcsX mrksX srcsX,
                C.Space.get hX (C.DecompRef.decomp ctx.bdc) = some dcsX → 0 < dcsX.size →
                C.Space.get hX ctx.rmrk = some mrksX → 0 < mrksX.size →
                C.Space.get hX ctx.rs = some srcsX → 0 < srcsX.size →
                rmRank dcs'[0]! mrks'[0]! srcs'[0]! < rmRank dcsX[0]! mrksX[0]! srcsX[0]! ∧
                (isConstEofPtr srcs'[0]!.nextInputByte = false →
                  rmRank dcs'[0]! mrks'[0]! srcs'[0]! + 32 ≤ rmRank dcsX[0]! mrksX[0]! srcsX[0]!)))) ∨
          (val = JPEG_REACHED_EOI ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧ RmFrame ctx hInit h') ∨
          val = JPEG_SUSPENDED
        | .errExit _ => True
      else k' < k0 ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧ RmFrame ctx hInit h' ∧
        (∀ dcs' mrks' srcs' errs', C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
          C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
          C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
          C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
          rmWarnPot errs' srcs' dcs'[0]! + (rmRank dcs'[0]! mrks'[0]! srcs'[0]! : Int) ≤ potBd ∧
          dcs'[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 ∧
          rmRank dcs'[0]! mrks'[0]! srcs'[0]! = k') ∧
        (∀ dcs0 dcs', C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
          C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
          PostSofBase hInit dcs0[0]! → PostSofBase h' dcs'[0]!)) := by
  obtain ⟨dcsX, hgdcX, hszdcX, kerrX, _, _, _, kmrkX, _⟩ := parserEnv_get_dc hpX
  obtain ⟨mrksX, hgmrkX, hszmrkX, _, _, hpcomX, _, hpappX, _⟩ := parserEnv_get_mrk hpX
  obtain ⟨srcsX, hgsrcX, hszsrcX, _⟩ := parserEnv_get_src hpX
  obtain ⟨errsX, hgerrX, hszerrX, _⟩ := parserEnv_get_err hpX
  have hldcX := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcX hszdcX
  have hheadX : ∀ errs0 srcs0, C.Space.get hX ctx.rerr = some errs0 → 0 < errs0.size →
      C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size → warnPotVal errs0 srcs0 + 2 ^ 18 < 2 ^ 63 :=
    fun e0 s0 he0 _ hs0 _ => by
      rw [Option.some.inj (he0.symm.trans hgerrX), Option.some.inj (hs0.symm.trans hgsrcX)]
      have ⟨_, hwp⟩ := hbdX dcsX mrksX srcsX errsX hgdcX hszdcX hgmrkX hszmrkX hgsrcX hszsrcX hgerrX hszerrX
      unfold isConstEofPtr at *; split at hwp <;> omega
  let um := dcsX[0]!.unreadMarker
  have runSof : ∀ (isP isL isA : Int32),
      ∃ (k' : Nat) (s' : ReadMarkersState) (h' : C.Heap),
        C.run (do match (← get_sof (.ref (C.DecompRef.decomp ctx.bdc) 0) isP isL isA) with
                  | .errExit code => return { done := true, ret := .errExit code }
                  | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
                  | .ok true => pure ()
                  let dcEnd ← Ptr.load (.ref (C.DecompRef.decomp ctx.bdc) 0)
                  Ptr.store (.ref (C.DecompRef.decomp ctx.bdc) 0) { dcEnd with unreadMarker := 0 }
                  return { done := false, ret := .ok JPEG_SUSPENDED }) hX = .ok (s', h') ∧
        (if s'.done then
          k' = 0 ∧
          match s'.ret with
          | .ok val => val = JPEG_SUSPENDED
          | .errExit _ => True
        else k' < k0 ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧ RmFrame ctx hInit h' ∧
          (∀ dcs' mrks' srcs' errs', C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
            C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
            C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
            C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
            rmWarnPot errs' srcs' dcs'[0]! + (rmRank dcs'[0]! mrks'[0]! srcs'[0]! : Int) ≤ potBd ∧
            dcs'[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 ∧
            rmRank dcs'[0]! mrks'[0]! srcs'[0]! = k') ∧
          (∀ dcs0 dcs', C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
            C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
            PostSofBase hInit dcs0[0]! → PostSofBase h' dcs'[0]!)) := by
    intro isP isL isA
    obtain ⟨res, h2, hrun, hp2, hstb2, hpost2⟩ := get_sof_parser isP isL isA hpX hsawX (fun e0 s0 he0 hse0 hs0 hss0 => by
      have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
    cases res with
    | errExit code =>
      refine ⟨0, { done := true, ret := .errExit code }, h2, ?_, rfl, trivial⟩
      rw [C.run_bind, hrun]; rfl
    | ok b =>
      cases b with
      | false =>
        refine ⟨0, { done := true, ret := .ok JPEG_SUSPENDED }, h2, ?_, rfl, rfl⟩
        rw [C.run_bind, hrun]; rfl
      | true =>
        rcases hpost2 with ⟨hsaw2, hstr2, hw2⟩
        have hrm2 := rmFrame_of_strong (rmFrameStrong_get_sof isP isL isA hrun)
        have hscan2 : ∀ dcs2, C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
            dcs2[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 := fun dcs2 hgd2 hsz2 => by
          rw [(hrm2.1 dcsX dcs2 hgdcX hszdcX hgd2 hsz2).1]; exact hscanX dcsX hgdcX hszdcX
        have hps02 : ∀ dcs0 dcs2, C.Space.get hInit (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
            C.Space.get h2 (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
            PostSofBase hInit dcs0[0]! → PostSofBase h2 dcs2[0]! := fun dcs0 dcs2 hgd0 hsz0 hgd2 hsz2 hps0 => by
          have hpsX1 := hpsX dcs0 dcsX hgd0 hsz0 hgdcX hszdcX hps0
          have hsawNe : mrksX[0]!.sawSOF ≠ 0 := by
            rcases hpsX1 with ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨rmrk0, mrks0, kr0, hgr0, hszr0, hs0⟩, _⟩
            have := kmrkX.symm.trans kr0; injection this with hrmq
            rw [← hrmq] at hgr0; rw [Option.some.inj (hgmrkX.symm.trans hgr0)]; exact hs0
          exact postSofBase_of_decompHeaderStable hpX hp2 (hstb2 mrksX hgmrkX hszmrkX hsawNe) hgdcX hszdcX hgd2 hsz2 hpsX1
        have hdrop := rmBudget_after_dispatch_step hbdX hpX hp2 hrm2.2
          (fun s0 s1 hs0 hsz0 hs1 hsz1 => srcMono_of_strict (hstr2 s0 s1 hs0 hsz0 hs1 hsz1))
          (fun e0 e1 s0 s1 he0 hse0 he1 hse1 hs0 hszs0 hs1 hszs1 => by
            obtain ⟨wf, wt⟩ := hw2 e0 e1 s0 s1 he0 hse0 he1 hse1 hs0 hszs0 hs1 hszs1
            exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩)
        obtain ⟨k', s', h', hrunCl, hltK, hnd, hp', hsaw', hrm', hbd', hps'⟩ :=
          read_markers_clear_unread hp2 hsaw2 (rmFrame_trans ctx hrmX hrm2 hpX) hps02 hscan2 hdrop
        have hndF : s'.done = false := by cases hc : s'.done <;> simp_all
        refine ⟨k', s', h', ?_, ?_⟩
        · rw [C.run_bind, hrun]; exact hrunCl
        · simp only [hndF, Bool.false_eq_true, ↓reduceIte]; exact ⟨hltK, hp', hsaw', hrm', hbd', hps'⟩
  -- dispatch on um
  by_cases h1 : (um == M_SOI) = true
  · obtain ⟨res, h2, hrun, hp2, hst2, hsm2, hw2⟩ := get_soi_parser hpX
    have hstStep : ∃ res h2, C.run (get_soi (.ref (.decomp ctx.bdc) 0)) hX = .ok (res, h2) ∧
        match res with
        | .ok true =>
          ParserEnv ctx h2 ∧ CompSawZero ctx h2 ∧ RmFrame ctx hX h2 ∧ DecompHeaderStable ctx hX h2 ∧
          (∀ srcs0 srcs', C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
            C.Space.get h2 ctx.rs = some srcs' → 0 < srcs'.size → SrcMono srcs0[0]! srcs'[0]!) ∧
          (∀ errs0 errs' srcs0 srcs',
            C.Space.get hX ctx.rerr = some errs0 → 0 < errs0.size →
            C.Space.get h2 ctx.rerr = some errs' → 0 < errs'.size →
            C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
            C.Space.get h2 ctx.rs = some srcs' → 0 < srcs'.size →
            (isConstEofPtr srcs'[0]!.nextInputByte = false → warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
            (isConstEofPtr srcs'[0]!.nextInputByte = true →
              errs'[0]!.numWarnings.toInt ≤ (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
                else warnPotVal errs0 srcs0) + 2 ^ 17))
        | _ => True := by
      refine ⟨res, h2, hrun, ?_⟩
      cases res with
      | errExit _ => trivial
      | ok b =>
        cases b with
        | false => trivial
        | true =>
          exact ⟨hp2, compSawZero_of_stable hsawX hst2 hpX, rmFrame_of_strong (rmFrameStrong_get_soi hrun),
            hst2, hsm2, fun e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2 => by
              obtain ⟨wf, wt⟩ := hw2 e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
              exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩⟩
    obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
    refine ⟨k', s', h', ?_, ?_⟩
    · rw [C.run_bind, hldcX]; dsimp only; change _ at hrunS; simp only [um, h1, ↓reduceIte]; exact hrunS
    · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
      · exact hsPost
      · rcases hsPost with ⟨rfl, hOk | ⟨c, hErr⟩⟩
        · refine ⟨rfl, ?_⟩; rw [hOk]; exact Or.inr (Or.inr rfl)
        · refine ⟨rfl, ?_⟩; rw [hErr]; trivial
  · rw [Bool.not_eq_true] at h1
    by_cases h2 : (um == M_SOF0 || um == M_SOF1) = true
    · obtain ⟨k', s', h', hrunS, hsPost⟩ := runSof FALSE FALSE FALSE
      refine ⟨k', s', h', ?_, ?_⟩
      · rw [C.run_bind, hldcX]; dsimp only; simp only [um, h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hrunS
      · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
        · exact hsPost
        · rcases hsPost with ⟨rfl, hPost⟩; refine ⟨rfl, ?_⟩
          cases hrt : s'.ret with
          | errExit _ => simp
          | ok val => simp only [hrt] at hPost ⊢; exact Or.inr (Or.inr hPost)
    · rw [Bool.not_eq_true] at h2
      by_cases h3 : (um == M_SOF2) = true
      · obtain ⟨k', s', h', hrunS, hsPost⟩ := runSof TRUE FALSE FALSE
        refine ⟨k', s', h', ?_, ?_⟩
        · rw [C.run_bind, hldcX]; dsimp only; simp only [um, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]; exact hrunS
        · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
          · exact hsPost
          · rcases hsPost with ⟨rfl, hPost⟩; refine ⟨rfl, ?_⟩
            cases hrt : s'.ret with
            | errExit _ => simp
            | ok val => simp only [hrt] at hPost ⊢; exact Or.inr (Or.inr hPost)
      · rw [Bool.not_eq_true] at h3
        by_cases h4 : (um == M_SOF3) = true
        · obtain ⟨k', s', h', hrunS, hsPost⟩ := runSof FALSE TRUE FALSE
          refine ⟨k', s', h', ?_, ?_⟩
          · rw [C.run_bind, hldcX]; dsimp only; simp only [um, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]; exact hrunS
          · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
            · exact hsPost
            · rcases hsPost with ⟨rfl, hPost⟩; refine ⟨rfl, ?_⟩
              cases hrt : s'.ret with
              | errExit _ => simp
              | ok val => simp only [hrt] at hPost ⊢; exact Or.inr (Or.inr hPost)
        · rw [Bool.not_eq_true] at h4
          by_cases h5 : (um == M_SOF9) = true
          · obtain ⟨k', s', h', hrunS, hsPost⟩ := runSof FALSE FALSE TRUE
            refine ⟨k', s', h', ?_, ?_⟩
            · rw [C.run_bind, hldcX]; dsimp only; simp only [um, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]; exact hrunS
            · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
              · exact hsPost
              · rcases hsPost with ⟨rfl, hPost⟩; refine ⟨rfl, ?_⟩
                cases hrt : s'.ret with
                | errExit _ => simp
                | ok val => simp only [hrt] at hPost ⊢; exact Or.inr (Or.inr hPost)
          · rw [Bool.not_eq_true] at h5
            by_cases h6 : (um == M_SOF10) = true
            · obtain ⟨k', s', h', hrunS, hsPost⟩ := runSof TRUE FALSE TRUE
              refine ⟨k', s', h', ?_, ?_⟩
              · rw [C.run_bind, hldcX]; dsimp only; simp only [um, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte]; exact hrunS
              · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                · exact hsPost
                · rcases hsPost with ⟨rfl, hPost⟩; refine ⟨rfl, ?_⟩
                  cases hrt : s'.ret with
                  | errExit _ => simp
                  | ok val => simp only [hrt] at hPost ⊢; exact Or.inr (Or.inr hPost)
            · rw [Bool.not_eq_true] at h6
              by_cases h7 : (um == M_SOF11) = true
              · obtain ⟨k', s', h', hrunS, hsPost⟩ := runSof FALSE TRUE TRUE
                refine ⟨k', s', h', ?_, ?_⟩
                · rw [C.run_bind, hldcX]; dsimp only; simp only [um, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ↓reduceIte]; exact hrunS
                · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                  · exact hsPost
                  · rcases hsPost with ⟨rfl, hPost⟩; refine ⟨rfl, ?_⟩
                    cases hrt : s'.ret with
                    | errExit _ => simp
                    | ok val => simp only [hrt] at hPost ⊢; exact Or.inr (Or.inr hPost)
              · rw [Bool.not_eq_true] at h7
                by_cases h8 : (um == M_SOF5 || um == M_SOF6 || um == M_SOF7 || um == M_JPG ||
                    um == M_SOF13 || um == M_SOF14 || um == M_SOF15) = true
                · obtain ⟨hE, herr_run, _⟩ := errexit1_parser hpX JERR_SOF_UNSUPPORTED um
                  refine ⟨0, { done := true, ret := .errExit JERR_SOF_UNSUPPORTED }, hE, ?_, rfl, trivial⟩
                  rw [C.run_bind, hldcX]; dsimp only
                  simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_eq_true, ↓reduceIte]
                  rw [kerrX, C.run_bind, herr_run]; rfl
                · rw [Bool.not_eq_true] at h8
                  by_cases h9 : (um == M_SOS) = true
                  · obtain ⟨resSos, hSos, hrun2, hp2, hst2, hpost2⟩ := get_sos_parser hpX
                      (fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
                      (fun dcs hgd hsz => by
                        rw [Option.some.inj (hgd.symm.trans hgdcX)]
                        have := hscanX dcsX hgdcX hszdcX; omega)
                    cases resSos with
                    | errExit code =>
                      refine ⟨0, { done := true, ret := .errExit code }, hSos, ?_, rfl, trivial⟩
                      rw [C.run_bind, hldcX]; dsimp only
                      simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.false_eq_true, ↓reduceIte, C.run_bind, hrun2]; rfl
                    | ok b =>
                      cases b with
                      | false =>
                        refine ⟨0, { done := true, ret := .ok JPEG_SUSPENDED }, hSos, ?_, rfl, Or.inr (Or.inr rfl)⟩
                        rw [C.run_bind, hldcX]; dsimp only
                        simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.false_eq_true, ↓reduceIte, C.run_bind, hrun2]; rfl
                      | true =>
                        rcases hpost2 with ⟨hsrc2, hsc2, hw2⟩
                        obtain ⟨dcs2, hgdc2, hszdc2, _⟩ := parserEnv_get_dc hp2
                        obtain ⟨mrks2, hgmrk2, hszmrk2, _⟩ := parserEnv_get_mrk hp2
                        obtain ⟨srcs2, hgsrc2, hszsrc2, _⟩ := parserEnv_get_src hp2
                        obtain ⟨errs2, hgerr2, hszerr2, _⟩ := parserEnv_get_err hp2
                        have hldc2 := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdc2 hszdc2
                        have hro2 : C.Space.ro hSos (C.DecompRef.decomp ctx.bdc) = false := rfl
                        let dcNew := { dcs2[0]! with unreadMarker := 0 }
                        have hstDc2 := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcNew) hgdc2 hro2 hszdc2
                        let h3s := C.Space.put hSos (C.DecompRef.decomp ctx.bdc) (dcs2.set! 0 dcNew)
                        have hp3 : ParserEnv ctx h3s := parserEnv_put_dc_same hp2 hgdc2 hszdc2
                          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                        have hst23 : DecompHeaderStable ctx hSos h3s := by
                          refine ⟨(fun da db hga _ hgb _ => by
                            have ha := Option.some.inj (hga.symm.trans hgdc2)
                            have hg3 : C.Space.get h3s (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dcNew) := by
                              simp [h3s, C.Space.get, C.Space.put]
                            have hb := Option.some.inj (hgb.symm.trans hg3)
                            rw [ha, hb, set0_bang_m dcs2 hszdc2 dcNew]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩),
                            (fun ma mb ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
                            (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
                        have hsaw2 := compSawZero_of_stable hsawX hst2 hpX
                        have hsaw3 := compSawZero_of_stable hsaw2 hst23 hp2
                        refine ⟨0, { done := true, ret := .ok JPEG_REACHED_SOS }, h3s, ?_, rfl, Or.inl ⟨rfl, hp3, hsaw3, ?_, ?_, ?_⟩⟩
                        · rw [C.run_bind, hldcX]; dsimp only
                          simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.false_eq_true, ↓reduceIte, C.run_bind, hrun2]
                          rw [hldc2]; dsimp only; rw [hstDc2]; rfl
                        · intro mrks3 hgm3 hsz3
                          obtain ⟨mrks2', hgm2', _⟩ := parserEnv_get_mrk hp2
                          have hmEq3 : h3s.markers = hSos.markers := rfl
                          have hgm2_3 : C.Space.get hSos ctx.rmrk = some mrks3 := by
                            cases hrm : ctx.rmrk with | marker bm => simpa [C.Space.get, hrm, hmEq3] using hgm3
                          have hs2Eq : mrks3[0]!.sawSOF = mrksX[0]!.sawSOF :=
                            hst2.2.1 mrksX mrks3 hgmrkX hszmrkX hgm2_3 hsz3
                          rw [hs2Eq]
                          exact get_sos_ok_sawSOF hpX hrun2 mrksX hgmrkX hszmrkX
                        · intro dcs0 dcs3 hgd0 hsz0 hgd3 hsz3
                          have hg3 : C.Space.get h3s (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dcNew) := by
                            simp [h3s, C.Space.get, C.Space.put]
                          rw [Option.some.inj (hgd3.symm.trans hg3), set0_bang_m dcs2 hszdc2 dcNew]
                          have hrm0X := hrmX.1 dcs0 dcsX hgd0 hsz0 hgdcX hszdcX
                          have hd2X := hst2.1 dcsX dcs2 hgdcX hszdcX hgdc2 hszdc2
                          obtain ⟨hsc2, hmsc2, hsc2Post⟩ := hsc2 dcsX dcs2 hgdcX hszdcX hgdc2 hszdc2
                          refine ⟨?_, ?_, ?_, ?_, ?_, fun hps0 => ?_⟩
                          · change dcs2[0]!.inputScanNumber.toInt = dcs0[0]!.inputScanNumber.toInt + 1
                            rw [hsc2, hrm0X.1]
                          · exact hd2X.2.2.2.2.2.2.1.trans hrm0X.2.1
                          · exact hd2X.2.2.2.2.2.2.2.1.trans hrm0X.2.2.1
                          · exact hd2X.2.2.2.2.2.2.2.2.trans hrm0X.2.2.2
                          · obtain ⟨sc1, sc2, scSz, hsci⟩ := hmsc2
                            refine ⟨sc1, sc2, scSz, fun i hi => ?_⟩
                            obtain ⟨rcp, offI, cs, h1i, h2i, h3i, h4i, h5i⟩ := hsci i hi
                            exact ⟨rcp, offI, cs, h1i, (by cases rcp; exact h2i), h3i, h4i, h5i⟩
                          · have hpsX0 := hpsX dcs0 dcsX hgd0 hsz0 hgdcX hszdcX hps0
                            have hm2 := hsc2Post hpsX0
                            exact multiScanReady_put_dc_unread dcs2 hgdc2 hszdc2 hm2
                        · intro dcs3 mrks3 srcs3 errs3 hgd3 _ hgm3 _ hgs3 _ hge3 _
                          have hg3 : C.Space.get h3s (C.DecompRef.decomp ctx.bdc) = some (dcs2.set! 0 dcNew) := by
                            simp [h3s, C.Space.get, C.Space.put]
                          rw [Option.some.inj (hgd3.symm.trans hg3), set0_bang_m dcs2 hszdc2 dcNew]
                          have hmrkM : MrkSoiStrong ctx hX hSos := mrkSoiStrong_get_sos hrun2
                          have hmMrk' : ∀ ma mb, C.Space.get hX ctx.rmrk = some ma → 0 < ma.size →
                              C.Space.get hSos ctx.rmrk = some mb → 0 < mb.size → ma[0]!.sawSOI ≠ 0 → mb[0]!.sawSOI ≠ 0 := by
                            intro ma mb hma hszma hmb _ hne
                            obtain ⟨mc, hmc, _, hf⟩ := hmrkM ma hma hszma
                            rw [Option.some.inj (hmb.symm.trans hmc)]; exact hf hne
                          have hwOk' : ∀ errs0 errs' srcs0 srcs',
                              C.Space.get hX ctx.rerr = some errs0 → 0 < errs0.size →
                              C.Space.get hSos ctx.rerr = some errs' → 0 < errs'.size →
                              C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
                              C.Space.get hSos ctx.rs = some srcs' → 0 < srcs'.size →
                              (isConstEofPtr srcs'[0]!.nextInputByte = false → warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
                              (isConstEofPtr srcs'[0]!.nextInputByte = true →
                                errs'[0]!.numWarnings.toInt ≤ (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
                                  else warnPotVal errs0 srcs0) + 2 ^ 17) := fun e0 e' s0 s' he0 hse0 he' hse' hs0 hss0 hs' hss' => by
                            obtain ⟨wf, wt⟩ := hw2 e0 e' s0 s' he0 hse0 he' hse' hs0 hss0 hs' hss'
                            exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩
                          have hmSrc' : ∀ srcs0 srcs', C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
                              C.Space.get hSos ctx.rs = some srcs' → 0 < srcs'.size → SrcMono srcs0[0]! srcs'[0]! :=
                            fun s0 s' hs0 hss0 hs' hss' => srcMono_of_strict (hsrc2 s0 s' hs0 hss0 hs' hss').1
                          have hdrop := rmBudget_after_dispatch_step hbdX hpX hp2 hmMrk' hmSrc' hwOk'
                          have hgm2' : C.Space.get hSos ctx.rmrk = some mrks3 := by
                            cases hrmk : ctx.rmrk with | marker bm => simpa [C.Space.get, h3s, C.Space.put, hrmk] using hgm3
                          have hgs2' : C.Space.get hSos ctx.rs = some srcs3 := by
                            cases hrs : ctx.rs with | src bs => simpa [C.Space.get, h3s, C.Space.put, hrs] using hgs3
                          have hge2' : C.Space.get hSos ctx.rerr = some errs3 := by
                            cases herr : ctx.rerr with | err be => simpa [C.Space.get, h3s, C.Space.put, herr] using hge3
                          refine ⟨(hdrop dcs2 mrks3 srcs3 errs3 hgdc2 hszdc2 hgm2' (by assumption) hgs2' (by assumption) hge2' (by assumption)).1, rfl, ?_⟩
                          intro dcsX' mrksX' srcsX' hgdX' _ hgmX' _ hgsX' _
                          rw [Option.some.inj (hgdX'.symm.trans hgdcX), Option.some.inj (hgmX'.symm.trans hgmrkX),
                            Option.some.inj (hgsX'.symm.trans hgsrcX)]
                          have hsSrc := hsrc2 srcsX srcs3 hgsrcX hszsrcX hgs2' (by assumption)
                          have hsoiLe : (if mrks3[0]!.sawSOI == 0 then 2 else 0) ≤ (if mrksX[0]!.sawSOI == 0 then 2 else 0) := by
                            by_cases hs0 : mrksX[0]!.sawSOI = 0
                            · simp only [hs0, beq_self_eq_true, ↓reduceIte]; split <;> omega
                            · have hne3 := hmMrk' mrksX mrks3 hgmrkX hszmrkX hgm2' (by assumption) hs0
                              have hfX : (mrksX[0]!.sawSOI == 0) = false := by simp [hs0]
                              have hf3 : (mrks3[0]!.sawSOI == 0) = false := by simp [hne3]
                              simp [hfX, hf3]
                          have humNew0 : (dcNew.unreadMarker != 0) = false := rfl
                          have humXne : (dcsX[0]!.unreadMarker != 0) = true := by
                            have humEq : dcsX[0]!.unreadMarker = M_SOS := by simpa [um] using h9
                            simp [humEq]; decide
                          constructor
                          · have hwLe := rmSrcWeight_mono (srcMono_of_strict hsSrc.1)
                            change rmRank dcNew mrks3[0]! srcs3[0]! < rmRank dcsX[0]! mrksX[0]! srcsX[0]!
                            unfold rmRank; simp only [humNew0, humXne, Bool.false_eq_true, ↓reduceIte]
                            omega
                          · intro hnf3
                            have hnfX : isConstEofPtr srcsX[0]!.nextInputByte = false := by
                              cases hc : isConstEofPtr srcsX[0]!.nextInputByte
                              · rfl
                              · rw [hsSrc.1.1 hc] at hnf3; cases hnf3
                            have hbibDrop : srcs3[0]!.bytesInBuffer.toNat + 8 ≤ srcsX[0]!.bytesInBuffer.toNat := by
                              rcases hsSrc.2 with hce3 | hle3
                              · rw [hce3] at hnf3; cases hnf3
                              · exact hle3
                            change rmRank dcNew mrks3[0]! srcs3[0]! + 32 ≤ rmRank dcsX[0]! mrksX[0]! srcsX[0]!
                            unfold rmRank rmSrcWeight
                            simp only [hnf3, hnfX, humNew0, humXne, Bool.false_eq_true, ↓reduceIte]
                            omega
                  · rw [Bool.not_eq_true] at h9
                    by_cases h10 : (um == M_EOI) = true
                    · obtain ⟨hTr, hrunTr, hpTr, hdTr, hmrTr, _, _, hcpTr, _, _, _, _, _, hnwTr⟩ :=
                        tracems_nonneg_parser hpX 1 JTRC_EOI (by decide)
                      have hgdcTr : C.Space.get hTr (C.DecompRef.decomp ctx.bdc) = some dcsX := by
                        simp only [C.Space.get, hdTr] at hgdcX ⊢; exact hgdcX
                      have hroTr : C.Space.ro hTr (C.DecompRef.decomp ctx.bdc) = false := rfl
                      let dcEnd := { dcsX[0]! with unreadMarker := 0 }
                      have hstTr := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcEnd) hgdcTr hroTr hszdcX
                      let h2e := C.Space.put hTr (C.DecompRef.decomp ctx.bdc) (dcsX.set! 0 dcEnd)
                      have hp2 : ParserEnv ctx h2e := parserEnv_put_dc_same hpTr hgdcTr hszdcX
                        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                      have hstTr2 : DecompHeaderStable ctx hTr h2e := by
                        refine ⟨(fun da db hga _ hgb _ => by
                          have ha := Option.some.inj (hga.symm.trans hgdcTr)
                          have hg2 : C.Space.get h2e (C.DecompRef.decomp ctx.bdc) = some (dcsX.set! 0 dcEnd) := by
                            simp [h2e, C.Space.get, C.Space.put]
                          have hb := Option.some.inj (hgb.symm.trans hg2)
                          rw [ha, hb, set0_bang_m dcsX hszdcX dcEnd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩),
                          (fun ma mb ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
                          (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
                      have hstXTr : DecompHeaderStable ctx hX hTr :=
                        decompHeaderStable_of_same hdTr hmrTr hcpTr
                      have hsaw2 := compSawZero_of_stable hsawX (decompHeaderStable_trans hpX hpTr hstXTr hstTr2) hpX
                      have hrmX2 : RmFrame ctx hX h2e := by
                        refine ⟨fun da db hga _ hgb _ => ?_, fun ma mb hma _ hmb _ hm => ?_⟩
                        · have ha := Option.some.inj (hga.symm.trans hgdcX)
                          have hg2 : C.Space.get h2e (C.DecompRef.decomp ctx.bdc) = some (dcsX.set! 0 dcEnd) := by
                            simp [h2e, C.Space.get, C.Space.put]
                          have hb := Option.some.inj (hgb.symm.trans hg2)
                          rw [ha, hb, set0_bang_m dcsX hszdcX dcEnd]; exact ⟨rfl, rfl, rfl, rfl⟩
                        · simp only [h2e, C.Space.get, C.Space.put, hmrTr] at hmb
                          rw [Option.some.inj (hmb.symm.trans hma)]; exact hm
                      refine ⟨0, { done := true, ret := .ok JPEG_REACHED_EOI }, h2e, ?_, rfl, Or.inr (Or.inl ⟨rfl, hp2, hsaw2, rmFrame_trans ctx hrmX hrmX2 hpX⟩)⟩
                      · rw [C.run_bind, hldcX]; dsimp only
                        simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ↓reduceIte]
                        have htrX : C.run (tracems dcsX[0]!.err 1 JTRC_EOI) hX = .ok ((), hTr) := by
                          rw [kerrX]; exact hrunTr
                        rw [C.run_bind, htrX]; dsimp only; rw [C.run_bind, hstTr]; rfl
                    · rw [Bool.not_eq_true] at h10
                      let ParserStepProp (res : C.JpegRes Bool) (h2 : C.Heap) : Prop :=
                        match res with
                        | .ok true =>
                          ParserEnv ctx h2 ∧ CompSawZero ctx h2 ∧ RmFrame ctx hX h2 ∧ DecompHeaderStable ctx hX h2 ∧
                          (∀ srcs0 srcs', C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
                            C.Space.get h2 ctx.rs = some srcs' → 0 < srcs'.size → SrcMono srcs0[0]! srcs'[0]!) ∧
                          (∀ errs0 errs' srcs0 srcs',
                            C.Space.get hX ctx.rerr = some errs0 → 0 < errs0.size →
                            C.Space.get h2 ctx.rerr = some errs' → 0 < errs'.size →
                            C.Space.get hX ctx.rs = some srcs0 → 0 < srcs0.size →
                            C.Space.get h2 ctx.rs = some srcs' → 0 < srcs'.size →
                            (isConstEofPtr srcs'[0]!.nextInputByte = false → warnPotVal errs' srcs' ≤ warnPotVal errs0 srcs0 + 1) ∧
                            (isConstEofPtr srcs'[0]!.nextInputByte = true →
                              errs'[0]!.numWarnings.toInt ≤ (if isConstEofPtr srcs0[0]!.nextInputByte then errs0[0]!.numWarnings.toInt
                                else warnPotVal errs0 srcs0) + 2 ^ 17))
                        | _ => True
                      by_cases h11 : (um == M_DAC) = true
                      · obtain ⟨res, h2s, hrun, hp2, hst2, hpost⟩ := get_dac_parser hpX
                          (fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
                        have hstStep : ∃ res h2s, C.run (get_dac (.ref (.decomp ctx.bdc) 0)) hX = .ok (res, h2s) ∧
                            ParserStepProp res h2s := by
                          refine ⟨res, h2s, hrun, ?_⟩
                          cases res with
                          | errExit _ => trivial
                          | ok b =>
                            cases b with
                            | false => trivial
                            | true =>
                              rcases hpost with ⟨hsm2, hw2⟩
                              exact ⟨hp2, compSawZero_of_stable hsawX hst2 hpX, rmFrame_of_strong (rmFrameStrong_get_dac hrun),
                                hst2, fun s0 s2 hs0 hss0 hs2 hss2 => srcMono_of_strict (hsm2 s0 s2 hs0 hss0 hs2 hss2),
                                fun e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2 => by
                                  obtain ⟨wf, wt⟩ := hw2 e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
                                  exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩⟩
                        obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
                        refine ⟨k', s', h', ?_, ?_⟩
                        · rw [C.run_bind, hldcX]; dsimp only
                          simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, Bool.false_eq_true, ↓reduceIte]; exact hrunS
                        · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                          · exact hsPost
                          · rcases hsPost with ⟨hs1, hret⟩
                            rcases hret with hret | ⟨c, hret⟩ <;> simp [hs1, hret]
                      · rw [Bool.not_eq_true] at h11
                        by_cases h12 : (um == M_DHT) = true
                        · obtain ⟨res, h2s, hrun, hp2, hst2, hpost⟩ := get_dht_parser hpX
                            (fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
                          have hstStep : ∃ res h2s, C.run (get_dht (.ref (.decomp ctx.bdc) 0)) hX = .ok (res, h2s) ∧
                              ParserStepProp res h2s := by
                            refine ⟨res, h2s, hrun, ?_⟩
                            cases res with
                            | errExit _ => trivial
                            | ok b =>
                              cases b with
                              | false => trivial
                              | true =>
                                rcases hpost with ⟨hsm2, hw2⟩
                                exact ⟨hp2, compSawZero_of_stable hsawX hst2 hpX, rmFrame_of_strong (rmFrameStrong_get_dht hrun),
                                  hst2, fun s0 s2 hs0 hss0 hs2 hss2 => srcMono_of_strict (hsm2 s0 s2 hs0 hss0 hs2 hss2),
                                  fun e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2 => by
                                    obtain ⟨wf, wt⟩ := hw2 e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
                                    exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩⟩
                          obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
                          refine ⟨k', s', h', ?_, ?_⟩
                          · rw [C.run_bind, hldcX]; dsimp only
                            simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, Bool.false_eq_true, ↓reduceIte]; exact hrunS
                          · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                            · exact hsPost
                            · rcases hsPost with ⟨hs1, hret⟩
                              rcases hret with hret | ⟨c, hret⟩ <;> simp [hs1, hret]
                        · rw [Bool.not_eq_true] at h12
                          by_cases h13 : (um == M_DQT) = true
                          · obtain ⟨res, h2s, hrun, hp2, hst2, hpost⟩ := get_dqt_parser hpX
                              (fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
                            have hstStep : ∃ res h2s, C.run (get_dqt (.ref (.decomp ctx.bdc) 0)) hX = .ok (res, h2s) ∧
                                ParserStepProp res h2s := by
                              refine ⟨res, h2s, hrun, ?_⟩
                              cases res with
                              | errExit _ => trivial
                              | ok b =>
                                cases b with
                                | false => trivial
                                | true =>
                                  rcases hpost with ⟨hsm2, hw2⟩
                                  exact ⟨hp2, compSawZero_of_stable hsawX hst2 hpX, rmFrame_of_strong (rmFrameStrong_get_dqt hrun),
                                    hst2, fun s0 s2 hs0 hss0 hs2 hss2 => srcMono_of_strict (hsm2 s0 s2 hs0 hss0 hs2 hss2),
                                    fun e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2 => by
                                      obtain ⟨wf, wt⟩ := hw2 e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
                                      exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩⟩
                            obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
                            refine ⟨k', s', h', ?_, ?_⟩
                            · rw [C.run_bind, hldcX]; dsimp only
                              simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, Bool.false_eq_true, ↓reduceIte]; exact hrunS
                            · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                              · exact hsPost
                              · rcases hsPost with ⟨hs1, hret⟩
                                rcases hret with hret | ⟨c, hret⟩ <;> simp [hs1, hret]
                          · rw [Bool.not_eq_true] at h13
                            by_cases h14 : (um == M_DRI) = true
                            · obtain ⟨res, h2s, hrun, hp2, hst2, hpost⟩ := get_dri_parser hpX
                                (fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
                              have hstStep : ∃ res h2s, C.run (get_dri (.ref (.decomp ctx.bdc) 0)) hX = .ok (res, h2s) ∧
                                  ParserStepProp res h2s := by
                                refine ⟨res, h2s, hrun, ?_⟩
                                cases res with
                                | errExit _ => trivial
                                | ok b =>
                                  cases b with
                                  | false => trivial
                                  | true =>
                                    rcases hpost with ⟨hsm2, hw2⟩
                                    exact ⟨hp2, compSawZero_of_stable hsawX hst2 hpX, rmFrame_of_strong (rmFrameStrong_get_dri hrun),
                                      hst2, fun s0 s2 hs0 hss0 hs2 hss2 => srcMono_of_strict (hsm2 s0 s2 hs0 hss0 hs2 hss2),
                                      fun e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2 => by
                                        obtain ⟨wf, wt⟩ := hw2 e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
                                        exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩⟩
                              obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
                              refine ⟨k', s', h', ?_, ?_⟩
                              · rw [C.run_bind, hldcX]; dsimp only
                                simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.false_eq_true, ↓reduceIte]; exact hrunS
                              · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                                · exact hsPost
                                · rcases hsPost with ⟨hs1, hret⟩
                                  rcases hret with hret | ⟨c, hret⟩ <;> simp [hs1, hret]
                            · rw [Bool.not_eq_true] at h14
                              by_cases h15 : (decide (um ≥ M_APP0) && decide (um ≤ M_APP15)) = true
                              · have hlmrkX := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrkX hszmrkX
                                have hidx := appn_idx_lt_16 h15
                                have hfnApp := hpappX (um - M_APP0).toInt.toNat hidx
                                obtain ⟨res, h2s, hrun, hp2, hst2, hpost⟩ := callMarkerParser_parser hpX _ hfnApp
                                  (fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
                                have hstStep : ∃ res h2s, C.run (callMarkerParser (.ref (.decomp ctx.bdc) 0) (mrksX[0]!.processAPPn[(um - M_APP0).toInt.toNat]!)) hX = .ok (res, h2s) ∧
                                    ParserStepProp res h2s := by
                                  refine ⟨res, h2s, hrun, ?_⟩
                                  cases res with
                                  | errExit _ => trivial
                                  | ok b =>
                                    cases b with
                                    | false => trivial
                                    | true =>
                                      rcases hpost with ⟨hsm2, hw2⟩
                                      exact ⟨hp2, compSawZero_of_stable hsawX hst2 hpX, rmFrame_of_strong (rmFrameStrong_callMarkerParser _ hrun),
                                        hst2, hsm2,
                                        fun e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2 => by
                                          obtain ⟨wf, wt⟩ := hw2 e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
                                          exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩⟩
                                obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
                                refine ⟨k', s', h', ?_, ?_⟩
                                · rw [C.run_bind, hldcX]; dsimp only
                                  simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.false_eq_true, ↓reduceIte]
                                  have h15' : (um ≥ M_APP0 && um ≤ M_APP15) = true := h15
                                  simp only [um, h15', ↓reduceIte]; rw [kmrkX, C.run_bind, hlmrkX]; exact hrunS
                                · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                                  · exact hsPost
                                  · rcases hsPost with ⟨hs1, hret⟩
                                    rcases hret with hret | ⟨c, hret⟩ <;> simp [hs1, hret]
                              · rw [Bool.not_eq_true] at h15
                                by_cases h16 : (um == M_COM) = true
                                · have hlmrkX := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrkX hszmrkX
                                  have hfnCom : mrksX[0]!.processCOM = .fn "save_marker" ∨
                                      mrksX[0]!.processCOM = .fn "skip_variable" ∨
                                      mrksX[0]!.processCOM = .fn "get_interesting_appn" :=
                                    Or.elim hpcomX Or.inl (fun h => Or.inr (Or.inl h))
                                  obtain ⟨res, h2s, hrun, hp2, hst2, hpost⟩ := callMarkerParser_parser hpX _ hfnCom
                                    (fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
                                  have hstStep : ∃ res h2s, C.run (callMarkerParser (.ref (.decomp ctx.bdc) 0) mrksX[0]!.processCOM) hX = .ok (res, h2s) ∧
                                      ParserStepProp res h2s := by
                                    refine ⟨res, h2s, hrun, ?_⟩
                                    cases res with
                                    | errExit _ => trivial
                                    | ok b =>
                                      cases b with
                                      | false => trivial
                                      | true =>
                                        rcases hpost with ⟨hsm2, hw2⟩
                                        exact ⟨hp2, compSawZero_of_stable hsawX hst2 hpX, rmFrame_of_strong (rmFrameStrong_callMarkerParser _ hrun),
                                          hst2, hsm2,
                                          fun e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2 => by
                                            obtain ⟨wf, wt⟩ := hw2 e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
                                            exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩⟩
                                  obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
                                  refine ⟨k', s', h', ?_, ?_⟩
                                  · rw [C.run_bind, hldcX]; dsimp only
                                    simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.false_eq_true, ↓reduceIte]
                                    have h15f : (um ≥ M_APP0 && um ≤ M_APP15) = false := h15
                                    simp only [um, h15f, h16, Bool.false_eq_true, ↓reduceIte]; rw [kmrkX, C.run_bind, hlmrkX]; exact hrunS
                                  · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                                    · exact hsPost
                                    · rcases hsPost with ⟨hs1, hret⟩
                                      rcases hret with hret | ⟨c, hret⟩ <;> simp [hs1, hret]
                                · rw [Bool.not_eq_true] at h16
                                  by_cases h17 : ((decide (um ≥ M_RST0) && decide (um ≤ M_RST7)) || um == M_TEM) = true
                                  · obtain ⟨hTr, hrunTr, hpTr, hdTr, hmrTr, hsrTr, _, hcpTr, _, _, _, _, _, hnwTr⟩ :=
                                      tracems1_nonneg_parser hpX 1 JTRC_PARMLESS_MARKER um (by decide)
                                    have hstStep : ∃ res h2s, C.run (do tracems1 dcsX[0]!.err 1 JTRC_PARMLESS_MARKER um; pure (JpegRes.ok true)) hX = .ok (res, h2s) ∧
                                        ParserStepProp res h2s := by
                                      refine ⟨.ok true, hTr, (by rw [kerrX, C.run_bind, hrunTr]; rfl), ?_⟩
                                      have hstTr := @decompHeaderStable_of_same ctx hX hTr hdTr hmrTr hcpTr
                                      refine ⟨hpTr, compSawZero_of_stable hsawX hstTr hpX, ?_, hstTr, ?_, ?_⟩
                                      · exact ⟨fun da db ha _ hb _ => by
                                          simp only [C.Space.get, hdTr] at hb
                                          rw [Option.some.inj (hb.symm.trans ha)]; exact ⟨rfl, rfl, rfl, rfl⟩,
                                          fun ma mb ha _ hb _ hm => by
                                          simp only [C.Space.get, hmrTr] at hb
                                          rw [Option.some.inj (hb.symm.trans ha)]; exact hm⟩
                                      · intro s0 s2 hs0 _ hs2 _
                                        simp only [C.Space.get, hsrTr] at hs2
                                        rw [Option.some.inj (hs2.symm.trans hs0)]
                                        exact ⟨fun h => h, fun _ => Or.inr (Nat.le_refl _)⟩
                                      · intro e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
                                        obtain ⟨_, hnw⟩ := hnwTr.2 e0 e2 he0 hse0 he2
                                        have hsEq : s2 = s0 := Option.some.inj (hs2.symm.trans (by simp only [C.Space.get, hsrTr]; exact hs0))
                                        subst hsEq
                                        refine ⟨fun _ => ?_, fun _ => ?_⟩
                                        · unfold warnPotVal; rw [hnw]; omega
                                        · rw [hnw]; split <;> omega
                                    obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
                                    refine ⟨k', s', h', ?_, ?_⟩
                                    · rw [C.run_bind, hldcX]; dsimp only
                                      simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.false_eq_true, ↓reduceIte]
                                      have h15f : (um ≥ M_APP0 && um ≤ M_APP15) = false := h15
                                      have h17' : ((um ≥ M_RST0 && um ≤ M_RST7) || um == M_TEM) = true := h17
                                      simp only [um, h15f, h16, h17', Bool.false_eq_true, ↓reduceIte]
                                      have htr1 : C.run (tracems1 dcsX[0]!.err 1 JTRC_PARMLESS_MARKER dcsX[0]!.unreadMarker) hX = .ok ((), hTr) := by
                                        rw [kerrX]; exact hrunTr
                                      have htr2 : C.run (do tracems1 dcsX[0]!.err 1 JTRC_PARMLESS_MARKER um; pure (JpegRes.ok true)) hX = .ok (.ok true, hTr) := by
                                        rw [C.run_bind, htr1]; rfl
                                      rw [C.run_bind, htr1]
                                      rw [C.run_bind, htr2] at hrunS
                                      exact hrunS
                                    · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                                      · exact hsPost
                                      · rcases hsPost with ⟨hs1, hret⟩
                                        rcases hret with hret | ⟨c, hret⟩ <;> simp [hs1, hret]
                                  · rw [Bool.not_eq_true] at h17
                                    by_cases h18 : (um == M_DNL) = true
                                    · obtain ⟨res, h2s, hrun, hp2, hst2, hpost⟩ := skip_variable_parser hpX
                                        (fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega)
                                      have hstStep : ∃ res h2s, C.run (skip_variable (.ref (.decomp ctx.bdc) 0)) hX = .ok (res, h2s) ∧
                                          ParserStepProp res h2s := by
                                        refine ⟨res, h2s, hrun, ?_⟩
                                        cases res with
                                        | errExit _ => trivial
                                        | ok b =>
                                          cases b with
                                          | false => trivial
                                          | true =>
                                            rcases hpost with ⟨hsm2, hw2⟩
                                            exact ⟨hp2, compSawZero_of_stable hsawX hst2 hpX, rmFrame_of_strong (rmFrameStrong_skip_variable hrun),
                                              hst2, fun s0 s2 hs0 hss0 hs2 hss2 => srcMono_of_strict (hsm2 s0 s2 hs0 hss0 hs2 hss2),
                                              fun e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2 => by
                                                obtain ⟨wf, wt⟩ := hw2 e0 e2 s0 s2 he0 hse0 he2 hse2 hs0 hss0 hs2 hss2
                                                exact ⟨fun hnf => Int.le_trans (wf hnf) (by omega), fun ht => Int.le_trans (wt ht) (by omega)⟩⟩
                                      obtain ⟨k', s', h', hrunS, hsPost⟩ := read_markers_parser_step _ hstStep hpX hrmX hscanX hpsX hbdX
                                      refine ⟨k', s', h', ?_, ?_⟩
                                      · rw [C.run_bind, hldcX]; dsimp only
                                        simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.false_eq_true, ↓reduceIte]
                                        have h15f : (um ≥ M_APP0 && um ≤ M_APP15) = false := h15
                                        have h17f : ((um ≥ M_RST0 && um ≤ M_RST7) || um == M_TEM) = false := h17
                                        simp only [um, h15f, h16, h17f, h18, Bool.false_eq_true, ↓reduceIte]; exact hrunS
                                      · cases hs : s'.done <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsPost ⊢
                                        · exact hsPost
                                        · rcases hsPost with ⟨hs1, hret⟩
                                          rcases hret with hret | ⟨c, hret⟩ <;> simp [hs1, hret]
                                    · rw [Bool.not_eq_true] at h18
                                      obtain ⟨hE, herr_run, _⟩ := errexit1_parser hpX JERR_UNKNOWN_MARKER um
                                      refine ⟨0, { done := true, ret := .errExit JERR_UNKNOWN_MARKER }, hE, ?_, rfl, trivial⟩
                                      rw [C.run_bind, hldcX]; dsimp only
                                      simp only [um, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.false_eq_true, ↓reduceIte]
                                      have h15f : (um ≥ M_APP0 && um ≤ M_APP15) = false := h15
                                      have h17f : ((um ≥ M_RST0 && um ≤ M_RST7) || um == M_TEM) = false := h17
                                      simp only [um, h15f, h16, h17f, h18, Bool.false_eq_true, ↓reduceIte]
                                      rw [kerrX, C.run_bind, herr_run]; rfl


theorem read_markers_parser {ctx : IoCtx} {h : C.Heap}
    (hp : ParserEnv ctx h) (hsaw0 : CompSawZero ctx h)
    (potBd : Int)
    (hpotBd : ∀ dcs mrks srcs errs,
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      C.Space.get h ctx.rmrk = some mrks → 0 < mrks.size →
      C.Space.get h ctx.rs = some srcs → 0 < srcs.size →
      C.Space.get h ctx.rerr = some errs → 0 < errs.size →
      rmWarnPot errs srcs dcs[0]! + (rmRank dcs[0]! mrks[0]! srcs[0]! : Int) ≤ potBd)
    (hpotHi : potBd + 2 ^ 23 < 2 ^ 63)
    (hscanBd : ∀ dcs,
      C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
      dcs[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31) :
    ∃ res h',
      C.run (read_markers (.ref (.decomp ctx.bdc) 0)) h = .ok (res, h') ∧
      match res with
      | .ok val =>
        (val = JPEG_REACHED_SOS ∧
          ParserEnv ctx h' ∧
          CompSawZero ctx h' ∧
          (∀ mrks', C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size → mrks'[0]!.sawSOF ≠ 0) ∧
          (∀ dcs0 dcs',
            C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
            C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
            dcs'[0]!.inputScanNumber.toInt = dcs0[0]!.inputScanNumber.toInt + 1 ∧
            dcs'[0]!.entropyStartPass = dcs0[0]!.entropyStartPass ∧
            dcs'[0]!.coefStartInputPass = dcs0[0]!.coefStartInputPass ∧
            dcs'[0]!.coefConsumeData = dcs0[0]!.coefConsumeData ∧
            ScanCompsInRange h' dcs'[0]! ∧
            (PostSofBase h dcs0[0]! → MultiScanReady h' dcs'[0]!)) ∧
          (∀ dcs' mrks' srcs' errs' dcs0 mrks0 srcs0,
            C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
            C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
            C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
            C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
            C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
            C.Space.get h ctx.rmrk = some mrks0 → 0 < mrks0.size →
            C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
            rmWarnPot errs' srcs' dcs'[0]! + (rmRank dcs'[0]! mrks'[0]! srcs'[0]! : Int) ≤ potBd ∧
            dcs'[0]!.unreadMarker = 0 ∧
            rmRank dcs'[0]! mrks'[0]! srcs'[0]! < rmRank dcs0[0]! mrks0[0]! srcs0[0]! ∧
            (isConstEofPtr srcs'[0]!.nextInputByte = false →
              isConstEofPtr srcs0[0]!.nextInputByte = false ∧
              srcs'[0]!.bytesInBuffer.toNat + 8 ≤ srcs0[0]!.bytesInBuffer.toNat))) ∨
        (val = JPEG_REACHED_EOI ∧
          ParserEnv ctx h' ∧
          CompSawZero ctx h' ∧
          RmFrame ctx h h') ∨
        val = JPEG_SUSPENDED
      | .errExit _ => True := by
  let cinfo : C.DecompPtr := .ref (C.DecompRef.decomp ctx.bdc) 0
  let condFn : ReadMarkersState → C.M (Bool × ReadMarkersState) :=
    fun (s : ReadMarkersState) => pure (!s.done, s)
  let dispatch : C.DecompPtr → C.M ReadMarkersState := fun cinfo => do
    let dc ← Ptr.load cinfo
    let um := dc.unreadMarker
    if um == M_SOI then
      match (← get_soi cinfo) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_SOF0 || um == M_SOF1 then
      match (← get_sof cinfo FALSE FALSE FALSE) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_SOF2 then
      match (← get_sof cinfo TRUE FALSE FALSE) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_SOF3 then
      match (← get_sof cinfo FALSE TRUE FALSE) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_SOF9 then
      match (← get_sof cinfo FALSE FALSE TRUE) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_SOF10 then
      match (← get_sof cinfo TRUE FALSE TRUE) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_SOF11 then
      match (← get_sof cinfo FALSE TRUE TRUE) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_SOF5 || um == M_SOF6 || um == M_SOF7 || um == M_JPG ||
        um == M_SOF13 || um == M_SOF14 || um == M_SOF15 then
      let _ ← errexit1 dc.err JERR_SOF_UNSUPPORTED um
      return { done := true, ret := .errExit JERR_SOF_UNSUPPORTED }
    else if um == M_SOS then
      match (← get_sos cinfo) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true =>
        let dcSos ← Ptr.load cinfo
        Ptr.store cinfo { dcSos with unreadMarker := 0 }
        return { done := true, ret := .ok JPEG_REACHED_SOS }
    else if um == M_EOI then
      tracems dc.err 1 JTRC_EOI
      Ptr.store cinfo { dc with unreadMarker := 0 }
      return { done := true, ret := .ok JPEG_REACHED_EOI }
    else if um == M_DAC then
      match (← get_dac cinfo) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_DHT then
      match (← get_dht cinfo) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_DQT then
      match (← get_dqt cinfo) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_DRI then
      match (← get_dri cinfo) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um ≥ M_APP0 && um ≤ M_APP15 then
      let mrk ← Ptr.load dc.marker
      let idx := (um - M_APP0).toInt.toNat
      match (← callMarkerParser cinfo (mrk.processAPPn[idx]!)) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if um == M_COM then
      let mrk ← Ptr.load dc.marker
      match (← callMarkerParser cinfo mrk.processCOM) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else if (um ≥ M_RST0 && um ≤ M_RST7) || um == M_TEM then
      tracems1 dc.err 1 JTRC_PARMLESS_MARKER um
    else if um == M_DNL then
      match (← skip_variable cinfo) with
      | .errExit code => return { done := true, ret := .errExit code }
      | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
      | .ok true => pure ()
    else
      let _ ← errexit1 dc.err JERR_UNKNOWN_MARKER um
      return { done := true, ret := .errExit JERR_UNKNOWN_MARKER }
    let dcEnd ← Ptr.load cinfo
    Ptr.store cinfo { dcEnd with unreadMarker := 0 }
    return { done := false, ret := .ok JPEG_SUSPENDED }
  let bodyFn : ReadMarkersState → C.M ReadMarkersState := fun (_ : ReadMarkersState) => do
    let dc0 ← Ptr.load cinfo
    if dc0.unreadMarker == 0 then
      let mrk0 ← Ptr.load dc0.marker
      if mrk0.sawSOI == 0 then
        match (← first_marker cinfo) with
        | .errExit code => return { done := true, ret := .errExit code }
        | .ok false => return { done := true, ret := .ok JPEG_SUSPENDED }
        | .ok true => pure ()
      else
        let nm ← next_marker cinfo
        if nm == 0 then
          return { done := true, ret := .ok JPEG_SUSPENDED }
    dispatch cinfo
  let DoneSpec (ret : C.JpegRes Int32) (hx : C.Heap) : Prop :=
    match ret with
    | .ok val =>
      (val = JPEG_REACHED_SOS ∧
        ParserEnv ctx hx ∧
        CompSawZero ctx hx ∧
        (∀ mrks', C.Space.get hx ctx.rmrk = some mrks' → 0 < mrks'.size → mrks'[0]!.sawSOF ≠ 0) ∧
        (∀ dcs0 dcs',
          C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
          C.Space.get hx (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
          dcs'[0]!.inputScanNumber.toInt = dcs0[0]!.inputScanNumber.toInt + 1 ∧
          dcs'[0]!.entropyStartPass = dcs0[0]!.entropyStartPass ∧
          dcs'[0]!.coefStartInputPass = dcs0[0]!.coefStartInputPass ∧
          dcs'[0]!.coefConsumeData = dcs0[0]!.coefConsumeData ∧
          ScanCompsInRange hx dcs'[0]! ∧
          (PostSofBase h dcs0[0]! → MultiScanReady hx dcs'[0]!)) ∧
        (∀ dcs' mrks' srcs' errs' dcs0 mrks0 srcs0,
          C.Space.get hx (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
          C.Space.get hx ctx.rmrk = some mrks' → 0 < mrks'.size →
          C.Space.get hx ctx.rs = some srcs' → 0 < srcs'.size →
          C.Space.get hx ctx.rerr = some errs' → 0 < errs'.size →
          C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
          C.Space.get h ctx.rmrk = some mrks0 → 0 < mrks0.size →
          C.Space.get h ctx.rs = some srcs0 → 0 < srcs0.size →
          rmWarnPot errs' srcs' dcs'[0]! + (rmRank dcs'[0]! mrks'[0]! srcs'[0]! : Int) ≤ potBd ∧
          dcs'[0]!.unreadMarker = 0 ∧
          rmRank dcs'[0]! mrks'[0]! srcs'[0]! < rmRank dcs0[0]! mrks0[0]! srcs0[0]! ∧
          (isConstEofPtr srcs'[0]!.nextInputByte = false →
            isConstEofPtr srcs0[0]!.nextInputByte = false ∧
            srcs'[0]!.bytesInBuffer.toNat + 8 ≤ srcs0[0]!.bytesInBuffer.toNat))) ∨
      (val = JPEG_REACHED_EOI ∧
        ParserEnv ctx hx ∧
        CompSawZero ctx hx ∧
        RmFrame ctx h hx) ∨
      val = JPEG_SUSPENDED
    | .errExit _ => True
  obtain ⟨dcs0, hgdc0, hszdc0, _⟩ := parserEnv_get_dc hp
  obtain ⟨mrks0, hgmrk0, hszmrk0, _⟩ := parserEnv_get_mrk hp
  obtain ⟨srcs0, hgsrc0, hszsrc0, _⟩ := parserEnv_get_src hp
  obtain ⟨errs0, hgerr0, hszerr0, _⟩ := parserEnv_get_err hp
  let k0 := rmRank dcs0[0]! mrks0[0]! srcs0[0]!
  let Inv (k : Nat) (hx : C.Heap) (s : ReadMarkersState) : Prop :=
    if s.done then
      DoneSpec s.ret hx
    else
      ParserEnv ctx hx ∧ CompSawZero ctx hx ∧ RmFrame ctx h hx ∧
      (∀ dcs1 mrks1 srcs1 errs1,
        C.Space.get hx (C.DecompRef.decomp ctx.bdc) = some dcs1 → 0 < dcs1.size →
        C.Space.get hx ctx.rmrk = some mrks1 → 0 < mrks1.size →
        C.Space.get hx ctx.rs = some srcs1 → 0 < srcs1.size →
        C.Space.get hx ctx.rerr = some errs1 → 0 < errs1.size →
        rmWarnPot errs1 srcs1 dcs1[0]! + (rmRank dcs1[0]! mrks1[0]! srcs1[0]! : Int) ≤ potBd ∧
        dcs1[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 ∧
        rmRank dcs1[0]! mrks1[0]! srcs1[0]! = k) ∧
      (∀ dcs0 dcs1,
        C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
        C.Space.get hx (C.DecompRef.decomp ctx.bdc) = some dcs1 → 0 < dcs1.size →
        PostSofBase h dcs0[0]! → PostSofBase hx dcs1[0]!) ∧
      k ≤ rmRank dcs0[0]! mrks0[0]! srcs0[0]!
  let Post (hx : C.Heap) (s : ReadMarkersState) : Prop :=
    s.done = true ∧ DoneSpec s.ret hx
  have hk0Lt : k0 < C.fuel := by
    obtain ⟨srcs0', hg0', _, _, _, _, _, _, hbib, _⟩ := parserEnv_get_src hp
    have hbib' : srcs0[0]!.bytesInBuffer.toNat < 2 ^ 20 := by
      rw [Option.some.inj (hgsrc0.symm.trans hg0')]; exact hbib
    dsimp only [k0]; unfold rmRank rmSrcWeight C.fuel
    split <;> split <;> split <;> omega
  have hinvInit : Inv k0 h { done := false, ret := .ok JPEG_SUSPENDED } := by
    refine ⟨hp, hsaw0, rmFrame_refl ctx h, ?_, ?_, Nat.le_refl k0⟩
    · intro dcs1 mrks1 srcs1 errs1 hgd _ hgm _ hgs _ hge _
      rw [Option.some.inj (hgd.symm.trans hgdc0), Option.some.inj (hgm.symm.trans hgmrk0),
        Option.some.inj (hgs.symm.trans hgsrc0), Option.some.inj (hge.symm.trans hgerr0)]
      exact ⟨hpotBd dcs0 mrks0 srcs0 errs0 hgdc0 hszdc0 hgmrk0 hszmrk0 hgsrc0 hszsrc0 hgerr0 hszerr0,
        hscanBd dcs0 hgdc0 hszdc0, rfl⟩
    · intro dcsA dcsB hgdA _ hgdB _ hpsA
      rw [Option.some.inj (hgdB.symm.trans hgdA)]; exact hpsA
  have liftDone : ∀ (hA : C.Heap) (dcsA : Array C.JpegDecompressStruct)
      (mrksA : Array C.JpegMarkerReader) (srcsA : Array C.JpegSourceMgr),
      C.Space.get hA (C.DecompRef.decomp ctx.bdc) = some dcsA → 0 < dcsA.size →
      C.Space.get hA ctx.rmrk = some mrksA → 0 < mrksA.size →
      C.Space.get hA ctx.rs = some srcsA → 0 < srcsA.size →
      rmRank dcsA[0]! mrksA[0]! srcsA[0]! ≤ k0 →
      ∀ ret h',
        (match ret with
         | .ok val =>
           (val = JPEG_REACHED_SOS ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧
             (∀ mrks', C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size → mrks'[0]!.sawSOF ≠ 0) ∧
             (∀ dcs1 dcs', C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs1 → 0 < dcs1.size →
               C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
               dcs'[0]!.inputScanNumber.toInt = dcs1[0]!.inputScanNumber.toInt + 1 ∧
               dcs'[0]!.entropyStartPass = dcs1[0]!.entropyStartPass ∧
               dcs'[0]!.coefStartInputPass = dcs1[0]!.coefStartInputPass ∧
               dcs'[0]!.coefConsumeData = dcs1[0]!.coefConsumeData ∧
               ScanCompsInRange h' dcs'[0]! ∧
               (PostSofBase h dcs1[0]! → MultiScanReady h' dcs'[0]!)) ∧
             (∀ dcs' mrks' srcs' errs',
               C.Space.get h' (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
               C.Space.get h' ctx.rmrk = some mrks' → 0 < mrks'.size →
               C.Space.get h' ctx.rs = some srcs' → 0 < srcs'.size →
               C.Space.get h' ctx.rerr = some errs' → 0 < errs'.size →
               rmWarnPot errs' srcs' dcs'[0]! + (rmRank dcs'[0]! mrks'[0]! srcs'[0]! : Int) ≤ potBd ∧
               dcs'[0]!.unreadMarker = 0 ∧
               (∀ dcsX' mrksX' srcsX',
                 C.Space.get hA (C.DecompRef.decomp ctx.bdc) = some dcsX' → 0 < dcsX'.size →
                 C.Space.get hA ctx.rmrk = some mrksX' → 0 < mrksX'.size →
                 C.Space.get hA ctx.rs = some srcsX' → 0 < srcsX'.size →
                 rmRank dcs'[0]! mrks'[0]! srcs'[0]! < rmRank dcsX'[0]! mrksX'[0]! srcsX'[0]! ∧
                 (isConstEofPtr srcs'[0]!.nextInputByte = false →
                   rmRank dcs'[0]! mrks'[0]! srcs'[0]! + 32 ≤ rmRank dcsX'[0]! mrksX'[0]! srcsX'[0]!)))) ∨
           (val = JPEG_REACHED_EOI ∧ ParserEnv ctx h' ∧ CompSawZero ctx h' ∧ RmFrame ctx h h') ∨
           val = JPEG_SUSPENDED
         | .errExit _ => True) →
        DoneSpec ret h' := by
    intro hA dcsA mrksA srcsA hgdA hszdA hgmA hszmA hgsA hszsA hkALe0 ret h' hpost
    cases ret with
    | errExit _ => trivial
    | ok val =>
      rcases hpost with ⟨rfl, hp', hsaw', hsof', hsc', hbd'⟩ | hrest
      · refine Or.inl ⟨rfl, hp', hsaw', hsof', hsc', ?_⟩
        intro dcs' mrks' srcs' errs' dcs1 mrks1 srcs1 hgd' hszd' hgm' hszm' hgs' hszs' hge' hsze' hgd1 _ hgm1 _ hgs1 _
        obtain ⟨hwp', hum', hrankA⟩ := hbd' dcs' mrks' srcs' errs' hgd' hszd' hgm' hszm' hgs' hszs' hge' hsze'
        obtain ⟨hltA, h32A⟩ := hrankA dcsA mrksA srcsA hgdA hszdA hgmA hszmA hgsA hszsA
        rw [Option.some.inj (hgd1.symm.trans hgdc0), Option.some.inj (hgm1.symm.trans hgmrk0),
          Option.some.inj (hgs1.symm.trans hgsrc0)]
        refine ⟨hwp', hum', Nat.lt_of_lt_of_le hltA hkALe0, ?_⟩
        intro hnf'
        have h32 := Nat.le_trans (h32A hnf') hkALe0
        by_cases hce1 : isConstEofPtr srcs0[0]!.nextInputByte = true
        · dsimp only [k0] at h32
          unfold rmRank rmSrcWeight at h32; simp only [hnf', hce1, Bool.false_eq_true, ↓reduceIte] at h32
          split at h32 <;> split at h32 <;> split at h32 <;> split at h32 <;> omega
        · have hnf1 : isConstEofPtr srcs0[0]!.nextInputByte = false := by
            cases hc : isConstEofPtr srcs0[0]!.nextInputByte <;> simp_all
          refine ⟨hnf1, ?_⟩
          dsimp only [k0] at h32
          unfold rmRank rmSrcWeight at h32; simp only [hnf', hnf1, Bool.false_eq_true, ↓reduceIte] at h32
          split at h32 <;> split at h32 <;> split at h32 <;> split at h32 <;> omega
      · exact Or.inr hrest
  have hstep : ∀ k hx s, Inv k hx s →
      ∃ cont s' hx', C.run (condFn s) hx = .ok ((cont, s'), hx') ∧
        (if cont then ∃ k' s'' hx'', C.run (bodyFn s') hx' = .ok (s'', hx'') ∧ k' < k ∧ Inv k' hx'' s''
         else Post hx' s') := by
    intro k hx s hinv
    by_cases hdone : s.done = true
    · have hinvD : DoneSpec s.ret hx := by simp only [Inv, hdone, ↓reduceIte] at hinv; exact hinv
      refine ⟨false, s, hx, ?_, hdone, hinvD⟩
      have hf : (!s.done) = false := by simp [hdone]
      simp [condFn, C.run, hf]
    · have hdoneF : s.done = false := by cases hc : s.done <;> simp_all
      have ht : (!s.done) = true := by simp [hdoneF]
      simp only [Inv, hdoneF, Bool.false_eq_true, ↓reduceIte] at hinv
      obtain ⟨hpX, hsawX, hrmX, hbdX, hpsX, hkLe0⟩ := hinv
      refine ⟨true, s, hx, (by simp [condFn, C.run, ht]), ?_⟩
      obtain ⟨dcsX, hgdcX, hszdcX, kerrX, _, _, _, kmrkX, ksrcX⟩ := parserEnv_get_dc hpX
      obtain ⟨mrksX, hgmrkX, hszmrkX, _, _, hpcomX, _, hpappX, _⟩ := parserEnv_get_mrk hpX
      obtain ⟨srcsX, hgsrcX, hszsrcX, _, _, _, _, _, hbibX, _⟩ := parserEnv_get_src hpX
      obtain ⟨errsX, hgerrX, hszerrX, _⟩ := parserEnv_get_err hpX
      obtain ⟨hwpX, hscX, hkX⟩ := hbdX dcsX mrksX srcsX errsX hgdcX hszdcX hgmrkX hszmrkX hgsrcX hszsrcX hgerrX hszerrX
      have hkPos : 0 < k := by rw [← hkX]; unfold rmRank; omega
      have hldcX := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcX hszdcX
      have hheadX : ∀ errs0 srcs0, C.Space.get hx ctx.rerr = some errs0 → 0 < errs0.size →
          C.Space.get hx ctx.rs = some srcs0 → 0 < srcs0.size → warnPotVal errs0 srcs0 + 2 ^ 23 < 2 ^ 63 :=
        fun e0 s0 he0 hse0 hs0 hss0 => by
          rw [Option.some.inj (he0.symm.trans hgerrX), Option.some.inj (hs0.symm.trans hgsrcX)]
          exact warnPotVal_bound_of_rmWarnPot hwpX hpotHi
      by_cases hum0 : (dcsX[0]!.unreadMarker == 0) = true
      · have hum0Eq : dcsX[0]!.unreadMarker = 0 := by simpa using hum0
        have hlmrkX := ptr_load_ok (r := ctx.rmrk) (off := 0) hgmrkX hszmrkX
        have hlmrkX' : C.run (Ptr.load dcsX[0]!.marker) hx = .ok (mrksX[0]!, hx) := by rw [kmrkX]; exact hlmrkX
        by_cases hsoi0 : (mrksX[0]!.sawSOI == 0) = true
        · have hbdFm : ∀ errs0 srcs0, C.Space.get hx ctx.rerr = some errs0 → 0 < errs0.size →
              C.Space.get hx ctx.rs = some srcs0 → 0 < srcs0.size → warnPotVal errs0 srcs0 + 2 < 2 ^ 63 :=
            fun e0 s0 he0 hse0 hs0 hss0 => by have := hheadX e0 s0 he0 hse0 hs0 hss0; omega
          obtain ⟨resFm, hFm, hrunFm, hpFm, hstFm, hpostFm⟩ := first_marker_parser hpX hbdFm
          have hsawFm := compSawZero_of_stable hsawX hstFm hpX
          have hrmFm := rmFrame_of_strong (rmFrameStrong_first_marker hrunFm)
          cases resFm with
          | errExit code =>
            refine ⟨0, { done := true, ret := .errExit code }, hFm, ?_, hkPos, ?_⟩
            · dsimp only [bodyFn, cinfo]; rw [C.run_bind, hldcX]; dsimp only
              simp only [hum0, ↓reduceIte]; rw [C.run_bind, hlmrkX']; dsimp only
              simp only [hsoi0, ↓reduceIte]; rw [C.run_bind, hrunFm]; rfl
            · dsimp only [Inv, DoneSpec]; rw [ite_eq_left rfl]; trivial
          | ok bFm =>
            cases bFm with
            | false =>
              refine ⟨0, { done := true, ret := .ok JPEG_SUSPENDED }, hFm, ?_, hkPos, ?_⟩
              · dsimp only [bodyFn, cinfo]; rw [C.run_bind, hldcX]; dsimp only
                simp only [hum0, ↓reduceIte]; rw [C.run_bind, hlmrkX']; dsimp only
                simp only [hsoi0, ↓reduceIte]; rw [C.run_bind, hrunFm]; rfl
              · dsimp only [Inv, DoneSpec]; rw [ite_eq_left rfl]; exact Or.inr (Or.inr rfl)
            | true =>
              rcases hpostFm with ⟨⟨dcsFm, hgdcFm, hszdcFm, humFm⟩, hstrFm, hwFm⟩
              have hldcFm := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcFm hszdcFm
              have hmSoiT : (M_SOI == M_SOI) = true := by decide
              obtain ⟨resSoi, hSoi, hrunSoi, hpSoi, hstSoi, hstrSoi, hwSoi⟩ := get_soi_parser hpFm
              have hpreBodyT : C.run (bodyFn s) hx = C.run (dispatch (.ref (C.DecompRef.decomp ctx.bdc) 0)) hFm := by
                dsimp only [bodyFn, cinfo]; rw [C.run_bind, hldcX]; dsimp only
                simp only [hum0, ↓reduceIte]; rw [C.run_bind, hlmrkX']; dsimp only
                simp only [hsoi0, ↓reduceIte]; rw [C.run_bind, hrunFm]
              cases resSoi with
              | errExit code =>
                refine ⟨0, { done := true, ret := .errExit code }, hSoi, ?_, hkPos, ?_⟩
                · rw [hpreBodyT]; dsimp only [dispatch]; rw [C.run_bind, hldcFm]; dsimp only
                  rw [humFm]; simp only [hmSoiT, ↓reduceIte]; rw [C.run_bind, hrunSoi]; rfl
                · dsimp only [Inv, DoneSpec]; rw [ite_eq_left rfl]; trivial
              | ok bSoi =>
                cases bSoi with
                | false =>
                  refine ⟨0, { done := true, ret := .ok JPEG_SUSPENDED }, hSoi, ?_, hkPos, ?_⟩
                  · rw [hpreBodyT]; dsimp only [dispatch]; rw [C.run_bind, hldcFm]; dsimp only
                    rw [humFm]; simp only [hmSoiT, ↓reduceIte]; rw [C.run_bind, hrunSoi]; rfl
                  · dsimp only [Inv, DoneSpec]; rw [ite_eq_left rfl]; exact Or.inr (Or.inr rfl)
                | true =>
                  have hsawSoi := compSawZero_of_stable hsawFm hstSoi hpFm
                  have hrmSoi := rmFrame_of_strong (rmFrameStrong_get_soi hrunSoi)
                  obtain ⟨mrksSoiT, hgmrkSoiT, hszmrkSoiT, hsawSoiT⟩ := get_soi_sawSOI_true hpFm hrunSoi
                  have hstr02 : ∀ s0 s2, C.Space.get hx ctx.rs = some s0 → 0 < s0.size →
                      C.Space.get hSoi ctx.rs = some s2 → 0 < s2.size → SrcStrict s0[0]! s2[0]! :=
                    fun s0 s2 hs0 hsz0 hs2 hsz2 => by
                      obtain ⟨s1, hs1, hsz1, _⟩ := parserEnv_get_src hpFm
                      exact srcStrict_mono_trans (hstrFm s0 s1 hs0 hsz0 hs1 hsz1) (hstrSoi s1 s2 hs1 hsz1 hs2 hsz2)
                  have hw02 : WarnPotOk ctx hx hSoi 2 := by
                    simpa using warnPotOk_trans (fun s0 s1 hs0 hsz0 hs1 hsz1 => srcMono_of_strict (hstrFm s0 s1 hs0 hsz0 hs1 hsz1)) hstrSoi hwFm hwSoi (by omega) hpFm
                  have hst02 := decompHeaderStable_trans hpX hpFm hstFm hstSoi
                  have hscanSoi : ∀ dcs2, C.Space.get hSoi (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
                      dcs2[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 := fun dcs2 hgd2 hsz2 => by
                    have h1 := (rmFrame_trans ctx hrmFm hrmSoi hpFm).1 dcsX dcs2 hgdcX hszdcX hgd2 hsz2
                    rw [h1.1]; exact hscX
                  have hps02 : ∀ dcs0 dcs2, C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
                      C.Space.get hSoi (C.DecompRef.decomp ctx.bdc) = some dcs2 → 0 < dcs2.size →
                      PostSofBase h dcs0[0]! → PostSofBase hSoi dcs2[0]! := fun dcs0 dcs2 hgd0 hsz0 hgd2 hsz2 hps0 =>
                    postSofBase_of_decompHeaderStable hpX hpSoi hst02 hgdcX hszdcX hgd2 hsz2
                      (hpsX dcs0 dcsX hgd0 hsz0 hgdcX hszdcX hps0)
                  obtain ⟨k', s', h', hrunCl, hltK, hnd, hp', hsaw', hrm', hbd', hps'⟩ :=
                    read_markers_clear_unread hpSoi hsawSoi
                      (rmFrame_trans ctx (rmFrame_trans ctx hrmX hrmFm hpX) hrmSoi hpFm)
                      hps02 hscanSoi (k0 := k) (potBd := potBd) (fun dcs2 mrks2 srcs2 errs2 hgd2 _ hgm2 _ hgs2 _ hge2 _ => by
                        have hm2Eq := Option.some.inj (hgm2.symm.trans hgmrkSoiT)
                        have hsaw2Ne : mrks2[0]!.sawSOI ≠ 0 := by rw [hm2Eq]; exact hsawSoiT
                        have humN0 : (dcsX[0]!.unreadMarker != 0) = false := by simp [hum0Eq]
                        have hmX0 : (mrksX[0]!.sawSOI == 0) = true := hsoi0
                        have hm20 : (mrks2[0]!.sawSOI == 0) = false := by
                          cases hc : (mrks2[0]!.sawSOI == 0); rfl; exact False.elim (hsaw2Ne (by simpa using hc))
                        have hu20 : (({ dcs2[0]! with unreadMarker := 0 } : C.JpegDecompressStruct).unreadMarker != 0) = false := rfl
                        have hwMono : rmSrcWeight srcs2[0]! ≤ rmSrcWeight srcsX[0]! :=
                          rmSrcWeight_mono (srcMono_of_strict (hstr02 srcsX srcs2 hgsrcX hszsrcX hgs2 (by assumption)))
                        unfold rmSrcWeight at hwMono
                        have hrkLt : rmRank { dcs2[0]! with unreadMarker := 0 } mrks2[0]! srcs2[0]! < k := by
                          rw [← hkX]
                          unfold rmRank rmSrcWeight
                          simp only [hm20, hu20, hmX0, humN0, Bool.false_eq_true, ↓reduceIte]
                          omega
                        obtain ⟨wf02, wt02⟩ := hw02 errsX errs2 srcsX srcs2 hgerrX hszerrX hge2 (by assumption) hgsrcX hszsrcX hgs2 (by assumption)
                        have hwpLe : rmWarnPot errs2 srcs2 { dcs2[0]! with unreadMarker := 0 } +
                            (rmRank { dcs2[0]! with unreadMarker := 0 } mrks2[0]! srcs2[0]! : Int) ≤ potBd := by
                          unfold rmWarnPot at hwpX ⊢
                          unfold rmRank rmSrcWeight at hrkLt hwpX ⊢
                          simp only [hm20, hu20, hmX0, humN0, Bool.false_eq_true, ↓reduceIte] at hrkLt hwpX ⊢
                          by_cases hc2 : isConstEofPtr srcs2[0]!.nextInputByte = false
                          · have hcX : isConstEofPtr srcsX[0]!.nextInputByte = false := by
                              cases hc : isConstEofPtr srcsX[0]!.nextInputByte
                              · rfl
                              · have ht2 := (srcMono_of_strict (hstr02 srcsX srcs2 hgsrcX hszsrcX hgs2 (by assumption))).1 hc
                                rw [ht2] at hc2; cases hc2
                            have wle := wf02 hc2
                            simp only [hc2, hcX, Bool.false_eq_true, ↓reduceIte] at hwMono hrkLt hwpX ⊢
                            omega
                          · have ht2 : isConstEofPtr srcs2[0]!.nextInputByte = true := by
                              cases hc : isConstEofPtr srcs2[0]!.nextInputByte
                              · exact False.elim (hc2 hc)
                              · rfl
                            have wle := wt02 ht2
                            simp only [ht2, ↓reduceIte] at wle hrkLt hwpX ⊢
                            by_cases hcX : isConstEofPtr srcsX[0]!.nextInputByte = true
                            · simp only [hcX, ↓reduceIte] at wle hrkLt hwpX
                              unfold warnPotVal at hwpX ⊢
                              simp only [ht2, hcX, ↓reduceIte] at hwpX ⊢
                              omega
                            · have hfX : isConstEofPtr srcsX[0]!.nextInputByte = false := by
                                cases hc : isConstEofPtr srcsX[0]!.nextInputByte
                                · rfl
                                · exact False.elim (hcX hc)
                              simp only [hfX, Bool.false_eq_true, ↓reduceIte] at wle hrkLt hwpX
                              unfold warnPotVal at wle hwpX ⊢
                              simp only [ht2, hfX, Bool.false_eq_true, ↓reduceIte] at wle hwpX ⊢
                              omega
                        exact ⟨hwpLe, hrkLt⟩)
                  have hrunCl_tail : C.run (bodyFn s) hx = .ok (s', h') := by
                    rw [hpreBodyT]; dsimp only [dispatch]; rw [C.run_bind, hldcFm]; dsimp only
                    rw [humFm]; simp only [hmSoiT, ↓reduceIte]; rw [C.run_bind, hrunSoi]; dsimp only; exact hrunCl
                  have hndF : s'.done = false := by
                    cases hc : s'.done
                    · rfl
                    · simp [hc] at hnd
                  refine ⟨k', s', h', hrunCl_tail, hltK, ?_⟩
                  simp only [Inv, hndF, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨hp', hsaw', hrm', hbd', hps', Nat.le_trans (Nat.le_of_lt hltK) hkLe0⟩
        · have hsoiF : (mrksX[0]!.sawSOI == 0) = false := by
            cases hc : (mrksX[0]!.sawSOI == 0); rfl; exact False.elim (hsoi0 hc)
          have hpreBody : C.run (bodyFn s) hx = C.run (do
              let r ← next_marker (.ref (.decomp ctx.bdc) 0)
              if r == 0 then return { done := true, ret := .ok JPEG_SUSPENDED }
              else pure ()
              dispatch (.ref (.decomp ctx.bdc) 0)) hx := by
            dsimp only [bodyFn, cinfo]; rw [C.run_bind, hldcX]; dsimp only
            simp only [hum0, ↓reduceIte]; rw [C.run_bind, hlmrkX']; dsimp only
            simp only [hsoiF, Bool.false_eq_true, ↓reduceIte]
          have hscanNm : ∀ dcs srcs, C.Space.get hx (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
              C.Space.get hx ctx.rs = some srcs → 0 < srcs.size → scanLimit dcs[0]! srcs[0]! < 2 ^ 31 := by
            intro dcs srcs hgd hszd hgs hszs
            rw [Option.some.inj (hgd.symm.trans hgdcX), Option.some.inj (hgs.symm.trans hgsrcX)]
            exact scanLimit_lt_of_scanBd hbibX hscX
          obtain ⟨retNm, hNm, hrunNm, hpostNm⟩ := next_marker_parser hpX hsawX hheadX hscanNm
          rcases hpostNm with rfl | ⟨rfl, dcsNm, srcsNm, srcs0Nm, hgsrc0Nm, hszsrc0Nm, hgdcNm, hszdcNm, hgsrcNm, hszsrcNm, hpNm, hsawNm, hrmNm, hstNm, hnmCase⟩
          · refine ⟨0, { done := true, ret := .ok JPEG_SUSPENDED }, hNm, ?_, hkPos, ?_⟩
            · rw [hpreBody, C.run_bind, hrunNm]; rfl
            · dsimp only [Inv, DoneSpec]; rw [ite_eq_left rfl]; exact Or.inr (Or.inr rfl)
          · have hneq0 : (TRUE == 0) = false := by decide
            have hrunNm_tail : C.run (bodyFn s) hx = C.run (dispatch (.ref (C.DecompRef.decomp ctx.bdc) 0)) hNm := by
              rw [hpreBody, C.run_bind, hrunNm]; dsimp only; simp only [hneq0, Bool.false_eq_true, ↓reduceIte]
            rcases hnmCase with ⟨humEoi, hwEoi⟩ | ⟨humNeEoi, hceX, hrkLtNm, hwNeEoi⟩
            · obtain ⟨errsNm, hgerrNm, hszerrNm, _⟩ := parserEnv_get_err hpNm
              obtain ⟨mrksNm, hgmrkNm, hszmrkNm, _⟩ := parserEnv_get_mrk hpNm
              have hldcNm := ptr_load_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) hgdcNm hszdcNm
              obtain ⟨dcsNm', hgdcNm', _, kerrNm, _⟩ := parserEnv_get_dc hpNm
              have kerrNm' : dcsNm[0]!.err = .ref ctx.rerr 0 := by
                rw [Option.some.inj (hgdcNm.symm.trans hgdcNm')]; exact kerrNm
              obtain ⟨hTr, hrunTr, hpTr, hdTr, hmrTr, _, _, hcpTr, _, _, _, _, _, hnwTr⟩ :=
                tracems_nonneg_parser hpNm 1 JTRC_EOI (by decide)
              have hgdcTr : C.Space.get hTr (C.DecompRef.decomp ctx.bdc) = some dcsNm := by
                simp only [C.Space.get, hdTr] at hgdcNm ⊢; exact hgdcNm
              have hroTr : C.Space.ro hTr (C.DecompRef.decomp ctx.bdc) = false := rfl
              let dcEoiEnd := { dcsNm[0]! with unreadMarker := 0 }
              have hstTr := ptr_store_ok (r := C.DecompRef.decomp ctx.bdc) (off := 0) (v := dcEoiEnd) hgdcTr hroTr hszdcNm
              let hEoiEnd := C.Space.put hTr (C.DecompRef.decomp ctx.bdc) (dcsNm.set! 0 dcEoiEnd)
              have hpEoiEnd : ParserEnv ctx hEoiEnd := parserEnv_put_dc_same hpTr hgdcTr hszdcNm
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              have hstTrEnd : DecompHeaderStable ctx hTr hEoiEnd := by
                refine ⟨(fun da db hga _ hgb _ => by
                  have ha := Option.some.inj (hga.symm.trans hgdcTr)
                  have hgE : C.Space.get hEoiEnd (C.DecompRef.decomp ctx.bdc) = some (dcsNm.set! 0 dcEoiEnd) := by
                    simp [hEoiEnd, C.Space.get, C.Space.put]
                  have hb := Option.some.inj (hgb.symm.trans hgE)
                  rw [ha, hb, set0_bang_m dcsNm hszdcNm dcEoiEnd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩),
                  (fun ma mb ha _ hb _ => by rw [Option.some.inj (hb.symm.trans ha)]),
                  (fun rcp cs i hg hi => ⟨cs, hg, hi, rfl, rfl, rfl⟩)⟩
              have hstNmTr : DecompHeaderStable ctx hNm hTr :=
                decompHeaderStable_of_same hdTr hmrTr hcpTr
              have hsawEoiEnd := compSawZero_of_stable hsawNm (decompHeaderStable_trans hpNm hpTr hstNmTr hstTrEnd) hpNm
              have hrmNmEnd : RmFrame ctx hNm hEoiEnd := by
                refine ⟨fun da db hga _ hgb _ => ?_, fun ma mb hma _ hmb _ hm => ?_⟩
                · have ha := Option.some.inj (hga.symm.trans hgdcNm)
                  have hgE : C.Space.get hEoiEnd (C.DecompRef.decomp ctx.bdc) = some (dcsNm.set! 0 dcEoiEnd) := by
                    simp [hEoiEnd, C.Space.get, C.Space.put]
                  have hb := Option.some.inj (hgb.symm.trans hgE)
                  rw [ha, hb, set0_bang_m dcsNm hszdcNm dcEoiEnd]; exact ⟨rfl, rfl, rfl, rfl⟩
                · simp only [hEoiEnd, C.Space.get, C.Space.put, hmrTr] at hmb
                  rw [Option.some.inj (hmb.symm.trans hma)]; exact hm
              refine ⟨0, { done := true, ret := .ok JPEG_REACHED_EOI }, hEoiEnd, ?_, hkPos, ?_⟩
              · rw [hrunNm_tail]; dsimp only [dispatch]; rw [C.run_bind, hldcNm]; dsimp only
                rw [humEoi]
                have hf1 : (M_EOI == M_SOI) = false := by decide
                have hf2 : (M_EOI == M_SOF0 || M_EOI == M_SOF1) = false := by decide
                have hf3 : (M_EOI == M_SOF2) = false := by decide
                have hf4 : (M_EOI == M_SOF3) = false := by decide
                have hf5 : (M_EOI == M_SOF9) = false := by decide
                have hf6 : (M_EOI == M_SOF10) = false := by decide
                have hf7 : (M_EOI == M_SOF11) = false := by decide
                have hf8 : (M_EOI == M_SOF5 || M_EOI == M_SOF6 || M_EOI == M_SOF7 || M_EOI == M_JPG ||
                    M_EOI == M_SOF13 || M_EOI == M_SOF14 || M_EOI == M_SOF15) = false := by decide
                have hf9 : (M_EOI == M_SOS) = false := by decide
                have ht10 : (M_EOI == M_EOI) = true := by decide
                simp only [hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, ht10, Bool.false_eq_true, ↓reduceIte]
                have hrunTr' : C.run (tracems dcsNm[0]!.err 1 JTRC_EOI) hNm = .ok ((), hTr) := by
                  rw [kerrNm']; exact hrunTr
                rw [C.run_bind, hrunTr']; dsimp only; rw [C.run_bind, hstTr]; rfl
              · dsimp only [Inv, DoneSpec]; rw [ite_eq_left rfl]
                refine Or.inr (Or.inl ⟨rfl, hpEoiEnd, hsawEoiEnd, rmFrame_trans ctx (rmFrame_trans ctx hrmX hrmNm hpX) hrmNmEnd hpNm⟩)
            · have hscanNmBd : ∀ dcs, C.Space.get hNm (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
                  dcs[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 := fun dcs hgd hsz => by
                rw [(hrmNm.1 dcsX dcs hgdcX hszdcX hgd hsz).1]; exact hscX
              have hpsNm : ∀ dcs0 dcs', C.Space.get h (C.DecompRef.decomp ctx.bdc) = some dcs0 → 0 < dcs0.size →
                  C.Space.get hNm (C.DecompRef.decomp ctx.bdc) = some dcs' → 0 < dcs'.size →
                  PostSofBase h dcs0[0]! → PostSofBase hNm dcs'[0]! := fun dcs0 dcs' hgd0 hsz0 hgd' hsz' hps0 =>
                postSofBase_of_decompHeaderStable hpX hpNm hstNm hgdcX hszdcX hgd' hsz'
                  (hpsX dcs0 dcsX hgd0 hsz0 hgdcX hszdcX hps0)
              have hbdNm : ∀ dcs1 mrks1 srcs1 errs1,
                  C.Space.get hNm (C.DecompRef.decomp ctx.bdc) = some dcs1 → 0 < dcs1.size →
                  C.Space.get hNm ctx.rmrk = some mrks1 → 0 < mrks1.size →
                  C.Space.get hNm ctx.rs = some srcs1 → 0 < srcs1.size →
                  C.Space.get hNm ctx.rerr = some errs1 → 0 < errs1.size →
                  rmRank { dcs1[0]! with unreadMarker := 0 } mrks1[0]! srcs1[0]! < k ∧
                  warnPotVal errs1 srcs1 + (if isConstEofPtr srcs1[0]!.nextInputByte then (2 ^ 17 : Int) else 2 ^ 18 + 1) +
                    (rmRank { dcs1[0]! with unreadMarker := 0 } mrks1[0]! srcs1[0]! : Int) ≤ potBd := by
                intro dcs1 mrks1 srcs1 errs1 hgd1 hsz1 hgm1 hszm1 hgs1 hszs1 hge1 hsze1
                have hs1Eq := Option.some.inj (hgs1.symm.trans hgsrcNm)
                have hs0Eq := Option.some.inj (hgsrc0Nm.symm.trans hgsrcX)
                rw [hs1Eq] at *; rw [hs0Eq] at hceX hrkLtNm
                have hsrcW := rmSrcWeight_lt_of_srcRank_lt hceX hrkLtNm
                unfold rmSrcWeight at hsrcW
                have hsmS := rmSawSoi_mono (hrmNm.2 mrksX mrks1 hgmrkX hszmrkX hgm1 hszm1)
                have hu1 : (({ dcs1[0]! with unreadMarker := 0 } : C.JpegDecompressStruct).unreadMarker != 0) = false := rfl
                have huX : (dcsX[0]!.unreadMarker != 0) = false := by simp [hum0Eq]
                have hrkLt1 : rmRank { dcs1[0]! with unreadMarker := 0 } mrks1[0]! srcsNm[0]! < k := by
                  rw [← hkX]; unfold rmRank rmSrcWeight; simp only [hu1, huX, hceX, Bool.false_eq_true, ↓reduceIte] at hsrcW ⊢; omega
                refine ⟨hrkLt1, ?_⟩
                have hwLe := hwNeEoi errs1 srcsNm hge1 hsze1 hgsrcNm hszsrcNm errsX hgerrX hszerrX
                rw [hs0Eq] at hwLe
                unfold srcPotential warnPotVal at hwLe
                simp only [hceX, Bool.false_eq_true, ↓reduceIte] at hwLe hsrcW
                unfold rmWarnPot at hwpX; simp only [hceX, Bool.false_eq_true, ↓reduceIte] at hwpX
                unfold warnPotVal at hwpX
                simp only [hceX, Bool.false_eq_true, ↓reduceIte] at hwpX
                unfold rmRank rmSrcWeight at hkX hwpX ⊢
                simp only [hu1, huX, hceX, Bool.false_eq_true, ↓reduceIte] at hkX hwpX ⊢
                unfold warnPotVal
                by_cases hceNm : isConstEofPtr srcsNm[0]!.nextInputByte = true
                · simp only [hceNm, ↓reduceIte] at hwLe hsrcW ⊢; omega
                · have hfNm : isConstEofPtr srcsNm[0]!.nextInputByte = false := by
                    cases hc : isConstEofPtr srcsNm[0]!.nextInputByte
                    · rfl
                    · exact False.elim (hceNm hc)
                  simp only [hfNm, Bool.false_eq_true, ↓reduceIte] at hwLe hsrcW ⊢; omega
              obtain ⟨k', s', h', hrunD, hpostD⟩ :=
                read_markers_dispatch_ok hpNm hsawNm (rmFrame_trans ctx hrmX hrmNm hpX) hpotHi
                  hscanNmBd hpsNm hbdNm
              refine ⟨k', s', h', (by rw [hrunNm_tail]; exact hrunD), ?_⟩
              cases hsD : s'.done <;> simp only [hsD] at hpostD ⊢
              · obtain ⟨hltK, hp', hsaw', hrm', hbd', hps'⟩ := hpostD
                exact ⟨hltK, by simp only [Inv, hsD, Bool.false_eq_true, ↓reduceIte]; exact ⟨hp', hsaw', hrm', hbd', hps', Nat.le_trans (Nat.le_of_lt hltK) hkLe0⟩⟩
              · obtain ⟨rfl, hpostDone⟩ := hpostD
                obtain ⟨dcsNm, hgdcNm, hszdcNm, _⟩ := parserEnv_get_dc hpNm
                obtain ⟨mrksNm, hgmrkNm, hszmrkNm, _⟩ := parserEnv_get_mrk hpNm
                obtain ⟨errsNm, hgerrNm, hszerrNm, _⟩ := parserEnv_get_err hpNm
                have hrkNm : rmRank dcsNm[0]! mrksNm[0]! srcsNm[0]! ≤ k0 := by
                  have hs0Eq := Option.some.inj (hgsrc0Nm.symm.trans hgsrcX)
                  have h4 : rmSrcWeight srcsNm[0]! + 4 ≤ rmSrcWeight srcsX[0]! := by
                    rw [← hs0Eq]; exact rmSrcWeight_lt_of_srcRank_lt hceX hrkLtNm
                  have hsoiLe : (if mrksNm[0]!.sawSOI == 0 then 2 else 0) ≤ (if mrksX[0]!.sawSOI == 0 then 2 else 0) :=
                    rmSawSoi_mono (hrmNm.2 mrksX mrksNm hgmrkX hszmrkX hgmrkNm hszmrkNm)
                  have hleK : rmRank dcsNm[0]! mrksNm[0]! srcsNm[0]! ≤ k := by
                    rw [← hkX]; unfold rmRank; split <;> split <;> omega
                  exact Nat.le_trans hleK hkLe0
                exact ⟨hkPos, by
                  simp only [Inv, hsD, ↓reduceIte]
                  exact liftDone hNm dcsNm mrksNm srcsNm hgdcNm hszdcNm hgmrkNm hszmrkNm hgsrcNm hszsrcNm hrkNm s'.ret h' hpostDone⟩
      · have humNe0 : (dcsX[0]!.unreadMarker == 0) = false := by
          cases hc : (dcsX[0]!.unreadMarker == 0); rfl; exact False.elim (hum0 hc)
        have humNe0' : (dcsX[0]!.unreadMarker != 0) = true := by
          simp [bne, humNe0]
        have hpreBody : C.run (bodyFn s) hx = C.run (dispatch (.ref (C.DecompRef.decomp ctx.bdc) 0)) hx := by
          dsimp only [bodyFn, cinfo]; rw [C.run_bind, hldcX]; dsimp only
          simp only [humNe0, Bool.false_eq_true, ↓reduceIte]
        have hscanX' : ∀ dcs, C.Space.get hx (C.DecompRef.decomp ctx.bdc) = some dcs → 0 < dcs.size →
            dcs[0]!.inputScanNumber.toInt + 2 ^ 20 + 6 < 2 ^ 31 := fun dcs hgd hsz => by
          rw [Option.some.inj (hgd.symm.trans hgdcX)]; exact hscX
        have hbdX' : ∀ dcs1 mrks1 srcs1 errs1,
            C.Space.get hx (C.DecompRef.decomp ctx.bdc) = some dcs1 → 0 < dcs1.size →
            C.Space.get hx ctx.rmrk = some mrks1 → 0 < mrks1.size →
            C.Space.get hx ctx.rs = some srcs1 → 0 < srcs1.size →
            C.Space.get hx ctx.rerr = some errs1 → 0 < errs1.size →
            rmRank { dcs1[0]! with unreadMarker := 0 } mrks1[0]! srcs1[0]! < k ∧
            warnPotVal errs1 srcs1 + (if isConstEofPtr srcs1[0]!.nextInputByte then (2 ^ 17 : Int) else 2 ^ 18 + 1) +
              (rmRank { dcs1[0]! with unreadMarker := 0 } mrks1[0]! srcs1[0]! : Int) ≤ potBd := by
          intro dcs1 mrks1 srcs1 errs1 hgd1 _ hgm1 _ hgs1 _ hge1 _
          rw [Option.some.inj (hgd1.symm.trans hgdcX), Option.some.inj (hgm1.symm.trans hgmrkX),
            Option.some.inj (hgs1.symm.trans hgsrcX), Option.some.inj (hge1.symm.trans hgerrX)]
          have hu1 : (({ dcsX[0]! with unreadMarker := 0 } : C.JpegDecompressStruct).unreadMarker != 0) = false := rfl
          have hrkLt : rmRank { dcsX[0]! with unreadMarker := 0 } mrksX[0]! srcsX[0]! < k := by
            rw [← hkX]; unfold rmRank; simp only [hu1, humNe0', Bool.false_eq_true, ↓reduceIte]; omega
          refine ⟨hrkLt, ?_⟩
          unfold rmWarnPot at hwpX; simp only [humNe0', ↓reduceIte] at hwpX
          unfold rmRank at hkX hwpX ⊢; simp only [hu1, humNe0', Bool.false_eq_true, ↓reduceIte] at hkX hwpX ⊢
          by_cases hceX : isConstEofPtr srcsX[0]!.nextInputByte = true
          · simp only [hceX, ↓reduceIte] at hwpX ⊢; omega
          · have hfX : isConstEofPtr srcsX[0]!.nextInputByte = false := by
              cases hc : isConstEofPtr srcsX[0]!.nextInputByte <;> simp_all
            simp only [hfX, Bool.false_eq_true, ↓reduceIte] at hwpX ⊢; omega
        obtain ⟨k', s', h', hrunD, hpostD⟩ :=
          read_markers_dispatch_ok hpX hsawX hrmX hpotHi hscanX' hpsX hbdX'
        refine ⟨k', s', h', (by rw [hpreBody]; exact hrunD), ?_⟩
        cases hsD : s'.done <;> simp only [hsD] at hpostD ⊢
        · obtain ⟨hltK, hp', hsaw', hrm', hbd', hps'⟩ := hpostD
          exact ⟨hltK, by simp only [Inv, hsD, Bool.false_eq_true, ↓reduceIte]; exact ⟨hp', hsaw', hrm', hbd', hps', Nat.le_trans (Nat.le_of_lt hltK) hkLe0⟩⟩
        · obtain ⟨rfl, hpostDone⟩ := hpostD
          exact ⟨hkPos, by
            simp only [Inv, hsD, ↓reduceIte]
            exact liftDone hx dcsX mrksX srcsX hgdcX hszdcX hgmrkX hszmrkX hgsrcX hszsrcX (hkX ▸ hkLe0) s'.ret h' hpostDone⟩
  obtain ⟨sEnd, hEnd, hrunEnd, _, hdoneSpec⟩ :=
    cwhile_terminates condFn bodyFn Inv Post hstep hk0Lt hinvInit
  refine ⟨sEnd.ret, hEnd, ?_, hdoneSpec⟩
  have cwhile_go_congr : ∀ (b1 b2 : ReadMarkersState → C.M ReadMarkersState)
      (heq : ∀ s1 h1, C.run (b1 s1) h1 = C.run (b2 s1) h1) n s1 h1,
      C.run (C.cwhile.go condFn b1 n s1) h1 = C.run (C.cwhile.go condFn b2 n s1) h1 := by
    intro b1 b2 heq n
    induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro s1 h1
      unfold C.cwhile.go
      have hcond : ∀ s h, C.run (condFn s) h = .ok ((!s.done, s), h) := fun _ _ => rfl
      cases hc : (!s1.done)
      · simp only [C.run_bind, hcond, hc, Bool.false_eq_true, ↓reduceIte]
      · simp only [C.run_bind, hcond, hc, ↓reduceIte]
        rw [heq s1 h1]
        cases C.run (b2 s1) h1 with
        | error e => rfl
        | ok p2 => exact ih p2.1 p2.2
  unfold read_markers C.cwhile
  rw [C.run_bind, ← cwhile_go_congr bodyFn]
  · unfold C.cwhile at hrunEnd
    change C.run (C.cwhile.go (fun s => pure (!s.done, s)) bodyFn C.fuel { done := false, ret := .ok JPEG_SUSPENDED }) h = .ok (sEnd, hEnd) at hrunEnd
    rw [hrunEnd]; rfl
  · intro s1 h1
    dsimp (config := { zetaHave := true }) only [bodyFn, dispatch]
    rfl






