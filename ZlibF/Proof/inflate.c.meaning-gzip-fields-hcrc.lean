import ZlibF.Proof.«inflate.c.meaning-gzip-fields-pos»

/-!
# inflate.c: `HCRC` keeps the format meaning

`case HCRC:` with `FHCRC` set waits for the two bytes of the header CRC (`NEEDBITS(16)`), and
compares them with the low 16 bits of `check`, the CRC-32 of the header so far. A mismatch is
`BAD`: no gzip member has a wrong header CRC (`gzipDecodes_hcrc`). Otherwise, and at once
without `FHCRC`, the header is complete: `check = crc32(0, NULL, 0) = 0`, `TYPE`.

The module also has the field-mode form of `NEEDBITS` (`GzAt.needbits`).
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningBits Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

/-! ## `NEEDBITS` in a field mode -/

theorem hm_bits {s : InflateState} {wrap : Api.Wrap} {configured : Nat} {bytes : List UInt8}
    (hm : HeaderMatches s wrap configured bytes) (wrapped : wrap ≠ .raw)
    (range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) (hold : UInt64) (bits : UInt32)
    (flagsOk : s.mode = FLAGS → bits.toNat ≤ 16)
    (posOk : TIME ≤ s.mode → s.mode ≤ HCRC → s.flags.toInt = gzipFlagsWord bytes →
      GzipPosition s (bytes.getD 3 0) bytes →
      GzipPosition { s with hold := hold, bits := bits } (bytes.getD 3 0) bytes) :
    HeaderMatches { s with hold := hold, bits := bits } wrap configured bytes := by
  obtain ⟨rawHead, _, _, flagsC, gzC, wrappedC, last0, total0, _⟩ := hm
  refine ⟨rawHead, fun m => ?_, fun m => ?_, fun m => ?_, fun lo hi => ?_, wrappedC, last0, total0,
    fun raw => absurd raw wrapped⟩
  · have e : s.mode = HEAD := m
    have := range.1
    rw [e] at this
    exact absurd this (by decide)
  · have e : s.mode = DICTID := m
    have := range.2
    rw [e] at this
    exact absurd this (by decide)
  · obtain ⟨a, _, c', d⟩ := flagsC m
    exact ⟨a, flagsOk m, c', d⟩
  · obtain ⟨a, b, c', d, e, p⟩ := gzC lo hi
    exact ⟨a, b, c', d, e, posOk lo hi c' p⟩

/-- `NEEDBITS(n)` in a field mode, with the loop meaning at the end when the held bits are
allowed by the position (`ok`). -/
theorem GzAt.needbits {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest)
    (range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) (short : GzipShort bytes) (n : UInt32) (small : n.toNat ≤ 32)
    {ok : Nat → Prop}
    (flagsOk : s.mode = FLAGS → ∀ b, ok b → b ≤ 16)
    (posOk : ∀ (hold : UInt64) (bits : UInt32) (b : List UInt8), ok bits.toNat → TIME ≤ s.mode →
      s.mode ≤ HCRC → s.flags.toInt = gzipFlagsWord b → GzipPosition (loopState s l) (b.getD 3 0) b →
      GzipPosition { loopState s l with hold := hold, bits := bits } (b.getD 3 0) b) :
    ∃ result l' j, runX (NEEDBITS n) l h = .ok ((result, l'), h) ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits } ∧
      l'.next = inputAdvance l.next j ∧ l'.have_.toNat + j = l.have_.toNat ∧
      l'.bits.toNat = l.bits.toNat + 8 * j ∧
      (result = .ok () → n.toNat ≤ l'.bits.toNat) ∧
      (result = .error Ex.leave → l'.have_ = 0 ∧ l'.bits.toNat < n.toNat) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      l'.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧
      (ok l'.bits.toNat → LoopMatches c f h l') := by
  obtain ⟨result, l', j, run, shape, _, _, enough, leaveFacts, kinds, bitsMax, loopAt⟩ :=
    MeaningBits.LoopMatches.needbits_at (g.loop short) (ok := ok)
      (fun zs' s' checked stage st' hs' stageM wrapM hold bits okb => by
        have same : zs' = zs ∧ s' = s := by
          rw [g.st] at st'
          cases st'
          exact ⟨rfl, Option.some.inj (hs'.symm.trans g.hs)⟩
        obtain ⟨rfl, rfl⟩ := same
        obtain ⟨b, rfl⟩ := MeaningDictid.stage_of_header stageM (UInt32.le_trans range.2 (by decide))
        obtain ⟨hmb, window, used⟩ := wrapM
        exact ⟨stageM, hm_bits hmb g.wrapped range hold bits (fun m => flagsOk m _ okb)
          (fun lo hi fw p => posOk hold bits b okb lo hi fw p), window, used⟩) n small
  obtain ⟨r2, l2, j2, run2, jle, binv2, _, bits2, _, _, _, _, _, _, next2⟩ :=
    NEEDBITS_run_cursor g.binv n (by omega)
  have same := run.symm.trans run2
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨⟨rfl, rfl⟩, _⟩ := same
  have count : l'.have_.toNat + j2 = l.have_.toNat := by
    have a := binv2.have_eq
    have b := g.binv.have_eq
    rw [List.length_drop] at a
    omega
  exact ⟨result, l', j2, run, shape, next2, count, bits2, enough, leaveFacts, kinds, bitsMax, loopAt⟩

/-! ## Run rules -/

theorem runX_wrZ {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (f : ZStream → ZStream) (l : IL) :
    runX (monadLift (wrZ c.strm f) : X Unit) l h = .ok ((.ok (), l), r.put h (f z)) := by
  apply runX_lift_ok
  rw [E.strm, wrZ_eq, E.hz]

theorem envSetI {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (s' : InflateState) : Env c (Zlib.Inflate.Spec.setI h zs s') r zs z s' :=
  ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact E.hz, setI_istates_same _ _ _⟩

theorem keep_ssi (h : Heap) (r : ZStreamRef) (zs : Nat) (a : InflateState) (z : ZStream)
    (b : InflateState) (l : IL) :
    InputKept h (Zlib.Inflate.Spec.setI (r.put (Zlib.Inflate.Spec.setI h zs a) z) zs b) l :=
  ((InputKept.setI _ _ _ l).trans (InputKept.stream _ _ _ l)).trans (InputKept.setI _ _ _ l)

/-- After `NEEDBITS`, the bytes it pulled join the held bytes. -/
theorem GzAt.pulled {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) {l' : IL} {j : Nat}
    (loop' : LoopMatches c f h l') (range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC)
    (inEq : l'.in_ = l.in_) (count : l'.have_.toNat + j = l.have_.toNat)
    (bitsEq : l'.bits.toNat = l.bits.toNat + 8 * j) :
    GzAt c f h l' zs s bytes (rest ++ (f.inp.drop (loopRead l)).take j) := by
  obtain ⟨b', r', g'⟩ := GzAt.of_loop loop' g.st g.hs range g.gz
  have readEq : loopRead l' = loopRead l + j := by
    simp only [loopRead, inEq]
    have := g.haveLe
    omega
  have chunkLen : ((f.inp.drop (loopRead l)).take j).length = j := by
    have := g.binv.have_eq
    rw [List.length_drop] at this
    simp only [List.length_take, List.length_drop]
    omega
  have eq : b' ++ r' = bytes ++ (rest ++ (f.inp.drop (loopRead l)).take j) := by
    rw [← g'.input, readEq, List.take_add, ← List.append_assoc, g.input, List.append_assoc]
  have lens : r'.length = (rest ++ (f.inp.drop (loopRead l)).take j).length := by
    rw [List.length_append, chunkLen]
    have a := g'.bits
    have b := g.bits
    omega
  have split := List.append_inj' eq lens
  obtain ⟨rfl, rfl⟩ := split
  exact g'

theorem getD_append {a t : List UInt8} {i : Nat} (lt : i < a.length) :
    (a ++ t).getD i 0 = a.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left lt]

theorem magic_prefix {b t : List UInt8} (gz : IsGzipHeader b) : [31, 139] <+: b ++ t := by
  have pre : b.take 2 <+: b ++ t := (List.take_prefix 2 b).trans (List.prefix_append _ _)
  rwa [gz] at pre

/-! ## The header CRC -/

theorem toUInt8_of {x : UInt8} {k : Nat} (e : x.toNat = k % 256) : x = (k % 256).toUInt8 := by
  apply UInt8.toNat_inj.mp
  rw [e]
  simp [Nat.toUInt8, UInt8.toNat_ofNat]

theorem le16_of_value {x y : UInt8} {n : Nat} (small : n < 2 ^ 16)
    (value : x.toNat + 256 * y.toNat = n) : [x, y] = le16 n := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [le16, List.cons.injEq, and_true]
  refine ⟨toUInt8_of (by omega), toUInt8_of (by omega)⟩

theorem value_of_le16 {x y : UInt8} {n : Nat} (small : n < 2 ^ 16) (e : [x, y] = le16 n) :
    x.toNat + 256 * y.toNat = n := by
  simp only [le16, List.cons.injEq, and_true] at e
  obtain ⟨ex, ey⟩ := e
  rw [ex, ey]
  simp [Nat.toUInt8, UInt8.toNat_ofNat]
  omega

/-! ## `HCRC` -/

set_option maxHeartbeats 1000000 in
theorem hcrc_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {zs : Nat} {s : InflateState} {bytes rest : List UInt8} (E : Env c h r zs z s)
    (g : GzAt c f h l zs s bytes rest) (mode : s.mode = HCRC) :
    ∃ result l' h', runX (inflate_HCRC c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have lo : TIME ≤ s.mode := by rw [mode]; decide
  have hi : s.mode ≤ HCRC := by rw [mode]; decide
  have high : s.mode ≤ DICTID := by rw [mode]; decide
  obtain ⟨gzb, len4, flagsInt, crcF, _, posAll⟩ := g.hm.2.2.2.2.1 lo hi
  obtain ⟨bitsLe, noCrcBits, mt, xfl, os, ex, nm, cm, fields, bytesEq⟩ := posAll.2.2.2.2.2.2 mode
  have method : bytes.getD 2 0 = 8 := by rw [bytesEq]; simp [Gzip.header]
  have flagsEq : s.flags = flagsWord (bytes.getD 3 0) := flagsWord_eq flagsInt method
  have head := g.head
  have w4 := g.wrap4
  have bitsAligned := g.bits
  obtain ⟨small, mtLength, exLimit, nmOk, cmOk⟩ := fields
  unfold inflate_HCRC
  rw [runX_bind, runX_rdS E]
  simp only [flagsEq, flagsWord_hcrc]
  by_cases fh : (bytes.getD 3 0).toNat / 2 % 2 = 1
  · simp only [fh, decide_true, ↓reduceIte]
    obtain ⟨result, l', j, run, shape, next, count, bitsCount, enough, leaveFacts, kinds, bitsMax,
      loopAt⟩ := g.needbits range (by rw [bytesEq]; exact gzipShort_hcrc ⟨small, mtLength, exLimit, nmOk, cmOk⟩ fh)
        16 (by decide) (ok := fun b => b ≤ 16)
        (fun m => by rw [mode] at m; exact absurd m (by decide))
        (fun hold bits b okb _ _ fw p => by
          obtain ⟨_, _, rest'⟩ := p.2.2.2.2.2.2 mode
          have same := flagsWord_byte (flagsEq ▸ fw)
          exact gzpos_hcrc mode ⟨okb, fun nf => absurd fh (by rw [← same]; omega), rest'⟩)
    have n16 : (16 : UInt32).toNat = 16 := rfl
    rw [runX_bind, run]
    rcases kinds with rfl | rfl
    · have atLeast := enough rfl
      rw [n16] at atLeast bitsMax
      have bits16 : l'.bits.toNat = 16 := by
        have := bitsLe
        change l.bits.toNat ≤ 16 at this
        omega
      have inEq : l'.in_ = l.in_ := by rw [shape]
      have g' := g.pulled (loopAt (by omega)) range inEq count bitsCount
      have restLen : (rest ++ (f.inp.drop (loopRead l)).take j).length = 2 := by
        have := g'.bits
        omega
      obtain ⟨x, y, xy⟩ : ∃ x y, rest ++ (f.inp.drop (loopRead l)).take j = [x, y] := by
        generalize rest ++ (f.inp.drop (loopRead l)).take j = w at restLen
        match w, restLen with
        | [x, y], _ => exact ⟨x, y, rfl⟩
      rw [xy] at g'
      have holdVal : l'.hold.toNat = x.toNat + 256 * y.toNat := by
        rw [g'.hold]
        simp [leValue]
      have checkEq : s.check = (crc32 bytes).toUInt64 := crcF fh
      have crcSmall : (crc32 bytes).toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
      have maskVal : (s.check &&& 65535).toNat = (crc32 bytes).toNat % 2 ^ 16 := by
        rw [checkEq, UInt64.toNat_and]
        change (crc32 bytes).toUInt64.toNat &&& (2 ^ 16 - 1) = _
        rw [Nat.and_two_pow_sub_one_eq_mod]
        rfl
      simp only []
      rw [runX_bind, runX_ldS E]
      simp only []
      rw [runX_bind, runX_get]
      simp only [w4, Bool.true_and]
      by_cases mismatch : (l'.hold != s.check &&& 65535) = true
      · simp only [mismatch, ↓reduceIte]
        obtain ⟨i, _, bad⟩ := runX_badMode E lit_header_crc_mismatch l'
        rw [runX_bind, bad]
        simp only [runX_pure]
        refine ⟨_, _, _, rfl, Or.inl ⟨rfl, Or.inr ?_⟩⟩
        refine g'.bad (s' := { s with mode := BAD }) (by simp [badHeap]) rfl
          ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ ?_
        refine gz_doomed g.gz g'.input (magic_prefix gzb) ?_
        intro source out valid pre
        rw [bytesEq] at pre
        have hc := gzipDecodes_hcrc valid ⟨small, mtLength, exLimit, nmOk, cmOk⟩ fh pre
        rw [← bytesEq] at hc
        have v := value_of_le16 crcSmall hc
        apply (show ¬ (l'.hold != s.check &&& 65535) = false from by simp [mismatch])
        simp only [bne_eq_false_iff_eq]
        apply UInt64.toNat_inj.mp
        rw [holdVal, maskVal, v]
      · simp only [Bool.not_eq_true] at mismatch
        simp only [mismatch, Bool.false_eq_true, ↓reduceIte]
        have sameVal : l'.hold = s.check &&& 65535 := by simpa using mismatch
        have v : x.toNat + 256 * y.toNat = (crc32 bytes).toNat % 2 ^ 16 := by
          rw [← holdVal, ← maskVal, sameVal]
        have xyEq := le16_of_value crcSmall v
        rw [runX_bind, runX_INITBITS]
        simp only []
        rw [runX_bind, runX_ldS E]
        simp only [head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_lift_ok (crc32_null_run h)]
        simp only []
        rw [runX_bind, runX_wrS E]
        simp only []
        rw [runX_bind, runX_wrZ (envSetI E _)]
        simp only []
        rw [runX_setMode ((envSetI E _).put _)]
        refine ⟨_, _, _, rfl, Or.inl ⟨rfl, Or.inl ?_⟩⟩
        refine g'.body range (header := bytes ++ [x, y]) (by simp) (keep_ssi _ _ _ _ _ _ _)
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
          (Kept.update s TYPE s.flags 0 s.length) rfl ?_ ?_ rfl
        · refine ⟨bytes.getD 3 0, mt, xfl, os, ex, nm, cm, small, mtLength, exLimit, nmOk, cmOk, ?_⟩
          rw [if_pos fh, ← bytesEq, xyEq]
        · show s.flags = _
          rw [flagsEq, getD_append (by omega)]
    · have below := (leaveFacts rfl).2
      rw [n16] at below
      exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (loopAt (by omega))⟩⟩
  · simp only [fh, decide_false, Bool.false_eq_true, ↓reduceIte]
    have nf : (bytes.getD 3 0).toNat / 2 % 2 = 0 := by omega
    have bits0 : l.bits = 0 := noCrcBits nf
    have restNil : rest = [] := by
      have := bitsAligned
      rw [bits0] at this
      have z : rest.length = 0 := by simp at this; omega
      exact List.eq_nil_of_length_eq_zero z
    subst restNil
    rw [runX_bind, runX_ldS E]
    simp only [head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [runX_bind, runX_lift_ok (crc32_null_run h)]
    simp only []
    rw [runX_bind, runX_wrS E]
    simp only []
    rw [runX_bind, runX_wrZ (envSetI E _)]
    simp only []
    rw [runX_setMode ((envSetI E _).put _)]
    refine ⟨_, _, _, rfl, Or.inl ⟨rfl, Or.inl ?_⟩⟩
    have hold0 : l.hold = 0 := by
      apply UInt64.toNat_inj.mp
      rw [g.hold]
      rfl
    refine g.body range (l' := l) (header := bytes ++ []) (by simp) (keep_ssi _ _ _ _ _ _ _)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hold0 bits0 rfl
      (Kept.update s TYPE s.flags 0 s.length) rfl ?_ ?_ rfl
    · refine ⟨bytes.getD 3 0, mt, xfl, os, ex, nm, cm, small, mtLength, exLimit, nmOk, cmOk, ?_⟩
      rw [if_neg (by omega), List.append_nil, List.append_nil, ← bytesEq]
    · show s.flags = _
      simp [flagsEq]

#print axioms hcrc_step

end Zlib.Inflate.Proofs.MeaningGzipFields
