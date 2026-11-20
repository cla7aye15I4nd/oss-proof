import ZlibNgF.Proof.«inflate.c.steps»

/-!
# The header modes of `inflate` (`ZlibNgF`)

`HEAD` (zlib and gzip headers), from a state with the loop invariant: no fault, and the trip leaves, or ends with
the invariant and a lower measure.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)

theorem rank_HEAD : rank HEAD = 28 := by decide
theorem rank_TYPEDO : rank TYPEDO = 10 := by decide
theorem rank_BAD : rank BAD = 0 := by decide
theorem rank_le (m : UInt32) : rank m ≤ 31 := Nat.min_le_left _ _

/-- A trip that ends normally below the measure. -/
theorem post_ok {E : Env} {m : Nat} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (h : μ l S < m) : Post E m (.ok ()) l H := ⟨z, S, Or.inl li, h⟩

/-- The zlib header after the gzip test and the `head->done` store (the code of `inflate_HEAD` from
`if (!(state->wrap & 1) || ...)` on). -/
def headZ (c : Ctx) : X Unit := do
  let s ← ldState c.st
  let bad ← if (s.wrap &&& 1) == 0 then pure true else do
    let b8 ← BITS 8
    pure (((b8 <<< 8) + ((← get).hold >>> 8)) % 31 != 0)
  if bad then
    SET_BAD c "incorrect header check"
    return
  if (← BITS 4) != Z_DEFLATED then
    SET_BAD c "unknown compression method"
    return
  DROPBITS 4
  let len := (← BITS 4).toUInt32 + 8
  modify fun l => { l with len := len }
  let s ← ldState c.st
  if len > MAX_WBITS.toUInt32 || (s.wbits != 0 && len > s.wbits) then
    SET_BAD c "invalid window size"
    return
  if s.wbits == 0 then wrS c.st fun s => { s with wbits := len }
  wrS c.st fun s => { s with flags := 0 }
  wrS c.st fun s => { s with check := ADLER32_INITIAL_VALUE }
  wrZ c.strm fun z => { z with adler := ADLER32_INITIAL_VALUE }
  let hold := (← get).hold
  setMode c.st (if (hold &&& 0x200) != 0 then DICTID else TYPE)
  INITBITS

/-- The zlib header from the method test on. -/
def headZ2 (c : Ctx) : X Unit := do
  if (← BITS 4) != Z_DEFLATED then
    SET_BAD c "unknown compression method"
    return
  DROPBITS 4
  let len := (← BITS 4).toUInt32 + 8
  modify fun l => { l with len := len }
  let s ← ldState c.st
  if len > MAX_WBITS.toUInt32 || (s.wbits != 0 && len > s.wbits) then
    SET_BAD c "invalid window size"
    return
  if s.wbits == 0 then wrS c.st fun s => { s with wbits := len }
  wrS c.st fun s => { s with flags := 0 }
  wrS c.st fun s => { s with check := ADLER32_INITIAL_VALUE }
  wrZ c.strm fun z => { z with adler := ADLER32_INITIAL_VALUE }
  let hold := (← get).hold
  setMode c.st (if (hold &&& 0x200) != 0 then DICTID else TYPE)
  INITBITS

theorem headZ2_ok {E : Env} {m : Nat} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hm : S.mode = HEAD) (h16 : 16 ≤ l.bits.toNat)
    (hμ : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 1 ≤ m) :
    SatX H l (headZ2 E.c) (Post E m) := by
  have hb39 : l.bits.toNat ≤ 39 := li.bits
  unfold headZ2
  refine SatX.bind (bits_ok 4 (by decide) ?_)
  dsimp only
  by_cases hd : ((l.hold &&& ((1 : UInt32) <<< 4 - 1).toUInt64) != Z_DEFLATED) = true
  · simp only [hd, ↓reduceIte]
    refine SatX.bind (SatX.lift (Sat.mono (li.setBad "unknown compression method" (strIdx 27 (by decide) (by decide) (by decide))) ?_))
    rintro _ H1 ⟨z1, li1⟩
    refine SatX.pure (post_ok li1 ?_)
    unfold μ; dsimp only; rw [rank_BAD]; omega
  simp only [hd, Bool.false_eq_true, ↓reduceIte]
  have hb4 : (l.bits - (4 : UInt32).toUInt8).toNat = l.bits.toNat - 4 := by
    rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; show 4 ≤ _; omega)]; rfl
  let l1 : IL := { l with hold := l.hold >>> (4 : UInt32).toUInt64, bits := l.bits - (4 : UInt32).toUInt8 }
  have li1 : LI E l1 H z S := li.setBits rfl rfl rfl rfl rfl (by
    show l.bits - (4 : UInt32).toUInt8 ≤ 39
    rw [UInt8.le_iff_toNat_le, hb4]; show _ ≤ 39; omega)
  refine SatX.bind (dropbits_ok 4 (by decide) ?_)
  refine SatX.bind (bits_ok 4 (by decide) ?_)
  dsimp only
  generalize (l1.hold &&& ((1 : UInt32) <<< 4 - 1).toUInt64) = v
  refine SatX.bind (SatX.modify ?_)
  let l2 : IL := { l1 with len := v.toUInt32 + 8 }
  have li2 : LI E l2 H z S := li1.locals rfl rfl rfl rfl rfl rfl
  refine SatX.bind (SatX.lift_eq li2.ldState ?_)
  dsimp only
  have hlt : (32 * (8 * l2.have_.toNat + l2.bits.toNat + l2.left.toNat) + 1 ≤ m) := by
    show 32 * (8 * l.have_.toNat + (l.bits - (4 : UInt32).toUInt8).toNat + l.left.toNat) + 1 ≤ m
    rw [hb4]; omega
  by_cases hw : (decide (v.toUInt32 + 8 > MAX_WBITS.toUInt32) || S.wbits != 0 && decide (v.toUInt32 + 8 > S.wbits))
      = true
  · simp only [hw, ↓reduceIte]
    refine SatX.bind (SatX.lift (Sat.mono (li2.setBad "invalid window size" (strIdx 25 (by decide) (by decide) (by decide))) ?_))
    rintro _ H1 ⟨z1, li3⟩
    refine SatX.pure (post_ok li3 ?_)
    unfold μ; dsimp only; rw [rank_BAD]; omega
  simp only [hw, Bool.false_eq_true, ↓reduceIte]
  have h15 : v.toUInt32 + 8 ≤ 15 := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hw
    exact UInt32.not_lt.mp hw.1
  suffices key : ∀ (H2 : Heap) (z2 : ZStream) (S2 : InflateState), LI E l2 H2 z2 S2 → S2.mode = HEAD →
      SatX H2 l2 (do
        (MonadLiftT.monadLift (ZlibNg.Inflate.wrS E.c.st fun s => { s with flags := 0 }) : X Unit)
        (MonadLiftT.monadLift (ZlibNg.Inflate.wrS E.c.st fun s => { s with check := ADLER32_INITIAL_VALUE }) : X Unit)
        (MonadLiftT.monadLift (wrZ E.c.strm fun z => { z with adler := ADLER32_INITIAL_VALUE }) : X Unit)
        let hold := (← get).hold
        (MonadLiftT.monadLift (setMode E.c.st (if (hold &&& 0x200) != 0 then DICTID else TYPE)) : X Unit)
        INITBITS) (Post E m) by
    by_cases h0 : (S.wbits == 0) = true
    · simp only [h0, ↓reduceIte]
      refine SatX.bind (SatX.lift (Sat.mono (li2.wrS (fun s => { s with wbits := v.toUInt32 + 8 })
        (fun _ _ c => { c with wbits := h15 }) rfl) ?_))
      intro _ H2 li3
      exact key _ _ _ li3 hm
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      exact key _ _ _ li2 hm
  intro H2 z2 S2 li3 hm2
  have hO : l2.out = E.O0 := li3.outEq (by rw [hm2]; decide)
  refine SatX.bind (SatX.lift (Sat.mono (li3.wrS (fun s => { s with flags := 0 }) (fun _ _ c => c) rfl) ?_))
  intro _ H3 li4
  refine SatX.bind (SatX.lift (Sat.mono (li4.wrS (fun s => { s with check := ADLER32_INITIAL_VALUE })
    (fun _ _ c => c) rfl) ?_))
  intro _ H4 li5
  refine SatX.bind (SatX.lift (Sat.mono (li5.wrZ (fun z => { z with adler := ADLER32_INITIAL_VALUE }) rfl rfl rfl) ?_))
  intro _ H5 li6
  refine SatX.bind (SatX.get ?_)
  dsimp only
  have hq : ∀ md : UInt32, (md = DICTID ∨ md = TYPE) →
      SatX H5 l2 (do (MonadLiftT.monadLift (setMode E.c.st md) : X Unit); INITBITS) (Post E m) := by
    intro md hmd
    have lo : HEAD ≤ md := by rcases hmd with rfl | rfl <;> decide
    have hi : md ≤ SYNC := by rcases hmd with rfl | rfl <;> decide
    have q : md < LENLENS ∨ LIT < md := by rcases hmd with rfl | rfl <;> decide
    refine SatX.bind (SatX.lift (Sat.mono (li6.setQuiet md lo hi q (Or.inl hO) (fun h => h.mono rfl (FrS.no_bits
      (by show 0 < (l.bits - (4 : UInt32).toUInt8).toNat; rw [hb4]; omega)))) ?_))
    intro _ H6 li7
    refine initbits_ok (post_ok (li7.setBits rfl rfl rfl rfl rfl (by show (0 : UInt8) ≤ 39; decide)) ?_)
    have := rank_le md
    have e0 : (0 : UInt8).toNat = 0 := rfl
    unfold μ; dsimp only; rw [e0]
    show 32 * (8 * l.have_.toNat + 0 + l.left.toNat) + rank md < m
    omega
  by_cases hd2 : ((l2.hold &&& 0x200) != 0) = true
  · have := hq DICTID (Or.inl rfl); simp only [hd2, ↓reduceIte]; exact this
  · have := hq TYPE (Or.inr rfl); simp only [hd2, Bool.false_eq_true, ↓reduceIte]; exact this

theorem headZ_ok {E : Env} {m : Nat} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hm : S.mode = HEAD) (h16 : 16 ≤ l.bits.toNat)
    (hμ : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 1 ≤ m) :
    SatX H l (headZ E.c) (Post E m) := by
  have hb39 : l.bits.toNat ≤ 39 := li.bits
  unfold headZ
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  dsimp only
  have bad : SatX H l (do (MonadLiftT.monadLift (SET_BAD E.c "incorrect header check") : X Unit); pure ())
      (Post E m) := by
    refine SatX.bind (SatX.lift (Sat.mono (li.setBad "incorrect header check"
      (strIdx 13 (by decide) (by decide) (by decide))) ?_))
    rintro _ H1 ⟨z1, li1⟩
    refine SatX.pure (post_ok li1 ?_)
    unfold μ; dsimp only; rw [rank_BAD]; omega
  by_cases h1 : (S.wrap &&& 1 == 0) = true
  · simp only [h1, ↓reduceIte]
    refine SatX.bind (SatX.pure ?_)
    exact bad
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  refine SatX.bind (bits_ok 8 (by decide) ?_)
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.pure ?_)
  dsimp only
  by_cases h2 : ((((l.hold &&& ((1 : UInt32) <<< 8 - 1).toUInt64) <<< 8) + (l.hold >>> 8)) % 31 != 0) = true
  · simp only [h2, ↓reduceIte]; exact bad
  · simp only [h2, Bool.false_eq_true, ↓reduceIte]
    exact headZ2_ok li hm h16 hμ

theorem run_HEAD (E : Env) (eo : EnvOK E) : ModeRun E inflate_HEAD (fun S => S.mode = HEAD) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 28 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_HEAD] at hμ
  unfold inflate_HEAD
  refine SatX.bind (SatX.lift_eq (li.rdS (·.wrap)) ?_)
  dsimp only
  by_cases hw : (S.wrap == 0) = true
  · simp only [hw, ↓reduceIte]
    refine SatX.bind (SatX.lift (Sat.mono (li.setQuiet TYPEDO (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (li.outEq (by rw [hm]; decide)))) ?_))
    intro _ H1 li1
    refine SatX.pure (post_ok li1 ?_)
    unfold μ; simp only [rank_TYPEDO]; omega
  simp only [hw, Bool.false_eq_true, ↓reduceIte]
  refine SatX.bind (SatX.mono (needbits_ok eo li 16 (by decide)) ?_)
  rintro r l1 H1 ⟨rfl, li1, p1, hb1, hr⟩
  rcases r with e | ⟨⟩
  · obtain ⟨rfl, -, h0⟩ := hr
    exact ⟨⟨z, S, li1⟩, Why.have0 h0⟩
  have h16 : 16 ≤ l1.bits.toNat := hr
  have hT : 8 * l1.have_.toNat + l1.bits.toNat = 8 * l.have_.toNat + l.bits.toNat := p1.2
  have hleft : l1.left = l.left := by rw [p1.1]
  refine SatX.bind (SatX.lift_eq li1.ldState ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  by_cases hg : (S.wrap &&& 2 != 0 && l1.hold == 35615) = true
  · simp only [hg, ↓reduceIte]
    suffices key : ∀ (H2 : Heap) (z2 : ZStream) (S2 : InflateState), LI E l1 H2 z2 S2 →
        SatX H2 l1 (do
          (MonadLiftT.monadLift (ZlibNg.Inflate.wrS E.c.st fun s => { s with check := CRC32_INITIAL_VALUE }) : X Unit)
          CRC2 E.c
          INITBITS
          (MonadLiftT.monadLift (setMode E.c.st FLAGS) : X Unit)
          pure ()) (Post E m) by
      by_cases h0 : (S.wbits == 0) = true
      · simp only [h0, ↓reduceIte]
        refine SatX.bind (SatX.lift (Sat.mono (li1.wrS (fun s => { s with wbits := MAX_WBITS.toUInt32 })
          (fun _ _ c => { c with wbits := by show MAX_WBITS.toUInt32 ≤ 15; decide }) rfl) ?_))
        intro _ H2 li2
        exact key _ _ _ li2
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        exact key _ _ _ li1
    intro H2 z2 S2 li2
    refine SatX.bind (SatX.lift (Sat.mono (li2.wrS (fun s => { s with check := CRC32_INITIAL_VALUE })
      (fun _ _ c => c) rfl) ?_))
    intro _ H3 li3
    refine SatX.bind (SatX.mono (li3.crc2 eo) ?_)
    rintro r l4 H4 ⟨rfl, hl4, v, li4, -⟩
    rw [hl4]
    refine SatX.bind (initbits_ok ?_)
    have li5 := li4.setBits (l' := { l1 with hold := 0, bits := 0 }) rfl rfl rfl rfl rfl (by show (0 : UInt8) ≤ 39; decide)
    refine SatX.bind (SatX.lift (Sat.mono (li5.setQuiet FLAGS (by decide) (by decide) (Or.inl (by decide))
      (Or.inl (li1.outEq (by rw [hm]; decide))) (fun _ => Fr.ofFreshLt (li1.frLt (FrS.no_bits (by omega))))) ?_))
    intro _ H5 li6
    refine SatX.pure (post_ok li6 ?_)
    have := rank_le FLAGS
    have e0 : (0 : UInt8).toNat = 0 := rfl
    unfold μ; dsimp only; rw [hleft, e0]; omega
  simp only [hg, Bool.false_eq_true, ↓reduceIte]
  have hz : 32 * (8 * l1.have_.toNat + l1.bits.toNat + l1.left.toNat) + 1 ≤ m := by rw [hleft]; omega
  refine SatX.bind (SatX.lift_eq li1.headOf ?_)
  cases hhp : E.hp with
  | none => exact headZ_ok li1 hm h16 hz
  | some k =>
    obtain ⟨g, hgk⟩ := li1.hdrRec hhp
    have hne : (some k != (none : HeaderPtr)) = true := rfl
    simp only [hne, ↓reduceIte]
    refine SatX.bind (SatX.lift_eq (show ldHeader (some k) H1 = .ok (g, H1) by simp [ldHeader, hgk]) ?_)
    refine SatX.bind (SatX.lift (Sat.mono (li1.stHdr eo hhp hgk { g with done := -1 } (Or.inl rfl) rfl (Or.inl rfl)
      rfl (Or.inl rfl) rfl) ?_))
    rintro _ H2 ⟨li2, -⟩
    exact headZ_ok li2 hm h16 hz

end ZlibNgF.Proof.InflateLoop
