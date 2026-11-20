import ZlibNgF.Proof.«inflate.c.header-modes»

/-!
# The gzip header modes `FLAGS`, `TIME`, `OS`, `EXLEN` of `inflate` (`ZlibNgF`)

Each mode falls through to the next (`FLAGS → TIME → OS → EXLEN → EXTRA`), so its statement takes the statement of
the next mode as a hypothesis.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)

theorem rank_FLAGS : rank FLAGS = 25 := by decide
theorem rank_TIME : rank TIME = 24 := by decide
theorem rank_OS : rank OS = 23 := by decide
theorem rank_EXLEN : rank EXLEN = 22 := by decide
theorem rank_EXTRA : rank EXTRA = 21 := by decide

/-- `(state->flags & 0x0200) && (state->wrap & 4)` of a state with the invariant. -/
theorem LI.hcrcOn {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    ZlibNg.Inflate.hcrcOn (some E.b) H = .ok ((S.flags &&& 0x0200) != 0 && (S.wrap &&& 4) != 0, H) := by
  simp [ZlibNg.Inflate.hcrcOn, bind_app, li.ldState]

/-- `if ((state->flags & 0x0200) && (state->wrap & 4)) CRC2(...)` followed by `k`. -/
theorem crc2_tail {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (k : X Unit) {Q : Except Ex Unit → IL → Heap → Prop}
    (hk : ∀ H' v, LI E l H' z { S with check := v } → H'.gzheaders = H.gzheaders → SatX H' l k Q) :
    SatX H l (do
      if ← ZlibNg.Inflate.hcrcOn E.c.st then CRC2 E.c
      k) Q := by
  refine SatX.bind (SatX.lift_eq li.hcrcOn ?_)
  dsimp only
  split
  · refine SatX.bind (SatX.mono (li.crc2 eo) ?_)
    rintro r l4 H4 ⟨rfl, rfl, v, li4, hg4⟩
    exact hk _ _ li4 hg4
  · exact hk _ _ li rfl

/-- The same with `CRC4`. -/
theorem crc4_tail {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (k : X Unit) {Q : Except Ex Unit → IL → Heap → Prop}
    (hk : ∀ H' v, LI E l H' z { S with check := v } → H'.gzheaders = H.gzheaders → SatX H' l k Q) :
    SatX H l (do
      if ← ZlibNg.Inflate.hcrcOn E.c.st then CRC4 E.c
      k) Q := by
  refine SatX.bind (SatX.lift_eq li.hcrcOn ?_)
  dsimp only
  split
  · refine SatX.bind (SatX.mono (li.crc4 eo) ?_)
    rintro r l4 H4 ⟨rfl, rfl, v, li4, hg4⟩
    exact hk _ _ li4 hg4
  · exact hk _ _ li rfl

/-- `f` keeps the buffer fields of a header (or nulls a buffer pointer). -/
def HKeep (f : GzHeader → GzHeader) : Prop :=
  ∀ g, ((f g).extra = g.extra ∨ (f g).extra = .null) ∧ (f g).extra_max = g.extra_max ∧
    ((f g).name = g.name ∨ (f g).name = .null) ∧ (f g).name_max = g.name_max ∧
    ((f g).comment = g.comment ∨ (f g).comment = .null) ∧ (f g).comm_max = g.comm_max

/-- `if (state->head != NULL) state->head->field = ...;` as a load and a store of the record. -/
theorem LI.stHdrF {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) {k : Nat} (hk : E.hp = some k) (f : GzHeader → GzHeader) (hf : HKeep f)
    :
    Sat H (do let g ← ldHeader (some k); stHeader (some k) (f g)) (fun _ H' => LI E l H' z S) := by
  obtain ⟨g, hgk⟩ := li.hdrRec hk
  refine Sat.bind (Sat.of_eq (show ldHeader (some k) H = .ok (g, H) by simp [ldHeader, hgk]) ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf g
  exact Sat.mono (li.stHdr eo hk hgk (f g) h1 h2 h3 h4 h5 h6) (fun _ _ q => q.1)

/-- One store into the header when there is one, followed by `k`. -/
theorem hdr1_tail {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (f : GzHeader → GzHeader) (hf : HKeep f) (k : X Unit)
    {Q : Except Ex Unit → IL → Heap → Prop}
    (hk : ∀ H', LI E l H' z S → SatX H' l k Q) :
    SatX H l (do
      let hd ← headOf E.c.st
      if hd != none then
        let g ← ldHeader hd
        stHeader hd (f g)
      k) Q := by
  refine SatX.bind (SatX.lift_eq li.headOf ?_)
  dsimp only
  cases hhp : E.hp with
  | none =>
    have he : ((none : HeaderPtr) != none) = false := rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    exact hk _ li
  | some kk =>
    have hne : (some kk != (none : HeaderPtr)) = true := rfl
    simp only [hne, ↓reduceIte]
    obtain ⟨g, hgk⟩ := li.hdrRec hhp
    refine SatX.bind (SatX.lift_eq (show ldHeader (some kk) H = .ok (g, H) by simp [ldHeader, hgk]) ?_)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf g
    refine SatX.bind (SatX.lift (Sat.mono (li.stHdr eo hhp hgk (f g) h1 h2 h3 h4 h5 h6) ?_))
    rintro _ H2 ⟨li2, -⟩
    exact hk _ li2

/-- Two stores into the header when there is one, followed by `k`. -/
theorem hdr2_tail {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (f1 f2 : GzHeader → GzHeader) (hf1 : HKeep f1) (hf2 : HKeep f2)
    (k : X Unit)
    {Q : Except Ex Unit → IL → Heap → Prop} (hk : ∀ H', LI E l H' z S → SatX H' l k Q) :
    SatX H l (do
      let hd ← headOf E.c.st
      if hd != none then
        let g ← ldHeader hd
        stHeader hd (f1 g)
        let g ← ldHeader hd
        stHeader hd (f2 g)
      k) Q := by
  refine SatX.bind (SatX.lift_eq li.headOf ?_)
  dsimp only
  cases hhp : E.hp with
  | none =>
    have he : ((none : HeaderPtr) != none) = false := rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    exact hk _ li
  | some kk =>
    have hne : (some kk != (none : HeaderPtr)) = true := rfl
    simp only [hne, ↓reduceIte]
    obtain ⟨g, hgk⟩ := li.hdrRec hhp
    refine SatX.bind (SatX.lift_eq (show ldHeader (some kk) H = .ok (g, H) by simp [ldHeader, hgk]) ?_)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf1 g
    refine SatX.bind (SatX.lift (Sat.mono (li.stHdr eo hhp hgk (f1 g) h1 h2 h3 h4 h5 h6) ?_))
    rintro _ H2 ⟨li2, -⟩
    obtain ⟨g2, hgk2⟩ := li2.hdrRec hhp
    refine SatX.bind (SatX.lift_eq (show ldHeader (some kk) H2 = .ok (g2, H2) by simp [ldHeader, hgk2]) ?_)
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hf2 g2
    refine SatX.bind (SatX.lift (Sat.mono (li2.stHdr eo hhp hgk2 (f2 g2) e1 e2 e3 e4 e5 e6) ?_))
    rintro _ H3 ⟨li3, -⟩
    exact hk _ li3

/-- `state->mode = md;` and the fall-through into the mode `md`. -/
theorem fall_ok {E : Env} {f : Ctx → X Unit} {md : UInt32} (run : ModeRun E f (·.mode = md))
    (lo : HEAD ≤ md) (hi : md ≤ SYNC) (q : md < LENLENS ∨ LIT < md)
    {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) {m : Nat}
    (hμ : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + rank md ≤ m)
    (ho : l.out = E.O0 ∨ (rank S.mode ≤ 2 → rank md ≤ 2)) :
    SatX H l (do (MonadLiftT.monadLift (setMode E.c.st md) : X Unit); f E.c) (Post E m) := by
  refine SatX.bind (SatX.lift (Sat.mono (li.setQuiet md lo hi q ho) ?_))
  intro _ H1 li1
  exact run _ _ _ _ li1 rfl m (by unfold μ; exact hμ)

/-- `INITBITS(); state->mode = md;` and the fall-through into the mode `md`. -/
theorem initfall_ok {E : Env} {f : Ctx → X Unit} {md : UInt32} (run : ModeRun E f (·.mode = md))
    (lo : HEAD ≤ md) (hi : md ≤ SYNC) (q : md < LENLENS ∨ LIT < md)
    {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) {m : Nat}
    (hμ : 32 * (8 * l.have_.toNat + l.left.toNat) + rank md ≤ m)
    (ho : l.out = E.O0 ∨ (rank S.mode ≤ 2 → rank md ≤ 2)) :
    SatX H l (do INITBITS; (MonadLiftT.monadLift (setMode E.c.st md) : X Unit); f E.c) (Post E m) := by
  refine SatX.bind (initbits_ok ?_)
  have e0 : (0 : UInt8).toNat = 0 := rfl
  exact fall_ok run lo hi q (li.setBits (l' := { l with hold := 0, bits := 0 }) rfl rfl rfl rfl rfl
    (by show (0 : UInt8) ≤ 39; decide))
    (by show 32 * (8 * l.have_.toNat + (0 : UInt8).toNat + l.left.toNat) + _ ≤ m; rw [e0]; omega) ho

/-- `SET_BAD(msg); break;` with the input bits conserved. -/
theorem bad_ok {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) {m : Nat}
    (hμ : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) < m) (msg : String) {i : Nat}
    (hi : strTable.findIdx? (· == msg) = some i) :
    SatX H l (do (MonadLiftT.monadLift (SET_BAD E.c msg) : X Unit); pure ()) (Post E m) := by
  refine SatX.bind (SatX.lift (Sat.mono (li.setBad msg hi) ?_))
  rintro _ H1 ⟨z1, li1⟩
  refine SatX.pure (post_ok li1 ?_)
  unfold μ; dsimp only; rw [rank_BAD]; omega

/-- `ret = v; SET_BAD(msg)` for a code `v` of `inflate_table`: the next trip (`BAD`) sets `ret` again. -/
theorem bad_ok_ret {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) (v : Int32)
    {m : Nat} (hμ : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) < m) (msg : String) {i : Nat}
    (hi : strTable.findIdx? (· == msg) = some i) :
    SatX H { l with ret := v } (do (MonadLiftT.monadLift (SET_BAD E.c msg) : X Unit); pure ()) (Post E m) := by
  refine SatX.bind (SatX.lift (Sat.mono (li.setBad msg hi) ?_))
  rintro _ H1 ⟨z1, li1⟩
  refine SatX.pure ⟨z1, _, Or.inr ⟨rfl, l.ret, li1⟩, ?_⟩
  unfold μ; dsimp only; rw [rank_BAD]; omega

/-- The result of `NEEDBITS(n)` at the start of a mode: the leave case is done. -/
theorem needbits_then {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (eo : EnvOK E)
    (li : LI E l H z S) (n : UInt32) (hn : n.toNat ≤ 32) {m : Nat} {k : X Unit}
    (hk : ∀ l1, LI E l1 H z S → n.toNat ≤ l1.bits.toNat → l1.left = l.left →
      8 * l1.have_.toNat + l1.bits.toNat = 8 * l.have_.toNat + l.bits.toNat → SatX H l1 k (Post E m)) :
    SatX H l (do NEEDBITS n; k) (Post E m) := by
  refine SatX.bind (SatX.mono (needbits_ok eo li n hn) ?_)
  rintro r l1 H1 ⟨rfl, li1, p1, hb1, hr⟩
  rcases r with e | ⟨⟩
  · obtain ⟨rfl, -, h0⟩ := hr
    exact ⟨⟨z, S, li1⟩, Why.have0 h0⟩
  exact hk l1 li1 hr (by rw [p1.1]) p1.2

theorem run_EXLEN (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_EXTRA (·.mode = EXTRA)) :
    ModeRun E inflate_EXLEN (·.mode = EXLEN) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 22 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_EXLEN] at hμ
  unfold inflate_EXLEN
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  dsimp only
  split
  · refine needbits_then eo li 16 (by decide) ?_
    intro l1 li1 h16 hleft hT
    refine SatX.bind (SatX.get ?_)
    dsimp only
    refine SatX.bind (SatX.lift (Sat.mono (li1.wrS (fun s => { s with length := l1.hold.toUInt16.toUInt32 })
      (fun _ _ c => { c with }) rfl) ?_))
    intro _ H2 li2
    refine hdr1_tail eo li2 (fun g => { g with extra_len := l1.hold.toUInt16.toUInt32 })
      (fun g => ⟨Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩) _ ?_
    intro H3 li3
    refine crc2_tail eo li3 _ ?_
    intro H4 _ li4 _
    refine SatX.bind (initbits_ok ?_)
    have e0 : (0 : UInt8).toNat = 0 := rfl
    exact fall_ok hX (by decide) (by decide) (Or.inl (by decide))
      (li4.setBits (l' := { l1 with hold := 0, bits := 0 }) rfl rfl rfl rfl rfl (by show (0 : UInt8) ≤ 39; decide))
      (by show 32 * (8 * l1.have_.toNat + (0 : UInt8).toNat + l1.left.toNat) + rank EXTRA ≤ m
          rw [e0, rank_EXTRA, hleft]; omega) (Or.inl (li1.outEq (by rw [hm]; decide)))
  · refine hdr1_tail eo li (fun g => { g with extra := .null })
      (fun g => ⟨Or.inr rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩) _ ?_
    intro H3 li3
    exact fall_ok hX (by decide) (by decide) (Or.inl (by decide)) li3 (by rw [rank_EXTRA]; omega)
      (Or.inl (li.outEq (by rw [hm]; decide)))

theorem run_OS (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_EXLEN (·.mode = EXLEN)) :
    ModeRun E inflate_OS (·.mode = OS) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 23 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_OS] at hμ
  unfold inflate_OS
  refine needbits_then eo li 16 (by decide) ?_
  intro l1 li1 h16 hleft hT
  refine SatX.bind (SatX.get ?_)
  dsimp only
  refine hdr2_tail eo li1 (fun g => { g with xflags := (l1.hold &&& 0xff).toUInt32.toInt32 })
    (fun g => { g with os := (l1.hold >>> 8).toUInt32.toInt32 })
    (fun g => ⟨Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩)
    (fun g => ⟨Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩) _ ?_
  intro H3 li3
  refine crc2_tail eo li3 _ ?_
  intro H4 v4 li4 _
  exact initfall_ok hX (by decide) (by decide) (Or.inl (by decide)) li4
    (by rw [rank_EXLEN, hleft]; omega) (Or.inl (li1.outEq (by rw [hm]; decide)))

theorem run_TIME (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_OS (·.mode = OS)) :
    ModeRun E inflate_TIME (·.mode = TIME) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 24 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_TIME] at hμ
  unfold inflate_TIME
  refine needbits_then eo li 32 (by decide) ?_
  intro l1 li1 h32 hleft hT
  refine SatX.bind (SatX.get ?_)
  dsimp only
  refine hdr1_tail eo li1 (fun g => { g with time := l1.hold.toUInt32.toUInt64 })
    (fun g => ⟨Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩) _ ?_
  intro H3 li3
  refine crc4_tail eo li3 _ ?_
  intro H4 v4 li4 _
  exact initfall_ok hX (by decide) (by decide) (Or.inl (by decide)) li4
    (by rw [rank_OS, hleft]; omega) (Or.inl (li1.outEq (by rw [hm]; decide)))

theorem run_FLAGS (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_TIME (·.mode = TIME)) :
    ModeRun E inflate_FLAGS (·.mode = FLAGS) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 25 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_FLAGS] at hμ
  unfold inflate_FLAGS
  refine needbits_then eo li 16 (by decide) ?_
  intro l1 li1 h16 hleft hT
  refine SatX.bind (SatX.get ?_)
  dsimp only
  refine SatX.bind (SatX.lift (Sat.mono (li1.wrS (fun s => { s with flags := l1.hold.toUInt32.toInt32 })
    (fun _ _ c => c) rfl) ?_))
  intro _ H2 li2
  refine SatX.bind (SatX.lift_eq li2.ldState ?_)
  dsimp only
  have hb : 32 * (8 * l1.have_.toNat + l1.bits.toNat + l1.left.toNat) < m := by rw [hleft]; omega
  split
  · exact bad_ok li2 hb "unknown compression method" (strIdx 27 (by decide) (by decide) (by decide))
  split
  · exact bad_ok li2 hb "unknown header flags set" (strIdx 28 (by decide) (by decide) (by decide))
  refine hdr1_tail eo li2 (fun g => { g with text := ((l1.hold >>> 8) &&& 1).toUInt32.toInt32 })
    (fun g => ⟨Or.inl rfl, rfl, Or.inl rfl, rfl, Or.inl rfl, rfl⟩) _ ?_
  intro H3 li3
  refine crc2_tail eo li3 _ ?_
  intro H4 v4 li4 _
  exact initfall_ok hX (by decide) (by decide) (Or.inl (by decide)) li4
    (by rw [rank_TIME, hleft]; omega) (Or.inl (li1.outEq (by rw [hm]; decide)))

end ZlibNgF.Proof.InflateLoop
