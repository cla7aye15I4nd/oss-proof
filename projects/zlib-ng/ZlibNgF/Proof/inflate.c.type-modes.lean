import ZlibNgF.Proof.«inflate.c.gzextra-modes»

/-!
# The modes `HCRC`, `DICTID`, `DICT`, `TYPE`, `TYPEDO` of `inflate` (`ZlibNgF`)

`DICTID` falls through to `DICT`, `DICT` to `TYPE`, `TYPE` to `TYPEDO` (with the state still in mode `TYPE`, so the
statement of `TYPEDO` accepts both modes). `TYPEDO` selects the fixed tables for a fixed block (`fixedtables`), whose
decoding-table predicate is checked by evaluation.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)

theorem rank_TYPE : rank TYPE = 11 := by decide
theorem rank_DICT : rank DICT = 26 := by decide
theorem rank_DICTID : rank DICTID = 27 := by decide

/-! ## Steps -/

/-- `BYTEBITS()`. -/
theorem bytebits_ok {H : Heap} {l : IL} {Q : Except Ex PUnit → IL → Heap → Prop}
    (q : Q (.ok ⟨⟩) { l with hold := l.hold >>> (l.bits &&& 7).toUInt32.toUInt64, bits := l.bits - (l.bits &&& 7) } H) :
    SatX H l BYTEBITS Q := by
  unfold BYTEBITS
  have h7 : (l.bits &&& 7).toUInt32 < 64 := by
    rw [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32, UInt8.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.lift_eq (a := l.hold >>> (l.bits &&& 7).toUInt32.toUInt64)
    (by simp only [shr64, h7, ↓reduceIte]; rfl) ?_)
  exact SatX.set q

theorem bytebits_le (b : UInt8) : (b - (b &&& 7)).toNat ≤ b.toNat := by
  have h : (b &&& 7) ≤ b := by
    rw [UInt8.le_iff_toNat_le, UInt8.toNat_and]; exact Nat.and_le_left
  rw [UInt8.toNat_sub_of_le _ _ h]; omega

/-- `RESTORE()`: the locals go back into the stream and the state. -/
theorem LI.restore {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    SatX H l (RESTORE E.c) (fun r l' H' => r = .ok ⟨⟩ ∧ l' = l ∧ ∃ z' S', LI E l H' z' S' ∧ S'.mode = S.mode) := by
  unfold RESTORE
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.lift (Sat.mono (li.wrZ (fun z => { z with
    next_out := l.put
    avail_out := l.left
    next_in := l.next
    avail_in := l.have_ }) rfl rfl rfl) ?_))
  intro _ H1 li1
  have hb : l.bits.toUInt32 ≤ 39 := by
    have := li.bits; rw [UInt8.le_iff_toNat_le] at this
    rw [UInt32.le_iff_toNat_le, UInt8.toNat_toUInt32]; exact this
  exact SatX.lift (Sat.mono (li1.wrS (fun s => { s with hold := l.hold, bits := l.bits.toUInt32 })
    (fun _ _ c => { c with bits := hb }) rfl) (fun _ H2 li2 => ⟨rfl, rfl, _, _, li2, rfl⟩))

/-! ## `HCRC` -/

/-- The header check of `HCRC` (`NEEDBITS(16)` and the comparison with the check value), followed by `k`. -/
theorem hcrcHead_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) {m : Nat} (hb : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) < m) (k : X Unit)
    (hk : ∀ l' H' S', LI E l' H' z S' → S'.mode = S.mode →
      8 * l'.have_.toNat + l'.bits.toNat ≤ 8 * l.have_.toNat + l.bits.toNat → l'.left = l.left →
      SatX H' l' k (Post E m)) :
    SatX H l (do
      let s ← ldState E.c.st
      if (s.flags &&& 0x0200) != 0 then
        NEEDBITS 16
        let s ← ldState E.c.st
        if (s.wrap &&& 4) != 0 && (← get).hold != (s.check &&& 0xffff) then
          SET_BAD E.c "header crc mismatch"
          return
        INITBITS
      k) (Post E m) := by
  refine SatX.bind (SatX.lift_eq li.ldState ?_)
  dsimp (config := { zeta := false }) only
  split
  · refine needbits_then eo li 16 (by decide) ?_
    intro l1 li1 h16 hleft hT
    refine SatX.bind (SatX.lift_eq li1.ldState ?_)
    refine SatX.bind (SatX.get ?_)
    dsimp (config := { zeta := false }) only
    split
    · exact bad_ok li1 (by rw [hleft]; omega) "header crc mismatch"
        (strIdx 11 (by decide) (by decide) (by decide))
    · refine SatX.bind (initbits_ok ?_)
      have e0 : (0 : UInt8).toNat = 0 := rfl
      exact hk _ _ _ (li1.setBits rfl rfl rfl rfl rfl (by show (0 : UInt8) ≤ 39; decide)) rfl
        (by show 8 * l1.have_.toNat + (0 : UInt8).toNat ≤ _; rw [e0]; omega) hleft
  · exact hk _ _ _ li rfl (Nat.le_refl _) rfl

/-- The header record stores of `HCRC` (`hcrc`, `done`), followed by `k`. -/
theorem hcrcHdr_ok {E : Env} (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) (hmx : S.mode ≠ EXTRA) (k : X Unit) {Q : Except Ex Unit → IL → Heap → Prop}
    (hk : ∀ H', LI E l H' z S → SatX H' l k Q) :
    SatX H l (do
      let hd ← headOf E.c.st
      if hd != none then
        let s ← ldState E.c.st
        let g ← ldHeader hd
        stHeader hd { g with hcrc := (s.flags >>> 9) &&& 1 }
        let g ← ldHeader hd
        stHeader hd { g with done := 1 }
      k) Q := by
  refine SatX.bind (SatX.lift_eq li.headOf ?_)
  dsimp (config := { zeta := false }) only
  cases hhp : E.hp with
  | none =>
    have he : ((none : HeaderPtr) != none) = false := rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    exact hk _ li
  | some kk =>
    have hne : (some kk != (none : HeaderPtr)) = true := rfl
    simp only [hne, ↓reduceIte]
    refine SatX.bind (SatX.lift_eq li.ldState ?_)
    obtain ⟨g, hgk⟩ := li.hdrRec hhp
    refine SatX.bind (SatX.lift_eq (show ldHeader (some kk) H = .ok (g, H) by simp [ldHeader, hgk]) ?_)
    refine SatX.bind (SatX.lift (Sat.mono (li.stHdr eo hhp hgk { g with hcrc := (S.flags >>> 9) &&& 1 }
      (Or.inl rfl) rfl (Or.inl rfl) rfl (Or.inl rfl) rfl hmx) ?_))
    rintro _ H2 ⟨li2, -⟩
    obtain ⟨g2, hgk2⟩ := li2.hdrRec hhp
    refine SatX.bind (SatX.lift_eq (show ldHeader (some kk) H2 = .ok (g2, H2) by simp [ldHeader, hgk2]) ?_)
    refine SatX.bind (SatX.lift (Sat.mono (li2.stHdr eo hhp hgk2 { g2 with done := 1 }
      (Or.inl rfl) rfl (Or.inl rfl) rfl (Or.inl rfl) rfl hmx) ?_))
    rintro _ H3 ⟨li3, -⟩
    exact hk _ li3

theorem run_HCRC (E : Env) (eo : EnvOK E) : ModeRun E inflate_HCRC (·.mode = HCRC) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 18 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_HCRC] at hμ
  unfold inflate_HCRC
  refine hcrcHead_ok eo li (by omega) _ ?_
  intro l1 H1 S1 li1 hm1 hT hleft
  have hmx : S1.mode ≠ EXTRA := by rw [hm1, hm]; decide
  refine hcrcHdr_ok eo li1 hmx _ ?_
  intro H2 li2
  refine SatX.bind (SatX.lift_eq li2.ldState ?_)
  dsimp (config := { zeta := false }) only
  have fin : ∀ H3 z3 S3, LI E l1 H3 z3 S3 →
      SatX H3 l1 (MonadLiftT.monadLift (setMode E.c.st TYPE) : X Unit) (Post E m) := by
    intro H3 z3 S3 li3
    refine SatX.lift (Sat.mono (li3.setQuiet TYPE (by decide) (by decide) (Or.inl (by decide)) (by decide)) ?_)
    intro _ H4 li4
    refine post_ok li4 ?_
    unfold μ; dsimp only; rw [rank_TYPE, hleft]; omega
  split
  · refine SatX.bind (SatX.lift (Sat.mono (li2.wrS (fun s => { s with check := CRC32_INITIAL_VALUE })
      (fun _ _ c => c) rfl) ?_))
    intro _ H3 li3
    refine SatX.bind (SatX.lift (Sat.mono (li3.wrZ (fun z => { z with adler := CRC32_INITIAL_VALUE })
      rfl rfl rfl) ?_))
    intro _ H4 li4
    exact fin _ _ _ li4
  · exact fin _ _ _ li2

/-! ## `TYPE`, `DICT`, `DICTID` -/

theorem run_TYPE (E : Env) (hX : ModeRun E inflate_TYPEDO (fun S => S.mode = TYPEDO ∨ S.mode = TYPE)) :
    ModeRun E inflate_TYPE (·.mode = TYPE) := by
  intro l H z S li hm m hμ
  unfold inflate_TYPE
  split
  · exact SatX.bind (SatX.throw ⟨z, S, li⟩)
  · exact hX l H z S li (Or.inr hm) m hμ

theorem run_DICT (E : Env) (hX : ModeRun E inflate_TYPE (·.mode = TYPE)) :
    ModeRun E inflate_DICT (·.mode = DICT) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 26 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_DICT] at hμ
  unfold inflate_DICT
  refine SatX.bind (SatX.lift_eq (li.rdS (·.havedict)) ?_)
  dsimp (config := { zeta := false }) only
  split
  · refine SatX.bind (SatX.mono li.restore ?_)
    rintro r l1 H1 ⟨rfl, rfl, z1, S1, li1, -⟩
    exact SatX.bind (SatX.throw ⟨li1.inv, li1.frame⟩)
  · refine SatX.bind (SatX.lift (Sat.mono (li.wrS (fun s => { s with check := ADLER32_INITIAL_VALUE })
      (fun _ _ c => c) rfl) ?_))
    intro _ H1 li1
    refine SatX.bind (SatX.lift (Sat.mono (li1.wrZ (fun z => { z with adler := ADLER32_INITIAL_VALUE })
      rfl rfl rfl) ?_))
    intro _ H2 li2
    exact fall_ok hX (by decide) (by decide) (Or.inl (by decide)) (by decide) li2 (by rw [rank_TYPE]; omega)

theorem run_DICTID (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_DICT (·.mode = DICT)) :
    ModeRun E inflate_DICTID (·.mode = DICTID) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 27 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_DICTID] at hμ
  unfold inflate_DICTID
  refine needbits_then eo li 32 (by decide) ?_
  intro l1 li1 h32 hleft hT
  refine SatX.bind (SatX.get ?_)
  dsimp only
  generalize (ZSWAP32 l1.hold.toUInt32).toUInt64 = v
  refine SatX.bind (SatX.lift (Sat.mono (li1.wrS (fun s => { s with check := v }) (fun _ _ c => c) rfl) ?_))
  intro _ H1 li2
  refine SatX.bind (SatX.lift (Sat.mono (li2.wrZ (fun z => { z with adler := v }) rfl rfl rfl) ?_))
  intro _ H2 li3
  exact initfall_ok hX (by decide) (by decide) (Or.inl (by decide)) (by decide) li3
    (by rw [rank_DICT, hleft]; omega)

/-! ## The fixed tables -/

open ZlibNgF.Proof.InflateTab (EntryOK LenOK CodeTable TabAt linkTest) in
/-- `EntryOK` by evaluation. -/
def entryB (e : Code) (m : Nat) (dist : Bool) : Bool :=
  decide (1 ≤ (ZlibNg.InflateP.CODE_BITS e).toNat) && decide ((ZlibNg.InflateP.CODE_BITS e).toNat ≤ e.bits.toNat) &&
  decide (e.bits.toNat ≤ m) && decide (e.op &&& 16 = 0 → e.op &&& 64 = 0 → e.op &&& 0xf0 = 0) &&
  decide (dist = true → (e.op &&& 64 = 0 ∨ e.op &&& 16 ≠ 0) → 1 ≤ e.val.toNat)

open ZlibNgF.Proof.InflateTab (EntryOK) in
theorem entryB_ok {e : Code} {m : Nat} {dist : Bool} (h : entryB e m dist = true) : EntryOK e m dist := by
  simp only [entryB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h
  exact ⟨a1, a2, a3, a4, a5⟩

/-- `LenOK 0` by evaluation. -/
def lenB (e : Code) : Bool :=
  decide (e.op = 0 → e.bits.toNat ≤ 15) && decide (e.op ≠ 0 → e.bits.toNat ≤ 20) &&
  decide (e.op &&& 16 ≠ 0 → 1 ≤ e.val.toNat ∧ e.val.toNat + 2 ^ (e.bits.toNat - e.op.toNat % 16) ≤ 259)

open ZlibNgF.Proof.InflateTab (LenOK) in
theorem lenB_ok {e : Code} (h : lenB e = true) : LenOK 0 e := by
  simp only [lenB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨a1, a2⟩, a3⟩ := h
  exact ⟨fun h => by have := a1 h; omega, fun h => by have := a2 h; omega, a3⟩

open ZlibNgF.Proof.InflateTab (linkTest) in
/-- A one-level table of `a.size` entries whose entries pass the checks and are not links. -/
def tabB (a : Array Code) (m : Nat) (dist : Bool) : Bool :=
  (List.range a.size).all fun j => entryB a[j]! m dist && (dist || lenB a[j]!) && !linkTest dist a[j]!

open ZlibNgF.Proof.InflateTab (CodeTable linkTest) in
theorem tabB_ok {a : Array Code} {n m : Nat} {dist : Bool} (h : tabB a m dist = true) (hn1 : 1 ≤ n) (hn2 : n ≤ 15)
    (hs : 2 ^ n = a.size) : CodeTable a 0 a.size n m dist := by
  have h' : ∀ j, j < a.size → entryB a[j]! m dist = true ∧ (dist = true ∨ lenB a[j]! = true) ∧
      linkTest dist a[j]! = false := by
    intro j hj
    have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨hn1, hn2, by omega, Nat.le_refl _, fun j _ hj => entryB_ok (h' j hj).1, fun hd j _ hj => ?_,
    fun j _ hj hl => ?_⟩
  · rcases (h' j (by omega)).2.1 with e | e
    · rw [hd] at e; cases e
    · exact lenB_ok e
  · rw [(h' j hj).2.2] at hl; cases hl

theorem lenfix_tabB : tabB lenfix 28 false = true := by decide +kernel
theorem distfix_tabB : tabB distfix 28 true = true := by decide +kernel
theorem lenfix_size : lenfix.size = 512 := by decide +kernel
theorem distfix_size : distfix.size = 32 := by decide +kernel

open ZlibNgF.Proof.InflateTab (CodeTable) in
theorem lenfix_table : CodeTable lenfix 0 512 9 28 false := by
  have := tabB_ok (n := 9) lenfix_tabB (by decide) (by decide) (by rw [lenfix_size])
  rwa [lenfix_size] at this

open ZlibNgF.Proof.InflateTab (CodeTable) in
theorem distfix_table : CodeTable distfix 0 32 5 28 true := by
  have := tabB_ok (n := 5) distfix_tabB (by decide) (by decide) (by rw [distfix_size])
  rwa [distfix_size] at this

/-- The four stores of `fixedtables`. -/
def fixF (s : InflateState) : InflateState :=
  { s with lencode := .val (.ref .lenfix 0), lenbits := 9, distcode := .val (.ref .distfix 0), distbits := 5 }

theorem fixedtables_eq {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) :
    fixedtables (some b) H = ZlibNg.Inflate.wrS (some b) fixF H := by
  have hd : ∃ d, H.bytes b = some d := by
    unfold Heap.istate at hs; split at hs <;> simp_all
  obtain ⟨d, hd⟩ := hd
  have hs' : H.istates b = some S := by simpa [Heap.istate, hd] using hs
  simp [fixedtables, ZlibNg.Inflate.wrS, bind_app, ldState, stState, Heap.istate, hd, hs', InflateInv.upd_upd,
    fixF]

/-- `fixedtables()` from a mode without mode clauses. -/
theorem LI.fixed {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (hq : S.mode < LENLENS ∨ LIT < S.mode) :
    Sat H (fixedtables (some E.b)) (fun _ H' => LI E l H' z (fixF S)) := by
  obtain ⟨r, H', e, li'⟩ := li.wrS fixF (fun _ _ c => { c with
    lencode := ⟨_, rfl, Or.inr (Or.inl rfl)⟩
    distcode := ⟨_, rfl, Or.inr (Or.inr rfl)⟩
    tables := Or.inr ⟨rfl, rfl⟩
    modes := InflateInv.ModeOK.quiet _ _ hq }) rfl
  exact ⟨r, H', (fixedtables_eq li.hs).trans e, li'⟩

/-- The mode clauses of `LEN_` with the fixed tables. -/
theorem fixedModeOK (b : Nat) (S : InflateState) :
    InflateInv.ModeOK b (view { fixF S with mode := LEN_ }).m where
  lenlens := fun e => absurd (show LEN_ = LENLENS from e) (by decide)
  codelens := fun e => absurd (show LEN_ = CODELENS from e) (by decide)
  decode := fun _ => ⟨Or.inr (Or.inl ⟨rfl, 512, lenfix_table⟩), Or.inr (Or.inr ⟨rfl, 32, distfix_table⟩)⟩
  extra := fun e => by
    rcases e with e | e
    · exact absurd (show LEN_ = LENEXT from e) (by decide)
    · exact absurd (show LEN_ = DISTEXT from e) (by decide)
  offset := fun e => by
    rcases e with e | e
    · exact absurd (show LEN_ = DISTEXT from e) (by decide)
    · exact absurd (show LEN_ = MATCH from e) (by decide)

theorem LI.setLen_ {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z (fixF S)) :
    Sat H (setMode (some E.b) LEN_) (fun _ H' => LI E l H' z { fixF S with mode := LEN_ }) :=
  li.wrS (fun s => { s with mode := LEN_ }) (fun _ _ c => { c with
    mode_lo := by show HEAD ≤ LEN_; decide
    mode_hi := by show LEN_ ≤ SYNC; decide
    modes := fixedModeOK _ S
    extraLen := fun e => absurd (show LEN_ = EXTRA from e) (by decide) }) rfl

theorem rank_CHECK : rank CHECK = 2 := by decide

/-! ## `TYPEDO` -/

theorem run_TYPEDO (E : Env) (eo : EnvOK E) :
    ModeRun E inflate_TYPEDO (fun S => S.mode = TYPEDO ∨ S.mode = TYPE) := by
  intro l H z S li hm m hμ
  have hr : 10 ≤ rank S.mode := by rcases hm with e | e <;> rw [e] <;> decide
  have hq : S.mode < LENLENS ∨ LIT < S.mode := by rcases hm with e | e <;> rw [e] <;> decide
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 10 ≤ m := by unfold μ at hμ; omega
  have hb39 : l.bits.toNat ≤ 39 := li.bits
  unfold inflate_TYPEDO
  refine SatX.bind (SatX.lift_eq (li.rdS (·.last)) ?_)
  dsimp (config := { zeta := false }) only
  split
  · refine SatX.bind (bytebits_ok ?_)
    have hbb := bytebits_le l.bits
    have li1 := li.setBits (l' := { l with
      hold := l.hold >>> (l.bits &&& 7).toUInt32.toUInt64
      bits := l.bits - (l.bits &&& 7) }) rfl rfl rfl rfl rfl
      (by show l.bits - (l.bits &&& 7) ≤ 39; rw [UInt8.le_iff_toNat_le]; show _ ≤ 39; omega)
    refine SatX.bind (SatX.lift (Sat.mono (li1.setQuiet CHECK (by decide) (by decide) (Or.inr (by decide))
      (by decide)) ?_))
    intro _ H1 li2
    refine SatX.pure (post_ok li2 ?_)
    unfold μ; dsimp only; rw [rank_CHECK]
    show 32 * (8 * l.have_.toNat + (l.bits - (l.bits &&& 7)).toNat + l.left.toNat) + 2 < m
    omega
  · refine needbits_then eo li 3 (by decide) ?_
    intro l1 li1 h3 hleft hT
    have h3' : 3 ≤ l1.bits.toNat := h3
    have hb1 : l1.bits.toNat ≤ 39 := li1.bits
    refine SatX.bind (bits_ok 1 (by decide) ?_)
    dsimp (config := { zeta := false }) only
    refine SatX.bind (SatX.lift (Sat.mono (li1.wrS (fun s => { s with
      last := (l1.hold &&& ((1 : UInt32) <<< 1 - 1).toUInt64).toUInt32.toInt32 }) (fun _ _ c => c) rfl) ?_))
    intro _ H2 li2
    refine SatX.bind (dropbits_ok 1 (by decide) ?_)
    have e1 : (l1.bits - (1 : UInt32).toUInt8).toNat = l1.bits.toNat - 1 := by
      rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega)]; rfl
    have li3 := li2.setBits (l' := { l1 with
      hold := l1.hold >>> (1 : UInt32).toUInt64
      bits := l1.bits - (1 : UInt32).toUInt8 }) rfl rfl rfl rfl rfl
      (by show l1.bits - (1 : UInt32).toUInt8 ≤ 39; rw [UInt8.le_iff_toNat_le, e1]; show _ ≤ 39; omega)
    generalize hl2 : ({ l1 with
      hold := l1.hold >>> (1 : UInt32).toUInt64
      bits := l1.bits - (1 : UInt32).toUInt8 } : IL) = l2 at li3 ⊢
    have hb2 : l2.bits.toNat = l1.bits.toNat - 1 := by rw [← hl2]; exact e1
    have hh2 : l2.have_ = l1.have_ := by rw [← hl2]
    have hlf2 : l2.left = l1.left := by rw [← hl2]
    refine SatX.bind (bits_ok 2 (by decide) ?_)
    dsimp (config := { zeta := false }) only
    have e2 : ∀ H' z' S', LI E l2 H' z' S' →
        LI E { l2 with hold := l2.hold >>> (2 : UInt32).toUInt64, bits := l2.bits - (2 : UInt32).toUInt8 } H' z' S' ∧
        μ { l2 with hold := l2.hold >>> (2 : UInt32).toUInt64, bits := l2.bits - (2 : UInt32).toUInt8 } S' < m := by
      intro H' z' S' li'
      have e2 : (l2.bits - (2 : UInt32).toUInt8).toNat = l2.bits.toNat - 2 := by
        rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; show 2 ≤ _; omega)]; rfl
      refine ⟨li'.setBits rfl rfl rfl rfl rfl
        (by show l2.bits - (2 : UInt32).toUInt8 ≤ 39; rw [UInt8.le_iff_toNat_le, e2]; show _ ≤ 39; omega), ?_⟩
      have := rank_le S'.mode
      unfold μ; dsimp only; rw [e2, hh2, hlf2, hleft]; omega
    have fin : ∀ H' z' S', LI E l2 H' z' S' → SatX H' l2 (DROPBITS 2) (Post E m) := by
      intro H' z' S' li'
      obtain ⟨li'', hlt⟩ := e2 H' z' S' li'
      exact dropbits_ok 2 (by decide) (post_ok li'' hlt)
    split
    · refine SatX.bind (SatX.lift (Sat.mono (li3.setQuiet STORED (by decide) (by decide) (Or.inl (by decide))
        (by decide)) ?_))
      intro _ H4 li4
      exact fin _ _ _ li4
    split
    · refine SatX.bind (SatX.lift (Sat.mono (li3.fixed hq) ?_))
      intro _ H4 li4
      refine SatX.bind (SatX.lift (Sat.mono li4.setLen_ ?_))
      intro _ H5 li5
      dsimp (config := { zeta := false }) only
      split
      · refine SatX.bind (dropbits_ok 2 (by decide) ?_)
        exact SatX.throw ⟨_, _, (e2 _ _ _ li5).1⟩
      · exact fin _ _ _ li5
    split
    · refine SatX.bind (SatX.lift (Sat.mono (li3.setQuiet TABLE (by decide) (by decide) (Or.inl (by decide))
        (by decide)) ?_))
      intro _ H4 li4
      exact fin _ _ _ li4
    · refine SatX.bind (SatX.lift (Sat.mono (li3.setBad "invalid block type"
        (strIdx 16 (by decide) (by decide) (by decide))) ?_))
      rintro _ H4 ⟨z4, li4⟩
      exact fin _ _ _ li4

end ZlibNgF.Proof.InflateLoop
