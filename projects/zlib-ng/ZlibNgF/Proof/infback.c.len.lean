import ZlibNgF.Proof.«infback.c.lencopy»

/-!
# `inflateBack()`: the mode `LEN` (`ZlibNgF`)

`LEN` takes the fast path (`Proof/infback.c.fast.lean`) with at least 15 input bytes and 3 bytes of room; otherwise
it decodes one literal/length symbol (`decodeSym`): a literal is stored at `put` after `ROOM`, an end of block goes
to `TYPE`, an invalid code to `BAD`; a length takes its extra bits, then a distance symbol and its extra bits, the
distance is checked against the window (`invalid distance too far back`), and the match is copied
(`Proof/infback.c.lencopy.lean`). Every code has at least one bit, so a trip that stays in `LEN` consumes input.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateLoop (withS strIdx bits_ok dropbits_ok store_heap set_get code_extra_le linkTest_dist
  linkTest_len)
open ZlibNgF.Proof.InflateTab (CodeTable EntryOK LenOK linkTest)

/-- The distance check and the copy of a match. -/
theorem len_check {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) (hm : S.mode = LEN)
    (tabs : RTab E.b S.codes S.lencode S.lenbits 28 false ∧ RTab E.b S.codes S.distcode S.distbits 28 true)
    (hb8 : l.bits.toNat < 8) (hlen : S.length ≠ 0) (hoff : 1 ≤ S.offset.toNat) {m : Nat}
    (hμ : 32 * (8 * (l.have_.toNat + t) + l.bits.toNat) + 1 < m) :
    SatX H l (do
      let s ← ldState E.c.st
      let left := (← get).left
      if s.offset > s.wsize - (if s.whave < s.wsize then left else 0) then
        SET_BAD E.c.ctx "invalid distance too far back"
        return
      lenBody E.c
      xwhile (do return (← rdS E.c.st (·.length)) != 0) (lenBody E.c)) (Post E m) := by
  have hn := bm.sh.ws
  have hn1 := bm.sh.n_pos
  have hL := bm.left
  refine SatX.bind (liftEq bm.sh.ldState ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  by_cases hc : S.offset > S.wsize - (if S.whave < S.wsize then l.left else 0)
  · simp only [hc, ↓reduceIte]
    obtain ⟨H', z', e, bm'⟩ := bm.setBad cb "invalid distance too far back"
      (strIdx 20 (by decide) (by decide) (by decide))
    refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
    refine SatX.pure ⟨t, z', _, ⟨bm', Or.inl rfl, BModeOK.quiet _ { S with mode := BAD }
      (by show BAD ≠ LEN; decide) (by show BAD ≠ MATCH; decide)⟩, ?_⟩
    unfold μ; dsimp only; rw [rank_BAD]; omega
  · simp only [hc, ↓reduceIte]
    have hx : (if S.whave < S.wsize then l.left else 0).toNat ≤ S.wsize.toNat := by
      split
      · rw [hn]; exact hL
      · exact Nat.zero_le _
    have hle' : S.offset.toNat ≤ E.n - (if S.whave < S.wsize then l.left else 0).toNat := by
      have := Nat.le_of_not_lt (fun h => hc (UInt32.lt_iff_toNat_lt.mpr h))
      rw [u32_sub_le hx, hn] at this; exact this
    refine len_copy cb ⟨bm, hm, tabs, rfl, rfl, hoff, by omega, fun hw => ?_⟩ hlen hb8 hμ
    have : S.whave < S.wsize := by
      rw [hw, UInt32.lt_iff_toNat_lt, hn]; show 0 < E.n; omega
    simp only [this, ↓reduceIte] at hle'; exact hle'

/-- The extra bits of a length or a distance: `NEEDBITS(extra)`, `BITS(extra)` stored with `g`, `DROPBITS(extra)`. -/
theorem xbits_ok {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) (hb8 : l.bits.toNat < 8) (hx : S.extra.toNat ≤ 28)
    (g : InflateState → UInt32 → InflateState) (hg : ∀ s v, SKeep s (g s v)) (hge : ∀ s v, (g s v).extra = s.extra)
    {Q : Except Ex Unit → IL → Heap → Prop}
    (kL : ∀ l' H', BLv E l' H' → Q (.error .leave) l' H')
    (k : Unit → X Unit)
    (kO : ∀ l' H' t' (b : UInt64), BM E l' H' t' z (g S b.toUInt32) → b.toNat < 2 ^ S.extra.toNat →
      l'.bits.toNat < 8 →
      8 * (l'.have_.toNat + t') + l'.bits.toNat + S.extra.toNat ≤ 8 * (l.have_.toNat + t) + l.bits.toNat →
      SatX H' l' (k ()) Q) :
    SatX H l (do
      NEEDBITS E.c (← rdS E.c.st (·.extra))
      let b ← BITS (← rdS E.c.st (·.extra))
      wrS E.c.st fun s => g s b.toUInt32
      let r ← DROPBITS (← rdS E.c.st (·.extra))
      k r) Q := by
  refine SatX.bind (liftEq (bm.sh.rdS _) ?_)
  refine SatX.bind (needbits_ok cb E.c rfl rfl bm.inB S.extra (by omega) ?_ ?_)
  · intro l' H' t' q hk hI hp h0 _ _
    exact kL _ _ (ZlibNgF.Proof.InfbackLoop.leave_of_pull bm hk hI hp h0)
  intro l1 H1 t1 hk hin1 hmeas hx1 hb1 hp1 _
  have hb1' : l1.bits.toNat ≤ S.extra.toNat + 7 := by
    have : max l.bits.toNat (S.extra.toNat + 7) ≤ S.extra.toNat + 7 := Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩
    omega
  have bm1 : BM E l1 H1 t1 z S := by
    refine ⟨bm.sh.keep hk, hin1, ?_, by rw [hp1]; exact bm.put, by rw [hp1]; exact bm.left, bm.whave⟩
    have := bm.tot; omega
  refine SatX.bind (liftEq (bm1.sh.rdS _) ?_)
  refine SatX.bind (bits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega) ?_)
  dsimp only [BEnv.c]
  refine SatX.bind (SatX.lift (Sat.of_eq (bm1.sh.wrS _) ?_))
  have bm2 := bm1.wS cb (S' := g S (l1.hold &&& ((1 : UInt32) <<< S.extra - 1).toUInt64).toUInt32) (hg _ _)
  refine SatX.bind (liftEq (bm2.sh.rdS _) ?_)
  rw [hge]
  refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
  have hx8 : S.extra.toUInt8.toNat = S.extra.toNat := by
    rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by omega)
  have hd : (l1.bits - S.extra.toUInt8).toNat = l1.bits.toNat - S.extra.toNat := by
    rw [UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by rw [hx8]; exact hx1)), hx8]
  refine kO _ _ t1 _ (bm2.locals rfl rfl rfl rfl) (ZlibNgF.Proof.InflateLoop.bits_lt32 _ _ (by omega))
    (by show (l1.bits - S.extra.toUInt8).toNat < 8; rw [hd]; omega) ?_
  show 8 * (l1.have_.toNat + t1) + (l1.bits - S.extra.toUInt8).toNat + S.extra.toNat ≤ _
  rw [hd]; omega

theorem run_LEN (E : BEnv) : ModeRun E back_LEN (fun S => S.mode = LEN) := by
  intro cb l H t z S bl hm m hμ
  have hb8 : l.bits.toNat < 8 := by
    rcases bl.bits with e | e
    · rw [hm] at e; exact absurd e (by decide)
    · exact e
  have hμ' : 32 * (8 * (l.have_.toNat + t) + l.bits.toNat) + 1 ≤ m := by
    unfold μ at hμ; rw [hm, rank_LEN] at hμ; exact hμ
  have tabs := bl.modes.dec (Or.inl hm)
  unfold back_LEN
  refine SatX.bind (SatX.get ?_)
  dsimp (config := { zeta := false }) only
  by_cases hf : (l.have_ >= INFLATE_FAST_MIN_HAVE && l.left >= INFLATE_FAST_MIN_SAFE) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hf)]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨hf1, hf2⟩ := hf
    exact len_fast cb bl hm (by simpa [INFLATE_FAST_MIN_HAVE, UInt32.le_iff_toNat_le] using hf1)
      (by simpa [INFLATE_FAST_MIN_SAFE, UInt32.le_iff_toNat_le] using hf2) hμ
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)]
    rw [linkTest_len]
    refine SatX.bind (SatX.mono (bdecode cb bl.toBM hb8 tabs.1) ?_)
    rintro r l1 H1 p
    match r, p with
    | .error .leave, p => exact p
    | .ok (), ⟨t1, bm1, hp1, hl1, hmeas1, hent, hlink, hlenok, hcb, hlive, hb35⟩ =>
    refine SatX.bind (SatX.get ?_)
    have hcb1 := hent.cb_pos
    refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
    have hd : (l1.bits - (CODE_BITS l1.here).toUInt8).toNat = l1.bits.toNat - (CODE_BITS l1.here).toNat := by
      have h8 : (CODE_BITS l1.here).toUInt8.toNat = (CODE_BITS l1.here).toNat := by
        rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by have := hent.cb_le; have := hent.bits_le; omega)
      rw [UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by rw [h8]; exact hcb)), h8]
    have bm2 := bm1.locals (l' := { l1 with
      hold := l1.hold >>> (CODE_BITS l1.here).toUInt64
      bits := l1.bits - (CODE_BITS l1.here).toUInt8 }) rfl rfl rfl rfl
    generalize hl2 : ({ l1 with
      hold := l1.hold >>> (CODE_BITS l1.here).toUInt64
      bits := l1.bits - (CODE_BITS l1.here).toUInt8 } : IL) = l2 at bm2 ⊢
    have hb2 : l2.bits.toNat = l1.bits.toNat - (CODE_BITS l1.here).toNat := by rw [← hl2]; exact hd
    have hh2 : l2.here = l1.here := by rw [← hl2]
    have hv2 : l2.have_ = l1.have_ := by rw [← hl2]
    refine SatX.bind (SatX.get ?_)
    dsimp (config := { zeta := false }) only
    refine SatX.bind (SatX.lift (Sat.of_eq (bm2.sh.wrS _) ?_))
    have bm3 := bm2.wS cb (S' := { S with length := l2.here.val.toUInt32 }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [hh2] at bm3 ⊢
    have hm1 : 32 * (8 * (l2.have_.toNat + t1) + l2.bits.toNat) + 32 ≤ 32 * (8 * (l.have_.toNat + t) + l.bits.toNat) := by
      rw [hb2, hv2]; omega
    have hlv : Live l1.here → l2.bits.toNat < 8 := fun h => by have := hlive h; omega
    have fin : ∀ Hx zx (Sx : InflateState), BM E l2 Hx t1 zx Sx → BModeOK E.b Sx → (Sx.mode = BAD ∨ Live l1.here) →
        Post E m (.ok ()) l2 Hx := by
      intro Hx zx Sx bmx mo hx
      refine ⟨t1, zx, Sx, ⟨bmx, ?_, mo⟩, ?_⟩
      · rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (hlv hx)
      · have := rank_le5 Sx.mode; unfold μ; omega
    dsimp (config := { zeta := false }) only
    by_cases hop : (l1.here.op.toNat == 0) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hop)]
      have hop' : l1.here.op = 0 := by
        have : l1.here.op.toNat = 0 := by simpa using hop
        exact UInt8.toNat_inj.mp this
      have hlive' : Live l1.here := Or.inl (by rw [hop']; decide)
      have lit : ∀ lx Hx (Sx : InflateState), BM E lx Hx t1 z Sx → lx.left ≠ 0 → lx.bits = l2.bits →
          lx.have_ = l2.have_ → Sx.codes = S.codes → Sx.lencode = S.lencode → Sx.lenbits = S.lenbits →
          Sx.distcode = S.distcode → Sx.distbits = S.distbits →
          SatX Hx lx (do
            let len ← rdS E.c.st (·.length)
            let l ← get
            Ptr.store l.put len.toUInt8
            let pt ← l.put.add 1
            modify fun l => { l with put := pt }
            modify fun l => { l with left := l.left - 1 }
            setMode E.c.st LEN
            pure () : X Unit) (Post E m) := by
        intro lx Hx Sx bmx hlx hbx hvx e1 e2 e3 e4 e5
        have hL1 := u32_ne_zero hlx
        have hL := bmx.left
        obtain ⟨a, ha, haN⟩ := bmx.winBytes
        refine SatX.bind (liftEq (bmx.sh.rdS _) ?_)
        refine SatX.bind (SatX.get ?_)
        dsimp only
        rw [bmx.put]
        refine SatX.bind (SatX.lift (Sat.of_eq (store_heap ha (by omega) _) ?_))
        have hsz : (a.set! (E.woff + (E.n - lx.left.toNat)) Sx.length.toUInt8).size = a.size := by simp
        have bmy := bmx.winW cb ha hsz (fun j hj => set_get a _ j _ (by omega))
        obtain ⟨a1, ha1, ha1N⟩ := bmy.winBytes
        refine SatX.bind (liftEq (add_nat ha1 1 (by omega)) ?_)
        refine SatX.bind (SatX.modify ?_)
        refine SatX.bind (SatX.modify ?_)
        have bmz : BM E { lx with
            put := .ref (.heap E.wb) (E.woff + (E.n - lx.left.toNat) + 1)
            left := lx.left - 1 }
            { Hx with bytes := upd Hx.bytes E.wb (some (a.set! (E.woff + (E.n - lx.left.toNat)) Sx.length.toUInt8)) }
            t1 z Sx := by
          refine ⟨bmy.sh, ZlibNgF.Proof.InfbackRoom.InB.locals bmy.inB rfl rfl, bmy.tot, ?_, ?_, bmy.whave⟩
          · show Ptr.ref _ _ = Ptr.ref _ _
            rw [u32_sub_le (by show 1 ≤ lx.left.toNat; omega)]; simp only [Ptr.ref.injEq, true_and]
            show _ = E.woff + (E.n - (lx.left.toNat - 1)); omega
          · show (lx.left - 1).toNat ≤ E.n
            rw [u32_sub_le (by show 1 ≤ lx.left.toNat; omega)]; show lx.left.toNat - 1 ≤ E.n; omega
        obtain ⟨e6, bmw⟩ := bmz.setMode cb LEN
        refine SatX.bind (SatX.lift (Sat.of_eq e6 (SatX.pure ?_)))
        refine ⟨t1, z, _, ⟨bmw, Or.inr (by show lx.bits.toNat < 8; rw [hbx]; exact hlv hlive'),
          ⟨fun _ => by rw [e1, e2, e3, e4, e5]; exact tabs, fun e => absurd (show LEN = MATCH from e) (by decide)⟩⟩, ?_⟩
        unfold μ; dsimp only; rw [rank_LEN, hbx, hvx]; omega
      refine SatX.bind (bm3.room cb (fun hl => lit _ _ _ bm3 hl rfl rfl rfl rfl rfl rfl rfl) ?_)
      intro _ H' bm'
      have hn := bm3.sh.ws
      have hn1 := bm3.sh.n_pos
      have hw0 : S.wsize ≠ 0 := fun e => by rw [e] at hn; simp at hn; omega
      exact ⟨(bm'.locals rfl rfl rfl rfl).leave, lit _ _ _ bm' hw0 rfl rfl rfl rfl rfl rfl rfl⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false hop)]
    by_cases h32 : (l1.here.op &&& 32 != 0) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h32)]
      have hlive' : Live l1.here := Or.inr (by simpa using h32)
      obtain ⟨e6, bmw⟩ := bm3.setMode cb TYPE
      refine SatX.bind (SatX.lift (Sat.of_eq e6 (SatX.pure ?_)))
      exact fin _ _ _ bmw (BModeOK.quiet _ { S with length := l1.here.val.toUInt32, mode := TYPE }
        (by show TYPE ≠ LEN; decide) (by show TYPE ≠ MATCH; decide)) (Or.inr hlive')
    rw [ite_eq_right_of_eq_false _ _ (eq_false h32)]
    by_cases h64 : (l1.here.op &&& 64 != 0) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h64)]
      obtain ⟨H', z', e, bm'⟩ := bm3.setBad cb "invalid literal/length code"
        (strIdx 22 (by decide) (by decide) (by decide))
      refine SatX.bind (SatX.lift (Sat.of_eq e (SatX.pure ?_)))
      exact fin _ _ _ bm' (BModeOK.quiet _ { S with length := l1.here.val.toUInt32, mode := BAD }
        (by show BAD ≠ LEN; decide) (by show BAD ≠ MATCH; decide)) (Or.inl rfl)
    rw [ite_eq_right_of_eq_false _ _ (eq_false h64)]
    have hent3 : EntryOK l1.here 28 false := hent
    have h16 : l1.here.op &&& 16 ≠ 0 := by
      intro h16
      have h64' : l1.here.op &&& 64 = 0 := by simpa using h64
      have hf0 := hent.op_lt h16 h64'
      have hne0 : l1.here.op ≠ 0 := by intro e; simp [e] at hop
      have : linkTest false l1.here = true := by simp [linkTest, hf0, hne0]
      exact absurd this (by simp [hlink])
    refine SatX.bind (SatX.lift (Sat.of_eq (bm3.sh.wrS _) ?_))
    have bm4 := bm3.wS cb (S' := { S with
      length := l1.here.val.toUInt32
      extra := CODE_EXTRA l1.here }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine SatX.bind (liftEq (bm4.sh.rdS _) ?_)
    dsimp (config := { zeta := false }) only
    extract_lets byte jtail lbody jcheck jdist
    have hx28 : (CODE_EXTRA l1.here).toNat ≤ 28 := UInt32.le_iff_toNat_le.mp (code_extra_le hent)
    have hval : 1 ≤ l1.here.val.toNat := by
      obtain ⟨pre, -, -, hl3⟩ := hlenok rfl
      exact (hl3 h16).1
    have hd : ∀ lx Hx tx zx (Sx : InflateState), BM E lx Hx tx zx Sx → Sx.mode = LEN →
        Sx.codes = S.codes → Sx.lencode = S.lencode → Sx.lenbits = S.lenbits → Sx.distcode = S.distcode →
        Sx.distbits = S.distbits → Sx.length ≠ 0 → lx.bits.toNat < 8 →
        32 * (8 * (lx.have_.toNat + tx) + lx.bits.toNat) + 32 < m → SatX Hx lx (jdist ()) (Post E m) := by
      intro lx Hx tx zx Sx bmx hmx e1 e2 e3 e4 e5 hlx hbx hmx'
      have hck : ∀ ly Hy ty (Sy : InflateState), BM E ly Hy ty zx Sy → Sy.mode = LEN → Sy.codes = S.codes →
          Sy.lencode = S.lencode → Sy.lenbits = S.lenbits → Sy.distcode = S.distcode → Sy.distbits = S.distbits →
          Sy.length ≠ 0 → 1 ≤ Sy.offset.toNat → ly.bits.toNat < 8 →
          32 * (8 * (ly.have_.toNat + ty) + ly.bits.toNat) + 1 < m → SatX Hy ly (jcheck ()) (Post E m) := by
        intro ly Hy ty Sy bmy hmy f1 f2 f3 f4 f5 hly hoy hby hmy'
        simp only [jcheck]
        exact len_check cb bmy hmy (by rw [f1, f2, f3, f4, f5]; exact tabs) hby hly hoy hmy'
      simp only [jdist]
      rw [linkTest_dist]
      have tabd : RTab E.b Sx.codes Sx.distcode Sx.distbits 28 true := by rw [e1, e4, e5]; exact tabs.2
      refine SatX.bind (SatX.mono (bdecode cb bmx hbx tabd) ?_)
      rintro r l6 H6 p
      match r, p with
      | .error .leave, p => exact p
      | .ok (), ⟨t6, bm6, _, _, hm6, hent6, _, _, hcb6, hlive6, hb6⟩ =>
      refine SatX.bind (SatX.get ?_)
      have hc6 := hent6.cb_pos
      refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
      have hd6 : (l6.bits - (CODE_BITS l6.here).toUInt8).toNat = l6.bits.toNat - (CODE_BITS l6.here).toNat := by
        have h8 : (CODE_BITS l6.here).toUInt8.toNat = (CODE_BITS l6.here).toNat := by
          rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by have := hent6.cb_le; have := hent6.bits_le; omega)
        rw [UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by rw [h8]; exact hcb6)), h8]
      have bm7 := bm6.locals (l' := { l6 with
        hold := l6.hold >>> (CODE_BITS l6.here).toUInt64
        bits := l6.bits - (CODE_BITS l6.here).toUInt8 }) rfl rfl rfl rfl
      refine SatX.bind (SatX.get ?_)
      dsimp (config := { zeta := false }) only
      by_cases hd64 : (l6.here.op &&& 64 != 0) = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hd64)]
        obtain ⟨H', z', e, bm'⟩ := bm7.setBad cb "invalid distance code" (strIdx 19 (by decide) (by decide) (by decide))
        refine SatX.bind (SatX.lift (Sat.of_eq e (SatX.pure ?_)))
        refine ⟨t6, z', _, ⟨bm', Or.inl rfl, BModeOK.quiet _ { Sx with mode := BAD } (by show BAD ≠ LEN; decide)
          (by show BAD ≠ MATCH; decide)⟩, ?_⟩
        unfold μ; dsimp only; rw [rank_BAD, hd6]; omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hd64)]
      have h64' : l6.here.op &&& 64 = 0 := by simpa using hd64
      have hb7 : (l6.bits - (CODE_BITS l6.here).toUInt8).toNat < 8 := by
        rw [hd6]; have := hlive6 (Or.inl h64'); omega
      have hv1 : 1 ≤ l6.here.val.toNat := hent6.dval rfl (Or.inl h64')
      have hx6 : (CODE_EXTRA l6.here).toNat ≤ 28 := UInt32.le_iff_toNat_le.mp (code_extra_le hent6)
      refine SatX.bind (SatX.lift (Sat.of_eq (bm7.sh.wrS _) ?_))
      have bm8 := bm7.wS cb (S' := { Sx with offset := l6.here.val.toUInt32 }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine SatX.bind (SatX.lift (Sat.of_eq (bm8.sh.wrS _) ?_))
      have bm9 := bm8.wS cb (S' := { Sx with
        offset := l6.here.val.toUInt32
        extra := CODE_EXTRA l6.here }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine SatX.bind (liftEq (bm9.sh.rdS _) ?_)
      dsimp (config := { zeta := false }) only
      by_cases hx0 : (CODE_EXTRA l6.here != 0) = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hx0)]
        refine xbits_ok cb bm9 hb7 hx6 (fun s v => { s with offset := s.offset + v })
          (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (fun _ _ => rfl) (fun _ _ p => p) jcheck ?_
        intro l5 H5 t5 b bm5 hb5 h85 hm5
        have hb5' : b.toNat < 2 ^ (CODE_EXTRA l6.here).toNat := hb5
        refine hck _ _ _ _ bm5 hmx e1 e2 e3 e4 e5 hlx ?_ h85 (by
          have : 8 * (l5.have_.toNat + t5) + l5.bits.toNat ≤ 8 * (l6.have_.toNat + t6) + l6.bits.toNat := by
            have := hm5; simp only at this; rw [hd6] at this; omega
          omega)
        show 1 ≤ (l6.here.val.toUInt32 + b.toUInt32).toNat
        rw [UInt32.toNat_add, UInt16.toNat_toUInt32, UInt64.toNat_toUInt32]
        have : 2 ^ (CODE_EXTRA l6.here).toNat ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) hx6
        have := l6.here.val.toNat_lt
        rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)]
        refine hck _ _ _ _ bm9 hmx e1 e2 e3 e4 e5 hlx ?_ hb7 (by
          show 32 * (8 * (l6.have_.toNat + t6) + (l6.bits - (CODE_BITS l6.here).toUInt8).toNat) + 1 < m
          rw [hd6]; omega)
        show 1 ≤ l6.here.val.toUInt32.toNat
        rw [UInt16.toNat_toUInt32]; exact hv1
    have hlive2 : l2.bits.toNat < 8 := hlv (Or.inl (by simpa using h64))
    by_cases hx0 : (CODE_EXTRA l1.here != 0) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hx0)]
      refine xbits_ok cb bm4 hlive2 hx28 (fun s v => { s with length := s.length + v })
        (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (fun _ _ => rfl) (fun _ _ p => p) jdist ?_
      intro l5 H5 t5 b bm5 hb5 h85 hm5
      have hb5' : b.toNat < 2 ^ (CODE_EXTRA l1.here).toNat := hb5
      refine hd _ _ _ _ _ bm5 hm rfl rfl rfl rfl rfl ?_ h85 (by omega)
      intro e
      have h1 : (l1.here.val.toUInt32 + b.toUInt32).toNat = l1.here.val.toNat + b.toNat % 2 ^ 32 := by
        rw [UInt32.toNat_add, UInt16.toNat_toUInt32, UInt64.toNat_toUInt32]
        have : 2 ^ (CODE_EXTRA l1.here).toNat ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) hx28
        have := l1.here.val.toNat_lt
        exact Nat.mod_eq_of_lt (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have := congrArg UInt32.toNat e
      rw [h1] at this; simp at this; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)]
      refine hd _ _ _ _ _ bm4 hm rfl rfl rfl rfl rfl ?_ hlive2 (by omega)
      intro e
      have := congrArg UInt32.toNat e
      rw [UInt16.toNat_toUInt32] at this; simp at this; omega

end ZlibNgF.Proof.InfbackLoop
