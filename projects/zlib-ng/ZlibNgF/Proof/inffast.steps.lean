import ZlibNgF.Proof.«inffast.inv»

/-!
# `inflate_fast`: the label steps (`ZlibNgF`)

`stepTop`, `stepDolen`, `stepCommon` and the non-copy branches of `stepDodist` preserve the label-loop invariant
`PI` with a smaller rank.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastSteps
open C ZlibNg.Inffast ZlibNg.InflateP ZlibNg.Chunkset
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem
open ZlibNgF.Proof.ChunkCopy (B)
open ZlibNgF.Proof.InffastBase
open ZlibNgF.Proof.InffastInv

theorem sat_stepDolen {H0 G : Heap} {c : FC} {e : FE} {ot n : Nat} (EV : EnvOK H0 c e) {l : FL}
    (hP : PI H0 c e ot n (l, .dolen) G) :
    Sat G (stepDolen c l) (fun x G' => ∃ m, m < n ∧ PI H0 c e ot m x G') := by
  simp only [PI] at hP
  obtain ⟨w, hw, ho, hin, hS, r, hph⟩ := hP
  have hb : l.here.bits.toNat ≤ l.bits.toNat ∧ l.here.bits.toNat ≤ 20 := by
    rcases hph with ⟨_, hr, h20⟩ | ⟨_, ⟨pre, he, _⟩, hle⟩
    · have := LenEnt.bits_le (RootL.ent EV.ltab hr); omega
    · have := LenEnt.bits_le he; omega
  unfold stepDolen
  refine Sat.bind (Sat.mono (sat_oldDrop l hb.1 (by omega)) ?_)
  rintro l1 G1 ⟨rfl, hin1, hout1, hh1, hlen1, hbits1⟩
  split
  · rename_i hlit
    refine Sat.bind (Sat.mono (sat_putLit r l1 (by rw [OutOK, hout1]; exact ho) hw EV.sN) ?_)
    rintro l2 G2 ⟨rfl, r2⟩
    refine Sat.pure ⟨0, by rcases hph with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega, ?_⟩
    obtain ⟨_, ho0, hroom⟩ := ho
    exact ⟨ot + w + 1, rfl, by omega, by split at hroom <;> omega,
      hin.mono hin1 (by dsimp only; omega) (by omega), hS.mono hin1 (by dsimp only; omega), r2⟩
  · rename_i hlit
    have hop : l1.here.op ≠ 0 := by intro h0; exact hlit (by simp [h0])
    rcases hph with ⟨rfl, hr, h20⟩ | ⟨rfl, hs, _⟩
    · refine Sat.pure ⟨5, by omega, w, hw, ?_, hin.mono hin1 (by dsimp only; omega) (by omega),
        hS.mono hin1 (by dsimp only; omega), r, hop, Or.inl ⟨rfl, ?_, ?_⟩⟩
      · rw [OutOK, hout1]; exact ho
      · rw [hh1]; exact hr
      · dsimp only; rw [hh1]; omega
    · refine Sat.pure ⟨3, by omega, w, hw, ?_, hin.mono hin1 (by dsimp only; omega) (by omega),
        hS.mono hin1 (by dsimp only; omega), r, hop, Or.inr ⟨rfl, ?_⟩⟩
      · rw [OutOK, hout1]; exact ho
      · rw [hh1]; exact hs

/-- The state at the start of a trip: `out` with room for a trip, 8 readable input bytes after the advance of the
next `REFILL`. -/
def TS (H0 : Heap) (c : FC) (e : FE) (ot : Nat) (l : FL) (G : Heap) : Prop :=
  OutOK e c.safeMode ot l 0 ∧ RH H0 e G ∧ ∃ p, l.in_ = .ref e.rin p ∧ e.in0 ≤ p ∧
    p + 8 + (7 - l.bits.toNat / 8) ≤ e.E ∧ l.bits.toNat < 64 ∧ l.bits.toNat ≤ 8 * (p - e.in0) + e.bits0

/-- `REFILL` at the start of a trip. -/
theorem sat_refill_top {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) (l : FL)
    (p : Nat) (hin : l.in_ = .ref e.rin p) (h0 : e.in0 ≤ p) (hE : p + 8 + (7 - l.bits.toNat / 8) ≤ e.E)
    (hb : l.bits.toNat < 64) (hacc : l.bits.toNat ≤ 8 * (p - e.in0) + e.bits0) :
    Sat G (REFILL l) (fun l' G' => G' = G ∧ l'.out = l.out ∧ l'.here = l.here ∧ 56 ≤ l'.bits.toNat ∧
      InOK e l' 8) := by
  obtain ⟨A, hA, hAE⟩ := EV.inA
  obtain ⟨A', hA', hsz⟩ := in_get r hA
  refine Sat.mono (sat_REFILL hA' l hin (by omega) hb) ?_
  rintro l' G' ⟨rfl, hd, rfl⟩
  have e56 := or56 l.bits hb
  refine ⟨rfl, rfl, rfl, by dsimp only; omega, p + (7 - l.bits.toNat / 8), rfl, by omega, by omega,
    by dsimp only; omega, ?_⟩
  dsimp only
  rw [e56]
  omega

theorem sat_stepTop {H0 G : Heap} {c : FC} {e : FE} {ot : Nat} (EV : EnvOK H0 c e) {l : FL}
    (hT : TS H0 c e ot l G) :
    Sat G (stepTop c l) (fun x G' => ∃ n, n ≤ 6 ∧ PI H0 c e ot n x G') := by
  obtain ⟨ho, r, p, hin, h0, hE, hb, hacc⟩ := hT
  unfold stepTop
  refine Sat.bind (Sat.mono (sat_lookupLen EV r l) ?_)
  rintro l1 G1 ⟨rfl, hr1, hl1⟩
  have hb1 : l1.bits = l.bits := by rw [hl1]
  have hin1 : l1.in_ = l.in_ := by rw [hl1]
  have ho1 : l1.out = l.out := by rw [hl1]
  refine Sat.bind (Sat.mono (sat_refill_top EV r l1 p (hin1.trans hin) h0 (by rw [hb1]; exact hE)
    (by rw [hb1]; exact hb) (by rw [hb1]; exact hacc)) ?_)
  rintro l2 G2 ⟨rfl, ho2, hh2, hb2, hin2⟩
  have e1 := LenEnt.bits_le (RootL.ent EV.ltab hr1)
  refine Sat.bind (Sat.mono (sat_oldDrop l2 (by rw [hh2]; omega) (by rw [hh2]; omega)) ?_)
  rintro l3 G3 ⟨rfl, hin3, hout3, hh3, hlen3, hbits3⟩
  rw [hh2] at hbits3
  have hS3 : InS e l3 := by
    obtain ⟨q, hq1, -, -, -, hq5⟩ := hin2
    have := (RootL.ent EV.ltab hr1).2.2.2
    exact ⟨q, hin3.trans hq1, by omega⟩
  have hO : ∀ l' : FL, l'.out = l.out → OutOK e c.safeMode ot l' 0 := by
    intro l' h; rw [OutOK, h]; exact ho
  split
  · rename_i hlit1
    have hl15 : l1.here.bits.toNat ≤ 15 := by
      have := (RootL.ent EV.ltab hr1).1 (by rw [← hh2, ← hh3]; simpa using hlit1); omega
    refine Sat.bind (Sat.mono (sat_putLit r l3 (hO l3 (by rw [hout3, ho2, ho1])) (by omega) EV.sN) ?_)
    rintro l4 G4 ⟨rfl, r4⟩
    refine Sat.bind (Sat.mono (sat_lookupLen EV r4 _) ?_)
    rintro l5 G5 ⟨rfl, hr5, hl5⟩
    have e5 := LenEnt.bits_le (RootL.ent EV.ltab hr5)
    have hb5 : l5.bits.toNat = l3.bits.toNat := by rw [hl5]
    refine Sat.bind (Sat.mono (sat_oldDrop l5 (by omega) (by omega)) ?_)
    rintro l6 G6 ⟨rfl, hin6, hout6, hh6, hlen6, hbits6⟩
    have hin5 : l5.in_ = l3.in_ := by rw [hl5]
    have hout5 : l5.out = B e.ob (ot + 0 + 1) := by rw [hl5]
    split
    · rename_i hlit2
      have hl15' : l5.here.bits.toNat ≤ 15 := by
        have := (RootL.ent EV.ltab hr5).1 (by rw [← hh6]; simpa using hlit2); omega
      refine Sat.bind (Sat.mono (sat_putLit r4 l6 (w := 1) (by rw [OutOK, hout6, hout5]; exact ⟨rfl, ho.2⟩)
        (by omega) EV.sN) ?_)
      rintro l7 G7 ⟨rfl, r7⟩
      refine Sat.bind (Sat.mono (sat_lookupLen EV r7 _) ?_)
      rintro l8 G8 ⟨rfl, hr8, hl8⟩
      refine Sat.pure ⟨6, by omega, 2, by omega, ?_, ?_, ?_, r7, Or.inl ⟨rfl, hr8, ?_⟩⟩
      · rw [OutOK, hl8]; exact ⟨rfl, ho.2⟩
      · refine hin2.mono ?_ ?_ (Nat.le_refl _)
        · rw [hl8]; dsimp only; rw [hin6, hin5, hin3]
        · rw [hl8]; dsimp only; omega
      · refine hS3.mono ?_ ?_
        · rw [hl8]; dsimp only; rw [hin6, hin5]
        · rw [hl8]; dsimp only; omega
      · rw [hl8]; dsimp only; omega
    · rename_i hlit2
      have hop : l6.here.op ≠ 0 := by intro h0; exact hlit2 (by simp [h0])
      refine Sat.pure ⟨5, by omega, 1, by omega, ?_, ?_, ?_, r4, hop, Or.inl ⟨rfl, by rw [hh6]; exact hr5, ?_⟩⟩
      · rw [OutOK, hout6, hout5]; exact ⟨rfl, ho.2⟩
      · refine hin2.mono ?_ ?_ (Nat.le_refl _)
        · dsimp only; rw [hin6, hin5, hin3]
        · dsimp only; omega
      · refine hS3.mono ?_ ?_
        · dsimp only; rw [hin6, hin5]
        · dsimp only; omega
      · dsimp only; rw [hh6]; omega
  · rename_i hlit1
    have hop : l3.here.op ≠ 0 := by intro h0; exact hlit1 (by simp [h0])
    refine Sat.pure ⟨5, by omega, 0, by omega, hO l3 (by rw [hout3, ho2, ho1]), ?_, hS3, r, hop,
      Or.inl ⟨rfl, by rw [hh3, hh2]; exact hr1, ?_⟩⟩
    · refine hin2.mono ?_ ?_ (Nat.le_refl _)
      · dsimp only; rw [hin3]
      · dsimp only; omega
    · dsimp only; rw [hh3, hh2]; omega

/-! ## Breaks -/

theorem strLit_ok (s : String) (hs : s ∈ strTable) (h : Heap) : ∃ p, strLitRef s h = .ok (p, h) := by
  cases hx : strTable.findIdx? (· == s) with
  | none => exfalso; rw [Array.findIdx?_eq_none_iff] at hx; simpa using hx s hs
  | some j => exact ⟨.ref (.str j) 0, by simp [strLitRef, hx]⟩

theorem sat_ldState_e {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) :
    Sat G (ldState c.st) (fun s G' => s = e.st ∧ G' = G) := by
  rw [EV.stp]
  exact ⟨e.st, G, by simp [ldState, istate_get r EV.bob, EV.hst], rfl, rfl⟩

theorem sat_stState_e {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) (s' : InflateState) :
    Sat G (stState c.st s') (fun _ G' => G' = { G with istates := upd G.istates e.b (some s') }) := by
  rw [EV.stp]
  exact ⟨(), _, by simp [stState, istate_get r EV.bob, EV.hst], rfl⟩

theorem brk_state {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) (s' : InflateState)
    (hs : s' = { e.st with mode := BAD } ∨ s' = { e.st with mode := TYPE } ∨
      ∃ len dist : UInt32, c.safeMode = true ∧ 1 ≤ dist.toNat ∧ s' = { e.st with mode := MATCH, length := len, was := len, offset := dist }) :
    BrkHeap H0 c.safeMode e { G with istates := upd G.istates e.b (some s') } := by
  refine ⟨G, s', e.z, r, ?_, hs, Or.inl rfl⟩
  have : upd G.streams e.i (some e.z) = G.streams := by
    rw [streams_get r]; exact ZlibNgF.Proof.ChunkMem.upd_self _ _ _ EV.hz
  rw [this]

/-- `SET_BAD(msg)` on the running heap. -/
theorem sat_SET_BAD {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) (msg : String)
    (hm : msg ∈ strTable) : Sat G (SET_BAD c msg) (fun _ G' => BrkHeap H0 c.safeMode e G') := by
  unfold SET_BAD
  refine Sat.bind (Sat.mono (sat_ldState_e EV r) ?_)
  rintro s G1 ⟨rfl, hG⟩
  rw [hG]
  refine Sat.bind (Sat.mono (sat_stState_e EV r _) ?_)
  rintro _ G1 hG1
  rw [hG1]
  generalize hK : ({ G with istates := upd G.istates e.b (some { e.st with mode := BAD }) } : Heap) = K
  have hz : K.streams e.i = some e.z := by
    rw [← hK]; show G.streams e.i = some e.z; rw [streams_get r]; exact EV.hz
  obtain ⟨p, hp⟩ := strLit_ok msg hm K
  refine Sat.bind ⟨p, _, hp, ?_⟩
  dsimp only
  rw [EV.strm]
  refine Sat.bind ⟨e.z, K, by simp only [ldStream, hz], ?_⟩
  refine ⟨(), { K with streams := upd K.streams e.i (some { e.z with msg := p }) },
    by simp only [stStream, hz], ?_⟩
  rw [← hK]
  exact ⟨G, _, _, r, rfl, Or.inl rfl, Or.inr ⟨p, rfl⟩⟩

/-! ## `common`: after `op = here.op;` -/

theorem op15 (x : UInt8) : (x.toUInt32 &&& MAX_BITS).toNat = x.toNat % 16 := by
  rw [UInt32.toNat_and]
  simp only [MAX_BITS, UInt8.toNat_toUInt32, UInt32.reduceToNat]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

theorem add_val (v : UInt16) (x : UInt64) (hx : x.toNat < 2 ^ 28) :
    (v.toUInt32 + x.toUInt32).toNat = v.toNat + x.toNat := by
  have := v.toNat_lt
  rw [UInt32.toNat_add, UInt64.toNat_toUInt32, UInt16.toNat_toUInt32, Nat.mod_eq_of_lt (a := x.toNat) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem add_val64 (v : UInt16) (x : UInt64) (hx : x.toNat < 2 ^ 32) :
    (v.toUInt64 + x).toNat = v.toNat + x.toNat := by
  have := v.toNat_lt
  rw [UInt64.toNat_add, UInt16.toNat_toUInt64]
  exact Nat.mod_eq_of_lt (by omega)

theorem sat_lookupDist {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) (x : UInt64) :
    Sat G (Ptr.index c.dcode (Int.ofNat (x &&& c.dmask.toUInt64).toNat) : M Code)
      (fun h G' => G' = G ∧ RootD e h) := by
  have hg : Space.get G e.rd = some e.Td := (code_get r EV.dnot).trans EV.dget
  have hk := EV.dmask x
  rw [EV.dcode]
  exact Sat.mono (sat_index_code hg _ (by have := EV.dtab.1; omega)) fun h G' ⟨h1, h2⟩ => ⟨h2, _, hk, h1⟩

theorem sat_stepCommon {H0 G : Heap} {c : FC} {e : FE} {ot n : Nat} (EV : EnvOK H0 c e) {l : FL}
    (hP : PI H0 c e ot n (l, .common) G) :
    Sat G (stepCommon c l) (fun x G' => ∃ m, m < n ∧ PI H0 c e ot m x G') := by
  simp only [PI] at hP
  obtain ⟨w, hw, ho, hin, hS, r, hop, hph⟩ := hP
  have hent : ∃ pre, LenEnt pre l.here ∧ (n = 5 ∨ n = 3) := by
    rcases hph with ⟨rfl, hr, _⟩ | ⟨rfl, pre, he, _⟩
    · exact ⟨0, RootL.ent EV.ltab hr, Or.inl rfl⟩
    · exact ⟨pre, he, Or.inr rfl⟩
  obtain ⟨pre, he, hn⟩ := hent
  have h20 := LenEnt.bits_le he
  unfold stepCommon
  dsimp only
  split
  · -- length base
    rename_i hbase
    have hB : Base l.here := by simpa [Base] using hbase
    obtain ⟨hv1, hv2⟩ := he.2.2.1 hB
    refine Sat.bind (Sat.mono (sat_EXTRA_BITS (H := G) l.old l.here _ (by omega)) ?_)
    rintro x G1 ⟨hG1, hx⟩
    rw [hG1]
    rw [op15] at hx
    have hx28 : x.toNat < 2 ^ 28 := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
    have hlen := add_val l.here.val x hx28
    have hpow : x.toNat + 1 ≤ 2 ^ (l.here.bits.toNat - l.here.op.toNat % 16) := hx
    refine Sat.bind (Sat.mono (sat_lookupDist EV r _) ?_)
    rintro d G1 ⟨hG1, hd⟩
    rw [hG1]
    obtain ⟨p, hp, hp0, hpE, hb64, hacc⟩ := hin
    obtain ⟨q, hq, hqs⟩ := hS
    have hqp : q = p := by rw [hp] at hq; cases hq; rfl
    subst hqp
    have fin : ∀ l' G', (G' = G ∧ l'.out = l.out ∧ l'.here = d ∧
        l'.len = l.here.val.toUInt32 + x.toUInt32 ∧ 28 ≤ l'.bits.toNat ∧ InOK e l' 0 ∧ InS e l') →
        Sat G' (pure (l', Lbl.dodist)) (fun x G' => ∃ m, m < n ∧ PI H0 c e ot m x G') := by
      rintro l' G' ⟨rfl, hout', hh', hlen', hb', hin', hS'⟩
      refine Sat.pure ⟨2, by omega, w, hw, ?_, hin', hS', r, ?_, ?_, Or.inl ⟨rfl, ?_, ?_⟩⟩
      · rw [OutOK, hout']; exact ho
      · dsimp only; rw [hlen', hlen]; omega
      · dsimp only; rw [hlen', hlen]; omega
      · dsimp only; rw [hh']; exact hd
      · dsimp only; omega
    split
    · rename_i hlt
      obtain ⟨A, hA, hAE⟩ := EV.inA
      obtain ⟨A', hA', hsz⟩ := in_get r hA
      refine Sat.bind (Sat.mono (sat_REFILL hA' _ hp (by omega) hb64) ?_)
      rintro l' G' ⟨hG', hd', rfl⟩
      have e56 := or56 l.bits hb64
      refine fin _ _ ⟨hG', rfl, rfl, rfl, by dsimp only; omega, ⟨q + (7 - l.bits.toNat / 8), rfl, by omega, by omega,
        by dsimp only; omega, ?_⟩, q + (7 - l.bits.toNat / 8), rfl, ?_⟩
      · dsimp only; rw [e56]; omega
      · dsimp only; rw [e56]; omega
    · rename_i hlt
      have : 38 ≤ l.bits.toNat := by
        simp only [MAX_BITS] at hlt
        rw [UInt32.lt_iff_toNat_lt] at hlt; simpa using hlt
      first
        | (apply fin; exact ⟨rfl, rfl, rfl, rfl, by dsimp only; omega, ⟨q, hp, hp0, by omega, hb64, hacc⟩, q, hp, hqs⟩)
        | (refine Sat.bind (Sat.pure ?_); apply fin
           exact ⟨rfl, rfl, rfl, rfl, by dsimp only; omega, ⟨q, hp, hp0, by omega, hb64, hacc⟩, q, hp, hqs⟩)
  · rename_i hbase
    split
    · -- second-level length code
      rename_i h64
      have hlink : LenLink l.here := ⟨hop, by simpa using hbase, by simpa using h64⟩
      rcases hph with ⟨rfl, hr, h20'⟩ | ⟨rfl, _, _, hnl⟩
      · obtain ⟨k, hk, hk'⟩ := hr
        obtain ⟨_, hlk⟩ := EV.ltab.2 k hk
        rw [← hk'] at hlk
        obtain ⟨hop16, hsz, hsub⟩ := hlk hlink
        refine Sat.bind (Sat.mono (sat_BITS (H := G) _ l.here.op.toUInt32 (by simp; omega)) ?_)
        rintro bv G1 ⟨hG1, hbv⟩
        rw [hG1]
        simp only [UInt8.toNat_toUInt32] at hbv
        have hg : Space.get G e.rl = some e.Tl := (code_get r EV.lnot).trans EV.lget
        rw [EV.lcode]
        have hidx := add_val64 l.here.val bv (by
          have : 2 ^ l.here.op.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
          omega)
        refine Sat.bind (Sat.mono (sat_index_code hg _ (by rw [hidx]; omega)) ?_)
        rintro d G1 ⟨rfl, hG1⟩
        rw [hG1]
        obtain ⟨hsd, hnl⟩ := hsub bv.toNat hbv
        have hd20 := LenEnt.bits_le hsd
        refine Sat.pure ⟨4, by omega, w, hw, ?_, hin, hS, r, Or.inr ⟨rfl, ⟨l.here.bits.toNat, ?_, ?_⟩, ?_⟩⟩
        · exact ho
        · dsimp only; rw [hidx, ← Nat.add_assoc]; exact hsd
        · dsimp only; rw [hidx, ← Nat.add_assoc]; exact hnl
        · dsimp only; rw [hidx, ← Nat.add_assoc]; omega
      · exact absurd hlink hnl
    · rename_i h64
      split
      · -- end of block
        refine Sat.bind (Sat.mono (sat_ldState_e EV r) ?_)
        rintro s G1 ⟨rfl, hG⟩
        rw [hG]
        refine Sat.bind (Sat.mono (sat_stState_e EV r _) ?_)
        rintro _ G1 rfl
        obtain ⟨_, ho0, hroom⟩ := id ho
        refine Sat.pure ⟨0, by omega, ot + w, ho.1, by omega, by split at hroom <;> omega,
          hin.mono rfl (Nat.le_refl _) (by omega), hS.mono rfl (Nat.le_refl _), brk_state EV r _ (Or.inr (Or.inl rfl))⟩
      · refine Sat.bind (Sat.mono (sat_SET_BAD EV r _ (by simp [strTable])) ?_)
        rintro _ G1 hb
        obtain ⟨_, ho0, hroom⟩ := id ho
        refine Sat.pure ⟨0, by omega, ot + w, ho.1, by omega, by split at hroom <;> omega,
          hin.mono rfl (Nat.le_refl _) (by omega), hS.mono rfl (Nat.le_refl _), hb⟩

end ZlibNgF.Proof.InffastSteps
