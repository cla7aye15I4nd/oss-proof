import ZlibNgF.Proof.«infback.c.len»
import ZlibNgF.Proof.«inflate.c.codelens-mode»
import ZlibNgF.Proof.«inftrees.c.facts»

/-!
# `inflateBack()`: the mode `TABLE` (`ZlibNgF`)

`TABLE` reads the counts of a dynamic block (`NEEDBITS(14)`), the code lengths of the code length code (`NEEDBITS(3)`
each, in the order `order`, the rest set to 0), builds that code's table with `zng_inflate_table` (`table_run_rep`),
decodes the literal/length and distance code lengths with it (with the repeat codes 16, 17, 18), checks for an
end-of-block code, builds the two tables and falls through to `LEN`.

Every step keeps the shape of the state (`BM`); the input measure `8 * (have + t) + bits` never grows, so every exit
to `BAD` lowers `μ` (rank 5 to 0), and so does the fall-through to `LEN` (rank 1). The code length code is a prefix
code whose entries have their code bits in `bits` (`table_run_rep`), so each code length symbol leaves fewer than 8
bits held, and `LEN` is entered with fewer than 8 bits and two prefix-code tables (`RTab`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateLoop (withS istates_of istate_withS wrS_app withS_withS getWords_withS storeLens_withS
  addLens_withS order_lt order_inj order_surj aget_order strIdx bits_ok dropbits_ok bits_lt32 tab_index index_lens)
open ZlibNgF.Proof.InflateTab (CodeTable EntryOK linkTest)

theorem rank_TABLE : rank TABLE = 5 := by decide

/-! ## The state block -/

theorem withS_self {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) : withS H b S = H := by
  unfold withS
  rw [ZlibNgF.Proof.ChunkMem.upd_self _ _ _ (istates_of hs)]

theorem BShape.addLens {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) {k : Nat}
    (hk : k ≤ 320) : Ptr.add (.ref (.lens E.b) 0 : WPtr) (Int.ofNat k) H = .ok (.ref (.lens E.b) k, H) := by
  have e := addLens_withS sh.istate S (k := k) (by rw [sh.lens]; exact hk)
  rwa [withS_self sh.istate] at e

theorem BShape.storeLens {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) {k : Nat}
    (hk : k < 320) (v : UInt16) :
    Ptr.store (.ref (.lens E.b) k : WPtr) v H = .ok ((), withS H E.b { S with lens := S.lens.set! k v }) := by
  have e := storeLens_withS sh.istate S (k := k) (by rw [sh.lens]; exact hk) v
  rw [withS_self sh.istate] at e
  exact e

theorem BShape.indexLens {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) {k : Nat}
    (hk : k < 320) : Ptr.index (.ref (.lens E.b) 0 : WPtr) (Int.ofNat k) H = .ok (S.lens[k]!, H) :=
  index_lens sh.istate sh.lens hk

/-- A store into the state that keeps the shape fields. -/
theorem SKeep.lensSet (S : InflateState) (k : Nat) (v : UInt16) : SKeep S { S with lens := S.lens.set! k v } :=
  ⟨rfl, rfl, rfl, rfl, rfl, by simp, rfl, rfl⟩

/-- `BM` after a store of `S'` into the state. -/
theorem BM.wS' {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S S' : InflateState}
    (bm : BM E l H t z S) (k : SKeep S S') (f : InflateState → InflateState) (hf : f S = S') :
    ZlibNg.Inflate.wrS (some E.b) f H = .ok ((), withS H E.b S') ∧ BM E l (withS H E.b S') t z S' := by
  refine ⟨by rw [bm.sh.wrS, hf], bm.wS cb k⟩

/-! ## Exits -/

/-- The input measure. -/
def IM (l : IL) (t : Nat) : Nat := 8 * (l.have_.toNat + t) + l.bits.toNat

/-- `SET_BAD(msg); return;` from a state whose input measure is at most `M0`, with `32 * M0 + 5 ≤ m`. -/
theorem bad_exit {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) {M0 m : Nat} (hM : IM l t ≤ M0) (hm : 32 * M0 + 5 ≤ m) (msg : String) {k : Nat}
    (hk : strTable.findIdx? (· == msg) = some k) :
    SatX H l (do (MonadLiftT.monadLift (SET_BAD E.c.ctx msg) : X Unit); pure ()) (Post E m) := by
  obtain ⟨H', z', e, bm'⟩ := bm.setBad cb msg hk
  refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
  refine SatX.pure ⟨t, z', _, ⟨bm', Or.inl rfl, BModeOK.quiet _ { S with mode := BAD }
    (by show BAD ≠ LEN; decide) (by show BAD ≠ MATCH; decide)⟩, ?_⟩
  unfold μ IM at *; dsimp only; rw [rank_BAD]; omega

/-- `BM` after a `NEEDBITS` that read whole bytes. -/
theorem BM.pulled {E : BEnv} {l l1 : IL} {H H1 : Heap} {t t1 : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) (hk : BackKeep H H1 E.i E.b E.w) (hin : InB E.I H1 l1 t1)
    (hm : IM l1 t1 = IM l t) (hb : l.bits.toNat < l1.bits.toNat + 8) (hp : Pb l l1) : BM E l1 H1 t1 z S := by
  refine ⟨bm.sh.keep hk, hin, ?_, by rw [hp]; exact bm.put, by rw [hp]; exact bm.left, bm.whave⟩
  have := bm.tot
  unfold IM at hm
  omega

theorem u8_sub' {a : UInt8} {k : Nat} (h : k ≤ a.toNat) (hk : k < 256) :
    (a - (UInt32.ofNat k).toUInt8).toNat = a.toNat - k := by
  have hk' : ((UInt32.ofNat k).toUInt8).toNat = k := by simp; omega
  rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hk']; exact h), hk']

/-! ## The code lengths of the code length code -/

/-- The counter `have` and the length counts of the state on the heap (`0` without a state). -/
def hvRank (E : BEnv) (f : InflateState → Nat) (H : Heap) : Nat := match H.istate E.b with | some S => f S | none => 0

theorem hvRank_of {E : BEnv} {f : InflateState → Nat} {H : Heap} {z : ZStream} {S : InflateState}
    (sh : BShape E H z S) : hvRank E f H = f S := by
  unfold hvRank; rw [sh.istate]

/-- The state of the loop over the code length code lengths. -/
def CLC (E : BEnv) (z : ZStream) (S0 : InflateState) (M0 : Nat) (l : IL) (H : Heap) : Prop :=
  ∃ t S, BM E l H t z S ∧ IM l t ≤ M0 ∧ l.bits.toNat < 8 ∧ S = { S0 with «have» := S.«have», lens := S.lens } ∧
    S.«have».toNat ≤ S0.ncode.toNat ∧ ∀ j, j < S.«have».toNat → S.lens[(order[j]!).toNat]! ≤ 7

theorem bits3 (x : UInt64) : (x &&& ((1 : UInt32) <<< (3 : UInt32) - 1).toUInt64).toUInt16 ≤ 7 :=
  ZlibNgF.Proof.InflateLoop.bits3_le x

/-- `while (state->have < state->ncode) { NEEDBITS(3); state->lens[order[state->have++]] = BITS(3); DROPBITS(3); }` -/
theorem clc_loop {E : BEnv} (cb : E.CB) {z : ZStream} {S0 : InflateState} {M0 : Nat} (hnc : S0.ncode.toNat ≤ 19)
    {l : IL} {H : Heap} (P : CLC E z S0 M0 l H) :
    SatX H l (xwhile (do let s ← C.ldState E.c.st; return s.«have» < s.ncode) (do
      ZlibNg.Infback.NEEDBITS E.c 3
      let hv ← rdS E.c.st (·.«have»)
      wrS E.c.st fun s => { s with «have» := s.«have» + 1 }
      let o ← ZlibNg.Inftrees.aget order hv.toNat
      let b ← BITS 3
      Ptr.store (← (Ptr.ref (WRef.lens E.b) 0 : WPtr).add (Int.ofNat o.toNat)) b.toUInt16
      DROPBITS 3))
    (fun r l' H' => match r with
      | .ok () => ∃ t S, BM E l' H' t z S ∧ IM l' t ≤ M0 ∧ l'.bits.toNat < 8 ∧
          S = { S0 with «have» := S.«have», lens := S.lens } ∧ S.«have» = S0.ncode ∧
          ∀ j, j < S.«have».toNat → S.lens[(order[j]!).toNat]! ≤ 7
      | .error .leave => BLv E l' H'
      | .error (.ret _) => False) := by
  unfold xwhile
  refine xwhileBrk_rank (CLC E z S0 M0) (fun _ H => hvRank E (fun S => S0.ncode.toNat - S.«have».toNat) H) _ ?_ P
    (by obtain ⟨t, S, bm, -⟩ := P; rw [hvRank_of bm.sh]; unfold fuel; omega)
  rintro l1 H1 ⟨t1, S1, bm1, hM1, hb1, hS1, hhv1, hlv1⟩
  refine SatX.bind (liftEq bm1.sh.ldState ?_)
  refine SatX.pure ?_
  dsimp only
  by_cases hlt : S1.«have» < S1.ncode
  · simp only [hlt, decide_true]
    have hnc1 : S1.ncode = S0.ncode := by rw [hS1]
    have hlt' : S1.«have».toNat < S0.ncode.toNat := by rw [← hnc1]; exact UInt32.lt_iff_toNat_lt.mp hlt
    refine SatX.bind (SatX.bind (needbits_ok cb E.c rfl rfl bm1.inB 3 (by decide) ?_ ?_))
    · intro l' H' t' q hk hI hp h0 _ _
      exact leave_of_pull bm1 hk hI hp h0
    intro l2 H2 t2 hk hin2 hmeas h3 hb2 hp2 _
    have h3' : 3 ≤ l2.bits.toNat := h3
    have hb2' : l2.bits.toNat ≤ 10 := by
      have : max l1.bits.toNat ((3 : UInt32).toNat + 7) ≤ 10 := Nat.max_le.mpr ⟨by omega, by decide⟩
      omega
    have bm2 : BM E l2 H2 t2 z S1 := bm1.pulled hk hin2 hmeas (by omega) hp2
    refine SatX.bind (liftEq (bm2.sh.rdS _) ?_)
    obtain ⟨e3, bm3⟩ := bm2.wS' cb (S' := { S1 with «have» := S1.«have» + 1 }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun s => { s with «have» := s.«have» + 1 }) rfl
    refine SatX.bind (SatX.lift (Sat.of_eq e3 ?_))
    refine SatX.bind (liftEq (aget_order (i := S1.«have».toNat) (by omega)) ?_)
    refine SatX.bind (bits_ok 3 (by decide) ?_)
    have ho := order_lt S1.«have».toNat (by omega)
    refine SatX.bind (liftEq (bm3.sh.addLens (k := (order[S1.«have».toNat]!).toNat) (by omega)) ?_)
    refine SatX.bind (SatX.lift (Sat.of_eq (bm3.sh.storeLens (k := (order[S1.«have».toNat]!).toNat) (by omega) _) ?_))
    have bm4 := bm3.wS cb (SKeep.lensSet _ (order[S1.«have».toNat]!).toNat
      (l2.hold &&& ((1 : UInt32) <<< (3 : UInt32) - 1).toUInt64).toUInt16)
    refine dropbits_ok 3 (by decide) (SatX.pure ?_)
    have hd : (l2.bits - (3 : UInt32).toUInt8).toNat = l2.bits.toNat - 3 := u8_sub' (k := 3) (by omega) (by decide)
    have hh1 : (S1.«have» + 1).toNat = S1.«have».toNat + 1 := by
      rw [UInt32.toNat_add]; show (S1.«have».toNat + 1) % 2 ^ 32 = _; omega
    refine ⟨⟨t2, _, bm4.locals rfl rfl rfl rfl, ?_, by show (l2.bits - (3 : UInt32).toUInt8).toNat < 8; omega, ?_, ?_, ?_⟩,
      ?_⟩
    · unfold IM at hM1 ⊢; show 8 * (l2.have_.toNat + t2) + (l2.bits - (3 : UInt32).toUInt8).toNat ≤ M0; omega
    · rw [hS1]
    · show (S1.«have» + 1).toNat ≤ _; omega
    · intro j hj
      show (S1.lens.set! _ _)[(order[j]!).toNat]! ≤ 7
      change j < (S1.«have» + 1).toNat at hj
      by_cases ej : j = S1.«have».toNat
      · subst ej
        rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simp; rw [bm1.sh.lens]; omega)]
        simp only [Array.getElem_setIfInBounds_self]
        exact bits3 _
      · have hne : (order[S1.«have».toNat]!).toNat ≠ (order[j]!).toNat := fun e =>
          ej (order_inj j (by omega) _ (by omega) (UInt16.toNat_inj.mp e.symm))
        rw [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds_ne hne, ← getElem!_def]
        exact hlv1 j (by omega)
    · rw [hvRank_of bm4.sh, hvRank_of bm1.sh]
      show S0.ncode.toNat - (S1.«have» + 1).toNat < S0.ncode.toNat - S1.«have».toNat
      omega
  · simp only [hlt, decide_false]
    have hnc1 : S1.ncode = S0.ncode := by rw [hS1]
    refine ⟨t1, S1, bm1, hM1, hb1, hS1, ?_, hlv1⟩
    apply UInt32.toNat_inj.mp
    have := Nat.le_of_not_lt (fun h => hlt (UInt32.lt_iff_toNat_lt.mpr h))
    rw [hnc1] at this
    omega

/-- The state of the loop that sets the remaining code length code lengths to 0. -/
def CLZ (E : BEnv) (z : ZStream) (S0 : InflateState) (t : Nat) (l : IL) (H : Heap) : Prop :=
  ∃ S, BM E l H t z S ∧ S = { S0 with «have» := S.«have», lens := S.lens } ∧
    S.«have».toNat ≤ 19 ∧ ∀ j, j < S.«have».toNat → S.lens[(order[j]!).toNat]! ≤ 7

/-- `while (state->have < 19) state->lens[order[state->have++]] = 0;` -/
theorem clz_loop {E : BEnv} (cb : E.CB) {z : ZStream} {S0 : InflateState} {t : Nat} {l : IL} {H : Heap}
    (P : CLZ E z S0 t l H) :
    SatX H l (xwhile (do return (← rdS E.c.st (·.«have»)) < 19) (do
      let hv ← rdS E.c.st (·.«have»)
      wrS E.c.st fun s => { s with «have» := s.«have» + 1 }
      let o ← ZlibNg.Inftrees.aget order hv.toNat
      Ptr.store (← (Ptr.ref (WRef.lens E.b) 0 : WPtr).add (Int.ofNat o.toNat)) (0 : UInt16)))
    (fun r l' H' => match r with
      | .ok () => l' = l ∧ ∃ S, BM E l H' t z S ∧ S = { S0 with «have» := S.«have», lens := S.lens } ∧
          ∀ k, k < 19 → S.lens[k]! ≤ 7
      | .error _ => False) := by
  unfold xwhile
  refine xwhileBrk_rank (fun l' H' => l' = l ∧ CLZ E z S0 t l H') (fun _ H => hvRank E (fun S => 19 - S.«have».toNat) H)
    _ ?_ ⟨rfl, P⟩ (by obtain ⟨S, bm, -⟩ := P; rw [hvRank_of bm.sh]; unfold fuel; omega)
  rintro l1 H1 ⟨rfl, S1, bm1, hS1, hhv1, hlv1⟩
  refine SatX.bind (liftEq (bm1.sh.rdS _) ?_)
  refine SatX.pure ?_
  dsimp only
  by_cases hlt : S1.«have» < 19
  · simp only [hlt, decide_true]
    have hlt' : S1.«have».toNat < 19 := UInt32.lt_iff_toNat_lt.mp hlt
    refine SatX.bind ?_
    refine SatX.bind (liftEq (bm1.sh.rdS _) ?_)
    obtain ⟨e3, bm3⟩ := bm1.wS' cb (S' := { S1 with «have» := S1.«have» + 1 }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun s => { s with «have» := s.«have» + 1 }) rfl
    refine SatX.bind (SatX.lift (Sat.of_eq e3 ?_))
    refine SatX.bind (liftEq (aget_order (i := S1.«have».toNat) (by omega)) ?_)
    have ho := order_lt S1.«have».toNat (by omega)
    refine SatX.bind (liftEq (bm3.sh.addLens (k := (order[S1.«have».toNat]!).toNat) (by omega)) ?_)
    refine SatX.lift (Sat.of_eq (bm3.sh.storeLens (k := (order[S1.«have».toNat]!).toNat) (by omega) _) ?_)
    have bm4 := bm3.wS cb (SKeep.lensSet _ (order[S1.«have».toNat]!).toNat 0)
    have hh1 : (S1.«have» + 1).toNat = S1.«have».toNat + 1 := by
      rw [UInt32.toNat_add]; show (S1.«have».toNat + 1) % 2 ^ 32 = _; omega
    refine SatX.pure ⟨⟨rfl, _, bm4, by rw [hS1], by show (S1.«have» + 1).toNat ≤ 19; omega, ?_⟩, ?_⟩
    · intro j hj
      show (S1.lens.set! _ _)[(order[j]!).toNat]! ≤ 7
      change j < (S1.«have» + 1).toNat at hj
      by_cases ej : j = S1.«have».toNat
      · subst ej
        rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simp; rw [bm1.sh.lens]; omega)]
        simp only [Array.getElem_setIfInBounds_self]
        decide
      · have hne : (order[S1.«have».toNat]!).toNat ≠ (order[j]!).toNat := fun e =>
          ej (order_inj j (by omega) _ (by omega) (UInt16.toNat_inj.mp e.symm))
        rw [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds_ne hne, ← getElem!_def]
        exact hlv1 j (by omega)
    · rw [hvRank_of bm4.sh, hvRank_of bm1.sh]
      show 19 - (S1.«have» + 1).toNat < 19 - S1.«have».toNat
      omega
  · simp only [hlt, decide_false]
    have h19 : S1.«have».toNat = 19 := by
      have := Nat.le_of_not_lt (fun h => hlt (UInt32.lt_iff_toNat_lt.mpr h))
      have h19 : (19 : UInt32).toNat = 19 := rfl
      omega
    refine ⟨trivial, S1, bm1, hS1, fun k hk => ?_⟩
    obtain ⟨j, hj, hjk⟩ := order_surj k hk
    rw [← hjk]
    exact hlv1 j (by omega)

/-! ## The code length code lookup -/

theorem codes_get {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) :
    Space.get H (CodeRef.codes E.b) = some S.codes := by
  show (H.istate E.b).map (·.codes) = _
  rw [sh.istate]; rfl

/-- The prefix property of the code length code in terms of `bits`. -/
theorem repB {a : Array Code} {n : Nat} (hl : LvlAll a 0 n) (h16 : ∀ j, j < 2 ^ n → a[0 + j]!.op.toNat &&& 16 = 0) :
    RepF (fun y => a[0 + y]!.bits.toNat) (fun _ => True) n := by
  intro x x' hx hx' _
  obtain ⟨h1, h2⟩ := hl x x' hx hx'
  rw [Inftrees.codeBits_of (h16 x' hx')] at h1 h2
  refine ⟨h1, fun e => ?_⟩
  have := congrArg UInt32.toNat (h2 e)
  rwa [Inftrees.codeBits_of (h16 x hx), Inftrees.codeBits_of (h16 x' hx')] at this

/-- The lookup loop of the code length code: `here = lencode[BITS(lenbits)]` until `here.bits` bits are held. -/
theorem bdecC {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) {e : Nat} (hp : S.lencode = .val (.ref (.codes E.b) 0))
    (ct : CodeTable S.codes 0 e S.lenbits.toNat 25 false) (hla : LvlAll S.codes 0 S.lenbits.toNat)
    (h16 : ∀ j, j < 2 ^ S.lenbits.toNat → S.codes[0 + j]!.op.toNat &&& 16 = 0) (hb8 : l.bits.toNat < 8) :
    SatX H l (xloopBrk (do
      let lc ← (← rdS E.c.st (·.lencode)).get
      let b ← BITS (← rdS E.c.st (·.lenbits))
      let here : Code ← Ptr.index lc (Int.ofNat b.toNat)
      modify fun l => { l with here := here }
      if (← get).here.bits <= (← get).bits then return true
      PULLBYTE E.c
      return false))
      (fun res l' H' => match res with
        | .ok () => DL E z S l t l' H' ∧ (∃ j, j < 2 ^ S.lenbits.toNat ∧ l'.here = S.codes[0 + j]!) ∧
            l'.here.bits.toNat ≤ l'.bits.toNat ∧ l'.bits.toNat < l'.here.bits.toNat + 8 ∧ l'.bits.toNat ≤ 32
        | .error .leave => BLv E l' H'
        | .error (.ret _) => False) := by
  have hn15 : S.lenbits.toNat ≤ 15 := ct.n_le
  have hrep := repB hla h16
  unfold xloopBrk
  refine xwhileBrk_rank (fun l' H' => DL E z S l t l' H' ∧
      J (fun y => (S.codes[0 + y]!).bits.toNat) S.lenbits.toNat l'.bits.toNat l'.hold.toNat ∧ l'.bits.toNat ≤ 32)
    (fun l' _ => 64 - l'.bits.toNat) _ ?_ ⟨DL.refl bm, Or.inl hb8, by omega⟩ (by unfold fuel; omega)
  rintro l1 H1 ⟨⟨t1, bm1, hp1, hl1, hla1, hm1⟩, hj1, hb1⟩
  refine SatX.pure ?_
  dsimp only
  refine SatX.bind (liftEq (bm1.sh.rdS _) ?_)
  rw [hp]
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  refine SatX.bind (liftEq (bm1.sh.rdS _) ?_)
  refine SatX.bind (bits_ok _ (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega) ?_)
  have hk := ZlibNgF.Proof.InflateLoop.bits_lt l1.hold S.lenbits hn15
  refine SatX.bind (liftEq (tab_index (codes_get bm1.sh) ct hk) ?_)
  have hkv : (l1.hold &&& ((1 : UInt32) <<< S.lenbits - 1).toUInt64).toNat =
      l1.hold.toNat % 2 ^ S.lenbits.toNat := by
    have h1 : ((1 : UInt32) <<< S.lenbits).toNat = 2 ^ S.lenbits.toNat := by
      rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : S.lenbits.toNat < 32)]
      show 1 <<< S.lenbits.toNat % 2 ^ 32 = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    have h2 : ((1 : UInt32) <<< S.lenbits - 1).toUInt64.toNat = 2 ^ S.lenbits.toNat - 1 := by
      rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, h1]; exact Nat.one_le_two_pow), h1]
      rfl
    rw [UInt64.toNat_and, h2, Nat.and_two_pow_sub_one_eq_mod]
  generalize (l1.hold &&& ((1 : UInt32) <<< S.lenbits - 1).toUInt64).toNat = k at hk hkv ⊢
  subst hkv
  refine SatX.bind (SatX.modify ?_)
  have hj2 : 0 + l1.hold.toNat % 2 ^ S.lenbits.toNat < e := by have := ct.root; omega
  have hent := ct.ent _ (Nat.zero_le _) hj2
  have bm2 : BM E { l1 with here := S.codes[0 + l1.hold.toNat % 2 ^ S.lenbits.toNat]! } H1 t1 z S :=
    bm1.locals rfl rfl rfl rfl
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · rename_i hle
    have hle' : (S.codes[0 + l1.hold.toNat % 2 ^ S.lenbits.toNat]!).bits.toNat ≤ l1.bits.toNat :=
      UInt8.le_iff_toNat_le.mp hle
    refine SatX.pure ⟨⟨t1, bm2, hp1, hl1, hla1, hm1⟩, ⟨_, Nat.mod_lt _ (Nat.two_pow_pos _), rfl⟩, hle',
      rep_exit (live := fun _ => True) hrep hj1 trivial, hb1⟩
  · rename_i hgt
    have hgt' : l1.bits.toNat < (S.codes[0 + l1.hold.toNat % 2 ^ S.lenbits.toNat]!).bits.toNat :=
      UInt8.lt_iff_toNat_lt.mp (UInt8.not_le.mp hgt)
    have h25 := hent.bits_le
    refine SatX.bind (pullbyte_ok cb E.c rfl rfl bm2.inB (by show l1.bits.toNat < 56; omega) ?_ ?_)
    · intro H' q hk hI h0
      exact ⟨t1, z, S, bm2.sh.keep hk, ⟨q, 0, hI, by rw [h0]; exact Nat.le_refl _, fun h => absurd rfl h⟩,
        bm2.put, bm2.left⟩
    · intro l3 H3 t3 hk hin3 hm3 hb3 pb3 _ hh3
      have hb3' : l3.bits.toNat = l1.bits.toNat + 8 := hb3
      refine SatX.pure ⟨⟨DL.pull bm2 hp1 hl1 hla1 hm1 hk hin3 hm3 hb3 pb3, ?_, by omega⟩, by omega⟩
      rw [hb3]
      exact rep_pull (c := fun y => (S.codes[0 + y]!).bits.toNat) hgt' hh3

/-! ## The literal/length and distance code lengths -/

/-- The state of the loop over the code lengths, for the state `S0` after the code length code was built. -/
def TLs (E : BEnv) (z : ZStream) (S0 : InflateState) (M0 : Nat) (l : IL) (H : Heap) : Prop :=
  ∃ t S, BM E l H t z S ∧ IM l t ≤ M0 ∧ l.bits.toNat < 8 ∧ S = { S0 with «have» := S.«have», lens := S.lens } ∧
    S.«have».toNat ≤ S0.nlen.toNat + S0.ndist.toNat ∧ ∀ j, j < S.«have».toNat → S.lens[j]! ≤ 15

/-- The state after the loop: all lengths read, or a bad repeat (mode `BAD`). -/
def TLd (E : BEnv) (z : ZStream) (S0 : InflateState) (M0 : Nat) (l : IL) (H : Heap) : Prop :=
  (∃ t S, BM E l H t z S ∧ IM l t ≤ M0 ∧ l.bits.toNat < 8 ∧ S = { S0 with «have» := S.«have», lens := S.lens } ∧
    S0.nlen.toNat + S0.ndist.toNat ≤ S.«have».toNat ∧ ∀ j, j < S.«have».toNat → S.lens[j]! ≤ 15) ∨
  (∃ t z' S, BM E l H t z' S ∧ IM l t ≤ M0 ∧ S.mode = BAD)

/-- The outcome of one trip of the loop body, from a state whose counter was `hv0`. -/
def TLbody (E : BEnv) (z : ZStream) (S0 : InflateState) (M0 hv0 : Nat) : Except Ex Bool → IL → Heap → Prop
  | .error .leave, l, H => BLv E l H
  | .error (.ret _), _, _ => False
  | .ok true, l, H => TLd E z S0 M0 l H
  | .ok false, l, H => TLs E z S0 M0 l H ∧
      hvRank E (fun S => S0.nlen.toNat + S0.ndist.toNat - S.«have».toNat) H < S0.nlen.toNat + S0.ndist.toNat - hv0

/-- A bad repeat: `SET_BAD(msg); break;`. -/
theorem badBrk {E : BEnv} (cb : E.CB) {z0 : ZStream} {S0 : InflateState} {M0 hv0 : Nat} {l : IL} {H : Heap} {t : Nat}
    {z : ZStream} {S : InflateState} (bm : BM E l H t z S) (hM : IM l t ≤ M0) :
    SatX H l (do (MonadLiftT.monadLift (SET_BAD E.c.ctx "invalid bit length repeat") : X Unit); pure true)
      (TLbody E z0 S0 M0 hv0) := by
  obtain ⟨H', z', e, bm'⟩ := bm.setBad cb "invalid bit length repeat" (strIdx 15 (by decide) (by decide) (by decide))
  refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
  exact SatX.pure (Or.inr ⟨t, z', _, bm', hM, rfl⟩)

theorem have_succ {v : UInt32} (h : v.toNat < 320) : (v + 1).toNat = v.toNat + 1 := by
  rw [UInt32.toNat_add]; show (v.toNat + 1) % 2 ^ 32 = _; omega

/-- The lengths read so far stay at most 15 after `lens[have] = v` with `v ≤ 15`. -/
theorem lens_keep {L : Array UInt16} {hv : Nat} (hL : L.size = 320) (h320 : hv < 320)
    (hold : ∀ j, j < hv → L[j]! ≤ 15) (v : UInt16) (hv15 : v ≤ 15) :
    ∀ j, j < hv + 1 → (L.set! hv v)[j]! ≤ 15 := by
  intro j hj
  by_cases e : j = hv
  · subst e
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simp; omega)]
    simp only [Array.getElem_setIfInBounds_self]
    exact hv15
  · rw [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds_ne (Ne.symm e), ← getElem!_def]
    exact hold j (by omega)

/-- The end of a repeat code: the check against `nlen + ndist` and the `copy` stores of `len`. -/
theorem repTail_ok {E : BEnv} (cb : E.CB) {z : ZStream} {S0 : InflateState} {M0 : Nat}
    (hn : S0.nlen.toNat ≤ 286) (hd : S0.ndist.toNat ≤ 30) {l : IL} {H : Heap} {t : Nat} {S : InflateState}
    (bm : BM E l H t z S) (hM : IM l t ≤ M0) (hb8 : l.bits.toNat < 8)
    (hS : S = { S0 with «have» := S.«have», lens := S.lens })
    (hlt : S.«have».toNat < S0.nlen.toNat + S0.ndist.toNat) (hlens : ∀ j, j < S.«have».toNat → S.lens[j]! ≤ 15)
    (hlen : l.len.toUInt16 ≤ 15) (hc1 : 1 ≤ l.copy.toNat) (hc2 : l.copy.toNat ≤ 138) :
    SatX H l (do
      let s ← C.ldState E.c.st
      if s.«have» + (← get).copy > s.nlen + s.ndist then
        SET_BAD E.c.ctx "invalid bit length repeat"
        return true
      xwhile (do return (← get).copy != 0) (do
        modify fun l => { l with copy := l.copy - 1 }
        let hv ← rdS E.c.st (·.«have»)
        wrS E.c.st fun s => { s with «have» := s.«have» + 1 }
        Ptr.store (← (Ptr.ref (WRef.lens E.b) 0 : WPtr).add (Int.ofNat hv.toNat)) (← get).len.toUInt16)
      return false) (TLbody E z S0 M0 S.«have».toNat) := by
  have hnl : S.nlen = S0.nlen := by rw [hS]
  have hnd : S.ndist = S0.ndist := by rw [hS]
  refine SatX.bind (liftEq bm.sh.ldState ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  have hsum : (S.«have» + l.copy).toNat = S.«have».toNat + l.copy.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by show _ < 4294967296; omega)
  have hnd' : (S.nlen + S.ndist).toNat = S0.nlen.toNat + S0.ndist.toNat := by
    rw [UInt32.toNat_add, hnl, hnd]; exact Nat.mod_eq_of_lt (by show _ < 4294967296; omega)
  split
  · exact badBrk cb bm hM
  rename_i hng
  have hle : S.«have».toNat + l.copy.toNat ≤ S0.nlen.toNat + S0.ndist.toNat := by
    have : ¬ (S.nlen + S.ndist).toNat < (S.«have» + l.copy).toNat := hng
    omega
  refine SatX.bind (SatX.mono (P := fun r l' H' => match r with
      | .ok () => TLs E z S0 M0 l' H' ∧
          hvRank E (fun S => S0.nlen.toNat + S0.ndist.toNat - S.«have».toNat) H' <
            S0.nlen.toNat + S0.ndist.toNat - S.«have».toNat
      | .error _ => False) ?_ ?_)
  · unfold xwhile
    refine xwhileBrk_rank (fun l' H' => ∃ S', BM E l' H' t z S' ∧ l' = { l with copy := l'.copy } ∧
        S' = { S0 with «have» := S'.«have», lens := S'.lens } ∧
        S'.«have».toNat + l'.copy.toNat = S.«have».toNat + l.copy.toNat ∧
        (∀ j, j < S'.«have».toNat → S'.lens[j]! ≤ 15))
      (fun l' _ => l'.copy.toNat) _ ?_ ⟨S, bm, rfl, hS, rfl, hlens⟩
      (by have := l.copy.toNat_lt; unfold fuel; omega)
    rintro l1 H1 ⟨S1, bm1, hl1, hS1, hs1, hlens1⟩
    refine SatX.bind (SatX.get ?_)
    refine SatX.pure ?_
    dsimp only
    by_cases h0 : l1.copy = 0
    · simp only [h0, bne_self_eq_false]
      have hc0 : l1.copy.toNat = 0 := by rw [h0]; rfl
      refine ⟨⟨t, S1, bm1, ?_, ?_, hS1, by omega, hlens1⟩, ?_⟩
      · unfold IM at hM ⊢; rw [hl1]; exact hM
      · rw [hl1]; exact hb8
      · rw [hvRank_of bm1.sh]; omega
    · have h0' : (l1.copy != 0) = true := by simpa using h0
      rw [h0']
      have hc1' : 1 ≤ l1.copy.toNat := u32_ne_zero h0
      have hcsub : (l1.copy - 1).toNat = l1.copy.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 1 ≤ _; omega)]; rfl
      refine SatX.bind (SatX.bind (SatX.modify ?_))
      have bm2 : BM E { l1 with copy := l1.copy - 1 } H1 t z S1 := bm1.locals rfl rfl rfl rfl
      have h320 : S1.«have».toNat < 320 := by omega
      refine SatX.bind (liftEq (bm2.sh.rdS _) ?_)
      obtain ⟨e3, bm3⟩ := bm2.wS' cb (S' := { S1 with «have» := S1.«have» + 1 })
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun s => { s with «have» := s.«have» + 1 }) rfl
      refine SatX.bind (SatX.lift (Sat.of_eq e3 ?_))
      refine SatX.bind (liftEq (bm3.sh.addLens (k := S1.«have».toNat) (by omega)) ?_)
      refine SatX.bind (SatX.get ?_)
      refine SatX.lift (Sat.of_eq (bm3.sh.storeLens (k := S1.«have».toNat) (by omega) _) (SatX.pure ?_))
      have bm4 := bm3.wS cb (SKeep.lensSet _ S1.«have».toNat ({ l1 with copy := l1.copy - 1 } : IL).len.toUInt16)
      have hlen1 : ({ l1 with copy := l1.copy - 1 } : IL).len.toUInt16 ≤ 15 := by
        show l1.len.toUInt16 ≤ 15
        have : l1.len = l.len := by rw [hl1]
        rw [this]; exact hlen
      refine ⟨⟨_, bm4, ?_, by rw [hS1], ?_, ?_⟩, ?_⟩
      · rw [hl1]
      · show (S1.«have» + 1).toNat + (l1.copy - 1).toNat = _
        rw [have_succ h320, hcsub]; omega
      · show ∀ j, j < (S1.«have» + 1).toNat → (S1.lens.set! _ _)[j]! ≤ 15
        rw [have_succ h320]
        exact lens_keep (by rw [bm1.sh.lens]) h320 hlens1 _ hlen1
      · show (l1.copy - 1).toNat < l1.copy.toNat
        rw [hcsub]; omega
  · rintro r l2 H2 p
    match r, p with
    | .ok (), p => exact SatX.pure p

/-- The end of a repeat code (`infback.c:318-325`), verbatim. -/
def bTail (c : BCtx) (lens : WPtr) : X Bool := do
  let s ← C.ldState c.st
  if s.«have» + (← get).copy > s.nlen + s.ndist then
    SET_BAD c.ctx "invalid bit length repeat"
    return true
  xwhile (do return (← get).copy != 0) (do
    modify fun l => { l with copy := l.copy - 1 }
    let hv ← rdS c.st (·.«have»)
    wrS c.st fun s => { s with «have» := s.«have» + 1 }
    Ptr.store (← lens.add (Int.ofNat hv.toNat)) (← get).len.toUInt16)
  return false

/-- The state after the lookup of a repeat code. -/
structure RepPre (E : BEnv) (z : ZStream) (S0 : InflateState) (M0 : Nat) (l : IL) (H : Heap) (t : Nat)
    (S : InflateState) (h : Code) : Prop where
  bm : BM E l H t z S
  hM : IM l t ≤ M0
  hS : S = { S0 with «have» := S.«have», lens := S.lens }
  hlt : S.«have».toNat < S0.nlen.toNat + S0.ndist.toNat
  hlens : ∀ j, j < S.«have».toNat → S.lens[j]! ≤ 15
  hn : S0.nlen.toNat ≤ 286
  hd : S0.ndist.toNat ≤ 30
  h25 : h.bits.toNat ≤ 25
  hb1 : h.bits.toNat ≤ l.bits.toNat
  hb2 : l.bits.toNat < h.bits.toNat + 8

/-- The repeat codes 17 and 18: `NEEDBITS(here.bits + k); DROPBITS(here.bits); len = 0; copy = base + BITS(k);
DROPBITS(k);` and the end of a repeat code. -/
theorem repK_ok {E : BEnv} (cb : E.CB) {z : ZStream} {S0 : InflateState} {M0 : Nat} {l : IL} {H : Heap} {t : Nat}
    {S : InflateState} {h : Code} (P : RepPre E z S0 M0 l H t S h) (k base : UInt32) (hk1 : 1 ≤ k.toNat)
    (hk : k.toNat ≤ 7) (hb1 : 1 ≤ base.toNat) (hb2 : base.toNat + 2 ^ k.toNat ≤ 139) :
    SatX H l (do
      ZlibNg.Infback.NEEDBITS E.c (h.bits.toUInt32 + k)
      DROPBITS h.bits.toUInt32
      modify fun l => { l with len := 0 }
      let b ← BITS k
      modify fun l => { l with copy := base + b.toUInt32 }
      DROPBITS k
      bTail E.c (.ref (.lens E.b) 0)) (TLbody E z S0 M0 S.«have».toNat) := by
  have hhb : h.bits.toUInt32.toNat = h.bits.toNat := UInt8.toNat_toUInt32 _
  have hn : (h.bits.toUInt32 + k).toNat = h.bits.toNat + k.toNat := by
    rw [UInt32.toNat_add, hhb]; exact Nat.mod_eq_of_lt (by have := P.h25; omega)
  have h25 := P.h25
  have hbl := P.hb1
  have hbu := P.hb2
  refine SatX.bind (needbits_ok cb E.c rfl rfl P.bm.inB _ (by rw [hn]; omega) ?_ ?_)
  · intro l' H' t' q hk' hI hp h0 _ _
    exact leave_of_pull P.bm hk' hI hp h0
  intro l3 H3 t3 hk3 hin3 hmeas3 hge3 hle3 hp3 _
  rw [hn] at hge3 hle3
  have hle3' : l3.bits.toNat ≤ h.bits.toNat + k.toNat + 7 := by
    have : max l.bits.toNat (h.bits.toNat + k.toNat + 7) ≤ h.bits.toNat + k.toNat + 7 :=
      Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩
    omega
  have bm3 : BM E l3 H3 t3 z S := P.bm.pulled hk3 hin3 hmeas3 (by omega) hp3
  refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hhb]; show _ < 64; omega) ?_)
  have hd4 : (l3.bits - h.bits.toUInt32.toUInt8).toNat = l3.bits.toNat - h.bits.toNat := by
    have h8 : h.bits.toUInt32.toUInt8 = h.bits := by simp
    rw [h8, UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by omega))]
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (bits_ok k (by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega) ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (dropbits_ok k (by rw [UInt32.lt_iff_toNat_lt]; show _ < 64; omega) ?_)
  have hk8 : k.toUInt8.toNat = k.toNat := by rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by omega)
  have hd5 : (l3.bits - h.bits.toUInt32.toUInt8 - k.toUInt8).toNat = l3.bits.toNat - h.bits.toNat - k.toNat := by
    rw [UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by rw [hd4, hk8]; omega)), hd4, hk8]
  have hbk := ZlibNgF.Proof.InflateLoop.bits_lt (l3.hold >>> h.bits.toUInt32.toUInt64) k (by omega)
  have hpow : 2 ^ k.toNat ≤ 128 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by decide)
  have hcp : (base + ((l3.hold >>> h.bits.toUInt32.toUInt64) &&& ((1 : UInt32) <<< k - 1).toUInt64).toUInt32).toNat =
      base.toNat + ((l3.hold >>> h.bits.toUInt32.toUInt64) &&& ((1 : UInt32) <<< k - 1).toUInt64).toNat := by
    rw [UInt32.toNat_add, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (a := UInt64.toNat _) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine repTail_ok cb P.hn P.hd (bm3.locals rfl rfl rfl rfl) ?_ ?_ P.hS P.hlt P.hlens
    (by show (0 : UInt32).toUInt16 ≤ 15; decide) ?_ ?_
  · have := P.hM
    unfold IM at this ⊢
    show 8 * (l3.have_.toNat + t3) + (l3.bits - h.bits.toUInt32.toUInt8 - k.toUInt8).toNat ≤ M0
    rw [hd5]; omega
  · show (l3.bits - h.bits.toUInt32.toUInt8 - k.toUInt8).toNat < 8
    rw [hd5]; omega
  · show 1 ≤ (base + _).toNat; rw [hcp]; omega
  · show (base + _).toNat ≤ 138; rw [hcp]; omega

/-- The repeat code 16: the previous length, 3 to 6 times. -/
theorem rep16_ok {E : BEnv} (cb : E.CB) {z : ZStream} {S0 : InflateState} {M0 : Nat} {l : IL} {H : Heap} {t : Nat}
    {S : InflateState} {h : Code} (P : RepPre E z S0 M0 l H t S h) :
    SatX H l (do
      ZlibNg.Infback.NEEDBITS E.c (h.bits.toUInt32 + 2)
      DROPBITS h.bits.toUInt32
      let hv ← rdS E.c.st (·.«have»)
      if hv == 0 then
        SET_BAD E.c.ctx "invalid bit length repeat"
        return true
      let len ← Ptr.index (.ref (.lens E.b) 0 : WPtr) (Int.ofNat (hv - 1).toNat)
      modify fun l => { l with len := len.toUInt32 }
      let b ← BITS 2
      modify fun l => { l with copy := 3 + b.toUInt32 }
      DROPBITS 2
      bTail E.c (.ref (.lens E.b) 0)) (TLbody E z S0 M0 S.«have».toNat) := by
  have hhb : h.bits.toUInt32.toNat = h.bits.toNat := UInt8.toNat_toUInt32 _
  have hn : (h.bits.toUInt32 + 2).toNat = h.bits.toNat + 2 := by
    have : (2 : UInt32).toNat = 2 := rfl
    rw [UInt32.toNat_add, hhb, this]; exact Nat.mod_eq_of_lt (by have := P.h25; omega)
  have h25 := P.h25
  have hbl := P.hb1
  have hbu := P.hb2
  refine SatX.bind (needbits_ok cb E.c rfl rfl P.bm.inB _ (by rw [hn]; omega) ?_ ?_)
  · intro l' H' t' q hk' hI hp h0 _ _
    exact leave_of_pull P.bm hk' hI hp h0
  intro l3 H3 t3 hk3 hin3 hmeas3 hge3 hle3 hp3 _
  rw [hn] at hge3 hle3
  have hle3' : l3.bits.toNat ≤ h.bits.toNat + 2 + 7 := by
    have : max l.bits.toNat (h.bits.toNat + 2 + 7) ≤ h.bits.toNat + 2 + 7 :=
      Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩
    omega
  have bm3 : BM E l3 H3 t3 z S := P.bm.pulled hk3 hin3 hmeas3 (by omega) hp3
  refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hhb]; show _ < 64; omega) ?_)
  have hd4 : (l3.bits - h.bits.toUInt32.toUInt8).toNat = l3.bits.toNat - h.bits.toNat := by
    have h8 : h.bits.toUInt32.toUInt8 = h.bits := by simp
    rw [h8, UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by omega))]
  have bm4 := bm3.locals (l' := { l3 with
    hold := l3.hold >>> h.bits.toUInt32.toUInt64
    bits := l3.bits - h.bits.toUInt32.toUInt8 }) rfl rfl rfl rfl
  have hM4 : IM { l3 with
      hold := l3.hold >>> h.bits.toUInt32.toUInt64
      bits := l3.bits - h.bits.toUInt32.toUInt8 } t3 ≤ M0 := by
    have := P.hM
    unfold IM at this ⊢
    show 8 * (l3.have_.toNat + t3) + (l3.bits - h.bits.toUInt32.toUInt8).toNat ≤ M0
    rw [hd4]; omega
  refine SatX.bind (liftEq (bm4.sh.rdS _) ?_)
  dsimp only
  split
  · exact badBrk cb bm4 hM4
  rename_i hv0
  have hv0' : S.«have» ≠ 0 := by simpa using hv0
  have hv1 : 1 ≤ S.«have».toNat := u32_ne_zero hv0'
  have hsub : (S.«have» - 1).toNat = S.«have».toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 1 ≤ _; omega)]; rfl
  have hlt := P.hlt
  have hnn := P.hn
  have hdd := P.hd
  refine SatX.bind (liftEq (bm4.sh.indexLens (k := (S.«have» - 1).toNat) (by omega)) ?_)
  have hlen : S.lens[(S.«have» - 1).toNat]! ≤ 15 := P.hlens _ (by omega)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (bits_ok 2 (by decide) ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (dropbits_ok 2 (by decide) ?_)
  have hd5 : (l3.bits - h.bits.toUInt32.toUInt8 - (2 : UInt32).toUInt8).toNat = l3.bits.toNat - h.bits.toNat - 2 := by
    rw [UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by rw [hd4]; show 2 ≤ _; omega)), hd4]; rfl
  have hbk := ZlibNgF.Proof.InflateLoop.bits_lt (l3.hold >>> h.bits.toUInt32.toUInt64) 2 (by decide)
  have h4 : (2 : Nat) ^ (2 : UInt32).toNat = 4 := rfl
  have hcp : ((3 : UInt32) + ((l3.hold >>> h.bits.toUInt32.toUInt64) &&& ((1 : UInt32) <<< 2 - 1).toUInt64).toUInt32).toNat =
      3 + ((l3.hold >>> h.bits.toUInt32.toUInt64) &&& ((1 : UInt32) <<< 2 - 1).toUInt64).toNat := by
    rw [UInt32.toNat_add, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (a := UInt64.toNat _) (by omega)]
    exact Nat.mod_eq_of_lt (by show _ < 4294967296; have : (3 : UInt32).toNat = 3 := rfl; omega)
  refine repTail_ok cb P.hn P.hd (bm4.locals rfl rfl rfl rfl) ?_ ?_ P.hS P.hlt P.hlens ?_ ?_ ?_
  · have := P.hM
    unfold IM at this ⊢
    show 8 * (l3.have_.toNat + t3) + (l3.bits - h.bits.toUInt32.toUInt8 - (2 : UInt32).toUInt8).toNat ≤ M0
    rw [hd5]; omega
  · show (l3.bits - h.bits.toUInt32.toUInt8 - (2 : UInt32).toUInt8).toNat < 8
    rw [hd5]; omega
  · show (S.lens[(S.«have» - 1).toNat]!).toUInt32.toUInt16 ≤ 15
    rw [UInt16.le_iff_toNat_le] at hlen ⊢
    simpa using hlen
  · show 1 ≤ (3 + _ : UInt32).toNat; rw [hcp]; omega
  · show (3 + _ : UInt32).toNat ≤ 138; rw [hcp]; omega

/-- What the loop over the code lengths needs of the state after the code length code was built. -/
structure S0OK (E : BEnv) (S0 : InflateState) : Prop where
  n1 : 257 ≤ S0.nlen.toNat
  n2 : S0.nlen.toNat ≤ 286
  d1 : 1 ≤ S0.ndist.toNat
  d2 : S0.ndist.toNat ≤ 30
  lc : S0.lencode = .val (.ref (.codes E.b) 0)
  ct : ∃ e, CodeTable S0.codes 0 e S0.lenbits.toNat 25 false
  la : LvlAll S0.codes 0 S0.lenbits.toNat
  op : ∀ j, j < 2 ^ S0.lenbits.toNat → S0.codes[0 + j]!.op.toNat &&& 16 = 0

/-- The loop over the literal/length and distance code lengths (`infback.c:285-327`). -/
theorem tl_loop {E : BEnv} (cb : E.CB) {z : ZStream} {S0 : InflateState} {M0 : Nat} (h0 : S0OK E S0)
    {l : IL} {H : Heap} (P : TLs E z S0 M0 l H) :
    SatX H l (xwhileBrk (do
        let s ← C.ldState E.c.st
        return s.«have» < s.nlen + s.ndist)
      (do
        xloopBrk (do
          let lc ← (← rdS E.c.st (·.lencode)).get
          let b ← BITS (← rdS E.c.st (·.lenbits))
          let here : Code ← Ptr.index lc (Int.ofNat b.toNat)
          modify fun l => { l with here := here }
          if (← get).here.bits <= (← get).bits then return true
          PULLBYTE E.c
          return false)
        let here := (← get).here
        if here.val < 16 then
          DROPBITS here.bits.toUInt32
          let hv ← rdS E.c.st (·.«have»)
          wrS E.c.st fun s => { s with «have» := s.«have» + 1 }
          Ptr.store (← (Ptr.ref (WRef.lens E.b) 0 : WPtr).add (Int.ofNat hv.toNat)) here.val
          return false
        else
          if here.val == 16 then
            ZlibNg.Infback.NEEDBITS E.c (here.bits.toUInt32 + 2)
            DROPBITS here.bits.toUInt32
            let hv ← rdS E.c.st (·.«have»)
            if hv == 0 then
              SET_BAD E.c.ctx "invalid bit length repeat"
              return true
            let len ← Ptr.index (Ptr.ref (WRef.lens E.b) 0 : WPtr) (Int.ofNat (hv - 1).toNat)
            modify fun l => { l with len := len.toUInt32 }
            let b ← BITS 2
            modify fun l => { l with copy := 3 + b.toUInt32 }
            DROPBITS 2
          else if here.val == 17 then
            ZlibNg.Infback.NEEDBITS E.c (here.bits.toUInt32 + 3)
            DROPBITS here.bits.toUInt32
            modify fun l => { l with len := 0 }
            let b ← BITS 3
            modify fun l => { l with copy := 3 + b.toUInt32 }
            DROPBITS 3
          else
            ZlibNg.Infback.NEEDBITS E.c (here.bits.toUInt32 + 7)
            DROPBITS here.bits.toUInt32
            modify fun l => { l with len := 0 }
            let b ← BITS 7
            modify fun l => { l with copy := 11 + b.toUInt32 }
            DROPBITS 7
          let s ← C.ldState E.c.st
          if s.«have» + (← get).copy > s.nlen + s.ndist then
            SET_BAD E.c.ctx "invalid bit length repeat"
            return true
          xwhile (do return (← get).copy != 0) (do
            modify fun l => { l with copy := l.copy - 1 }
            let hv ← rdS E.c.st (·.«have»)
            wrS E.c.st fun s => { s with «have» := s.«have» + 1 }
            Ptr.store (← (Ptr.ref (WRef.lens E.b) 0 : WPtr).add (Int.ofNat hv.toNat)) (← get).len.toUInt16)
          return false))
      (fun r l' H' => match r with
        | .ok () => TLd E z S0 M0 l' H'
        | .error .leave => BLv E l' H'
        | .error (.ret _) => False) := by
  obtain ⟨n1, n2, d1, d2, hlc, ⟨e, ct⟩, hla, h16⟩ := h0
  refine xwhileBrk_rank (TLs E z S0 M0) (fun _ H => hvRank E (fun S => S0.nlen.toNat + S0.ndist.toNat - S.«have».toNat) H)
    _ ?_ P (by obtain ⟨t, S, bm, -⟩ := P; rw [hvRank_of bm.sh]; unfold fuel; omega)
  rintro l1 H1 ⟨t1, S1, bm1, hM1, hb1, hS1, hhv1, hlens1⟩
  have hnl : S1.nlen = S0.nlen := by rw [hS1]
  have hnd : S1.ndist = S0.ndist := by rw [hS1]
  have e1 : S1.lencode = S0.lencode := by rw [hS1]
  have e2 : S1.codes = S0.codes := by rw [hS1]
  have e3 : S1.lenbits = S0.lenbits := by rw [hS1]
  refine SatX.bind (liftEq bm1.sh.ldState ?_)
  refine SatX.pure ?_
  dsimp only
  have hsum : (S1.nlen + S1.ndist).toNat = S0.nlen.toNat + S0.ndist.toNat := by
    rw [UInt32.toNat_add, hnl, hnd]; exact Nat.mod_eq_of_lt (by show _ < 4294967296; omega)
  by_cases hlt : S1.«have» < S1.nlen + S1.ndist
  · simp only [hlt, decide_true]
    have hlt' : S1.«have».toNat < S0.nlen.toNat + S0.ndist.toNat := by
      rw [← hsum]; exact UInt32.lt_iff_toNat_lt.mp hlt
    refine SatX.mono (P := TLbody E z S0 M0 S1.«have».toNat) ?_ ?_
    · refine SatX.bind (SatX.mono (bdecC cb bm1 (e1.trans hlc) (by rw [e2, e3]; exact ct) (by rw [e2, e3]; exact hla)
        (by rw [e2, e3]; exact h16) hb1) ?_)
      rintro r l2 H2 p
      match r, p with
      | .error .leave, p => exact p
      | .ok (), ⟨⟨t2, bm2, hp2, hl2, _, hm2⟩, ⟨j, hj, hh⟩, hbl, hbu, hb32⟩ =>
      refine SatX.bind (SatX.get ?_)
      dsimp only
      have hent := ct.ent (0 + j) (Nat.zero_le _) (by have := ct.root; rw [e3] at hj; omega)
      have h25 : l2.here.bits.toNat ≤ 25 := by rw [hh, e2]; exact hent.bits_le
      have hM2 : IM l2 t2 ≤ M0 := by unfold IM at hM1 ⊢; omega
      split
      · rename_i hv16
        have hhb : l2.here.bits.toUInt32.toNat = l2.here.bits.toNat := UInt8.toNat_toUInt32 _
        refine SatX.bind (dropbits_ok _ (by rw [UInt32.lt_iff_toNat_lt, hhb]; show _ < 64; omega) ?_)
        have hd3 : (l2.bits - l2.here.bits.toUInt32.toUInt8).toNat = l2.bits.toNat - l2.here.bits.toNat := by
          have h8 : l2.here.bits.toUInt32.toUInt8 = l2.here.bits := by simp
          rw [h8, UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (by omega))]
        have bm3 := bm2.locals (l' := { l2 with
          hold := l2.hold >>> l2.here.bits.toUInt32.toUInt64
          bits := l2.bits - l2.here.bits.toUInt32.toUInt8 }) rfl rfl rfl rfl
        have h320 : S1.«have».toNat < 320 := by omega
        refine SatX.bind (liftEq (bm3.sh.rdS _) ?_)
        obtain ⟨e4, bm4⟩ := bm3.wS' cb (S' := { S1 with «have» := S1.«have» + 1 })
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun s => { s with «have» := s.«have» + 1 }) rfl
        refine SatX.bind (SatX.lift (Sat.of_eq e4 ?_))
        refine SatX.bind (liftEq (bm4.sh.addLens (k := S1.«have».toNat) (by omega)) ?_)
        refine SatX.bind (SatX.lift (Sat.of_eq (bm4.sh.storeLens (k := S1.«have».toNat) (by omega) _) ?_))
        have bm5 := bm4.wS cb (SKeep.lensSet _ S1.«have».toNat l2.here.val)
        have hv15 : l2.here.val ≤ 15 := by
          rw [UInt16.le_iff_toNat_le]; have := UInt16.lt_iff_toNat_lt.mp hv16; show _ ≤ 15
          have : (16 : UInt16).toNat = 16 := rfl; omega
        refine SatX.pure ⟨⟨_, _, bm5, ?_, ?_, by rw [hS1], ?_, ?_⟩, ?_⟩
        · unfold IM at hM2 ⊢
          show 8 * (l2.have_.toNat + t2) + (l2.bits - l2.here.bits.toUInt32.toUInt8).toNat ≤ M0
          rw [hd3]; omega
        · show (l2.bits - l2.here.bits.toUInt32.toUInt8).toNat < 8
          rw [hd3]; omega
        · show (S1.«have» + 1).toNat ≤ _
          rw [have_succ h320]; omega
        · show ∀ j, j < (S1.«have» + 1).toNat → (S1.lens.set! _ _)[j]! ≤ 15
          rw [have_succ h320]
          exact lens_keep (by rw [bm1.sh.lens]) h320 hlens1 _ hv15
        · rw [hvRank_of bm5.sh]
          show S0.nlen.toNat + S0.ndist.toNat - (S1.«have» + 1).toNat < _
          rw [have_succ h320]; omega
      · have P : RepPre E z S0 M0 l2 H2 t2 S1 l2.here :=
          ⟨bm2, hM2, hS1, hlt', hlens1, n2, d2, h25, hbl, hbu⟩
        split
        · exact rep16_ok cb P
        · split
          · exact repK_ok cb P 3 3 (by decide) (by decide) (by decide) (by decide)
          · exact repK_ok cb P 7 11 (by decide) (by decide) (by decide) (by decide)
    · rintro r l2 H2 p
      match r, p with
      | .error .leave, p => exact p
      | .ok true, p => exact p
      | .ok false, ⟨p1, p2⟩ => exact ⟨p1, by rw [hvRank_of bm1.sh]; exact p2⟩
  · simp only [hlt, decide_false]
    refine Or.inl ⟨t1, S1, bm1, hM1, hb1, hS1, ?_, hlens1⟩
    have := UInt32.not_lt.mp hlt; rw [UInt32.le_iff_toNat_le, hsum] at this; exact this

/-! ## The two tables -/

/-- `Rep` depends only on the entries of its table's region. -/
theorem Rep.congr {a a' : Array Code} {o e n m : Nat} {dist : Bool} (t : CodeTable a o e n m dist)
    (rp : Rep a o n dist) (he : ∀ j, o ≤ j → j < e → a'[j]! = a[j]!) : Rep a' o n dist := by
  have hr := t.root
  obtain ⟨r1, r2⟩ := rp
  refine ⟨lvl_congr (fun x hx => he _ (Nat.le_add_right _ _) (by omega)) r1, fun j hj hl => ?_⟩
  have ej := he (o + j) (Nat.le_add_right _ _) (by omega)
  rw [ej] at hl ⊢
  obtain ⟨hlt, -⟩ := t.link (o + j) (Nat.le_add_right _ _) (by omega) hl
  exact lvl_congr (fun x hx => he _ (by omega) (by omega)) (r2 j hj hl)

theorem rank_LEN' : rank LEN = 1 := by decide

/-- After the loop over the code lengths: the check of the mode, the end-of-block code, the two tables, and the
fall-through to `LEN`. -/
theorem tb_tail {E : BEnv} (cb : E.CB) {z : ZStream} {S0 : InflateState} {M0 m : Nat} (hm : 32 * M0 + 5 ≤ m)
    (h0 : S0OK E S0) (hmode : S0.mode = TABLE) {l : IL} {H : Heap} (P : TLd E z S0 M0 l H) :
    SatX H l (do
      if (← rdS E.c.st (·.mode)) == BAD then return
      if (← Ptr.index (Ptr.ref (WRef.lens E.b) 0 : WPtr) 256) == (0 : UInt16) then
        SET_BAD E.c.ctx "invalid code -- missing end-of-block"
        return
      wrS E.c.st fun s => { s with next := .val (Ptr.ref (CodeRef.codes E.b) 0) }
      let nx ← (← rdS E.c.st (·.next)).get
      wrS E.c.st fun s => { s with lencode := .val nx }
      wrS E.c.st fun s => { s with lenbits := MAX_LEN_ROOT_BITS }
      let s ← C.ldState E.c.st
      let (ret, nx, lb) ← ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.LENS (Ptr.ref (WRef.lens E.b) 0 : WPtr)
        s.nlen (← s.next.get) s.lenbits (← workP E.c.st)
      wrS E.c.st fun s => { s with next := .val nx, lenbits := lb }
      modify fun l => { l with ret := ret }
      if ret != 0 then
        SET_BAD E.c.ctx "invalid literal/lengths set"
        return
      let nx ← (← rdS E.c.st (·.next)).get
      wrS E.c.st fun s => { s with distcode := .val nx }
      wrS E.c.st fun s => { s with distbits := 9 }
      let s ← C.ldState E.c.st
      let (ret, nx, db) ← ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.DISTS
        (← (Ptr.ref (WRef.lens E.b) 0 : WPtr).add (Int.ofNat s.nlen.toNat)) s.ndist (← s.next.get) s.distbits
        (← workP E.c.st)
      wrS E.c.st fun s => { s with next := .val nx, distbits := db }
      modify fun l => { l with ret := ret }
      if ret != 0 then
        SET_BAD E.c.ctx "invalid distances set"
        return
      setMode E.c.st LEN
      back_LEN E.c) (Post E m) := by
  rcases P with ⟨t, S, bm, hM, hb8, hS, hcnt, hlens⟩ | ⟨t, z', S, bm, hM, hbad⟩
  rotate_left
  · refine SatX.bind (liftEq (bm.sh.rdS _) ?_)
    rw [hbad]
    simp only [beq_self_eq_true, ↓reduceIte]
    refine SatX.pure ⟨t, z', S, ⟨bm, Or.inl hbad, BModeOK.quiet _ S (by rw [hbad]; decide) (by rw [hbad]; decide)⟩, ?_⟩
    unfold μ IM at *; rw [hbad, rank_BAD]; omega
  obtain ⟨n1, n2, d1, d2, -, -, -, -⟩ := h0
  have hmS : S.mode = TABLE := by rw [hS, hmode]
  have hnl : S.nlen = S0.nlen := by rw [hS]
  have hnd : S.ndist = S0.ndist := by rw [hS]
  refine SatX.bind (liftEq (bm.sh.rdS _) ?_)
  rw [hmS]
  simp only [show (TABLE == BAD) = false by decide, Bool.false_eq_true, ↓reduceIte]
  refine SatX.bind (liftEq (bm.sh.indexLens (k := 256) (by decide)) ?_)
  dsimp only
  split
  · exact bad_exit cb bm hM hm "invalid code -- missing end-of-block" (strIdx 17 (by decide) (by decide) (by decide))
  have hcs := bm.sh.codes
  have hls := bm.sh.lens
  have hws := bm.sh.work
  -- the literal/length table
  let S4 : InflateState := { S with
    next := .val (.ref (.codes E.b) 0)
    lencode := .val (.ref (.codes E.b) 0)
    lenbits := MAX_LEN_ROOT_BITS }
  have k4 : SKeep S S4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨e1, bm1⟩ := bm.wS' cb (S' := { S with next := .val (.ref (.codes E.b) 0) })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun s => { s with next := .val (.ref (.codes E.b) 0) }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e1 ?_))
  refine SatX.bind (liftEq (bm1.sh.rdS _) ?_)
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  obtain ⟨e2, bm2⟩ := bm1.wS' cb (S' := { { S with next := .val (.ref (.codes E.b) 0) } with
      lencode := .val (.ref (.codes E.b) 0) })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun s => { s with lencode := .val (.ref (.codes E.b) 0) }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e2 ?_))
  obtain ⟨e3, bm3⟩ := bm2.wS' cb (S' := S4) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with lenbits := MAX_LEN_ROOT_BITS }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e3 ?_))
  refine SatX.bind (liftEq bm3.sh.ldState ?_)
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  refine SatX.bind (liftEq (a := (.ref (.work E.b) 0 : WPtr)) rfl ?_)
  generalize hH3 : withS (withS (withS H E.b _) E.b _) E.b S4 = H3 at bm3
  obtain ⟨ret, o', lb, codes', work', e, hcs1, hws1, -, -, hok, herr⟩ :=
    Inftrees.table_run_rep H3 E.b S4 ZlibNg.Inftrees.LENS 0 S.nlen 0 10 bm3.sh.istate hcs hls hws
      (Or.inr (Or.inl ⟨rfl, rfl, by rw [hnl]; exact n1, by rw [hnl]; exact n2, rfl, rfl⟩))
      (fun j hj => by
        have := hlens (0 + j) (by rw [hnl, ← hnd] at *; omega)
        rw [UInt16.le_iff_toNat_le] at this
        show _ ≤ (if ZlibNg.Inftrees.LENS = ZlibNg.Inftrees.CODES then 7 else 15)
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide))]; exact this)
  have e' : (ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.LENS (.ref (.lens E.b) 0) S4.nlen
      (.ref (.codes E.b) 0) S4.lenbits (.ref (.work E.b) 0) : M _) H3 =
      .ok ((ret, .ref (.codes E.b) o', lb), withS H3 E.b { S4 with codes := codes', work := work' }) := by
    rw [show S4.nlen = S.nlen from rfl, show S4.lenbits = 10 from rfl]
    unfold C.run at e; exact e
  refine SatX.bind (SatX.lift (Sat.of_eq e' ?_))
  dsimp only
  have bm4 := bm3.wS cb (S' := { S4 with codes := codes', work := work' })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by rw [hws1, ← hws], by rw [hcs1, ← hcs]⟩
  let S5 : InflateState := { S4 with
    codes := codes'
    work := work'
    next := .val (.ref (.codes E.b) o')
    lenbits := lb }
  obtain ⟨e5, bm5⟩ := bm4.wS' cb (S' := S5) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with next := .val (.ref (.codes E.b) o'), lenbits := lb }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e5 ?_))
  have bm5r := bm5.locals (l' := { l with ret := ret }) rfl rfl rfl rfl
  refine SatX.bind (SatX.modify ?_)
  dsimp only
  split
  · exact bad_exit cb bm5r hM hm "invalid literal/lengths set" (strIdx 23 (by decide) (by decide) (by decide))
  rename_i hne
  have h0r : ret = 0 := by simpa using hne
  obtain ⟨ho1, -, -, -, hct1, hrep1, -⟩ := hok h0r
  rw [Inftrees.mOf_lens, Inftrees.dOf_lens] at hct1
  rw [Inftrees.dOf_lens] at hrep1
  have ho1' : o' ≤ 1332 := by
    have e2 : (if ZlibNg.Inftrees.LENS = ZlibNg.Inftrees.DISTS then 592 else 1332) = 1332 := by decide
    omega
  -- the distance table
  refine SatX.bind (liftEq (bm5r.sh.rdS _) ?_)
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  obtain ⟨e6, bm6⟩ := bm5r.wS' cb (S' := { S5 with distcode := .val (.ref (.codes E.b) o') })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with distcode := .val (.ref (.codes E.b) o') }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e6 ?_))
  let S6 : InflateState := { S5 with
    distcode := .val (.ref (.codes E.b) o')
    distbits := 9 }
  obtain ⟨e7, bm7⟩ := bm6.wS' cb (S' := S6) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with distbits := 9 }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e7 ?_))
  refine SatX.bind (liftEq bm7.sh.ldState ?_)
  refine SatX.bind (liftEq (bm7.sh.addLens (k := S.nlen.toNat) (by rw [hnl]; omega)) ?_)
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  refine SatX.bind (liftEq (a := (.ref (.work E.b) 0 : WPtr)) rfl ?_)
  generalize hH7 : withS (withS (withS (withS H3 E.b _) E.b _) E.b _) E.b S6 = H7 at bm7
  have hcs6 : S6.codes.size = ENOUGH := by rw [hcs1]
  have hws6 : S6.work.size = 288 := hws1
  obtain ⟨ret2, o'', db, codes'', work'', e2, hcs2, hws2, hkeep2, -, hok2, herr2⟩ :=
    Inftrees.table_run_rep H7 E.b S6 ZlibNg.Inftrees.DISTS S.nlen.toNat S.ndist o' 9 bm7.sh.istate hcs6 hls hws6
      (Or.inr (Or.inr ⟨rfl, by rw [hnl]; exact n1, by rw [hnl]; exact n2, by rw [hnd]; exact d1,
        by rw [hnd]; exact d2, ho1', rfl⟩))
      (fun j hj => by
        have := hlens (S.nlen.toNat + j) (by rw [hnl, hnd] at *; omega)
        rw [UInt16.le_iff_toNat_le] at this
        show _ ≤ (if ZlibNg.Inftrees.DISTS = ZlibNg.Inftrees.CODES then 7 else 15)
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide))]; exact this)
  have e2' : (ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.DISTS (.ref (.lens E.b) S6.nlen.toNat) S6.ndist
      (.ref (.codes E.b) o') S6.distbits (.ref (.work E.b) 0) : M _) H7 =
      .ok ((ret2, .ref (.codes E.b) o'', db), withS H7 E.b { S6 with codes := codes'', work := work'' }) := by
    rw [show S6.nlen = S.nlen from rfl, show S6.ndist = S.ndist from rfl, show S6.distbits = 9 from rfl]
    unfold C.run at e2; exact e2
  refine SatX.bind (SatX.lift (Sat.of_eq e2' ?_))
  dsimp only
  have bm8 := bm7.wS cb (S' := { S6 with codes := codes'', work := work'' })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by rw [hws2]; exact hws6.symm, by rw [hcs2]; exact hcs6.symm⟩
  let S9 : InflateState := { S6 with
    codes := codes''
    work := work''
    next := .val (.ref (.codes E.b) o'')
    distbits := db }
  obtain ⟨e9, bm9⟩ := bm8.wS' cb (S' := S9) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with next := .val (.ref (.codes E.b) o''), distbits := db }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e9 ?_))
  have bm9r := bm9.locals (l' := { { l with ret := ret } with ret := ret2 }) rfl rfl rfl rfl
  refine SatX.bind (SatX.modify ?_)
  dsimp only
  split
  · exact bad_exit cb bm9r hM hm "invalid distances set" (strIdx 21 (by decide) (by decide) (by decide))
  rename_i hne2
  have h02 : ret2 = 0 := by simpa using hne2
  obtain ⟨ho2, -, -, -, hct2, hrep2, -⟩ := hok2 h02
  rw [Inftrees.mOf_dists, Inftrees.dOf_dists] at hct2
  rw [Inftrees.dOf_dists] at hrep2
  have hct1' : CodeTable codes'' 0 o' lb.toNat 28 false :=
    hct1.congr (by rw [hcs2]; show o' ≤ 1924; omega) (fun j _ h2 => hkeep2 j h2)
  have hrep1' : Rep codes'' 0 lb.toNat false := Rep.congr hct1 hrep1 (fun j _ h2 => hkeep2 j h2)
  obtain ⟨e10, bm10⟩ := bm9r.setMode cb LEN
  refine SatX.bind (SatX.lift (Sat.of_eq e10 ?_))
  refine run_LEN E cb _ _ t z _ ⟨bm10, Or.inr hb8, ⟨fun _ => ⟨Or.inl ⟨0, o', rfl, hct1', hrep1'⟩,
    Or.inl ⟨o', o'', rfl, hct2, hrep2⟩⟩, fun e => absurd (show LEN = MATCH from e) (by decide)⟩⟩ rfl m ?_
  unfold μ IM at *; dsimp only; rw [rank_LEN']; omega

/-! ## `TABLE` -/

theorem mOf_codes : Inftrees.mOf ZlibNg.Inftrees.CODES = 25 := by decide

theorem mask_lt (x : UInt64) (k : UInt32) (hk : k.toNat ≤ 15) :
    (x &&& ((1 : UInt32) <<< k - 1).toUInt64).toUInt32.toNat < 2 ^ k.toNat := by
  have := ZlibNgF.Proof.InflateLoop.bits_lt x k hk
  rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by have : 2 ^ k.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hk; omega)]
  exact this

theorem add_small {a : UInt32} {k : Nat} (c : UInt32) (ha : a.toNat < 2 ^ k) (hk : k ≤ 5) (hc : c.toNat < 1000) :
    (a + c).toNat = a.toNat + c.toNat := by
  have : 2 ^ k ≤ 32 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by decide)
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by show _ < 4294967296; omega)

theorem u8_subL (a : UInt8) (n : UInt32) (h : n.toNat ≤ a.toNat) (hn : n.toNat < 256) :
    (a - n.toUInt8).toNat = a.toNat - n.toNat := by
  have hk' : n.toUInt8.toNat = n.toNat := by rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt hn
  rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hk']; exact h), hk']

theorem run_TABLE (E : BEnv) : ModeRun E back_TABLE (fun S => S.mode = TABLE) := by
  intro cb l H t z S bl hm m hμ
  have hb8 : l.bits.toNat < 8 := by
    rcases bl.bits with e | e
    · rw [hm] at e; exact absurd e (by decide)
    · exact e
  have hμ' : 32 * IM l t + 5 ≤ m := by
    unfold μ at hμ; rw [hm, rank_TABLE] at hμ; unfold IM; exact hμ
  generalize hM0 : IM l t = M0 at hμ'
  unfold back_TABLE
  refine SatX.bind (needbits_ok cb E.c rfl rfl bl.inB 14 (by decide) ?_ ?_)
  · intro l' H' t' q hk hI hp h0 _ _
    exact leave_of_pull bl.toBM hk hI hp h0
  intro l1 H1 t1 hk hin1 hmeas h14 hb1 hp1 _
  have h14' : 14 ≤ l1.bits.toNat := h14
  have hb1' : l1.bits.toNat ≤ 21 := by
    have : max l.bits.toNat ((14 : UInt32).toNat + 7) ≤ 21 := Nat.max_le.mpr ⟨by omega, by decide⟩
    omega
  have bm1 : BM E l1 H1 t1 z S := bl.toBM.pulled hk hin1 hmeas (by omega) hp1
  have hM1 : IM l1 t1 = M0 := by rw [← hM0]; exact hmeas
  -- the three counts
  refine SatX.bind (bits_ok 5 (by decide) ?_)
  refine SatX.bind (SatX.lift (Sat.of_eq (bm1.sh.wrS _) ?_))
  have bm2 := bm1.wS cb (S' := { S with nlen := (l1.hold &&& ((1 : UInt32) <<< 5 - 1).toUInt64).toUInt32 + 257 })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.bind (dropbits_ok 5 (by decide) ?_)
  refine SatX.bind (bits_ok 5 (by decide) ?_)
  refine SatX.bind (SatX.lift (Sat.of_eq (bm2.sh.wrS _) ?_))
  have bm3 := bm2.wS cb (S' := { { S with nlen := (l1.hold &&& ((1 : UInt32) <<< 5 - 1).toUInt64).toUInt32 + 257 } with
      ndist := ((l1.hold >>> (5 : UInt32).toUInt64) &&& ((1 : UInt32) <<< 5 - 1).toUInt64).toUInt32 + 1 })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.bind (dropbits_ok 5 (by decide) ?_)
  refine SatX.bind (bits_ok 4 (by decide) ?_)
  refine SatX.bind (SatX.lift (Sat.of_eq (bm3.sh.wrS _) ?_))
  generalize hnl : (l1.hold &&& ((1 : UInt32) <<< 5 - 1).toUInt64).toUInt32 + 257 = nlen at bm3 ⊢
  generalize hnd : ((l1.hold >>> (5 : UInt32).toUInt64) &&& ((1 : UInt32) <<< 5 - 1).toUInt64).toUInt32 + 1 = ndist
    at bm3 ⊢
  have hnc0 : ((l1.hold >>> (5 : UInt32).toUInt64 >>> (5 : UInt32).toUInt64) &&&
      ((1 : UInt32) <<< 4 - 1).toUInt64).toUInt32.toNat < 2 ^ 4 := mask_lt _ 4 (by decide)
  generalize hnc : ((l1.hold >>> (5 : UInt32).toUInt64 >>> (5 : UInt32).toUInt64) &&&
      ((1 : UInt32) <<< 4 - 1).toUInt64).toUInt32 + 4 = ncode at ⊢
  let S3 : InflateState := { { { S with nlen := nlen } with ndist := ndist } with ncode := ncode }
  have bm4 := bm3.wS cb (S' := S3) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.bind (dropbits_ok 4 (by decide) ?_)
  have hd14 : (l1.bits - (5 : UInt32).toUInt8 - (5 : UInt32).toUInt8 - (4 : UInt32).toUInt8).toNat =
      l1.bits.toNat - 14 := by
    have h5 : (5 : UInt32).toNat = 5 := rfl
    have h4 : (4 : UInt32).toNat = 4 := rfl
    have e1 : (l1.bits - (5 : UInt32).toUInt8).toNat = l1.bits.toNat - 5 := by
      rw [u8_subL _ 5 (by rw [h5]; omega) (by decide), h5]
    have e2 : (l1.bits - (5 : UInt32).toUInt8 - (5 : UInt32).toUInt8).toNat = l1.bits.toNat - 10 := by
      rw [u8_subL _ 5 (by rw [e1, h5]; omega) (by decide), e1, h5]; omega
    rw [u8_subL _ 4 (by rw [e2, h4]; omega) (by decide), e2, h4]; omega
  generalize hl2 : ({ { { l1 with
      hold := l1.hold >>> (5 : UInt32).toUInt64
      bits := l1.bits - (5 : UInt32).toUInt8 } with
      hold := l1.hold >>> (5 : UInt32).toUInt64 >>> (5 : UInt32).toUInt64
      bits := l1.bits - (5 : UInt32).toUInt8 - (5 : UInt32).toUInt8 } with
      hold := l1.hold >>> (5 : UInt32).toUInt64 >>> (5 : UInt32).toUInt64 >>> (4 : UInt32).toUInt64
      bits := l1.bits - (5 : UInt32).toUInt8 - (5 : UInt32).toUInt8 - (4 : UInt32).toUInt8 } : IL) = l2
  have hb2 : l2.bits.toNat < 8 := by rw [← hl2]; show (l1.bits - _ - _ - _).toNat < 8; rw [hd14]; omega
  have bm5 : BM E l2 _ t1 z S3 := bm4.locals (by rw [← hl2]) (by rw [← hl2]) (by rw [← hl2]) (by rw [← hl2])
  have hM2 : IM l2 t1 ≤ M0 := by
    rw [← hM1]; unfold IM
    have : l2.have_ = l1.have_ := by rw [← hl2]
    rw [this, show l2.bits.toNat = l1.bits.toNat - 14 by rw [← hl2]; exact hd14]; omega
  have hnl' : 257 ≤ nlen.toNat ∧ nlen.toNat ≤ 288 := by
    rw [← hnl, add_small (k := 5) 257 (mask_lt _ 5 (by decide)) (by decide) (by decide)]
    have := mask_lt l1.hold 5 (by decide); have : (257 : UInt32).toNat = 257 := rfl
    have : (2 : Nat) ^ (5 : UInt32).toNat = 32 := rfl
    constructor <;> omega
  have hnd' : 1 ≤ ndist.toNat ∧ ndist.toNat ≤ 32 := by
    rw [← hnd, add_small (k := 5) 1 (mask_lt _ 5 (by decide)) (by decide) (by decide)]
    have := mask_lt (l1.hold >>> (5 : UInt32).toUInt64) 5 (by decide); have : (1 : UInt32).toNat = 1 := rfl
    have : (2 : Nat) ^ (5 : UInt32).toNat = 32 := rfl
    constructor <;> omega
  have hnc' : ncode.toNat ≤ 19 := by
    rw [← hnc, add_small (k := 4) 4 hnc0 (by decide) (by decide)]
    have : (2 : Nat) ^ (4 : UInt32).toNat = 16 := rfl
    have : (4 : UInt32).toNat = 4 := rfl
    omega
  -- the check of the counts
  refine SatX.bind (liftEq bm5.sh.ldState ?_)
  dsimp only
  split
  · exact bad_exit cb bm5 hM2 hμ' "too many length or distance symbols" (strIdx 26 (by decide) (by decide) (by decide))
  rename_i hok
  have hn286 : nlen.toNat ≤ 286 ∧ ndist.toNat ≤ 30 := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, UInt32.not_lt, UInt32.le_iff_toNat_le] at hok
    exact ⟨hok.1, hok.2⟩
  let S4 : InflateState := { S3 with «have» := 0 }
  obtain ⟨e4, bm6⟩ := bm5.wS' cb (S' := S4) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with «have» := 0 }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e4 ?_))
  refine SatX.bind (liftEq (a := (.ref (.lens E.b) 0 : WPtr)) rfl ?_)
  -- the code length code lengths
  refine SatX.bind (SatX.mono (clc_loop cb (S0 := S4) (M0 := M0) hnc' ⟨t1, S4, bm6, hM2, hb2, rfl, by
    show (0 : UInt32).toNat ≤ _; exact Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩) ?_)
  rintro r l3 H3 p
  match r, p with
  | .error .leave, p => exact p
  | .ok (), ⟨t3, S5, bm7, hM3, hb3, hS5, hhv5, hlv5⟩ =>
  refine SatX.bind (SatX.mono (clz_loop cb (S0 := S4) ⟨S5, bm7, hS5, by rw [hhv5]; exact hnc', hlv5⟩) ?_)
  rintro r l4 H4 p
  match r, p with
  | .error _, p => exact p.elim
  | .ok (), ⟨hl4, S6, bm8, hS6, hl7⟩ =>
  subst hl4
  -- the code length code
  refine SatX.bind (liftEq (a := (.ref (.codes E.b) 0 : CodePtr)) rfl ?_)
  obtain ⟨e5, bm9⟩ := bm8.wS' cb (S' := { S6 with next := .val (.ref (.codes E.b) 0) })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun s => { s with next := .val (.ref (.codes E.b) 0) }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e5 ?_))
  refine SatX.bind (liftEq (bm9.sh.rdS _) ?_)
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  obtain ⟨e6, bm10⟩ := bm9.wS' cb (S' := { { S6 with next := .val (.ref (.codes E.b) 0) } with
      lencode := .val (.ref (.codes E.b) 0) })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun s => { s with lencode := .val (.ref (.codes E.b) 0) }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e6 ?_))
  let S9 : InflateState := { { { S6 with next := .val (.ref (.codes E.b) 0) } with
      lencode := .val (.ref (.codes E.b) 0) } with lenbits := 7 }
  obtain ⟨e7, bm11⟩ := bm10.wS' cb (S' := S9) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with lenbits := 7 }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e7 ?_))
  refine SatX.bind (liftEq bm11.sh.ldState ?_)
  refine SatX.bind (liftEq (ival_get _ _) ?_)
  refine SatX.bind (liftEq (a := (.ref (.work E.b) 0 : WPtr)) rfl ?_)
  generalize hH9 : withS (withS (withS H4 E.b _) E.b _) E.b S9 = H9 at bm11
  have hcs := bm11.sh.codes
  have hls := bm11.sh.lens
  have hws := bm11.sh.work
  have hS6l : S6.lens = S9.lens := rfl
  obtain ⟨ret, o', lb, codes', work', e, hcs1, hws1, -, -, hok1, herr1⟩ :=
    Inftrees.table_run_rep H9 E.b S9 ZlibNg.Inftrees.CODES 0 19 0 7 bm11.sh.istate hcs hls hws
      (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)
      (fun j hj => by
        have := hl7 (0 + j) (by have : (19 : UInt32).toNat = 19 := rfl; omega)
        rw [UInt16.le_iff_toNat_le] at this
        rw [ite_eq_left_of_eq_true _ _ (eq_self _)]; exact this)
  have e' : (ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.CODES (.ref (.lens E.b) 0) 19
      (.ref (.codes E.b) 0) S9.lenbits (.ref (.work E.b) 0) : M _) H9 =
      .ok ((ret, .ref (.codes E.b) o', lb), withS H9 E.b { S9 with codes := codes', work := work' }) := by
    rw [show S9.lenbits = 7 from rfl]
    unfold C.run at e; exact e
  refine SatX.bind (SatX.lift (Sat.of_eq e' ?_))
  dsimp only
  have bm12 := bm11.wS cb (S' := { S9 with codes := codes', work := work' })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by rw [hws1, ← hws], by rw [hcs1, ← hcs]⟩
  let S10 : InflateState := { S9 with
    codes := codes'
    work := work'
    next := .val (.ref (.codes E.b) o')
    lenbits := lb }
  obtain ⟨e8, bm13⟩ := bm12.wS' cb (S' := S10) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with next := .val (.ref (.codes E.b) o'), lenbits := lb }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e8 ?_))
  have bm13r := bm13.locals (l' := { l4 with ret := ret }) rfl rfl rfl rfl
  have hM3' : IM { l4 with ret := ret } t3 ≤ M0 := hM3
  refine SatX.bind (SatX.modify ?_)
  dsimp only
  split
  · exact bad_exit cb bm13r hM3' hμ' "invalid code lengths set" (strIdx 18 (by decide) (by decide) (by decide))
  rename_i hne
  have h0r : ret = 0 := by simpa using hne
  obtain ⟨-, -, -, -, hct, -, hcodes⟩ := hok1 h0r
  obtain ⟨hla, hop⟩ := hcodes rfl
  rw [mOf_codes, Inftrees.dOf_codes] at hct
  let S11 : InflateState := { S10 with «have» := 0 }
  obtain ⟨e9, bm14⟩ := bm13r.wS' cb (S' := S11) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun s => { s with «have» := 0 }) rfl
  refine SatX.bind (SatX.lift (Sat.of_eq e9 ?_))
  have hS6n : S6.nlen = nlen ∧ S6.ndist = ndist ∧ S6.mode = TABLE := by
    rw [hS6]; exact ⟨rfl, rfl, hm⟩
  have h0 : S0OK E S11 := ⟨by show 257 ≤ S6.nlen.toNat; rw [hS6n.1]; exact hnl'.1,
    by show S6.nlen.toNat ≤ 286; rw [hS6n.1]; exact hn286.1, by show 1 ≤ S6.ndist.toNat; rw [hS6n.2.1]; exact hnd'.1,
    by show S6.ndist.toNat ≤ 30; rw [hS6n.2.1]; exact hn286.2, rfl, ⟨o', hct⟩, hla, hop⟩
  -- the code lengths
  refine SatX.bind (SatX.mono (tl_loop cb h0 ⟨t3, S11, bm14, hM3', hb3, rfl, by
    show (0 : UInt32).toNat ≤ _; exact Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩) ?_)
  rintro r l5 H5 p
  match r, p with
  | .error .leave, p => exact p
  | .ok (), p =>
  exact tb_tail cb hμ' h0 hS6n.2.2 p

end ZlibNgF.Proof.InfbackLoop
