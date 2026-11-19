import ZlibNgF.Proof.«inflate.c.stored-modes»
import ZlibNgF.Proof.«inftrees.c.facts»

/-!
# The modes `TABLE`, `LENLENS` of `inflate` (`ZlibNgF`)

These modes read the counts of a dynamic block header and the code lengths of the code length code into the state's
`lens`, and build that code's table in the state's `codes` with `zng_inflate_table` (`tableFacts`). Several
consecutive stores into the state pass through records that the invariant does not describe (the `have` counter is
advanced before the length it counts is stored; `distcode` is moved into `codes` before `lencode`), so they are
followed on the heap as one store of the final record.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view ModeOK DecodeMode upd_upd)
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq St Touch)
open ZlibNgF.Proof.InflateTab (TabAt CodeTable)

theorem rank_TABLE : rank TABLE = 15 := by decide
theorem rank_LENLENS : rank LENLENS = 17 := by decide
theorem rank_CODELENS : rank CODELENS = 16 := by decide

/-! ## Stores into the state on the heap -/

/-- The heap with the state of block `b` replaced by `S`. -/
def withS (H : Heap) (b : Nat) (S : InflateState) : Heap := { H with istates := upd H.istates b (some S) }

theorem istates_of {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) : H.istates b = some S := by
  unfold Heap.istate at hs; split at hs <;> simp_all

theorem istate_withS {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (S' : InflateState) :
    (withS H b S').istate b = some S' := by
  unfold Heap.istate at hs ⊢
  simp only [withS]
  split at hs <;> simp_all

theorem withS_withS (H : Heap) (b : Nat) (S1 S2 : InflateState) : withS (withS H b S1) b S2 = withS H b S2 := by
  simp only [withS, upd_upd]

theorem wrS_app {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (f : InflateState → InflateState) :
    ZlibNg.Inflate.wrS (some b) f H = .ok ((), withS H b (f S)) := by
  simp [ZlibNg.Inflate.wrS, bind_app, InflateInv.ldState_app hs, stState, hs, withS]

theorem wrS_withS {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (S1 : InflateState)
    (f : InflateState → InflateState) :
    ZlibNg.Inflate.wrS (some b) f (withS H b S1) = .ok ((), withS H b (f S1)) := by
  rw [wrS_app (istate_withS hs S1), withS_withS]

theorem ldState_withS {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (S1 : InflateState) :
    C.ldState (some b) (withS H b S1) = .ok (S1, withS H b S1) := InflateInv.ldState_app (istate_withS hs S1)

theorem rdS_withS {α : Type} {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (S1 : InflateState)
    (g : InflateState → α) : ZlibNg.Inflate.rdS (some b) g (withS H b S1) = .ok (g S1, withS H b S1) := by
  simp [ZlibNg.Inflate.rdS, bind_app, ldState_withS hs S1]

theorem getWords_withS {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (S1 : InflateState) :
    Space.get (withS H b S1) (WRef.lens b) = some S1.lens := by
  show Heap.getWords _ _ = _
  simp only [Heap.getWords, istate_withS hs S1, Option.map_some]

theorem addLens_withS {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (S1 : InflateState)
    {k : Nat} (hk : k ≤ S1.lens.size) :
    Ptr.add (.ref (.lens b) 0 : WPtr) (Int.ofNat k) (withS H b S1) = .ok (.ref (.lens b) k, withS H b S1) := by
  have hc : 0 ≤ S1.lens.size ∧ 0 ≤ ((0 : Nat) : Int) + Int.ofNat k ∧ ((0 : Nat) : Int) + Int.ofNat k ≤ (S1.lens.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [Ptr.add, getWords_withS hs S1, hc, and_self, ↓reduceIte]
  congr 2
  simp

theorem storeLens_withS {H : Heap} {b : Nat} {S : InflateState} (hs : H.istate b = some S) (S1 : InflateState)
    {k : Nat} (hk : k < S1.lens.size) (v : UInt16) :
    Ptr.store (.ref (.lens b) k : WPtr) v (withS H b S1) =
      .ok ((), withS H b { S1 with lens := S1.lens.set! k v }) := by
  have hg := getWords_withS hs S1
  have hro : Space.ro (withS H b S1) (WRef.lens b) = false := rfl
  simp only [Ptr.store, hg, hro, hk, Bool.false_eq_true, ↓reduceIte]
  rw [Space.modify_eq _ _ _ _ hg hro]
  show Except.ok ((), Heap.putWords _ _ _) = _
  simp only [Heap.putWords, withS, upd_same, upd_upd]

/-- `LI` after a store of `f S` into the state that keeps the invariant. -/
theorem LI.withS {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    (S' : InflateState)
    (keep : ∀ al z, Core H (some E.i) z E.b (view S) al → Core H (some E.i) z E.b (view S') al)
    (hh : S'.head = S.head) : LI E l (withS H E.b S') z S' := by
  obtain ⟨_, H', e, hl⟩ := li.wrS (fun _ => S') keep hh
  rw [wrS_app li.hs] at e
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
  exact hl

/-! ## The code length order -/

theorem order_lt : ∀ j, j < 19 → (order[j]!).toNat < 19 := by decide
theorem order_inj : ∀ i, i < 19 → ∀ j, j < 19 → order[i]! = order[j]! → i = j := by decide
theorem order_surj : ∀ k, k < 19 → ∃ j, j < 19 ∧ (order[j]!).toNat = k := by decide

theorem aget_order {H : Heap} {i : Nat} (hi : i < 19) :
    ZlibNg.Inftrees.aget order i H = .ok (order[i]!, H) := by
  have hs : i < order.size := hi
  simp [ZlibNg.Inftrees.aget, hs]

theorem bits3_le (x : UInt64) : (x &&& ((1 : UInt32) <<< (3 : UInt32) - 1).toUInt64).toUInt16 ≤ 7 := by
  have e : ((1 : UInt32) <<< (3 : UInt32) - 1).toUInt64 = 7 := by decide
  rw [e, UInt16.le_iff_toNat_le, UInt64.toNat_toUInt16, UInt64.toNat_and]
  have : x.toNat &&& (7 : UInt64).toNat ≤ 7 := Nat.and_le_right
  show _ ≤ 7
  exact Nat.le_trans (Nat.mod_le _ _) this

/-! ## The mode clauses of `LENLENS` -/

theorem modeOK_LL (b : Nat) (v : InflateInv.MView) (hm : v.mode = LENLENS)
    (h : v.ncode ≤ 19 ∧ (257 ≤ v.nlen.toNat ∧ v.nlen ≤ 286) ∧ (1 ≤ v.ndist.toNat ∧ v.ndist ≤ 30) ∧
      ∀ j, j < v.«have».toNat → v.lens[(order[j]!).toNat]! ≤ 7) :
    ModeOK b v where
  lenlens := fun _ => h
  codelens := fun e => absurd (hm.symm.trans e) (by decide)
  decode := fun e => by
    rw [hm] at e; rcases e with e | e | e | e | e | e | e <;> exact absurd e (by decide)
  extra := fun e => by rw [hm] at e; rcases e with e | e <;> exact absurd e (by decide)
  offset := fun e => by rw [hm] at e; rcases e with e | e <;> exact absurd e (by decide)

/-- A store of the counter and the lengths in `LENLENS` that keeps the lengths read in range. -/
theorem core_LL {H : Heap} {i b : Nat} {z : ZStream} {al : InflateAllocs} {S : InflateState} (hv : UInt32)
    (L : Array UInt16) (c : Core H (some i) z b (view S) al) (hm : S.mode = LENLENS) (hL : L.size = S.lens.size)
    (hk : ∀ j, j < hv.toNat → L[(order[j]!).toNat]! ≤ 7) :
    Core H (some i) z b (view { S with «have» := hv, lens := L }) al := by
  have hll := c.modes.lenlens hm
  exact { c with
    lens_size := by show L.size = 320; rw [hL]; exact c.lens_size
    modes := modeOK_LL b _ hm ⟨hll.1, hll.2.1, hll.2.2.1, hk⟩
    extraLen := fun e => absurd (hm.symm.trans e) (by decide) }

theorem LI.lensSize {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    S.lens.size = 320 := by
  obtain ⟨al, -, c⟩ := li.core; exact c.lens_size

/-- The state of `LENLENS` during its loops, from the locals `l0` at entry. -/
def LLs (E : Env) (l0 : IL) (z : ZStream) (l : IL) (H : Heap) : Prop :=
  ∃ S, LI E l H z S ∧ S.mode = LENLENS ∧ l.left = l0.left ∧
    8 * l.have_.toNat + l.bits.toNat ≤ 8 * l0.have_.toNat + l0.bits.toNat

def LLrank (E : Env) (_l : IL) (H : Heap) : Nat :=
  match H.istate E.b with | some S => 19 - S.«have».toNat | none => 0

theorem have_succ {v : UInt32} (h : v.toNat < 19) : (v + 1).toNat = v.toNat + 1 := by
  rw [UInt32.toNat_add]; show (v.toNat + 1) % 4294967296 = _; omega

theorem set16_ne (a : Array UInt16) (o j : Nat) (v : UInt16) (hj : j ≠ o) : (a.set! o v)[j]! = a[j]! := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [Ne.symm hj]

theorem set16_eq (a : Array UInt16) (o : Nat) (v : UInt16) (ho : o < a.size) : (a.set! o v)[o]! = v := by
  simp [Array.set!_eq_setIfInBounds, ho]

/-- The lengths read so far stay in range after `lens[order[have]] = v; have++` with `v ≤ 7`. -/
theorem ll_keep {L : Array UInt16} {hv : UInt32} (hL : L.size = 320) (h19 : hv.toNat < 19)
    (hk : ∀ j, j < hv.toNat → L[(order[j]!).toNat]! ≤ 7) (v : UInt16) (hvle : v ≤ 7) :
    ∀ j, j < (hv + 1).toNat → (L.set! (order[hv.toNat]!).toNat v)[(order[j]!).toNat]! ≤ 7 := by
  intro j hj
  rw [have_succ h19] at hj
  by_cases e : j = hv.toNat
  · subst e
    rw [set16_eq _ _ _ (by have := order_lt _ h19; omega)]; exact hvle
  · have hne : (order[j]!).toNat ≠ (order[hv.toNat]!).toNat := by
      intro e'; exact e (order_inj j (by omega) _ h19 (UInt16.toNat_inj.mp e'))
    rw [set16_ne _ _ _ _ hne]; exact hk j (by omega)

/-- The state of `LENLENS` after its loops: all 19 lengths are read. -/
def LLd (E : Env) (l0 : IL) (z : ZStream) (l : IL) (H : Heap) : Prop :=
  ∃ S, LI E l H z S ∧ S.mode = LENLENS ∧ l.left = l0.left ∧
    8 * l.have_.toNat + l.bits.toNat ≤ 8 * l0.have_.toNat + l0.bits.toNat ∧ 19 ≤ S.«have».toNat

theorem lens19 {L : Array UInt16} {hv : UInt32} (h19 : 19 ≤ hv.toNat)
    (hk : ∀ j, j < hv.toNat → L[(order[j]!).toNat]! ≤ 7) : ∀ j, j < 19 → (L[0 + j]!).toNat ≤ 7 := by
  intro j hj
  obtain ⟨j', hj', e⟩ := order_surj j hj
  have := hk j' (by omega)
  rw [e] at this
  rw [Nat.zero_add]; exact UInt16.le_iff_toNat_le.mp this

theorem modeOK_CL (b : Nat) (v : InflateInv.MView) (hm : v.mode = CODELENS)
    (h : (257 ≤ v.nlen.toNat ∧ v.nlen ≤ 286) ∧ (1 ≤ v.ndist.toNat ∧ v.ndist ≤ 30) ∧
      (∀ j, j < v.«have».toNat → v.lens[j]! ≤ 15) ∧
      TabAt b v.codes v.lencode v.lenbits 25 false) :
    ModeOK b v where
  lenlens := fun e => absurd (hm.symm.trans e) (by decide)
  codelens := fun _ => h
  decode := fun e => by
    rw [hm] at e; rcases e with e | e | e | e | e | e | e <;> exact absurd e (by decide)
  extra := fun e => by rw [hm] at e; rcases e with e | e <;> exact absurd e (by decide)
  offset := fun e => by rw [hm] at e; rcases e with e | e <;> exact absurd e (by decide)

/-- The state after the table of the code length code is built (in `LENLENS`, before the mode changes). -/
theorem core_LLtab {H : Heap} {i b : Nat} {z : ZStream} {al : InflateAllocs} {S : InflateState}
    (c : Core H (some i) z b (view S) al) (hm : S.mode = LENLENS) {C' : Array Code} {W' : Array UInt16}
    (cs : C'.size = ENOUGH) (ws : W'.size = 288) {o : Nat} (ho : o ≤ ENOUGH) (lb : UInt32) :
    Core H (some i) z b (view { S with
      next := .val (.ref (.codes b) o)
      distcode := .val (.ref (.codes b) 0)
      lencode := .val (.ref (.codes b) 0)
      lenbits := lb
      codes := C'
      work := W' }) al :=
  { c with
    codes_size := cs
    work_size := ws
    lencode := ⟨_, rfl, Or.inl ⟨0, rfl, by decide⟩⟩
    distcode := ⟨_, rfl, Or.inl ⟨0, rfl, by decide⟩⟩
    next := ⟨o, rfl, ho⟩
    tables := Or.inl ⟨rfl, 0, rfl, by decide⟩
    modes := modeOK_LL b _ hm (c.modes.lenlens hm)
    extraLen := fun e => absurd (hm.symm.trans e) (by decide) }

/-- The state entering `CODELENS`. -/
theorem core_CL {H : Heap} {i b : Nat} {z : ZStream} {al : InflateAllocs} {S : InflateState}
    (c : Core H (some i) z b (view S) al) (hm : S.mode = LENLENS) {C' : Array Code} {W' : Array UInt16}
    (cs : C'.size = ENOUGH) (ws : W'.size = 288) {o : Nat} (ho : o ≤ ENOUGH) (lb : UInt32)
    (ht : CodeTable C' 0 o lb.toNat 25 false) :
    Core H (some i) z b (view { S with
      next := .val (.ref (.codes b) o)
      distcode := .val (.ref (.codes b) 0)
      lencode := .val (.ref (.codes b) 0)
      lenbits := lb
      codes := C'
      work := W'
      «have» := 0
      mode := CODELENS }) al := by
  have hll := c.modes.lenlens hm
  exact { c with
    mode_lo := by show HEAD ≤ CODELENS; decide
    mode_hi := by show CODELENS ≤ SYNC; decide
    codes_size := cs
    work_size := ws
    lencode := ⟨_, rfl, Or.inl ⟨0, rfl, by decide⟩⟩
    distcode := ⟨_, rfl, Or.inl ⟨0, rfl, by decide⟩⟩
    next := ⟨o, rfl, ho⟩
    tables := Or.inl ⟨rfl, 0, rfl, by decide⟩
    modes := modeOK_CL b _ rfl ⟨hll.2.1, hll.2.2.1, fun j hj => absurd hj (Nat.not_lt_zero _),
      Or.inl ⟨0, o, rfl, ht⟩⟩
    extraLen := fun e => absurd (show CODELENS = EXTRA from e) (by decide) }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem run_LENLENS (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_CODELENS (·.mode = CODELENS)) :
    ModeRun E inflate_LENLENS (·.mode = LENLENS) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 17 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_LENLENS] at hμ
  unfold inflate_LENLENS
  refine SatX.bind (SatX.lift_eq (a := (.ref (.lens E.b) 0 : WPtr)) rfl ?_)
  dsimp only
  have hb39 : l.bits.toNat ≤ 39 := li.bits
  refine SatX.bind (SatX.mono (P := fun r l' H' => match r with
      | .ok () => LLs E l z l' H'
      | .error e => Post E m (.error e) l' H') ?_ ?_)
  · unfold xwhile
    refine xwhileBrk_rank (LLs E l z) (LLrank E) _ ?_ ⟨S, li, hm, rfl, Nat.le_refl _⟩
      (by unfold LLrank; rw [li.hs]; dsimp only; unfold fuel; omega)
    rintro l1 H1 ⟨S1, li1, hm1, hl1, hb1⟩
    refine SatX.bind (SatX.lift_eq li1.ldState ?_)
    refine SatX.pure ?_
    by_cases hlt : S1.«have» < S1.ncode
    · simp only [hlt, decide_true]
      obtain ⟨_, -, c1⟩ := li1.core
      have hll := c1.modes.lenlens hm1
      have hlt19 : S1.«have».toNat < 19 := by
        have := hll.1; rw [UInt32.le_iff_toNat_le] at this; rw [UInt32.lt_iff_toNat_lt] at hlt
        show _ < 19; have : S1.ncode.toNat ≤ 19 := this; omega
      refine SatX.bind (SatX.bind (SatX.mono (needbits_ok eo li1 3 (by decide)) ?_))
      rintro r l2 H2 ⟨rfl, li2, p2, hb2, hr⟩
      match r, hr with
      | .error e, hr =>
        obtain ⟨rfl, -⟩ := hr
        exact ⟨z, S1, li2⟩
      | .ok (), hr =>
        have hs1 := li2.hs
        have hsz := li2.lensSize
        refine SatX.bind (SatX.lift_eq (li2.rdS (·.«have»)) ?_)
        refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app hs1 _) ?_))
        refine SatX.bind (SatX.lift_eq (aget_order hlt19) ?_)
        refine SatX.bind (bits_ok 3 (by decide) ?_)
        have hk : (order[S1.«have».toNat]!).toNat < 19 := order_lt _ hlt19
        refine SatX.bind (SatX.lift_eq (addLens_withS hs1 _ (k := (order[S1.«have».toNat]!).toNat)
          (by show _ ≤ S1.lens.size; omega)) ?_)
        refine SatX.bind (SatX.lift (Sat.of_eq (storeLens_withS hs1 _ (by show _ < S1.lens.size; omega) _) ?_))
        refine dropbits_ok 3 (by decide) (SatX.pure ?_)
        have hb3 : (l2.bits - (3 : UInt32).toUInt8).toNat = l2.bits.toNat - 3 := by
          rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; exact hr)]; rfl
        refine ⟨⟨_, (li2.withS _ (fun _ _ c => core_LL (S1.«have» + 1) _ c hm1 (by simp)
            (ll_keep hsz hlt19 hll.2.2.2 _ (bits3_le _))) rfl).setBits rfl rfl rfl rfl rfl ?_, hm1, ?_, ?_⟩, ?_⟩
        · rw [UInt8.le_iff_toNat_le, hb3]; have := li2.bits; rw [UInt8.le_iff_toNat_le] at this; omega
        · show l2.left = l.left; rw [p2.1]; exact hl1
        · show 8 * l2.have_.toNat + (l2.bits - (3 : UInt32).toUInt8).toNat ≤ _
          rw [hb3]; have := p2.2; omega
        · unfold LLrank; rw [istate_withS hs1, li1.hs]; show 19 - (S1.«have» + 1).toNat < 19 - S1.«have».toNat
          rw [have_succ hlt19]; omega
    · simp only [hlt, decide_false]
      exact ⟨S1, li1, hm1, hl1, hb1⟩
  rintro r l1 H1 p
  match r, p with
  | .error e, p => exact p
  | .ok (), ⟨S1, li1, hm1, hl1, hb1⟩ =>
  dsimp only
  refine SatX.bind (SatX.mono (P := fun r l' H' => match r with
      | .ok () => LLd E l z l' H'
      | .error e => Post E m (.error e) l' H') ?_ ?_)
  · unfold xwhile
    refine xwhileBrk_rank (LLs E l z) (LLrank E) _ ?_ ⟨S1, li1, hm1, hl1, hb1⟩
      (by unfold LLrank; rw [li1.hs]; dsimp only; unfold fuel; omega)
    rintro l2 H2 ⟨S2, li2, hm2, hl2, hb2⟩
    refine SatX.bind (SatX.lift_eq (li2.rdS (·.«have»)) ?_)
    refine SatX.pure ?_
    by_cases hlt : S2.«have» < 19
    · simp only [hlt, decide_true]
      have hlt19 : S2.«have».toNat < 19 := UInt32.lt_iff_toNat_lt.mp hlt
      obtain ⟨_, -, c2⟩ := li2.core
      have hll := c2.modes.lenlens hm2
      have hs2 := li2.hs
      have hsz := li2.lensSize
      refine SatX.bind (SatX.bind (SatX.lift_eq (li2.rdS (·.«have»)) ?_))
      refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app hs2 _) ?_))
      refine SatX.bind (SatX.lift_eq (aget_order hlt19) ?_)
      have hk : (order[S2.«have».toNat]!).toNat < 19 := order_lt _ hlt19
      refine SatX.bind (SatX.lift_eq (addLens_withS hs2 _ (k := (order[S2.«have».toNat]!).toNat)
        (by show _ ≤ S2.lens.size; omega)) ?_)
      refine SatX.lift (Sat.of_eq (storeLens_withS hs2 _ (by show _ < S2.lens.size; omega) _) (SatX.pure ?_))
      refine ⟨⟨_, li2.withS _ (fun _ _ c => core_LL (S := S2) (S2.«have» + 1) (S2.lens.set! (order[S2.«have».toNat]!).toNat 0) c hm2 (by simp)
          (ll_keep hsz hlt19 hll.2.2.2 _ (by decide))) rfl, hm2, hl2, hb2⟩, ?_⟩
      unfold LLrank; rw [istate_withS hs2, li2.hs]; show 19 - (S2.«have» + 1).toNat < 19 - S2.«have».toNat
      rw [have_succ hlt19]; omega
    · simp only [hlt, decide_false]
      exact ⟨S2, li2, hm2, hl2, hb2, by
        have := UInt32.not_lt.mp hlt; rw [UInt32.le_iff_toNat_le] at this; exact this⟩
  rintro r l2 H2 p
  match r, p with
  | .error e, p => exact p
  | .ok (), ⟨S2, li2, hm2, hl2, hb2, h19⟩ =>
  dsimp only
  have hs2 := li2.hs
  obtain ⟨al, -, c2⟩ := li2.core
  have hll := c2.modes.lenlens hm2
  refine SatX.bind (SatX.lift_eq (a := (.ref (.codes E.b) 0 : CodePtr)) rfl ?_)
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app hs2 _) ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs2 _ _) ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs2 _ _) ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs2 _ _) ?_))
  refine SatX.bind (SatX.lift_eq (ldState_withS hs2 _) ?_)
  refine SatX.bind (SatX.lift_eq (a := (.ref (.codes E.b) 0 : CodePtr)) rfl ?_)
  refine SatX.bind (SatX.lift_eq (a := (.ref (.work E.b) 0 : WPtr)) rfl ?_)
  let S4 : InflateState := { S2 with
    next := .val (.ref (.codes E.b) 0)
    distcode := .val (.ref (.codes E.b) 0)
    lencode := .val (.ref (.codes E.b) 0)
    lenbits := 7 }
  obtain ⟨ret, o', lb, codes', work', e, hcs, hws, -, -, hok, herr⟩ :=
    Inftrees.table_run (withS H2 E.b S4) E.b S4 ZlibNg.Inftrees.CODES 0 19 0 7 (istate_withS hs2 _)
      c2.codes_size c2.lens_size c2.work_size (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)
      (fun j hj => by show _ ≤ 7; exact lens19 h19 hll.2.2.2 j hj)
  have e' : (ZlibNg.Inftrees.zng_inflate_table ZlibNg.Inftrees.CODES (.ref (.lens E.b) 0) 19
      (.ref (.codes E.b) 0) 7 (.ref (.work E.b) 0) : M _) (withS H2 E.b S4) =
      .ok ((ret, .ref (.codes E.b) o', lb), withS H2 E.b { S4 with codes := codes', work := work' }) := by
    unfold C.run at e; rw [e]; exact congrArg (fun H' => Except.ok (_, H')) (withS_withS H2 E.b S4 _)
  refine SatX.bind (SatX.lift (Sat.of_eq e' ?_))
  refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs2 _ _) ?_))
  have hμ2 : 32 * (8 * l2.have_.toNat + l2.bits.toNat + l2.left.toNat) + 17 ≤ m := by rw [hl2]; omega
  refine SatX.bind (SatX.modify (SatX.ite (fun hne => ?_) (fun hne => ?_)))
  · have h0 : ret ≠ 0 := by simpa using hne
    obtain rfl := herr h0
    exact bad_ok ((li2.withS { S4 with
        codes := codes'
        work := work'
        next := .val (.ref (.codes E.b) 0)
        lenbits := lb } (fun _ _ c => core_LLtab (o := 0) c hm2 hcs hws (by decide) lb) rfl).locals
        (l' := { l2 with ret := ret }) rfl rfl rfl rfl rfl rfl)
        (by show 32 * (8 * l2.have_.toNat + l2.bits.toNat + l2.left.toNat) < m; omega) "invalid code lengths set" (strIdx 18 (by decide) (by decide) (by decide))
  · have h0 : ret = 0 := by simpa using hne
    obtain ⟨ho1, ho2, -, -, hct⟩ := hok h0
    have hct' : CodeTable codes' 0 o' lb.toNat 25 false := hct
    refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs2 _ _) ?_))
    refine SatX.bind (SatX.lift (Sat.of_eq (wrS_withS hs2 _ _) ?_))
    refine hX _ _ z _ ((li2.withS { S4 with
        codes := codes'
        work := work'
        next := .val (.ref (.codes E.b) o')
        lenbits := lb
        «have» := 0
        mode := CODELENS } (fun _ _ c => core_CL c hm2 hcs hws
          (by have : (1332 : Nat) ≤ ENOUGH := by decide
              have e : (if ZlibNg.Inftrees.CODES = ZlibNg.Inftrees.DISTS then 592 else 1332) = 1332 := by decide
              omega) lb hct') rfl).locals
        (l' := { l2 with ret := ret }) rfl rfl rfl rfl rfl rfl) rfl m ?_
    unfold μ; dsimp only; rw [rank_CODELENS]; omega

/-! ## `TABLE` -/

theorem drop_toNat {b : UInt8} {n : UInt32} (hn : n.toNat < 256) (hb : n.toNat ≤ b.toNat) :
    (b - n.toUInt8).toNat = b.toNat - n.toNat := by
  have e : n.toUInt8.toNat = n.toNat := by rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt hn
  rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, e]; exact hb), e]

/-- `DROPBITS(n)` keeps `LI` and takes `n` bits off. -/
theorem LI.drop {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) (n : UInt32)
    (hn : n.toNat < 256) (hb : n.toNat ≤ l.bits.toNat) :
    LI E { l with hold := l.hold >>> n.toUInt64, bits := l.bits - n.toUInt8 } H z S :=
  li.setBits rfl rfl rfl rfl rfl (by
    rw [UInt8.le_iff_toNat_le, drop_toNat hn hb]; have := li.bits; rw [UInt8.le_iff_toNat_le] at this
    show _ ≤ 39; have : l.bits.toNat ≤ 39 := this; omega)

theorem bits4_le (x : UInt64) : (x &&& ((1 : UInt32) <<< (4 : UInt32) - 1).toUInt64).toUInt32 + 4 ≤ 19 := by
  have e : ((1 : UInt32) <<< (4 : UInt32) - 1).toUInt64 = 15 := by decide
  rw [e]
  have h1 : (x &&& 15).toNat ≤ 15 := by rw [UInt64.toNat_and]; exact Nat.and_le_right
  have h2 : (x &&& 15).toUInt32.toNat ≤ 15 := by rw [UInt64.toNat_toUInt32]; exact Nat.le_trans (Nat.mod_le _ _) h1
  rw [UInt32.le_iff_toNat_le, UInt32.toNat_add]
  show _ % 4294967296 ≤ 19
  have : (4 : UInt32).toNat = 4 := rfl
  omega

theorem bits5_ge (x : UInt64) (k : UInt32) (hk : k.toNat ≤ 257) :
    k.toNat ≤ ((x &&& ((1 : UInt32) <<< (5 : UInt32) - 1).toUInt64).toUInt32 + k).toNat := by
  rw [UInt32.toNat_add]
  have h1 : (x &&& ((1 : UInt32) <<< (5 : UInt32) - 1).toUInt64).toUInt32.toNat ≤ 31 := by
    have e : ((1 : UInt32) <<< (5 : UInt32) - 1).toUInt64 = 31 := by decide
    rw [e, UInt64.toNat_toUInt32, UInt64.toNat_and]
    have : x.toNat &&& (31 : UInt64).toNat ≤ 31 := Nat.and_le_right
    exact Nat.le_trans (Nat.mod_le _ _) this
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- A store into the state in a mode outside `LENLENS .. LIT` other than `EXTRA` that keeps the shape. -/
theorem core_quiet {H : Heap} {i b : Nat} {z : ZStream} {al : InflateAllocs} {S : InflateState}
    (c : Core H (some i) z b (view S) al) (hq : S.mode < LENLENS ∨ LIT < S.mode) (hx : S.mode ≠ EXTRA)
    (S' : InflateState) (e : view S' = { view S with
      ncode := S'.ncode
      nlen := S'.nlen
      ndist := S'.ndist
      «have» := S'.«have» }) : Core H (some i) z b (view S') al := by
  rw [e]
  exact { c with
    modes := ModeOK.quiet _ _ hq
    extraLen := fun e' => absurd e' hx }

theorem run_TABLE (E : Env) (eo : EnvOK E) (hX : ModeRun E inflate_LENLENS (·.mode = LENLENS)) :
    ModeRun E inflate_TABLE (·.mode = TABLE) := by
  intro l H z S li hm m hμ
  have hμ' : 32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + 15 ≤ m := by
    unfold μ at hμ; rwa [hm, rank_TABLE] at hμ
  have hq : S.mode < LENLENS ∨ LIT < S.mode := Or.inl (by rw [hm]; decide)
  have hx : S.mode ≠ EXTRA := by rw [hm]; decide
  unfold inflate_TABLE
  refine needbits_then eo li 14 (by decide) ?_
  intro l1 li1 h14 hleft hT
  have h14' : 14 ≤ l1.bits.toNat := h14
  refine SatX.bind (bits_ok 5 (by decide) ?_)
  refine SatX.bind (SatX.lift (Sat.mono (li1.wrS _ (fun _ _ c => core_quiet c hq hx _ rfl) rfl) ?_))
  intro _ H2 li2
  refine SatX.bind (dropbits_ok 5 (by decide) ?_)
  have li3 := li2.drop 5 (by decide) (by show 5 ≤ _; omega)
  refine SatX.bind (bits_ok 5 (by decide) ?_)
  refine SatX.bind (SatX.lift (Sat.mono (li3.wrS _ (fun _ _ c => core_quiet c hq hx _ rfl) rfl) ?_))
  intro _ H4 li4
  refine SatX.bind (dropbits_ok 5 (by decide) ?_)
  have hb3 : (l1.bits - (5 : UInt32).toUInt8).toNat = l1.bits.toNat - 5 := drop_toNat (by decide) (by show 5 ≤ _; omega)
  have li5 := li4.drop 5 (by decide) (by show 5 ≤ (l1.bits - (5 : UInt32).toUInt8).toNat; omega)
  refine SatX.bind (bits_ok 4 (by decide) ?_)
  refine SatX.bind (SatX.lift (Sat.mono (li5.wrS _ (fun _ _ c => core_quiet c hq hx _ rfl) rfl) ?_))
  intro _ H6 li6
  refine SatX.bind (dropbits_ok 4 (by decide) ?_)
  have hb5 : ((l1.bits - (5 : UInt32).toUInt8) - (5 : UInt32).toUInt8).toNat = l1.bits.toNat - 10 :=
    by rw [drop_toNat (by decide) (by show 5 ≤ (l1.bits - (5 : UInt32).toUInt8).toNat; omega), hb3]; rfl
  have li7 := li6.drop 4 (by decide) (by show 4 ≤ _; rw [hb5]; omega)
  have hb7 : (((l1.bits - (5 : UInt32).toUInt8) - (5 : UInt32).toUInt8) - (4 : UInt32).toUInt8).toNat =
      l1.bits.toNat - 14 := by
    rw [drop_toNat (by decide) (by show 4 ≤ _; rw [hb5]; omega), hb5]; rfl
  have hT' : 8 * l1.have_.toNat + l1.bits.toNat = 8 * l.have_.toNat + l.bits.toNat := hT
  have hl' : l1.left = l.left := hleft
  refine SatX.bind (SatX.lift_eq li7.ldState (SatX.ite (fun hbad => ?_) (fun hok => ?_)))
  · exact bad_ok li7 (by
      show 32 * (8 * l1.have_.toNat + (((l1.bits - (5 : UInt32).toUInt8) - (5 : UInt32).toUInt8) -
        (4 : UInt32).toUInt8).toNat + l1.left.toNat) < m
      rw [hb7, hl']; omega) "too many length or distance symbols" (strIdx 26 (by decide) (by decide) (by decide))
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, UInt32.not_lt] at hok
    refine SatX.bind (SatX.lift (Sat.mono (li7.wrS _ (fun _ _ c => core_quiet c hq hx _ rfl) rfl) ?_))
    intro _ H8 li8
    refine SatX.bind (SatX.lift (Sat.mono (li8.wrS (fun s => { s with mode := LENLENS }) (fun _ _ c => { c with
      mode_lo := by show HEAD ≤ LENLENS; decide
      mode_hi := by show LENLENS ≤ SYNC; decide
      modes := modeOK_LL _ _ rfl ⟨bits4_le _, ⟨bits5_ge _ 257 (by decide), hok.1⟩, ⟨bits5_ge _ 1 (by decide), hok.2⟩,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      extraLen := fun e => absurd (show LENLENS = EXTRA from e) (by decide) }) rfl) ?_))
    intro _ H9 li9
    refine hX _ _ _ _ li9 rfl m ?_
    unfold μ
    show 32 * (8 * l1.have_.toNat + (((l1.bits - (5 : UInt32).toUInt8) - (5 : UInt32).toUInt8) -
        (4 : UInt32).toUInt8).toNat + l1.left.toNat) + rank LENLENS ≤ m
    rw [hb7, hl', rank_LENLENS]; omega

end ZlibNgF.Proof.InflateLoop
