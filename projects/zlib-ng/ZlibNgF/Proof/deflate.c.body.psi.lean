import ZlibNgF.Proof.«deflate.c.body.run»
import ZlibNgF.Proof.«trees.c.owed»

/-!
# `deflate`: the potential across a call (`ZlibNgF`)

The accounting of `DeflatePsi.psi` through the parts of a `deflate` call that entered at heap `h` with potential `P`
(`psi flush` of the state at entry) on stream `i`, state block `b`:

* `Bud f P e d h i b H`: at `H`, `psiS f` of the state plus the bytes produced since `h` plus `e` is at most `P` plus
  `G2` per input byte consumed plus `d` (a debt: the `2^18` of a last block before `FINISH_STATE` releases it);
* `EndOk f P h i b H`: at the end, `psi f` plus the bytes produced is at most `P` plus `G2` per input byte consumed,
  plus the marker `markK f` when the output is full (the `K` of `GzWriteNeeds.CallOk`).

`G2 = 2 G`: `G` per byte pays the strategy's potential (`PsiPost`), the other `G` the flush marker that `deflate` emits
after `block_done` when the call consumed input (with no input at entry the marker owed at entry pays it).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflatePsi
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-- The raise per input byte of a whole call. -/
def G2 : Nat := 2 * G

theorem G2_le : G2 ≤ 2 ^ 28 := by decide

/-- The budget at `H` (see the module comment). -/
def Bud (f : Int32) (P e d : Nat) (h : Heap) (i b : Nat) (H : Heap) : Prop :=
  ∀ st, H.dstate b = some st → psiS f st + (aOut h i - aOut H i) + e ≤ P + G2 * (aIn h i - aIn H i) + d

/-- The end of a call (see the module comment). -/
def EndOk (f : Int32) (P : Nat) (h : Heap) (i b : Nat) (H : Heap) : Prop :=
  ∀ st, H.dstate b = some st →
    psi f st + (aOut h i - aOut H i) ≤ P + G2 * (aIn h i - aIn H i) + (if aOut H i = 0 then markK f else 0)

/-! ## The marker -/

theorem mark_le_markK (f : Int32) (st : DeflateState) : mark f st ≤ markK f := by
  unfold mark; split <;> omega

theorem markK_le5 (f : Int32) : markK f ≤ 5 := markK_le f

theorem markK_le_G (f : Int32) : markK f ≤ G := Nat.le_trans (markK_le f) (by decide)

/-- No marker owed in `FINISH_STATE`. -/
theorem mark_fin {f : Int32} {st : DeflateState} (h : st.status = FINISH_STATE) : mark f st = 0 := by
  unfold mark; exact ite_eq_right fun x => x.1 h

/-- `markK Z_FINISH = 0`. -/
theorem markK_finish : markK Z_FINISH = 0 := by decide

/-! ## Moving the budget -/

theorem Bud.mono {f : Int32} {P e d e' d' : Nat} {h H : Heap} {i b : Nat} (B : Bud f P e d h i b H)
    (he : e' + d ≤ e + d') : Bud f P e' d' h i b H := fun st hs => by
  have := B st hs; omega

/-- A step that keeps the stream's counts and changes `psiS` by at most `e + d' - e' - d`. -/
theorem Bud.step {f : Int32} {P e d e' d' : Nat} {h H H' : Heap} {i b : Nat} (B : Bud f P e d h i b H)
    (hs : ∃ st, H.dstate b = some st) (ea : aIn H' i = aIn H i) (eo : aOut H' i = aOut H i)
    (S : ∀ st st', H.dstate b = some st → H'.dstate b = some st' → psiS f st' + e' + d ≤ psiS f st + e + d') :
    Bud f P e' d' h i b H' := by
  intro st' hst'
  obtain ⟨st, hst⟩ := hs
  have q := B st hst
  have q' := S st st' hst hst'
  rw [ea, eo]
  generalize G2 * (aIn h i - aIn H i) = X at *
  omega

/-- A step that writes output and lowers `psiS` by at least the bytes written (a flush). -/
theorem Bud.out {f : Int32} {P e d : Nat} {h H H' : Heap} {i b : Nat} (B : Bud f P e d h i b H)
    (hs : ∃ st, H.dstate b = some st) (ea : aIn H' i = aIn H i) (m : aOut H i ≤ aOut h i)
    (m' : aOut H' i ≤ aOut H i)
    (S : ∀ st st', H.dstate b = some st → H'.dstate b = some st' →
      psiS f st' + (aOut H i - aOut H' i) ≤ psiS f st) :
    Bud f P e d h i b H' := by
  intro st' hst'
  obtain ⟨st, hst⟩ := hs
  have q := B st hst
  have q' := S st st' hst hst'
  rw [ea]
  generalize G2 * (aIn h i - aIn H i) = X at *
  omega

/-- A strategy call (`PsiAccF f d`, `DeflatePsi`): the budget gains `G` per input byte consumed and takes the
strategy's allowance `d` as a debt. -/
theorem Bud.strat {f : Int32} {P e d : Nat} {h H H' : Heap} {i b : Nat} (B : Bud f P e 0 h i b H)
    (A : PsiAccF f d H H' i b) (hz : ∃ z, H.streams i = some z) (hz' : ∃ z, H'.streams i = some z)
    (hs : ∃ st, H.dstate b = some st) (m : aIn H i ≤ aIn h i ∧ aOut H i ≤ aOut h i)
    (m' : aIn H' i ≤ aIn H i ∧ aOut H' i ≤ aOut H i) :
    Bud f P (e + G * (aIn H i - aIn H' i)) d h i b H' := by
  intro st' hst'
  obtain ⟨st, hst⟩ := hs
  obtain ⟨z, hz⟩ := hz
  obtain ⟨z', hz'⟩ := hz'
  have q := B st hst
  have a := A z z' st st' hz hz' hst hst'
  rw [← aIn_of hz, ← aIn_of hz', ← aOut_of hz, ← aOut_of hz'] at a
  have e1 : aIn h i - aIn H' i = (aIn h i - aIn H i) + (aIn H i - aIn H' i) := by omega
  have e2 : G2 * (aIn H i - aIn H' i) = G * (aIn H i - aIn H' i) + G * (aIn H i - aIn H' i) := by
    unfold G2; rw [Nat.mul_assoc, Nat.two_mul]
  rw [e1, Nat.mul_add, e2]
  generalize G2 * (aIn h i - aIn H i) = X at *
  generalize G * (aIn H i - aIn H' i) = Y at *
  omega

/-! ## The end -/

/-- The end from a budget that covers the marker owed (or the output is full). -/
theorem endOk_of {f : Int32} {P e : Nat} {h H : Heap} {i b : Nat} (B : Bud f P e 0 h i b H)
    (hm : ∀ st, H.dstate b = some st → mark f st ≤ e + (if aOut H i = 0 then markK f else 0)) :
    EndOk f P h i b H := by
  intro st hst
  have q := B st hst
  have q' := hm st hst
  rw [psi_psiS]
  generalize G2 * (aIn h i - aIn H i) = X at *
  generalize (if aOut H i = 0 then markK f else 0) = Y at *
  omega

/-- The end with a full output. -/
theorem endOk_full {f : Int32} {P e : Nat} {h H : Heap} {i b : Nat} (B : Bud f P e 0 h i b H)
    (h0 : aOut H i = 0) : EndOk f P h i b H :=
  endOk_of B fun st _ => by rw [if_pos h0]; have := mark_le_markK f st; omega

/-- The end with no marker owed. -/
theorem endOk_zero {f : Int32} {P e : Nat} {h H : Heap} {i b : Nat} (B : Bud f P e 0 h i b H)
    (hm : ∀ st, H.dstate b = some st → mark f st = 0) : EndOk f P h i b H :=
  endOk_of B fun st hs => by rw [hm st hs]; exact Nat.zero_le _

/-- `EndOk` moves to a heap with the same stream record and state. -/
theorem EndOk.congr {f : Int32} {P : Nat} {h H H' : Heap} {i b : Nat} (q : EndOk f P h i b H)
    (ez : H'.streams i = H.streams i) (es : ∀ st, H'.dstate b = some st → H.dstate b = some st) :
    EndOk f P h i b H' := fun st hs => by
  rw [aIn_congr ez, aOut_congr ez]; exact q st (es st hs)

/-! ## `psiS` along the steps of `deflate` -/

/-- `psiS` does not read `last_flush`. -/
theorem psiS_lf (f : Int32) (st : DeflateState) (x : Int32) : psiS f { st with last_flush := x } = psiS f st := rfl

/-- After `last_flush = -1` the marker owed is at most `markK`. -/
theorem mark_m1 (f : Int32) (st : DeflateState) : mark f st ≤ markK f := mark_le_markK f st

/-- `status = BUSY_STATE` from `INIT_STATE` / `GZIP_STATE`: 16 less. -/
theorem psiS_busy (f : Int32) (st : DeflateState) (hs : st.status = INIT_STATE ∨ st.status = GZIP_STATE) :
    psiS f { st with status := BUSY_STATE } + 16 = psiS f st := by
  unfold psiS content quickB owed span
  dsimp only
  have h1 : (if st.status = INIT_STATE ∨ st.status = GZIP_STATE then (16 : Nat) else 0) = 16 := if_pos hs
  have h2 : (if BUSY_STATE = INIT_STATE ∨ BUSY_STATE = GZIP_STATE then (16 : Nat) else 0) = 0 :=
    if_neg (by decide)
  have h3 : (if BUSY_STATE ≠ FINISH_STATE then (2 : Nat) ^ 18 else 0) = 2 ^ 18 := if_pos (by decide)
  have h4 : (if st.status ≠ FINISH_STATE then (2 : Nat) ^ 18 else 0) = 2 ^ 18 :=
    if_pos (by rcases hs with x | x <;> rw [x] <;> decide)
  rw [h1, h2, h3, h4]
  omega

/-- `status = FINISH_STATE` from a status other than `FINISH_STATE`: `2^18` less. -/
theorem psiS_finish (f : Int32) (st : DeflateState) (hs : st.status ≠ FINISH_STATE) :
    psiS f { st with status := FINISH_STATE } + 2 ^ 18 ≤ psiS f st := by
  have := content_finish (st := st) (st' := { st with status := FINISH_STATE }) hs rfl rfl rfl rfl rfl rfl
  unfold psiS
  have e1 : quickB f { st with status := FINISH_STATE } = quickB f st := rfl
  have e2 : owed { st with status := FINISH_STATE } = owed st := rfl
  rw [e1, e2]; omega

/-- `wrap = -wrap` after the trailer: `4 wrap` less. -/
theorem psiS_wrap (f : Int32) (st : DeflateState) (hw : 0 < st.wrap.toInt) (w : Int32)
    (hw' : w.toInt = -st.wrap.toInt) :
    psiS f { st with wrap := w } + 4 * st.wrap.toInt.toNat = psiS f st := by
  have := content_wrap (st := st) (st' := { st with wrap := w }) hw hw' rfl rfl rfl rfl rfl
  unfold psiS
  have e1 : quickB f { st with wrap := w } = quickB f st := rfl
  have e2 : owed { st with wrap := w } = owed st := rfl
  rw [e1, e2]; omega

/-- A change of the bytes owed only (`flush_pending`, the trailer bytes): `psiS` moves with `owed`. -/
theorem psiS_owed (f : Int32) {st st' : DeflateState}
    (e : st' = { st with
      pending := st'.pending
      pending_out := st'.pending_out
      bi_buf := st'.bi_buf
      bi_valid := st'.bi_valid }) : psiS f st' + owed st = psiS f st + owed st' := by
  have e1 : content st' = content st := by rw [e]; rfl
  have e2 : quickB f st' = quickB f st := by rw [e]; rfl
  unfold psiS; rw [e1, e2]; omega

/-- A block emitter (`EmitKeeps`) that keeps `sym_next`: `psiS` moves with `owed`. -/
theorem psiS_emit (f : Int32) {st st' : DeflateState} (k : EmitKeeps st st') (hs : st'.sym_next = st.sym_next) :
    psiS f st' + owed st = psiS f st + owed st' := by
  have e1 : content st' = content st := by
    unfold content span; rw [hs]; rw [k]
  have e2 : quickB f st' = quickB f st := by rw [k]; rfl
  unfold psiS; rw [e1, e2]; omega

/-! ## `flush_pending` with the budget -/

/-- The counts do not grow over a `RunW`. -/
theorem RunW.mono {h H : Heap} {i b : Nat} (R : RunW h i b H) : aIn H i ≤ aIn h i ∧ aOut H i ≤ aOut h i := by
  obtain ⟨z0, z, ob, oo, k, h0, h1, -, -, ek⟩ := R.out
  obtain ⟨z0', z', k', h0', h1', ek', -⟩ := R.inp
  obtain rfl := Option.some.inj (h0.symm.trans h0')
  obtain rfl := Option.some.inj (h1.symm.trans h1')
  rw [aIn_of h0, aIn_of h1, aOut_of h0, aOut_of h1]; omega

/-- `run_flush` with the budget: `flush_pending` lowers `owed` by exactly the bytes it writes, so every budget
moves along. -/
theorem run_flushB {h H : Heap} {i b : Nat} (R : RunW h i b H) :
    ∃ H', C.run (ZlibNg.DeflateP.flush_pending (some i)) H = .ok ((), H') ∧ Run h i b H' ∧
      (∀ z st, H.streams i = some z → H.dstate b = some st → ∃ z' st', H'.streams i = some z' ∧
        H'.dstate b = some st' ∧ st' = { st with
          pending := st'.pending
          pending_out := st'.pending_out
          bi_buf := st'.bi_buf
          bi_valid := st'.bi_valid } ∧
        z' = { z with
          next_out := z'.next_out
          avail_out := z'.avail_out
          total_out := z'.total_out } ∧
        (z'.avail_out ≠ 0 → st'.pending = 0) ∧ st'.bi_valid < 8 ∧ HdrMove H H' b b st ∧
        z'.avail_out.toNat + st.pending.toNat ≤ z.avail_out.toNat + st'.pending.toNat) ∧
      aIn H' i = aIn H i ∧ (∀ f P e d, Bud f P e d h i b H → Bud f P e d h i b H') := by
  obtain ⟨H', e, R', k⟩ := run_flush R
  obtain ⟨z, hz, hb⟩ := R.blk
  obtain ⟨i', z2, b2, st, al, e2, hz2, hb2, hst, -⟩ := R.work
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj (hz.symm.trans hz2)
  obtain rfl := Option.some.inj (hb.symm.trans hb2)
  obtain ⟨z', st', hz', hst', hse, hze, -⟩ := k z st hz hst
  have hai : aIn H' i = aIn H i := by rw [aIn_of hz', aIn_of hz, hze]
  refine ⟨H', e, R', k, hai, fun f P e' d B => ?_⟩
  have ow := TreesOwed.flush_pending_owed' R.work R.io R.set H' e z b st z' st' hz hb hst hz' hst'
  have m := R.mono
  refine B.out ⟨st, hst⟩ hai m.2 (by rw [aOut_of hz', aOut_of hz]; exact ow.1) fun s1 s2 h1 h2 => ?_
  obtain rfl := Option.some.inj (hst.symm.trans h1)
  obtain rfl := Option.some.inj (hst'.symm.trans h2)
  have := psiS_owed f hse
  rw [aOut_of hz', aOut_of hz]
  omega

end ZlibNgF.Proof.DeflateBody
