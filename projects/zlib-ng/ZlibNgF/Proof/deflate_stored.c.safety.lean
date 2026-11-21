import ZlibNgF.Proof.«deflate_stored.c.block»
import ZlibNgF.Proof.«deflate_rle.c.safety»
import ZlibNgF.Proof.«deflate_huff.c.safety»

/-!
# `deflate_stored` (`ZlibNgF`)

`stored_ok`: the level-0 strategy keeps the strategy frame (`StratOkP`): the copy loop (`trip_ok`, measure
`avail_out`), the window update (`uw_ok`), the early returns, the filling of the window (`fill_ok`), the stored block
through `pending_buf` (`blk_ok`, `tail_ok`), and `StratPost` from `SF` (`sf_post`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.StoredSafe
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateFlush ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.StoredIO ZlibNgF.Proof.StoredF ZlibNgF.Proof.StoredTrip ZlibNgF.Proof.StoredWin
open ZlibNgF.Proof.StoredBlk
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNg.DeflateStored
open ZlibNgF.Proof.DeflatePsi (span)

/-- Progress of stream `i` from `h` to `H` (the clause of `StratPost` for `need_more` / `finish_started` under
`Z_FINISH`): from an output with room, some input consumed or some output produced. -/
def Prog (h H : Heap) (i : Nat) : Prop :=
  ∀ z z', StreamAt h (some i) z → StreamAt H (some i) z' → z.avail_out ≠ 0 →
    z'.avail_in < z.avail_in ∨ z'.avail_out < z.avail_out

theorem streamAt_congr {H H' : Heap} {i : Nat} (e : H'.streams i = H.streams i) (z' : ZStream) :
    StreamAt H' (some i) z' ↔ StreamAt H (some i) z' := by
  constructor
  · rintro ⟨i', e', h'⟩; obtain rfl := Option.some.inj e'; exact ⟨_, rfl, by rw [← e]; exact h'⟩
  · rintro ⟨i', e', h'⟩; obtain rfl := Option.some.inj e'; exact ⟨_, rfl, by rw [e]; exact h'⟩

/-- `s->bi_used = 8; return r;` from `SF` with no pending bytes. -/
theorem fin_bu {e : Nat} {h H : Heap} {i b wo : Nat} (F : SF e h i b H)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (flush : Int32) (r : BlockState)
    (he : e ≤ finSlack r)
    (hp0 : r = .block_done ∨ r = .finish_done → ∀ st, H.dstate b = some st → st.pending = 0)
    (hB : r = .need_more ∨ r = .block_done → CF H i) (hF : r = .finish_started ∨ r = .finish_done → flush = Z_FINISH)
    (hP : flush = Z_FINISH → r = .need_more ∨ r = .finish_started → Prog h H i)
    (hD : r ≠ .block_done) :
    Sat H (do
      wrD (some b) fun s => { s with bi_used := 8 }
      return r) (fun r' H' => StratPost h (some i) flush r' H') := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by
    rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  have ee : (SH (setB H ob X) i z b { st with bi_used := 8 } d).streams i = H.streams i := by
    rw [SH_streams, S.hz]
  rw [← e0]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.pure (sf_post (sf_state (st' := { st with bi_used := 8 }) F S rfl hss hb0 hbs S.ins rfl
    (Nat.le_refl _)) flush r
    (fun e z' hz' => hB e z' ((streamAt_congr ee z').mp hz')) hF
    (fun hf e z0 z' hz0 hz' => hP hf e z0 z' hz0 ((streamAt_congr ee z').mp hz')) (fun e st2 h2 => ?_)
    (fun e => absurd e hD) he)
  rw [SH_dstate] at h2; cases h2; exact hp0 e st S.hst

/-- Progress after the stored block through `pending_buf`: input consumed since the entry, or the output emptied
(input left), or one more output byte (`pending` holds at least the 4 header bytes). -/
theorem prog_blk {e : Nat} {h H H' : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {len : UInt32}
    (F : SF e h i b H)
    (hz : H.streams i = some z) (hst : H.dstate b = some st) (hb : BlkIO H H' i b len)
    (hA : z.avail_in ≠ 0 → z.avail_out.toNat ≤ len.toNat + (st.bi_valid.toInt.toNat + 42) / 8) : Prog h H' i := by
  rintro z0 z2 ⟨i1, e1, h1⟩ ⟨i2, e2, h2⟩ hne
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain ⟨b1, b2, b3, b4⟩ := hb z st z2 hz hst h2
  obtain ⟨z0', z', ob, oo, k, h0', h', -, -, hk⟩ := F.out
  obtain rfl := Option.some.inj (h1.symm.trans h0')
  obtain rfl := Option.some.inj (hz.symm.trans h')
  obtain ⟨z0'', z'', h0'', h'', hle, -⟩ := F.inp
  obtain rfl := Option.some.inj (h1.symm.trans h0'')
  obtain rfl := Option.some.inj (hz.symm.trans h'')
  have hne' : z0.avail_out.toNat ≠ 0 := fun e => hne (UInt32.toNat_inj.mp (by rw [e]; rfl))
  by_cases hai : z.avail_in.toNat < z0.avail_in.toNat
  · left; rw [b1]; exact UInt32.lt_iff_toNat_lt.mpr hai
  · right; apply UInt32.lt_iff_toNat_lt.mpr
    by_cases h0 : z.avail_in = 0
    · by_cases ho : z.avail_out = 0
      · have : z.avail_out.toNat = 0 := by rw [ho]; rfl
        omega
      · have := b4 ho; omega
    · rw [b3 (hA h0)]; show 0 < _; omega

section parts
open ZlibNg.DeflateP

/-- The stored block through `pending_buf` and the return (`deflate_stored.c:168-186`). -/
def tail_part (st : StatePtr) (window : BPtr) (w_size : UInt32) (flush : Int32) (last : Int32) :
    M BlockState := do
  let have_ ← headerBytes st
  let have_ := MIN32 ((← rdD st (·.pending_buf_size)) - have_) MAX_STORED
  let min_block := MIN32 have_ w_size
  let left ← leftOf st
  let c : Bool ← if left ≥ min_block then pure true
    else if (left != 0 || flush == Z_FINISH) && flush != Z_NO_FLUSH then do
      pure ((← rdZ (← strmOf st) (·.avail_in)) == 0 && left ≤ have_)
    else pure false
  let last ← if c then do
      let len := MIN32 left have_
      let c2 : Bool ← if flush == Z_FINISH then do
          pure ((← rdZ (← strmOf st) (·.avail_in)) == 0 && len == left)
        else pure false
      let last : Int32 := if c2 then 1 else 0
      ZlibNg.Trees.zng_tr_stored_block st (← window.add (← rdD st (·.block_start)).toInt) len last
      let bs ← chkI32 ((← rdD st (·.block_start)).toInt + len.toInt32.toInt)
      wrD st fun s => { s with block_start := bs }
      flush_pending (← strmOf st)
      pure last
    else pure last
  if last != 0 then
    wrD st fun s => { s with bi_used := 8 }
    return .finish_started
  return .need_more

end parts

/-- The stored block through `pending_buf` and the return, from `SF` with no pending bytes, after a copy loop that did
not set `last`. `hx`: input left only with at least `w_size` bytes left in the window, and the copy loop stopped for
lack of output room or of input (`TExit`, carried through the window update and the filling). -/
theorem tail_ok {h H : Heap} {i b wo : Nat} (F : SF 0 h i b H) (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (w_size : UInt32) (flush last : Int32)
    (hl0 : last = 0)
    (hx : ∀ z st, H.streams i = some z → H.dstate b = some st → st.w_size = w_size ∧
      (z.avail_in ≠ 0 → (w_size.toNat : Int) ≤ st.strstart.toNat - st.block_start.toInt) ∧
      (z.avail_out.toNat < (st.bi_valid.toInt.toNat + 42) / 8 + min (st.pending_buf_size.toNat - 5) w_size.toNat ∨
        (st.strstart.toNat : Int) - st.block_start.toInt + z.avail_in.toNat <
          min (st.pending_buf_size.toNat - 5) w_size.toNat)) :
    Sat H (tail_part (some b) (.ref (.heap b) wo) w_size flush last) (fun r H' => StratPost h (some i) flush r H') := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e1 : SH H i z b st d = H := ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  obtain ⟨hv0, hv8⟩ := S.bits
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  have hws := S.ws.1
  have hw32 := S.ws.2.2.2
  obtain ⟨lb1, lb2, lb3⟩ := S.lb
  obtain ⟨hwz, hx1, hx2⟩ := hx z st S.hz S.hst
  have hw5 : 512 ≤ w_size.toNat := by rw [← hwz]; exact S.ws.2.2.1
  rw [hwz] at hw32
  obtain ⟨hv, ehv, hvn⟩ := headerBytes_SH (H := H) (i := i) (z := z) (d := d) hv0 hv8
  obtain ⟨left, elf, hlf⟩ := leftOf_SH (H := H) (i := i) (z := z) (d := d) hb0 hbs (by omega)
  rw [e1] at ehv elf
  have esm : strmOf (some b) H = .ok (some i, H) := by rw [← e1]; exact strmOf_SH S.strm
  have erz : ∀ {β : Type} (f : ZStream → β), rdZ (some i) f H = .ok (f z, H) := fun f => by
    rw [← e1]; exact rdZ_SH f
  have erd : ∀ {β : Type} (f : DeflateState → β), rdD (some b) f H = .ok (f st, H) := fun f => by
    rw [← e1]; exact rdD_SH f
  have hend : ∀ (e' : Nat) (l : Int32) (H' : Heap), SF e' h i b H' → (l = 0 → e' = 0) → e' ≤ 5 → CF H' i →
      (l ≠ 0 → flush = Z_FINISH) → (flush = Z_FINISH → Prog h H' i) → Sat H' (do
      if l != 0 then
        wrD (some b) fun s => { s with bi_used := 8 }
        return BlockState.finish_started
      return BlockState.need_more) (fun r H' => StratPost h (some i) flush r H') := by
    intro e' l H' F' hl0 he5 hcf hlf hpg
    by_cases hl : (l != 0) = true
    · simp only [hl, ↓reduceIte]
      have hl' : l ≠ 0 := by simpa using hl
      exact fin_bu F' hw0 flush _ (by unfold finSlack; rw [ite_eq_left (Or.inl rfl)]; omega) (fun e => by rcases e with e | e <;> cases e)
        (fun _ => hcf) (fun _ => hlf hl') (fun hf _ => hpg hf) (by decide)
    · simp only [hl, Bool.false_eq_true, ↓reduceIte]
      have hl' : l = 0 := by simpa using hl
      exact Sat.pure (sf_post F' flush _ (fun _ => hcf) (fun e => by rcases e with e | e <;> cases e)
        (fun hf _ => hpg hf) (fun e => by rcases e with e | e <;> cases e) (fun e => by cases e)
        (by rw [hl0 hl']; exact Nat.zero_le _))
  unfold tail_part
  refine Sat.bind (Sat.of_eq ehv ?_)
  refine Sat.bind (Sat.of_eq (erd _) ?_)
  refine Sat.bind (Sat.of_eq elf ?_)
  extract_lets jEnd len jC2 jC
  have hEnd : ∀ e' l H', SF e' h i b H' → (l = 0 → e' = 0) → e' ≤ 5 → CF H' i → (l ≠ 0 → flush = Z_FINISH) →
      (flush = Z_FINISH → Prog h H' i) → Sat H' (jEnd l) (fun r H' => StratPost h (some i) flush r H') :=
    fun e' l H' F' b1 b2 a1 a2 a3 => by simp only [jEnd]; exact hend e' l H' F' b1 b2 a1 a2 a3
  have hpv : (st.pending_buf_size - hv).toNat = st.pending_buf_size.toNat - hv.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have hm1 := min32_toNat (st.pending_buf_size - hv) ZlibNg.DeflateP.MAX_STORED
  have hm2 := min32_toNat left (MIN32 (st.pending_buf_size - hv) ZlibNg.DeflateP.MAX_STORED)
  have hm3 := min32_toNat (MIN32 (st.pending_buf_size - hv) ZlibNg.DeflateP.MAX_STORED) w_size
  have hMS : ZlibNg.DeflateP.MAX_STORED.toNat = 65535 := rfl
  have hlen : len.toNat ≤ left.toNat ∧ len.toNat + hv.toNat ≤ st.pending_buf_size.toNat := by
    simp only [len]; omega
  have hlen' : len.toNat = min left.toNat (min (st.pending_buf_size.toNat - hv.toNat) 65535) := by
    simp only [len]; omega
  have hA : z.avail_in ≠ 0 → z.avail_out.toNat ≤ len.toNat + (st.bi_valid.toInt.toNat + 42) / 8 := by
    intro hne
    have hx1' := hx1 hne
    rcases hx2 with h2 | h2 <;> omega
  -- with input left, the window holds at least `w_size` bytes, so a block is written
  have hW : z.avail_in ≠ 0 → (MIN32 (MIN32 (st.pending_buf_size - hv) ZlibNg.DeflateP.MAX_STORED) w_size).toNat ≤
      left.toNat := fun hne => by have := hx1 hne; omega
  have hC2 : ∀ c2 : Bool, (c2 = true → flush = Z_FINISH ∧ z.avail_in = 0) → (c2 = false → len.toNat ≠ 0) →
      Sat H (jC2 c2) (fun r H' => StratPost h (some i) flush r H') := by
    intro c2 hc2 hc2'
    simp only [jC2]
    refine blk_ok F (fun st2 h2 => by rw [S.hst] at h2; cases h2; exact hp0 st S.hst) hw0 len _
      (fun st2 h2 => by rw [S.hst] at h2; cases h2; exact ⟨by omega, by omega⟩) _ _ (fun H' F' hb => ?_)
    refine hEnd _ _ H' F' (fun hl0 => ?_) (by split <;> omega) ?_ (fun hne => ?_)
      (fun _ => prog_blk F S.hz S.hst hb hA)
    · cases c2
      · rw [ite_eq_right (hc2' rfl)]
      · exact absurd hl0 (by decide)
    · rintro z2 ⟨i2, e2, h2⟩
      obtain rfl := Option.some.inj e2
      obtain ⟨b1, -, b3, -⟩ := hb z st z2 S.hz S.hst h2
      by_cases h0 : z.avail_in = 0
      · exact .inl (b1.trans h0)
      · exact .inr (b3 (hA h0))
    · cases c2
      · exact absurd rfl hne
      · exact (hc2 rfl).1
  have hhv : 1 ≤ min (st.pending_buf_size.toNat - hv.toNat) 65535 := by omega
  have hC : ∀ c : Bool, (c = false → z.avail_in = 0 ∧ flush ≠ Z_FINISH) →
      (c = true → len.toNat = 0 → flush = Z_FINISH ∧ z.avail_in = 0) →
      Sat H (jC c) (fun r H' => StratPost h (some i) flush r H') := by
    intro c hc hct
    simp only [jC]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h0, hf⟩ := hc rfl
      refine hEnd 0 last H F (fun _ => rfl) (Nat.zero_le _) ?_ (fun e => absurd hl0 e) (fun e => absurd e hf)
      rintro z2 ⟨i2, e2, h2⟩
      obtain rfl := Option.some.inj e2
      rw [S.hz] at h2; cases h2; exact .inl h0
    · simp only [↓reduceIte]
      split
      · rename_i hf
        refine Sat.bind (Sat.of_eq esm ?_)
        refine Sat.bind (Sat.of_eq (erz _) ?_)
        refine Sat.bind (Sat.pure (hC2 _ (fun e => ?_) fun e hl => ?_))
        · simp only [Bool.and_eq_true, beq_iff_eq] at e hf
          exact ⟨hf, e.1⟩
        · obtain ⟨-, h0⟩ := hct rfl hl
          have hlf0 : left.toNat = 0 := by omega
          have : len = left := UInt32.toNat_inj.mp (by omega)
          rw [h0, this] at e
          simp at e
      · rename_i hf
        refine Sat.bind (Sat.pure (hC2 _ (fun e => by cases e) fun _ hl => ?_))
        exact hf (by simp only [beq_iff_eq]; exact (hct rfl hl).1)
  have hfin : (Z_FINISH != Z_NO_FLUSH) = true := by decide
  split
  · rename_i hge
    refine hC true (fun e => by cases e) fun _ hl => ?_
    have := UInt32.le_iff_toNat_le.mp hge
    omega
  · rename_i hlt
    have hlt' : left.toNat < (MIN32 (MIN32 (st.pending_buf_size - hv) ZlibNg.DeflateP.MAX_STORED) w_size).toNat :=
      UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hlt)
    have h0 : z.avail_in = 0 := Classical.byContradiction fun hne => by have := hW hne; omega
    split
    · refine Sat.bind (Sat.of_eq esm ?_)
      refine Sat.bind (Sat.of_eq (erz _) ?_)
      rename_i hcond
      refine Sat.bind (Sat.pure (hC _ (fun e => ?_) fun e hl => ?_))
      rotate_left
      · have hlf0 : left.toNat = 0 := by omega
        have hl0' : left = 0 := UInt32.toNat_inj.mp (by rw [hlf0]; rfl)
        rw [hl0'] at hcond
        simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hcond
        exact ⟨hcond.1, h0⟩
      exfalso
      rw [h0] at e
      simp only [beq_self_eq_true, Bool.true_and, decide_eq_false_iff_not] at e
      have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp e)
      omega
    · rename_i hcond
      refine hC false (fun _ => ⟨h0, fun hf => hcond ?_⟩) (fun e => by cases e)
      subst hf
      simp [hfin]

/-- `deflate_stored` keeps the strategy frame. -/
theorem stored_ok (_T : TreesFacts) : StratOkP (fun st => st.level = 0) deflate_stored := by
  intro h s b flush P hsb hE
  obtain ⟨z, ⟨i, rfl, hz⟩, hb⟩ := hsb
  obtain ⟨st0, hst0, hp00, F0⟩ := sf_entry P hz hb hE
  obtain ⟨i', z', b', st', al, e, L, -, c⟩ := live P.1
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans L.hz)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans L.hb)
  obtain rfl : st0 = st' := Option.some.inj (hst0.symm.trans L.dstate)
  obtain ⟨d0, wo, -, -, -, hd0, hwin, -⟩ := c.lay
  simp only [dview] at hwin
  have hw0 : ∀ st, h.dstate b = some st → st.window = .val (.ref (.heap b) wo) := fun st h1 => by
    rw [hst0] at h1; cases h1; exact hwin
  have hp0 : ∀ st, h.dstate b = some st → st.pending = 0 := fun st h1 => by
    rw [hst0] at h1; cases h1; exact hp00
  have e1 : SH h i z b st0 d0 = h :=
    ZlibNgF.Proof.DeflateReset.SH_self hz (dstates_of_dstate hst0 hd0) hd0
  have esm : strmOf (some b) h = .ok (some i, h) := by rw [← e1]; exact strmOf_SH c.strm
  have erz : ∀ {β : Type} (f : ZStream → β), rdZ (some i) f h = .ok (f z, h) := fun f => by
    rw [← e1]; exact rdZ_SH f
  suffices S : Sat h (deflate_stored (some b) flush) (fun bs h' => StratPost h (some i) flush bs h') by
    obtain ⟨bs, h', e, q⟩ := S
    exact ⟨bs, h', e, q⟩
  unfold deflate_stored
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hwin]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  refine Sat.bind (Sat.of_eq esm ?_)
  refine Sat.bind (Sat.of_eq (erz _) ?_)
  obtain ⟨z0, st0', d0', ob0, oo0, X0, pbo0, S0⟩ := F0.facts hw0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans S0.hz)
  obtain rfl : st0 = st0' := Option.some.inj (hst0.symm.trans S0.hst)
  have hw32 := S0.ws.2.2.2
  have hw512 := S0.ws.2.2.1
  obtain ⟨lb1, lb2, lb3⟩ := S0.lb
  have hmb := min32_toNat (st0.pending_buf_size - 5) st0.w_size
  have hp5 : (st0.pending_buf_size - 5).toNat = st0.pending_buf_size.toNat - 5 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
  rw [hp5] at hmb
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cdoWhileH
    (fun s H => SF 0 h i b H ∧ (∀ st, H.dstate b = some st → st.pending = 0) ∧ (s.1 ≠ 0 → flush = Z_FINISH))
    (fun _ H => avOut H i)
    (fun s H => SF (if s.1 = 0 then 0 else 5) h i b H ∧ (∀ st, H.dstate b = some st → st.pending = 0) ∧
      (s.1 ≠ 0 → flush = Z_FINISH) ∧
      (s.1 = 0 → TExit H i b (MIN32 (st0.pending_buf_size - 5) st0.w_size))) ?_ (s := ((0 : Int32), false))
    ⟨F0, hp0, fun e => absurd rfl e⟩ ?_) ?_)
  · rintro ⟨l, br⟩ H ⟨F, hp, hL⟩
    refine Sat.mono (trip_ok flush _ l F hp hw0 (by omega) (by omega) hL) ?_
    rintro ⟨l1, b1⟩ H1 ⟨F1, hp1, hdec, hfl, hex⟩
    refine Sat.pure ⟨fun hc => ⟨⟨?_, hp1, hfl⟩, hdec ?_⟩, fun hc => ⟨F1, hp1, hfl, fun hl => hex ?_⟩⟩
    · have hl' : l1 = 0 := by simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.2
      simp only [hl'] at F1; exact F1
    · cases b1
      · rfl
      · simp at hc
    · cases b1
      · have hl' : l1 = 0 := hl
        simp [hl'] at hc
      · rfl
  · have : avOut h i < 2 ^ 32 := by simp only [avOut, hz]; exact UInt32.toNat_lt _
    simp only [fuel]; omega
  rintro ⟨last, br⟩ H1 ⟨F1, hp1, hfl1, hex1⟩
  have F1 : SF (if last = 0 then 0 else 5) h i b H1 := F1
  have hfl1 : last ≠ 0 → flush = Z_FINISH := hfl1
  have hex1 : last = 0 → TExit H1 i b (MIN32 (st0.pending_buf_size - 5) st0.w_size) := hex1
  refine Sat.bind (Sat.mono (uw_ok F1 hp1 hw0 last hz hst0) ?_)
  rintro _ H2 ⟨F2, hp2, hai2, hao2, huw2⟩
  by_cases hl : (last != 0) = true
  · simp only [hl, ↓reduceIte]
    have hl' : last ≠ 0 := by simpa using hl
    exact fin_bu F2 hw0 flush _ (by simp only [finSlack]; split <;> simp) (fun _ => hp2)
      (fun e => by rcases e with e | e <;> cases e) (fun _ => hfl1 hl')
      (fun _ e => by rcases e with e | e <;> cases e) (by decide)
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  have hl0 : last = 0 := by simpa using hl
  rw [hl0] at F1 F2
  simp only [↓reduceIte] at F1 F2
  obtain ⟨z1, st1, d1, ob1, oo1, X1, pbo1, S1⟩ := F1.facts hw0
  obtain ⟨z2, st2, d2, ob2, oo2, X2, pbo2, S2⟩ := F2.facts hw0
  have e2 : SH H2 i z2 b st2 d2 = H2 := ZlibNgF.Proof.DeflateReset.SH_self S2.hz S2.hsts S2.hd
  have esm2 : strmOf (some b) H2 = .ok (some i, H2) := by rw [← e2]; exact strmOf_SH S2.strm
  have erz2 : ∀ {β : Type} (f : ZStream → β), rdZ (some i) f H2 = .ok (f z2, H2) := fun f => by
    rw [← e2]; exact rdZ_SH f
  have eld2 : ldDState (some b) H2 = .ok (st2, H2) := by rw [← e2]; exact ldDState_SH
  have hX1 := hex1 hl0 z1 st1 S1.hz S1.hst
  rw [hmb] at hX1
  have hai2' : z2.avail_in = z1.avail_in := by
    simp only [avIn, S1.hz, S2.hz] at hai2; exact UInt32.toNat_inj.mp hai2
  have hao2' : z2.avail_out = z1.avail_out := by
    simp only [avOut, S1.hz, S2.hz] at hao2; exact UInt32.toNat_inj.mp hao2
  obtain ⟨hbv2, hlf2⟩ := huw2 st1 st2 S1.hst S2.hst
  obtain ⟨st0a, h0a, -, -, hk2⟩ := F2.keeps
  obtain rfl : st0 = st0a := Option.some.inj (hst0.symm.trans h0a)
  have K2 := hk2 st2 S2.hst
  have hfill := fill_ok F2 hp2 hw0 hst0 (tail_part (some b) (.ref (.heap b) wo) st0.w_size flush last)
    (fun r H' => StratPost h (some i) flush r H') (fun H3 F3 hp3 hX3 => tail_ok F3 hp3 hw0 _ _ _ hl0
      fun z3 st3 g1 g2 => by
        obtain ⟨st0b, h0b, -, -, hk3⟩ := F3.keeps
        obtain rfl : st0 = st0b := Option.some.inj (hst0.symm.trans h0b)
        have K3 := hk3 st3 g2
        obtain ⟨f1, f2, f3, f4⟩ := hX3 z2 st2 z3 st3 S2.hz S2.hst g1 g2
        rw [K2.2.2.1] at f4
        refine ⟨K3.2.2.1, fun hne => f4 hne, ?_⟩
        rw [K3.2.2.2.2, f1, hao2', f2, hbv2]
        rw [hai2'] at f3
        have hf3 : ((z3.avail_in.toNat : Int)) = (st2.strstart.toNat : Int) - st2.block_start.toInt + z1.avail_in.toNat -
          ((st3.strstart.toNat : Int) - st3.block_start.toInt) := by omega
        omega)
  refine Sat.bind (Sat.of_eq esm2 ?_)
  refine Sat.bind (Sat.of_eq (erz2 _) ?_)
  by_cases hc : (flush != Z_NO_FLUSH && flush != ZlibNg.Inflate.Z_FINISH && z2.avail_in == 0) = true
  · rw [ite_t hc]
    refine Sat.bind (Sat.of_eq eld2 ?_)
    by_cases hc2 : (st2.strstart.toInt32 == st2.block_start) = true
    · rw [ite_t hc2]
      have h0 : z2.avail_in = 0 := by simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.2
      have hnf : flush ≠ Z_NO_FLUSH ∧ flush ≠ Z_FINISH := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc; exact ⟨hc.1.1, hc.1.2⟩
      refine Sat.pure (sf_post F2 flush _ (fun _ => ?_) (fun e => by rcases e with e | e <;> cases e)
        (fun _ e => by rcases e with e | e <;> cases e) (fun _ => hp2) fun _ => ⟨hnf.1, hnf.2, fun z' hz' => ?_⟩)
      · rintro z' ⟨i', e', h'⟩
        obtain rfl := Option.some.inj e'
        rw [S2.hz] at h'; cases h'; exact .inl h0
      · obtain ⟨i', e', h'⟩ := hz'
        obtain rfl := Option.some.inj e'
        rw [S2.hz] at h'; cases h'; exact h0
    · rw [ite_f hc2]
      exact hfill
  · rw [ite_f hc]
    exact hfill

end ZlibNgF.Proof.StoredSafe
