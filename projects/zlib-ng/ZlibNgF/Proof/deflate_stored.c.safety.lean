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

/-- `s->bi_used = 8; return r;` from `SF` with no pending bytes. -/
theorem fin_bu {h H : Heap} {i b wo : Nat} (F : SF h i b H)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (flush : Int32) (r : BlockState)
    (hp0 : r = .block_done ∨ r = .finish_done → ∀ st, H.dstate b = some st → st.pending = 0) :
    Sat H (do
      wrD (some b) fun s => { s with bi_used := 8 }
      return r) (fun r' H' => StratPost h (some i) flush r' H') := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by
    rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  rw [← e0]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.pure (sf_post (sf_state (st' := { st with bi_used := 8 }) F S rfl hss hb0 hbs S.ins rfl) flush r fun e st2 h2 => ?_)
  rw [SH_dstate] at h2; cases h2; exact hp0 e st S.hst

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

/-- The stored block through `pending_buf` and the return, from `SF` with no pending bytes. -/
theorem tail_ok {h H : Heap} {i b wo : Nat} (F : SF h i b H) (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (w_size : UInt32) (flush last : Int32) :
    Sat H (tail_part (some b) (.ref (.heap b) wo) w_size flush last) (fun r H' => StratPost h (some i) flush r H') := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e1 : SH H i z b st d = H := ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  obtain ⟨hv0, hv8⟩ := S.bits
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  have hws := S.ws.1
  obtain ⟨lb1, lb2, lb3⟩ := S.lb
  obtain ⟨hv, ehv, hvn⟩ := headerBytes_SH (H := H) (i := i) (z := z) (d := d) hv0 hv8
  obtain ⟨left, elf, hlf⟩ := leftOf_SH (H := H) (i := i) (z := z) (d := d) hb0 hbs (by omega)
  rw [e1] at ehv elf
  have esm : strmOf (some b) H = .ok (some i, H) := by rw [← e1]; exact strmOf_SH S.strm
  have erz : ∀ {β : Type} (f : ZStream → β), rdZ (some i) f H = .ok (f z, H) := fun f => by
    rw [← e1]; exact rdZ_SH f
  have erd : ∀ {β : Type} (f : DeflateState → β), rdD (some b) f H = .ok (f st, H) := fun f => by
    rw [← e1]; exact rdD_SH f
  have hend : ∀ (l : Int32) (H' : Heap), SF h i b H' → Sat H' (do
      if l != 0 then
        wrD (some b) fun s => { s with bi_used := 8 }
        return BlockState.finish_started
      return BlockState.need_more) (fun r H' => StratPost h (some i) flush r H') := by
    intro l H' F'
    by_cases hl : (l != 0) = true
    · simp only [hl, ↓reduceIte]
      exact fin_bu F' hw0 flush _ fun e => by rcases e with e | e <;> cases e
    · simp only [hl, Bool.false_eq_true, ↓reduceIte]
      exact Sat.pure (sf_post F' flush _ fun e => by rcases e with e | e <;> cases e)
  unfold tail_part
  refine Sat.bind (Sat.of_eq ehv ?_)
  refine Sat.bind (Sat.of_eq (erd _) ?_)
  refine Sat.bind (Sat.of_eq elf ?_)
  extract_lets jEnd len jC2 jC
  have hEnd : ∀ l H', SF h i b H' → Sat H' (jEnd l) (fun r H' => StratPost h (some i) flush r H') :=
    fun l H' F' => by simp only [jEnd]; exact hend l H' F'
  have hpv : (st.pending_buf_size - hv).toNat = st.pending_buf_size.toNat - hv.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have hm1 := min32_toNat (st.pending_buf_size - hv) ZlibNg.DeflateP.MAX_STORED
  have hm2 := min32_toNat left (MIN32 (st.pending_buf_size - hv) ZlibNg.DeflateP.MAX_STORED)
  have hlen : len.toNat ≤ left.toNat ∧ len.toNat + hv.toNat ≤ st.pending_buf_size.toNat := by
    simp only [len]; omega
  have hC2 : ∀ c2 : Bool, Sat H (jC2 c2) (fun r H' => StratPost h (some i) flush r H') := by
    intro c2
    simp only [jC2]
    exact blk_ok F (fun st2 h2 => by rw [S.hst] at h2; cases h2; exact hp0 st S.hst) hw0 len _
      (fun st2 h2 => by rw [S.hst] at h2; cases h2; exact ⟨by omega, by omega⟩) _ _ (fun H' F' => hEnd _ H' F')
  have hC : ∀ c : Bool, Sat H (jC c) (fun r H' => StratPost h (some i) flush r H') := by
    intro c
    simp only [jC]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hEnd last H F
    · simp only [↓reduceIte]
      split
      · refine Sat.bind (Sat.of_eq esm ?_)
        refine Sat.bind (Sat.of_eq (erz _) ?_)
        exact Sat.bind (Sat.pure (hC2 _))
      · exact Sat.bind (Sat.pure (hC2 _))
  split
  · exact hC true
  · split
    · refine Sat.bind (Sat.of_eq esm ?_)
      refine Sat.bind (Sat.of_eq (erz _) ?_)
      exact Sat.bind (Sat.pure (hC _))
    · exact hC false

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
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cdoWhileH
    (fun _ H => SF h i b H ∧ ∀ st, H.dstate b = some st → st.pending = 0) (fun _ H => avOut H i)
    (fun _ H => SF h i b H ∧ ∀ st, H.dstate b = some st → st.pending = 0) ?_ (s := ((0 : Int32), false))
    ⟨F0, hp0⟩ ?_) ?_)
  · rintro ⟨l, br⟩ H ⟨F, hp⟩
    refine Sat.mono (trip_ok flush _ l F hp hw0) ?_
    rintro ⟨l1, b1⟩ H1 ⟨F1, hp1, hdec⟩
    refine Sat.pure ⟨fun hc => ⟨⟨F1, hp1⟩, hdec ?_⟩, fun _ => ⟨F1, hp1⟩⟩
    cases b1
    · rfl
    · simp at hc
  · have : avOut h i < 2 ^ 32 := by simp only [avOut, hz]; exact UInt32.toNat_lt _
    simp only [fuel]; omega
  rintro ⟨last, br⟩ H1 ⟨F1, hp1⟩
  refine Sat.bind (Sat.mono (uw_ok F1 hp1 hw0 last hz hst0) ?_)
  rintro _ H2 ⟨F2, hp2, -, -⟩
  by_cases hl : (last != 0) = true
  · simp only [hl, ↓reduceIte]
    exact fin_bu F2 hw0 flush _ (fun _ => hp2)
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨z2, st2, d2, ob2, oo2, X2, pbo2, S2⟩ := F2.facts hw0
  have e2 : SH H2 i z2 b st2 d2 = H2 := ZlibNgF.Proof.DeflateReset.SH_self S2.hz S2.hsts S2.hd
  have esm2 : strmOf (some b) H2 = .ok (some i, H2) := by rw [← e2]; exact strmOf_SH S2.strm
  have erz2 : ∀ {β : Type} (f : ZStream → β), rdZ (some i) f H2 = .ok (f z2, H2) := fun f => by
    rw [← e2]; exact rdZ_SH f
  have eld2 : ldDState (some b) H2 = .ok (st2, H2) := by rw [← e2]; exact ldDState_SH
  have hfill := fill_ok F2 hp2 hw0 hst0 (tail_part (some b) (.ref (.heap b) wo) st0.w_size flush last)
    (fun r H' => StratPost h (some i) flush r H') (fun H3 F3 hp3 => tail_ok F3 hp3 hw0 _ _ _)
  refine Sat.bind (Sat.of_eq esm2 ?_)
  refine Sat.bind (Sat.of_eq (erz2 _) ?_)
  by_cases hc : (flush != Z_NO_FLUSH && flush != ZlibNg.Inflate.Z_FINISH && z2.avail_in == 0) = true
  · rw [ite_t hc]
    refine Sat.bind (Sat.of_eq eld2 ?_)
    by_cases hc2 : (st2.strstart.toInt32 == st2.block_start) = true
    · rw [ite_t hc2]
      exact Sat.pure (sf_post F2 flush _ fun _ => hp2)
    · rw [ite_f hc2]
      exact hfill
  · rw [ite_f hc]
    exact hfill

end ZlibNgF.Proof.StoredSafe

namespace ZlibNgF.Proof.Strategy
open C ZlibNgF.Spec ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts

/-- The three strategies of this branch: `deflate_stored`, `deflate_huff` and `deflate_rle`, given the block
emitters. -/
theorem strategiesA (T : TreesFacts) :
    StratOkP (fun st => st.level = 0) ZlibNg.DeflateStored.deflate_stored ∧
      StratOkP (fun st => 0 < st.level ∧ st.strategy = Z_HUFFMAN_ONLY) ZlibNg.DeflateHuff.deflate_huff ∧
      StratOkP (fun st => 0 < st.level ∧ st.strategy = Z_RLE) ZlibNg.DeflateRle.deflate_rle :=
  ⟨ZlibNgF.Proof.StoredSafe.stored_ok T, ZlibNgF.Proof.DeflateHuffP.huff_ok T, ZlibNgF.Proof.DeflateRleP.rle_ok T⟩

end ZlibNgF.Proof.Strategy
