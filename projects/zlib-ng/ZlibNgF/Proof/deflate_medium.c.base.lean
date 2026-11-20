import ZlibNgF.Proof.«deflate_medium.c.step»
import ZlibNgF.Proof.«deflate_strategy.chain»
import ZlibNgF.Proof.«deflate.c.fill_window.facts»

/-!
# The loop state of `deflate_medium` (`ZlibNgF`)

`deflate_medium` keeps `lookahead` and `strstart` in the state, so between statements its loop state is `SLC` (the
strategy frame with no pending bytes and room for one symbol) together with the hash chains (`ChainAll`): `MG`.

* `chain_adv`: `ChainOk` survives a state that keeps the hash layout, does not move `strstart` back and does not lower
  `chainLim`;
* `sli_congr` / `slw_congr`: `SLI` / `SLW` read the state only with the locals written back;
* `mg_fill`: `fill_window` from `MG`;
* `slf_flush_mg`: `FLUSH_BLOCK` from `SLF` with no pending bytes and the chains;
* `tally_lit_shape` / `tally_dist_shape`: the tallies write only `sym_next`, the two frequency trees and the bytes.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.StrategyChain
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP

/-- The hash chains of block `b` in `H`. -/
def ChainAll (b : Nat) (H : Heap) : Prop :=
  ∀ st d, H.dstate b = some st → H.bytes b = some d → ChainOk b d st

theorem chainAll_SH {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} :
    ChainAll b (SH H0 i z b st d) ↔ ChainOk b d st := by
  constructor
  · intro C; exact C st d (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)
  · intro C st' d' h1 h2
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h1)
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans h2)
    exact C

theorem chainAll_keep {b : Nat} {H H2 : Heap} (K : ChainKeep b H H2) (C : ChainAll b H)
    (hs : ∃ st d, H.dstate b = some st ∧ H.bytes b = some d) : ChainAll b H2 := by
  obtain ⟨st, d, h1, h2⟩ := hs
  exact fun st2 d2 g1 g2 => K st d st2 d2 h1 h2 g1 g2 (C st d h1 h2)

/-- `ChainOk` survives a state with the same hash layout, `strstart` not moved back and `chainLim` not lowered. -/
theorem chain_adv {b : Nat} {d : Array UInt8} {st st' : DeflateState} (C : ChainOk b d st)
    (e1 : st'.level = st.level) (e2 : st'.strategy = st.strategy) (e3 : st'.head = st.head)
    (e4 : st'.prev = st.prev) (e5 : st'.w_size = st.w_size) (hss : st.strstart.toNat ≤ st'.strstart.toNat)
    (hl : chainLim st ≤ chainLim st') : ChainOk b d st' :=
  ZlibNgF.Proof.InsertGrow.ChainOk.grow (S := fun _ => False) C
    (fun ho po _ _ => ZlibNgF.Proof.InsertGrow.Grow.refl d ho po _ _) e1 e2 e3 e4 e5 hss hl
    (fun _ h _ => h.elim)

/-- The loop state of `deflate_medium`. -/
def MG (h : Heap) (i b : Nat) (H : Heap) : Prop := SLC h i b H ∧ ChainAll b H

/-- `SLI` reads the state only with the locals written back. -/
theorem sli_congr {h H0 : Heap} {i b : Nat} {z : ZStream} {st st' : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (e : FS st' la ss = FS st la ss) :
    SLI h i b la ss (SH H0 i z b st' d) := by
  obtain ⟨H1, z1, st1, d1, e0, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e0
  have e2 := congrArg (fun H => H.bytes b) e0
  have e3 := congrArg (fun H => H.streams i) e0
  simp only [SH_dstate, SH_bytes, SH_streams] at e1 e2 e3
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj e3
  refine ⟨H1, z, st', d, ?_, by rw [e]; exact C⟩
  rw [← SH_SH H0 i z z b st st' d d, e0, SH_SH]

/-- `SLW` reads the state only with the locals written back. -/
theorem slw_congr {h H0 : Heap} {i b : Nat} {z : ZStream} {st st' : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (W : SLW h i b la ss (SH H0 i z b st d)) (e : FS st' la ss = FS st la ss) :
    SLW h i b la ss (SH H0 i z b st' d) := by
  obtain ⟨H1, z1, st1, d1, e0, C, hp⟩ := W
  have e1 := congrArg (fun H => H.dstate b) e0
  have e2 := congrArg (fun H => H.bytes b) e0
  have e3 := congrArg (fun H => H.streams i) e0
  simp only [SH_dstate, SH_bytes, SH_streams] at e1 e2 e3
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj e3
  refine ⟨H1, z, st', d, ?_, by rw [e]; exact C, ?_⟩
  · rw [← SH_SH H0 i z z b st st' d d, e0, SH_SH]
  · have := congrArg DeflateState.pending e
    exact this.trans hp

/-- `SLW` of a heap whose state holds the locals is `SLF` with no pending bytes. -/
theorem slw_slf {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (W : SLW h i b st.lookahead st.strstart (SH H0 i z b st d)) :
    SLF h i b (SH H0 i z b st d) ∧ st.pending = 0 := by
  obtain ⟨H1, z1, st1, d1, e, C, hp⟩ := W
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  have e3 := congrArg (fun H => H.streams i) e
  simp only [SH_dstate, SH_bytes, SH_streams] at e1 e2 e3
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj e3
  rw [FS_self, ← e] at C
  exact ⟨C, hp⟩

/-- The input of an invariant stream with valid buffers is readable (`DInput`). -/
theorem dinput_of_io {H : Heap} {i : Nat} (hio : DStreamIO H (some i)) (hset : DBufsSet H (some i)) :
    DInput H (some i) := by
  obtain ⟨z, b, hp, ⟨i2, e2, hz⟩, hb, -, -, hin0, -, -, hdj⟩ := hio
  obtain rfl : i = i2 := Option.some.inj e2
  obtain ⟨z3, ⟨i3, e3, hz3⟩, -, hni⟩ := hset
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  exact ⟨z, b, ⟨i, rfl, hz⟩, hb, hin0, (hdj _ (.inl rfl)).2, hni⟩

/-- `fill_window` from the loop state (with `lookahead < MIN_LOOKAHEAD`): the loop state after, the lookahead plus
the input not grown, and the lookahead full or the input empty. -/
theorem mg_fill {h H : Heap} {i b : Nat} {st : DeflateState} (G : MG h i b H) (hst : H.dstate b = some st)
    (hla : st.lookahead.toNat < 262) :
    Sat H (ZlibNg.Deflate.fill_window (some b)) (fun _ H2 => ∃ H0 z st2 d, H2 = SH H0 i z b st2 d ∧
      MG h i b H2 ∧ avIn H2 i + st2.lookahead.toNat ≤ avIn H i + st.lookahead.toNat ∧
      (st2.lookahead ≠ st.lookahead → avIn H2 i < avIn H i) ∧ st2.w_size = st.w_size ∧
      (262 ≤ st2.lookahead.toNat ∨ z.avail_in = 0)) := by
  obtain ⟨C, Ch⟩ := G
  have I := sli_of_slc C hst
  have I1 := I
  obtain ⟨H0, z, st0, d, rfl, -⟩ := I1
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
  obtain ⟨_, H1, e, q⟩ := sli_fill I hla
  rw [wrD_SH] at e
  obtain rfl : SH H0 i z b (FS st0 st0.lookahead st0.strstart) d = H1 := by
    injection e with e'; injection e'
  rw [FS_self] at q
  obtain ⟨u, H2, e2, ⟨H0', z', st2, d2, rfl, I2, hsum, hne, hend⟩⟩ := q
  obtain ⟨z1, st1, -, hz1, hb, hst1, -, -⟩ := C.1.live
  obtain rfl := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  have Ch2 := ZlibNgF.Proof.FillFacts.fill_window_chain _ _ (some i) b st0 d C.1.inv
    ⟨i, z, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _⟩ (SH_bytes _ _ _ _ _ _)
    (dinput_of_io C.1.io C.1.set) (fun _ => C.1.crc) hla (Ch _ _ (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)) e2
  obtain ⟨H3, e3, FI⟩ := ZlibNgF.Proof.FillIO.fill_io C.1.inv C.1.io C.1.set C.1.crc (SH_streams _ _ _ _ _ _) hb
    (SH_dstate _ _ _ _ _ _) hla
  have e3' : ZlibNg.Deflate.fill_window (some b) (SH H0 i z b st0 d) = .ok ((), H3) := e3
  rw [e2] at e3'
  obtain rfl : SH H0' i z' b st2 d2 = H3 := by injection e3' with e'; injection e'
  obtain ⟨z5, z6, st5, st6, d6, -, hst5, e6, -, fws⟩ := FI.shape
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst5)
  have e7 := congrArg (fun H => H.dstate b) e6
  simp only [SH_dstate] at e7
  obtain rfl := Option.some.inj e7
  have hws := (ZlibNgF.Proof.FillSlide.FWS.keeps fws).2.2.2.2
  refine ⟨u, _, e2, H0', z', st2, d2, rfl, ⟨sli_slc I2, fun st3 d3 h3 h4 => ?_⟩, ?_, ?_, hws, hend⟩
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h3)
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans h4)
    obtain ⟨z5, h5, hb5⟩ := (sli_slc I2).1.blk
    obtain rfl := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans h5)
    exact Ch2 _ _ ⟨i, z', rfl, SH_streams _ _ _ _ _ _, hb5, SH_dstate _ _ _ _ _ _⟩ (SH_bytes _ _ _ _ _ _)
  · rw [avIn_SH, avIn_SH] at *; omega
  · intro h; simpa only [avIn_SH] using hne h

/-- `FLUSH_BLOCK(s, window, last)` from `SLF` with no pending bytes keeps `w_size`. -/
theorem slf_flush_ws (T : TreesFacts) {h H : Heap} {i b wo : Nat} (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1)
    (F : SLF h i b H) (hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo)) :
    Sat H (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun _ H2 =>
      ∀ st st2, H.dstate b = some st → H2.dstate b = some st2 → st2.w_size = st.w_size) := by
  obtain ⟨z, st, -, hz, hb, hst, -, -⟩ := F.live
  obtain ⟨hp0, hwin⟩ := hp st hst
  obtain ⟨hlv, -, -, h8, -⟩ := F.st st hst
  obtain ⟨r, h', e, P, -⟩ := ZlibNgF.Proof.FlushBlock.flush_block_ok T last hl0 hl1 F.inv F.io F.set hz hb hst hp0 hlv
    h8 hwin
  refine ⟨r, h', e, fun st1 st2 h1 h2 => ?_⟩
  obtain rfl := Option.some.inj (hst.symm.trans h1)
  obtain ⟨z', st', L, -, hst', -, -, -, -, -, -, st3, hK1, hst'e⟩ := P.out
  obtain rfl := Option.some.inj (hst'.symm.trans h2)
  have hk : st'.w_size = st.w_size := by rw [hst'e, hK1]
  exact hk

/-- `FLUSH_BLOCK(s, window, last)` from `SLF` with no pending bytes and the chains: `slf_flush` and the chains
after. -/
theorem slf_flush_mg (T : TreesFacts) {h H : Heap} {i b wo : Nat} (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1)
    (F : SLF h i b H) (hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo))
    (Ch : ChainAll b H) (hsy0 : last = 0 → NZ b H) :
    Sat H (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun r H2 => avIn H2 i = avIn H i ∧
      SLFe (lastSlack last) h i b H2 ∧
      ChainAll b H2 ∧ (∀ st st2, H.dstate b = some st → H2.dstate b = some st2 → st2.w_size = st.w_size) ∧
      (∀ st2, H2.dstate b = some st2 → st2.sym_next = 0 ∧ st2.sym_next < st2.sym_end ∧
        ∃ st, H.dstate b = some st ∧ st2.lookahead = st.lookahead ∧ st2.strstart = st.strstart ∧
          st2.window = st.window) ∧
      (r = none → ∀ st2, H2.dstate b = some st2 → st2.pending = 0) ∧
      (r ≠ none → r = some (if last != 0 then .finish_started else .need_more)) ∧ (r ≠ none → O0 H2 i)) := by
  refine Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and (slf_flush T last hl0 hl1 F hp hsy0)
    (ZlibNgF.Proof.MediumStep.Sat.and (slf_flush_chain T last hl0 hl1 F hp) (slf_flush_ws T last hl0 hl1 F hp))) ?_
  rintro r H2 ⟨⟨a1, a2, a3, a4, a5, a6⟩, K, KW⟩
  obtain ⟨z, st, -, -, -, hst, -, -⟩ := F.live
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  exact ⟨a1, a2, chainAll_keep K Ch ⟨st, d, hst, hd⟩, KW, a3, a4, a5, a6⟩

open ZlibNgF.Proof.Tally (W4 tally_lit_SH tally_dist_SH incF) in
/-- `zng_tr_tally_lit` from `SLF` changes only `sym_next`, `dyn_ltree` and the bytes. -/
theorem tally_lit_shape {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (F : SLF h i b (SH H0 i z b (FS st la ss) d)) (hle : st.sym_next ≤ st.sym_end) (c : UInt8) :
    Sat (SH H0 i z b st d) (zng_tr_tally_lit (some b) c) (fun _ H' => ∃ sn lt d',
      H' = SH H0 i z b { st with sym_next := sn, dyn_ltree := lt } d') := by
  obtain ⟨sbo, hsb, hk, hlt, -⟩ := slf_sym F hle
  exact Sat.mono (tally_lit_SH c hsb hk hlt) fun _ _ q => ⟨_, _, _, q.1⟩

open ZlibNgF.Proof.Tally (W4 tally_lit_SH tally_dist_SH incF) in
/-- `zng_tr_tally_dist` from `SLF` changes only `sym_next`, the two trees and the bytes. -/
theorem tally_dist_shape {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (F : SLF h i b (SH H0 i z b (FS st la ss) d)) (hle : st.sym_next ≤ st.sym_end)
    (dist len : UInt32) (hlen : len.toNat < 256) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) :
    Sat (SH H0 i z b st d) (zng_tr_tally_dist (some b) dist len) (fun _ H' => ∃ sn lt dt d',
      H' = SH H0 i z b { st with sym_next := sn, dyn_ltree := lt, dyn_dtree := dt } d') := by
  obtain ⟨sbo, hsb, hk, hlt, hdt⟩ := slf_sym F hle
  exact Sat.mono (tally_dist_SH dist len hlen hd1 hd2 hsb hk hlt hdt) fun _ _ q => ⟨_, _, _, _, q.1⟩

/-- The layout facts of the state of an `SLF` heap (as `MediumStep.sli_lay`). -/
theorem slf_lay {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) :
    ∃ wo po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho ∧ (∃ k, st.w_size.toNat = 2 ^ k) ∧
      512 ≤ st.w_size.toNat ∧ st.w_size.toNat ≤ 32768 ∧
      st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat ∧ st.window_size.toNat ≤ 65536 ∧
      wo + st.window_size.toNat ≤ po ∧ wo + 131400 ≤ d.size ∧
      (∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) → ho + 131072 ≤ pbo) ∧
      (∀ sbo, st.sym_buf = .val (.ref (.heap b) sbo) → ho + 131072 ≤ sbo) := by
  obtain ⟨z2, st2, al, hz2, hb2, hst2, -, c⟩ := F.live
  obtain rfl : st = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
  obtain ⟨wo, po, ho, pbo, L, hwp, hpb, hhp, hsb⟩ := ZlibNgF.Proof.FillFacts.hlay_of c (SH_bytes _ _ _ _ _ _)
  obtain ⟨k, -, -, hk⟩ := c.wpow
  obtain ⟨w1, w2, hws, -⟩ := c.sizes
  have hlook : st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat := c.look
  have hws' : st.window_size = W_BUF_SIZE st.w_size := hws
  have w1' : 512 ≤ st.w_size.toNat := w1
  have w2' : st.w_size.toNat ≤ 32768 := w2
  have h65 : st.window_size.toNat ≤ 65536 := by
    rw [hws', DeflateInit.wbuf_toNat _ w2']; unfold DeflateAlloc.dWS; split <;> omega
  obtain ⟨d3, -, -, -, pbo3, hd3, -, -, -, hpb3, -, -, -, h4, -⟩ := c.lay
  obtain rfl : d = d3 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd3)
  simp only [dview] at hpb3 h4
  rw [hpb] at hpb3
  obtain rfl : pbo = pbo3 := by injection hpb3 with e; injection e
  have hL := L.ph
  have hLw := L.pw
  refine ⟨wo, po, ho, ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩, ⟨k, hk⟩, w1', w2', hlook, h65, hwp,
    by omega, fun p hp => ?_, fun s hs => ?_⟩
  · rw [hpb] at hp; obtain rfl : pbo = p := by injection hp with e; injection e
    exact hhp
  · rw [hsb] at hs; obtain rfl : pbo + st.lit_bufsize.toNat + 8 = s := by injection hs with e; injection e
    omega

open ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop in
/-- An insertion function (any `m` with the post `GPost` under the layout) on an `SLF` heap: `SLF` again on the new
bytes (the state record is kept), and the chains grown. -/
theorem slf_ins {α : Type} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {m : M α} {S : Nat → Prop} (F : SLF h i b (SH H0 i z b st d))
    (hm : ∀ wo po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho → (∃ k, st.w_size.toNat = 2 ^ k) →
      wo + st.window_size.toNat ≤ po → Sat (SH H0 i z b st d) m (GPost H0 i z b st d ho po st.w_size.toNat S)) :
    Sat (SH H0 i z b st d) m (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLF h i b H' ∧ GrowSt b st d d' S) := by
  obtain ⟨wo, po, ho, L, hp, hwp⟩ := slf_hlay F
  refine Sat.mono (hm wo po ho L hp hwp) ?_
  rintro _ _ ⟨d', rfl, w, g⟩
  refine ⟨d', rfl, slf_bytes F fun ho' hh => ?_, fun ho' po' hh hpv => ?_⟩
  · rw [L.head] at hh
    obtain rfl : ho = ho' := by injection hh with e; injection e
    exact w.widen (Nat.zero_le _) (Nat.le_refl _)
  · rw [L.head] at hh; rw [L.prev] at hpv
    obtain rfl : ho = ho' := by injection hh with e; injection e
    obtain rfl : po = po' := by injection hpv with e; injection e
    exact g

open ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop in
/-- `insert_knuth(s, window, str)` on an `SLF` heap. -/
theorem slf_insert_knuth {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (str : UInt32) (hr : str.toNat + 4 ≤ st.window_size.toNat) (hs : str.toNat < 65536) :
    Sat (SH H0 i z b st d) (ZlibNg.InsertStringP.insert_knuth (some b) (.ref (.heap b) wo) str)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLF h i b H' ∧ GrowSt b st d d' (· = str.toNat)) :=
  slf_ins F fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_knuth_G L hp str (by have := L.pw; omega) hs

open ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop in
/-- `insert_match(s, window, m, max_insert_count)` on an `SLF` heap. -/
theorem slf_insert_match {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (m : ZlibNg.DeflateMedium.Match) (mic : UInt32) (hm2 : 2 ≤ mic.toNat) (hm3 : mic.toNat ≤ 258)
    (hl : 2 ≤ m.match_length.toNat) (ho2 : m.orgstart.toNat ≤ m.strstart.toNat + m.match_length.toNat)
    (hs : m.strstart.toNat + m.match_length.toNat ≤ 65536)
    (hr : m.strstart.toNat + m.match_length.toNat + 3 ≤ st.window_size.toNat) :
    Sat (SH H0 i z b st d) (ZlibNg.DeflateMedium.insert_match (some b) (.ref (.heap b) wo) m mic)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLF h i b H' ∧
        GrowSt b st d d' (fun q => m.strstart.toNat < q ∧ q < m.strstart.toNat + m.match_length.toNat)) :=
  slf_ins F fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_match_G L hp m mic hm2 hm3 hl ho2 hs (by have := L.pw; omega)

end ZlibNgF.Proof.MediumLoop
