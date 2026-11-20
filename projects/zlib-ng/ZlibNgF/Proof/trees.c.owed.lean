import ZlibNgF.Proof.«deflate.c.psi»
import ZlibNgF.Proof.«trees.c.facts»
import ZlibNgF.Proof.«trees.c.compress»
import ZlibNgF.Proof.«deflate_p.h.flush»

/-!
# The bytes owed after each block emitter (`ZlibNgF`)

`owed st = pending + (bi_valid + 7) / 8` (`Proof/deflate.c.psi.lean`) counts the pending bytes and the bytes of the
bits waiting in `bi_buf`. For each emitter of `trees.c` / `trees_emit.h` and for `flush_pending`, the change of
`owed`, as companions of the existing statements about the same run:

* on `SH` heaps (`*_owed_SH`): the premises of the matching `_SH` lemma, a `Sat` post about `owed` of the state
  after, which `MediumStep.Sat.and` combines with that lemma's post;
* in the working state (`*_owed`): the premises of the matching `TreesFacts` field, a post about every successful
  run (`RunPost`), which holds of the run that the field gives.

The counts: `zng_tr_emit_tree` 3 bits, `zng_tr_emit_lit` `static_ltree[c].Len` bits (at most 9),
`zng_tr_emit_dist` `matchCost` bits (at most 31), `zng_tr_emit_end_block` 7 bits (exact; with `bi_windup` for
`last != 0`), `zng_tr_align` 10 bits and `zng_tr_flush_bits` (exact: `owed' = (8 pending + bi_valid + 17) / 8`),
`zng_tr_stored_block` 3 bits, the padding to a byte, 4 bytes `LEN` / `NLEN` and the `len` data bytes,
`zng_tr_flush_block` at most `4 * lit_bufsize + 9` in all (`FinPost`), `zng_tr_flush_bits` keeps `owed`, and
`flush_pending` lowers it by exactly the bytes it copies to the output.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesOwed
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateBits ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflatePsi
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- A post `Q st st'` about every successful run of `m` from the working state of stream `s` (block `b`) with `pre`
and `room st` bytes of room after the pending bytes (the premises of `EmitOk`). -/
def RunPost (s : StreamPtr) (b : Nat) (pre : DeflateState → Prop) (room : DeflateState → Nat) (m : M Unit)
    (Q : DeflateState → DeflateState → Prop) : Prop :=
  ∀ (h h' : Heap) (st : DeflateState), DWork h s → DStateIs h s b st → pre st →
    PendRoom b st (room st) (4 * st.lit_bufsize.toNat + 9) → C.run m h = .ok ((), h') →
    ∀ st', DStateIs h' s b st' → Q st st'

/-- `owed` as one quotient of the bit count. -/
theorem owed_bits (st : DeflateState) :
    owed st = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 7) / 8 := by
  unfold owed; omega

/-! ## From the posts of the `_SH` lemmas -/

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- `n` bits counted exactly (`APost`): `owed' = (8 pending + bi_valid + n + 7) / 8`. -/
theorem owed_apost {pbo n K : Nat} {H' : Heap} (q : TreesEmitP.APost H i z b st d pbo n K H') :
    ∀ st', H'.dstate b = some st' →
      owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + n + 7) / 8 := by
  obtain ⟨np, bb, bv, d', rfl, -, hacc, hbv, -, -⟩ := q
  intro st' hs
  rw [SH_dstate] at hs; obtain rfl := Option.some.inj hs
  have e := TreesEmitP.toInt32_toInt bv hbv
  unfold owed; dsimp only; rw [e]; omega

/-- `bi_windup` (`WDPost`): the bit buffer empty, at most `K` more pending bytes. -/
theorem owed_wdpost {pbo K : Nat} {H' : Heap} (q : TreesEmitP.WDPost H i z b st d pbo K H') :
    ∀ st', H'.dstate b = some st' → owed st' ≤ st.pending.toNat + K := by
  obtain ⟨np, bu, d', rfl, -, -, h2⟩ := q
  intro st' hs
  rw [SH_dstate] at hs; obtain rfl := Option.some.inj hs
  unfold owed; dsimp only
  rw [show (0 : Int32).toInt.toNat = 0 from rfl]; omega

/-- `zng_tr_flush_bits` (`FBPost`) keeps `owed`. -/
theorem owed_fbpost {pbo : Nat} {H' : Heap} (q : FBPost H i z b st d pbo H') :
    ∀ st', H'.dstate b = some st' → owed st' = owed st := by
  obtain ⟨d', bb, bv, np, rfl, -, h0, h8, he⟩ := q
  intro st' hs
  rw [SH_dstate] at hs; obtain rfl := Option.some.inj hs
  unfold owed; dsimp only; omega

/-! ## The emitters on `SH` heaps -/

/-- **`zng_tr_flush_bits`** keeps `owed` (premises of `flush_bits_SH`; `owed_flush_bits` is the arithmetic). -/
theorem flush_bits_owed_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (h0 : 0 ≤ st.bi_valid.toInt) (h64 : st.bi_valid.toInt ≤ 64)
    (hroom : pbo + st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ d.size) (hp : st.pending.toNat + 32 < 2 ^ 32) :
    Sat (SH H i z b st d) (ZlibNg.Trees.zng_tr_flush_bits (some b))
      (fun _ H' => ∀ st', H'.dstate b = some st' → owed st' = owed st) :=
  Sat.mono (flush_bits_SH hpb h0 h64 hroom hp) fun _ _ q => owed_fbpost q

/-- **`zng_tr_emit_tree`**: 3 bits, `owed' = (8 pending + bi_valid + 10) / 8 <= owed + 1`. -/
theorem emit_tree_owed_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32)
    (type last : Int32) (ht0 : 0 ≤ type.toInt) (ht2 : type.toInt ≤ 2) (hl : 2 * type.toInt + last.toInt < 2147483648) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_tree (some b) type last)
      (fun _ H' => ∀ st', H'.dstate b = some st' →
        owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 3 + 7) / 8 ∧ owed st' ≤ owed st + 1) :=
  Sat.mono (TreesEmitP.emit_tree_SH hpb h0 h64 hroom hp type last ht0 ht2 hl) fun _ _ q st' hs => by
    have e := owed_apost q st' hs
    exact ⟨e, by rw [e]; unfold owed; omega⟩

/-- **`zng_tr_emit_lit`** with the static tree: `static_ltree[c].Len` bits (at most 9), `owed' <= owed + 2`. -/
theorem emit_lit_owed_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32)
    (c : UInt32) (hc : c.toNat < 256) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_lit (some b) ZlibNg.DeflateQuick.static_ltree_p c)
      (fun _ H' => ∀ st', H'.dstate b = some st' →
        owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + (static_ltree[c.toNat]!).dl.toNat + 7) / 8 ∧
          owed st' ≤ owed st + 2) := by
  have hl : (static_ltree[c.toNat]!).dl.toNat ≤ 9 :=
    UInt16.le_iff_toNat_le.mp (TreesEmitP.sl_len ⟨c.toNat, by omega⟩)
  exact Sat.mono (TreesCompress.emit_lit_exact hpb h0 h64 hroom hp c hc) fun _ _ q st' hs => by
    have e := owed_apost q st' hs
    exact ⟨e, by rw [e]; unfold owed; omega⟩

/-- **`zng_tr_emit_dist`** with the static trees: `matchCost` bits (at most 31), `owed' <= owed + 4`. -/
theorem emit_dist_owed_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32)
    (lc dist : UInt32) (hlc : lc.toNat < 256) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_dist (some b) (.ref .static_ltree 0) (.ref .static_dtree 0)
      lc dist) (fun _ H' => ∀ st', H'.dstate b = some st' →
        owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat +
          TreesCompress.matchCost static_ltree static_dtree lc.toNat (dist.toNat - 1) + 7) / 8 ∧
          owed st' ≤ owed st + 4) := by
  have hmc : TreesCompress.matchCost static_ltree static_dtree lc.toNat (dist.toNat - 1) ≤ 31 :=
    TreesOverlayP.staticMatchCost_le _ _ hlc (TreesCompress.dCodeOf_lt _ (by omega : dist.toNat - 1 < 32768))
  exact Sat.mono (TreesCompress.emit_dist_exact hpb h0 h64 hroom hp lc dist hlc hd1 hd2) fun _ _ q st' hs => by
    have e := owed_apost q st' hs
    exact ⟨e, by rw [e]; unfold owed; omega⟩

/-- **`zng_tr_emit_end_block`** with the static tree: 7 bits for `last == 0`
(`owed' = (8 pending + bi_valid + 14) / 8`), the 7 bits and `bi_windup` otherwise; `owed' <= owed + 1`. -/
theorem end_block_owed_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 16 ≤ d.size) (hp : st.pending.toNat + 16 < 2 ^ 32)
    (last : Int32) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) (.ref .static_ltree 0) last)
      (fun _ H' => ∀ st', H'.dstate b = some st' →
        (last = 0 → owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 7 + 7) / 8) ∧
          owed st' ≤ owed st + 1) := by
  by_cases hl : last = 0
  · exact Sat.mono (TreesEmitP.end_block_SH hpb h0 h64 hroom hp last) fun _ _ q st' hs => by
      have e := owed_apost (q.1 hl) st' hs
      exact ⟨fun _ => e, by rw [e]; unfold owed; omega⟩
  · exact Sat.mono (TreesCompress.end_block_last_exact hpb h0 h64 hroom hp last hl) fun _ _ q st' hs => by
      have e := owed_wdpost q st' hs
      exact ⟨fun h => absurd h hl, by unfold owed at e ⊢; omega⟩

/-- **`zng_tr_emit_align`** (`bi_windup`): the bit buffer goes to the pending bytes, `owed' <= owed`. -/
theorem emit_align_owed_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_align (some b))
      (fun _ H' => ∀ st', H'.dstate b = some st' → owed st' ≤ owed st) := by
  unfold ZlibNg.TreesEmit.zng_tr_emit_align
  exact Sat.mono (TreesEmitP.windup_SH hpb h0 h64 hroom hp) fun _ _ q st' hs => by
    have e := owed_wdpost q st' hs
    unfold owed at e ⊢; omega

/-- **`zng_tr_align`**: 10 bits and `zng_tr_flush_bits`, exactly `owed' = (8 pending + bi_valid + 17) / 8`, so
`owed' <= owed + 2` (premises of `align_SH`). -/
theorem align_owed_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 24 ≤ d.size)
    (hp : st.pending.toNat + 64 < 2 ^ 32) :
    Sat (SH H i z b st d) (ZlibNg.Trees.zng_tr_align (some b))
      (fun _ H' => ∀ st', H'.dstate b = some st' →
        owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 10 + 7) / 8 ∧ owed st' ≤ owed st + 2) := by
  unfold ZlibNg.Trees.zng_tr_align
  refine Sat.bind (Sat.mono (TreesEmitP.emit_tree_SH hpb h0 h64 (by omega) (by omega) _ _ (by decide) (by decide)
    (by decide)) ?_)
  rintro _ _ ⟨np, bb, bv, d1, rfl, w1, hacc1, hbv1, hle1, hge1⟩
  have e1 := TreesEmitP.toInt32_toInt bv hbv1
  refine Sat.bind (Sat.mono (TreesEmitP.end_block_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega)
    (by dsimp only; omega) (by dsimp only; rw [w1.1]; omega) (by dsimp only; omega) 0) ?_)
  rintro _ _ ⟨q, -⟩
  obtain ⟨np2, bb2, bv2, d2, rfl, w2, hacc2, hbv2, hle2, hge2⟩ := q rfl
  dsimp only at w2 hacc2 hle2 hge2
  rw [e1] at hacc2
  have e2 := TreesEmitP.toInt32_toInt bv2 hbv2
  refine Sat.mono (flush_bits_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; rw [e2, w2.1, w1.1]; omega) (by dsimp only; omega)) ?_
  intro _ _ q st' hs
  have e3 := owed_fbpost q st' hs
  have e4 : owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 10 + 7) / 8 := by
    rw [e3]; unfold owed; dsimp only; rw [e2]; omega
  exact ⟨e4, by rw [e4]; unfold owed; omega⟩

/-- **`zng_tr_stored_block`** of `len` bytes: the 3 header bits and the padding (at most
`(8 pending + bi_valid + 10) / 8` bytes in all), `LEN` / `NLEN` and the data, so `owed' <= owed + len + 5`
(premises of `stored_block_X_SH`). -/
theorem stored_owed_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (buf : BPtr) (len : UInt32)
    (hbuf : (buf = .null ∧ len = 0) ∨ ∃ os, buf = .ref (.heap b) os ∧ os + len.toNat ≤ pbo)
    (hroom : pbo + st.pending.toNat + len.toNat + 16 ≤ d.size) (hp : st.pending.toNat + len.toNat + 64 < 2 ^ 32)
    (last : Int32) :
    Sat (SH H i z b st d) (ZlibNg.Trees.zng_tr_stored_block (some b) buf len last)
      (fun _ H' => ∀ st', H'.dstate b = some st' →
        owed st' ≤ (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 3 + 7) / 8 + 4 + len.toNat ∧
          owed st' ≤ owed st + len.toNat + 5) :=
  Sat.mono (TreesEmitP.stored_block_X_SH hpb h0 h64 buf len hbuf hroom hp last) fun _ _ q st' hs => by
    obtain ⟨np2, pend, bu, d', rfl, hpe, hle, hb2, -⟩ := q
    rw [SH_dstate] at hs; obtain rfl := Option.some.inj hs
    unfold owed; dsimp only
    rw [show (0 : Int32).toInt.toNat = 0 from rfl]
    constructor <;> omega

end

/-! ## The emitters in the working state -/

/-- A `Sat` post on `SH` heaps from the working state gives `RunPost`. -/
theorem runPost_of {s : StreamPtr} {b : Nat} {pre : DeflateState → Prop} {room : DeflateState → Nat} {m : M Unit}
    {Q : DeflateState → DeflateState → Prop}
    (H : ∀ h i z st d pbo, TreesEmitP.WCtx h i z b st d pbo → pre st →
      st.pending.toNat + room st ≤ 4 * st.lit_bufsize.toNat + 9 →
      Sat (SH h i z b st d) m (fun _ H' => ∀ st', H'.dstate b = some st' → Q st st')) :
    RunPost s b pre room m Q := by
  intro h h' st hw hs hpre hr1 hrun st' hs'
  obtain ⟨i, z, b', st0, al, rfl, hz, hb, hst, hal, b0, b64, c, -, -⟩ := hw
  obtain ⟨i1, z1, e1, hz1, hb1, hst1⟩ := hs
  obtain rfl := Option.some.inj e1
  rw [hz] at hz1; obtain rfl := Option.some.inj hz1
  rw [hb] at hb1; obtain rfl := (Option.some.inj hb1).symm
  rw [hst] at hst1; obtain rfl := (Option.some.inj hst1).symm
  obtain ⟨pbo1, poo1, hpb1, hpo1, hroom⟩ := hr1
  obtain ⟨-, -, -, -, l2, -, -⟩ := c.sizes
  obtain ⟨d, wo, po, ho, pbo, hd, hw, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  simp only [dview] at l2 hw hp hh hpb h1 h2 h3 h4 hsb hpo hpoo hpe
  obtain rfl := TreesEmitP.pend_inj hpb hpb1
  obtain rfl := TreesEmitP.pend_inj hpo hpo1
  have hst' : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  have v0 : 0 ≤ st.bi_valid.toInt := by have := Int32.le_iff_toInt_le.mp b0; simpa using this
  have v64 : st.bi_valid.toInt < 64 := by have := Int32.lt_iff_toInt_lt.mp b64; simpa using this
  have hwin : ∀ wo1, st.window = .val (.ref (.heap b) wo1) → wo1 + st.strstart.toNat ≤ pbo := by
    intro wo1 hw1
    rw [hw] at hw1; injection hw1 with e; injection e with _ e; subst e
    have := c.look; simp only [dview] at this; omega
  have S := H h i z st d pbo ⟨hpb, h4, l2, v0, v64, hwin⟩ hpre (by omega)
  rw [DeflateReset.SH_self hz hst' hd] at S
  obtain ⟨r, h'', e, q⟩ := S
  rw [show C.run m h = m h from rfl, e] at hrun
  obtain rfl : h'' = h' := (Prod.mk.inj (Except.ok.inj hrun)).2
  obtain ⟨i2, z2, e2, -, -, hst2⟩ := hs'
  exact q st' hst2

section
variable (s : StreamPtr) (b : Nat)

/-- **`emit_tree_owed`** (premises of `TreesFacts.emit_tree`): `owed' = (8 pending + bi_valid + 10) / 8`. -/
theorem emit_tree_owed (last : Int32) (_h0 : 0 ≤ last) (h1 : last ≤ 1) :
    RunPost s b (fun _ => True) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STATIC_TREES last)
      (fun st st' => owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 3 + 7) / 8 ∧
        owed st' ≤ owed st + 1) :=
  runPost_of fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb; have := W.v64
    have hl := Int32.le_iff_toInt_le.mp h1
    exact emit_tree_owed_SH W.hpb W.v0 W.v64 (by omega) (by omega) _ last (by decide) (by decide)
      (by show 2 * (1 : Int32).toInt + last.toInt < _; simp at hl ⊢; omega)

/-- **`emit_lit_owed`** (premises of `TreesFacts.emit_lit`): `static_ltree[c].Len` bits, `owed' <= owed + 2`. -/
theorem emit_lit_owed (c : UInt32) (hc : c < 256) :
    RunPost s b (fun _ => True) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_lit (some b) ZlibNg.DeflateQuick.static_ltree_p c)
      (fun st st' =>
        owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + (static_ltree[c.toNat]!).dl.toNat + 7) / 8 ∧
          owed st' ≤ owed st + 2) :=
  runPost_of fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact emit_lit_owed_SH W.hpb W.v0 W.v64 (by omega) (by omega) c
      (by have := UInt32.lt_iff_toNat_lt.mp hc; simpa using this)

/-- **`emit_dist_owed`** (premises of `TreesFacts.emit_dist`): `matchCost` bits (at most 31), `owed' <= owed + 4`. -/
theorem emit_dist_owed (lc dist : UInt32) (hlc : lc ≤ 255) (hd1 : 1 ≤ dist) (hd2 : dist ≤ 32768) :
    RunPost s b (fun _ => True) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_dist (some b) ZlibNg.DeflateQuick.static_ltree_p
        ZlibNg.DeflateQuick.static_dtree_p lc dist)
      (fun st st' => owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat +
          TreesCompress.matchCost static_ltree static_dtree lc.toNat (dist.toNat - 1) + 7) / 8 ∧
        owed st' ≤ owed st + 4) :=
  runPost_of fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact emit_dist_owed_SH W.hpb W.v0 W.v64 (by omega) (by omega) lc dist
      (by have := UInt32.le_iff_toNat_le.mp hlc; simp at this; omega)
      (by have := UInt32.le_iff_toNat_le.mp hd1; simpa using this)
      (by have := UInt32.le_iff_toNat_le.mp hd2; simpa using this)

/-- **`emit_end_block_owed`** (premises of `TreesFacts.emit_end_block`): `owed' <= owed + 1`, exactly 7 bits for
`last == 0`. -/
theorem emit_end_block_owed (last : Int32) :
    RunPost s b (fun _ => True) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) ZlibNg.DeflateQuick.static_ltree_p last)
      (fun st st' => (last = 0 → owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 7 + 7) / 8) ∧
        owed st' ≤ owed st + 1) :=
  runPost_of fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact end_block_owed_SH W.hpb W.v0 W.v64 (by omega) (by omega) last

/-- **`emit_align_owed`** (premises of `TreesFacts.emit_align`): `owed' <= owed`. -/
theorem emit_align_owed :
    RunPost s b (fun _ => True) (fun _ => 16) (ZlibNg.TreesEmit.zng_tr_emit_align (some b))
      (fun st st' => owed st' ≤ owed st) :=
  runPost_of fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact emit_align_owed_SH W.hpb W.v0 W.v64 (by omega) (by omega)

/-- **`align_owed`** (premises of `TreesFacts.align`): the `Z_PARTIAL_FLUSH` marker,
`owed' = (8 pending + bi_valid + 17) / 8 <= owed + 2`. -/
theorem align_owed :
    RunPost s b (fun _ => True) (fun _ => 16) (ZlibNg.Trees.zng_tr_align (some b))
      (fun st st' => owed st' = (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 10 + 7) / 8 ∧
        owed st' ≤ owed st + 2) :=
  runPost_of fun _ _ _ _ _ _ W _ hr => by
    have := W.pad; have := W.lb
    exact align_owed_SH W.hpb W.v0 W.v64 (by omega) (by omega)

/-- **`stored_owed`** (premises of `TreesFacts.stored_block`): a stored block of `len` bytes,
`owed' <= (8 pending + bi_valid + 10) / 8 + 4 + len <= owed + len + 5`. -/
theorem stored_owed (buf : BPtr) (len : UInt32) (last : Int32) :
    RunPost s b (fun st => WindowBuf b st buf len) (fun st => storedRoom st len)
      (ZlibNg.Trees.zng_tr_stored_block (some b) buf len last)
      (fun st st' => owed st' ≤ (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 3 + 7) / 8 + 4 + len.toNat ∧
        owed st' ≤ owed st + len.toNat + 5) :=
  runPost_of fun _ _ _ st _ pbo W hw hr => by
    have := W.pad; have := W.lb
    have hsr : storedRoom st len = len.toNat + (st.bi_valid.toInt.toNat + 42) / 8 := rfl
    refine stored_owed_SH W.hpb W.v0 W.v64 buf len ?_ (by omega) (by omega) last
    rcases hw with h | ⟨wo, k, hwo, rfl, hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨wo + k, rfl, by have := W.win wo hwo; omega⟩

/-- **`stored_empty_owed`**: the empty stored block of `Z_SYNC_FLUSH` / `Z_FULL_FLUSH`
(`zng_tr_stored_block(s, NULL, 0, last)`): `owed' <= (8 pending + bi_valid + 10) / 8 + 4 <= owed + 5`. -/
theorem stored_empty_owed (last : Int32) :
    RunPost s b (fun _ => True) (fun st => storedRoom st 0)
      (ZlibNg.Trees.zng_tr_stored_block (some b) .null 0 last)
      (fun st st' => owed st' ≤ (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + 3 + 7) / 8 + 4 ∧
        owed st' ≤ owed st + 5) := by
  intro h h' st hw hs _ hr hrun st' hs'
  have := stored_owed s b .null 0 last h h' st hw hs (Or.inl ⟨rfl, rfl⟩) hr hrun st' hs'
  simpa using this

/-- **`flush_block_owed`** (premises of `TreesFacts.flush_block`): any branch of `zng_tr_flush_block` leaves at most
`4 * lit_bufsize + 9` bytes owed (`FinPost`: the bits after fit `pending_buf`), so `owed' <= owed + 4 * lit_bufsize +
9`. -/
theorem flush_block_owed (buf : BPtr) (len : UInt32) (last : Int32) (h0 : 0 ≤ last) (h1 : last ≤ 1) :
    RunPost s b (FlushBlockPre b buf len) (fun _ => 0) (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last)
      (fun st st' => owed st' ≤ 4 * st.lit_bufsize.toNat + 9 ∧ owed st' ≤ owed st + (4 * st.lit_bufsize.toNat + 9)) := by
  intro h h'' st hw hs hpre _ er st'' hs''
  obtain ⟨i, z, d, pbo, al, rfl, hz, hb, hst, hd, hal, c, hpb0, h', e, q⟩ :=
    TreesFactsP.flush_run ZlibNgF.Proof.TreesCodes.buildTreeSpec h0 h1 hw hs hpre
  rw [e] at er
  obtain rfl : h' = h'' := (Prod.mk.inj (Except.ok.inj er)).2
  obtain ⟨dt, st', d', rfl, -, -, -, -, -, -, hacc, -, -⟩ := q
  obtain ⟨i2, z2, e2, -, -, hst2⟩ := hs''
  rw [SH_dstate] at hst2; obtain rfl := Option.some.inj hst2
  have : owed st' ≤ 4 * st.lit_bufsize.toNat + 9 := by unfold owed; omega
  exact ⟨this, by omega⟩

end

/-! ## `flush_pending` -/

section
open ZlibNgF.Proof.DeflateFlush (OH OH_self OH_dstate ldDState_OH rdD_OH wrD_OH wrZ_OH rdZ_OH addb_OH addo_OH)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size)

/-- `flush_pending` on an `SH` heap (premises of `DeflateFlush.flush_SH`): `len` bytes copied to the output, `owed`
lowered by exactly `len`, `avail_out` by `len`. -/
theorem flush_owed_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    {ob oo : Nat} {ad : Array UInt8} {pbo poo lb : Nat}
    (hzb : z.state = some b) (hob : ob ≠ b) (had : H.bytes ob = some ad)
    (hno : z.next_out = .ref (.heap ob) oo) (hoo : oo + z.avail_out.toNat ≤ ad.size)
    (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hpo : st.pending_out = .val (.ref (.heap b) poo))
    (hle : pbo ≤ poo) (hroom : poo - pbo + st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ 4 * lb + 9)
    (hd : pbo + 4 * lb + 64 ≤ d.size) (hlb : lb ≤ 32768)
    (h0 : 0 ≤ st.bi_valid.toInt) (h64 : st.bi_valid.toInt < 64) :
    Sat (SH H i z b st d) (ZlibNg.DeflateP.flush_pending (some i))
      (fun _ H' => ∃ (len : Nat) (z' : ZStream) (st' : DeflateState) (d1 X : Array UInt8),
        H' = OH H i z' b st' d1 ob X ∧ owed st' + len = owed st ∧ z'.avail_out.toNat + len = z.avail_out.toNat) := by
  unfold ZlibNg.DeflateP.flush_pending ZlibNg.DeflateP.flush_pending_inline
  refine Sat.bind (Sat.of_eq (by simp only [dstateOf]; exact rdZ_SH _) ?_); try dsimp only
  rw [hzb]
  refine Sat.bind (Sat.mono (flush_bits_SH (pbo := pbo) hpb h0 (by omega) (by omega) (by omega)) ?_)
  rintro _ _ ⟨d1, bb, bv, np, rfl, w1, hb0, hb8, hnp⟩
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  refine Sat.bind (Sat.of_eq ldStream_SH ?_); try dsimp only
  have hd1 : d1.size = d.size := w1.1
  obtain ⟨L, hL, hLn⟩ : ∃ L : UInt32, (if np > z.avail_out then z.avail_out else np) = L ∧
      L.toNat = min np.toNat z.avail_out.toNat := by
    refine ⟨_, rfl, ?_⟩
    split
    · rename_i hc; have := UInt32.lt_iff_toNat_lt.mp hc; omega
    · rename_i hc; have := UInt32.not_lt.mp hc; have := UInt32.le_iff_toNat_le.mp this; omega
  rw [hL]
  by_cases hL0 : L = 0
  · simp only [hL0, beq_self_eq_true, ↓reduceIte]
    refine Sat.pure ⟨0, z, { st with pending := np, bi_buf := bb, bi_valid := bv }, d1, ad, ?_, ?_, rfl⟩
    · rw [OH_self hob had]
    · unfold owed; dsimp only; omega
  · have hLb : (L == 0) = false := by simpa using hL0
    simp only [hLb, Bool.false_eq_true, ↓reduceIte]
    have hL1 : L.toNat ≠ 0 := fun e => hL0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
    simp only [hpo, Ival.get, pure_bind_M, hno]
    have hX := copyFold_size d1 oo poo (List.range' 0 L.toNat) ad
    refine Sat.bind (Sat.of_eq (DeflateFlush.memcpy_SH hob had (by omega) (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (addo_OH _ (by omega)) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrZ_OH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (addb_OH hob _ (by omega)) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_OH hob _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrZ_OH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrZ_OH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_OH hob _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (ldDState_OH hob) ?_); try dsimp only
    have hsub : (np - L).toNat = np.toNat - L.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    have hav : (z.avail_out - L).toNat = z.avail_out.toNat - L.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    split
    · refine Sat.of_eq (wrD_OH hob _) ⟨L.toNat, _, _, d1, _, rfl, ?_, ?_⟩
      · unfold owed; dsimp only; rw [hsub]; omega
      · dsimp only; rw [hav]; omega
    · refine Sat.pure ⟨L.toNat, _, _, d1, _, rfl, ?_, ?_⟩
      · unfold owed; dsimp only; rw [hsub]; omega
      · dsimp only; rw [hav]; omega

/-- **`flush_pending_owed`** (premises of `DeflateFlush.flush_work`): every run of `flush_pending` lowers `owed` by
exactly the bytes it copies to the output, the drop of `avail_out` (`zng_tr_flush_bits` first keeps `owed`). -/
theorem flush_pending_owed {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (hw : DWork h (some i))
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st)
    (hout : WriteSlice h z.next_out z.avail_out.toNat) (hnb : NotInBlock b z.next_out) :
    ∀ h', C.run (ZlibNg.DeflateP.flush_pending (some i)) h = .ok ((), h') →
      ∀ z' st', h'.streams i = some z' → h'.dstate b = some st' →
        z'.avail_out.toNat ≤ z.avail_out.toNat ∧ owed st' + (z.avail_out.toNat - z'.avail_out.toNat) = owed st := by
  intro h' hrun z' st' hz' hst'
  obtain ⟨i', z0, b0, st0, al, e0, hz0, hb0, hst0, hal, v0, v64, c, R1, -⟩ := hw
  obtain rfl : i = i' := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨-, -, -, -, l2, -, -⟩ := c.sizes
  obtain ⟨d, wo, po, ho, pbo, hd, hwo, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, -⟩ := c.lay
  simp only [dview] at l2 hpb h4 hpo hpoo
  obtain ⟨pbo1, poo1, hp1, ho1, hq1⟩ := R1
  rw [hpb] at hp1; rw [hpo] at ho1
  obtain rfl : pbo = pbo1 := by injection hp1 with e1; injection e1
  obtain rfl : poo = poo1 := by injection ho1 with e1; injection e1
  obtain ⟨ob, oo, ad, hno, had, hoo⟩ := hout
  have hob : ob ≠ b := fun e => hnb oo (by rw [hno, e])
  have hsts : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  have v0' : 0 ≤ st.bi_valid.toInt := by have := Int32.le_iff_toInt_le.mp v0; simpa using this
  have v64' : st.bi_valid.toInt < 64 := by have := Int32.lt_iff_toInt_lt.mp v64; simpa using this
  have S := flush_owed_SH (H := h) (i := i) (d := d) (lb := st.lit_bufsize.toNat) hb hob had hno hoo hpb hpo hpoo
    hq1 h4 l2 v0' v64'
  rw [ZlibNgF.Proof.DeflateReset.SH_self hz hsts hd] at S
  obtain ⟨r, h'', e, L, z'', st'', d1, X, rfl, ho, ha⟩ := S
  rw [show C.run (ZlibNg.DeflateP.flush_pending (some i)) h = ZlibNg.DeflateP.flush_pending (some i) h from rfl,
    e] at hrun
  obtain rfl := (Prod.mk.inj (Except.ok.inj hrun)).2
  rw [OH_dstate hob] at hst'; obtain rfl := Option.some.inj hst'
  have : (OH h i z'' b st'' d1 ob X).streams i = some z'' := by simp [OH]
  rw [this] at hz'; obtain rfl := Option.some.inj hz'
  omega

/-- `flush_pending_owed` with the premises of `DeflateFlush.flush_ok` (valid and set buffers). -/
theorem flush_pending_owed' {h : Heap} {i : Nat} (hw : DWork h (some i)) (hio : DStreamIO h (some i))
    (hset : DBufsSet h (some i)) :
    ∀ h', C.run (ZlibNg.DeflateP.flush_pending (some i)) h = .ok ((), h') →
      ∀ z b st z' st', h.streams i = some z → z.state = some b → h.dstate b = some st →
        h'.streams i = some z' → h'.dstate b = some st' →
        z'.avail_out.toNat ≤ z.avail_out.toNat ∧ owed st' + (z.avail_out.toNat - z'.avail_out.toNat) = owed st := by
  intro h' hrun z b st z' st' hz hb hst hz' hst'
  obtain ⟨z1, ⟨i1, e1, hz1⟩, hnn, -⟩ := hset
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain ⟨z2, b2, -, ⟨i2, e2, hz2⟩, hb2, -, -, -, hout, hnb, -⟩ := hio
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb.symm.trans hb2)
  exact flush_pending_owed hw hz hb hst (hout.resolve_left hnn) hnb h' hrun z' st' hz' hst'

end

end ZlibNgF.Proof.TreesOwed
