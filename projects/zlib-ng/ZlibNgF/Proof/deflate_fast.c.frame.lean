import ZlibNgF.Proof.«insert_string_p.h.slw»
import ZlibNgF.Proof.«deflate_strategy.chain»

/-!
# The strategy frame at a level other than 1 (`ZlibNgF`)

`deflate_fast` runs at level 2 with any strategy but `Z_HUFFMAN_ONLY` and `Z_RLE`, `Z_FIXED` included. The entry and
exit lemmas of `Proof/deflate_strategy.common.lean` (`sli_entry`, `slf_post`, `slc_post`) take a strategy
other than `Z_FIXED`, which they use only to rule out the level-1 clauses of `SymsOk`; a level other than 1 rules them
out as well. The lemmas here take level 2 instead (`…_l`); `LazyOk` follows from `StratKeeps` (level 2 is not
`deflate_slow`'s).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FastFrame
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP

/-- `slf_post` for a strategy entered at level 2 (any strategy, `Z_FIXED` included). -/
theorem slf_post_l {h H : Heap} {i b : Nat} (F : SLF h i b H) (flush : Int32) (bs : BlockState)
    (hn : ∀ st0, h.dstate b = some st0 → st0.level = 2) (hx : ExitIO H i flush bs)
    (hs : ∀ st, H.dstate b = some st → ExitOk flush bs st) : StratPost h (some i) flush bs H := by
  refine slf_postL F flush bs hx (fun st0 h0 e => absurd ((hn st0 h0).symm.trans e) (by decide))
    (fun st0 h0 L st hst => ?_) hs
  obtain ⟨st1, h1, hk⟩ := F.keeps
  obtain rfl : st0 = st1 := Option.some.inj (h0.symm.trans h1)
  have hT : ¬ TableAt 7 9 st0 := fun ht => by
    have := ht.1; rw [hn st0 h0] at this; exact absurd this (by decide)
  obtain ⟨L', hm⟩ := (hk st hst).lazy L hT
  exact ⟨L', fun _ => hm⟩

/-- `sli_entry` for a strategy entered at a level above 1. -/
theorem sli_entry_l {h : Heap} {i b : Nat} {z : ZStream} {flush : Int32} (P : StratPre h (some i) flush)
    (hz : h.streams i = some z) (hb : z.state = some b)
    (hE : ∀ b' st, DStateIs h (some i) b' st → 0 < st.level ∧ st.level ≠ 1) :
    ∃ st, h.dstate b = some st ∧ SLI h i b st.lookahead st.strstart h := by
  obtain ⟨hv, hcrc, hio, hset, -, -, b1, st1, ⟨i1, z1, e1, hz1, hb1, hst1⟩, hp0, hs1, ⟨hsym, -, -, hg2, hg8⟩, -⟩ := P
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  have hD : DStateIs h (some i) b st1 := ⟨i, z, rfl, hz, hb, hst1⟩
  obtain ⟨hlv, hl1⟩ := hE b st1 hD
  have hgap : GapOk st1 := ⟨hg2, Int32.not_le.mp fun e8 => hl1 (hg8 e8).1⟩
  refine ⟨st1, hst1, sli_of_slc ⟨⟨hv, hio, hset, hcrc, ⟨z, hz, hb⟩, ⟨z, hz, hb⟩, dframe_refl _ _ _ _ _, ?_,
    InTail.refl hz hz rfl rfl, ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; rfl⟩,
    ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; exact StratKeeps.refl _⟩, fun st h1 => ?_⟩,
    fun st h1 => ?_⟩ hst1⟩
  · have hio0 := hio
    obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, -, hout, hnb, -⟩ := hio0
    obtain rfl : i = i2 := Option.some.inj e2
    obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
    obtain ⟨z3, ⟨i3, e3, hz3⟩, hnn, -⟩ := hset
    obtain rfl : i = i3 := Option.some.inj e3
    obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
    obtain ⟨ob, oo, ad, hno, -, -⟩ := hout.resolve_left hnn
    exact ⟨z, z, ob, oo, 0, hz, hz, hno, hno, rfl⟩
  · obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans h1)
    exact ⟨hlv, hs1, hgap⟩
  · obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans h1)
    exact ⟨hp0, hsym⟩

/-- `slc_post` at level 2. -/
theorem slc_post_l {h H : Heap} {i b : Nat} (C : SLC h i b H) (hn : ∀ st0, h.dstate b = some st0 → st0.level = 2)
    (hc : CF H i) : StratPost h (some i) Z_NO_FLUSH .need_more H := by
  refine slf_post_l C.1 _ _ hn (exitIO_nmNF hc) fun st2 h2 => ⟨(C.2 st2 h2).2, ?_, ?_, ?_, ?_⟩
  · intro e; rcases e with e | e <;> cases e
  · intro e; exact absurd rfl e
  · intro e; rcases e with e | e <;> cases e
  · intro e; cases e

end ZlibNgF.Proof.FastFrame
