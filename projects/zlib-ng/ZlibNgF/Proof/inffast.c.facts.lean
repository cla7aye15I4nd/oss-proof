import ZlibNgF.Proof.«chunkset.copy»
import ZlibNgF.Proof.«inflate.c.facts»
import ZlibNgF.Proof.«inffast.base»

/-!
# The `CopyFacts` statement for `chunkmemset_safe_c` (`ZlibNgF`)

`copyFacts` proves `InflateFacts.CopyFacts`: `chunkmemset_safe_c` as `MATCH` calls it. `CHUNKMEMSET` computes
`out - from` (`chunkset_tpl.h:118`), a `ptrdiff_t` (ISO C17 §6.5.6p9) because `d < 2 ^ 63`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastFacts
open C
open ZlibNgF.Proof.InflateSync (Sat)
open ZlibNgF.Proof.ChunkMem
open ZlibNgF.Proof.ChunkCopy

theorem copyFacts : ZlibNgF.Proof.InflateFacts.CopyFacts := by
  refine ⟨fun h bo p d data len left hd hd1 hd63 hdp hl hll _ => ?_⟩
  obtain ⟨q, H', e, hq, r⟩ := chunkmemset_safe_c_safe hd rfl (o := p) (f := p - d) (by omega) len left hl (by omega)
  have hmin : min len.toNat left.toNat = len.toNat := by
    rw [UInt64.le_iff_toNat_le] at hll; omega
  obtain ⟨a0, a, e0, e1, s0, s1, hp⟩ := r.blk
  rw [hd] at e0; cases e0
  refine ⟨a, ?_, s1.trans s0.symm, hp⟩
  have heq := r.eq
  rw [e1] at heq
  rw [hq, hmin, heq] at e
  exact e

/-! ## The decoding tables of `LEN` and `FastTableOK` -/

open ZlibNgF.Proof.InflateTab (CodeTable TabAt linkTest LenOK EntryOK)
open ZlibNgF.Proof.InffastBase (Tab LenEnt LenLink DistEnt DistLink Base FastTableOK)

theorem and16_iff : ∀ x : UInt8, (x.toUInt32 &&& 16 = 0) ↔ (x &&& 16 = 0) := by decide
theorem and64_iff : ∀ x : UInt8, (x.toUInt32 &&& 64 = 0) ↔ (x &&& 64 = 0) := by decide
theorem andf0_lt : ∀ x : UInt8, x &&& 0xf0 = 0 → x.toNat < 16 := by decide

theorem lenOK_ent {pre : Nat} {e : Code} (h : LenOK pre e) (h1 : 1 ≤ pre + e.bits.toNat) : LenEnt pre e := by
  refine ⟨h.1, h.2.1, fun hb => h.2.2 ?_, h1⟩
  intro h0; exact hb ((and16_iff _).mpr h0)

theorem lenLink_test {e : Code} {m : Nat} (E : EntryOK e m false) (h : LenLink e) : linkTest false e = true := by
  obtain ⟨h0, h16, h64⟩ := h
  have := E.op_lt ((and16_iff _).mp h16) ((and64_iff _).mp h64)
  simp [linkTest, h0, this]

theorem distLink_test {e : Code} {m : Nat} (E : EntryOK e m true) (h : DistLink e) : linkTest true e = true := by
  obtain ⟨h16, h64⟩ := h
  have := E.op_lt ((and16_iff _).mp h16) ((and64_iff _).mp h64)
  simp [linkTest, this]

/-- A literal/length `CodeTable` (at most 28 bits per code) is a `Tab` for `inflate_fast`. -/
theorem codeTable_len {a : Array Code} {o e n : Nat} (t : CodeTable a o e n 28 false) : Tab a o n LenEnt LenLink := by
  have hr := t.root
  have hf := t.fits
  refine ⟨by omega, fun k hk => ?_⟩
  have E := t.ent (o + k) (by omega) (by omega)
  have E1 : 1 ≤ (a[o + k]!).bits.toNat := Nat.le_trans E.cb_pos E.cb_le
  refine ⟨lenOK_ent (t.lit rfl _ (by omega) (by omega)) (by omega), fun hl => ?_⟩
  have hlt := lenLink_test E hl
  obtain ⟨hsz, hsub⟩ := t.link (o + k) (by omega) (by omega) hlt
  have h16 : (a[o + k]!).op &&& 0xf0 = 0 := by
    obtain ⟨_, h16, h64⟩ := hl
    exact E.op_lt ((and16_iff _).mp h16) ((and64_iff _).mp h64)
  refine ⟨andf0_lt _ h16, by omega, fun j hj => ?_⟩
  obtain ⟨_, hnl, hok⟩ := hsub j hj
  refine ⟨lenOK_ent (hok rfl) (by omega), fun hl' => ?_⟩
  have E' := t.ent (o + (a[o + k]!).val.toNat + j) (by omega) (by omega)
  rw [lenLink_test E' hl'] at hnl
  exact absurd hnl (by decide)

/-- A distance `CodeTable` (at most 28 bits per code) is a `Tab` for `inflate_fast`, given that its base entries
(`op & 16`) have a nonzero `val`. `CodeTable` asks `val ≥ 1` only of entries with `(op & 64) == 0`: the slow decoder
tests `op & 64` first, `inflate_fast` tests `op & 16` first (`inffast_tpl.h:194`), so an entry with both bits and
`val = 0` would be read as a distance of `extra` (possibly 0) by `inflate_fast`. -/
theorem codeTable_dist {a : Array Code} {o e n : Nat} (t : CodeTable a o e n 28 true)
    (hv : ∀ j, o ≤ j → j < e → Base a[j]! → 1 ≤ (a[j]!).val.toNat) : Tab a o n DistEnt DistLink := by
  have hr := t.root
  have hf := t.fits
  refine ⟨by omega, fun k hk => ⟨⟨by have := (t.ent (o + k) (by omega) (by omega)).bits_le; omega,
    hv _ (by omega) (by omega)⟩, fun hl => ?_⟩⟩
  have E := t.ent (o + k) (by omega) (by omega)
  have hlt := distLink_test E hl
  obtain ⟨hsz, hsub⟩ := t.link (o + k) (by omega) (by omega) hlt
  have h16 : (a[o + k]!).op &&& 0xf0 = 0 := by
    obtain ⟨h16, h64⟩ := hl
    exact E.op_lt ((and16_iff _).mp h16) ((and64_iff _).mp h64)
  refine ⟨andf0_lt _ h16, by omega, fun j hj => ?_⟩
  obtain ⟨hb, hnl, -⟩ := hsub j hj
  refine ⟨⟨hb, hv _ (by omega) (by omega)⟩, fun hl' => ?_⟩
  have E' := t.ent (o + (a[o + k]!).val.toNat + j) (by omega) (by omega)
  rw [distLink_test E' hl'] at hnl
  exact absurd hnl (by decide)

/-- The tables of a state in `LEN` (`ModeOK.decode`) satisfy `FastTableOK` on the values `inflate_fast` reads, given
the base-entry fact `codeTable_dist` needs for the distance table. -/
theorem tabAt_fast {H : Heap} {b : Nat} {st : InflateState} (hst : H.istate b = some st)
    (hl : TabAt b st.codes st.lencode st.lenbits 28 false) (hd : TabAt b st.codes st.distcode st.distbits 28 true)
    (hv : ∀ (r : CodeRef) (o : Nat) (T : Array Code), st.distcode = .val (.ref r o) → Space.get H r = some T →
      ∀ j, o ≤ j → j < T.size → Base T[j]! → 1 ≤ (T[j]!).val.toNat) :
    ∃ lc dc, st.lencode = .val lc ∧ st.distcode = .val dc ∧ FastTableOK H lc st.lenbits dc st.distbits := by
  have hc : Space.get H (CodeRef.codes b) = some st.codes := by
    show (H.istate b).map (·.codes) = _; rw [hst]; rfl
  have L : ∃ r o T e, st.lencode = .val (.ref r o) ∧ Space.get H r = some T ∧ CodeTable T o e st.lenbits.toNat 28 false := by
    rcases hl with ⟨o, e, h1, h2⟩ | ⟨h1, e, h2⟩ | ⟨h1, e, h2⟩
    · exact ⟨_, o, _, e, h1, hc, h2⟩
    · exact ⟨.lenfix, 0, _, e, h1, rfl, h2⟩
    · exact ⟨.distfix, 0, _, e, h1, rfl, h2⟩
  have D : ∃ r o T e, st.distcode = .val (.ref r o) ∧ Space.get H r = some T ∧ CodeTable T o e st.distbits.toNat 28 true := by
    rcases hd with ⟨o, e, h1, h2⟩ | ⟨h1, e, h2⟩ | ⟨h1, e, h2⟩
    · exact ⟨_, o, _, e, h1, hc, h2⟩
    · exact ⟨.lenfix, 0, _, e, h1, rfl, h2⟩
    · exact ⟨.distfix, 0, _, e, h1, rfl, h2⟩
  obtain ⟨rl, ol, Tl, el, hl1, hl2, tl⟩ := L
  obtain ⟨rd, od, Td, ed, hd1, hd2, td⟩ := D
  have := tl.n_le
  have := td.n_le
  have := td.fits
  exact ⟨_, _, hl1, hd1, by omega, by omega, ⟨rl, ol, Tl, rfl, hl2, codeTable_len tl⟩,
    ⟨rd, od, Td, rfl, hd2, codeTable_dist td fun j h1 h2 hb => hv rd od Td hd1 hd2 j h1 (by omega) hb⟩⟩

end ZlibNgF.Proof.InffastFacts
