import ZlibNgF.Proof.«chunkset.copy»
import ZlibNgF.Proof.«inflate.c.facts»
import ZlibNgF.Proof.«inffast.main»

/-!
# `CopyFacts`, `FastFacts` and the `LEN` tables (`ZlibNgF`)

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

/-! ## `FastFacts` -/

open ZlibNgF.Spec ZlibNgF.Proof.InflateInv in
/-- `InflateFacts.FastFacts`, given the distance-base fact that `codeTable_dist` needs on the distance table of a state
in `LEN` (a base entry, `op & 16`, of the distance table has `val ≥ 1`). `CodeTable` asks it only of entries with
`(op & 64) == 0`; `zng_inflate_table` and `distfix` never make an entry with both bits, but the invariant does not
say so. -/
theorem fastFacts_of
    (hv : ∀ (h : Heap) (i b : Nat) (z : ZStream) (st : InflateState), Inv h (some i) → h.streams i = some z →
      z.state = some b → h.istate b = some st → st.mode = ZlibNg.Inflate.LEN →
      ∀ (r : CodeRef) (o : Nat) (T : Array Code), st.distcode = .val (.ref r o) → Space.get h r = some T →
        ∀ j, o ≤ j → j < T.size → Base T[j]! → 1 ≤ (T[j]!).val.toNat) :
    ZlibNgF.Proof.InflateFacts.FastFacts := by
  refine ⟨fun safe h i b z st start ri oi bo oo hinv hz hzs hst hmode hbits hin15 hroom hstart hni hrd hno hwr _ _
    hbo => ?_⟩
  have hinv' := hinv
  obtain ⟨i', z0, b0, st0, al, hi, hz0, hb0, hst0, -, core⟩ := hinv'
  cases hi
  rw [hz] at hz0; cases hz0
  rw [hzs] at hb0; cases hb0
  rw [hst] at hst0; cases hst0
  obtain ⟨woff, wd, hwv, -, hwd, hws⟩ := core.window
  have hwb := core.wbufsize
  have hwz := core.wsize
  have hws' : woff + st.wsize.toNat ≤ wd.size := by
    have e1 : (view st).wbufsize.toNat = 32832 := by rw [hwb]; rfl
    have e2 : (view st).wsize.toNat ≤ 32768 := UInt32.le_iff_toNat_le.mp hwz
    have : (view st).wbufsize = st.wbufsize := rfl
    have : (view st).wsize = st.wsize := rfl
    simp only [view] at e1 e2 hws ⊢
    omega
  obtain ⟨hl, hd⟩ := core.modes.decode (Or.inr (Or.inl hmode))
  obtain ⟨lc, dc, hlc, hdc, htab⟩ := tabAt_fast hst hl hd (hv h i b z st hinv hz hzs hst hmode)
  have hnb : ∀ (p : CodePtr) (q : Ival CodePtr), (∃ p', q = .val p' ∧ CodeTarget b p') → q = .val p →
      ∀ r o b', p = .ref r o → r = .codes b' → b' ≠ bo := by
    rintro p q ⟨p', hq, ht⟩ hp r o b' rfl rfl
    rw [hp] at hq; cases hq
    rcases ht with ⟨o', he, -⟩ | he | he <;> cases he
    exact fun e => hbo e.symm
  obtain ⟨r1, off1, A, hr1, hA, hAs⟩ := hrd
  rw [hni] at hr1; cases hr1
  obtain ⟨b1, off2, D, hr2, hD, hDs⟩ := hwr
  cases hr2
  have hroom' : if safe then 3 ≤ z.avail_out else 260 ≤ z.avail_out := by
    cases safe
    · exact hroom
    · exact hroom.1
  obtain ⟨_, h', e, ai, ao, m, hold, bits, len, was, off, msg, -, rest⟩ := InffastMain.inflate_fast_post safe h i b z st
    start ri oi bo oo A D hmode hz hzs hst hbits hbo woff wd hwv hwd hws' core.whave core.wnext_le lc dc hlc hdc htab
    (hnb lc _ core.lencode hlc) (hnb dc _ core.distcode hdc) hin15 hstart hroom' hni hA hAs hno hD hDs
  refine ⟨h', ai, ao, m, hold, bits, len, was, off, msg, ?_, rest⟩
  cases safe <;> exact e

end ZlibNgF.Proof.InffastFacts
