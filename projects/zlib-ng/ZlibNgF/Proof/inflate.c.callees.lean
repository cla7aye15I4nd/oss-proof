import ZlibNgF.Proof.«inffast.c.facts»

/-!
# The callee facts of `inflate` as theorems (`ZlibNgF`)

`fastFacts`: `InflateFacts.FastFacts` without hypotheses. The distance-base fact that `codeTable_dist` asks of the
distance table of `LEN` (`op & 16` gives `val ≥ 1`) follows from `EntryOK.dval` for the entries of the table's
region. `copyFacts` (`Proof/inffast.c.facts.lean`) proves `CopyFacts`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastFacts
open C
open ZlibNgF.Proof.InflateSync (Sat)
open ZlibNgF.Proof.InflateTab (CodeTable TabAt linkTest LenOK EntryOK)
open ZlibNgF.Proof.InffastBase (Tab LenEnt LenLink DistEnt DistLink Base FastTableOK)

/-- `FastTableOK` of the tables of a state from their `TabAt` clauses. -/
theorem tabAt_fast' {H : Heap} {b : Nat} {st : InflateState} (hst : H.istate b = some st)
    (hl : TabAt b st.codes st.lencode st.lenbits 28 false) (hd : TabAt b st.codes st.distcode st.distbits 28 true) :
    ∃ lc dc, st.lencode = .val lc ∧ st.distcode = .val dc ∧ FastTableOK H lc st.lenbits dc st.distbits := by
  have hc : Space.get H (CodeRef.codes b) = some st.codes := by
    show (H.istate b).map (·.codes) = _; rw [hst]; rfl
  have L : ∃ r o T e, st.lencode = .val (.ref r o) ∧ Space.get H r = some T ∧
      CodeTable T o e st.lenbits.toNat 28 false := by
    rcases hl with ⟨o, e, h1, h2⟩ | ⟨h1, e, h2⟩ | ⟨h1, e, h2⟩
    · exact ⟨_, o, _, e, h1, hc, h2⟩
    · exact ⟨.lenfix, 0, _, e, h1, rfl, h2⟩
    · exact ⟨.distfix, 0, _, e, h1, rfl, h2⟩
  have D : ∃ r o T e, st.distcode = .val (.ref r o) ∧ Space.get H r = some T ∧
      CodeTable T o e st.distbits.toNat 28 true := by
    rcases hd with ⟨o, e, h1, h2⟩ | ⟨h1, e, h2⟩ | ⟨h1, e, h2⟩
    · exact ⟨_, o, _, e, h1, hc, h2⟩
    · exact ⟨.lenfix, 0, _, e, h1, rfl, h2⟩
    · exact ⟨.distfix, 0, _, e, h1, rfl, h2⟩
  obtain ⟨rl, ol, Tl, el, hl1, hl2, tl⟩ := L
  obtain ⟨rd, od, Td, ed, hd1, hd2, td⟩ := D
  have := tl.n_le
  have := td.n_le
  exact ⟨_, _, hl1, hd1, by omega, by omega, ⟨rl, ol, Tl, rfl, hl2, codeTable_len tl⟩,
    ⟨rd, od, Td, rfl, hd2, codeTable_dist td fun j h1 h2 hb =>
      (td.ent j h1 h2).dval rfl (Or.inr fun h0 => hb ((and16_iff _).mpr h0))⟩⟩

open ZlibNgF.Spec ZlibNgF.Proof.InflateInv in
/-- **`FastFacts`**: `inflate_fast_c` / `inflate_fast_safe_c` as `LEN` calls them. -/
theorem fastFacts : ZlibNgF.Proof.InflateFacts.FastFacts := by
  refine ⟨fun safe h i b z st start ri oi bo oo hinv hz hzs hst hmode hin15 hroom hstart hni hrd hno hwr _ _
    hbo => ?_⟩
  have hinv' := hinv
  obtain ⟨i', z0, b0, st0, al, hi, hz0, hb0, hst0, -, core⟩ := hinv'
  cases hi
  rw [hz] at hz0; cases hz0
  rw [hzs] at hb0; cases hb0
  rw [hst] at hst0; cases hst0
  have hb39 : st.bits ≤ 39 := core.bits
  have hbits : st.bits < 64 := by rw [UInt32.le_iff_toNat_le] at hb39; rw [UInt32.lt_iff_toNat_lt]; simp at hb39 ⊢; omega
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
  obtain ⟨lc, dc, hlc, hdc, htab⟩ := tabAt_fast' hst hl hd
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
  obtain ⟨_, h', e, ai, ao, m, hold, bits, len, was, off, msg, -, r1, r2, r3, r4, r5, r6, rest⟩ :=
    InffastMain.inflate_fast_post safe h i b z st
    start ri oi bo oo A D hmode hz hzs hst hbits hbo woff wd hwv hwd hws' core.whave core.wnext_le lc dc hlc hdc htab
    (hnb lc _ core.lencode hlc) (hnb dc _ core.distcode hdc) hin15 hstart hroom' hni hA hAs hno hD hDs
  have r6' : bits ≤ 39 := by
    rw [UInt32.le_iff_toNat_le] at hb39 ⊢
    rcases r6 with r6 | r6 <;> rw [UInt32.lt_iff_toNat_lt] at r6 <;> simp at r6 hb39 ⊢ <;> omega
  refine ⟨h', ai, ao, m, hold, bits, len, was, off, msg, ?_, r1, r2, r3, r4, r5, r6', rest⟩
  cases safe <;> exact e

end ZlibNgF.Proof.InffastFacts
