import ZlibNgF.Proof.«inftrees.c.table»
import ZlibNgF.Proof.«inflate.c.facts»

/-!
# `zng_inflate_table` as `inflate` calls it (`ZlibNgF`)

`table_run`: the three calls of `inflate` (`TableCall`, lengths at most 7 for the code length code and 15 otherwise)
end without fault, change only the `codes` and `work` arrays of the state, keep the entries before the table start,
and on success return a table end `o'` with room for the root table, within `ENOUGH_LENS` / `ENOUGH_DISTS` of the
start. This is `TableFacts` without its `CodeTable` conclusion.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP
open ZlibNgF.Proof.InflateFacts (TableCall)

theorem LiveSt.of_istate {h : Heap} {b : Nat} {s : InflateState} (hi : h.istate b = some s) : LiveSt h b s := by
  unfold Heap.istate at hi
  cases e : h.bytes b with
  | none => rw [e] at hi; cases hi
  | some _ => rw [e] at hi; exact ⟨by rw [e]; rfl, hi⟩

/-- `TableCall` with lengths in range gives the precondition of `zng_inflate_table_wp`. -/
theorem TblPre.of_call {h : Heap} {b : Nat} {st : InflateState} {type : UInt32} {lo : Nat} {n : UInt32} {o : Nat}
    {bits : UInt32} (hi : h.istate b = some st) (hc : st.codes.size = ENOUGH) (hl : st.lens.size = 320)
    (hw : st.work.size = 288) (hcall : TableCall type lo n o bits)
    (hv : ∀ j, j < n.toNat → (st.lens[lo + j]!).toNat ≤ (if type = CODES then 7 else 15)) :
    TblPre h b st type lo n o bits := by
  have hE : ENOUGH = 1924 := rfl
  rcases hcall with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, h1, h2, rfl, rfl⟩ | ⟨rfl, h1, h2, h3, h4, h5, rfl⟩
  · have hv' : ∀ j, j < (19 : UInt32).toNat → lensf st 0 j ≤ 7 := fun j hj => by
      have := hv j hj; simp only [ite_true] at this; exact this
    exact { live := LiveSt.of_istate hi, lens_size := by rw [hl]; decide,
            lens15 := fun j hj => by have := hv' j hj; omega, work_size := hw,
            room := by rw [hc, hE]; decide, codes_lt := by rw [hc, hE]; decide,
            kind := Or.inl ⟨rfl, by decide, by decide, by decide, hv'⟩ }
  · have hv' : ∀ j, j < n.toNat → lensf st 0 j ≤ 15 := fun j hj => by
      have := hv j hj; rw [ite_eq_right (by decide)] at this; exact this
    have hb : bndOf LENS 10 = 1332 := by unfold bndOf; rw [ite_eq_left rfl]
    exact { live := LiveSt.of_istate hi, lens_size := by rw [hl]; omega, lens15 := hv', work_size := hw,
            room := by rw [hc, hE, hb]; decide, codes_lt := by rw [hc, hE]; decide,
            kind := Or.inr (Or.inl ⟨rfl, by omega⟩) }
  · have hv' : ∀ j, j < n.toNat → lensf st lo j ≤ 15 := fun j hj => by
      have := hv j hj; rw [ite_eq_right (by decide)] at this; exact this
    have hb : bndOf DISTS 9 = 592 := by unfold bndOf; rw [ite_eq_right (by decide), ite_eq_left rfl]
    exact { live := LiveSt.of_istate hi, lens_size := by rw [hl]; omega, lens15 := hv', work_size := hw,
            room := by rw [hc, hE, hb]; omega, codes_lt := by rw [hc, hE]; decide,
            kind := Or.inr (Or.inr ⟨rfl, by omega⟩) }

/-- The three calls of `zng_inflate_table` in `inflate`: no fault, only `codes` and `work` change, the entries
before the table start are kept, and on success the table `[o, o')` has room for its `2 ^ lb` root entries and ends
within `ENOUGH_DISTS` (distance code) or `ENOUGH_LENS` (the other two) of `o`. -/
theorem table_run (h : Heap) (b : Nat) (st : InflateState) (type : UInt32) (lo : Nat) (n : UInt32) (o : Nat)
    (bits : UInt32) (hi : h.istate b = some st) (hc : st.codes.size = ENOUGH) (hl : st.lens.size = 320)
    (hw : st.work.size = 288) (hcall : TableCall type lo n o bits)
    (hv : ∀ j, j < n.toNat → (st.lens[lo + j]!).toNat ≤ (if type = CODES then 7 else 15)) :
    ∃ (ret : Int32) (o' : Nat) (lb : UInt32) (codes' : Array Code) (work' : Array UInt16),
      C.run (zng_inflate_table type (.ref (.lens b) lo) n (.ref (.codes b) o) bits (.ref (.work b) 0)) h =
        .ok ((ret, .ref (.codes b) o', lb),
          { h with istates := upd h.istates b (some { st with codes := codes', work := work' }) }) ∧
      codes'.size = ENOUGH ∧ work'.size = 288 ∧ (∀ j, j < o → codes'[j]! = st.codes[j]!) ∧
      (ret = 0 ∨ ret = -1 ∨ ret = 1) ∧
      (ret = 0 → o' ≤ o + (if type = DISTS then 592 else 1332) ∧ o + 2 ^ lb.toNat ≤ o' ∧ 1 ≤ lb.toNat ∧
        lb.toNat ≤ 15) := by
  have hP := TblPre.of_call hi hc hl hw hcall hv
  obtain ⟨⟨ret, p, lb⟩, h', e, C, W, rfl, hCs, hWs, hfr, hret, herr, hok⟩ := zng_inflate_table_wp hP
  have hbits := hcall
  have hbnd : bndOf type bits ≤ (if type = DISTS then 592 else 1332) := by
    rcases hbits with ⟨rfl, -, -, -, rfl⟩ | ⟨rfl, -, -, -, -, rfl⟩ | ⟨rfl, -, -, -, -, -, rfl⟩
    · unfold bndOf; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]; decide
    · unfold bndOf; rw [ite_eq_left rfl, ite_eq_right (by decide)]; decide
    · unfold bndOf; rw [ite_eq_right (by decide), ite_eq_left rfl, ite_eq_left rfl]; exact Nat.le_refl _
  have hkeep : ∀ j, j < o → C[j]! = st.codes[j]! := by
    intro j hj
    have := hfr j (by omega)
    simp only [getElem!_def, this]
  by_cases h0 : ret = 0
  · obtain ⟨used, h1, h2, hp, h3, h4, -⟩ := hok h0
    simp only at hp h1 h3 h4
    subst hp
    exact ⟨ret, o + used, lb, C, W, e, by rw [hCs, hc], by rw [hWs, hw], hkeep, hret,
      fun _ => ⟨by omega, by omega, h3, h4⟩⟩
  · have hp := herr h0
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨ret, o, _, C, W, e, by rw [hCs, hc], by rw [hWs, hw], hkeep, hret, fun e => absurd e h0⟩

end ZlibNgF.Proof.Inftrees
