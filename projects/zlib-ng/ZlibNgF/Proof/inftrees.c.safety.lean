import ZlibNgF.Proof.«inftrees.c.pre»

/-!
# Toward the safety theorem of `zng_inflate_table` (`ZlibNgF`)

The postcondition `TablePost` of the final theorem and the room `bndOf` of each code type; the loop rule
`tbl_loop_gen` for a table-filling loop whose body is given by its one-trip property.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

theorem Wp.ite {α : Type} {c : Prop} [Decidable c] {A B : M α} {h : Heap} {Q : α → Heap → Prop}
    (ha : c → Wp A h Q) (hb : ¬ c → Wp B h Q) : Wp (if c then A else B) h Q := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact ha hc
  · rw [ite_eq_right hc]; exact hb hc

theorem Wp.pure_of {α : Type} {a : α} {h : Heap} {Q : α → Heap → Prop} (hq : Q a h) : Wp (pure a) h Q :=
  Wp.pure_iff.2 hq

/-- The room `zng_inflate_table` may use for each code type: `ENOUGH_LENS`, `ENOUGH_DISTS`, or the root table
`2 ^ bits` for `CODES` (whose lengths never exceed `bits`, so it has no sub-tables). -/
def bndOf (type bits : UInt32) : Nat :=
  if type = LENS then 1332 else if type = DISTS then 592 else 2 ^ bits.toNat

/-- What `zng_inflate_table` guarantees about its result and the heap: only `codes[off .. off + bndOf type bits)` and
`work` change, and on success the region `[off, off + used)` is a decoding table with the returned root bits and a
prefix code; in a code length table every root entry has `op & 16` clear (its code bits are its `bits`) and the root
level is a prefix code for every entry (`LvlAll`) (for at most 286 literal/length lengths). -/
def TablePost (h : Heap) (b : Nat) (s : InflateState) (type codes bits : UInt32) (off : Nat)
    (r : Int32 × CodePtr × UInt32) (h' : Heap) : Prop :=
  ∃ C W, h' = setCW h b s C W ∧ C.size = s.codes.size ∧ W.size = s.work.size ∧
    (∀ i, ¬ (off ≤ i ∧ i < off + bndOf type bits) → C[i]? = s.codes[i]?) ∧
    (r.1 = 0 ∨ r.1 = -1 ∨ r.1 = 1) ∧
    (r.1 ≠ 0 → r.2 = (.ref (.codes b) off, bits)) ∧
    (r.1 = 0 → ∃ used, 2 ^ r.2.2.toNat ≤ used ∧ used ≤ bndOf type bits ∧ r.2.1 = .ref (.codes b) (off + used) ∧
      1 ≤ r.2.2.toNat ∧ r.2.2.toNat ≤ 15 ∧ (∀ i, ¬ (off ≤ i ∧ i < off + used) → C[i]? = s.codes[i]?) ∧
      ((type = LENS → codes.toNat ≤ 286) →
        InflateTab.CodeTable C off (off + used) r.2.2.toNat (mOf type) (dOf type) ∧
          InfbackLoop.Rep C off r.2.2.toNat (dOf type) ∧
          (type = CODES → InfbackLoop.LvlAll C off r.2.2.toNat ∧
            ∀ j, j < 2 ^ r.2.2.toNat → C[off + j]!.op.toNat &&& 16 = 0)))

theorem set_ne {α : Type} {C : Array α} {k i : Nat} (v : α) (h : k ≠ i) : (C.set! k v)[i]? = C[i]? := by
  simp [Array.set!_eq_setIfInBounds, h]

theorem lcount_pos {f : Nat → Nat} {n v : Nat} (h : lcount f n v ≠ 0) : ∃ j, j < n ∧ f j = v := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    rw [lcount_succ] at h
    by_cases e : f n = v
    · exact ⟨n, by omega, e⟩
    · rw [ite_eq_right e] at h
      obtain ⟨j, hj, hf⟩ := ih (by omega)
      exact ⟨j, by omega, hf⟩

/-- The root bits after `root = MIN(*bits, max)` and `root = MAX(root, min)`. -/
theorem root_toNat (bits mx mn : UInt32) (h1 : mn.toNat ≤ mx.toNat) :
    (if (if bits > mx then mx else bits) > mn then (if bits > mx then mx else bits) else mn).toNat =
      max (min bits.toNat mx.toNat) mn.toNat := by
  by_cases e1 : bits > mx
  · rw [ite_eq_left e1]
    simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at e1
    by_cases e2 : mx > mn
    · rw [ite_eq_left e2]; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at e2; omega
    · rw [ite_eq_right e2]; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at e2; omega
  · rw [ite_eq_right e1]
    simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at e1
    by_cases e2 : bits > mn
    · rw [ite_eq_left e2]; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at e2; omega
    · rw [ite_eq_right e2]; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at e2; omega

/-- The table-filling loop with any body that makes one trip. -/
theorem tbl_loop_gen {S : Setup} {t0 : TL} {h : Heap} (hS : S.OK) (hI : MI S t0 h) (body : TL → M TL)
    (hb : ∀ t h, MI S t h → Wp (body t) h (fun t' h' => Trip S t t' h')) :
    Wp (cwhile (fun (t : TL) => pure (t.ret.isNone, t)) body t0) h
      (fun t h' => (∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin0 S t C) ∨
        (∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin1 S t C)) := by
  obtain ⟨C0, K0, rfl, hst0⟩ := hI
  have hs0 : t0.sym.toNat ≤ nsum S.c0 15 := by
    have := hst0.sym
    have := nsum_mono S.c0 (show t0.len.toNat ≤ 15 by have := hst0.len_hi; have := hS.mx15; omega)
    omega
  refine Wp.cwhile_pure (c := fun t => t.ret.isNone)
    (fun n t h' => (MI S t h' ∧ t.sym.toNat ≤ nsum S.c0 15 ∧ n = nsum S.c0 15 - t.sym.toNat + 1) ∨
      (n = 0 ∧ ((∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin0 S t C) ∨
        (∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin1 S t C)))) _ ?_
    (Or.inl ⟨⟨C0, K0, rfl, hst0⟩, hs0, rfl⟩) (by unfold fuel; have := hS.n_codes; have := hS.kind; omega)
  rintro n t h' (⟨hmi, hsn, rfl⟩ | ⟨rfl, hfin⟩)
  · refine ⟨fun _ => ?_, fun hc => ?_⟩
    · refine Wp.mono (hb t h' hmi) ?_
      rintro t' h'' (⟨hmi', hlt, hle⟩ | hf0 | hf1)
      · exact ⟨_, by omega, Or.inl ⟨hmi', hle, rfl⟩⟩
      · exact ⟨0, by omega, Or.inr ⟨rfl, Or.inl hf0⟩⟩
      · exact ⟨0, by omega, Or.inr ⟨rfl, Or.inr hf1⟩⟩
    · obtain ⟨C, K, -, hst⟩ := hmi
      simp [hst.ret] at hc
  · refine ⟨fun hc => ?_, fun _ => hfin⟩
    exfalso
    rcases hfin with ⟨C, -, hf⟩ | ⟨C, -, hf⟩ <;> simp [hf.ret] at hc

end ZlibNgF.Proof.Inftrees
