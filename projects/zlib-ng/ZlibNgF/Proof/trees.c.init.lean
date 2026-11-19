import ZlibNgF.Proof.«trees_emit.h.emit»

/-!
# `init_block` and `detect_data_type` (`ZlibNgF`)

On `SH` heaps: `init_block` clears the frequencies of the three tree arrays (`ctLoop` of
`Proof/deflate.c.init.lean`), sets `dyn_ltree[END_BLOCK].Freq = 1` and resets `static_len`, `opt_len`, `sym_next`;
`detect_data_type` reads the frequencies of the 256 literals of `dyn_ltree` and changes nothing.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesInit
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- The fields that `init_block` sets, with the three tree arrays `A`, `B`, `C`. -/
def ibS (st : DeflateState) (A B C : Array Ct) : DeflateState :=
  { st with
    dyn_ltree := A
    dyn_dtree := B
    bl_tree := C
    static_len := 0
    opt_len := 0
    sym_next := 0 }

/-- The frequencies that `init_block` leaves: `END_BLOCK` once in `dyn_ltree`, every other code of the three trees
zero. -/
def IbFreq (A B C : Array Ct) : Prop :=
  A.size = HEAP_SIZE ∧ B.size = 2 * 30 + 1 ∧ C.size = 2 * 19 + 1 ∧
    (∀ c, c < 286 → (A[c]!).fc.toNat = if c = 256 then 1 else 0) ∧ (∀ c, c < 30 → (B[c]!).fc.toNat = 0) ∧
    (∀ c, c < 19 → (C[c]!).fc.toNat = 0)

/-- `init_block` on a state whose tree arrays have their C sizes. -/
theorem init_block_SH (st : DeflateState) (h1 : st.dyn_ltree.size = HEAP_SIZE) (h2 : st.dyn_dtree.size = 2 * 30 + 1)
    (h3 : st.bl_tree.size = 2 * 19 + 1) :
    Sat (SH H i z b st d) (ZlibNg.Trees.init_block (some b)) (fun _ H' => ∃ A B C, H' = SH H i z b (ibS st A B C) d ∧
      IbFreq A B C) := by
  simp only [ZlibNg.Trees.init_block, dynLtreeP, dynDtreeP, blTreeP, pure_bind_M]
  refine Sat.bind (Sat.mono (ctLoop CtRef.dyn_ltree (·.dyn_ltree) (fun s A => { s with dyn_ltree := A })
    ctl_get ctl_mod (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) _ L_CODES (by decide)
    (by simp [h1, HEAP_SIZE, L_CODES])) ?_)
  rintro _ _ ⟨A, rfl, hA, hA0⟩
  refine Sat.bind (Sat.mono (ctLoop CtRef.dyn_dtree (·.dyn_dtree) (fun s A => { s with dyn_dtree := A })
    ctd_get ctd_mod (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) _ D_CODES (by decide)
    (by simp [h2, D_CODES])) ?_)
  rintro _ _ ⟨B, rfl, hB, hB0⟩
  refine Sat.bind (Sat.mono (ctLoop CtRef.bl_tree (·.bl_tree) (fun s A => { s with bl_tree := A })
    ctb_get ctb_mod (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) _ BL_CODES (by decide)
    (by simp [h3, BL_CODES])) ?_)
  rintro _ _ ⟨C, rfl, hC, hC0⟩
  simp only at hA hB hC hA0 hB0 hC0
  refine Sat.bind (Sat.of_eq (ctSetFc_l _ END_BLOCK 1 (by simp [hA, h1, END_BLOCK, HEAP_SIZE, L_CODES])) ?_)
  try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.of_eq (wrD_SH _) ⟨_, B, C, rfl, ⟨?_, by rw [hB, h2], by rw [hC, h3], fun c hc => ?_,
    fun c hc => by rw [hB0 c (by simp [D_CODES]; omega)]; rfl, fun c hc => by rw [hC0 c (by simp [BL_CODES]; omega)]; rfl⟩⟩
  · simp [hA, h1]
  · have hc' : c < A.size := by rw [hA, h1]; simp [HEAP_SIZE, L_CODES]; omega
    simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
    by_cases e : c = 256
    · subst e; simp [END_BLOCK, hc']
    · have e' : (END_BLOCK : Nat) ≠ c := by simp [END_BLOCK]; omega
      have := hA0 c (by simp [L_CODES]; omega)
      simp only [getElem!_def] at this
      simp only [e', e, ↓reduceIte] at this ⊢
      simp [this]

theorem ctGet_dl (s : DeflateState) (k : Nat) (hk : k < s.dyn_ltree.size) :
    ctGet (.ref (CtRef.dyn_ltree b) 0) (k : Int) (SH H i z b s d) = .ok (s.dyn_ltree[k]!, SH H i z b s d) := by
  have e1 : Ptr.add (Ptr.ref (CtRef.dyn_ltree b) 0) (k : Int) (SH H i z b s d) =
      .ok (Ptr.ref (CtRef.dyn_ltree b) k, SH H i z b s d) := by
    simp only [Ptr.add, ctl_get]
    rw [ite_t (by omega)]
    congr 3; omega
  simp [ctGet, Ptr.index, bind_app, e1, Ptr.load, ctl_get, hk]

theorem ctFc_dl (s : DeflateState) (k : Nat) (hk : k < s.dyn_ltree.size) :
    ctFc (.ref (CtRef.dyn_ltree b) 0) (k : Int) (SH H i z b s d) = .ok ((s.dyn_ltree[k]!).fc, SH H i z b s d) := by
  have e1 : Ptr.add (Ptr.ref (CtRef.dyn_ltree b) 0) (k : Int) (SH H i z b s d) =
      .ok (Ptr.ref (CtRef.dyn_ltree b) k, SH H i z b s d) := by
    simp only [Ptr.add, ctl_get]
    rw [ite_t (by omega)]
    congr 3; omega
  simp [ctFc, ctGet, Ptr.index, bind_app, e1, Ptr.load, ctl_get, hk]

theorem i32_succ (n : Int32) (h0 : 0 ≤ n.toInt) (h1 : n.toInt ≤ 1000) : (n + 1).toInt = n.toInt + 1 := by
  rw [Int32.toInt_add, Int32.toInt_one]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- `detect_data_type` reads the literal frequencies of `dyn_ltree` and changes nothing. -/
theorem detect_SH (st : DeflateState) (h1 : 256 ≤ st.dyn_ltree.size) :
    Sat (SH H i z b st d) (ZlibNg.Trees.detect_data_type (some b)) (fun _ H' => H' = SH H i z b st d) := by
  simp only [ZlibNg.Trees.detect_data_type, dynLtreeP, pure_bind_M]
  have e31 : (31 : Int32).toInt = 31 := rfl
  refine Sat.bind (Sat.mono (sat_cwhile (s := ((0 : Int32), (0xf3ffc07f : UInt64), false))
    (fun (x : Int32 × UInt64 × Bool) H' => H' = SH H i z b st d ∧ 0 ≤ x.1.toInt ∧
      x.1.toInt ≤ 32 ∧ (x.2.2 = true → x.1.toInt ≤ 31)) (fun x => if x.2.2 then 0 else 33 - x.1.toInt.toNat)
    (fun _ H' => H' = SH H i z b st d) ?_ ⟨rfl, by decide, by decide, by decide⟩ (by simp [fuel])) ?_)
  · rintro ⟨n, bm, f⟩ _ ⟨rfl, h0, h32, hf⟩
    dsimp only at h0 h32 hf
    refine Sat.pure ⟨fun hc => ?_, fun _ => rfl⟩
    dsimp only at hc ⊢
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨rfl, hc⟩ := hc
    have hn := Int32.le_iff_toInt_le.mp hc
    rw [e31] at hn
    have hk : n.toInt.toNat < st.dyn_ltree.size := by omega
    have hc1 : ((n.toInt.toNat : Nat) : Int) = n.toInt := by omega
    have hs := i32_succ _ h0 (by omega)
    have hm : 33 - (n + 1).toInt.toNat < 33 - n.toInt.toNat := by rw [hs]; omega
    have hnext : (SH H i z b st d = SH H i z b st d ∧ 0 ≤ (n + 1).toInt ∧ (n + 1).toInt ≤ 32 ∧
        (false = true → (n + 1).toInt ≤ 31)) := ⟨rfl, by rw [hs]; omega, by rw [hs]; omega, by simp⟩
    by_cases hb : (bm &&& 1 != 0) = true
    · simp only [hb, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (hc1 ▸ ctFc_dl st _ hk) ?_)
      by_cases hh : ((st.dyn_ltree[n.toInt.toNat]!).fc != 0) = true
      · simp only [hh, ↓reduceIte]
        exact Sat.pure ⟨⟨rfl, h0, h32, fun _ => hn⟩, by simpa using (show 0 < 33 - n.toInt.toNat by omega)⟩
      · simp only [hh, Bool.false_eq_true, ↓reduceIte]
        exact Sat.pure ⟨hnext, by simpa using hm⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact Sat.pure ⟨hnext, by simpa using hm⟩
  rintro ⟨n, bm, f⟩ _ rfl
  try dsimp only
  by_cases hf : f = true
  · subst hf; exact Sat.pure rfl
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (ctFc_dl st 9 (by omega)) ?_)
    split
    · exact Sat.pure rfl
    refine Sat.bind (Sat.of_eq (ctFc_dl st 10 (by omega)) ?_)
    split
    · exact Sat.pure rfl
    refine Sat.bind (Sat.of_eq (ctFc_dl st 13 (by omega)) ?_)
    split
    · exact Sat.pure rfl
    have e256 : (LITERALS.toInt32).toInt = 256 := by decide
    refine Sat.bind (Sat.mono (sat_cwhile (s := ((32 : Int32), false))
      (fun (x : Int32 × Bool) H' => H' = SH H i z b st d ∧ 32 ≤ x.1.toInt ∧ x.1.toInt ≤ 256)
      (fun x => if x.2 then 0 else 257 - x.1.toInt.toNat)
      (fun _ H' => H' = SH H i z b st d) ?_ ⟨rfl, by decide, by decide⟩ (by simp [fuel])) ?_)
    · rintro ⟨n, f⟩ _ ⟨rfl, h0, h1⟩
      dsimp only at h0 h1
      refine Sat.pure ⟨fun hc => ?_, fun _ => rfl⟩
      dsimp only at hc ⊢
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      obtain ⟨rfl, hc⟩ := hc
      have hn := Int32.lt_iff_toInt_lt.mp hc
      rw [e256] at hn
      have hk : n.toInt.toNat < st.dyn_ltree.size := by omega
      have hc1 : ((n.toInt.toNat : Nat) : Int) = n.toInt := by omega
      have hs := i32_succ n (by omega) (by omega)
      refine Sat.bind (Sat.of_eq (hc1 ▸ ctFc_dl st _ hk) ?_)
      split
      · exact Sat.pure ⟨⟨rfl, h0, h1⟩, by simpa using (show 0 < 257 - n.toInt.toNat by omega)⟩
      · exact Sat.pure ⟨⟨rfl, by rw [hs]; omega, by rw [hs]; omega⟩,
          by simpa using (show 257 - (n + 1).toInt.toNat < 257 - n.toInt.toNat by rw [hs]; omega)⟩
    rintro ⟨n, f⟩ _ rfl
    split <;> exact Sat.pure rfl

end

end ZlibNgF.Proof.TreesInit
