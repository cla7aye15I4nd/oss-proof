import ZlibNgF.Proof.«trees.c.merge»

/-!
# `gen_bitlen` on `SH` heaps (`ZlibNgF`)

`gen_bitlen` (`trees.c:283-373`) cut into its loops (`gen_bitlen_eq`): the clearing of `bl_count`, the depth pass
over the internal nodes (`p1Body`, from the root down through the `Dad` links), the pass over the leaves
(`p2Body`: lengths, `bl_count`, `opt_len`, `static_len`), the overflow repair (`rpBody`) and the length
re-assignment (`raBody` / `riBody`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesBitlen
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesScan ZlibNgF.Proof.TreesSort ZlibNgF.Proof.TreesBuild ZlibNgF.Proof.TreesMerge
open ZlibNgF.Math.TreesLabeled
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f u32_toInt32_toInt)

/-! ## The loops -/

/-- The condition of the clearing loop of `bl_count`. -/
def zCond : UInt32 → M (Bool × UInt32) := fun (bits : UInt32) => pure (bits <= MAX_BITS.toUInt32, bits)

/-- The body of the clearing loop of `bl_count`. -/
def zBody (st : StatePtr) : UInt32 → M UInt32 := fun bits => do blCountSet st bits.toNat 0; pure (bits + 1)

/-- The condition of the depth pass. -/
def p1Cond (elems : Int32) : Int32 × Int32 → M (Bool × (Int32 × Int32)) :=
  fun ((n, overflow) : Int32 × Int32) => pure (n >= elems, (n, overflow))

/-- The body of the depth pass. -/
def p1Body (tree : CtPtr) (max_length : UInt32) : Int32 × Int32 → M (Int32 × Int32) :=
  fun ((n, overflow) : Int32 × Int32) => do
    let dad ← ctDl tree n.toInt
    let mut bits : UInt32 := (← ctDl tree dad.toNat).toUInt32 + 1
    let mut overflow := overflow
    if bits > max_length then
      bits := max_length
      overflow ← chkI32 (overflow.toInt + 1)
    ctSetDl tree n.toInt bits.toUInt16
    pure (← chkI32 (n.toInt - 1), overflow)

/-- The condition of the leaf pass. -/
def p2Cond (nleaves : Int32) : Int32 × Int32 → M (Bool × (Int32 × Int32)) :=
  fun ((i, overflow) : Int32 × Int32) => pure (i < nleaves, (i, overflow))

/-- The body of the leaf pass. -/
def p2Body (st : StatePtr) (tree stree : CtPtr) (sorted : DWPtr) (extra : IPtr) (base : Int32)
    (max_length : UInt32) : Int32 × Int32 → M (Int32 × Int32) :=
  fun ((i, overflow) : Int32 × Int32) => do
    let n := pq_node (← dwGet sorted i.toInt)
    let dad ← ctDl tree n.toInt
    let mut bits : UInt32 := (← ctDl tree dad.toNat).toUInt32 + 1
    let mut overflow := overflow
    if bits > max_length then
      bits := max_length
      overflow ← chkI32 (overflow.toInt + 1)
    ctSetDl tree n.toInt bits.toUInt16
    blCountSet st bits.toNat ((← blCountGet st bits.toNat) + 1)
    let mut xbits : Int32 := 0
    if n >= base then
      xbits ← Ptr.index extra (← chkI32 (n.toInt - base.toInt)).toInt
    let f ← ctFc tree n.toInt
    wrD st fun s => { s with opt_len := s.opt_len + f.toUInt32 * (bits + xbits.toUInt32) }
    match stree with
    | .null => pure ()
    | _ =>
      let sl ← ctDl stree n.toInt
      let v ← chkI32 (sl.toNat + xbits.toInt)
      wrD st fun s => { s with static_len := s.static_len + f.toUInt32 * v.toUInt32 }
    pure (i + 1, overflow)

/-- One iteration of the overflow repair. -/
def rpBody (st : StatePtr) (max_length : UInt32) : Int32 → M Int32 :=
  fun (overflow : Int32) => do
    let bits := max_length - 1
    let bits ← cwhile
      (fun (bits : UInt32) => do pure ((← blCountGet st bits.toNat) == 0, bits))
      (fun (bits : UInt32) => pure (bits - 1))
      bits
    blCountSet st bits.toNat ((← blCountGet st bits.toNat) - 1)
    blCountSet st (bits + 1).toNat ((← blCountGet st (bits + 1).toNat).toUInt32 + 2).toUInt16
    blCountSet st max_length.toNat ((← blCountGet st max_length.toNat) - 1)
    chkI32 (overflow.toInt - 2)

/-- The condition of the overflow repair. -/
def rpCond : Int32 → M (Bool × Int32) := fun overflow => pure (overflow > 0, overflow)

/-- The condition of the inner re-assignment loop. -/
def riCond : Int32 × Int32 → M (Bool × (Int32 × Int32)) := fun ((n, i) : Int32 × Int32) => pure (n != 0, (n, i))

/-- The body of the inner re-assignment loop. -/
def riBody (st : StatePtr) (tree : CtPtr) (sorted : DWPtr) (bits : UInt32) : Int32 × Int32 → M (Int32 × Int32) :=
  fun ((n, i) : Int32 × Int32) => do
    let m := pq_node (← dwGet sorted i.toInt)
    let i ← chkI32 (i.toInt + 1)
    let len ← ctDl tree m.toInt
    if len.toUInt32 != bits then
      let fr ← ctFc tree m.toInt
      wrD st fun s => { s with opt_len := s.opt_len + bits * fr.toUInt32 }
      let len ← ctDl tree m.toInt
      let fr ← ctFc tree m.toInt
      let p ← chkI32 (len.toNat * fr.toNat)
      wrD st fun s => { s with opt_len := s.opt_len - p.toUInt32 }
      ctSetDl tree m.toInt bits.toUInt16
    pure (← chkI32 (n.toInt - 1), i)

/-- The condition of the outer re-assignment loop. -/
def raCond : UInt32 × Int32 → M (Bool × (UInt32 × Int32)) :=
  fun ((bits, i) : UInt32 × Int32) => pure (bits != 0, (bits, i))

/-- The body of the outer re-assignment loop. -/
def raBody (st : StatePtr) (tree : CtPtr) (sorted : DWPtr) : UInt32 × Int32 → M (UInt32 × Int32) :=
  fun ((bits, i) : UInt32 × Int32) => do
    let n : Int32 := (← blCountGet st bits.toNat).toUInt32.toInt32
    let (_, i) ← cwhile riCond (riBody st tree sorted bits) (n, i)
    pure (bits - 1, i)

theorem gen_bitlen_eq (st : StatePtr) (desc : DescSel) (sorted : DWPtr) (nleaves root : Int32) :
    gen_bitlen st desc sorted nleaves root = (do
      let tree ← descDynTree st desc
      let elems := (← descStat st desc).elems
      let stree := (← descStat st desc).static_tree
      let extra := (← descStat st desc).extra_bits
      let base := (← descStat st desc).extra_base
      let max_length := (← descStat st desc).max_length
      let _ ← cwhile zCond (zBody st) 0
      ctSetDl tree root.toInt 0
      let (_, overflow) ← cwhile (p1Cond elems) (p1Body tree max_length) (← chkI32 (root.toInt - 1), 0)
      let (_, overflow) ← cwhile (p2Cond nleaves) (p2Body st tree stree sorted extra base max_length) (0, overflow)
      if overflow == 0 then
        return
      let _ ← cdoWhile (rpBody st max_length) rpCond overflow
      let _ ← cwhile raCond (raBody st tree sorted) (max_length, (0 : Int32))) := rfl

/-! ## Clearing `bl_count` -/

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

theorem zero_SH (Y : DeflateState) (hY : Y.bl_count.size = 16) :
    Sat (SH H i z b Y d) (cwhile zCond (zBody (some b)) 0)
      (fun _ H' => ∃ blc : Array UInt16, H' = SH H i z b { Y with bl_count := blc } d ∧ blc.size = 16 ∧
        ∀ k, k < 16 → blc[k]! = 0) := by
  refine sat_cwhile (I := fun (x : UInt32) H' => ∃ blc : Array UInt16, x.toNat ≤ 16 ∧
      H' = SH H i z b { Y with bl_count := blc } d ∧ blc.size = 16 ∧ ∀ k, k < x.toNat → blc[k]! = 0)
    (μ := fun x => 16 - x.toNat) _ ?_ ⟨Y.bl_count, by simp, rfl, hY, fun k hk => by simp at hk⟩ (by simp [fuel])
  rintro x _ ⟨blc, hx, rfl, hs, hz⟩
  simp only [zCond]
  refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · have hx' : x.toNat ≤ 15 := by
      simp only [decide_eq_true_eq, UInt32.le_iff_toNat_le] at hc; exact hc
    simp only [zBody]
    have e := blCountSet_SH (H := H) (i := i) (z := z) (b := b) (d := d) { Y with bl_count := blc } x.toNat
      (by simp; omega) 0
    have hx1 : (x + 1).toNat = x.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    refine Sat.bind (Sat.of_eq e (Sat.pure ⟨⟨blc.set! x.toNat 0, by omega, rfl, by simp [hs], fun k hk => ?_⟩, ?_⟩))
    · rw [hx1] at hk
      by_cases hkx : k = x.toNat
      · subst hkx; exact set!_get_eq _ _ _ (by omega)
      · rw [set!_get_ne _ _ _ _ hkx]; exact hz k (by omega)
    · rw [hx1]; omega
  · have hx' : 16 ≤ x.toNat := by
      have h15 : (MAX_BITS.toUInt32).toNat = 15 := by decide
      simp only [decide_eq_false_iff_not, UInt32.le_iff_toNat_le, h15] at hc; omega
    exact ⟨blc, rfl, hs, fun k hk => hz k (by omega)⟩

end

/-! ## The depth pass -/

/-- The depth pass has handled the internal nodes `(n, R]`. -/
def P1Inv (T : NT) (Lm R : Nat) (A A' : Array Ct) (n : Int) (ov : Int) : Prop :=
  A'.size = A.size ∧ (∀ k : Nat, (A'[k]!).fc = (A[k]!).fc) ∧
  (∀ k : Nat, ((k : Int) ≤ n ∨ R < k) → A'[k]! = A[k]!) ∧
  (∀ x : Nat, n < x → x ≤ R → (A'[x]!).dl.toNat = min (T.dep 0 x) Lm) ∧
  ov = ((List.range' (n + 1).toNat (R - (n + 1).toNat + 1)).countP (fun x => decide (Lm < T.dep 0 x)) : Nat)

theorem countP_range'_succ (P : Nat → Bool) (a k : Nat) :
    (List.range' a (k + 1)).countP P = (if P a then 1 else 0) + (List.range' (a + 1) k).countP P := by
  rw [List.range'_succ, List.countP_cons]; cases P a <;> simp [Nat.add_comm]

theorem u16_u32 (x : UInt16) : x.toUInt32.toNat = x.toNat := by simp

theorem p1_step (T : NT) (Lm R : Nat) (A A' : Array Ct) (nN : Nat) (ov : Int) (v : UInt16)
    (hv : v.toNat = min (T.dep 0 nN) Lm) (hnN : nN < R) (hs : nN < A'.size) (inv : P1Inv T Lm R A A' nN ov) :
    P1Inv T Lm R A (A'.set! nN { A'[nN]! with dl := v }) ((nN : Int) - 1)
      (ov + if Lm < T.dep 0 nN then 1 else 0) := by
  obtain ⟨hsA, hfc, hsame, hdone, hov⟩ := inv
  refine ⟨by simp [hsA], fun k => ?_, fun k hk => ?_, fun x h1 h2 => ?_, ?_⟩
  · by_cases hk : k = nN
    · subst hk; rw [set!_get_eq _ _ _ hs]; exact hfc k
    · rw [set!_get_ne _ _ _ _ hk]; exact hfc k
  · have hk' : k ≠ nN := by omega
    rw [set!_get_ne _ _ _ _ hk']; exact hsame k (by omega)
  · by_cases hx : x = nN
    · subst hx; rw [set!_get_eq _ _ _ hs]; exact hv
    · rw [set!_get_ne _ _ _ _ hx]; exact hdone x (by omega) h2
  · rw [hov, show ((nN : Int) - 1 + 1).toNat = nN by omega, show ((nN : Int) + 1).toNat = nN + 1 by omega,
      show R - (nN + 1) + 1 = R - nN by omega, show R - nN + 1 = (R - nN) + 1 by omega, List.range'_succ,
      List.countP_cons]
    by_cases h : Lm < T.dep 0 nN <;> simp [h] <;> omega

theorem countP_le_len (P : Nat → Bool) (l : List Nat) : l.countP P ≤ l.length := List.countP_le_length

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- **The depth pass.** From the root `R` (whose `Len` is 0) down to `elems`, each internal node gets
`min(depth, max_length)` through its `Dad` link, and `overflow` counts the internal nodes deeper than
`max_length`. -/
theorem p1_SH (t : DescSel) (Y : DeflateState) (T : NT) (E R Lm : Nat) (L : UInt32) (elems n0 : Int32)
    (hL : L.toNat = Lm) (hLm : 1 ≤ Lm) (hLm' : Lm ≤ 15) (hE : elems.toInt = E) (hE1 : 1 ≤ E) (hER : E ≤ R)
    (hR : R < (tArr t Y).size) (hsz : (tArr t Y).size ≤ 1000) (hn0 : n0.toInt = (R : Int) - 1)
    (hlab : T.lab = R) (hnd : T.labs.Nodup) (hints : T.ints.Perm (List.range' E (R - E + 1)))
    (hed : ∀ e ∈ T.edges, e.1 < e.2) (hdl : ∀ e ∈ T.edges, E ≤ e.1 → ((tArr t Y)[e.1]!).dl.toNat = e.2)
    (hroot : ((tArr t Y)[R]!).dl.toNat = 0) :
    Sat (SH H i z b Y d) (cwhile (p1Cond elems) (p1Body (.ref (tRef t b) 0) L) (n0, 0))
      (fun x H' => ∃ A', H' = SH H i z b (tPut t Y A') d ∧ P1Inv T Lm R (tArr t Y) A' ((E : Int) - 1) x.2.toInt) := by
  refine sat_cwhile (I := fun (x : Int32 × Int32) H' => ∃ A', H' = SH H i z b (tPut t Y A') d ∧
      (E : Int) - 1 ≤ x.1.toInt ∧ x.1.toInt ≤ (R : Int) - 1 ∧ 0 ≤ x.2.toInt ∧ x.2.toInt ≤ R ∧
      P1Inv T Lm R (tArr t Y) A' x.1.toInt x.2.toInt)
    (μ := fun x => (x.1.toInt + 1).toNat) _ ?_ ⟨tArr t Y, by rw [tPut_self], by dsimp only; omega,
      by dsimp only; omega, by simp, by simp,
      rfl, fun _ => rfl, fun _ _ => rfl, fun x h1 h2 => ?_, ?_⟩ (by simp [fuel]; omega)
  rotate_left
  · dsimp only at h1 h2
    have : x = R := by omega
    subst this; rw [hroot, ← hlab, NT.dep_lab]; simp
  · simp only [Int32.toInt_zero]
    rw [show (n0.toInt + 1).toNat = R by omega, show R - R + 1 = 0 + 1 by omega, countP_range'_succ]
    simp [← hlab, NT.dep_lab]
  rintro ⟨n, ov⟩ _ ⟨A', rfl, hn1, hn2, hov0, hov1, hsA, hfc, hsame, hdone, hov⟩
  dsimp only at hn1 hn2 hov0 hov1 hov hsame hdone ⊢
  simp only [p1Cond]
  refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · have hc' : E ≤ n.toInt := by
      have := Int32.le_iff_toInt_le.mp (show elems ≤ n by simpa using hc); omega
    obtain ⟨nN, hnN⟩ : ∃ nN : Nat, n.toInt = nN := ⟨n.toInt.toNat, by omega⟩
    have hmem : nN ∈ T.ints := hints.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
    obtain ⟨p, hp⟩ := NT.has_parent T nN (NT.ints_sub T hmem) (by omega)
    have hnp : nN < p := hed _ hp
    have hpR : p ≤ R := by
      have := List.mem_range'_1.mp (hints.mem_iff.mp (NT.edge_par T hp)); simp only at this; omega
    have hdep : T.dep 0 nN = T.dep 0 p + 1 := NT.dep_edge T 0 hnd _ hp
    have hdad : (A'[nN]!).dl.toNat = p := by
      rw [hsame nN (Or.inl (by omega))]; exact hdl _ hp (by omega)
    have hpd : (A'[p]!).dl.toNat = min (T.dep 0 p) Lm := hdone p (by omega) hpR
    simp only [p1Body]
    rw [hnN]
    refine Sat.bind (Sat.of_eq (ctDl_T t (tPut t Y A') nN (by simp; omega)) ?_)
    simp only [tArr_tPut]
    rw [show ((A'[nN]!).dl.toNat : Int) = (p : Int) by rw [hdad]]
    refine Sat.bind (Sat.of_eq (ctDl_T t (tPut t Y A') p (by simp; omega)) ?_)
    simp only [tArr_tPut]
    have hb : ((A'[p]!).dl.toUInt32 + 1).toNat = min (T.dep 0 p) Lm + 1 := by
      rw [UInt32.toNat_add, u16_u32, hpd]; simp; omega
    by_cases hgt : (A'[p]!).dl.toUInt32 + 1 > L
    · have hgt' : Lm ≤ T.dep 0 p := by
        have := UInt32.lt_iff_toNat_lt.mp hgt; rw [hb, hL] at this; omega
      simp only [hgt, ↓reduceIte]
      rw [chkI32_ok (by omega) (by omega)]
      refine Sat.bind (Sat.pure ?_)
      refine Sat.bind (Sat.of_eq (ctSetDl_T t (tPut t Y A') nN (by simp; omega) _) ?_)
      simp only [tArr_tPut, tPut_tPut]
      rw [chkI32_ok (by omega) (by omega)]
      have hst := p1_step T Lm R (tArr t Y) A' nN ov.toInt L.toUInt16 (by simp; omega) (by omega) (by omega)
        (by rw [← hnN]; exact ⟨hsA, hfc, hsame, hdone, hov⟩)
      have hcnt : ov.toInt ≤ R := by
        have := countP_le_len (fun x => decide (Lm < T.dep 0 x))
          (List.range' (n.toInt + 1).toNat (R - (n.toInt + 1).toNat + 1))
        simp only [List.length_range'] at this; omega
      refine Sat.bind (Sat.pure (Sat.pure ⟨⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩))
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]
        have : (List.range' (n.toInt + 1).toNat (R - (n.toInt + 1).toNat + 1)).countP (fun x => decide (Lm < T.dep 0 x)) ≤ R - nN := by
          have := countP_le_len (fun x => decide (Lm < T.dep 0 x))
            (List.range' (n.toInt + 1).toNat (R - (n.toInt + 1).toNat + 1))
          simp only [List.length_range'] at this; omega
        omega
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega), i32_ofInt _ (by omega) (by omega)]
        have e1 : (if Lm < T.dep 0 nN then 1 else 0 : Int) = 1 := by simp; omega
        simpa only [e1] using hst
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
    · have hle : T.dep 0 p < Lm := by
        have : ¬ (Lm < min (T.dep 0 p) Lm + 1) := fun h => hgt (UInt32.lt_iff_toNat_lt.mpr (by rw [hb, hL]; exact h))
        omega
      simp only [hgt, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (ctSetDl_T t (tPut t Y A') nN (by simp; omega) _) ?_)
      simp only [tArr_tPut, tPut_tPut]
      rw [chkI32_ok (by omega) (by omega)]
      have hv : ((A'[p]!).dl.toUInt32 + 1).toUInt16.toNat = min (T.dep 0 nN) Lm := by
        rw [UInt32.toNat_toUInt16, hb]; omega
      have hst := p1_step T Lm R (tArr t Y) A' nN ov.toInt _ hv (by omega) (by omega)
        (by rw [← hnN]; exact ⟨hsA, hfc, hsame, hdone, hov⟩)
      refine Sat.bind (Sat.pure (Sat.pure ⟨⟨_, rfl, ?_, ?_, hov0, ?_, ?_⟩, ?_⟩))
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
      · exact hov1
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]
        have e1 : (if Lm < T.dep 0 nN then 1 else 0 : Int) = 0 := by simp; omega
        simpa only [e1, Int.add_zero] using hst
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
  · have hc' : n.toInt < E := by
      have := Int32.lt_iff_toInt_lt.mp (show n < elems by simpa using hc); omega
    have hnE : n.toInt = (E : Int) - 1 := by omega
    exact ⟨A', rfl, by rw [← hnE]; exact ⟨hsA, hfc, hsame, hdone, hov⟩⟩

end

end ZlibNgF.Proof.TreesBitlen
