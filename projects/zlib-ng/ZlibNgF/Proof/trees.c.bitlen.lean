import ZlibNgF.Proof.«trees.c.merge»
import ZlibNgF.Math.TreesRank

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

/-! # The leaf pass -/

namespace ZlibNgF.Proof.TreesBitlen
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesScan ZlibNgF.Proof.TreesSort ZlibNgF.Proof.TreesBuild ZlibNgF.Proof.TreesMerge
open ZlibNgF.Proof.TreesForce (sdl)
open ZlibNgF.Proof.TreesBuildSpec (tElems tMaxLen xb)
open ZlibNgF.Math.TreesLabeled
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f u32_toInt32_toInt)

/-! ## Static tables -/

theorem lbits_tab : ∀ k : Fin 29, (extra_lbits[k.val]!).toInt = (ZlibNgF.Math.OverlayDynamic.lengthExtra k.val : Int) := by
  decide +kernel
theorem dbits_tab : ∀ k : Fin 30, (extra_dbits[k.val]!).toInt = (ZlibNgF.Math.OverlayDynamic.distanceExtra k.val : Int) := by
  decide +kernel
theorem blbits_tab : ∀ k : Fin 19, (extra_blbits[k.val]!).toInt = (ZlibNgF.Math.Huff.blExtra k.val : Int) := by
  decide +kernel

theorem xb_le (t : DescSel) (n : Nat) (hn : n < tElems t) : xb t n ≤ 13 := by
  cases t
  · simp only [xb]; split
    · have := ZlibNgF.Math.OverlayDynamic.lengthExtra
      have h : ∀ k : Fin 29, ZlibNgF.Math.OverlayDynamic.lengthExtra k.val ≤ 13 := by decide +kernel
      exact h ⟨n - 257, by simp [tElems] at hn; omega⟩
    · omega
  · have h : ∀ k : Fin 30, ZlibNgF.Math.OverlayDynamic.distanceExtra k.val ≤ 13 := by decide +kernel
    exact h ⟨n, by simpa [tElems] using hn⟩
  · have h : ∀ k : Fin 19, ZlibNgF.Math.Huff.blExtra k.val ≤ 13 := by decide +kernel
    exact h ⟨n, by simpa [tElems] using hn⟩

theorem ints_index {H : Heap} (r : IRef) (a : Array Int32) (k : Nat) (hr : Heap.getInts H r = some a) (hk : k < a.size) :
    Ptr.index (Ptr.ref r 0 : IPtr) (k : Int) H = .ok (a[k]!, H) := by
  have e1 : Ptr.add (Ptr.ref r 0 : IPtr) (k : Int) H = .ok (Ptr.ref r k, H) := by
    simp only [Ptr.add, Space.get, hr]
    rw [ite_t (by omega)]
    congr 3; omega
  simp [Ptr.index, bind_app, e1, Ptr.load, Space.get, hr, hk]

/-- `xbits = 0; if (n >= base) xbits = extra[n - base];` reads `xb t n`. -/
theorem xbits_eq (t : DescSel) (n : Int32) (hn0 : 0 ≤ n.toInt) (hn : n.toInt < tElems t) {β : Type}
    (K : Int32 → M β) (H : Heap) :
    ∃ x : Int32, x.toInt = xb t n.toInt.toNat ∧
      (if n >= (tSD t).get.extra_base then do
        let x ← Ptr.index (tSD t).get.extra_bits (← chkI32 (n.toInt - (tSD t).get.extra_base.toInt)).toInt
        K x
      else K 0) H = K x H := by
  cases t
  · simp only [tElems] at hn
    by_cases hge : n >= (tSD .l_desc).get.extra_base
    · have hge' : 257 ≤ n.toInt := by
        have := Int32.le_iff_toInt_le.mp hge; simpa [tSD, StaticDescPtr.get] using this
      simp only [hge, ↓reduceIte]
      have hb : (tSD .l_desc).get.extra_base.toInt = 257 := rfl
      rw [hb, chkI32_ok (by omega) (by omega)]
      rw [pure_bind_M, i32_ofInt _ (by omega) (by omega)]
      have hk : n.toInt - 257 = ((n.toInt.toNat - 257 : Nat) : Int) := by omega
      rw [hk, show (tSD .l_desc).get.extra_bits = (Ptr.ref IRef.extra_lbits 0 : IPtr) from rfl]
      simp only [bind_app, ints_index .extra_lbits extra_lbits (n.toInt.toNat - 257) rfl (by rw [show extra_lbits.size = 29 from rfl]; omega)]
      refine ⟨_, ?_, rfl⟩
      rw [lbits_tab ⟨n.toInt.toNat - 257, by omega⟩]
      simp only [xb]; rw [ite_t (by omega)]
    · simp only [hge, ↓reduceIte]
      have hlt : n.toInt < 257 := by
        have := mt Int32.le_iff_toInt_le.mpr hge; simp [tSD, StaticDescPtr.get] at this; omega
      refine ⟨0, ?_, rfl⟩
      simp only [xb]; rw [ite_f (by omega)]; rfl
  · simp only [tElems] at hn
    have hge : n >= (tSD .d_desc).get.extra_base := Int32.le_iff_toInt_le.mpr (by simp [tSD, StaticDescPtr.get]; omega)
    simp only [hge, ↓reduceIte]
    have hb : (tSD .d_desc).get.extra_base.toInt = 0 := rfl
    rw [hb, chkI32_ok (by omega) (by omega)]
    rw [pure_bind_M, i32_ofInt _ (by omega) (by omega)]
    have hk : n.toInt - 0 = ((n.toInt.toNat : Nat) : Int) := by omega
    rw [hk, show (tSD .d_desc).get.extra_bits = (Ptr.ref IRef.extra_dbits 0 : IPtr) from rfl]
    simp only [bind_app, ints_index .extra_dbits extra_dbits n.toInt.toNat rfl (by rw [show extra_dbits.size = 30 from rfl]; omega)]
    refine ⟨_, ?_, rfl⟩
    rw [dbits_tab ⟨n.toInt.toNat, by omega⟩]; rfl
  · simp only [tElems] at hn
    have hge : n >= (tSD .bl_desc).get.extra_base := Int32.le_iff_toInt_le.mpr (by simp [tSD, StaticDescPtr.get]; omega)
    simp only [hge, ↓reduceIte]
    have hb : (tSD .bl_desc).get.extra_base.toInt = 0 := rfl
    rw [hb, chkI32_ok (by omega) (by omega)]
    rw [pure_bind_M, i32_ofInt _ (by omega) (by omega)]
    have hk : n.toInt - 0 = ((n.toInt.toNat : Nat) : Int) := by omega
    rw [hk, show (tSD .bl_desc).get.extra_bits = (Ptr.ref IRef.extra_blbits 0 : IPtr) from rfl]
    simp only [bind_app, ints_index .extra_blbits extra_blbits n.toInt.toNat rfl (by rw [show extra_blbits.size = 19 from rfl]; omega)]
    refine ⟨_, ?_, rfl⟩
    rw [blbits_tab ⟨n.toInt.toNat, by omega⟩]; rfl


theorem i32_u32 (x : Int32) (h : 0 ≤ x.toInt) : x.toUInt32.toNat = x.toInt.toNat := by
  have e1 : x.toUInt32.toNat = x.toBitVec.toNat := rfl
  have e2 : x.toInt = x.toBitVec.toInt := rfl
  have lt := x.toBitVec.isLt
  rw [e1]; rw [e2] at h ⊢
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  by_cases hc : 2 * x.toBitVec.toNat < 2 ^ 32
  · simp only [hc, ↓reduceIte]; omega
  · simp only [hc, ↓reduceIte] at h; omega

theorem static_ldl (k : Nat) (hk : k < 288) (H : Heap) :
    ctDl (Ptr.ref CtRef.static_ltree 0) (k : Int) H = .ok ((static_ltree[k]!).dl, H) := by
  have e1 : Ptr.add (Ptr.ref CtRef.static_ltree 0) (k : Int) H = .ok (Ptr.ref CtRef.static_ltree k, H) := by
    simp only [Ptr.add, Space.get, Heap.getCts]
    rw [ite_t (by rw [ZlibNgF.Proof.TreesEmitP.sl_size]; omega)]
    congr 3; omega
  have hk' : k < static_ltree.size := by rw [ZlibNgF.Proof.TreesEmitP.sl_size]; omega
  simp [ctDl, ctGet, Ptr.index, bind_app, e1, Ptr.load, Space.get, Heap.getCts, hk']

theorem static_ddl (k : Nat) (hk : k < 30) (H : Heap) :
    ctDl (Ptr.ref CtRef.static_dtree 0) (k : Int) H = .ok ((static_dtree[k]!).dl, H) := by
  have e1 : Ptr.add (Ptr.ref CtRef.static_dtree 0) (k : Int) H = .ok (Ptr.ref CtRef.static_dtree k, H) := by
    simp only [Ptr.add, Space.get, Heap.getCts]
    rw [ite_t (by rw [ZlibNgF.Proof.TreesEmitP.sd_size]; omega)]
    congr 3; omega
  have hk' : k < static_dtree.size := by rw [ZlibNgF.Proof.TreesEmitP.sd_size]; omega
  simp [ctDl, ctGet, Ptr.index, bind_app, e1, Ptr.load, Space.get, Heap.getCts, hk']

theorem stat_term (f sl : UInt16) (v : Int32) (x : Nat) (hv : v.toInt = (sl.toNat : Int) + x) :
    f.toUInt32 * v.toUInt32 = (f.toNat * (sl.toUInt32.toNat + x)).toUInt32 := by
  apply UInt32.toNat_inj.mp
  have h1 := i32_u32 v (by omega)
  rw [hv] at h1
  simp only [UInt32.toNat_mul, h1, Nat.toUInt32_eq, UInt32.toNat_ofNat', UInt16.toNat_toUInt32]
  have : ((sl.toNat : Int) + x).toNat = sl.toNat + x := by omega
  rw [this]

/-! ## The state during `gen_bitlen` -/

/-- The state with the tree of `t`, `bl_count`, `opt_len` and `static_len` replaced. -/
def LS (t : DescSel) (Y : DeflateState) (A : Array Ct) (blc : Array UInt16) (o sl : UInt32) : DeflateState :=
  { tPut t Y A with bl_count := blc, opt_len := o, static_len := sl }

section
variable (t : DescSel) (Y : DeflateState) (A : Array Ct) (blc : Array UInt16) (o sl : UInt32)

@[simp] theorem tArr_LS : tArr t (LS t Y A blc o sl) = A := by cases t <;> rfl
@[simp] theorem tPut_LS (A' : Array Ct) : tPut t (LS t Y A blc o sl) A' = LS t Y A' blc o sl := by cases t <;> rfl
@[simp] theorem LS_bc : (LS t Y A blc o sl).bl_count = blc := by cases t <;> rfl
@[simp] theorem LS_opt : (LS t Y A blc o sl).opt_len = o := by cases t <;> rfl
@[simp] theorem LS_stat : (LS t Y A blc o sl).static_len = sl := by cases t <;> rfl
@[simp] theorem qArr_LS (q : Bool) : qArr q (LS t Y A blc o sl) = qArr q Y := by cases q <;> cases t <;> rfl
theorem LS_set_bc (blc' : Array UInt16) : { LS t Y A blc o sl with bl_count := blc' } = LS t Y A blc' o sl := by
  cases t <;> rfl
theorem LS_set_opt (o' : UInt32) : { LS t Y A blc o sl with opt_len := o' } = LS t Y A blc o' sl := by
  cases t <;> rfl
theorem LS_set_stat (sl' : UInt32) : { LS t Y A blc o sl with static_len := sl' } = LS t Y A blc o sl' := by
  cases t <;> rfl

end

/-- The static-length term of a leaf: `f * (stree[n].Len + extra)`, none for the bit-length tree. -/
def stp (t : DescSel) (n f : Nat) : Nat :=
  match t with
  | .bl_desc => 0
  | _ => f * ((sdl t n).toNat + xb t n)

/-- What follows the extra bits in the leaf pass. -/
def p2Fin (st : StatePtr) (tree stree : CtPtr) (ii n : Int32) (bits : UInt32) (overflow xbits : Int32) :
    M (Int32 × Int32) := do
    let f ← ctFc tree n.toInt
    wrD st fun s => { s with opt_len := s.opt_len + f.toUInt32 * (bits + xbits.toUInt32) }
    match stree with
    | .null => pure ()
    | _ =>
      let sl ← ctDl stree n.toInt
      let v ← chkI32 (sl.toNat + xbits.toInt)
      wrD st fun s => { s with static_len := s.static_len + f.toUInt32 * v.toUInt32 }
    pure (ii + 1, overflow)

/-- What follows the clamping of `bits` in the leaf pass. -/
def p2Tail (st : StatePtr) (tree stree : CtPtr) (extra : IPtr) (base : Int32) (ii n : Int32) (bits : UInt32)
    (overflow : Int32) : M (Int32 × Int32) := do
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
    pure (ii + 1, overflow)

theorem p2Tail_eq (st : StatePtr) (tree stree : CtPtr) (extra : IPtr) (base : Int32) (ii n : Int32) (bits : UInt32)
    (overflow : Int32) : p2Tail st tree stree extra base ii n bits overflow = (do
      ctSetDl tree n.toInt bits.toUInt16
      blCountSet st bits.toNat ((← blCountGet st bits.toNat) + 1)
      if n >= base then do
        let x ← Ptr.index extra (← chkI32 (n.toInt - base.toInt)).toInt
        p2Fin st tree stree ii n bits overflow x
      else p2Fin st tree stree ii n bits overflow 0) := rfl

theorem p2Body_eq (st : StatePtr) (tree stree : CtPtr) (sorted : DWPtr) (extra : IPtr) (base : Int32)
    (max_length : UInt32) (ii ov : Int32) :
    p2Body st tree stree sorted extra base max_length (ii, ov) = (do
      let n := pq_node (← dwGet sorted ii.toInt)
      let dad ← ctDl tree n.toInt
      let b0 : UInt32 := (← ctDl tree dad.toNat).toUInt32 + 1
      if b0 > max_length then do
        let o ← chkI32 (ov.toInt + 1)
        p2Tail st tree stree extra base ii n max_length o
      else p2Tail st tree stree extra base ii n b0 ov) := rfl

theorem opt_term (f : UInt16) (bits : UInt32) (xbits : Int32) (x : Nat) (hx : xbits.toInt = x) (hb : bits.toNat ≤ 15)
    (hx' : x ≤ 13) :
    f.toUInt32 * (bits + xbits.toUInt32) = (f.toNat * (bits.toNat + x)).toUInt32 := by
  apply UInt32.toNat_inj.mp
  have h1 := i32_u32 xbits (by omega)
  rw [hx] at h1
  simp only [UInt32.toNat_mul, UInt32.toNat_add, h1, Nat.toUInt32_eq, UInt32.toNat_ofNat', UInt16.toNat_toUInt32]
  simp only [Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt (a := bits.toNat + x) (by omega)]


/-! ## List helpers for the leaf pass -/

theorem take_succ' {α : Type} [Inhabited α] (l : List α) (k : Nat) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]!] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp [hk]

theorem nd_take_ne (srt : List (Nat × Nat)) (hnd : (srt.map Prod.snd).Nodup) (k : Nat) (hk : k < srt.length)
    (e : Nat × Nat) (he : e ∈ srt.take k) : e.2 ≠ (srt[k]!).2 := by
  have hs : srt = srt.take k ++ srt.drop k := (List.take_append_drop k srt).symm
  rw [hs, List.map_append] at hnd
  have hmem : srt[k]! ∈ srt.drop k := by
    rw [getElem!_pos srt k hk]
    rw [List.mem_iff_getElem]
    exact ⟨0, by simp; omega, by simp⟩
  intro eq
  exact (List.nodup_append.mp hnd).2.2 _ (List.mem_map_of_mem he) _ (List.mem_map_of_mem hmem) eq

theorem mem_of_idx' (l : List (Nat × Nat)) (k : Nat) (hk : k < l.length) : l[k]! ∈ l := by
  rw [getElem!_pos l k hk]; exact List.getElem_mem hk

theorem u32_acc (o : UInt32) (S T : Nat) : o + S.toUInt32 + T.toUInt32 = o + (S + T).toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, Nat.toUInt32_eq, UInt32.toNat_ofNat']
  omega

theorem cntOf_snoc (l : List Nat) (x j : Nat) :
    ZlibNgF.Math.TreesRank.cntOf (l ++ [x]) j = ZlibNgF.Math.TreesRank.cntOf l j + if x = j then 1 else 0 := by
  by_cases h : x = j <;> simp [ZlibNgF.Math.TreesRank.cntOf, List.countP_append, h]

theorem cntOf_le (l : List Nat) (j : Nat) : ZlibNgF.Math.TreesRank.cntOf l j ≤ l.length := List.countP_le_length

/-- The `opt_len` term of a leaf. -/
def optT (t : DescSel) (D : Nat → Nat) (Lm : Nat) (e : Nat × Nat) : Nat := e.1 * (min (D e.2) Lm + xb t e.2)

/-- The `static_len` term of a leaf. -/
def statT (t : DescSel) (e : Nat × Nat) : Nat := stp t e.2 e.1

/-- What the leaf pass has done after `k` leaves. -/
def P2Inv (t : DescSel) (Y : DeflateState) (srt : List (Nat × Nat)) (D : Nat → Nat) (Lm : Nat) (ov0 : Int) (k : Nat)
    (A2 : Array Ct) (blc : Array UInt16) (ov : Int) : Prop :=
  ov = ov0 + (srt.take k).countP (fun e => decide (Lm < D e.2)) ∧ A2.size = (tArr t Y).size ∧
  (∀ m : Nat, (A2[m]!).fc = ((tArr t Y)[m]!).fc) ∧ (∀ m : Nat, m ∉ (srt.take k).map Prod.snd → A2[m]! = (tArr t Y)[m]!) ∧
  (∀ e ∈ srt.take k, (A2[e.2]!).dl.toNat = min (D e.2) Lm) ∧ blc.size = 16 ∧
  ∀ j, j < 16 → (blc[j]!).toNat = ZlibNgF.Math.TreesRank.cntOf ((srt.take k).map (fun e => min (D e.2) Lm)) j

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

theorem p2Fin_SH (t : DescSel) (Y : DeflateState) (A : Array Ct) (blc : Array UInt16) (o sl : UInt32)
    (ii n : Int32) (bits : UInt32) (ov xbits : Int32) (nN : Nat) (hn : n.toInt = nN) (hnE : nN < tElems t)
    (hA : nN < A.size) (hx : xbits.toInt = xb t nN) (hbits : bits.toNat ≤ 15) :
    Sat (SH H i z b (LS t Y A blc o sl) d)
      (p2Fin (some b) (.ref (tRef t b) 0) (tSD t).get.static_tree ii n bits ov xbits)
      (fun r H' => r = (ii + 1, ov) ∧ H' = SH H i z b (LS t Y A blc
        (o + ((A[nN]!).fc.toNat * (bits.toNat + xb t nN)).toUInt32)
        (sl + (stp t nN (A[nN]!).fc.toNat).toUInt32)) d) := by
  have hxl := xb_le t nN hnE
  unfold p2Fin
  rw [hn]
  refine Sat.bind (Sat.of_eq (ctFc_T t _ nN (by simp; omega)) ?_)
  simp only [tArr_LS]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  simp only [LS_opt, LS_set_opt]
  rw [opt_term _ bits xbits (xb t nN) hx hbits hxl]
  cases t
  · simp only [tSD, StaticDescPtr.get]
    refine Sat.bind (Sat.of_eq (static_ldl nN (by simp [tElems] at hnE; omega) _) ?_)
    rw [chkI32_ok (by omega) (by have := (static_ltree[nN]!).dl.toNat_lt; omega)]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    simp only [LS_stat, LS_set_stat]
    rw [stat_term _ _ _ (xb .l_desc nN) (by rw [i32_ofInt _ (by omega) (by have := (static_ltree[nN]!).dl.toNat_lt; omega), hx])]
    exact Sat.pure ⟨rfl, rfl⟩
  · simp only [tSD, StaticDescPtr.get]
    refine Sat.bind (Sat.of_eq (static_ddl nN (by simp [tElems] at hnE; omega) _) ?_)
    rw [chkI32_ok (by omega) (by have := (static_dtree[nN]!).dl.toNat_lt; omega)]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    simp only [LS_stat, LS_set_stat]
    rw [stat_term _ _ _ (xb .d_desc nN) (by rw [i32_ofInt _ (by omega) (by have := (static_dtree[nN]!).dl.toNat_lt; omega), hx])]
    exact Sat.pure ⟨rfl, rfl⟩
  · simp only [tSD, StaticDescPtr.get]
    refine Sat.pure ⟨rfl, ?_⟩
    simp only [stp]; rw [show (0 : Nat).toUInt32 = 0 from rfl, UInt32.add_zero]

theorem p2Tail_SH (t : DescSel) (Y : DeflateState) (A : Array Ct) (blc : Array UInt16) (o sl : UInt32)
    (ii n : Int32) (bits : UInt32) (ov : Int32) (nN : Nat) (hn : n.toInt = nN) (hnE : nN < tElems t)
    (hA : nN < A.size) (hbits : bits.toNat ≤ 15) (hbs : blc.size = 16) :
    Sat (SH H i z b (LS t Y A blc o sl) d)
      (p2Tail (some b) (.ref (tRef t b) 0) (tSD t).get.static_tree (tSD t).get.extra_bits (tSD t).get.extra_base
        ii n bits ov)
      (fun r H' => r = (ii + 1, ov) ∧ H' = SH H i z b (LS t Y (A.set! nN { A[nN]! with dl := bits.toUInt16 })
        (blc.set! bits.toNat (blc[bits.toNat]! + 1))
        (o + ((A[nN]!).fc.toNat * (bits.toNat + xb t nN)).toUInt32)
        (sl + (stp t nN (A[nN]!).fc.toNat).toUInt32)) d) := by
  rw [p2Tail_eq]
  rw [hn]
  refine Sat.bind (Sat.of_eq (ctSetDl_T t _ nN (by simp; omega) _) ?_)
  simp only [tArr_LS, tPut_LS]
  refine Sat.bind (Sat.of_eq (blCountGet_SH _ bits.toNat (by simp; omega)) ?_)
  refine Sat.bind (Sat.of_eq (blCountSet_SH _ bits.toNat (by simp; omega) _) ?_)
  simp only [LS_bc, LS_set_bc]
  have hfc : ((A.set! nN { A[nN]! with dl := bits.toUInt16 })[nN]!).fc = (A[nN]!).fc := by
    rw [set!_get_eq _ _ _ hA]
  obtain ⟨x, hx, e⟩ := xbits_eq t n (by omega) (by omega)
    (fun x => p2Fin (some b) (.ref (tRef t b) 0) (tSD t).get.static_tree ii n bits ov x)
    (SH H i z b (LS t Y (A.set! nN { A[nN]! with dl := bits.toUInt16 })
      (blc.set! bits.toNat (blc[bits.toNat]! + 1)) o sl) d)
  rw [hn] at e hx
  simp only [Int.toNat_natCast] at hx
  obtain ⟨r, H', e', q⟩ := p2Fin_SH (H := H) (i := i) (z := z) (b := b) (d := d) t Y
    (A.set! nN { A[nN]! with dl := bits.toUInt16 }) (blc.set! bits.toNat (blc[bits.toNat]! + 1)) o sl ii n bits ov x nN
    hn hnE (by simp; omega) hx hbits
  rw [hfc] at q
  exact ⟨r, H', e.trans e', q⟩


/-- **The leaf pass.** Every sorted leaf `e` gets `Len = min(depth, max_length)` (its parent `p` holds
`min(depth - 1, max_length)`), `bl_count` counts the clamped lengths, `overflow` grows by the leaves deeper than
`max_length`, `opt_len` grows by `Σ f * (len + extra)` and `static_len` by `Σ f * (stree.Len + extra)` (none for the
bit-length tree). -/
theorem p2_SH (t : DescSel) (Y : DeflateState) (qS : Bool) (srt : List (Nat × Nat)) (D : Nat → Nat) (Lm : Nat)
    (L : UInt32) (nl ov0 : Int32) (hL : L.toNat = Lm) (hLm1 : 1 ≤ Lm) (hLm : Lm ≤ 15)
    (hnl : nl.toInt = srt.length) (hN : srt.length ≤ 286) (hov0 : 0 ≤ ov0.toInt) (hov0' : ov0.toInt ≤ 1000)
    (hS : (qArr qS Y).size = 287) (hsrt : ∀ p, p < srt.length → (qArr qS Y)[p]! = pk srt[p]!)
    (hb : ∀ e ∈ srt, e.1 < 65536 ∧ e.2 < tElems t) (hnd : (srt.map Prod.snd).Nodup)
    (hfc : ∀ e ∈ srt, ((tArr t Y)[e.2]!).fc.toNat = e.1)
    (hpar : ∀ e ∈ srt, 1 ≤ D e.2 ∧ ∃ p, ((tArr t Y)[e.2]!).dl.toNat = p ∧ tElems t ≤ p ∧ p < (tArr t Y).size ∧
      ((tArr t Y)[p]!).dl.toNat = min (D e.2 - 1) Lm)
    (hAs : tElems t < (tArr t Y).size) (hAs' : (tArr t Y).size ≤ 1000)
    (hbc : Y.bl_count.size = 16) (hbz : ∀ j, j < 16 → Y.bl_count[j]! = 0) :
    Sat (SH H i z b Y d)
      (cwhile (p2Cond nl) (p2Body (some b) (.ref (tRef t b) 0) (tSD t).get.static_tree (.ref (qRef qS b) 0)
        (tSD t).get.extra_bits (tSD t).get.extra_base L) (0, ov0))
      (fun x H' => ∃ A2 blc, H' = SH H i z b (LS t Y A2 blc (Y.opt_len + ((srt.map (optT t D Lm)).sum).toUInt32)
          (Y.static_len + ((srt.map (statT t)).sum).toUInt32)) d ∧
        P2Inv t Y srt D Lm ov0.toInt srt.length A2 blc x.2.toInt) := by
  refine sat_cwhile (I := fun (x : Int32 × Int32) H' => ∃ (k : Nat) (A2 : Array Ct) (blc : Array UInt16),
      k ≤ srt.length ∧ x.1.toInt = k ∧
      H' = SH H i z b (LS t Y A2 blc (Y.opt_len + (((srt.take k).map (optT t D Lm)).sum).toUInt32)
          (Y.static_len + (((srt.take k).map (statT t)).sum).toUInt32)) d ∧
      P2Inv t Y srt D Lm ov0.toInt k A2 blc x.2.toInt)
    (μ := fun x => srt.length - x.1.toInt.toNat) _ ?_ ⟨0, tArr t Y, Y.bl_count, Nat.zero_le _, by simp, ?_, ?_⟩
    (by simp [fuel]; omega)
  rotate_left
  · simp only [List.take_zero, List.map_nil, List.sum_nil]
    rw [show (0 : Nat).toUInt32 = 0 from rfl, UInt32.add_zero, UInt32.add_zero]
    congr 1; cases t <;> rfl
  · refine ⟨by simp, rfl, fun _ => rfl, fun _ _ => rfl, fun e he => by simp at he, hbc, fun j hj => ?_⟩
    rw [hbz j hj]; simp [ZlibNgF.Math.TreesRank.cntOf]
  rintro ⟨ii, ov⟩ _ ⟨k, A2, blc, hk, hii, rfl, hov, hA2s, hA2fc, hA2o, hA2l, hbcs, hbcv⟩
  dsimp only at hii hov ⊢
  simp only [p2Cond]
  refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · have hc' : k < srt.length := by
      have := Int32.lt_iff_toInt_lt.mp (show ii < nl by simpa using hc); omega
    have hcnt : (srt.take k).countP (fun e => decide (Lm < D e.2)) ≤ k := by
      have := List.countP_le_length (p := fun e => decide (Lm < D e.2)) (l := srt.take k)
      simp only [List.length_take] at this; omega
    have hovb : ov.toInt ≤ 1000 + k := by omega
    have hov0b : 0 ≤ ov.toInt := by omega
    generalize he : srt[k]! = e
    have hmem : e ∈ srt := he ▸ mem_of_idx' srt k hc'
    obtain ⟨he1, he2⟩ := hb e hmem
    obtain ⟨hD1, p, hp1, hp2, hp3, hp4⟩ := hpar e hmem
    have hnin : e.2 ∉ (srt.take k).map Prod.snd := by
      intro hm
      obtain ⟨e', he', eq⟩ := List.mem_map.mp hm
      exact nd_take_ne srt hnd k hc' e' he' (by rw [he]; exact eq)
    have hpin : p ∉ (srt.take k).map Prod.snd := by
      intro hm
      obtain ⟨e', he', eq⟩ := List.mem_map.mp hm
      have := (hb e' (List.mem_of_mem_take he')).2; omega
    rw [p2Body_eq]
    rw [hii]
    refine Sat.bind (Sat.of_eq (dwGet_Q qS _ k (by simp; omega)) ?_)
    simp only [qArr_LS]
    rw [hsrt k hc', he, pk_node e (by omega) (by omega)]
    refine Sat.bind (Sat.of_eq (ctDl_T t _ e.2 (by simp; omega)) ?_)
    simp only [tArr_LS]
    rw [hA2o e.2 hnin, hp1]
    refine Sat.bind (Sat.of_eq (ctDl_T t _ p (by simp; omega)) ?_)
    simp only [tArr_LS]
    rw [hA2o p hpin]
    have hb0 : ((tArr t Y)[p]!.dl.toUInt32 + 1).toNat = min (D e.2 - 1) Lm + 1 := by
      rw [UInt32.toNat_add, u16_u32, hp4]; simp; omega
    -- the rest of the trip, for the clamped `bits` and the new `overflow`
    have fin : ∀ (bits : UInt32) (ov' : Int32), bits.toNat = min (D e.2) Lm →
        ov'.toInt = ov.toInt + (if Lm < D e.2 then 1 else 0) →
        Sat (SH H i z b (LS t Y A2 blc (Y.opt_len + (((srt.take k).map (optT t D Lm)).sum).toUInt32)
            (Y.static_len + (((srt.take k).map (statT t)).sum).toUInt32)) d)
          (p2Tail (some b) (.ref (tRef t b) 0) (tSD t).get.static_tree (tSD t).get.extra_bits (tSD t).get.extra_base
            ii (pq_node (pk e)) bits ov')
          (fun s2 H2 => (∃ (k : Nat) (A2 : Array Ct) (blc : Array UInt16),
            k ≤ srt.length ∧ s2.1.toInt = k ∧
            H2 = SH H i z b (LS t Y A2 blc (Y.opt_len + (((srt.take k).map (optT t D Lm)).sum).toUInt32)
              (Y.static_len + (((srt.take k).map (statT t)).sum).toUInt32)) d ∧
            P2Inv t Y srt D Lm ov0.toInt k A2 blc s2.2.toInt) ∧
            srt.length - s2.1.toInt.toNat < srt.length - (k : Int).toNat) := by
      intro bits ov' hbits hov'
      refine Sat.mono (p2Tail_SH t Y A2 blc _ _ ii (pq_node (pk e)) bits ov' e.2 (pk_node e (by omega) (by omega))
        he2 (by omega) (by omega) hbcs) ?_
      rintro r H2 ⟨rfl, rfl⟩
      have hfce : ((A2[e.2]!).fc).toNat = e.1 := by rw [hA2fc]; exact hfc e hmem
      have htk := take_succ' srt k hc'
      rw [he] at htk
      have hbl : bits.toNat < 16 := by omega
      have hcb : (blc[bits.toNat]!).toNat ≤ k := by
        rw [hbcv _ hbl]; have := cntOf_le ((srt.take k).map (fun e => min (D e.2) Lm)) bits.toNat
        simp only [List.length_map, List.length_take] at this; omega
      refine ⟨⟨k + 1, A2.set! e.2 { A2[e.2]! with dl := bits.toUInt16 }, blc.set! bits.toNat (blc[bits.toNat]! + 1),
        by omega, ?_, ?_, ?_⟩, ?_⟩
      · rw [i32_add1 _ (by omega) (by omega), hii]; push_cast; rfl
      · rw [htk, hfce]
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero]
        rw [u32_acc, u32_acc, hbits]
        rfl
      · refine ⟨?_, by simp [hA2s], fun m => ?_, fun m hm => ?_, fun e' he' => ?_, by simp [hbcs], fun j hj => ?_⟩
        · rw [hov', hov, htk, List.countP_append]; split <;> simp_all <;> omega
        · by_cases hm : m = e.2
          · subst hm; rw [set!_get_eq _ _ _ (by omega)]; exact hA2fc _
          · rw [set!_get_ne _ _ _ _ hm]; exact hA2fc m
        · rw [htk] at hm
          have hm2 : m ≠ e.2 := fun eq => hm (by simp [eq])
          rw [set!_get_ne _ _ _ _ hm2]
          exact hA2o m (fun h => hm (by simp only [List.map_append, List.mem_append]; exact Or.inl h))
        · rw [htk] at he'
          rcases List.mem_append.mp he' with h1 | h1
          · have hne : e'.2 ≠ e.2 := by rw [← he]; exact nd_take_ne srt hnd k hc' e' h1
            rw [set!_get_ne _ _ _ _ hne]; exact hA2l e' h1
          · simp only [List.mem_singleton] at h1; subst h1
            rw [set!_get_eq _ _ _ (by omega)]
            simp only [UInt32.toNat_toUInt16]; omega
        · rw [htk, List.map_append, List.map_singleton, cntOf_snoc]
          by_cases hj' : j = bits.toNat
          · subst hj'
            rw [set!_get_eq _ _ _ (by omega), UInt16.toNat_add, hbcv _ hj]
            have := cntOf_le ((srt.take k).map (fun e => min (D e.2) Lm)) bits.toNat
            simp only [List.length_map, List.length_take] at this
            simp only [hbits, ↓reduceIte]
            rw [show ((1 : UInt16)).toNat = 1 from rfl, ← hbits]
            omega
          · rw [set!_get_ne _ _ _ _ hj', hbcv j hj]
            have : ¬ (min (D e.2) Lm = j) := by omega
            simp [this]
      · dsimp only; rw [i32_add1 _ (by omega) (by omega), hii]; omega
    by_cases hgt : (tArr t Y)[p]!.dl.toUInt32 + 1 > L
    · have hgt' : Lm < D e.2 := by
        have := UInt32.lt_iff_toNat_lt.mp hgt; rw [hb0, hL] at this; omega
      simp only [hgt, ↓reduceIte]
      rw [chkI32_ok (v := ov.toInt + 1) (by omega) (by omega)]
      refine Sat.bind (Sat.pure ?_)
      exact fin L _ (by omega) (by rw [i32_ofInt (ov.toInt + 1) (by omega) (by omega)]; simp [hgt'])
    · have hle : D e.2 ≤ Lm := by
        have : ¬ (Lm < min (D e.2 - 1) Lm + 1) := fun h => hgt (UInt32.lt_iff_toNat_lt.mpr (by rw [hb0, hL]; exact h))
        omega
      simp only [hgt, ↓reduceIte]
      exact fin _ ov (by rw [hb0]; omega) (by simp only [show ¬ (Lm < D e.2) by omega, ↓reduceIte]; omega)
  · have hc' : ¬ k < srt.length := by
      have hc2 : ¬ ii < nl := by simpa using hc
      intro h; exact hc2 (Int32.lt_iff_toInt_lt.mpr (by omega))
    have hkN : k = srt.length := by omega
    subst hkN
    simp only [List.take_length] at hov hA2o hA2l hbcv ⊢
    exact ⟨A2, blc, rfl, by simp only [P2Inv, List.take_length]; exact ⟨hov, hA2s, hA2fc, hA2o, hA2l, hbcs, hbcv⟩⟩

end

end ZlibNgF.Proof.TreesBitlen
