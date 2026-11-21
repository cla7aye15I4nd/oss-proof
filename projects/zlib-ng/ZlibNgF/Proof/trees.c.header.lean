import ZlibNgF.Proof.«trees.c.prims»
import ZlibNgF.Math.TreesHdr

/-!
# `scan_tree` (`ZlibNgF`)

On `SH` heaps: `scan_tree(s, tree, max_code)` on the literal/length or distance tree with code lengths at most 15
stores the `0xffff` guard at `tree[max_code + 1].Len` and adds to `bl_tree[t].Freq` the number of bit-length
symbols `t` of the model's `treeTokens` (`Math/OverlayHeader.lean`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesHeader
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Math.Huff
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## Array facts -/

theorem tArr_bl (t : DescSel) (ht : t ≠ .bl_desc) (s : DeflateState) (C : Array Ct) :
    tArr t (tPut .bl_desc s C) = tArr t s := by
  cases t <;> first | rfl | exact absurd rfl ht

theorem tPut_bl_comm (t : DescSel) (ht : t ≠ .bl_desc) (s : DeflateState) (A C : Array Ct) :
    tPut t (tPut .bl_desc s C) A = tPut .bl_desc (tPut t s A) C := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- `tree[k].Freq = v` read back. -/
theorem setFc_get (C : Array Ct) (k c : Nat) (v : UInt16) :
    ((C.set! k { C[k]! with fc := v })[c]!).fc = if c = k ∧ k < C.size then v else (C[c]!).fc := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases e : k = c
  · subst e
    by_cases hk : k < C.size
    · simp [hk]
    · simp [hk]
  · simp [e, Ne.symm e]

theorem setFc_size (C : Array Ct) (k : Nat) (v : Ct) : (C.set! k v).size = C.size := by simp

theorem i32_eq_iff (a b : Int32) : a = b ↔ a.toInt = b.toInt := by
  constructor
  · rintro rfl; rfl
  · intro h; exact Int32.toInt_inj.mp h

/-- A tree array's code lengths as numbers. -/
def lenOf (A : Array Ct) (n : Nat) : Nat := (A[n]!).dl.toNat

theorem scanTokens_congr (f g : Nat → Nat) (m : Nat) (h : ∀ n, n < m → f n = g n) :
    ∀ k n (p : Int) (c mx mn nl : Nat), scanTokens f m k n p c mx mn nl = scanTokens g m k n p c mx mn nl := by
  have hn : ∀ n, nextLen f m n = nextLen g m n := fun n => by
    unfold nextLen; split
    · exact h _ (by omega)
    · rfl
  intro k
  induction k with
  | zero => intro n p c mx mn nl; rfl
  | succ k ih =>
    intro n p c mx mn nl
    simp only [scanTokens, hn, ih]

theorem treeTokens_congr (f g : Nat → Nat) (m : Nat) (hm : 1 ≤ m) (h : ∀ n, n < m → f n = g n) :
    treeTokens f m = treeTokens g m := by
  unfold treeTokens; rw [h 0 hm]; exact scanTokens_congr f g m h _ _ _ _ _ _ _

/-- One frequency increment read back. -/
theorem bump_get (C : Array Ct) (k : Nat) (hk : k < C.size) (w : UInt16) (hw : (C[k]!).fc.toNat + w.toNat < 65536)
    (c : Nat) : ((C.set! k { C[k]! with fc := (C[k]!).fc + w })[c]!).fc.toNat =
      (C[c]!).fc.toNat + if c = k then w.toNat else 0 := by
  rw [setFc_get]
  by_cases e : c = k
  · subst e; simp only [hk, and_self, ↓reduceIte, UInt16.toNat_add]; exact Nat.mod_eq_of_lt hw
  · simp [e]

/-- The loop state of `scan_tree`: `n`, `prevlen`, `nextlen`, `count`, `max_count`, `min_count`. -/
abbrev SX := Int32 × Int32 × Int32 × UInt16 × UInt16 × UInt16

/-- The loop body of `scan_tree` (a copy of the translation's lambda). -/
def scanBody (tree bltree : CtPtr) : SX → M SX :=
    (fun ((n, prevlen, nextlen, count, max_count, min_count) :
        Int32 × Int32 × Int32 × UInt16 × UInt16 × UInt16) => do
      let curlen := nextlen
      let nextlen : Int32 := (← ctDl tree (n.toInt + 1)).toUInt32.toInt32
      let count := count + 1
      if count < max_count && curlen == nextlen then
        return (n + 1, prevlen, nextlen, count, max_count, min_count)
      else if count < min_count then
        let fr ← ctFc bltree curlen.toInt
        ctSetFc bltree curlen.toInt (fr + count)
      else if curlen != 0 then
        if curlen != prevlen then
          ctSetFc bltree curlen.toInt ((← ctFc bltree curlen.toInt) + 1)
        ctSetFc bltree REP_3_6 ((← ctFc bltree REP_3_6) + 1)
      else if count <= 10 then
        ctSetFc bltree REPZ_3_10 ((← ctFc bltree REPZ_3_10) + 1)
      else
        ctSetFc bltree REPZ_11_138 ((← ctFc bltree REPZ_11_138) + 1)
      let count : UInt16 := 0
      let prevlen := curlen
      let (max_count, min_count) : UInt16 × UInt16 :=
        if nextlen == 0 then (138, 3)
        else if curlen == nextlen then (6, 3)
        else (7, 4)
      pure (n + 1, prevlen, nextlen, count, max_count, min_count))

/-- The tail of `scan_tree` after the initial `max_count` / `min_count`. -/
def scanTail (st : StatePtr) (tree : CtPtr) (max_code : Int32) (nextlen : Int32) (max_count min_count : UInt16) :
    M Unit := do
  ctSetDl tree (← chkI32 (max_code.toInt + 1)).toInt 0xffff
  let bltree ← blTreeP st
  let _ ← cwhile
    (fun (x : SX) => pure (x.1 <= max_code, x))
    (scanBody tree bltree)
    ((0 : Int32), (-1 : Int32), nextlen, (0 : UInt16), max_count, min_count)

theorem scan_tree_eq (st : StatePtr) (tree : CtPtr) (max_code : Int32) :
    scan_tree st tree max_code = (do
      let nextlen : Int32 := (← ctDl tree 0).toUInt32.toInt32
      if nextlen == 0 then scanTail st tree max_code nextlen 138 3 else scanTail st tree max_code nextlen 7 4) := by
  rfl

theorem u16_succ (c : UInt16) (h : c.toNat < 138) : (c + 1).toNat = c.toNat + 1 := by
  rw [UInt16.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)

theorem i32_eq_toInt (a b : Int32) : (a == b) = true ↔ a.toInt = b.toInt := by
  simp only [beq_iff_eq]; exact ⟨fun h => h ▸ rfl, fun h => Int32.toInt_inj.mp h⟩

theorem i32_ne_toInt (a b : Int32) : (a != b) = true ↔ a.toInt ≠ b.toInt := by
  simp only [bne_iff_ne, ne_eq]; exact not_congr ⟨fun h => h ▸ rfl, fun h => Int32.toInt_inj.mp h⟩

/-- The `(max_count, min_count)` choice after a group. -/
theorem mxmn (nx nl : Int32) (NL nl' : Nat) (h1 : nx.toInt = NL) (h2 : nl.toInt = nl') :
    (if (nx == 0) = true then ((138 : UInt16), (3 : UInt16)) else if (nl == nx) = true then (6, 3) else (7, 4)).1.toNat =
      (if NL = 0 then 138 else if nl' = NL then 6 else 7) ∧
    (if (nx == 0) = true then ((138 : UInt16), (3 : UInt16)) else if (nl == nx) = true then (6, 3) else (7, 4)).2.toNat =
      (if NL = 0 then 3 else if nl' = NL then 3 else 4) := by
  have a : (nx == 0) = true ↔ NL = 0 := by rw [i32_eq_toInt]; simp only [Int32.toInt_zero]; omega
  have c : (nl == nx) = true ↔ nl' = NL := by rw [i32_eq_toInt]; omega
  by_cases e1 : NL = 0
  · simp [a.mpr e1, e1]
  · have e1' : ¬ (nx == 0) = true := fun h => e1 (a.mp h)
    by_cases e2 : nl' = NL
    · simp [e1, e1', c.mpr e2, e2]
    · have e2' : ¬ (nl == nx) = true := fun h => e2 (c.mp h)
      simp [e1, e1', e2, e2']

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- The loop invariant of `scan_tree` on tree `t` (guarded array `A`, `m = max_code + 1` codes): the state is `s` with
the tree `A` and the bit-length tree `C`; at position `n` the frequencies of `C` plus the symbols still to come are
those of `s.bl_tree` plus all of `treeTokens`. -/
def SInv (t : DescSel) (s : DeflateState) (A : Array Ct) (m : Nat) (x : SX) (H' : Heap) : Prop :=
  ∃ (C : Array Ct) (n : Nat) (p : Int) (nl : Nat),
    H' = SH H i z b (tPut .bl_desc (tPut t s A) C) d ∧ C.size = s.bl_tree.size ∧
    x.1.toInt = n ∧ n ≤ m ∧ x.2.1.toInt = p ∧ x.2.2.1.toInt = nl ∧ (n < m → nl ≤ 15) ∧
    (p = -1 ∨ (0 ≤ p ∧ p ≤ 15)) ∧
    x.2.2.2.1.toNat < x.2.2.2.2.1.toNat ∧ x.2.2.2.2.1.toNat ≤ 138 ∧ 3 ≤ x.2.2.2.2.2.toNat ∧ x.2.2.2.2.2.toNat ≤ 4 ∧
    ∀ c, c < 19 → (C[c]!).fc.toNat +
      (scanTokens (lenOf A) m (m - n) n p x.2.2.2.1.toNat x.2.2.2.2.1.toNat x.2.2.2.2.2.toNat nl).count c =
      (s.bl_tree[c]!).fc.toNat + (treeTokens (lenOf A) m).count c

theorem scan_step (t : DescSel) (ht : t ≠ .bl_desc) (s : DeflateState) (A : Array Ct) (m : Nat) (mc : Int32)
    (hmc : mc.toInt + 1 = m) (hm : m < A.size) (hm1k : m ≤ 1000) (hA : (A[m]!).dl = 0xffff) (hA15 : ∀ n, n < m → lenOf A n ≤ 15)
    (hbl : 19 ≤ s.bl_tree.size) (hcap : ∀ c, c < 19 → (s.bl_tree[c]!).fc.toNat + m < 65536)
    (x : SX) (H' : Heap) (hI : SInv (H := H) (i := i) (z := z) (b := b) (d := d) t s A m x H') (hlt : x.1 ≤ mc) :
    Sat H' (scanBody (.ref (tRef t b) 0) (.ref (.bl_tree b) 0) x)
      (fun x' H2 => SInv (H := H) (i := i) (z := z) (b := b) (d := d) t s A m x' H2 ∧
        m - x'.1.toInt.toNat < m - x.1.toInt.toNat) := by
  obtain ⟨n, p, nl, cnt, mx, mn⟩ := x
  obtain ⟨C, n', p', nl', rfl, hCs, hn, hnm, hp, hnl, hnl15, hp15, hcm, hmx, hmn3, hmn4, hcount⟩ := hI
  dsimp only at hn hp hnl hcm hmx hmn3 hmn4 hcount hlt ⊢
  have hlt' : n' < m := by have := Int32.le_iff_toInt_le.mp hlt; omega
  have hk : m - n' = (m - (n' + 1)) + 1 := by omega
  have e1 : n.toInt + 1 = ((n' + 1 : Nat) : Int) := by omega
  unfold scanBody
  simp only [e1]
  refine Sat.bind (Sat.of_eq (ctDl_T t _ (n' + 1) (by rw [tArr_bl t ht, tArr_tPut]; omega)) ?_)
  simp only [tArr_bl t ht, tArr_tPut]
  -- the length just read is the model's `nextLen`
  have hNL : (A[n' + 1]!.dl.toUInt32.toInt32).toInt = nextLen (lenOf A) m n' := by
    have e : (A[n' + 1]!.dl.toUInt32.toInt32).toInt = (A[n' + 1]!.dl.toNat : Int) := by
      have := (A[n' + 1]!).dl.toNat_lt
      rw [DeflateAlloc.u32_toInt32_toInt _ (by simp only [UInt16.toNat_toUInt32]; omega), UInt16.toNat_toUInt32]
    rw [e]; unfold nextLen lenOf
    split
    · rfl
    · obtain rfl : n' + 1 = m := by omega
      rw [hA]; rfl
  have hNL15 : n' + 1 < m → nextLen (lenOf A) m n' ≤ 15 := fun h => by
    unfold nextLen; rw [ite_t h]; exact hA15 _ h
  rw [hk] at hcount
  simp only [scanTokens] at hcount
  generalize A[n' + 1]!.dl.toUInt32.toInt32 = nx at hNL ⊢
  generalize nextLen (lenOf A) m n' = NL at hNL hNL15 hcount
  have hs := u16_succ cnt (by omega)
  have hsucc : (n + 1).toInt = ((n' + 1 : Nat) : Int) := by
    rw [TreesInit.i32_succ n (by omega) (by omega)]; omega
  have hmu : m - (n + 1).toInt.toNat < m - n.toInt.toNat := by rw [hsucc, hn]; omega
  have bc1 : ((decide (cnt + 1 < mx) && nl == nx) = true) ↔ (cnt.toNat + 1 < mx.toNat ∧ nl' = NL) := by
    rw [Bool.and_eq_true, decide_eq_true_iff, UInt16.lt_iff_toNat_lt, hs, i32_eq_toInt, hnl, hNL]; omega
  by_cases c1 : cnt.toNat + 1 < mx.toNat ∧ nl' = NL
  · rw [ite_t (bc1.mpr c1)]
    simp only [ite_t c1] at hcount
    refine Sat.pure ⟨⟨C, n' + 1, p', NL, rfl, hCs, hsucc, by omega, hp, hNL, hNL15, hp15, by dsimp only; rw [hs]; omega, hmx, hmn3,
      hmn4, fun c hc => by rw [hs]; exact hcount c hc⟩, hmu⟩
  rw [ite_f (fun h => c1 (bc1.mp h))]
  simp only [ite_f c1] at hcount
  have hnl15' := hnl15 hlt'
  generalize hG : groupTokens p' (cnt.toNat + 1) mn.toNat nl' = G at hcount
  have cap : ∀ c, c < 19 → (C[c]!).fc.toNat + G.count c < 65536 := fun c hc => by
    have h1 := hcount c hc
    have h2 := hcap c hc
    have h3 := List.count_le_length (a := c) (l := treeTokens (lenOf A) m)
    have h4 := treeTokens_length (lenOf A) m
    rw [List.count_append] at h1
    omega
  have fin : ∀ (C' : Array Ct) (mx' mn' : UInt16), C'.size = s.bl_tree.size →
      (∀ c, c < 19 → (C'[c]!).fc.toNat = (C[c]!).fc.toNat + G.count c) →
      mx'.toNat = (if NL = 0 then 138 else if nl' = NL then 6 else 7) →
      mn'.toNat = (if NL = 0 then 3 else if nl' = NL then 3 else 4) →
      SInv (H := H) (i := i) (z := z) (b := b) (d := d) t s A m (n + 1, nl, nx, 0, mx', mn')
        (SH H i z b (tPut .bl_desc (tPut t s A) C') d) ∧ m - (n + 1).toInt.toNat < m - n.toInt.toNat := by
    intro C' mx' mn' hs' hC' h1 h2
    refine ⟨⟨C', n' + 1, nl', NL, rfl, hs', hsucc, by omega, hnl, hNL, hNL15, Or.inr ⟨by omega, by omega⟩, ?_, ?_, ?_, ?_,
      fun c hc => ?_⟩, hmu⟩
    · dsimp only; rw [h1]; simp only [UInt16.toNat_zero]; split <;> (try split) <;> omega
    · dsimp only; rw [h1]; split <;> (try split) <;> omega
    · dsimp only; rw [h2]; split <;> (try split) <;> omega
    · dsimp only; rw [h2]; split <;> (try split) <;> omega
    · dsimp only; rw [h1, h2, hC' c hc]
      have := hcount c hc
      rw [List.count_append] at this
      simp only [UInt16.toNat_zero]
      omega
  obtain ⟨m1, m2⟩ := mxmn nx nl NL nl' hNL hnl
  have hX : (tArr .bl_desc (tPut .bl_desc (tPut t s A) C)).size = s.bl_tree.size := by simp [hCs]
  have r16 : REP_3_6 = ((16 : Nat) : Int) := rfl
  have r17 : REPZ_3_10 = ((17 : Nat) : Int) := rfl
  have r18 : REPZ_11_138 = ((18 : Nat) : Int) := rfl
  rw [hnl, r16, r17, r18]
  by_cases c2 : cnt.toNat + 1 < mn.toNat
  · have b2 : cnt + 1 < mn := by rw [UInt16.lt_iff_toNat_lt, hs]; exact c2
    rw [ite_t b2]
    have hGc : ∀ c, G.count c = if c = nl' then cnt.toNat + 1 else 0 := fun c => by
      rw [← hG]; unfold groupTokens; rw [ite_t c2, List.count_replicate]
      by_cases e : c = nl'
      · subst e; simp
      · have e' : ¬ nl' = c := fun h => e h.symm
        simp [e, e']
    refine Sat.bind (Sat.of_eq (ctFc_T .bl_desc _ nl' (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (ctSetFc_T .bl_desc _ nl' (by omega) _) ?_)
    simp only [tArr_tPut, tPut_tPut]
    have cw := cap nl' (by omega)
    rw [hGc, ite_t rfl] at cw
    refine Sat.pure (fin _ _ _ (by simp [hCs]) (fun c hc => ?_) m1 m2)
    rw [bump_get C nl' (by omega) _ (by rw [hs]; omega), hGc, hs]
  rw [ite_f (fun h => c2 (by have := UInt16.lt_iff_toNat_lt.mp h; rw [hs] at this; exact this))]
  by_cases c3 : nl' ≠ 0
  · have b3 : (nl != 0) = true := by rw [i32_ne_toInt, hnl]; simp; omega
    rw [ite_t b3]
    by_cases c4 : (nl' : Int) ≠ p'
    · have b4 : (nl != p) = true := by rw [i32_ne_toInt, hnl, hp]; exact c4
      rw [ite_t b4]
      have hGc : ∀ c, G.count c = (if c = nl' then 1 else 0) + if c = 16 then 1 else 0 := fun c => by
        rw [← hG]; unfold groupTokens; rw [ite_f (by omega), ite_t c3, ite_t c4]
        simp only [List.cons_append, List.nil_append, List.count_cons, List.count_nil, beq_iff_eq]
        (repeat' split) <;> omega
      refine Sat.bind (Sat.of_eq (ctFc_T .bl_desc _ nl' (by omega)) ?_)
      refine Sat.bind (Sat.of_eq (ctSetFc_T .bl_desc _ nl' (by omega) _) ?_)
      simp only [tArr_tPut, tPut_tPut]
      refine Sat.bind (Sat.of_eq (ctFc_T .bl_desc _ 16 (by simp; omega)) ?_)
      refine Sat.bind (Sat.of_eq (ctSetFc_T .bl_desc _ 16 (by simp; omega) _) ?_)
      simp only [tArr_tPut, tPut_tPut]
      have cw := cap nl' (by omega)
      have cw2 := cap 16 (by omega)
      rw [hGc, ite_t rfl] at cw
      rw [hGc, ite_t rfl] at cw2
      have b1 := bump_get C nl' (by omega) 1 (by simp; split at cw <;> omega)
      refine Sat.pure (fin _ _ _ (by simp [hCs]) (fun c hc => ?_) m1 m2)
      rw [bump_get _ 16 (by simp; omega) 1 (by
        rw [b1]
        simp only [show ¬ (16 = nl') by omega, ↓reduceIte] at cw2 ⊢
        simp; omega), b1, hGc]
      simp only [UInt16.toNat_one]
      omega
    · have b4 : ¬ (nl != p) = true := by rw [i32_ne_toInt, hnl, hp]; exact c4
      rw [ite_f b4]
      have hGc : ∀ c, G.count c = if c = 16 then 1 else 0 := fun c => by
        rw [← hG]; unfold groupTokens; rw [ite_f (by omega), ite_t c3, ite_f c4]
        simp only [List.nil_append, List.count_cons, List.count_nil, beq_iff_eq]
        (repeat' split) <;> omega
      refine Sat.bind (Sat.of_eq (ctFc_T .bl_desc _ 16 (by simp; omega)) ?_)
      refine Sat.bind (Sat.of_eq (ctSetFc_T .bl_desc _ 16 (by simp; omega) _) ?_)
      simp only [tArr_tPut, tPut_tPut]
      have cw2 := cap 16 (by omega)
      rw [hGc, ite_t rfl] at cw2
      refine Sat.pure (fin _ _ _ (by simp [hCs]) (fun c hc => ?_) m1 m2)
      rw [bump_get _ 16 (by omega) 1 (by simp; omega), hGc]
      simp only [UInt16.toNat_one]
  · have b3 : ¬ (nl != 0) = true := by rw [i32_ne_toInt, hnl]; simp; omega
    rw [ite_f b3]
    have c0 : nl' = 0 := by omega
    by_cases c5 : cnt.toNat + 1 ≤ 10
    · have b5 : cnt + 1 ≤ 10 := by rw [UInt16.le_iff_toNat_le, hs]; exact c5
      rw [ite_t b5]
      have hGc : ∀ c, G.count c = if c = 17 then 1 else 0 := fun c => by
        rw [← hG]; unfold groupTokens; rw [ite_f (by omega), ite_f (by omega), ite_t c5]
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        (repeat' split) <;> omega
      refine Sat.bind (Sat.of_eq (ctFc_T .bl_desc _ 17 (by simp; omega)) ?_)
      refine Sat.bind (Sat.of_eq (ctSetFc_T .bl_desc _ 17 (by simp; omega) _) ?_)
      simp only [tArr_tPut, tPut_tPut]
      have cw2 := cap 17 (by omega)
      rw [hGc, ite_t rfl] at cw2
      refine Sat.pure (fin _ _ _ (by simp [hCs]) (fun c hc => ?_) m1 m2)
      rw [bump_get _ 17 (by omega) 1 (by simp; omega), hGc]
      simp only [UInt16.toNat_one]
    · have b5 : ¬ cnt + 1 ≤ 10 := by rw [UInt16.le_iff_toNat_le, hs]; exact c5
      rw [ite_f b5]
      have hGc : ∀ c, G.count c = if c = 18 then 1 else 0 := fun c => by
        rw [← hG]; unfold groupTokens; rw [ite_f (by omega), ite_f (by omega), ite_f c5]
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        (repeat' split) <;> omega
      refine Sat.bind (Sat.of_eq (ctFc_T .bl_desc _ 18 (by simp; omega)) ?_)
      refine Sat.bind (Sat.of_eq (ctSetFc_T .bl_desc _ 18 (by simp; omega) _) ?_)
      simp only [tArr_tPut, tPut_tPut]
      have cw2 := cap 18 (by omega)
      rw [hGc, ite_t rfl] at cw2
      refine Sat.pure (fin _ _ _ (by simp [hCs]) (fun c hc => ?_) m1 m2)
      rw [bump_get _ 18 (by omega) 1 (by simp; omega), hGc]
      simp only [UInt16.toNat_one]

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

end

theorem i32_of (m : Nat) (h : m ≤ 1000) : (Int32.ofInt m).toInt = m := by
  rw [Int32.toInt_ofInt]; apply Int.bmod_eq_of_le <;> simp [Int32.size] <;> omega

/-- The tree array after `scan_tree`'s guard store `tree[max_code + 1].Len = 0xffff` (`m = max_code + 1`). -/
def guard (L : Array Ct) (m : Nat) : Array Ct := L.set! m { L[m]! with dl := 0xffff }

theorem guard_lt (L : Array Ct) (m n : Nat) (h : n < m) : (guard L m)[n]! = L[n]! := by
  unfold guard
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [show m ≠ n by omega]

theorem guard_m (L : Array Ct) (m : Nat) (h : m < L.size) : ((guard L m)[m]!).dl = 0xffff := by
  unfold guard
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [h]

theorem guard_size (L : Array Ct) (m : Nat) : (guard L m).size = L.size := by simp [guard]

theorem tPut_bl_self (t : DescSel) (ht : t ≠ .bl_desc) (s : DeflateState) (A : Array Ct) :
    tPut .bl_desc (tPut t s A) s.bl_tree = tPut t s A := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- What `scan_tree` leaves: the guard stored, `bl_tree[c].Freq` raised by the count of `c` in `treeTokens`. -/
def ScanPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (d : Array UInt8) (t : DescSel) (s : DeflateState) (m : Nat)
    (H' : Heap) : Prop :=
  ∃ C : Array Ct, H' = SH H i z b (tPut .bl_desc (tPut t s (guard (tArr t s) m)) C) d ∧ C.size = s.bl_tree.size ∧
    ∀ c, c < 19 → (C[c]!).fc.toNat = (s.bl_tree[c]!).fc.toNat + (treeTokens (lenOf (tArr t s)) m).count c

theorem scan_tail (t : DescSel) (ht : t ≠ .bl_desc) (s : DeflateState) (m : Nat) (mc : Int32)
    (hmc : mc.toInt + 1 = m) (hm1 : 1 ≤ m) (hm : m < (tArr t s).size) (hm1k : m ≤ 1000)
    (h15 : ∀ n, n < m → lenOf (tArr t s) n ≤ 15) (hbl : 19 ≤ s.bl_tree.size)
    (hcap : ∀ c, c < 19 → (s.bl_tree[c]!).fc.toNat + m < 65536)
    (nl : Int32) (hnl : nl.toInt = lenOf (tArr t s) 0) (mx mn : UInt16)
    (hmx : mx.toNat = if lenOf (tArr t s) 0 = 0 then 138 else 7)
    (hmn : mn.toNat = if lenOf (tArr t s) 0 = 0 then 3 else 4) :
    Sat (SH H i z b s d) (scanTail (some b) (.ref (tRef t b) 0) mc nl mx mn)
      (fun _ H' => ScanPost H i z b d t s m H') := by
  unfold scanTail
  have em : chkI32 (mc.toInt + 1) = pure (Int32.ofInt m) :=
    DeflateAlloc.chk_eq _ (by rw [i32_of m hm1k]; omega)
  rw [em, pure_bind_M, i32_of m hm1k]
  refine Sat.bind (Sat.of_eq (ctSetDl_T t s m hm _) ?_)
  simp only [blTreeP, pure_bind_M]
  generalize hL : tArr t s = L at hm h15 hnl hmx hmn
  have hA : guard L m = L.set! m { L[m]! with dl := 0xffff } := rfl
  rw [← hA]
  have hlen : ∀ n, n < m → lenOf (guard L m) n = lenOf L n := fun n h => by unfold lenOf; rw [guard_lt L m n h]
  have hgs := guard_size L m
  refine Sat.bind (Sat.mono (sat_cwhile (SInv (H := H) (i := i) (z := z) (b := b) (d := d) t s (guard L m) m)
    (fun x => m - x.1.toInt.toNat) (fun x H' => SInv (H := H) (i := i) (z := z) (b := b) (d := d) t s (guard L m) m x H'
      ∧ ¬ x.1 ≤ mc) ?_ ?_ (by simp [fuel]; omega)) ?_)
  · intro x H' hI
    refine Sat.pure ⟨fun hc => scan_step t ht s (guard L m) m mc hmc (by omega) hm1k (guard_m L m hm)
      (fun n h => by rw [hlen n h]; exact h15 n h) hbl hcap x H' hI (of_decide_eq_true hc), fun hc => ⟨hI, ?_⟩⟩
    exact fun h => by simp [h] at hc
  · refine ⟨s.bl_tree, 0, -1, lenOf L 0, by rw [tPut_bl_self t ht], rfl, rfl, by omega, rfl, ?_, fun h => ?_,
      Or.inl rfl, ?_, ?_, ?_, ?_, fun c hc => ?_⟩
    · dsimp only; rw [hnl]
    · exact h15 0 hm1
    · dsimp only; rw [hmx]; simp; split <;> omega
    · dsimp only; rw [hmx]; split <;> omega
    · dsimp only; rw [hmn]; split <;> omega
    · dsimp only; rw [hmn]; split <;> omega
    · dsimp only
      unfold treeTokens
      rw [hmx, hmn, hlen 0 hm1]
      simp
  · rintro x _ ⟨⟨C, n, p, nl', rfl, hCs, hn, hnm, -, -, -, -, -, -, -, -, hcount⟩, hx⟩
    have hmn' : n = m := by have := Int32.lt_iff_toInt_lt.mp (Int32.not_le.mp hx); omega
    subst hmn'
    refine Sat.pure ⟨C, by rw [hL], hCs, fun c hc => ?_⟩
    have := hcount c hc
    rw [Nat.sub_self] at this
    simp only [scanTokens, List.count_nil, Nat.add_zero] at this
    rw [this, treeTokens_congr _ _ _ hm1 hlen, hL]

/-- `scan_tree` on the literal/length or distance tree with `m = max_code + 1` codes of lengths at most 15. -/
theorem scan_tree_SH (t : DescSel) (ht : t ≠ .bl_desc) (s : DeflateState) (m : Nat) (mc : Int32)
    (hmc : mc.toInt + 1 = m) (hm1 : 1 ≤ m) (hm : m < (tArr t s).size) (hm1k : m ≤ 1000)
    (h15 : ∀ n, n < m → lenOf (tArr t s) n ≤ 15) (hbl : 19 ≤ s.bl_tree.size)
    (hcap : ∀ c, c < 19 → (s.bl_tree[c]!).fc.toNat + m < 65536) :
    Sat (SH H i z b s d) (scan_tree (some b) (.ref (tRef t b) 0) mc) (fun _ H' => ScanPost H i z b d t s m H') := by
  rw [scan_tree_eq]
  refine Sat.bind (Sat.of_eq (ctDl_T t s 0 (by omega)) ?_)
  have e : ((tArr t s)[0]!.dl.toUInt32.toInt32).toInt = lenOf (tArr t s) 0 := by
    have := (tArr t s)[0]!.dl.toNat_lt
    rw [DeflateAlloc.u32_toInt32_toInt _ (by simp only [UInt16.toNat_toUInt32]; omega), UInt16.toNat_toUInt32]; rfl
  have b0 : ((tArr t s)[0]!.dl.toUInt32.toInt32 == 0) = true ↔ lenOf (tArr t s) 0 = 0 := by
    rw [i32_eq_toInt, e]; simp
  dsimp only
  split
  · rename_i h
    exact scan_tail t ht s m mc hmc hm1 hm hm1k h15 hbl hcap _ e _ _ (by simp [b0.mp h]) (by simp [b0.mp h])
  · rename_i h
    have h' : lenOf (tArr t s) 0 ≠ 0 := fun h2 => h (b0.mpr h2)
    exact scan_tail t ht s m mc hmc hm1 hm hm1k h15 hbl hcap _ e _ _ (by simp [h']) (by simp [h'])

end

end ZlibNgF.Proof.TreesHeader
