import ZlibNgF.Proof.«trees.c.scan»

/-!
# The forced codes of `build_tree` (`ZlibNgF`)

The second loop of `build_tree` (`while (nleaves < 2)`) on `SH` heaps computes the model's `forced`: it appends
`pq_pack(1, node)` to `pq_leaves` with `node = (max_code < 2 ? ++max_code : 0)` until there are two leaves, sets
`tree[node].Freq = 1`, and lowers `opt_len` by one and `static_len` by the static length of `node` per forced
code.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesForce
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesScan
open ZlibNgF.Math.Huff (forced forceNode forceNext)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- The static length of code `k` of the static tree of descriptor `t` (none for the bit-length tree). -/
def sdl (t : DescSel) (k : Nat) : UInt32 :=
  match t with
  | .l_desc => (static_ltree[k]!).dl.toUInt32
  | .d_desc => (static_dtree[k]!).dl.toUInt32
  | .bl_desc => 0

/-- `opt_len -= 1; static_len -= stree[node].Len` for the forced codes `ex`. -/
def optSub (o : UInt32) (ex : List (Nat × Nat)) : UInt32 := o - ex.length.toUInt32
def statSub (t : DescSel) (sl : UInt32) (ex : List (Nat × Nat)) : UInt32 := sl - (ex.map fun e => sdl t e.2).sum

/-- The tree `F` with `Freq = 1` at the forced codes `ex`. -/
def setOnes (F : Array Ct) (ex : List (Nat × Nat)) (k : Nat) : Ct :=
  if k ∈ ex.map (·.2) then { F[k]! with fc := 1 } else F[k]!

theorem forced_step (ls : List (Nat × Nat)) (m : Nat) (h : ls.length < 2) :
    forced (ls ++ [(1, forceNode m)]) (forceNext m) = forced ls m := by
  match ls, h with
  | [], _ => rfl
  | [_], _ => rfl

theorem forced_done (ls : List (Nat × Nat)) (m : Nat) (h : 2 ≤ ls.length) : forced ls m = (ls, m) := by
  match ls, h with
  | _ :: _ :: _, _ => rfl

theorem forceNode_le (m : Nat) : forceNode m ≤ 2 := by unfold forceNode; split <;> omega

/-- The body of the forcing loop. -/
def forceBody (st : StatePtr) (tree stree : CtPtr) (leaves : DWPtr) : Int32 × Int32 × Int32 → M (Int32 × Int32 × Int32) :=
  fun ((nl, mc, _) : Int32 × Int32 × Int32) => do
    let (mc, nd) := if mc < 2 then (mc + 1, mc + 1) else (mc, (0 : Int32))
    dwSet leaves nl.toInt (pq_pack 1 nd)
    let nl := nl + 1
    ctSetFc tree nd.toInt 1
    wrD st fun s => { s with opt_len := s.opt_len - 1 }
    match stree with
    | .null => pure ()
    | _ =>
      let l ← ctDl stree nd.toInt
      wrD st fun s => { s with static_len := s.static_len - l.toUInt32 }
    pure (nl, mc, nd)

/-- The condition of the forcing loop. -/
def forceCond : Int32 × Int32 × Int32 → M (Bool × (Int32 × Int32 × Int32)) :=
  fun ((nl, mc, nd) : Int32 × Int32 × Int32) => pure (nl < 2, (nl, mc, nd))

theorem static_dl (t : DescSel) (k : Nat) (hk : k ≤ 2) (H : Heap) (ht : t ≠ .bl_desc) :
    ctDl (StaticDescPtr.get (tSD t)).static_tree (k : Int) H =
      .ok ((sdl t k).toUInt16, H) := by
  cases t
  · have e1 : Ptr.add (Ptr.ref CtRef.static_ltree 0) (k : Int) H = .ok (Ptr.ref CtRef.static_ltree k, H) := by
      simp only [Ptr.add, Space.get, Heap.getCts]
      rw [ite_t (by rw [ZlibNgF.Proof.TreesEmitP.sl_size]; omega)]
      congr 3; omega
    have hk' : k < static_ltree.size := by rw [ZlibNgF.Proof.TreesEmitP.sl_size]; omega
    simp [ctDl, ctGet, Ptr.index, bind_app, tSD, StaticDescPtr.get, e1, Ptr.load, Space.get, Heap.getCts, hk', sdl]
  · have e1 : Ptr.add (Ptr.ref CtRef.static_dtree 0) (k : Int) H = .ok (Ptr.ref CtRef.static_dtree k, H) := by
      simp only [Ptr.add, Space.get, Heap.getCts]
      rw [ite_t (by rw [ZlibNgF.Proof.TreesEmitP.sd_size]; omega)]
      congr 3; omega
    have hk' : k < static_dtree.size := by rw [ZlibNgF.Proof.TreesEmitP.sd_size]; omega
    simp [ctDl, ctGet, Ptr.index, bind_app, tSD, StaticDescPtr.get, e1, Ptr.load, Space.get, Heap.getCts, hk', sdl]
  · exact absurd rfl ht

theorem u32_sub_add (x a b : UInt32) : x - (a + b) = x - a - b := by
  apply UInt32.toNat_inj.mp; have := a.toNat_lt; have := b.toNat_lt; have := x.toNat_lt
  simp only [UInt32.toNat_sub, UInt32.toNat_add]; omega

theorem optSub_snoc (o : UInt32) (ex : List (Nat × Nat)) (e : Nat × Nat) :
    optSub o (ex ++ [e]) = optSub o ex - 1 := by
  simp only [optSub, List.length_append, List.length_singleton]
  rw [show (ex.length + 1).toUInt32 = ex.length.toUInt32 + 1 by simp, u32_sub_add]

theorem statSub_snoc (t : DescSel) (sl : UInt32) (ex : List (Nat × Nat)) (e : Nat × Nat) :
    statSub t sl (ex ++ [e]) = statSub t sl ex - sdl t e.2 := by
  simp only [statSub, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [show sdl t e.2 + (0 : UInt32) = sdl t e.2 by simp, u32_sub_add]

/-- The state with `opt_len` / `static_len` replaced, through the tree and queue updates. -/
theorem qt_opt (t : DescSel) (q : Bool) (s : DeflateState) (A : Array Ct) (L : Array UInt32) (v : UInt32) :
    { qPut q (tPut t s A) L with opt_len := v } = qPut q (tPut t { s with opt_len := v } A) L := by
  cases t <;> cases q <;> rfl
theorem qt_stat (t : DescSel) (q : Bool) (s : DeflateState) (A : Array Ct) (L : Array UInt32) (v : UInt32) :
    { qPut q (tPut t s A) L with static_len := v } = qPut q (tPut t { s with static_len := v } A) L := by
  cases t <;> cases q <;> rfl
@[simp] theorem qt_opt_get (t : DescSel) (q : Bool) (s : DeflateState) (A : Array Ct) (L : Array UInt32) :
    (qPut q (tPut t s A) L).opt_len = s.opt_len := by cases t <;> cases q <;> rfl
@[simp] theorem qt_stat_get (t : DescSel) (q : Bool) (s : DeflateState) (A : Array Ct) (L : Array UInt32) :
    (qPut q (tPut t s A) L).static_len = s.static_len := by cases t <;> cases q <;> rfl
@[simp] theorem tArr_upd_opt (t : DescSel) (s : DeflateState) (v : UInt32) :
    tArr t { s with opt_len := v } = tArr t s := by cases t <;> rfl
@[simp] theorem tArr_upd_stat (t : DescSel) (s : DeflateState) (v : UInt32) :
    tArr t { s with static_len := v } = tArr t s := by cases t <;> rfl

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- The forcing loop of `build_tree` from the leaves `L0` (`nleaves = |L0|`, `max_code + 1 = m0`) in `pq_leaves`:
it ends with the leaves and `max_code + 1` of `forced L0 m0`, `Freq = 1` at the forced codes `ex`, `opt_len` and
`static_len` lowered for each. -/
theorem force_SH (t : DescSel) (s : DeflateState) (L0 : List (Nat × Nat)) (m0 : Nat) (nl0 mc0 nd0 : Int32)
    (hF : 3 ≤ (tArr t s).size) (hq : s.pq_leaves.size = 287)
    (hLv : ∀ j, j < L0.length → s.pq_leaves[j]! = pk L0[j]!) (hL0 : L0.length ≤ 286) (hm0 : m0 ≤ 286)
    (hnl : nl0.toInt = L0.length) (hmc : mc0.toInt + 1 = m0) :
    Sat (SH H i z b s d)
      (cwhile forceCond (forceBody (some b) (.ref (tRef t b) 0) (StaticDescPtr.get (tSD t)).static_tree
        (.ref (qRef false b) 0)) (nl0, mc0, nd0))
      (fun x H' => ∃ A Lv, H' = SH H i z b (qPut false (tPut t { s with
          opt_len := optSub s.opt_len ((forced L0 m0).1.drop L0.length)
          static_len := statSub t s.static_len ((forced L0 m0).1.drop L0.length) } A) Lv) d ∧
        x.1.toInt = (forced L0 m0).1.length ∧ x.2.1.toInt + 1 = (forced L0 m0).2 ∧ Lv.size = 287 ∧
        (∀ j, j < (forced L0 m0).1.length → Lv[j]! = pk (forced L0 m0).1[j]!) ∧ A.size = (tArr t s).size ∧
        ∀ k, k < (tArr t s).size → A[k]! = setOnes (tArr t s) ((forced L0 m0).1.drop L0.length) k) := by
  refine sat_cwhile (I := fun (x : Int32 × Int32 × Int32) H' => ∃ ex A Lv,
      forced (L0 ++ ex) (x.2.1.toInt + 1).toNat = forced L0 m0 ∧ ex.length ≤ 2 ∧
      H' = SH H i z b (qPut false (tPut t { s with
          opt_len := optSub s.opt_len ex
          static_len := statSub t s.static_len ex } A) Lv) d ∧
      x.1.toInt = (L0 ++ ex).length ∧ 0 ≤ x.2.1.toInt + 1 ∧ x.2.1.toInt + 1 ≤ 287 ∧ Lv.size = 287 ∧
      (∀ j, j < (L0 ++ ex).length → Lv[j]! = pk (L0 ++ ex)[j]!) ∧ A.size = (tArr t s).size ∧
      ∀ k, k < (tArr t s).size → A[k]! = setOnes (tArr t s) ex k)
    (μ := fun x => 2 - x.1.toInt.toNat) _ ?_
    ⟨[], tArr t s, s.pq_leaves, by rw [hmc]; simp, by simp,
      by simp [optSub, statSub, tPut_self]; rfl, by simp [hnl], by dsimp only; omega, by dsimp only; omega, hq,
      by simpa using hLv, rfl, fun k _ => by simp [setOnes]⟩ (by simp [fuel]; omega)
  rintro ⟨nl, mc, nd⟩ _ ⟨ex, A, Lv, hR, hex, rfl, hnl1, hm1, hm2, hLv1, hLvj, hA, hAk⟩
  dsimp only at hR hnl1 hm1 hm2 hLvj ⊢
  simp only [forceCond]
  refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · simp only [decide_eq_true_eq] at hc
    have hlt : nl.toInt < 2 := by have := Int32.lt_iff_toInt_lt.mp hc; simpa using this
    have hlen : (L0 ++ ex).length < 2 := by omega
    have hlen' : L0.length + ex.length < 2 := by simpa using hlen
    generalize hm : (mc.toInt + 1).toNat = m at hR
    have hmn : mc.toInt + 1 = (m : Int) := by omega
    -- the node chosen by this iteration
    obtain ⟨mc', nd', hsel, hnd, hmc'⟩ : ∃ mc' nd' : Int32,
        (if mc < 2 then (mc + 1, mc + 1) else (mc, (0 : Int32))) = (mc', nd') ∧
        nd'.toInt = forceNode m ∧ mc'.toInt + 1 = forceNext m := by
      by_cases h2 : mc < 2
      · have h2' : mc.toInt < 2 := by have := Int32.lt_iff_toInt_lt.mp h2; simpa using this
        have e := i32_add1 mc (by omega) (by omega)
        refine ⟨mc + 1, mc + 1, by simp [h2], ?_, ?_⟩
        · rw [e]; have h3 : m < 3 := by omega
          simp only [forceNode, h3, ↓reduceIte]; omega
        · rw [e]; have h3 : m < 3 := by omega
          simp only [forceNext, h3, ↓reduceIte]; omega
      · have h2' : ¬ mc.toInt < 2 := fun h => h2 (Int32.lt_iff_toInt_lt.mpr (by simpa using h))
        refine ⟨mc, 0, by simp [h2], ?_, ?_⟩
        · have h3 : ¬ m < 3 := by omega
          simp only [forceNode, h3, ↓reduceIte]; rfl
        · have h3 : ¬ m < 3 := by omega
          simp only [forceNext, h3, ↓reduceIte]; omega
    simp only [forceBody, hsel]
    have hn2 := forceNode_le m
    have hnd0 : 0 ≤ nd'.toInt := by omega
    generalize hN : forceNode m = N at hnd hn2
    have hndN : nd'.toInt = (N : Int) := hnd
    -- `pq_leaves[nleaves] = pq_pack(1, node)`
    rw [hnl1]
    have e2 := dwSet_Q (H := H) (i := i) (z := z) (b := b) (d := d) false
      (qPut false (tPut t { s with opt_len := optSub s.opt_len ex, static_len := statSub t s.static_len ex } A) Lv)
      (L0 ++ ex).length (by simp [hLv1]; omega) (pq_pack 1 nd')
    refine Sat.bind (Sat.of_eq e2 ?_)
    simp only [qArr_qPut, qPut_qPut]
    -- `tree[node].Freq = 1`
    have e3 := ctSetFc_T (H := H) (i := i) (z := z) (b := b) (d := d) t
      (qPut false (tPut t { s with opt_len := optSub s.opt_len ex, static_len := statSub t s.static_len ex } A)
        (Lv.set! (L0 ++ ex).length (pq_pack 1 nd'))) N (by simp; omega) 1
    rw [← hndN] at e3
    refine Sat.bind (Sat.of_eq e3 ?_)
    simp only [tArr_qPut, tArr_tPut, tPut_qPut]
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    simp only [qt_opt_get, qt_opt]
    have hpk : pq_pack 1 nd' = pk (1, N) := by
      have := pq_pack_pk 1 nd' hnd0 (by omega); rw [hndN] at this; exact this
    have post : ∀ (v : UInt32), v = sdl t N →
        Sat (SH H i z b (qPut false (tPut t { s with
            opt_len := optSub s.opt_len ex - 1
            static_len := statSub t s.static_len ex - v } (A.set! N { fc := 1, dl := (A[N]!).dl }))
            (Lv.set! (L0 ++ ex).length (pq_pack 1 nd'))) d)
          (pure (nl + 1, mc', nd'))
          (fun s2 H2 => (∃ ex A Lv, forced (L0 ++ ex) (s2.2.1.toInt + 1).toNat = forced L0 m0 ∧ ex.length ≤ 2 ∧
            H2 = SH H i z b (qPut false (tPut t { s with
              opt_len := optSub s.opt_len ex
              static_len := statSub t s.static_len ex } A) Lv) d ∧
            s2.1.toInt = (L0 ++ ex).length ∧ 0 ≤ s2.2.1.toInt + 1 ∧ s2.2.1.toInt + 1 ≤ 287 ∧ Lv.size = 287 ∧
            (∀ j, j < (L0 ++ ex).length → Lv[j]! = pk (L0 ++ ex)[j]!) ∧ A.size = (tArr t s).size ∧
            ∀ k, k < (tArr t s).size → A[k]! = setOnes (tArr t s) ex k) ∧
            2 - s2.1.toInt.toNat < 2 - (((L0 ++ ex).length : Nat) : Int).toNat) := by
      intro v hv
      have hs1 := i32_add1 nl (by omega) (by omega)
      refine Sat.pure ⟨⟨ex ++ [(1, N)], A.set! N { fc := 1, dl := (A[N]!).dl }, _, ?_, by simp; omega,
        by rw [optSub_snoc, statSub_snoc, hv], ?_⟩, ?_⟩
      · dsimp only
        rw [← List.append_assoc, show (mc'.toInt + 1).toNat = forceNext m by omega, ← hN,
          forced_step _ _ hlen, hR]
      · dsimp only
        refine ⟨by rw [hs1, hnl1]; simp; omega, by unfold forceNext at hmc'; split at hmc' <;> omega,
          by unfold forceNext at hmc'; split at hmc' <;> omega, by simp [hLv1], fun j hj => ?_,
          by simp [hA], fun k hk => ?_⟩
        · rw [← List.append_assoc] at hj ⊢
          have hjl : (L0 ++ ex).length = L0.length + ex.length := by simp
          simp only [List.length_append, List.length_singleton] at hj
          by_cases e : j = (L0 ++ ex).length
          · rw [e, set!_get_eq _ _ _ (by omega), getElem!_append_eq, hpk]
          · rw [set!_get_ne _ _ _ _ e, getElem!_append_lt (by omega)]; exact hLvj j (by omega)
        · by_cases e : k = N
          · rw [e, set!_get_eq _ _ _ (by omega)]
            rw [e] at hk
            rw [hAk N hk]
            have hm : N ∈ (ex ++ [(1, N)]).map (fun e : Nat × Nat => e.2) := by simp
            unfold setOnes
            simp only [hm, ↓reduceIte]
            split <;> rfl
          · rw [set!_get_ne _ _ _ _ e, hAk k hk]
            have hm : (k ∈ (ex ++ [(1, N)]).map (fun e : Nat × Nat => e.2)) ↔ k ∈ ex.map (fun e : Nat × Nat => e.2) := by
              simp [e]
            unfold setOnes
            simp only [hm]
      · dsimp only; omega
    cases t
    · rw [hndN]
      refine Sat.bind (Sat.of_eq (static_dl .l_desc N hn2 _ (by decide)) ?_)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      simp only [qt_stat_get, qt_stat]
      rw [show (sdl DescSel.l_desc N).toUInt16.toUInt32 = sdl DescSel.l_desc N by simp [sdl]]
      exact post _ rfl
    · rw [hndN]
      refine Sat.bind (Sat.of_eq (static_dl .d_desc N hn2 _ (by decide)) ?_)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      simp only [qt_stat_get, qt_stat]
      rw [show (sdl DescSel.d_desc N).toUInt16.toUInt32 = sdl DescSel.d_desc N by simp [sdl]]
      exact post _ rfl
    · simp only [tSD, StaticDescPtr.get]
      have := post 0 rfl
      rw [UInt32.sub_zero] at this
      exact this
  · simp only [decide_eq_false_iff_not] at hc
    have hge : 2 ≤ nl.toInt := Int.not_lt.mp fun hh => hc (Int32.lt_iff_toInt_lt.mpr (by simpa using hh))
    have hdone := forced_done (L0 ++ ex) (mc.toInt + 1).toNat (by omega)
    rw [hdone] at hR
    have h1 : (forced L0 m0).1 = L0 ++ ex := by rw [← hR]
    have h2 : (forced L0 m0).2 = (mc.toInt + 1).toNat := by rw [← hR]
    have hdrop : (forced L0 m0).1.drop L0.length = ex := by rw [h1]; simp
    dsimp only
    refine ⟨A, Lv, by rw [hdrop], ?_, ?_, hLv1, ?_, hA, ?_⟩
    · rw [h1]; exact hnl1
    · rw [h2]; omega
    · rw [h1]; exact hLvj
    · rw [hdrop]; exact hAk

end

end ZlibNgF.Proof.TreesForce
