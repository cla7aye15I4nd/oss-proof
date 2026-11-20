import ZlibNgF.Proof.«trees.c.sort»
import ZlibNgF.Proof.«trees.c.buildspec»

/-!
# `build_tree` cut into its phases (`ZlibNgF`)

`build_tree` (`trees.c:165-271`) is the leaf scan (`scanBody`), the forcing loop (`forceBody`), the store of
`desc->max_code`, the sort (`sortBlock`), the merge loop (`mergeBody`), `gen_bitlen` and `gen_codes`. `build_tree_eq`
states that the translation is that sequence.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesBuild
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesScan ZlibNgF.Proof.TreesForce ZlibNgF.Proof.TreesSort
open ZlibNg.Inftrees (aget aset)
open ZlibNgF.Proof.TreesBuildSpec (tElems tSize)
open ZlibNgF.Math.Huff (scanLeaves maxCode1 forced sortKeys)
open ZlibNgF.Math.TreesRadix (forced_props scan_inc)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- The condition of the merge loop. -/
def mergeCond : Int32 × Int32 × Int32 × Int32 × Int32 → M (Bool × (Int32 × Int32 × Int32 × Int32 × Int32)) :=
  fun ((merges, li, ihead, itail, node) : Int32 × Int32 × Int32 × Int32 × Int32) =>
    pure (merges > 0, (merges, li, ihead, itail, node))

/-- The body of the merge loop. -/
def mergeBody (tree : CtPtr) (sorted internals : DWPtr) (nleaves : Int32) :
    Int32 × Int32 × Int32 × Int32 × Int32 → M (Int32 × Int32 × Int32 × Int32 × Int32) :=
  fun ((merges, li, ihead, itail, node) : Int32 × Int32 × Int32 × Int32 × Int32) => do
    let (en, li, ihead) ← pq_take sorted li nleaves internals ihead itail
    let (em, li, ihead) ← pq_take sorted li nleaves internals ihead itail
    let n := pq_node en
    let m := pq_node em
    let f : UInt16 := (pq_freq en + pq_freq em).toUInt16
    ctSetFc tree node.toInt f
    ctSetDl tree m.toInt node.toUInt32.toUInt16
    ctSetDl tree n.toInt node.toUInt32.toUInt16
    dwSet internals itail.toInt (pq_pack f.toUInt32 node)
    let itail ← chkI32 (itail.toInt + 1)
    let node ← chkI32 (node.toInt + 1)
    pure (merges - 1, li, ihead, itail, node)

theorem M_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f) >>= g = m >>= fun a => f a >>= g := by
  funext h; simp only [bind_app]; cases m h <;> rfl

/-- What follows the sort. -/
def buildTail (st : StatePtr) (desc : DescSel) (tree : CtPtr) (elems nleaves max_code : Int32)
    (sorted internals : DWPtr) : M Unit := do
  let (_, _, _, _, nd) ← cwhile mergeCond (mergeBody tree sorted internals nleaves)
    (nleaves - 1, (0 : Int32), (0 : Int32), (0 : Int32), elems)
  gen_bitlen st desc sorted nleaves (← chkI32 (nd.toInt - 1))
  gen_codes tree max_code (← blCountP st)

theorem build_tree_eq (st : StatePtr) (desc : DescSel) :
    build_tree st desc = (do
      let tree ← descDynTree st desc
      let stree := (← descStat st desc).static_tree
      let elems := (← descStat st desc).elems
      let leaves ← pqLeavesP st
      let scratch ← pqScratchP st
      let (_, nl, mc, clo, chi) ← cwhile (scanCond elems) (scanBody tree leaves)
        ((0 : Int32), (0 : Int32), (-1 : Int32), Array.replicate 257 (0 : UInt16), Array.replicate 257 (0 : UInt16))
      let (nl, mc, _) ← cwhile forceCond (forceBody st tree stree leaves) (nl, mc, (0 : Int32))
      wrD st fun s => desc.set s { desc.get s with max_code := mc }
      let (sorted, internals) ← sortBlock leaves scratch nl clo chi
      buildTail st desc tree elems nl mc sorted internals) := by
  unfold build_tree
  refine congrArg (descDynTree st desc >>= ·) (funext fun tree => ?_)
  refine congrArg (descStat st desc >>= ·) (funext fun sd1 => ?_)
  refine congrArg (descStat st desc >>= ·) (funext fun sd2 => ?_)
  refine congrArg (pqLeavesP st >>= ·) (funext fun leaves => ?_)
  refine congrArg (pqScratchP st >>= ·) (funext fun scratch => ?_)
  refine congrArg (_ >>= ·) (funext fun x1 => ?_)
  obtain ⟨_, nl, mc, clo, chi⟩ := x1
  refine congrArg (_ >>= ·) (funext fun x2 => ?_)
  obtain ⟨nl2, mc2, nd2⟩ := x2
  refine congrArg (_ >>= ·) (funext fun u => ?_)
  simp only [sortBlock]
  by_cases h2 : (nl2 == 2) = true
  · simp only [h2, ↓reduceIte, M_bind_assoc]
    refine congrArg (_ >>= ·) (funext fun l0 => ?_)
    refine congrArg (_ >>= ·) (funext fun l1 => ?_)
    by_cases h3 : l0 > l1
    · simp only [h3, ↓reduceIte, M_bind_assoc]; rfl
    · simp only [h3, ↓reduceIte]; rfl
  · simp only [h2, Bool.false_eq_true, ↓reduceIte, M_bind_assoc]
    refine congrArg (_ >>= ·) (funext fun c1 => ?_)
    by_cases h3 : (c1.toUInt32.toInt32 == nl2) = true
    · simp only [h3, ↓reduceIte, M_bind_assoc]; rfl
    · simp only [h3, Bool.false_eq_true, ↓reduceIte, M_bind_assoc]; rfl

/-! ## The phases before the merge -/

theorem elems_tSD (t : DescSel) : ((tSD t).get.elems).toInt = tElems t := by cases t <;> rfl

theorem tSize_ge (t : DescSel) : tElems t ≤ tSize t ∧ 3 ≤ tElems t ∧ tElems t ≤ 286 := by
  cases t <;> decide

theorem set_q (t : DescSel) (X : DeflateState) (Lv1 : Array UInt32) (D : TreeDesc) :
    t.set (qPut false X Lv1) D = qPut false (t.set X D) Lv1 := by
  cases t <;> simp only [qPut, DescSel.set, Bool.false_eq_true, ↓reduceIte]

theorem pq_set (t : DescSel) (X : DeflateState) (D : TreeDesc) :
    (t.set X D).pq_leaves = X.pq_leaves ∧ (t.set X D).pq_scratch = X.pq_scratch := by cases t <;> exact ⟨rfl, rfl⟩

theorem get_tPut_opt (t : DescSel) (s : DeflateState) (A : Array Ct) (o sl : UInt32) :
    t.get (tPut t { s with opt_len := o, static_len := sl } A) = t.get s := by cases t <;> rfl

theorem norm_force (t : DescSel) (s : DeflateState) (A0 A : Array Ct) (Lv0 Lv : Array UInt32) (o sl : UInt32) :
    qPut false (tPut t { qPut false (tPut t s A0) Lv0 with opt_len := o, static_len := sl } A) Lv =
      qPut false (tPut t { s with opt_len := o, static_len := sl } A) Lv := by
  cases t <;> simp only [qPut, tPut, Bool.false_eq_true, ↓reduceIte]

theorem norm_sort (t : DescSel) (X : DeflateState) (Lv1 Lv Sc : Array UInt32) (D : TreeDesc) :
    { qPut false (t.set X D) Lv1 with pq_leaves := Lv, pq_scratch := Sc } =
      { t.set X D with pq_leaves := Lv, pq_scratch := Sc } := by cases t <;> rfl

theorem get_set_q (t : DescSel) (s : DeflateState) (A : Array Ct) (Lv : Array UInt32) (o sl : UInt32) :
    t.get (qPut false (tPut t { s with opt_len := o, static_len := sl } A) Lv) = t.get s := by
  cases t <;> rfl

theorem norm_q (X : DeflateState) (Lv1 Lv Sc : Array UInt32) :
    { qPut false X Lv1 with pq_leaves := Lv, pq_scratch := Sc } = { X with pq_leaves := Lv, pq_scratch := Sc } := by
  simp only [qPut, Bool.false_eq_true, ↓reduceIte]

theorem scratch_set (t : DescSel) (s : DeflateState) (A : Array Ct) (o sl : UInt32) (D : TreeDesc) :
    (t.set (tPut t { s with opt_len := o, static_len := sl } A) D).pq_scratch = s.pq_scratch := by cases t <;> rfl

theorem forced_len (L : List (Nat × Nat)) (m : Nat) :
    (forced L m).1.length = max L.length 2 ∧ (3 ≤ (forced L m).1.length → (forced L m).1 = L) := by
  match L with
  | [] => simp [forced]
  | [_] => simp [forced]
  | _ :: _ :: _ => simp [forced]

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- **`build_tree` up to the merge loop.** The leaf scan, the forcing loop, the store of `desc->max_code` and the
sort run without fault; the merge loop and what follows (`buildTail`) start from a state whose tree has the forced
frequencies, whose `sorted` queue holds the packed `sortKeys` of the forced leaves, with `opt_len` / `static_len`
lowered per forced code. -/
theorem prefix_SH (t : DescSel) (s : DeflateState) (hdyn : (t.get s).dyn_tree = .val (.ref (tRef t b) 0))
    (hstat : (t.get s).stat_desc = .val (tSD t)) (hF : (tArr t s).size = tSize t) (hql : s.pq_leaves.size = 287)
    (hqs : s.pq_scratch.size = 287) (Q : Unit → Heap → Prop)
    (hk : ∀ (A : Array Ct) (Lv Sc : Array UInt32) (qS : Bool) (nl mc : Int32),
      A.size = (tArr t s).size →
      (∀ k, k < (tArr t s).size → (A[k]!).fc = (setOnes (tArr t s)
        ((forced (scanLeaves (frq (tArr t s)) (tElems t)) (maxCode1 (frq (tArr t s)) (tElems t))).1.drop
          (scanLeaves (frq (tArr t s)) (tElems t)).length) k).fc) →
      (∀ k, k < (tArr t s).size → (A[k]!).dl = if k < tElems t ∧ ((tArr t s)[k]!).fc = 0 then 0 else ((tArr t s)[k]!).dl) →
      nl.toInt = (forced (scanLeaves (frq (tArr t s)) (tElems t)) (maxCode1 (frq (tArr t s)) (tElems t))).1.length →
      mc.toInt + 1 = (forced (scanLeaves (frq (tArr t s)) (tElems t)) (maxCode1 (frq (tArr t s)) (tElems t))).2 →
      Lv.size = 287 → Sc.size = 287 →
      (∀ p, p < (forced (scanLeaves (frq (tArr t s)) (tElems t)) (maxCode1 (frq (tArr t s)) (tElems t))).1.length →
        (qArr qS { t.set (tPut t { s with
            opt_len := optSub s.opt_len ((forced (scanLeaves (frq (tArr t s)) (tElems t))
              (maxCode1 (frq (tArr t s)) (tElems t))).1.drop (scanLeaves (frq (tArr t s)) (tElems t)).length)
            static_len := statSub t s.static_len ((forced (scanLeaves (frq (tArr t s)) (tElems t))
              (maxCode1 (frq (tArr t s)) (tElems t))).1.drop (scanLeaves (frq (tArr t s)) (tElems t)).length) } A)
            { t.get s with max_code := mc } with pq_leaves := Lv, pq_scratch := Sc })[p]! =
          pk (sortKeys (forced (scanLeaves (frq (tArr t s)) (tElems t))
            (maxCode1 (frq (tArr t s)) (tElems t))).1)[p]!) →
      Sat (SH H i z b { t.set (tPut t { s with
            opt_len := optSub s.opt_len ((forced (scanLeaves (frq (tArr t s)) (tElems t))
              (maxCode1 (frq (tArr t s)) (tElems t))).1.drop (scanLeaves (frq (tArr t s)) (tElems t)).length)
            static_len := statSub t s.static_len ((forced (scanLeaves (frq (tArr t s)) (tElems t))
              (maxCode1 (frq (tArr t s)) (tElems t))).1.drop (scanLeaves (frq (tArr t s)) (tElems t)).length) } A)
            { t.get s with max_code := mc } with pq_leaves := Lv, pq_scratch := Sc } d)
        (buildTail (some b) t (.ref (tRef t b) 0) (tSD t).get.elems nl mc (.ref (qRef qS b) 0)
          (.ref (qRef (!qS) b) 0)) Q) :
    Sat (SH H i z b s d) (build_tree (some b) t) Q := by
  obtain ⟨hEs, hE3, hE286⟩ := tSize_ge t
  rw [build_tree_eq]
  refine Sat.bind (Sat.of_eq (descDynTree_SH t s hdyn) ?_)
  refine Sat.bind (Sat.of_eq (descStat_SH t s hstat) ?_)
  refine Sat.bind (Sat.of_eq (descStat_SH t s hstat) ?_)
  refine Sat.bind (Sat.of_eq (pqLeavesP_eq s) ?_)
  refine Sat.bind (Sat.of_eq (pqScratchP_eq s) ?_)
  refine Sat.bind (Sat.mono (scan_SH t s _ (tElems t) (elems_tSD t) hE286 (by omega) hql) fun x H1 h1 => ?_)
  obtain ⟨A0, Lv0, rfl, hx1, hA0s, hA0fc, hA0dl, hLv0s, hnl0, hLv0, hmc0, hclos, hchis, hclo, hchi⟩ := h1
  obtain ⟨n0, nl0, mc0, clo, chi⟩ := x
  dsimp only at hx1 hnl0 hLv0 hmc0 hclos hchis hclo hchi ⊢
  have hm0 := ZlibNgF.Math.Huff.maxCode1_le (frq (tArr t s)) (tElems t)
  have hL0 := scan_len (frq (tArr t s)) (tElems t)
  refine Sat.bind (Sat.mono (force_SH t (qPut false (tPut t s A0) Lv0) (scanLeaves (frq (tArr t s)) (tElems t))
    (maxCode1 (frq (tArr t s)) (tElems t)) nl0 mc0 0 (by simp; omega) (by simp [qPut]; exact hLv0s)
    (by intro j hj; have := hLv0 j hj; simpa [qPut] using this) (by omega) (by omega) hnl0 hmc0) fun x H2 h2 => ?_)
  obtain ⟨A, Lv1, rfl, hnl1, hmc1, hLv1s, hLv1, hAs, hA⟩ := h2
  obtain ⟨nl, mc, nd⟩ := x
  dsimp only at hnl1 hmc1 ⊢
  simp only [qt_opt_get, qt_stat_get, norm_force, tArr_qPut, tArr_tPut] at hAs hA ⊢
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  rw [get_set_q, set_q]
  obtain ⟨pd, pb, p2⟩ := forced_props (frq (tArr t s)) (tElems t)
  obtain ⟨fl1, fl2⟩ := forced_len (scanLeaves (frq (tArr t s)) (tElems t)) (maxCode1 (frq (tArr t s)) (tElems t))
  refine Sat.bind (Sat.mono (sort_SH _ _ nl clo chi (by simp [qPut]; exact hLv1s)
    (by simp only [qPut, Bool.false_eq_true, ↓reduceIte, scratch_set]; exact hqs)
    (fun j hj => by have := hLv1 j hj; simpa [qPut] using this) hnl1 p2 (by omega)
    (fun e he => by
      have ⟨h1, h2⟩ := pb e he
      have : frq (tArr t s) e.2 < 65536 := by simp only [frq]; exact UInt16.toNat_lt _
      refine ⟨by omega, by omega⟩) pd
    (fun h3 => by
      have e3 := fl2 h3
      rw [e3]
      refine ⟨scan_inc _ _, hclos, hchis, hclo, hchi⟩)) fun r H3 h3 => ?_)
  obtain ⟨qS, Lv, Sc, rfl, rfl, hLs, hSs, hsorted⟩ := h3
  rw [norm_q] at hsorted ⊢
  refine hk A Lv Sc qS nl mc (by rw [hAs, hA0s]) (fun k hk => ?_) (fun k hk => ?_) hnl1 hmc1 hLs hSs hsorted
  · rw [hA k (by omega)]; unfold setOnes; split <;> simp [hA0fc k hk]
  · rw [hA k (by omega), ← hA0dl k hk]; unfold setOnes; split <;> rfl

end

end ZlibNgF.Proof.TreesBuild
