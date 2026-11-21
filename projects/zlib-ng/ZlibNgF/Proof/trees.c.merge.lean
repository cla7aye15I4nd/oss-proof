import ZlibNgF.Proof.«trees.c.build»
import ZlibNgF.Math.TreesLabeled

/-!
# The merge loop of `build_tree` (`ZlibNgF`)

The loop `for (merges = nleaves - 1; merges > 0; merges--)` of `build_tree` (`trees.c:236-254`) on `SH` heaps runs
the numbered model `miter` of `Math/TreesLabeled.lean`: `pq_take` is `pqTakeL` (`take_SH`), the FIFO
`internals[ihead .. itail)` holds the packed (frequency, node) of the model FIFO, the leaf cursor `li` points at
the model's remaining leaves, and every (child, parent) edge of a created node is stored as `tree[child].Dad`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesMerge
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesScan ZlibNgF.Proof.TreesSort ZlibNgF.Proof.TreesBuild
open ZlibNgF.Math.TreesLabeled
open ZlibNgF.Math.Huff (keyLt)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f u32_toInt32_toInt)

/-! ## Packed entries -/

theorem pk_node (e : Nat × Nat) (h1 : e.1 < 65536) (h2 : e.2 < 1024) : (pq_node (pk e)).toInt = e.2 := by
  have hk := pk_toNat e (by omega) h2
  have ha : (pk e &&& ((1 <<< PQ_NODE_BITS) - 1)).toNat = e.2 := by
    have : ((1 : UInt32) <<< PQ_NODE_BITS) - 1 = 1023 := by decide
    rw [this, UInt32.toNat_and, hk]
    have e3 : (1023 : UInt32).toNat = 2 ^ 10 - 1 := rfl
    rw [e3, Nat.and_two_pow_sub_one_eq_mod]; omega
  simp only [pq_node]
  rw [u32_toInt32_toInt _ (by omega), ha]

theorem pk_freq (e : Nat × Nat) (h1 : e.1 < 65536) (h2 : e.2 < 1024) : (pq_freq (pk e)).toNat = e.1 := by
  have hk := pk_toNat e (by omega) h2
  simp only [pq_freq, UInt32.toNat_shiftRight, hk]
  have : (PQ_NODE_BITS).toNat % 32 = 10 := rfl
  rw [this, Nat.shiftRight_eq_div_pow]; omega

theorem qt_q (t : DescSel) (q : Bool) (X : DeflateState) (I I' : Array UInt32) (A : Array Ct) :
    qPut q (tPut t (qPut q X I) A) I' = tPut t (qPut q X I') A := by cases t <;> cases q <;> rfl

/-! ## The queues -/

/-- The leaf queue `S` holds the remaining leaves `ls` at `[N - |ls|, N)`, the FIFO `I` holds `is` at
`[ih, it)`. -/
structure QR (S I : Array UInt32) (N : Nat) (ls : List (Nat × Nat)) (is : List QL) (ih it : Nat) : Prop where
  lsl : ls.length ≤ N
  lsv : ∀ p, p < ls.length → S[N - ls.length + p]! = pk ls[p]!
  ihl : ih + is.length = it
  isv : ∀ p, p < is.length → I[ih + p]! = pk (is[p]!.freq, is[p]!.node)
  lb : ∀ e ∈ ls, e.1 < 65536 ∧ e.2 < 1024
  ib : ∀ q ∈ is, q.freq < 65536 ∧ q.node < 1024

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

theorem i32_lt (x y : Int32) : x < y ↔ x.toInt < y.toInt := Int32.lt_iff_toInt_lt

/-- **`pq_take` is `pqTakeL`.** -/
theorem take_SH (Y : DeflateState) (qS : Bool) (N : Nat) (ls : List (Nat × Nat)) (is : List QL)
    (li nl ih it : Int32) (IH IT : Nat) (hS : (qArr qS Y).size = 287) (hI : (qArr (!qS) Y).size = 287)
    (hN : N ≤ 286) (hnl : nl.toInt = N) (hli : li.toInt = N - ls.length) (hih : ih.toInt = IH)
    (hit : it.toInt = IT) (hIT : IT ≤ 286)
    (R : QR (qArr qS Y) (qArr (!qS) Y) N ls is IH IT) (ne : ls ≠ [] ∨ is ≠ []) :
    Sat (SH H i z b Y d) (pq_take (.ref (qRef qS b) 0) li nl (.ref (qRef (!qS) b) 0) ih it)
      (fun r H' => H' = SH H i z b Y d ∧
        r.1 = pk ((pqTakeL ls is).1.freq, (pqTakeL ls is).1.node) ∧
        r.2.1.toInt = N - (pqTakeL ls is).2.1.length ∧ ∃ IH' : Nat, r.2.2.toInt = IH' ∧
        QR (qArr qS Y) (qArr (!qS) Y) N (pqTakeL ls is).2.1 (pqTakeL ls is).2.2 IH' IT) := by
  have hlsl := R.lsl
  have hihl := R.ihl
  -- reading the head of each queue
  have rdS : ∀ (l : Nat × Nat) (ls' : List (Nat × Nat)), ls = l :: ls' →
      dwGet (.ref (qRef qS b) 0) li.toInt (SH H i z b Y d) = .ok (pk l, SH H i z b Y d) := by
    intro l ls' e
    have h0 := R.lsv 0 (by simp [e])
    have hk : li.toInt = ((N - ls.length + 0 : Nat) : Int) := by rw [hli]; omega
    rw [hk, dwGet_Q qS Y _ (by rw [hS]; omega), h0]; simp [e]
  have rdI : ∀ (q : QL) (is' : List QL), is = q :: is' →
      dwGet (.ref (qRef (!qS) b) 0) ih.toInt (SH H i z b Y d) = .ok (pk (q.freq, q.node), SH H i z b Y d) := by
    intro q is' e
    have h0 := R.isv 0 (by simp [e])
    have hl : is.length = is'.length + 1 := by simp [e]
    have hk : ih.toInt = ((IH + 0 : Nat) : Int) := by omega
    rw [hk, dwGet_Q (!qS) Y _ (by rw [hI]; omega), h0]; simp [e]
  match ls, is, ne with
  | l :: ls', [], _ =>
    simp only [List.length_cons, List.length_nil] at hli hlsl hihl
    have c1 : li < nl := (i32_lt _ _).mpr (by omega)
    have c2 : (ih == it) = true := (i32_beq_iff ih _ it hit).mpr (by omega)
    simp only [pq_take, c1, c2, ↓reduceIte]
    refine Sat.bind (Sat.pure ?_)
    simp only [↓reduceIte]
    refine Sat.bind (Sat.of_eq (rdS l ls' rfl) (Sat.pure ⟨rfl, rfl, ?_, IH, hih, ?_⟩))
    · simp only [pqTakeL]
      rw [i32_add1 _ (by omega) (by omega)]; omega
    · simp only [pqTakeL]
      refine ⟨by omega, fun p hp => ?_, by simp; omega, fun p hp => by simp at hp,
        fun e he => R.lb e (by simp [he]), fun q hq => by simp at hq⟩
      have := R.lsv (p + 1) (by simp; omega)
      simp only [List.length_cons, List.getElem!_cons_succ] at this
      rw [← this]; congr 1; omega
  | l :: ls', q :: is', _ =>
    simp only [List.length_cons] at hli hlsl hihl
    have c1 : li < nl := (i32_lt _ _).mpr (by omega)
    have c2 : (ih == it) = false := by
      cases h : (ih == it)
      · rfl
      · have := (i32_beq_iff ih _ it hit).mp h; omega
    have bl := R.lb l (by simp)
    have bq := R.ib q (by simp)
    simp only [pq_take, c1, c2, ↓reduceIte, Bool.false_eq_true]
    refine Sat.bind (Sat.bind (Sat.of_eq (rdS l ls' rfl) (Sat.bind (Sat.of_eq (rdI q is' rfl) (Sat.pure ?_)))))
    by_cases k : keyLt l (q.freq, q.node) = true
    · have k' : (pk l < pk (q.freq, q.node)) = True := by
        simp only [eq_iff_iff, iff_true]; exact (pk_lt_iff l _ bl.1 bl.2 bq.1 bq.2).mpr k
      simp only [k', decide_true, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (rdS l ls' rfl) (Sat.pure ⟨rfl, by simp [pqTakeL, k, leafQL], ?_, IH, hih, ?_⟩))
      · simp only [pqTakeL, k, ↓reduceIte]
        rw [i32_add1 _ (by omega) (by omega)]; omega
      · simp only [pqTakeL, k, ↓reduceIte]
        refine ⟨by omega, fun p hp => ?_, by simp; omega, R.isv, fun e he => R.lb e (by simp [he]), R.ib⟩
        have := R.lsv (p + 1) (by simp; omega)
        simp only [List.length_cons, List.getElem!_cons_succ] at this
        rw [← this]; congr 1; omega
    · have k' : (pk l < pk (q.freq, q.node)) = False := by
        simp only [eq_iff_iff, iff_false]; intro h; exact k ((pk_lt_iff l _ bl.1 bl.2 bq.1 bq.2).mp h)
      simp only [k', decide_false, Bool.false_eq_true, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (rdI q is' rfl) ?_)
      rw [chkI32_ok (by omega) (by omega)]
      refine Sat.bind (Sat.pure (Sat.pure ⟨rfl, by simp [pqTakeL, k], ?_, IH + 1, ?_, ?_⟩))
      · simp only [pqTakeL, k, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      · rw [i32_ofInt _ (by omega) (by omega)]; omega
      · simp only [pqTakeL, k, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by simp; omega, fun p hp => ?_, by omega, fun p hp => ?_, fun e he => R.lb e he,
          fun e he => R.ib e (by simp [he])⟩
        · have := R.lsv p hp; exact this
        · have := R.isv (p + 1) (by simp; omega)
          simp only [List.getElem!_cons_succ] at this
          rw [← this]; congr 1; omega
  | [], q :: is', _ =>
    simp only [List.length_cons, List.length_nil] at hli hlsl hihl
    have c1 : ¬ li < nl := fun h => by have := (i32_lt _ _).mp h; omega
    simp only [pq_take, c1, ↓reduceIte]
    refine Sat.bind (Sat.pure ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (rdI q is' rfl) ?_)
    rw [chkI32_ok (by omega) (by omega)]
    refine Sat.bind (Sat.pure (Sat.pure ⟨rfl, by simp [pqTakeL], ?_, IH + 1, ?_, ?_⟩))
    · simp only [pqTakeL, List.length_nil]; omega
    · rw [i32_ofInt _ (by omega) (by omega)]; omega
    · simp only [pqTakeL]
      refine ⟨by simp, fun p hp => by simp at hp, by omega, fun p hp => ?_, fun e he => by simp at he,
        fun e he => R.ib e (by simp [he])⟩
      have := R.isv (p + 1) (by simp; omega)
      simp only [List.getElem!_cons_succ] at this
      rw [← this]; congr 1; omega

end

theorem nat_le_sum : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: l, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := nat_le_sum h; simp; omega

theorem gq_lt {L : List QL} {e : QL} {j : Nat} (hj : j < L.length) : (L ++ [e])[j]! = L[j]! := by
  simp [List.getElem?_append_left hj]

theorem gq_eq {L : List QL} {e : QL} : (L ++ [e])[L.length]! = e := by simp

theorem nd_of_flat : ∀ {l : List QL}, (l.flatMap (·.tree.labs)).Nodup → ∀ {q : QL}, q ∈ l → q.tree.labs.Nodup
  | [], _, _, hq => by simp at hq
  | x :: l, h, q, hq => by
    simp only [List.flatMap_cons, List.nodup_append] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact nd_of_flat h.2.1 hq

theorem tSize_eq (t : DescSel) : ZlibNgF.Proof.TreesBuildSpec.tSize t = 2 * ZlibNgF.Proof.TreesBuildSpec.tElems t + 1 := by
  cases t <;> decide

theorem i32_u16 (x : Int32) (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 65536) : x.toUInt32.toUInt16.toNat = x.toInt.toNat := by
  rw [UInt32.toNat_toUInt16, ZlibNgF.Proof.DeflatePrime.toUInt32_toNat x h0]; omega

theorem sum_u16 (x y : UInt32) (h : x.toNat + y.toNat < 65536) : (x + y).toUInt16.toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_toUInt16, UInt32.toNat_add]; omega

theorem roots_bnd {N : Nat} {ls : List (Nat × Nat)} {is : List QL} {S I : Array UInt32} {IH IT : Nat}
    (R : QR S I N ls is IH IT) (q : QL) (hq : q ∈ roots ls is) : q.freq < 65536 ∧ q.node < 1024 := by
  rcases roots_mem hq with h | ⟨e, he, rfl⟩
  · exact R.ib q h
  · exact R.lb e he

theorem sum_le_of_perm {a c : QL} {l r : List QL} (p : l.Perm (a :: c :: r)) :
    a.freq + c.freq ≤ (l.map QL.freq).sum := by
  rw [sum_perm p]; simp only [List.map_cons, List.sum_cons]; omega

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- **The merge loop** from the sorted leaves `srt` in queue `qS`: it runs `srt.length - 1` trips without fault,
ends with the model's single FIFO entry `q` (the root, node `elems + nleaves - 2`) and every edge of `q`'s tree
stored as `tree[child].Dad`; codes below `elems` keep their `Freq`, and those that are not leaves are unchanged. -/
theorem merge_SH (t : DescSel) (X : DeflateState) (qS : Bool) (srt : List (Nat × Nat)) (nl elems : Int32)
    (hE : elems.toInt = ZlibNgF.Proof.TreesBuildSpec.tElems t) (hnl : nl.toInt = srt.length) (h2 : 2 ≤ srt.length)
    (hNE : srt.length ≤ ZlibNgF.Proof.TreesBuildSpec.tElems t)
    (hA : (tArr t X).size = ZlibNgF.Proof.TreesBuildSpec.tSize t) (hS : (qArr qS X).size = 287)
    (hI : (qArr (!qS) X).size = 287) (hsrt : ∀ p, p < srt.length → (qArr qS X)[p]! = pk srt[p]!)
    (hnd : (srt.map Prod.snd).Nodup) (hlt : ∀ e ∈ srt, e.2 < ZlibNgF.Proof.TreesBuildSpec.tElems t)
    (hsum : (srt.map Prod.fst).sum < 65536) :
    Sat (SH H i z b X d)
      (cwhile mergeCond (mergeBody (.ref (tRef t b) 0) (.ref (qRef qS b) 0) (.ref (qRef (!qS) b) 0) nl)
        (nl - 1, (0 : Int32), (0 : Int32), (0 : Int32), elems))
      (fun x H' => ∃ (Iq : Array UInt32) (A' : Array Ct) (q : QL),
        H' = SH H i z b (tPut t (qPut (!qS) X Iq) A') d ∧
        x.2.2.2.2.toInt = ZlibNgF.Proof.TreesBuildSpec.tElems t + srt.length - 1 ∧ Iq.size = 287 ∧
        A'.size = (tArr t X).size ∧
        (∀ k, k < ZlibNgF.Proof.TreesBuildSpec.tElems t → (A'[k]!).fc = ((tArr t X)[k]!).fc) ∧
        (∀ k, k < ZlibNgF.Proof.TreesBuildSpec.tElems t → k ∉ srt.map Prod.snd → A'[k]! = (tArr t X)[k]!) ∧
        (miter (srt.length - 1) (srt, [], ZlibNgF.Proof.TreesBuildSpec.tElems t)).2.1 = [q] ∧
        q.node = ZlibNgF.Proof.TreesBuildSpec.tElems t + srt.length - 2 ∧
        ∀ e ∈ q.tree.edges, (A'[e.1]!).dl.toNat = e.2) := by
  generalize hEd : ZlibNgF.Proof.TreesBuildSpec.tElems t = E at *
  generalize hNd : srt.length = N at *
  have hsz := tSize_eq t
  rw [hEd] at hsz
  have hE286 : E ≤ 286 := by rw [← hEd]; cases t <;> decide
  refine sat_cwhile (I := fun (x : Int32 × Int32 × Int32 × Int32 × Int32) H' =>
      ∃ (j : Nat) (Iq : Array UInt32) (A' : Array Ct) (IH : Nat), j + 1 ≤ N ∧
        x.1.toInt = (N : Int) - 1 - j ∧ x.2.1.toInt = N - (miter j (srt, [], E)).1.length ∧
        x.2.2.1.toInt = IH ∧ x.2.2.2.1.toInt = j ∧ x.2.2.2.2.toInt = E + j ∧
        H' = SH H i z b (tPut t (qPut (!qS) X Iq) A') d ∧ Iq.size = 287 ∧ A'.size = (tArr t X).size ∧
        QR (qArr qS X) Iq N (miter j (srt, [], E)).1 (miter j (srt, [], E)).2.1 IH j ∧
        (∀ q ∈ (miter j (srt, [], E)).2.1, ∀ e ∈ q.tree.edges, (A'[e.1]!).dl.toNat = e.2) ∧
        (∀ k, k < E → (A'[k]!).fc = ((tArr t X)[k]!).fc) ∧
        (∀ k, k < E → k ∉ srt.map Prod.snd → A'[k]! = (tArr t X)[k]!))
    (μ := fun x => x.1.toInt.toNat) _ ?_ ⟨0, qArr (!qS) X, tArr t X, 0, by omega,
      by rw [i32_sub1 _ (by omega) (by omega)]; omega, by simp [miter, hNd], rfl, rfl, by simp [hE], by
        rw [qPut_self, tPut_self], hI, rfl,
      ⟨by simp [miter, hNd], fun p hp => by simp only [miter] at hp ⊢; rw [hNd, Nat.sub_self, Nat.zero_add]; exact hsrt p (by omega), by simp [miter],
        fun p hp => by simp [miter] at hp, fun e he => by
          simp only [miter] at he
          have := hlt e he
          have : e.1 ≤ (srt.map Prod.fst).sum := nat_le_sum (List.mem_map_of_mem he)
          omega, fun q hq => by simp [miter] at hq⟩,
      fun q hq => by simp [miter] at hq, fun _ _ => rfl, fun _ _ _ => rfl⟩
      (by show (nl - 1).toInt.toNat < fuel; rw [i32_sub1 _ (by omega) (by omega)]; simp only [fuel]; omega)
  rintro ⟨mg, li, ih, it, nd⟩ _ ⟨j, Iq, A', IH, hj, hmg, hli, hih, hit, hnd', rfl, hIqs, hA's, R, hed, hfc, hoth⟩
  dsimp only at hmg hli hih hit hnd'
  have g := good_iter srt E hnd hlt j (by omega)
  simp only [mergeCond]
  refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · have hc' : mg > 0 := by simpa using hc
    have hjN : j + 1 < N := by have := (i32_lt _ _).mp hc'; simp at this; omega
    have hgn := g.node
    have hglen := g.len
    have hglab := g.lab
    have hgqi := g.qi
    have hgsum := g.sum
    obtain ⟨ndup, below⟩ := good_labs g hnd hlt
    generalize hy : miter j (srt, [], E) = y at hli R hed g hgn hglen ndup below hglab hgqi hgsum
    obtain ⟨ls, is, nn⟩ := y
    dsimp only at hli R hed hgn hglen ndup below hglab hgqi hgsum
    subst hgn
    have two : 2 ≤ (roots ls is).length := by omega
    have ne1 : ls ≠ [] ∨ is ≠ [] := by
      by_cases h : ls = []
      · right; intro h'; simp [roots, h, h'] at two
      · exact Or.inl h
    obtain ⟨p1, _, i1, _⟩ := take_roots ls is ne1
    have eS : qArr qS (tPut t (qPut (!qS) X Iq) A') = qArr qS X := by simp
    have eI : qArr (!qS) (tPut t (qPut (!qS) X Iq) A') = Iq := by simp
    have R' : QR (qArr qS (tPut t (qPut (!qS) X Iq) A')) (qArr (!qS) (tPut t (qPut (!qS) X Iq) A')) N ls is IH j := by
      rw [eS, eI]; exact R
    simp only [mergeBody]
    refine Sat.bind (Sat.mono (take_SH _ qS N ls is li nl ih it IH j (by rw [eS]; exact hS) (by rw [eI]; exact hIqs)
      (by omega) hnl hli hih hit (by omega) R' ne1) fun r1 H1 h1 => ?_)
    obtain ⟨rfl, hen, hli1, IH1, hih1, R1⟩ := h1
    obtain ⟨en, li1, ih1⟩ := r1
    dsimp only at hen hli1 hih1 ⊢
    generalize ha : pqTakeL ls is = A1 at p1 i1 hen hli1 R1
    obtain ⟨a, ls1, is1⟩ := A1
    dsimp only at p1 i1 hen hli1 R1
    have ne2 : ls1 ≠ [] ∨ is1 ≠ [] := by
      have h3 := p1.length_eq
      have h4 : (a :: roots ls1 is1).length = (roots ls1 is1).length + 1 := rfl
      have h5 : 1 ≤ (roots ls1 is1).length := by omega
      by_cases h : ls1 = []
      · right; intro h'; simp [roots, h, h'] at h5
      · exact Or.inl h
    obtain ⟨p2, _, i2, _⟩ := take_roots ls1 is1 ne2
    refine Sat.bind (Sat.mono (take_SH _ qS N ls1 is1 li1 nl ih1 it IH1 j (by rw [eS]; exact hS)
      (by rw [eI]; exact hIqs) (by omega) hnl hli1 hih1 hit (by omega) R1 ne2) fun r2 H2 h2 => ?_)
    obtain ⟨rfl, hem, hli2, IH2, hih2, R2⟩ := h2
    obtain ⟨em, li2, ih2⟩ := r2
    dsimp only at hem hli2 hih2 ⊢
    generalize hb : pqTakeL ls1 is1 = B1 at p2 i2 hem hli2 R2
    obtain ⟨c, ls2, is2⟩ := B1
    dsimp only at p2 i2 hem hli2 R2
    subst hen hem
    have P : (roots ls is).Perm (a :: c :: roots ls2 is2) := p1.trans (List.Perm.cons _ p2)
    have memA : a ∈ roots ls is := P.mem_iff.mpr (by simp)
    have memC : c ∈ roots ls is := P.mem_iff.mpr (by simp)
    have bA := roots_bnd R a memA
    have bC := roots_bnd R c memC
    have hAC : a.freq + c.freq < 65536 := by have := sum_le_of_perm P; omega
    have aL := hglab a memA
    have cL := hglab c memC
    have aB : a.node < E + j := by rw [aL]; exact below a memA _ (NT.lab_mem _)
    have cB : c.node < E + j := by rw [cL]; exact below c memC _ (NT.lab_mem _)
    have nA : (pq_node (pk (a.freq, a.node))).toInt = ((a.node : Nat) : Int) := pk_node _ bA.1 bA.2
    have nC : (pq_node (pk (c.freq, c.node))).toInt = ((c.node : Nat) : Int) := pk_node _ bC.1 bC.2
    have fAC : (pq_freq (pk (a.freq, a.node)) + pq_freq (pk (c.freq, c.node))).toUInt16.toNat = a.freq + c.freq := by
      rw [sum_u16 _ _ (by rw [pk_freq _ bA.1 bA.2, pk_freq _ bC.1 bC.2]; omega), pk_freq _ bA.1 bA.2,
        pk_freq _ bC.1 bC.2]
    generalize (pq_freq (pk (a.freq, a.node)) + pq_freq (pk (c.freq, c.node))).toUInt16 = f at fAC ⊢
    rw [nA, nC]
    have hpk : pq_pack f.toUInt32 nd = pk (a.freq + c.freq, E + j) := by
      rw [pq_pack_pk f nd (by omega) (by omega), fAC]; congr; omega
    rw [hpk]
    have hv : nd.toUInt32.toUInt16.toNat = E + j := by rw [i32_u16 nd (by omega) (by omega)]; omega
    generalize nd.toUInt32.toUInt16 = v at hv ⊢
    have hnd2 : nd.toInt = ((E + j : Nat) : Int) := by omega
    have hit2 : it.toInt = ((j : Nat) : Int) := hit
    rw [hnd2, hit2]
    have hA'sz : A'.size = 2 * E + 1 := by rw [hA's, hA, hsz]
    refine Sat.bind (Sat.of_eq (ctSetFc_T t (tPut t (qPut (!qS) X Iq) A') (E + j) (by simp; omega) f) ?_)
    simp only [tArr_tPut, tPut_tPut]
    refine Sat.bind (Sat.of_eq (ctSetDl_T t _ c.node (by simp; omega) v) ?_)
    simp only [tArr_tPut, tPut_tPut]
    refine Sat.bind (Sat.of_eq (ctSetDl_T t _ a.node (by simp; omega) v) ?_)
    simp only [tArr_tPut, tPut_tPut]
    refine Sat.bind (Sat.of_eq (dwSet_Q (!qS) _ j (by simp; omega) _) ?_)
    simp only [qArr_tPut, qArr_qPut, qt_q]
    rw [chkI32_ok (by omega) (by omega)]
    refine Sat.bind (Sat.pure ?_)
    rw [chkI32_ok (by omega) (by omega)]
    refine Sat.bind (Sat.pure (Sat.pure ?_))
    -- the model after this trip
    have hM : miter (j + 1) (srt, [], E) =
        (ls2, is2 ++ [⟨a.freq + c.freq, E + j, .node (E + j) a.tree c.tree⟩], E + j + 1) := by
      rw [miter_succ, hy]; simp only [mstep, ha, hb]
    -- distinct labels
    have NDP := (flatMap_perm (·.tree.labs) P).nodup_iff.mp ndup
    simp only [List.flatMap_cons, List.nodup_append, List.mem_append] at NDP
    obtain ⟨_, ⟨_, _, dcR⟩, daR⟩ := NDP
    have tnd : ∀ q ∈ roots ls is, q.tree.labs.Nodup := fun q hq => nd_of_flat ndup hq
    have ac : a.node ≠ c.node := fun e => daR _ (aL ▸ NT.lab_mem a.tree) _ (Or.inl (e ▸ cL ▸ NT.lab_mem c.tree)) rfl
    have lowLeaf : ∀ q ∈ roots ls is, q.node < E → q.node ∈ srt.map Prod.snd := fun q hq hqE => by
      rcases roots_mem hq with h | ⟨e, he, rfl⟩
      · have := (hgqi q h).1; omega
      · obtain ⟨k, hk⟩ := g.suffix
        dsimp only at hk
        rw [hk] at he
        exact List.mem_map_of_mem (List.mem_of_mem_drop he)
    have hR2 := R2
    rw [eS, eI] at hR2
    -- the tree after the four stores
    have get3 : ∀ k, k ≠ E + j → k ≠ c.node → k ≠ a.node →
        (((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
          { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v }).set! a.node
          { fc := ((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
            { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v })[a.node]!.fc,
            dl := v })[k]! = A'[k]! := fun k h1 h2 h3 => by
      rw [set!_get_ne _ _ _ _ h3, set!_get_ne _ _ _ _ h2, set!_get_ne _ _ _ _ h1]
    have fc3 : ∀ k, k ≠ E + j →
        ((((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
          { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v }).set! a.node
          { fc := ((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
            { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v })[a.node]!.fc,
            dl := v })[k]!).fc = (A'[k]!).fc := fun k h1 => by
      by_cases h3 : k = a.node
      · subst h3; rw [set!_get_eq _ _ _ (by simp; omega)]
        by_cases h2 : a.node = c.node
        · exact absurd h2 ac
        · rw [set!_get_ne _ _ _ _ h2, set!_get_ne _ _ _ _ h1]
      · rw [set!_get_ne _ _ _ _ h3]
        by_cases h2 : k = c.node
        · subst h2; rw [set!_get_eq _ _ _ (by simp; omega), set!_get_ne _ _ _ _ h1]
        · rw [set!_get_ne _ _ _ _ h2, set!_get_ne _ _ _ _ h1]
    have dlA : ((((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
          { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v }).set! a.node
          { fc := ((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
            { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v })[a.node]!.fc,
            dl := v })[a.node]!).dl = v := by rw [set!_get_eq _ _ _ (by simp; omega)]
    have dlC : ((((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
          { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v }).set! a.node
          { fc := ((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
            { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v })[a.node]!.fc,
            dl := v })[c.node]!).dl = v := by
      rw [set!_get_ne _ _ _ _ (Ne.symm ac), set!_get_eq _ _ _ (by simp; omega)]
    have hA3 : (((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
          { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v }).set! a.node
          { fc := ((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
            { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v })[a.node]!.fc,
            dl := v }).size = A'.size := by simp
    generalize ((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
          { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v }).set! a.node
          { fc := ((A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl }).set! c.node
            { fc := (A'.set! (E + j) { fc := f, dl := A'[E + j]!.dl })[c.node]!.fc, dl := v })[a.node]!.fc,
            dl := v } = A3 at get3 fc3 dlA dlC hA3 ⊢
    have memR : ∀ q ∈ roots ls2 is2, q ∈ roots ls is := fun q hq => P.mem_iff.mpr (by simp [hq])
    -- edges of the other roots are kept
    have keep : ∀ q ∈ roots ls2 is2, ∀ e ∈ q.tree.edges, (A3[e.1]!).dl.toNat = e.2 := by
      intro q hq e he
      obtain ⟨h1, _, _⟩ := NT.edge_mem q.tree (tnd q (memR q hq)) he
      have m1 : e.1 ∈ (roots ls2 is2).flatMap (·.tree.labs) := List.mem_flatMap.mpr ⟨q, hq, h1⟩
      have n1 : e.1 ≠ a.node := fun h => daR _ (aL ▸ NT.lab_mem a.tree) _ (Or.inr m1) h.symm
      have n2 : e.1 ≠ c.node := fun h => dcR _ (cL ▸ NT.lab_mem c.tree) _ m1 h.symm
      have n3 : e.1 ≠ E + j := by have := below q (memR q hq) _ h1; omega
      rw [get3 _ n3 n2 n1]
      rcases roots_mem hq with hq' | ⟨l, _, rfl⟩
      · exact hed q (i1 q (i2 q hq')) e he
      · simp [leafQL, NT.edges] at he
    -- the edges of the two taken roots
    have eA : ∀ e ∈ a.tree.edges, (A3[e.1]!).dl.toNat = e.2 := by
      intro e he
      obtain ⟨h1, _, h3⟩ := NT.edge_mem a.tree (tnd a memA) he
      have n1 : e.1 ≠ a.node := by rw [aL]; exact h3
      have n2 : e.1 ≠ c.node := fun h => daR _ h1 _ (Or.inl (h ▸ cL ▸ NT.lab_mem c.tree)) rfl
      have n3 : e.1 ≠ E + j := by have := below a memA _ h1; omega
      rw [get3 _ n3 n2 n1]
      rcases roots_mem memA with hq' | ⟨l, _, hl⟩
      · exact hed a hq' e he
      · rw [hl] at he; simp [leafQL, NT.edges] at he
    have eC : ∀ e ∈ c.tree.edges, (A3[e.1]!).dl.toNat = e.2 := by
      intro e he
      obtain ⟨h1, _, h3⟩ := NT.edge_mem c.tree (tnd c memC) he
      have n2 : e.1 ≠ c.node := by rw [cL]; exact h3
      have n1 : e.1 ≠ a.node := fun h => daR _ (aL ▸ NT.lab_mem a.tree) _ (Or.inl h1) h.symm
      have n3 : e.1 ≠ E + j := by have := below c memC _ h1; omega
      rw [get3 _ n3 n2 n1]
      rcases roots_mem memC with hq' | ⟨l, _, hl⟩
      · exact hed c hq' e he
      · rw [hl] at he; simp [leafQL, NT.edges] at he
    refine ⟨⟨j + 1, Iq.set! j (pk (a.freq + c.freq, E + j)), A3, IH2, by omega, ?_, ?_, hih2, ?_, ?_, rfl,
      by simp [hIqs], by rw [hA3, hA's], ?_, ?_, ?_, ?_⟩, ?_⟩
    · dsimp only; rw [i32_sub1 _ (by omega) (by omega)]; omega
    · dsimp only; rw [hM]; exact hli2
    · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
    · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
    · rw [hM]
      have hl2 := hR2.ihl
      refine ⟨hR2.lsl, hR2.lsv, by simp; omega, fun p hp => ?_, hR2.lb, fun q hq => ?_⟩
      · simp only [List.length_append, List.length_singleton] at hp
        by_cases hpl : p < is2.length
        · rw [set!_get_ne _ _ _ _ (by omega), gq_lt hpl]; exact hR2.isv p hpl
        · have hpe : p = is2.length := by omega
          subst hpe
          rw [show IH2 + is2.length = j by omega, set!_get_eq _ _ _ (by omega), gq_eq]
      · rcases List.mem_append.mp hq with hq | hq
        · exact hR2.ib q hq
        · simp only [List.mem_singleton] at hq; subst hq; simp only; omega
    · rw [hM]
      intro q hq e he
      rcases List.mem_append.mp hq with hq | hq
      · exact keep q (List.mem_append_right _ hq) e he
      · simp only [List.mem_singleton] at hq; subst hq
        simp only [NT.edges, List.mem_cons, List.mem_append] at he
        rcases he with rfl | rfl | he | he
        · simp only; rw [← aL, dlA, hv]
        · simp only; rw [← cL, dlC, hv]
        · exact eA e he
        · exact eC e he
    · intro k hk; rw [fc3 k (by omega)]; exact hfc k hk
    · intro k hk hk'
      have n2 : k ≠ c.node := fun h => hk' (h ▸ lowLeaf c memC (by omega))
      have n1 : k ≠ a.node := fun h => hk' (h ▸ lowLeaf a memA (by omega))
      rw [get3 k (by omega) n2 n1]; exact hoth k hk hk'
    · dsimp only; rw [i32_sub1 _ (by omega) (by omega)]; omega
  · have hc' : ¬ (mg > 0) := by simpa using hc
    have hjN : j = N - 1 := by
      have : ¬ (j < N - 1) := fun hlt => hc' ((i32_lt _ _).mpr (by simp; omega))
      omega
    subst hjN
    obtain ⟨_, q, hq, hqn⟩ := good_final (srt := srt) (by rw [hNd]; omega) (by rw [hNd]; exact g)
    exact ⟨Iq, A', q, rfl, by dsimp only; omega, hIqs, hA's, hfc, hoth, hq, by rw [hqn, hNd], fun e he => hed q (by rw [hq]; simp) e he⟩

end

end ZlibNgF.Proof.TreesMerge
