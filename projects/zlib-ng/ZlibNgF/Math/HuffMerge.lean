import ZlibNgF.Math.HuffModel

noncomputable section


/-!
# zlib-ng's two-queue merge is a Huffman merge (heap-free)

`mergeLoop` (the `for (merges = nleaves - 1; …)` loop of `build_tree`) takes, at each step, two roots of least
weight: the sorted leaves and the FIFO of created nodes are each ascending, so the two least roots are at the
queue heads (the comment of `build_tree`). The invariant (`MInv t ls is`, `t` the weight of the last root
taken): the leaves are ascending, the FIFO is ascending, every remaining root weighs at least `t`, and every
FIFO node weighs at most `2 * t` (it is the sum of two roots taken before, each at most `t`).

`mergeLoop_merges`: the loop ends with a single FIFO entry, and the forest of the initial leaves `Merges` to its
tree (`HuffTree.Merges`, weight-only order), so `HuffFib.fibPlus_of_merges` applies.
-/

namespace ZlibNgF.Math.Huff
set_option autoImplicit false

/-- The forest of roots: the unused leaves and the FIFO's nodes. -/
def forestOf (ls : List (Nat × Nat)) (is : List QE) : List HTree :=
  ls.map (fun e => HTree.leaf e.2 e.1) ++ is.map QE.tree

/-- The merge invariant. -/
structure MInv (t : Nat) (ls : List (Nat × Nat)) (is : List QE) : Prop where
  lsSorted : ls.Pairwise (fun a b => a.1 ≤ b.1)
  isSorted : is.Pairwise (fun a b => a.freq ≤ b.freq)
  lsLow : ∀ e ∈ ls, t ≤ e.1
  isLow : ∀ q ∈ is, t ≤ q.freq
  isHigh : ∀ q ∈ is, q.freq ≤ 2 * t
  isWeight : ∀ q ∈ is, q.freq = q.tree.weight
  lsPos : ∀ e ∈ ls, 1 ≤ e.1
  isPos : ∀ q ∈ is, 1 ≤ q.freq

/-- What one `pq_take` gives: the taken entry is no heavier than any remaining root, it was one of the roots,
and the queues lose exactly it. -/
structure TakeOK (ls : List (Nat × Nat)) (is : List QE) (x : QE) (ls' : List (Nat × Nat)) (is' : List QE) :
    Prop where
  perm : (forestOf ls is).Perm (x.tree :: forestOf ls' is')
  leLs : ∀ e ∈ ls', x.freq ≤ e.1
  leIs : ∀ q ∈ is', x.freq ≤ q.freq
  src : (∃ e ∈ ls, x = leafQE e) ∨ x ∈ is
  subLs : ∀ e ∈ ls', e ∈ ls
  subIs : ∀ q ∈ is', q ∈ is
  sortLs : ls'.Pairwise (fun a b => a.1 ≤ b.1)
  sortIs : is'.Pairwise (fun a b => a.freq ≤ b.freq)

theorem pqTake_ok {t : Nat} {ls : List (Nat × Nat)} {is : List QE} (h : MInv t ls is)
    (ne : ls ≠ [] ∨ is ≠ []) :
    TakeOK ls is (pqTake ls is).1 (pqTake ls is).2.1 (pqTake ls is).2.2 := by
  have hl := h.lsSorted
  have hi := h.isSorted
  match ls, is, ne with
  | l :: ls, [], _ =>
    rw [List.pairwise_cons] at hl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [pqTake, forestOf, leafQE]
    · intro e he; exact hl.1 e he
    · intro q hq; simp [pqTake] at hq
    · exact Or.inl ⟨l, by simp, rfl⟩
    · intro e he; simp [pqTake] at he; simp [he]
    · intro q hq; simp [pqTake] at hq
    · exact hl.2
    · simp [pqTake]
  | [], i :: is, _ =>
    rw [List.pairwise_cons] at hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [pqTake, forestOf]
    · intro e he; simp [pqTake] at he
    · intro q hq; exact hi.1 q hq
    · exact Or.inr (by simp [pqTake])
    · intro e he; simp [pqTake] at he
    · intro q hq; simp only [pqTake] at hq; simp [hq]
    · simp [pqTake]
    · exact hi.2
  | l :: ls, i :: is, _ =>
    rw [List.pairwise_cons] at hl hi
    by_cases k : keyLt l (i.freq, i.node) = true
    · have hli : l.1 ≤ i.freq := by
        simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at k
        omega
      simp only [pqTake, k, ite_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [forestOf, leafQE]
      · intro e he; exact hl.1 e he
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hli
        · exact Nat.le_trans hli (hi.1 q hq)
      · exact Or.inl ⟨l, by simp, rfl⟩
      · intro e he; simp [he]
      · intro q hq; exact hq
      · exact hl.2
      · exact List.pairwise_cons.mpr hi
    · have hil : i.freq ≤ l.1 := by
        simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at k
        omega
      have k' : keyLt l (i.freq, i.node) = false := by simpa using k
      simp only [pqTake, k', Bool.false_eq_true, ite_false]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [forestOf, List.map_cons, List.cons_append]
        exact (List.Perm.cons _ List.perm_middle).trans (List.Perm.swap _ _ _)
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hil
        · exact Nat.le_trans hil (hl.1 e he)
      · intro q hq; exact hi.1 q hq
      · exact Or.inr (by simp)
      · intro e he; exact he
      · intro q hq; simp [hq]
      · exact List.pairwise_cons.mpr hl
      · exact hi.2

/-- `Merges` depends on the starting forest only up to permutation. -/
theorem Merges.perm {s s₁ tr : List HTree} {T : HTree} (h : Merges s tr T) (p : s.Perm s₁) :
    Merges s₁ tr T := by
  match h with
  | .done t =>
    have := List.perm_singleton.mp p.symm
    subst this; exact Merges.done t
  | .step hst hm =>
    obtain ⟨r, hp, hn, hmm, hs'⟩ := hst
    exact Merges.step ⟨r, p.symm.trans hp, hn, hmm, hs'⟩ hm

theorem forestOf_length (ls : List (Nat × Nat)) (is : List QE) :
    (forestOf ls is).length = ls.length + is.length := by simp [forestOf]

/-- **The merge loop is a Huffman merge.** From an invariant state with `k + 1` roots (and a nonempty FIFO
when `k = 0`), `mergeLoop k` ends with one FIFO entry `q`, and the roots `Merges` to `q.tree`. -/
theorem mergeLoop_merges : ∀ (k : Nat) (t : Nat) (ls : List (Nat × Nat)) (is : List QE) (node : Nat),
    MInv t ls is → ls.length + is.length = k + 1 → (1 ≤ k ∨ is ≠ []) →
    ∃ q tr, mergeLoop k ls is node = [q] ∧ Merges (forestOf ls is) tr q.tree ∧ q.freq = q.tree.weight
  | 0, t, ls, is, node, h, len, ne => by
    rcases ne with ne | ne
    · omega
    · rcases is with _ | ⟨q, is'⟩
      · exact absurd rfl ne
      · have hl0 : ls.length = 0 := by simp only [List.length_cons] at len; omega
        have hi0 : is'.length = 0 := by simp only [List.length_cons] at len; omega
        rw [List.length_eq_zero_iff] at hl0 hi0
        subst hl0; subst hi0
        exact ⟨q, [], rfl, by simpa [forestOf] using Merges.done q.tree, h.isWeight q (by simp)⟩
  | k + 1, t, ls, is, node, h, len, _ => by
    have ne1 : ls ≠ [] ∨ is ≠ [] := by
      rcases ls with _ | ⟨l, ls⟩
      · rcases is with _ | ⟨i, is⟩
        · simp at len
        · exact Or.inr (by simp)
      · exact Or.inl (by simp)
    have A := pqTake_ok h ne1
    generalize ha : pqTake ls is = a at A
    obtain ⟨x, ls1, is1⟩ := a
    dsimp only at A
    have lx : t ≤ x.freq ∧ x.freq = x.tree.weight ∧ 1 ≤ x.freq := by
      rcases A.src with ⟨e, he, rfl⟩ | hx
      · exact ⟨h.lsLow e he, rfl, h.lsPos e he⟩
      · exact ⟨h.isLow x hx, h.isWeight x hx, h.isPos x hx⟩
    have len1 : ls1.length + is1.length = k + 1 := by
      have := A.perm.length_eq
      simp only [forestOf_length, List.length_cons] at this
      omega
    have h1 : MInv t ls1 is1 :=
      ⟨A.sortLs, A.sortIs, fun e he => h.lsLow e (A.subLs e he), fun q hq => h.isLow q (A.subIs q hq),
        fun q hq => h.isHigh q (A.subIs q hq), fun q hq => h.isWeight q (A.subIs q hq),
        fun e he => h.lsPos e (A.subLs e he), fun q hq => h.isPos q (A.subIs q hq)⟩
    have ne2 : ls1 ≠ [] ∨ is1 ≠ [] := by
      rcases ls1 with _ | ⟨l, ls1⟩
      · rcases is1 with _ | ⟨i, is1⟩
        · simp at len1
        · exact Or.inr (by simp)
      · exact Or.inl (by simp)
    have B := pqTake_ok h1 ne2
    generalize hb : pqTake ls1 is1 = b at B
    obtain ⟨y, ls2, is2⟩ := b
    dsimp only at B
    have ly : t ≤ y.freq ∧ y.freq = y.tree.weight ∧ 1 ≤ y.freq ∧ x.freq ≤ y.freq := by
      rcases B.src with ⟨e, he, rfl⟩ | hy
      · exact ⟨h1.lsLow e he, rfl, h1.lsPos e he, A.leLs e he⟩
      · exact ⟨h1.isLow y hy, h1.isWeight y hy, h1.isPos y hy, A.leIs y hy⟩
    obtain ⟨lx1, lx2, lx3⟩ := lx
    obtain ⟨ly1, ly2, ly3, ly4⟩ := ly
    let nq : QE := ⟨x.freq + y.freq, node, .node x.tree y.tree⟩
    have len2 : ls2.length + (is2 ++ [nq]).length = k + 1 := by
      have := B.perm.length_eq
      simp only [forestOf_length, List.length_cons] at this
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have h2 : MInv y.freq ls2 (is2 ++ [nq]) := by
      refine ⟨B.sortLs, ?_, fun e he => B.leLs e he, ?_, ?_, ?_, fun e he => h1.lsPos e (B.subLs e he), ?_⟩
      · rw [List.pairwise_append]
        refine ⟨B.sortIs, by simp, ?_⟩
        intro q hq r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        subst hr
        have := h1.isHigh q (B.subIs q hq)
        show q.freq ≤ x.freq + y.freq
        omega
      · intro q hq
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with hq | rfl
        · exact B.leIs q hq
        · show y.freq ≤ x.freq + y.freq; omega
      · intro q hq
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with hq | rfl
        · have := h1.isHigh q (B.subIs q hq); omega
        · show x.freq + y.freq ≤ 2 * y.freq; omega
      · intro q hq
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with hq | rfl
        · exact h1.isWeight q (B.subIs q hq)
        · show x.freq + y.freq = HTree.weight (.node x.tree y.tree)
          simp only [HTree.weight]; omega
      · intro q hq
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with hq | rfl
        · exact h1.isPos q (B.subIs q hq)
        · show 1 ≤ x.freq + y.freq; omega
    obtain ⟨q, tr, run, merges, qw⟩ := mergeLoop_merges k y.freq ls2 (is2 ++ [nq]) (node + 1) h2 len2
      (Or.inr (by simp))
    refine ⟨q, x.tree :: y.tree :: tr, ?_, ?_, qw⟩
    · simp only [mergeLoop, ha, hb]; exact run
    · refine Merges.step (s' := HTree.node x.tree y.tree :: forestOf ls2 is2) ?_ ?_
      · refine ⟨forestOf ls2 is2, A.perm.trans (List.Perm.cons _ B.perm), ?_, ?_, rfl⟩
        · intro z hz
          simp only [List.mem_cons] at hz
          show x.tree.weight ≤ z.weight
          rcases hz with rfl | hz
          · omega
          · simp only [forestOf, List.mem_append, List.mem_map] at hz
            rcases hz with ⟨e, he, rfl⟩ | ⟨r, hr, rfl⟩
            · have := B.leLs e he; simp only [HTree.weight]; omega
            · have := B.leIs r hr; have := h1.isWeight r (B.subIs r hr); omega
        · intro z hz
          show y.tree.weight ≤ z.weight
          simp only [forestOf, List.mem_append, List.mem_map] at hz
          rcases hz with ⟨e, he, rfl⟩ | ⟨r, hr, rfl⟩
          · have := B.leLs e he; simp only [HTree.weight]; omega
          · have := B.leIs r hr; have := h1.isWeight r (B.subIs r hr); omega
      · refine merges.perm ?_
        show (ls2.map (fun e => HTree.leaf e.2 e.1) ++ (is2 ++ [nq]).map QE.tree).Perm
          (HTree.node x.tree y.tree :: (ls2.map (fun e => HTree.leaf e.2 e.1) ++ is2.map QE.tree))
        rw [List.map_append, ← List.append_assoc]
        exact List.perm_append_singleton _ _

end ZlibNgF.Math.Huff
