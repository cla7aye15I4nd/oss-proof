import ZlibNgF.Math.HuffBuilt

/-!
# The merge loop with node numbers (heap-free)

`HuffModel.mergeLoop` builds an `HTree`, whose internal nodes carry no number. `build_tree` numbers them
(`node = elems, elems + 1, …`) and stores, for every node but the root, the number of its parent in
`tree[n].Dad`. This file runs the same merge on numbered trees (`NT`): `pqTakeL` / `mstep` / `miter` are
`pqTake` / one trip of `mergeLoop` / `mergeLoop` with the node number kept on every internal node, and
`mergeLoop_erase` says that forgetting the numbers gives `mergeLoop` back.

`NT.dep` is the depth of a number; `dep_edge`, `depthIn_erase` and `ovf_erase` relate it to the parent links, to
`depthIn` and to `overflowCount`.
-/

set_option autoImplicit false

noncomputable section

namespace ZlibNgF.Math.TreesLabeled
open ZlibNgF.Math.Huff

/-- A tree whose internal nodes carry their node number. -/
inductive NT where
  | leaf (s w : Nat)
  | node (n : Nat) (a b : NT)

instance : Inhabited NT := ⟨.leaf 0 0⟩

namespace NT

/-- The tree without the numbers of the internal nodes. -/
noncomputable def erase : NT → HTree
  | leaf s w => .leaf s w
  | node _ a b => .node a.erase b.erase

/-- The number of the root. -/
def lab : NT → Nat
  | leaf s _ => s
  | node n _ _ => n

/-- Every number of the tree. -/
noncomputable def labs : NT → List Nat
  | leaf s _ => [s]
  | node n a b => n :: (a.labs ++ b.labs)

/-- The (child, parent) pairs. -/
noncomputable def edges : NT → List (Nat × Nat)
  | leaf _ _ => []
  | node n a b => (a.lab, n) :: (b.lab, n) :: (a.edges ++ b.edges)

/-- The numbers of the internal nodes. -/
noncomputable def ints : NT → List Nat
  | leaf _ _ => []
  | node n a b => n :: (a.ints ++ b.ints)

/-- The numbers of the leaves. -/
noncomputable def lvs : NT → List Nat
  | leaf s _ => [s]
  | node _ a b => a.lvs ++ b.lvs

/-- The depth of number `x` when the root is at depth `k`. -/
noncomputable def dep : NT → Nat → Nat → Nat
  | leaf _ _, k, _ => k
  | node n a b, k, x => if x = n then k else if x ∈ a.labs then a.dep (k + 1) x else b.dep (k + 1) x

theorem lab_mem : ∀ t : NT, t.lab ∈ t.labs
  | leaf _ _ => by simp [lab, labs]
  | node _ _ _ => by simp [lab, labs]

theorem dep_lab : ∀ (t : NT) (k : Nat), t.dep k t.lab = k
  | leaf _ _, _ => rfl
  | node _ _ _, _ => by simp [dep, lab]

theorem dep_shift : ∀ (t : NT) (k x : Nat), t.dep (k + 1) x = t.dep k x + 1
  | leaf _ _, _, _ => rfl
  | node n a b, k, x => by
    simp only [dep]
    split
    · rfl
    · split
      · exact dep_shift a _ x
      · exact dep_shift b _ x


theorem ints_sub : ∀ (t : NT) {x : Nat}, x ∈ t.ints → x ∈ t.labs
  | leaf _ _, _, h => by simp [ints] at h
  | node n a b, x, h => by
    simp only [ints, labs, List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (ints_sub a h))
    · exact Or.inr (Or.inr (ints_sub b h))

theorem lvs_sub : ∀ (t : NT) {x : Nat}, x ∈ t.lvs → x ∈ t.labs
  | leaf _ _, _, h => by simpa [lvs, labs] using h
  | node n a b, x, h => by
    simp only [lvs, labs, List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inr (Or.inl (lvs_sub a h))
    · exact Or.inr (Or.inr (lvs_sub b h))

theorem edge_labs : ∀ (t : NT) {e : Nat × Nat}, e ∈ t.edges → e.1 ∈ t.labs ∧ e.2 ∈ t.labs ∧ e.1 ≠ t.lab ∨
    (t.labs.Nodup → False)
  | leaf _ _, _, h => by simp [edges] at h
  | node n a b, e, h => by
    by_cases nd : (node n a b).labs.Nodup
    · left
      have nd' := nd
      simp only [labs, List.nodup_cons, List.mem_append, not_or, List.nodup_append] at nd'
      obtain ⟨⟨na, nb⟩, nda, ndb, dab⟩ := nd'
      simp only [edges, List.mem_cons, List.mem_append] at h
      simp only [labs, lab, List.mem_cons, List.mem_append]
      rcases h with rfl | rfl | h | h
      · exact ⟨Or.inr (Or.inl (lab_mem a)), Or.inl rfl, fun e => na (e ▸ lab_mem a)⟩
      · exact ⟨Or.inr (Or.inr (lab_mem b)), Or.inl rfl, fun e => nb (e ▸ lab_mem b)⟩
      · rcases edge_labs a h with ⟨h1, h2, _⟩ | h'
        · exact ⟨Or.inr (Or.inl h1), Or.inr (Or.inl h2), fun e => na (e ▸ h1)⟩
        · exact (h' nda).elim
      · rcases edge_labs b h with ⟨h1, h2, _⟩ | h'
        · exact ⟨Or.inr (Or.inr h1), Or.inr (Or.inr h2), fun e => nb (e ▸ h1)⟩
        · exact (h' ndb).elim
    · exact Or.inr nd

theorem edge_mem (t : NT) (nd : t.labs.Nodup) {e : Nat × Nat} (h : e ∈ t.edges) :
    e.1 ∈ t.labs ∧ e.2 ∈ t.labs ∧ e.1 ≠ t.lab := by
  rcases edge_labs t h with h | h
  · exact h
  · exact (h nd).elim

/-- **A child is one deeper than its parent.** -/
theorem dep_edge : ∀ (t : NT) (k : Nat), t.labs.Nodup → ∀ e ∈ t.edges, t.dep k e.1 = t.dep k e.2 + 1
  | leaf _ _, _, _, e, h => by simp [edges] at h
  | node n a b, k, nd, e, h => by
    have nd' := nd
    simp only [labs, List.nodup_cons, List.mem_append, not_or, List.nodup_append] at nd'
    obtain ⟨⟨na, nb⟩, nda, ndb, dab⟩ := nd'
    have nab : ∀ x, x ∈ b.labs → x ∉ a.labs := fun x hb ha => dab x ha x hb rfl
    simp only [edges, List.mem_cons, List.mem_append] at h
    rcases h with rfl | rfl | h | h
    · have h1 : a.lab ≠ n := fun e => na (e ▸ lab_mem a)
      simp [dep, h1, lab_mem, dep_lab]
    · have h1 : b.lab ≠ n := fun e => nb (e ▸ lab_mem b)
      simp [dep, h1, nab _ (lab_mem b), dep_lab]
    · obtain ⟨h1, h2, _⟩ := edge_mem a nda h
      have e1 : e.1 ≠ n := fun e' => na (e' ▸ h1)
      have e2 : e.2 ≠ n := fun e' => na (e' ▸ h2)
      simp only [dep, e1, e2, h1, h2, ite_false, ite_true]
      exact dep_edge a _ nda e h
    · obtain ⟨h1, h2, _⟩ := edge_mem b ndb h
      have e1 : e.1 ≠ n := fun e' => nb (e' ▸ h1)
      have e2 : e.2 ≠ n := fun e' => nb (e' ▸ h2)
      simp only [dep, e1, e2, nab _ h1, nab _ h2, ite_false]
      exact dep_edge b _ ndb e h

/-- Every number but the root's is the child of an edge. -/
theorem has_parent : ∀ (t : NT) (x : Nat), x ∈ t.labs → x ≠ t.lab → ∃ p, (x, p) ∈ t.edges
  | leaf _ _, x, h, ne => by simp [labs] at h; exact (ne h).elim
  | node n a b, x, h, ne => by
    simp only [labs, lab, List.mem_cons, List.mem_append] at h ne
    rcases h with h | h | h
    · exact (ne h).elim
    · by_cases hx : x = a.lab
      · exact ⟨n, by simp [edges, hx]⟩
      · obtain ⟨p, hp⟩ := has_parent a x h hx
        exact ⟨p, by simp [edges, hp]⟩
    · by_cases hx : x = b.lab
      · exact ⟨n, by simp [edges, hx]⟩
      · obtain ⟨p, hp⟩ := has_parent b x h hx
        exact ⟨p, by simp [edges, hp]⟩

theorem erase_syms : ∀ t : NT, t.erase.leaves.map (·.sym) = t.lvs
  | leaf _ _ => rfl
  | node _ a b => by
    simp only [erase, HTree.leaves, lvs, List.map_map, List.map_append]
    rw [← erase_syms a, ← erase_syms b]; rfl

/-- **`depthIn` of the erased tree is `dep`.** -/
theorem depthIn_find : ∀ (t : NT), t.labs.Nodup → ∀ v ∈ t.lvs,
    (t.erase.leaves.find? (fun x => x.sym == v)).map (·.d) = some (t.dep 0 v)
  | leaf s w, _, v, h => by
    simp only [lvs, List.mem_singleton] at h; subst h
    simp [erase, HTree.leaves, dep]
  | node n a b, nd, v, h => by
    have nd' := nd
    simp only [labs, List.nodup_cons, List.mem_append, not_or, List.nodup_append] at nd'
    obtain ⟨⟨na, nb⟩, nda, ndb, dab⟩ := nd'
    simp only [erase, HTree.leaves, List.find?_map]
    simp only [lvs, List.mem_append] at h
    have vn : v ≠ n := by
      rcases h with h | h
      · exact fun e => na (e ▸ lvs_sub a h)
      · exact fun e => nb (e ▸ lvs_sub b h)
    rcases h with h | h
    · rw [List.find?_append]
      have ih := depthIn_find a nda v h
      have hf : (a.erase.leaves.find? ((fun x => x.sym == v) ∘ fun x => { x with d := x.d + 1 })) =
          a.erase.leaves.find? (fun x => x.sym == v) := rfl
      rw [hf]
      cases hc : a.erase.leaves.find? (fun x => x.sym == v) with
      | none => simp [hc] at ih
      | some y =>
        simp only [hc, Option.map_some, Option.some_or] at ih ⊢
        simp only [Option.some.injEq] at ih ⊢
        simp only [dep, vn, lvs_sub a h, ite_false, ite_true, dep_shift, ← ih]
    · have hna : v ∉ a.lvs := fun ha => dab v (lvs_sub a ha) v (lvs_sub b h) rfl
      rw [List.find?_append]
      have hnone : (a.erase.leaves.find? ((fun x => x.sym == v) ∘ fun x => { x with d := x.d + 1 })) = none := by
        rw [List.find?_eq_none]
        intro x hx
        simp only [Function.comp, beq_iff_eq]
        intro e; apply hna; rw [← erase_syms a, ← e]; exact List.mem_map_of_mem hx
      have hnla : v ∉ a.labs := fun ha => dab v ha v (lvs_sub b h) rfl
      rw [hnone, Option.none_or]
      have ih := depthIn_find b ndb v h
      have hf : (b.erase.leaves.find? ((fun x => x.sym == v) ∘ fun x => { x with d := x.d + 1 })) =
          b.erase.leaves.find? (fun x => x.sym == v) := rfl
      rw [hf]
      cases hc : b.erase.leaves.find? (fun x => x.sym == v) with
      | none => simp [hc] at ih
      | some y =>
        simp only [hc, Option.map_some, Option.some.injEq] at ih ⊢
        simp only [dep, vn, hnla, ite_false, dep_shift, ← ih]

theorem depthIn_erase (t : NT) (nd : t.labs.Nodup) (v : Nat) (h : v ∈ t.lvs) :
    depthIn t.erase v = t.dep 0 v := by
  have := depthIn_find t nd v h
  unfold depthIn
  cases hc : t.erase.leaves.find? (fun x => x.sym == v) with
  | none => simp [hc] at this
  | some y => simp only [hc, Option.map_some, Option.some.injEq] at this; exact this

/-- **The overflow of the erased tree** counts the numbers deeper than `L`. -/
theorem ovf_erase : ∀ (L k : Nat) (t : NT), t.labs.Nodup →
    ovfAux L k t.erase = t.ints.countP (fun x => decide (L < t.dep k x)) + t.lvs.countP (fun x => decide (L < t.dep k x))
  | L, k, leaf s w, _ => by by_cases h : L < k <;> simp [ovfAux, erase, ints, lvs, dep, h]
  | L, k, node n a b, nd => by
    have nd' := nd
    simp only [labs, List.nodup_cons, List.mem_append, not_or, List.nodup_append] at nd'
    obtain ⟨⟨na, nb⟩, nda, ndb, dab⟩ := nd'
    have nab : ∀ x, x ∈ b.labs → x ∉ a.labs := fun x hb ha => dab x ha x hb rfl
    simp only [ovfAux, erase, ints, lvs, List.countP_cons, List.countP_append]
    rw [ovf_erase L (k + 1) a nda, ovf_erase L (k + 1) b ndb]
    have ca : ∀ l : List Nat, (∀ x ∈ l, x ∈ a.labs) →
        l.countP (fun x => decide (L < (node n a b).dep k x)) = l.countP (fun x => decide (L < a.dep (k + 1) x)) :=
      fun l hl => List.countP_congr (fun x hx => by
        have h1 := hl x hx
        have h2 : x ≠ n := fun e => na (e ▸ h1)
        simp [dep, h2, h1])
    have cb : ∀ l : List Nat, (∀ x ∈ l, x ∈ b.labs) →
        l.countP (fun x => decide (L < (node n a b).dep k x)) = l.countP (fun x => decide (L < b.dep (k + 1) x)) :=
      fun l hl => List.countP_congr (fun x hx => by
        have h1 := hl x hx
        have h2 : x ≠ n := fun e => nb (e ▸ h1)
        simp [dep, h2, nab x h1])
    rw [ca a.ints (fun x => ints_sub a), cb b.ints (fun x => ints_sub b), ca a.lvs (fun x => lvs_sub a),
      cb b.lvs (fun x => lvs_sub b)]
    by_cases h : L < k <;> simp [dep, h] <;> omega

theorem labs_perm : ∀ t : NT, t.labs.Perm (t.ints ++ t.lvs)
  | leaf _ _ => by simp [labs, ints, lvs]
  | node n a b => by
    simp only [labs, ints, lvs, List.cons_append]
    refine List.Perm.cons _ ?_
    refine ((labs_perm a).append (labs_perm b)).trans ?_
    simp only [List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (List.perm_append_comm.trans ?_)
    simp only [List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm

theorem edge_par : ∀ (t : NT) {e : Nat × Nat}, e ∈ t.edges → e.2 ∈ t.ints
  | leaf _ _, _, h => by simp [edges] at h
  | node n a b, e, h => by
    simp only [edges, List.mem_cons, List.mem_append] at h
    simp only [ints, List.mem_cons, List.mem_append]
    rcases h with rfl | rfl | h | h
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (edge_par a h))
    · exact Or.inr (Or.inr (edge_par b h))

theorem lab_int : ∀ (t : NT), t.ints ≠ [] → t.lab ∈ t.ints
  | leaf _ _, h => by simp [ints] at h
  | node _ _ _, _ => by simp [ints, lab]

end NT

/-! ## The merge on numbered trees -/

/-- A queue entry: frequency, node number, numbered subtree. -/
structure QL where
  freq : Nat
  node : Nat
  tree : NT
  deriving Inhabited

/-- The queue entry of a leaf `(freq, node)`. -/
def leafQL (e : Nat × Nat) : QL := ⟨e.1, e.2, .leaf e.2 e.1⟩

/-- The entry without the numbers. -/
def eraseQ (q : QL) : QE := ⟨q.freq, q.node, q.tree.erase⟩

/-- `pqTake` on numbered entries. -/
def pqTakeL : List (Nat × Nat) → List QL → QL × List (Nat × Nat) × List QL
  | l :: ls, [] => (leafQL l, ls, [])
  | l :: ls, i :: is => if keyLt l (i.freq, i.node) then (leafQL l, ls, i :: is) else (i, l :: ls, is)
  | [], i :: is => (i, [], is)
  | [], [] => (⟨0, 0, .leaf 0 0⟩, [], [])

/-- The merge state: remaining leaves, FIFO, next node number. -/
abbrev MS := List (Nat × Nat) × List QL × Nat

/-- One trip of the merge loop. -/
def mstep (x : MS) : MS :=
  let a := pqTakeL x.1 x.2.1
  let b := pqTakeL a.2.1 a.2.2
  (b.2.1, b.2.2 ++ [⟨a.1.freq + b.1.freq, x.2.2, .node x.2.2 a.1.tree b.1.tree⟩], x.2.2 + 1)

/-- `k` trips. -/
noncomputable def miter : Nat → MS → MS
  | 0, x => x
  | k + 1, x => miter k (mstep x)

theorem pqTake_erase (ls : List (Nat × Nat)) (is : List QL) :
    pqTake ls (is.map eraseQ) = (eraseQ (pqTakeL ls is).1, (pqTakeL ls is).2.1, (pqTakeL ls is).2.2.map eraseQ) := by
  match ls, is with
  | l :: ls, [] => rfl
  | l :: ls, i :: is =>
    by_cases k : keyLt l (i.freq, i.node) = true <;> simp [pqTake, pqTakeL, k, eraseQ, leafQE, leafQL, NT.erase]
  | [], i :: is => rfl
  | [], [] => rfl

/-- **Forgetting the numbers gives `mergeLoop`.** -/
theorem mergeLoop_erase : ∀ (k : Nat) (ls : List (Nat × Nat)) (is : List QL) (node : Nat),
    mergeLoop k ls (is.map eraseQ) node = (miter k (ls, is, node)).2.1.map eraseQ
  | 0, _, _, _ => rfl
  | k + 1, ls, is, node => by
    simp only [mergeLoop, miter, mstep]
    rw [pqTake_erase]
    generalize pqTakeL ls is = A
    obtain ⟨a, ls1, is1⟩ := A
    simp only [pqTake_erase]
    generalize pqTakeL ls1 is1 = B
    obtain ⟨b, ls2, is2⟩ := B
    have := mergeLoop_erase k ls2 (is2 ++ [⟨a.freq + b.freq, node, .node node a.tree b.tree⟩]) (node + 1)
    simpa [eraseQ, NT.erase] using this

/-- The roots of a merge state. -/
def roots (ls : List (Nat × Nat)) (is : List QL) : List QL := ls.map leafQL ++ is

/-- One `pq_take`: a leaf from the front of `ls` or the FIFO head. -/
theorem take_cases (ls : List (Nat × Nat)) (is : List QL) (h : ls ≠ [] ∨ is ≠ []) :
    (∃ l ls', ls = l :: ls' ∧ pqTakeL ls is = (leafQL l, ls', is)) ∨
    (∃ i is', is = i :: is' ∧ pqTakeL ls is = (i, ls, is')) := by
  match ls, is, h with
  | l :: ls, [], _ => exact Or.inl ⟨l, ls, rfl, rfl⟩
  | l :: ls, i :: is, _ =>
    by_cases k : keyLt l (i.freq, i.node) = true
    · exact Or.inl ⟨l, ls, rfl, by simp [pqTakeL, k]⟩
    · exact Or.inr ⟨i, is, rfl, by simp [pqTakeL, k]⟩
  | [], i :: is, _ => exact Or.inr ⟨i, is, rfl, rfl⟩

theorem take_roots (ls : List (Nat × Nat)) (is : List QL) (h : ls ≠ [] ∨ is ≠ []) :
    (roots ls is).Perm ((pqTakeL ls is).1 :: roots (pqTakeL ls is).2.1 (pqTakeL ls is).2.2) ∧
    (∃ k, (pqTakeL ls is).2.1 = ls.drop k) ∧ (∀ q ∈ (pqTakeL ls is).2.2, q ∈ is) ∧
    ((pqTakeL ls is).1 ∈ is ∨ ∃ e ∈ ls, (pqTakeL ls is).1 = leafQL e) := by
  rcases take_cases ls is h with ⟨l, ls', rfl, e⟩ | ⟨i, is', rfl, e⟩
  · rw [e]
    exact ⟨by simp [roots], ⟨1, rfl⟩, fun q hq => hq, Or.inr ⟨l, by simp, rfl⟩⟩
  · rw [e]
    exact ⟨by simp [roots, List.perm_middle], ⟨0, rfl⟩, fun q hq => by simp [hq], Or.inl (by simp)⟩

/-- What holds after `j` trips from the sorted leaves `srt` (total frequency `S`). -/
structure Good (srt : List (Nat × Nat)) (elems S j : Nat) (x : MS) : Prop where
  node : x.2.2 = elems + j
  suffix : ∃ k, x.1 = srt.drop k
  len : (roots x.1 x.2.1).length + j = srt.length
  lab : ∀ q ∈ roots x.1 x.2.1, q.node = q.tree.lab
  qi : ∀ q ∈ x.2.1, elems ≤ q.node ∧ q.node < elems + j
  sum : ((roots x.1 x.2.1).map QL.freq).sum = S
  lv : ((roots x.1 x.2.1).flatMap (·.tree.lvs)).Perm (srt.map Prod.snd)
  it : ((roots x.1 x.2.1).flatMap (·.tree.ints)).Perm (List.range' elems j)
  ed : ∀ q ∈ roots x.1 x.2.1, ∀ e ∈ q.tree.edges, e.1 < e.2
  last : 1 ≤ j → ∃ q, x.2.1.getLast? = some q ∧ q.node = elems + j - 1

theorem leaf_lvs (srt : List (Nat × Nat)) : (srt.map leafQL).flatMap (·.tree.lvs) = srt.map Prod.snd := by
  induction srt <;> simp_all [leafQL, NT.lvs]

theorem leaf_ints (srt : List (Nat × Nat)) : (srt.map leafQL).flatMap (·.tree.ints) = [] := by
  induction srt with
  | nil => rfl
  | cons e r ih => simp only [List.map_cons, List.flatMap_cons, leafQL, NT.ints, List.nil_append]; exact ih

theorem good_zero (srt : List (Nat × Nat)) (elems : Nat) :
    Good srt elems ((srt.map Prod.fst).sum) 0 (srt, [], elems) := by
  refine ⟨rfl, ⟨0, rfl⟩, by simp [roots], fun q hq => ?_, by simp, ?_, ?_, ?_, fun q hq e he => ?_, by omega⟩
  · simp only [roots, List.append_nil, List.mem_map] at hq
    obtain ⟨e, _, rfl⟩ := hq; rfl
  · simp [roots, leafQL, List.map_map, Function.comp_def]
  · simp only [roots, List.append_nil, leaf_lvs]; exact List.Perm.refl _
  · simp only [roots, List.append_nil, leaf_ints]; exact List.Perm.refl _
  · simp only [roots, List.append_nil, List.mem_map] at hq
    obtain ⟨_, _, rfl⟩ := hq; simp [leafQL, NT.edges] at he

theorem sum_perm {l₁ l₂ : List QL} (p : l₁.Perm l₂) : (l₁.map QL.freq).sum = (l₂.map QL.freq).sum :=
  perm_sum (p.map _)

/-- The labels of the roots are distinct, below `elems + j`; the leaves' below `elems`. -/
theorem good_labs {srt : List (Nat × Nat)} {elems S j : Nat} {x : MS} (g : Good srt elems S j x)
    (nd : (srt.map Prod.snd).Nodup) (lt : ∀ e ∈ srt, e.2 < elems) :
    ((roots x.1 x.2.1).flatMap (·.tree.labs)).Nodup ∧ (∀ q ∈ roots x.1 x.2.1, ∀ y ∈ q.tree.labs, y < elems + j) := by
  have hp : ((roots x.1 x.2.1).flatMap (·.tree.labs)).Perm
      ((roots x.1 x.2.1).flatMap (·.tree.ints) ++ (roots x.1 x.2.1).flatMap (·.tree.lvs)) := by
    generalize roots x.1 x.2.1 = R
    induction R with
    | nil => simp
    | cons q R ih =>
      simp only [List.flatMap_cons]
      refine ((NT.labs_perm q.tree).append ih).trans ?_
      simp only [List.append_assoc]
      refine List.Perm.append_left _ ?_
      refine List.perm_append_comm.trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
  have hlv : ∀ y, y ∈ (roots x.1 x.2.1).flatMap (·.tree.lvs) → y < elems := fun y hy => by
    have := g.lv.mem_iff.mp hy
    simp only [List.mem_map] at this
    obtain ⟨e, he, rfl⟩ := this; exact lt e he
  have hit : ∀ y, y ∈ (roots x.1 x.2.1).flatMap (·.tree.ints) → elems ≤ y ∧ y < elems + j := fun y hy => by
    have := g.it.mem_iff.mp hy
    simp only [List.mem_range'_1] at this; exact this
  refine ⟨hp.nodup_iff.mpr ?_, fun q hq y hy => ?_⟩
  · rw [List.nodup_append]
    refine ⟨g.it.nodup_iff.mpr List.nodup_range', g.lv.nodup_iff.mpr nd, fun a ha c hc => ?_⟩
    have := hit a ha; have := hlv c hc; omega
  · have hm : y ∈ (roots x.1 x.2.1).flatMap (·.tree.labs) := List.mem_flatMap.mpr ⟨q, hq, hy⟩
    rcases List.mem_append.mp (hp.mem_iff.mp hm) with h | h
    · exact (hit y h).2
    · have := hlv y h; omega

theorem flatMap_perm {β : Type} (f : QL → List β) {l₁ l₂ : List QL} (p : l₁.Perm l₂) :
    (l₁.flatMap f).Perm (l₂.flatMap f) := List.Perm.flatMap_right f p

/-- **One trip keeps `Good`** while there are two roots. -/
theorem good_step {srt : List (Nat × Nat)} {elems S j : Nat} {x : MS} (g : Good srt elems S j x)
    (nd : (srt.map Prod.snd).Nodup) (lt : ∀ e ∈ srt, e.2 < elems) (two : 2 ≤ (roots x.1 x.2.1).length) :
    Good srt elems S (j + 1) (mstep x) := by
  obtain ⟨ls, is, node⟩ := x
  simp only at g two
  have ne1 : ls ≠ [] ∨ is ≠ [] := by
    by_cases h : ls = []
    · right; intro h'; simp [roots, h, h'] at two
    · exact Or.inl h
  obtain ⟨p1, ⟨k1, s1⟩, i1, src1⟩ := take_roots ls is ne1
  generalize ha : pqTakeL ls is = A at p1 s1 i1 src1
  obtain ⟨a, ls1, is1⟩ := A
  simp only at p1 s1 i1 src1
  have len1 := p1.length_eq
  have ne2 : ls1 ≠ [] ∨ is1 ≠ [] := by
    have : 1 ≤ (roots ls1 is1).length := by
      have h3 : (a :: roots ls1 is1).length = (roots ls1 is1).length + 1 := rfl
      omega
    by_cases h : ls1 = []
    · right; intro h'; simp [roots, h, h'] at this
    · exact Or.inl h
  obtain ⟨p2, ⟨k2, s2⟩, i2, src2⟩ := take_roots ls1 is1 ne2
  generalize hb : pqTakeL ls1 is1 = B at p2 s2 i2 src2
  obtain ⟨b, ls2, is2⟩ := B
  simp only at p2 s2 i2 src2
  have hm : mstep (ls, is, node) =
      (ls2, is2 ++ [⟨a.freq + b.freq, node, .node node a.tree b.tree⟩], node + 1) := by
    simp only [mstep, ha, hb]
  rw [hm]
  have P : (roots ls is).Perm (a :: b :: roots ls2 is2) := p1.trans (List.Perm.cons _ p2)
  have P' : (roots ls2 (is2 ++ [⟨a.freq + b.freq, node, .node node a.tree b.tree⟩])).Perm
      (⟨a.freq + b.freq, node, .node node a.tree b.tree⟩ :: roots ls2 is2) := by
    simp only [roots, ← List.append_assoc]; exact List.perm_append_comm
  have memA : a ∈ roots ls is := P.mem_iff.mpr (by simp)
  have memB : b ∈ roots ls is := P.mem_iff.mpr (by simp)
  have memR : ∀ q ∈ roots ls2 is2, q ∈ roots ls is := fun q hq => P.mem_iff.mpr (by simp [hq])
  obtain ⟨_, below⟩ := good_labs g nd lt
  have gn := g.node
  simp only at gn
  subst gn
  refine ⟨by simp only; omega, by obtain ⟨k0, s0⟩ := g.suffix; exact ⟨_, by dsimp only at s0; rw [s2, s1, s0, List.drop_drop, List.drop_drop]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P'.length_eq]; have h1 := P.length_eq; have h2 := g.len; dsimp only at h2
    simp only [List.length_cons] at h1 h2 ⊢; omega
  · intro q hq
    rcases List.mem_cons.mp (P'.mem_iff.mp hq) with rfl | hq
    · rfl
    · exact g.lab q (memR q hq)
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · have := g.qi q (i1 q (i2 q hq)); omega
    · simp only [List.mem_singleton] at hq; subst hq; simp only; omega
  · rw [sum_perm P', ← g.sum, sum_perm P]; simp only [List.map_cons, List.sum_cons]; omega
  · refine (flatMap_perm _ P').trans ?_
    refine List.Perm.trans ?_ ((flatMap_perm _ P).symm.trans g.lv)
    simp [NT.lvs, List.append_assoc]
  · refine (flatMap_perm _ P').trans ?_
    rw [List.range'_1_concat]
    refine List.Perm.trans ?_ (List.Perm.append_right _ ((flatMap_perm _ P).symm.trans g.it))
    simp only [List.flatMap_cons, NT.ints, List.cons_append, List.append_assoc]
    refine List.Perm.trans ?_ List.perm_append_comm
    exact List.perm_iff_count.mpr (fun _ => by
      simp only [List.count_append, List.count_cons, List.count_nil]; omega)
  · intro q hq e he
    rcases List.mem_cons.mp (P'.mem_iff.mp hq) with rfl | hq
    · simp only [NT.edges, List.mem_cons, List.mem_append] at he
      rcases he with rfl | rfl | he | he
      · exact below a memA _ (NT.lab_mem _)
      · exact below b memB _ (NT.lab_mem _)
      · exact g.ed a memA e he
      · exact g.ed b memB e he
    · exact g.ed q (memR q hq) e he
  · intro _; exact ⟨⟨a.freq + b.freq, elems + j, .node (elems + j) a.tree b.tree⟩, by simp, by simp only; omega⟩

theorem miter_succ : ∀ (k : Nat) (x : MS), miter (k + 1) x = mstep (miter k x)
  | 0, _ => rfl
  | k + 1, x => miter_succ k (mstep x)

theorem roots_mem {q : QL} {ls : List (Nat × Nat)} {is : List QL} (h : q ∈ roots ls is) :
    q ∈ is ∨ ∃ e ∈ ls, q = leafQL e := by
  simp only [roots, List.mem_append, List.mem_map] at h
  rcases h with ⟨e, he, rfl⟩ | h
  · exact Or.inr ⟨e, he, rfl⟩
  · exact Or.inl h

theorem good_iter (srt : List (Nat × Nat)) (elems : Nat) (nd : (srt.map Prod.snd).Nodup)
    (lt : ∀ e ∈ srt, e.2 < elems) : ∀ j, j + 1 ≤ srt.length →
    Good srt elems ((srt.map Prod.fst).sum) j (miter j (srt, [], elems))
  | 0, _ => good_zero srt elems
  | j + 1, h => by
    have g := good_iter srt elems nd lt j (by omega)
    have := g.len
    have e : ∀ (k : Nat) (x : MS), miter (k + 1) x = mstep (miter k x) := by
      intro k; induction k with
      | zero => intro x; rfl
      | succ k ih => intro x; simp only [miter] at ih ⊢; exact ih _
    rw [e]
    exact good_step g nd lt (by omega)

/-- **The end of the merge**: one FIFO entry, the last node created. -/
theorem good_final {srt : List (Nat × Nat)} {elems S : Nat} {x : MS} (two : 2 ≤ srt.length)
    (g : Good srt elems S (srt.length - 1) x) :
    x.1 = [] ∧ ∃ q, x.2.1 = [q] ∧ q.node = elems + srt.length - 2 := by
  have hl := g.len
  obtain ⟨q, hq, hn⟩ := g.last (by omega)
  simp only [roots, List.length_append, List.length_map] at hl
  have hne : x.2.1 ≠ [] := by intro h; simp [h] at hq
  have : x.2.1.length = 1 := by
    rcases hx : x.2.1 with _ | ⟨_, _⟩
    · exact absurd hx hne
    · rw [hx] at hl; simp only [List.length_cons] at hl ⊢; omega
  rcases hx : x.2.1 with _ | ⟨q', _ | _⟩
  · exact absurd hx hne
  · rw [hx] at hq; simp at hq; subst hq
    refine ⟨?_, q', rfl, by omega⟩
    rw [hx] at hl; simp only [List.length_cons, List.length_nil] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rw [hx] at this; simp at this

/-- **The tree of the merge**, from the sorted leaves `srt` (at least two, distinct nodes below `elems`). -/
theorem final_tree (srt : List (Nat × Nat)) (elems : Nat) (nd : (srt.map Prod.snd).Nodup)
    (lt : ∀ e ∈ srt, e.2 < elems) (two : 2 ≤ srt.length) :
    ∃ q, (miter (srt.length - 1) (srt, [], elems)).2.1 = [q] ∧ q.node = elems + srt.length - 2 ∧
      q.tree.lab = q.node ∧ q.tree.labs.Nodup ∧ q.tree.ints.Perm (List.range' elems (srt.length - 1)) ∧
      q.tree.lvs.Perm (srt.map Prod.snd) ∧ (∀ e ∈ q.tree.edges, e.1 < e.2) ∧
      mergeLoop (srt.length - 1) srt [] elems = [eraseQ q] := by
  have g := good_iter srt elems nd lt (srt.length - 1) (by omega)
  obtain ⟨h1, q, hq, hn⟩ := good_final two g
  obtain ⟨ndl, _⟩ := good_labs g nd lt
  have hr : roots (miter (srt.length - 1) (srt, [], elems)).1 (miter (srt.length - 1) (srt, [], elems)).2.1 = [q] := by
    rw [h1, hq]; rfl
  have lv := g.lv
  have it := g.it
  rw [hr] at ndl lv it
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at ndl lv it
  refine ⟨q, hq, hn, (g.lab q (by rw [hr]; simp)).symm, ndl, it, lv, fun e he => g.ed q (by rw [hr]; simp) e he, ?_⟩
  have := mergeLoop_erase (srt.length - 1) srt [] elems
  simp only [List.map_nil] at this
  rw [this, hq]; rfl

