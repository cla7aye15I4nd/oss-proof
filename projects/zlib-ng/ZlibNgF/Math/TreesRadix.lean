import ZlibNgF.Math.HuffBuilt

/-!
# Counting-sort ranks (heap-free)

`pq_radix_pass` (`trees.c:137-144`) is a stable counting sort: entry `j` of `src[0 .. n)` lands at
`krank n g j`, the number of entries whose digit `g` is smaller, or equal with a smaller index. This file proves
that `krank` is a bijection of `[0, n)` that respects the order (digit, index), that two passes (low digit, then
high digit) place entry `j` at its rank by (high, low, index), and relates the rank to the model's `sortKeys`.
-/

set_option autoImplicit false

namespace ZlibNgF.Math.TreesRadix
open ZlibNgF.Math.Huff

/-- The order of a counting sort: digit, then index. -/
def kLt (g : Nat → Nat) (l j : Nat) : Bool := decide (g l < g j ∨ (g l = g j ∧ l < j))

/-- Where a stable counting sort by digit `g` puts entry `j` of `n`. -/
def krank (n : Nat) (g : Nat → Nat) (j : Nat) : Nat := (List.range n).countP (fun l => kLt g l j)

theorem countP_le_of {p q : Nat → Bool} : ∀ (xs : List Nat), (∀ x ∈ xs, p x → q x) → xs.countP p ≤ xs.countP q
  | [], _ => by simp
  | x :: xs, h => by
    rw [List.countP_cons, List.countP_cons]
    have ih := countP_le_of xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self ..)
    by_cases hp : p x = true
    · simp [hp, hx hp]; omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]; split <;> omega

theorem countP_lt_of {p q : Nat → Bool} : ∀ (xs : List Nat), (∀ x ∈ xs, p x → q x) → ∀ y ∈ xs, q y → p y = false →
    xs.countP p < xs.countP q
  | [], _, y, hy, _, _ => by simp at hy
  | x :: xs, h, y, hy, hq, hp => by
    rw [List.countP_cons, List.countP_cons]
    have hle := countP_le_of xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hx := h x (List.mem_cons_self ..)
    rcases List.mem_cons.mp hy with e | e
    · subst e; simp [hq, hp]; omega
    · have ih := countP_lt_of xs (fun z hz => h z (List.mem_cons_of_mem _ hz)) y e hq hp
      by_cases hpx : p x = true
      · simp [hpx, hx hpx]; omega
      · simp only [hpx, Bool.false_eq_true, ↓reduceIte]; split <;> omega

theorem krank_lt {n : Nat} (g : Nat → Nat) {j : Nat} (hj : j < n) : krank n g j < n := by
  have := countP_lt_of (p := fun l => kLt g l j) (q := fun _ => true) (List.range n) (fun _ _ _ => rfl) j
    (List.mem_range.mpr hj) rfl (by simp [kLt])
  simpa [krank] using this

/-- `krank` respects the order (digit, index). -/
theorem krank_strict {n : Nat} (g : Nat → Nat) {l j : Nat} (hl : l < n) (h : kLt g l j = true) :
    krank n g l < krank n g j := by
  unfold krank
  refine countP_lt_of (List.range n) (fun x _ hx => ?_) l (List.mem_range.mpr hl) h (by simp [kLt])
  simp only [kLt, decide_eq_true_eq] at hx h ⊢; omega

theorem kLt_total (g : Nat → Nat) {l j : Nat} (h : l ≠ j) : kLt g l j = true ∨ kLt g j l = true := by
  simp only [kLt, decide_eq_true_eq]; omega

/-- `krank l < krank j` exactly when `(g l, l) < (g j, j)`. -/
theorem krank_lt_iff {n : Nat} (g : Nat → Nat) {l j : Nat} (hl : l < n) (hj : j < n) :
    krank n g l < krank n g j ↔ kLt g l j = true := by
  refine ⟨fun hlt => ?_, krank_strict g hl⟩
  by_cases e : l = j
  · subst e; omega
  · rcases kLt_total g e with h | h
    · exact h
    · have := krank_strict (n := n) g hj h; omega

theorem krank_inj {n : Nat} (g : Nat → Nat) {l j : Nat} (hl : l < n) (hj : j < n) (e : krank n g l = krank n g j) :
    l = j := by
  refine Classical.byContradiction fun ne => ?_
  rcases kLt_total g ne with h | h
  · have := krank_strict (n := n) g hl h; omega
  · have := krank_strict (n := n) g hj h; omega

/-- A list without duplicates of numbers below `m` has at most `m` entries. -/
theorem nodup_len_le : ∀ (m : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < m) → l.length ≤ m
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, h => absurd (h x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | m + 1, l, nd, h => by
    have nd' := nd.erase m
    have ih := nodup_len_le m (l.erase m) nd' (fun x hx => by
      have ⟨ne, hm⟩ := (List.Nodup.mem_erase_iff nd).mp hx
      have := h x hm; omega)
    rw [List.length_erase] at ih
    split at ih <;> omega

theorem nodup_map_of (n : Nat) (f : Nat → Nat) (inj : ∀ l j, l < n → j < n → f l = f j → l = j) :
    ((List.range n).map f).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  exact List.Pairwise.imp_of_mem (fun {a b} ha hb ne e => ne (inj a b (List.mem_range.mp ha) (List.mem_range.mp hb) e))
    List.nodup_range

/-- An injection of `[0, n)` into itself is onto. -/
theorem inj_onto (n : Nat) (f : Nat → Nat) (hf : ∀ j, j < n → f j < n)
    (inj : ∀ l j, l < n → j < n → f l = f j → l = j) : ∀ p, p < n → ∃ j, j < n ∧ f j = p := by
  intro p hp
  refine Classical.byContradiction fun hno => ?_
  have nd := nodup_map_of n f inj
  have nd2 : (p :: (List.range n).map f).Nodup := List.nodup_cons.mpr ⟨fun hm => by
    obtain ⟨j, hj, e⟩ := List.mem_map.mp hm
    exact hno ⟨j, List.mem_range.mp hj, e⟩, nd⟩
  have := nodup_len_le n _ nd2 (fun x hx => by
    rcases List.mem_cons.mp hx with e | hx
    · omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx; exact hf j (List.mem_range.mp hj))
  simp at this; omega

theorem krank_onto (n : Nat) (g : Nat → Nat) : ∀ p, p < n → ∃ j, j < n ∧ krank n g j = p :=
  inj_onto n (krank n g) (fun _ h => krank_lt g h) (fun _ _ hl hj e => krank_inj g hl hj e)

/-- Counting over `[0, n)` through a bijection of `[0, n)`. -/
theorem countP_reindex (n : Nat) (f : Nat → Nat) (hf : ∀ j, j < n → f j < n)
    (inj : ∀ l j, l < n → j < n → f l = f j → l = j) (P : Nat → Bool) :
    (List.range n).countP P = (List.range n).countP (fun l => P (f l)) := by
  have perm : ((List.range n).map f).Perm (List.range n) := by
    refine (List.perm_ext_iff_of_nodup (nodup_map_of n f inj) List.nodup_range).mpr fun a => ?_
    constructor
    · intro hm
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
      exact List.mem_range.mpr (hf j (List.mem_range.mp hj))
    · intro hm
      obtain ⟨j, hj, e⟩ := inj_onto n f hf inj a (List.mem_range.mp hm)
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, e⟩
  rw [← perm.countP_eq, List.countP_map]
  rfl

/-- **Two passes.** If `R1` is the result of the first pass (`R1 (krank n g1 j) = L j`), the second pass by `g2` puts
entry `j` of `L` at its rank by (`g2`, `g1`, index). -/
theorem two_pass {α : Type} (n : Nat) (L R1 : Nat → α) (g1 g2 : α → Nat)
    (hR : ∀ j, j < n → R1 (krank n (fun l => g1 (L l)) j) = L j) (j : Nat) (hj : j < n) :
    krank n (fun q => g2 (R1 q)) (krank n (fun l => g1 (L l)) j) =
      (List.range n).countP (fun l => decide (g2 (L l) < g2 (L j) ∨
        (g2 (L l) = g2 (L j) ∧ (g1 (L l) < g1 (L j) ∨ (g1 (L l) = g1 (L j) ∧ l < j))))) := by
  have hRj := hR j hj
  have keyj : ∀ l, l < n → (krank n (fun l => g1 (L l)) l < krank n (fun l => g1 (L l)) j ↔
      kLt (fun l => g1 (L l)) l j = true) := fun l hl => krank_lt_iff _ hl hj
  generalize krank n (fun l => g1 (L l)) j = p at hRj keyj
  unfold krank
  rw [countP_reindex n (krank n (fun l => g1 (L l))) (fun _ h => krank_lt _ h)
    (fun _ _ hl hj e => krank_inj _ hl hj e)]
  apply List.countP_congr
  intro l hl
  have hl' := List.mem_range.mp hl
  have key := keyj l hl'
  simp only [kLt, decide_eq_true_eq] at key ⊢
  rw [hR l hl', hRj]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, key.mp h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, key.mpr h2⟩

/-! ## The ranks and `sortKeys` -/

theorem keyLt_iff (a b : Nat × Nat) : keyLt a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  simp [keyLt]

theorem keyLt_trans {a b c : Nat × Nat} (h1 : keyLt a b = true) (h2 : keyLt b c = true) : keyLt a c = true := by
  rw [keyLt_iff] at *; omega

theorem keyLt_asymm {a b : Nat × Nat} (h1 : keyLt a b = true) : keyLt b a = false := by
  rw [keyLt_iff] at h1
  cases h : keyLt b a
  · rfl
  · rw [keyLt_iff] at h; omega

theorem keyLt_total {a b : Nat × Nat} (ne : a ≠ b) (h : keyLt a b = false) : keyLt b a = true := by
  rw [keyLt_iff]
  have h' : ¬ (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) := fun c => by rw [← keyLt_iff] at c; simp [c] at h
  have : a.1 ≠ b.1 ∨ a.2 ≠ b.2 := by
    refine Classical.byContradiction fun c => ne ?_
    have e1 : a.1 = b.1 := Classical.byContradiction fun x => c (Or.inl x)
    have e2 : a.2 = b.2 := Classical.byContradiction fun x => c (Or.inr x)
    exact Prod.ext e1 e2
  omega

theorem insKey_pw (e : Nat × Nat) : ∀ l : List (Nat × Nat), l.Pairwise (fun a b => keyLt a b = true) →
    (∀ x ∈ l, x ≠ e) → (insKey e l).Pairwise (fun a b => keyLt a b = true)
  | [], _, _ => by simp [insKey]
  | x :: xs, pw, ne => by
    simp only [insKey]
    have ⟨hx, pxs⟩ := List.pairwise_cons.mp pw
    split
    · rename_i h
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_, pw⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h
      · exact keyLt_trans h (hx y hy)
    · rename_i h
      have h' : keyLt e x = false := by simpa using h
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_,
        insKey_pw e xs pxs (fun y hy => ne y (List.mem_cons_of_mem _ hy))⟩
      rcases List.mem_cons.mp ((insKey_perm e xs).mem_iff.mp hy) with rfl | hy
      · exact keyLt_total (fun c => ne x (List.mem_cons_self ..) c.symm) h'
      · exact hx y hy

theorem sortKeys_pw : ∀ l : List (Nat × Nat), l.Nodup → (sortKeys l).Pairwise (fun a b => keyLt a b = true)
  | [], _ => by simp [sortKeys]
  | x :: xs, nd => by
    simp only [sortKeys]
    have ⟨nx, nxs⟩ := List.nodup_cons.mp nd
    exact insKey_pw x _ (sortKeys_pw xs nxs)
      (fun y hy e => nx (e ▸ (sortKeys_perm xs).mem_iff.mp hy))

/-- In a strictly sorted list, the entry at `p` has exactly `p` entries below it. -/
theorem pos_count : ∀ (S : List (Nat × Nat)), S.Pairwise (fun a b => keyLt a b = true) →
    ∀ p (hp : p < S.length), S.countP (fun x => keyLt x S[p]) = p
  | [], _, p, hp => by simp at hp
  | a :: rest, pw, p, hp => by
    have ⟨ha, prest⟩ := List.pairwise_cons.mp pw
    rw [List.countP_cons]
    match p, hp with
    | 0, _ =>
      simp only [List.getElem_cons_zero]
      have : rest.countP (fun x => keyLt x a) = 0 :=
        List.countP_eq_zero.mpr fun x hx => by simp [keyLt_asymm (ha x hx)]
      rw [this]
      have : keyLt a a = false := by simp [keyLt]
      simp [this]
    | q + 1, hq =>
      simp only [List.getElem_cons_succ]
      have hq' : q < rest.length := by simpa using hq
      rw [pos_count rest prest q hq']
      have : keyLt a rest[q] = true := ha _ (List.getElem_mem hq')
      simp [this]

theorem countP_idx {α : Type} [Inhabited α] (p : α → Bool) (L : List α) :
    L.countP p = (List.range L.length).countP (fun l => p L[l]!) := by
  have e : (List.range L.length).map (fun l => L[l]!) = L := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp at h1 ⊢
    simp [h1]
  calc L.countP p = ((List.range L.length).map (fun l => L[l]!)).countP p := by rw [e]
    _ = _ := by rw [List.countP_map]; rfl

/-- **The rank in `sortKeys`.** For leaves with strictly increasing nodes, entry `j` is at position
`krank n freq j` of `sortKeys`. -/
theorem sortKeys_at (Ls : List (Nat × Nat)) (inc : Ls.Pairwise (fun a b => a.2 < b.2)) (j : Nat)
    (hj : j < Ls.length) :
    (sortKeys Ls)[krank Ls.length (fun l => (Ls[l]!).1) j]! = Ls[j]! ∧
      krank Ls.length (fun l => (Ls[l]!).1) j < (sortKeys Ls).length := by
  have nd : Ls.Nodup := inc.imp (fun h e => by rw [e] at h; omega)
  have perm := sortKeys_perm Ls
  have pw := sortKeys_pw Ls nd
  have mem : Ls[j]! ∈ sortKeys Ls := perm.mem_iff.mpr (by simp [hj])
  obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp mem
  have cnt := pos_count _ pw p hp
  rw [hpe, perm.countP_eq, countP_idx] at cnt
  have idx : ∀ l, l < Ls.length → l < j → (Ls[l]!).2 < (Ls[j]!).2 := by
    intro l hl hlj
    have := List.pairwise_iff_getElem.mp inc l j hl hj hlj
    simpa [hl, hj] using this
  have idx2 : ∀ l, l < Ls.length → j < l → (Ls[j]!).2 < (Ls[l]!).2 := by
    intro l hl hlj
    have := List.pairwise_iff_getElem.mp inc j l hj hl hlj
    simpa [hl, hj] using this
  have kr : krank Ls.length (fun l => (Ls[l]!).1) j = p := by
    rw [← cnt]
    unfold krank
    apply List.countP_congr
    intro l hl
    have hl' := List.mem_range.mp hl
    simp only [kLt, decide_eq_true_eq, keyLt_iff]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, idx l hl' h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_⟩
        refine Classical.byContradiction fun c => ?_
        rcases Nat.lt_or_ge j l with h3 | h3
        · have := idx2 l hl' h3; omega
        · have : l = j := by omega
          subst this; omega
  rw [kr]
  refine ⟨?_, hp⟩
  simp [hp, hpe]

theorem scan_lt (f : Nat → Nat) : ∀ n, ∀ e ∈ scanLeaves f n, e.2 < n
  | 0, e, he => by simp [scanLeaves] at he
  | n + 1, e, he => by
    simp only [scanLeaves] at he
    rcases List.mem_append.mp he with h | h
    · have := scan_lt f n e h; omega
    · split at h
      · simp at h; subst h; simp
      · simp at h

/-- The leaf scan lists the nodes in increasing order. -/
theorem scan_inc (f : Nat → Nat) : ∀ n, (scanLeaves f n).Pairwise (fun a b => a.2 < b.2)
  | 0 => by simp [scanLeaves]
  | n + 1 => by
    simp only [scanLeaves]
    refine List.pairwise_append.mpr ⟨scan_inc f n, ?_, ?_⟩
    · split <;> simp
    · intro a ha b hb
      have := scan_lt f n a ha
      split at hb
      · simp at hb; subst hb; simp; omega
      · simp at hb

/-- The order of the two passes (high byte, low byte, index) is the order (frequency, index). -/
theorem digits_iff (f g l j : Nat) :
    (g / 256 < f / 256 ∨ (g / 256 = f / 256 ∧ (g % 256 < f % 256 ∨ (g % 256 = f % 256 ∧ l < j)))) ↔
      (g < f ∨ (g = f ∧ l < j)) := by
  omega

/-! ## Counting facts for the loops of `pq_radix_pass` -/

theorem countP_range_succ (p : Nat → Bool) (i : Nat) :
    (List.range (i + 1)).countP p = (List.range i).countP p + (if p i then 1 else 0) := by
  rw [List.range_succ, List.countP_append]; simp

theorem cnt_split (g : Nat → Nat) (c : Nat) : ∀ xs : List Nat,
    xs.countP (fun l => decide (g l < c + 1)) =
      xs.countP (fun l => decide (g l < c)) + xs.countP (fun l => decide (g l = c))
  | [] => rfl
  | x :: xs => by
    simp only [List.countP_cons, cnt_split g c xs]
    by_cases h1 : g x < c
    · simp [h1, show g x < c + 1 by omega, show g x ≠ c by omega]; omega
    · by_cases h2 : g x = c
      · simp [h2]; omega
      · simp [h1, h2, show ¬ g x < c + 1 by omega]

theorem cnt_and_lt (B : Nat → Bool) (i : Nat) : ∀ N, i ≤ N →
    (List.range N).countP (fun l => B l && decide (l < i)) = (List.range i).countP B := by
  intro N hN
  induction N with
  | zero =>
    have : i = 0 := by omega
    subst this; rfl
  | succ N ih =>
    by_cases e : i = N + 1
    · subst e
      apply List.countP_congr
      intro l hl; simp [List.mem_range.mp hl]
    · rw [countP_range_succ, ih (by omega)]
      simp [show ¬ N < i by omega]

theorem cnt_or (A B : Nat → Bool) (dis : ∀ l, A l = true → B l = false) : ∀ xs : List Nat,
    xs.countP (fun l => A l || B l) = xs.countP A + xs.countP B
  | [] => rfl
  | x :: xs => by
    simp only [List.countP_cons, cnt_or A B dis xs]
    cases hA : A x <;> cases hB : B x <;> simp_all <;> omega

/-- `krank` is the count of smaller digits plus the count of equal digits at smaller indices. -/
theorem krank_split (N : Nat) (g : Nat → Nat) (i : Nat) (hi : i ≤ N) :
    krank N g i = (List.range N).countP (fun l => decide (g l < g i)) +
      (List.range i).countP (fun l => decide (g l = g i)) := by
  unfold krank
  rw [← cnt_and_lt (fun l => decide (g l = g i)) i N hi, ← cnt_or]
  · apply List.countP_congr; intro l _; simp [kLt]
  · intro l h; simp at h ⊢; omega

/-! ## The forced leaves -/

theorem scan_nil_mc (f : Nat → Nat) : ∀ n, scanLeaves f n = [] → maxCode1 f n = 0
  | 0, _ => rfl
  | n + 1, h => by
    simp only [scanLeaves] at h
    have h1 := List.append_eq_nil_iff.mp h
    simp only [maxCode1]
    split at h1
    · simp at h1
    · rename_i hf; simp only [hf, ↓reduceIte]; exact scan_nil_mc f n h1.1

theorem scan_last_mc (f : Nat → Nat) : ∀ n (L : List (Nat × Nat)) (e : Nat × Nat), scanLeaves f n = L ++ [e] →
    maxCode1 f n = e.2 + 1
  | 0, L, e, h => by simp [scanLeaves] at h
  | n + 1, L, e, h => by
    simp only [scanLeaves] at h
    simp only [maxCode1]
    split at h
    · rename_i hf
      rw [ite_eq_left_of_eq_true _ _ (eq_true hf)]
      have := (List.append_inj' h rfl).2
      simp at this; rw [← this]
    · rename_i hf
      simp only [hf, ↓reduceIte, List.append_nil] at h ⊢
      exact scan_last_mc f n L e h

/-- The leaves after the forcing loop have distinct nodes, below `max(elems, 3)`, and every scanned frequency. -/
theorem forced_props (f : Nat → Nat) (n : Nat) :
    (forced (scanLeaves f n) (maxCode1 f n)).1.Pairwise (fun a b => a.2 ≠ b.2) ∧
    (∀ e ∈ (forced (scanLeaves f n) (maxCode1 f n)).1, e.2 < max n 3 ∧ (e.1 = 1 ∨ e.1 = f e.2)) ∧
    2 ≤ (forced (scanLeaves f n) (maxCode1 f n)).1.length := by
  have inc := scan_inc f n
  have lt := scan_lt f n
  generalize hL : scanLeaves f n = L at inc lt
  have mem : ∀ e ∈ L, e.1 = f e.2 := by
    intro e he; rw [← hL] at he
    clear hL inc lt
    induction n with
    | zero => simp [scanLeaves] at he
    | succ n ih =>
      simp only [scanLeaves] at he
      rcases List.mem_append.mp he with h | h
      · exact ih h
      · split at h <;> simp at h; subst h; rfl
  match L, hL with
  | [], hL =>
    have := scan_nil_mc f n hL
    rw [this]
    simp [forced, forceNode, forceNext]
    omega
  | [l], hL =>
    have hm := scan_last_mc f n [] l (by simpa using hL)
    have hl := lt l (by simp)
    rw [hm]
    simp only [forced, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.length_cons, List.length_nil]
    unfold forceNode
    refine ⟨⟨by split <;> omega, by simp⟩, ⟨⟨by omega, Or.inr (mem l (by simp))⟩, ⟨by split <;> omega, by simp⟩⟩, by omega⟩
  | a :: c :: rest, _ =>
    simp only [forced]
    refine ⟨inc.imp (fun h => Nat.ne_of_lt h), fun e he => ⟨by have := lt e he; omega, Or.inr (mem e he)⟩, by simp⟩

end ZlibNgF.Math.TreesRadix
