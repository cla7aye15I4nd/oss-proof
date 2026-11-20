import ZlibNgF.Math.OverlayHeader
import ZlibNgF.Math.HuffBuilt

/-!
# Counting facts of the tree header model (heap-free)

The token list of `scanTokens` (the loop of `scan_tree` / `send_tree`) has at most one token per code length it
covers, so `scan_tree`'s `bl_tree` frequencies stay far below `2^16`.
-/

namespace ZlibNgF.Math.Huff
set_option autoImplicit false

theorem groupTokens_length (prevlen : Int) (count minc curlen : Nat) (h1 : 1 ≤ count) (hm : 3 ≤ minc) :
    (groupTokens prevlen count minc curlen).length ≤ count := by
  unfold groupTokens
  split
  · simp
  · split
    · split <;> simp <;> omega
    · split <;> simp <;> omega

theorem scanTokens_length (len : Nat → Nat) (m : Nat) :
    ∀ k n (prevlen : Int) (count maxc minc nextlen : Nat), 3 ≤ minc →
      (scanTokens len m k n prevlen count maxc minc nextlen).length ≤ count + k
  | 0, _, _, _, _, _, _, _ => by simp [scanTokens]
  | k + 1, n, prevlen, count, maxc, minc, nextlen, hm => by
    simp only [scanTokens]
    split
    · have := scanTokens_length len m k (n + 1) prevlen (count + 1) maxc minc (nextLen len m n) hm
      omega
    · rw [List.length_append]
      have g := groupTokens_length prevlen (count + 1) minc nextlen (by omega) hm
      have r := scanTokens_length len m k (n + 1) nextlen 0
        (if nextLen len m n = 0 then 138 else if nextlen = nextLen len m n then 6 else 7)
        (if nextLen len m n = 0 then 3 else if nextlen = nextLen len m n then 3 else 4) (nextLen len m n)
        (by split <;> (try split) <;> omega)
      omega

theorem treeTokens_length (len : Nat → Nat) (m : Nat) : (treeTokens len m).length ≤ m := by
  have := scanTokens_length len m m 0 (-1) 0 (if len 0 = 0 then 138 else 7) (if len 0 = 0 then 3 else 4) (len 0)
    (by split <;> omega)
  unfold treeTokens; omega

theorem groupTokens_lt (prevlen : Int) (count minc curlen : Nat) (hc : curlen ≤ 15) :
    ∀ x ∈ groupTokens prevlen count minc curlen, x < 19 := by
  intro x hx
  unfold groupTokens at hx
  split at hx
  · rw [List.mem_replicate] at hx; omega
  · split at hx
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at hx
      split at hx <;> simp at hx <;> omega
    · split at hx <;> simp at hx <;> omega

theorem scanTokens_lt (len : Nat → Nat) (m : Nat) (hl : ∀ n, n < m → len n ≤ 15) :
    ∀ k n (prevlen : Int) (count maxc minc nextlen : Nat), n + k = m → (1 ≤ k → nextlen ≤ 15) →
      ∀ x ∈ scanTokens len m k n prevlen count maxc minc nextlen, x < 19
  | 0, _, _, _, _, _, _, _, _ => by simp [scanTokens]
  | k + 1, n, prevlen, count, maxc, minc, nextlen, hk, hn => by
    have nl : 1 ≤ k → nextLen len m n ≤ 15 := fun h => by
      unfold nextLen; simp only [show n + 1 < m by omega, ↓reduceIte]; exact hl _ (by omega)
    simp only [scanTokens]
    split
    · exact scanTokens_lt len m hl k (n + 1) prevlen (count + 1) maxc minc (nextLen len m n) (by omega) nl
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact groupTokens_lt prevlen (count + 1) minc nextlen (hn (by omega)) x hx
      · exact scanTokens_lt len m hl k (n + 1) nextlen 0 _ _ (nextLen len m n) (by omega) nl x hx

theorem treeTokens_lt (len : Nat → Nat) (m : Nat) (hl : ∀ n, n < m → len n ≤ 15) :
    ∀ x ∈ treeTokens len m, x < 19 :=
  scanTokens_lt len m hl m 0 (-1) 0 _ _ (len 0) (by omega) (fun h => hl 0 (by omega))

open ZlibNgF.Math.HuffSymbols (mass mass_add mass_single mass_zero mass_congr)

theorem itT {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : ite c a b = a := by simp [h]
theorem itF {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : ite c a b = b := by simp [h]

theorem count_cons_eq (x c : Nat) (l : List Nat) : (x :: l).count c = l.count c + if c = x then 1 else 0 := by
  rw [List.count_cons]; by_cases h : c = x
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The frequencies of a list of symbols below `n` add up to at most its length. -/
theorem mass_count_le (n : Nat) : ∀ l : List Nat, mass (fun c => l.count c) n ≤ l.length
  | [] => by simp [mass_zero]
  | x :: l => by
    have ih := mass_count_le n l
    have e : (fun c => (x :: l).count c) = fun c => l.count c + if c = x then 1 else 0 := by
      funext c; exact count_cons_eq x c l
    rw [e, mass_add, mass_single]
    simp only [List.length_cons]
    split <;> omega

/-- Weighted frequencies: `Σ_{c < n} count(c) * g(c)` is the sum of `g` over a list of symbols below `n`. -/
theorem mass_count_mul (g : Nat → Nat) (n : Nat) : ∀ l : List Nat, (∀ x ∈ l, x < n) →
    mass (fun c => l.count c * g c) n = (l.map g).sum
  | [], _ => by simp [mass_zero]
  | x :: l, h => by
    have ih := mass_count_mul g n l (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    have e : (fun c => (x :: l).count c * g c) = fun c => l.count c * g c + (if c = x then 1 else 0) * g c := by
      funext c; rw [count_cons_eq, Nat.add_mul]
    rw [e, mass_add, ih]
    have e2 : (fun c => (if c = x then 1 else 0) * g c) = fun c => if c = x then g x else 0 := by
      funext c; split <;> simp_all
    rw [e2]
    have e3 : ∀ m, mass (fun c => if c = x then g x else 0) m = if x < m then g x else 0 := by
      intro m
      induction m with
      | zero => simp [mass]
      | succ m ihm =>
        simp only [mass, ihm]
        by_cases eq : m = x
        · subst eq; simp
        · by_cases lt : x < m
          · simp [lt, eq, show x < m + 1 by omega]
          · simp [lt, eq, show ¬ x < m + 1 by omega]
    rw [e3, itT hx]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem scanLeaves_congr (f g : Nat → Nat) : ∀ n, (∀ k, k < n → f k = g k) → scanLeaves f n = scanLeaves g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [scanLeaves, scanLeaves_congr f g n (fun k hk => h k (by omega)), h n (by omega)]

theorem maxCode1_congr (f g : Nat → Nat) : ∀ n, (∀ k, k < n → f k = g k) → maxCode1 f n = maxCode1 g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [maxCode1, maxCode1_congr f g n (fun k hk => h k (by omega)), h n (by omega)]

theorem buildTree_congr (e : Nat) (f g : Nat → Nat) (h : ∀ k, k < e → f k = g k) : buildTree e f = buildTree e g := by
  unfold buildTree; rw [scanLeaves_congr f g e h, maxCode1_congr f g e h]

theorem treeLengths_congr (e L : Nat) (f g : Nat → Nat) (h : ∀ k, k < e → f k = g k) :
    treeLengths e L f = treeLengths e L g := by
  unfold treeLengths; rw [buildTree_congr e f g h]

/-- `max_blindex` as the C loop computes it from index `k` down: 2 when no length at `bl_order[3 .. k]` is
nonzero (the model `blMaxIndex` stops at 3). -/
noncomputable def blMaxC (blLen : Nat → Nat) : Nat → Nat
  | 0 => 2
  | k + 1 => if k + 1 < 3 then 2 else if blLen (blOrder.getD (k + 1) 0) ≠ 0 then k + 1 else blMaxC blLen k

theorem blMaxC_le (blLen : Nat → Nat) : ∀ k, 2 ≤ blMaxC blLen k ∧ blMaxC blLen k ≤ max k 2
  | 0 => by simp [blMaxC]
  | k + 1 => by
    have := blMaxC_le blLen k
    simp only [blMaxC]; split
    · omega
    · split <;> omega

theorem blMaxC_eq (blLen : Nat → Nat) : ∀ k, (∃ j, 3 ≤ j ∧ j ≤ k ∧ blLen (blOrder.getD j 0) ≠ 0) →
    blMaxC blLen k = blMaxIndex blLen k
  | 0, ⟨j, h1, h2, _⟩ => by omega
  | k + 1, ⟨j, h1, h2, h3⟩ => by
    simp only [blMaxC, blMaxIndex]
    by_cases a : k + 1 ≤ 3
    · obtain rfl : j = k + 1 := by omega
      rw [itF (by omega), itT h3, itT a]; omega
    · rw [itF (by omega), itF a]
      split
      · rfl
      · rename_i hz
        have hj : j ≤ k := by
          rcases Nat.lt_or_ge j (k + 1) with h | h
          · omega
          · obtain rfl : j = k + 1 := by omega
            exact absurd h3 hz
        exact blMaxC_eq blLen k ⟨j, h1, hj, h3⟩

theorem blOrder_lt (j : Nat) : blOrder.getD j 0 < 19 := by
  by_cases h : j < 19
  · have : ∀ k : Fin 19, blOrder.getD k.val 0 < 19 := by decide
    exact this ⟨j, h⟩
  · have hl : blOrder.length = 19 := rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide

theorem blMaxC_congr (f g : Nat → Nat) (h : ∀ k, k < 19 → f k = g k) : ∀ j, blMaxC f j = blMaxC g j
  | 0 => rfl
  | j + 1 => by simp only [blMaxC, h _ (blOrder_lt _), blMaxC_congr f g h j]

end ZlibNgF.Math.Huff
