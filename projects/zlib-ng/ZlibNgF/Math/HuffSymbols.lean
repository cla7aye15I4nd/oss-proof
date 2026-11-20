noncomputable section

/-! # Block symbols, frequency histograms and weighted sums (heap-free)

Re-proved from the sibling `zlib` project (`ZlibNgF.Math.HuffSymbols`, `DeflateSymbolMass`,
`DeflateWeightedMass`). A symbol with distance 0 is a literal (`value` = the byte), otherwise a match
(`value` = length - 3, `distance` = the match distance). -/

/-! # Symbols, frequencies and the bytes represented by a deflate block -/

namespace ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

/-- Distance zero denotes a literal. A match stores its length minus three. -/
structure Symbol where
  distance : Nat
  value : Nat
  deriving DecidableEq

def Symbol.Valid (s : Symbol) : Prop := s.distance ≤ 32768 ∧ s.value < 256

def Symbol.bytes (s : Symbol) : Nat := if s.distance = 0 then 1 else s.value + 3

def Symbol.literalKey (lengthCode : Nat → Nat) (s : Symbol) : Nat :=
  if s.distance = 0 then s.value else lengthCode s.value + 257

def Symbol.distanceKey (distanceCode : Nat → Nat) (s : Symbol) : Option Nat :=
  if s.distance = 0 then none else some (distanceCode (s.distance - 1))

noncomputable def represented : List Symbol → Nat
  | [] => 0
  | s :: rest => s.bytes + represented rest

noncomputable def countKey {α : Type} (key : α → Option Nat) : List α → Nat → Nat
  | [], _ => 0
  | s :: rest, k => (if key s = some k then 1 else 0) + countKey key rest k

def literalFrequency (lengthCode : Nat → Nat) (symbols : List Symbol) (k : Nat) : Nat :=
  (if k = 256 then 1 else 0) + countKey (fun s => some (s.literalKey lengthCode)) symbols k

def distanceFrequency (distanceCode : Nat → Nat) (symbols : List Symbol) (k : Nat) : Nat :=
  countKey (Symbol.distanceKey distanceCode) symbols k

theorem represented_append (xs ys : List Symbol) :
    represented (xs ++ ys) = represented xs + represented ys := by
  induction xs with
  | nil => simp [represented]
  | cons s xs ih => simp [represented, ih, Nat.add_assoc]

theorem represented_snoc (xs : List Symbol) (s : Symbol) :
    represented (xs ++ [s]) = represented xs + s.bytes := by
  simp [represented_append, represented]

theorem symbol_bytes_le {s : Symbol} (valid : s.Valid) : s.bytes ≤ 258 := by
  unfold Symbol.bytes
  split <;> have := valid.2 <;> omega

/-- The bound depends on the number of stored symbols, not on a caller's
claim about the signed block position. -/
theorem represented_le {xs : List Symbol} (valid : ∀ s ∈ xs, s.Valid) :
    represented xs ≤ 258 * xs.length := by
  induction xs with
  | nil => simp [represented]
  | cons s xs ih =>
    have first := symbol_bytes_le (valid s (by simp))
    have rest := ih (fun t member => valid t (by simp [member]))
    simp only [represented, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem countKey_append {α : Type} (key : α → Option Nat) (xs ys : List α) (k : Nat) :
    countKey key (xs ++ ys) k = countKey key xs k + countKey key ys k := by
  induction xs with
  | nil => simp [countKey]
  | cons s xs ih => simp [countKey, ih, Nat.add_assoc]

theorem countKey_le {α : Type} (key : α → Option Nat) (xs : List α) (k : Nat) :
    countKey key xs k ≤ xs.length := by
  induction xs with
  | nil => simp [countKey]
  | cons s xs ih => simp only [countKey, List.length_cons]; split <;> omega

theorem literal_frequency_snoc (lc : Nat → Nat) (xs : List Symbol) (s : Symbol) (k : Nat) :
    literalFrequency lc (xs ++ [s]) k =
      literalFrequency lc xs k + if s.literalKey lc = k then 1 else 0 := by
  simp [literalFrequency, countKey_append, countKey, Nat.add_assoc]

theorem distance_frequency_snoc (dc : Nat → Nat) (xs : List Symbol) (s : Symbol) (k : Nat) :
    distanceFrequency dc (xs ++ [s]) k =
      distanceFrequency dc xs k + if s.distanceKey dc = some k then 1 else 0 := by
  simp [distanceFrequency, countKey_append, countKey]

theorem literal_frequency_le (lc : Nat → Nat) (xs : List Symbol) (k : Nat) :
    literalFrequency lc xs k ≤ xs.length + 1 := by
  have bound := countKey_le (fun s => some (s.literalKey lc)) xs k
  unfold literalFrequency
  split <;> omega

theorem distance_frequency_le (dc : Nat → Nat) (xs : List Symbol) (k : Nat) :
    distanceFrequency dc xs k ≤ xs.length := countKey_le _ _ _

end ZlibNgF.Math.HuffSymbols

/-! # The total weight of a symbol histogram -/

namespace ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

noncomputable def mass (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mass f n + f n

theorem mass_congr {f g : Nat → Nat} {n : Nat} (agree : ∀ k, k < n → f k = g k) :
    mass f n = mass g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mass, ih (fun k bound => agree k (by omega)), agree n (by omega)]

theorem mass_zero (n : Nat) : mass (fun _ => 0) n = 0 := by
  induction n <;> simp_all [mass]

theorem mass_add (f g : Nat → Nat) (n : Nat) :
    mass (fun k => f k + g k) n = mass f n + mass g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [mass, ih]; omega

theorem mass_single (n k : Nat) :
    mass (fun j => if j = k then 1 else 0) n = if k < n then 1 else 0 := by
  induction n with
  | zero => simp [mass]
  | succ n ih =>
    simp only [mass, ih]
    by_cases eq : n = k
    · subst k
      simp
    · by_cases before : k < n
      · simp [before, eq, show k < n + 1 by omega]
      · simp [before, eq, show ¬ k < n + 1 by omega]

theorem mass_count_key {α : Type} (key : α → Nat) {xs : List α} (n : Nat)
    (bounds : ∀ s ∈ xs, key s < n) :
    mass (countKey (fun s => some (key s)) xs) n = xs.length := by
  induction xs with
  | nil => exact mass_zero n
  | cons s xs ih =>
    have first := bounds s (by simp)
    have rest := ih (fun t member => bounds t (by simp [member]))
    have split : countKey (fun s => some (key s)) (s :: xs) =
        fun k => (if k = key s then 1 else 0) + countKey (fun s => some (key s)) xs k := by
      funext k
      simp [countKey, eq_comm]
    rw [split, mass_add, mass_single, ite_eq_left first, rest]
    simp only [List.length_cons]
    omega

theorem mass_optional_key {α : Type} (key : α → Option Nat) {xs : List α} (n : Nat)
    (bounds : ∀ s ∈ xs, ∀ k, key s = some k → k < n) :
    mass (countKey key xs) n ≤ xs.length := by
  induction xs with
  | nil => simp only [countKey]; rw [mass_zero]; simp
  | cons s xs ih =>
    have rest := ih (fun t member => bounds t (by simp [member]))
    rw [show countKey key (s :: xs) =
      (fun k => (if key s = some k then 1 else 0) + countKey key xs k) from rfl, mass_add]
    cases eq : key s with
    | none =>
      simp only [reduceCtorEq, ite_false]
      rw [mass_zero]
      simp only [List.length_cons]
      omega
    | some k =>
      have first := bounds s (by simp) k eq
      have single : (fun j => if some k = some j then 1 else 0) =
          (fun j => if j = k then 1 else 0) := by funext j; simp [eq_comm]
      rw [single, mass_single, ite_eq_left first]
      simp only [List.length_cons]
      omega

theorem literal_frequency_mass (lc : Nat → Nat) {xs : List Symbol}
    (bounds : ∀ s ∈ xs, s.literalKey lc < 286) :
    mass (literalFrequency lc xs) 286 = xs.length + 1 := by
  unfold literalFrequency
  rw [mass_add, mass_single, mass_count_key _ _ bounds]
  simp [Nat.add_comm]

theorem distance_frequency_mass (dc : Nat → Nat) {xs : List Symbol}
    (bounds : ∀ s ∈ xs, ∀ k, s.distanceKey dc = some k → k < 30) :
    mass (distanceFrequency dc xs) 30 ≤ xs.length := mass_optional_key _ _ bounds

end ZlibNgF.Math.HuffSymbols

namespace ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

theorem mass_mono {f g : Nat → Nat} {n : Nat} (bound : ∀ k, k < n → f k ≤ g k) :
    mass f n ≤ mass g n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have before := ih (fun k hk => bound k (by omega))
    have last := bound n (by omega)
    simp only [mass]
    omega

end ZlibNgF.Math.HuffSymbols

/-! # Weighted source symbol histograms and their integer cost bounds -/

namespace ZlibNgF.Math.HuffSymbols
set_option autoImplicit false

theorem mass_mul_left (f : Nat → Nat) (n c : Nat) : mass (fun k => c * f k) n = c * mass f n := by
  induction n with
  | zero => simp [mass]
  | succ n ih => simp only [mass, ih, Nat.mul_add]

theorem mass_mul_right (f : Nat → Nat) (n c : Nat) : mass (fun k => f k * c) n = mass f n * c := by
  induction n with
  | zero => simp [mass]
  | succ n ih => simp only [mass, ih, Nat.add_mul]

theorem mass_single_value (n key value : Nat) :
    mass (fun k => if k = key then value else 0) n = if key < n then value else 0 := by
  have point : (fun k => if k = key then value else 0) = (fun k => (if k = key then 1 else 0) * value) := by
    funext k
    by_cases same : k = key <;> simp only [same, ite_true, ite_false, Nat.one_mul, Nat.zero_mul]
  rw [point, mass_mul_right, mass_single]
  split <;> simp

/-- A histogram weighted by code cost equals the sum of costs over the
original source symbols, including repeated occurrences of the same code. -/
theorem weighted_count_key {α : Type} (key : α → Nat) {xs : List α} (n : Nat) (cost : Nat → Nat)
    (bounds : ∀ x ∈ xs, key x < n) :
    mass (fun k => countKey (fun x => some (key x)) xs k * cost k) n =
      (xs.map (fun x => cost (key x))).sum := by
  induction xs with
  | nil => simp only [countKey, Nat.zero_mul, List.map_nil, List.sum_nil]; exact mass_zero n
  | cons x xs ih =>
    have first := bounds x (by simp)
    have rest := ih (fun y member => bounds y (by simp [member]))
    have point : (fun k => countKey (fun x => some (key x)) (x :: xs) k * cost k) =
        (fun k => (if k = key x then cost (key x) else 0) + countKey (fun x => some (key x)) xs k * cost k) := by
      funext k
      by_cases same : k = key x
      · subst k
        simp only [countKey, ite_true, Nat.add_mul, Nat.one_mul]
      · simp [countKey, same, Ne.symm same]
    rw [point, mass_add, mass_single_value, ite_eq_left first, rest]
    simp only [List.map_cons, List.sum_cons]

/-- Pointwise code certificates add to a whole-tree cost bound. Zero-count
codes contribute no left-hand cost. The class budget is used once globally. -/
theorem weighted_tree_bound (frequency cost coefficient push : Nat → Nat)
    (n lambda mu weight budget : Nat)
    (codes : ∀ k, k < n → frequency k ≠ 0 →
      frequency k * (1000 * cost k) ≤ lambda * frequency k + coefficient k * weight + mu * push k * weight)
    (pushBound : mass push n ≤ budget) :
    1000 * mass (fun k => frequency k * cost k) n ≤
      lambda * mass frequency n + (mass coefficient n + mu * budget) * weight := by
  have point : ∀ k, k < n → 1000 * (frequency k * cost k) ≤
      lambda * frequency k + coefficient k * weight + mu * push k * weight := by
    intro k bound
    by_cases zero : frequency k = 0
    · simp only [zero, Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
      omega
    · simpa only [Nat.mul_left_comm] using codes k bound zero
  have combined := mass_mono point
  simp only [mass_add, mass_mul_left, mass_mul_right] at combined
  have bounded := Nat.mul_le_mul_right weight (Nat.mul_le_mul_left mu pushBound)
  rw [Nat.add_mul]
  omega

/-- Every occurrence contributes one to its selected histogram entry. -/
theorem count_key_positive {α : Type} (key : α → Option Nat) {xs : List α} {x : α} {v : Nat}
    (member : x ∈ xs) (selected : key x = some v) : 1 ≤ countKey key xs v := by
  induction xs with
  | nil => cases member
  | cons y ys ih =>
    simp only [List.mem_cons] at member
    rcases member with same | rest
    · subst x
      rw [countKey, selected, ite_eq_left rfl]
      omega
    · have previous := ih rest
      rw [countKey]
      omega

/-- Optional histograms omit unselected symbols and otherwise retain the
exact weighted contribution of every occurrence. -/
theorem weighted_optional_key {α : Type} (key : α → Option Nat) {xs : List α} (n : Nat) (cost : Nat → Nat)
    (bounds : ∀ x ∈ xs, ∀ k, key x = some k → k < n) :
    mass (fun k => countKey key xs k * cost k) n =
      (xs.map (fun x => match key x with | none => 0 | some k => cost k)).sum := by
  induction xs with
  | nil => simp only [countKey, Nat.zero_mul, List.map_nil, List.sum_nil]; exact mass_zero n
  | cons x xs ih =>
    have rest := ih (fun y member => bounds y (by simp [member]))
    cases selected : key x with
    | none =>
      have same : (fun k => countKey key (x :: xs) k * cost k) =
          (fun k => countKey key xs k * cost k) := by
        funext k
        simp only [countKey, selected, reduceCtorEq, ite_false, Nat.zero_add]
      rw [same, rest]
      simp only [List.map_cons, selected, List.sum_cons, Nat.zero_add]
    | some v =>
      have first := bounds x (by simp) v selected
      have point : (fun k => countKey key (x :: xs) k * cost k) =
          (fun k => (if k = v then cost v else 0) + countKey key xs k * cost k) := by
        funext k
        by_cases same : k = v
        · subst k
          simp only [countKey, selected, ite_true, Nat.add_mul, Nat.one_mul]
        · simp [countKey, selected, same, Ne.symm same]
      rw [point, mass_add, mass_single_value, ite_eq_left first, rest]
      simp only [List.map_cons, selected, List.sum_cons]

theorem list_sum_le_split {α : Type} (xs : List α) (cost left right : α → Nat)
    (bound : ∀ x ∈ xs, cost x ≤ left x + right x) :
    (xs.map cost).sum ≤ (xs.map left).sum + (xs.map right).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have first := bound x (by simp)
    have rest := ih (fun y member => bound y (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    omega

end ZlibNgF.Math.HuffSymbols
