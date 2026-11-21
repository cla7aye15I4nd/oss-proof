import OssProof.Runtime.Monad

/-!
# Strict ISO C17 pointer operations and proof lemmas (`OssProof.Runtime.Ptr`)

Implements ISO C17 §6.5.6 and §6.5.8 strictly (no `NULL + 0`, no wild/dangling `+ 0`, no
`NULL - NULL`, no cross-object pointer subtraction or comparison, no transient out-of-bounds pointer
formation) and ships the full `*_ok` and strict-UB fault lemma suite once for all projects.
-/

namespace OssProof

namespace Ptr

section generic
variable {H R T : Type} [Space H R T]

/-- `p + k` under strict ISO C17 §6.5.6p8. Both `off` and `off + k` must lie in `[0, a.size]` of a
live array object `a`; `NULL + 0` and dangling/wild pointer `+ 0` fault with `Fault.ub`. -/
def add (p : Ptr R) (k : Int) : M H (Ptr R) := fun h =>
  match p with
  | .null => .error (.ub "arithmetic on a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "arithmetic on a dangling pointer")
    | some a =>
      if off ≤ a.size ∧ 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int) then
        .ok (.ref r ((off : Int) + k).toNat, h)
      else .error (.ub "pointer arithmetic outside its object")

/-- `p - k` under strict ISO C17 §6.5.6p8. -/
def sub (p : Ptr R) (k : Int) : M H (Ptr R) := add p (-k)

/-- `*p`. Faults if `p` is null, dangling, or outside `[0, a.size)`. -/
def load (p : Ptr R) : M H T := fun h =>
  match p with
  | .null => .error (.ub "null dereference")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "read through a dangling pointer")
    | some a =>
      if hk : off < a.size then .ok (a[off], h)
      else .error (.ub "read outside its object")

/-- `p[i]`, that is `*(p + i)`. -/
def index (p : Ptr R) (i : Int) : M H T := do
  load (← add p i)

/-- `*p = v`. Faults if `p` is null, dangling, read-only, or outside `[0, a.size)`. -/
def store (p : Ptr R) (v : T) : M H Unit := fun h =>
  match p with
  | .null => .error (.ub "null store")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "store through a dangling pointer")
    | some a =>
      if Space.ro h r then .error (.ub "store into a read-only object")
      else if off < a.size then .ok ((), Space.modify h r (fun a => a.set! off v))
      else .error (.ub "store outside its object")

/-- `p[i] = v`, that is `*(p + i) = v`. -/
def storeAt (p : Ptr R) (i : Int) (v : T) : M H Unit := do
  store (← add p i) v

/-- `p - q` under strict ISO C17 §6.5.6p9. Both operands must point into (or one past the end of)
the same live array object; `NULL - NULL` faults with `Fault.ub`. -/
def diff [DecidableEq R] (p q : Ptr R) : M H Int64 := fun h =>
  match p, q with
  | .ref r1 o1, .ref r2 o2 =>
    if r1 = r2 then
      match Space.get h r1 with
      | some a =>
        if o1 ≤ a.size ∧ o2 ≤ a.size then
          if I64_MIN ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) ≤ I64_MAX then
            .ok (Int64.ofInt ((o1 : Int) - (o2 : Int)), h)
          else .error (.ub "pointer difference is not a ptrdiff_t")
        else .error (.ub "pointer outside its object")
      | none => .error (.ub "difference of dangling pointers")
    else .error (.ub "difference of pointers into different objects")
  | _, _ => .error (.ub "difference involving a null pointer")

/-- `p < q` under strict ISO C17 §6.5.8p5. -/
def lt [DecidableEq R] (p q : Ptr R) : M H Bool := fun h =>
  match p, q with
  | .ref r1 o1, .ref r2 o2 =>
    if r1 = r2 then
      match Space.get h r1 with
      | some a =>
        if o1 ≤ a.size ∧ o2 ≤ a.size then .ok (decide (o1 < o2), h)
        else .error (.ub "pointer outside its object")
      | none => .error (.ub "comparison of dangling pointers")
    else .error (.ub "comparison of pointers into different objects")
  | _, _ => .error (.ub "comparison involving a null pointer")

/-- `p <= q` under strict ISO C17 §6.5.8p5. -/
def le [DecidableEq R] (p q : Ptr R) : M H Bool := do
  return !(← lt q p)

/-! ### Reusable `*_ok` lemmas -/

theorem add_ok (h : H) (r : R) (off : Nat) (k : Int) (a : Array T)
    (hget : Space.get h r = some a)
    (hoff : off ≤ a.size)
    (hlo : 0 ≤ (off : Int) + k)
    (hhi : (off : Int) + k ≤ (a.size : Int)) :
    add (H := H) (R := R) (T := T) (.ref r off) k h = .ok (.ref r ((off : Int) + k).toNat, h) := by
  simp [add, hget, hoff, hlo, hhi]

theorem add_nat_ok (h : H) (r : R) (off k : Nat) (a : Array T)
    (hget : Space.get h r = some a)
    (hhi : off + k ≤ a.size) :
    add (H := H) (R := R) (T := T) (.ref r off) (k : Int) h = .ok (.ref r (off + k), h) := by
  have h1 := add_ok h r off (k : Int) a hget (by omega) (by omega) (by omega)
  have h2 : ((off : Int) + (k : Int)).toNat = off + k := by omega
  simpa [h2] using h1

theorem load_ok (h : H) (r : R) (off : Nat) (a : Array T)
    (hget : Space.get h r = some a) (hlt : off < a.size) :
    load (H := H) (R := R) (T := T) (.ref r off) h = .ok (a[off], h) := by
  simp [load, hget, hlt]

theorem index_ok (h : H) (r : R) (off : Nat) (i : Int) (a : Array T)
    (hget : Space.get h r = some a)
    (hoff : off ≤ a.size)
    (hlo : 0 ≤ (off : Int) + i)
    (hhi : (off : Int) + i < (a.size : Int)) :
    index (H := H) (R := R) (T := T) (.ref r off) i h =
      .ok (a[((off : Int) + i).toNat]'(by omega), h) := by
  have hadd := add_ok h r off i a hget hoff hlo (by omega)
  have hlt : ((off : Int) + i).toNat < a.size := by omega
  simp [index, hadd, load, hget, hlt]

theorem store_ok (h : H) (r : R) (off : Nat) (v : T) (a : Array T)
    (hget : Space.get h r = some a)
    (hro : Space.ro h r = false)
    (hlt : off < a.size) :
    store (H := H) (R := R) (T := T) (.ref r off) v h =
      .ok ((), Space.modify h r (fun arr => arr.set! off v)) := by
  simp [store, hget, hro, hlt]

theorem diff_ok [DecidableEq R] (h : H) (r : R) (o1 o2 : Nat) (a : Array T)
    (hget : Space.get h r = some a)
    (ho1 : o1 ≤ a.size) (ho2 : o2 ≤ a.size)
    (hlo : I64_MIN ≤ (o1 : Int) - (o2 : Int))
    (hhi : (o1 : Int) - (o2 : Int) ≤ I64_MAX) :
    diff (H := H) (R := R) (T := T) (.ref r o1) (.ref r o2) h =
      .ok (Int64.ofInt ((o1 : Int) - (o2 : Int)), h) := by
  simp [diff, hget, ho1, ho2, hlo, hhi]

theorem lt_ok [DecidableEq R] (h : H) (r : R) (o1 o2 : Nat) (a : Array T)
    (hget : Space.get h r = some a)
    (ho1 : o1 ≤ a.size) (ho2 : o2 ≤ a.size) :
    lt (H := H) (R := R) (T := T) (.ref r o1) (.ref r o2) h = .ok (decide (o1 < o2), h) := by
  simp [lt, hget, ho1, ho2]

/-! ### Canonical strict ISO C17 UB fault theorems -/

theorem null_add_zero_ub (h : H) :
    ∃ msg, add (H := H) (R := R) (T := T) .null 0 h = .error (.ub msg) :=
  ⟨_, rfl⟩

theorem dangling_add_zero_ub (h : H) (r : R) (off : Nat) (hnone : Space.get h r = none) :
    ∃ msg, add (H := H) (R := R) (T := T) (.ref r off) 0 h = .error (.ub msg) :=
  ⟨"arithmetic on a dangling pointer", by simp [add, hnone]⟩

theorem null_diff_null_ub [DecidableEq R] (h : H) :
    ∃ msg, diff (H := H) (R := R) (T := T) .null .null h = .error (.ub msg) :=
  ⟨_, rfl⟩

theorem cross_object_diff_ub [DecidableEq R] (h : H) (r1 r2 : R) (o1 o2 : Nat) (hne : r1 ≠ r2) :
    ∃ msg, diff (H := H) (R := R) (T := T) (.ref r1 o1) (.ref r2 o2) h = .error (.ub msg) :=
  ⟨"difference of pointers into different objects", by simp [diff, hne]⟩

theorem cross_object_lt_ub [DecidableEq R] (h : H) (r1 r2 : R) (o1 o2 : Nat) (hne : r1 ≠ r2) :
    ∃ msg, lt (H := H) (R := R) (T := T) (.ref r1 o1) (.ref r2 o2) h = .error (.ub msg) :=
  ⟨"comparison of pointers into different objects", by simp [lt, hne]⟩

end generic
end Ptr
end OssProof
