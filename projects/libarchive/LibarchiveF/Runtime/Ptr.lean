import LibarchiveF.Runtime.Monad

/-!
# Strict ISO C17 pointer primitives (`LibarchiveF`)

Enforces ISO C17 §6.5.6 and §6.5.8 without permissive zero-offset or null-difference shortcuts:
- `Ptr.add` / `Ptr.sub` fault on `NULL` and dangling pointers even when `k = 0`;
- `Ptr.diff` faults on `NULL - NULL` and cross-object pointers;
- `Ptr.lt` / `Ptr.le` fault on `NULL` and cross-object pointers.
-/

namespace C

section generic
variable {R T : Type} [Space Heap R T]

/-- `p + k` under strict ISO C17 §6.5.6p8. -/
def Ptr.add (p : Ptr R) (k : Int) : M (Ptr R) := fun h =>
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
def Ptr.sub (p : Ptr R) (k : Int) : M (Ptr R) := p.add (-k)

/-- `*p`. Faults if `p` is null, dangling, or outside `[0, a.size)`. -/
def Ptr.load (p : Ptr R) : M T := fun h =>
  match p with
  | .null => .error (.ub "null dereference")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "read through a dangling pointer")
    | some a => if hk : off < a.size then .ok (a[off], h) else .error (.ub "read outside its object")

/-- `p[i]`, that is `*(p + i)`. -/
def Ptr.index (p : Ptr R) (i : Int) : M T := do
  Ptr.load (← p.add i)

/-- `*p = v`. Faults if `p` is null, dangling, read-only, or outside `[0, a.size)`. -/
def Ptr.store (p : Ptr R) (v : T) : M Unit := fun h =>
  match p with
  | .null => .error (.ub "null store")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "store through a dangling pointer")
    | some a =>
      if Space.ro h r then .error (.ub "store into a read-only object")
      else if off < a.size then .ok ((), Space.modify h r (fun a => a.set! off v))
      else .error (.ub "store outside its object")

/-- `p - q` under strict ISO C17 §6.5.6p9. -/
def Ptr.diff [DecidableEq R] (p q : Ptr R) : M Int64 := fun h =>
  match p, q with
  | .ref r1 o1, .ref r2 o2 =>
    if r1 = r2 then
      match Space.get h r1 with
      | some a =>
        if o1 ≤ a.size ∧ o2 ≤ a.size then
          if -(2 ^ 63 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 2 ^ 63 then
            .ok (Int64.ofInt ((o1 : Int) - (o2 : Int)), h)
          else .error (.ub "pointer difference is not a ptrdiff_t")
        else .error (.ub "pointer outside its object")
      | none => .error (.ub "difference of dangling pointers")
    else .error (.ub "difference of pointers into different objects")
  | _, _ => .error (.ub "difference involving a null pointer")

/-- `p < q` under strict ISO C17 §6.5.8p5. -/
def Ptr.lt [DecidableEq R] (p q : Ptr R) : M Bool := fun h =>
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
def Ptr.le [DecidableEq R] (p q : Ptr R) : M Bool := do
  return !(← Ptr.lt q p)

end generic

end C
