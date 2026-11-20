import MozjpegF.Runtime.Monad

/-!
# Strict ISO C17 pointer arithmetic (`MozjpegF`)

Instantiated from `framework/lean/StrictPtr.lean`:
- `Ptr.add` faults on `NULL` (even when `k = 0`), on dangling pointers (even when `k = 0`), and on out-of-bounds offsets.
- `Ptr.diff`, `Ptr.lt`, and `Ptr.le` require both operands to refer to `[0, a.size]` of the exact same live array object.
-/

set_option autoImplicit false

namespace C

section generic
variable {R T : Type} [Space Heap R T]

/-- `p + k` under strict ISO C17 §6.5.6p8. Both `off` and `off + k` must lie in `[0, a.size]` of a live
array object `a`; `NULL + 0` and dangling/wild pointer `+ 0` fault with `Fault.ub`. -/
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

/-- `p - q` under strict ISO C17 §6.5.6p9. Both operands must point into (or one past the end of) the
same live array object; `NULL - NULL` faults with `Fault.ub`. -/
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

def Ptr.le [DecidableEq R] (p q : Ptr R) : M Bool := do
  return !(← Ptr.lt q p)

theorem Ptr.add_eq (h : Heap) (r : R) (off : Nat) (k : Int) (a : Array T)
    (hg : Space.get h r = some a)
    (hb : off ≤ a.size ∧ 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int)) :
    C.run (Ptr.add (.ref r off) k >>= pure) h =
      .ok (.ref r ((off : Int) + k).toNat, h) := by
  simp [C.run, bind, pure, Ptr.add, hg, hb]

theorem Ptr.add_bind {β : Type} (h : Heap) (r : R) (off : Nat) (k : Int) (a : Array T)
    (f : Ptr R → M β) (hg : Space.get h r = some a)
    (hb : off ≤ a.size ∧ 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int)) :
    C.run (Ptr.add (.ref r off) k >>= f) h =
      C.run (f (.ref r ((off : Int) + k).toNat)) h := by
  simp [C.run, bind, Ptr.add, hg, hb]

theorem Ptr.load_bind {β : Type} (h : Heap) (r : R) (off : Nat) (a : Array T)
    (f : T → M β) (hg : Space.get h r = some a) (ho : off < a.size) :
    C.run (Ptr.load (.ref r off) >>= f) h = C.run (f a[off]) h := by
  simp [C.run, bind, Ptr.load, hg, ho]

theorem Ptr.store_bind {β : Type} (h : Heap) (r : R) (off : Nat) (v : T) (a : Array T)
    (f : Unit → M β) (hg : Space.get h r = some a) (hro : Space.ro h r = false) (ho : off < a.size) :
    C.run (Ptr.store (.ref r off) v >>= f) h =
      C.run (f ()) (Space.put h r (a.set! off v)) := by
  simp [C.run, bind, Ptr.store, hg, hro, ho, Space.modify_eq]

end generic

end C
