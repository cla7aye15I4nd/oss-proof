import SevenZipF.Runtime.Ptr

/-!
# Strict ISO C17 memory primitives (`SevenZipF`)

Under ISO C17 §7.24.1p2, pointer arguments to `memcpy` and `memset` must point into live objects even
when the byte count `n` is `0`.
-/

namespace C

/-- `memset(dst, byte, n)` under strict ISO C17 §7.24.1p2 and §7.24.6.1. -/
def Ptr.memset {R : Type} [Space Heap R UInt8] (dst : Ptr R) (byte : UInt8) (n : Nat) : M Unit := fun h =>
  match dst with
  | .null => .error (.ub "memset on a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "memset on a dangling pointer")
    | some a =>
      if Space.ro h r then .error (.ub "memset into a read-only object")
      else if off + n ≤ a.size then
        let fillSlice := Id.run do
          let mut out := a
          for i in [0:n] do
            out := out.set! (off + i) byte
          return out
        .ok ((), Space.modify h r (fun _ => fillSlice))
      else .error (.ub "memset outside its object")

/-- `memcpy(dst, src, n)` under strict ISO C17 §7.24.1p2 and §7.24.2.1 (disjoint ranges required when `n > 0`). -/
def Ptr.memcpy {R : Type} [DecidableEq R] [Space Heap R UInt8] (dst src : Ptr R) (n : Nat) : M Unit := fun h =>
  match dst, src with
  | .null, _ | _, .null => .error (.ub "memcpy involving a null pointer")
  | .ref rd od, .ref rs os =>
    match Space.get h rd, Space.get h rs with
    | some ad, some as_ =>
      if Space.ro h rd then .error (.ub "memcpy into a read-only object")
      else if od + n ≤ ad.size ∧ os + n ≤ as_.size then
        if rd = rs ∧ n > 0 ∧ ¬ (od + n ≤ os ∨ os + n ≤ od) then
          .error (.ub "overlapping memcpy")
        else
          let copied := Id.run do
            let mut out := ad
            for i in [0:n] do
              out := out.set! (od + i) as_[os + i]!
            return out
          .ok ((), Space.modify h rd (fun _ => copied))
      else .error (.ub "memcpy outside its object")
    | _, _ => .error (.ub "memcpy involving a dangling pointer")

end C
