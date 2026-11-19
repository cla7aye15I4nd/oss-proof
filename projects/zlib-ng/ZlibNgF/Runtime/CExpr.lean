import ZlibNgF.Runtime.Libc

/-!
# Checked C operators and unaligned scalar access (`ZlibNgF`)

* Shifts fault when the count is negative or not below the width (ISO C17 §6.5.7p3); signed results fault on
  overflow (§6.5p5).
* `memmove` (§7.24.2.2): both pointers must point into live objects with `n` bytes in range, even for `n = 0`.
* `zng_memread_N` / `zng_memwrite_N` (`zmemory.h`) read and write `N` bytes at any alignment, little-endian
  (x86_64). With GCC they are accesses through a packed `may_alias` struct; the model performs them as byte
  accesses, each in bounds of the object.
-/

set_option autoImplicit false

namespace C

/-- `x << n` on 32 bits. -/
def shl32 (x n : UInt32) : M UInt32 := if n < 32 then pure (x <<< n) else ub "shift count out of range"
/-- `x >> n` on 32 bits. -/
def shr32 (x n : UInt32) : M UInt32 := if n < 32 then pure (x >>> n) else ub "shift count out of range"
/-- `x << n` on 64 bits. -/
def shl64 (x : UInt64) (n : UInt32) : M UInt64 := if n < 64 then pure (x <<< n.toUInt64) else ub "shift count out of range"
/-- `x >> n` on 64 bits. -/
def shr64 (x : UInt64) (n : UInt32) : M UInt64 := if n < 64 then pure (x >>> n.toUInt64) else ub "shift count out of range"

/-- An `int` result: faults on signed overflow. -/
def chkI32 (v : Int) : M Int32 :=
  if -2147483648 ≤ v ∧ v < 2147483648 then pure (Int32.ofInt v) else ub "signed integer overflow"

/-- `memmove(dst, src, n)` (ISO C17 §7.24.2.2): overlapping ranges allowed. -/
def Ptr.memmove {R : Type} [DecidableEq R] [Space Heap R UInt8] (dst src : Ptr R) (n : Nat) : M Unit := fun h =>
  match dst, src with
  | .null, _ | _, .null => .error (.ub "memmove involving a null pointer")
  | .ref rd od, .ref rs os =>
    match Space.get h rd, Space.get h rs with
    | some ad, some as_ =>
      if Space.ro h rd then .error (.ub "memmove into a read-only object")
      else if od + n ≤ ad.size ∧ os + n ≤ as_.size then
        let copied := Id.run do
          let mut out := ad
          for i in [0:n] do
            out := out.set! (od + i) as_[os + i]!
          return out
        .ok ((), Space.modify h rd (fun _ => copied))
      else .error (.ub "memmove outside its object")
    | _, _ => .error (.ub "memmove involving a dangling pointer")

/-- `zng_memread_2(p)`. -/
def memread2 (p : BPtr) : M UInt16 := do
  let b0 ← index8 p 0
  let b1 ← index8 p 1
  return b0.toUInt16 ||| (b1.toUInt16 <<< 8)

/-- `zng_memread_4(p)`. -/
def memread4 (p : BPtr) : M UInt32 := do
  let b0 ← index8 p 0
  let b1 ← index8 p 1
  let b2 ← index8 p 2
  let b3 ← index8 p 3
  return b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- `zng_memread_8(p)`. -/
def memread8 (p : BPtr) : M UInt64 := do
  let lo ← memread4 p
  let hi ← memread4 (← p.add 4)
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-- `zng_memwrite_8(p, v)`. -/
def memwrite8 (p : BPtr) (v : UInt64) : M Unit := do
  Ptr.store (← p.add 0) v.toUInt8
  Ptr.store (← p.add 1) (v >>> 8).toUInt8
  Ptr.store (← p.add 2) (v >>> 16).toUInt8
  Ptr.store (← p.add 3) (v >>> 24).toUInt8
  Ptr.store (← p.add 4) (v >>> 32).toUInt8
  Ptr.store (← p.add 5) (v >>> 40).toUInt8
  Ptr.store (← p.add 6) (v >>> 48).toUInt8
  Ptr.store (← p.add 7) (v >>> 56).toUInt8

/-- A local array of `n` bytes whose address is taken (`unsigned char buf[n]`): a fresh block with
uninitialised contents (from `Heap.garbage`). Unlike `malloc` it never fails and does not consume an allocation
oracle step. -/
def localBlock (n : Nat) : M BPtr := fun h =>
  let b := h.nextBlk
  let arr := Array.ofFn (n := n) (fun i => Junk.of (h.garbage (2 ^ 41 + b) i.val))
  .ok (.ref (.heap b) 0, { h with bytes := upd h.bytes b (some arr), nextBlk := b + 1 })

/-- The values of the uninitialised scalar locals of a function (ISO C17 §6.7.9p10, §6.2.6.1): the garbage oracle
at key `2 ^ 42 + k`, one key per translated function. A translation reads local `i` as `Junk.of (g i)`. -/
def uninitLocals (k : Nat) : M (Nat → UInt64) := fun h => .ok (h.garbage (2 ^ 42 + k), h)

/-- The end of the lifetime of a local array made by `localBlock`. -/
def dropLocal (p : BPtr) : M Unit := fun h =>
  match p with
  | .ref (.heap b) 0 =>
    match h.bytes b with
    | some _ => .ok ((), { h with bytes := upd h.bytes b none })
    | none => .error (.ub "end of lifetime of a dead local array")
  | _ => .error (.ub "not a local array")

end C
