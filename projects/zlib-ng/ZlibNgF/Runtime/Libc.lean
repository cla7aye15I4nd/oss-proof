import ZlibNgF.Runtime.Ptr

/-!
# Strict ISO C17 memory, allocation, and string-literal primitives (`ZlibNgF`)

Under ISO C17 §7.24.1p2, pointer arguments to `memcpy` and `memset` must point into live objects even
when the byte count `n` is `0`.
-/

set_option autoImplicit false

namespace C

def load8 (p : BPtr) : M UInt8 := Ptr.load p
def index8 (p : BPtr) (i : Int) : M UInt8 := Ptr.index p i
def store8 (p : BPtr) (v : UInt8) : M Unit := Ptr.store p v

/-- Address representative of `p` (`baseAddr r + off`), preserving arbitrary origin alignment modulo `2^64`. -/
def addrOf (p : BPtr) : M UInt64 := fun h =>
  match p with
  | .null => .ok (0, h)
  | .ref r off => .ok (h.baseAddr r + UInt64.ofNat off, h)

/-- `(T *)p` for a byte pointer `p` and an object type `T` of alignment `align`: undefined unless the address of
`p` is a multiple of `align` (ISO C17 §6.3.2.3p7). The result designates the same byte position, so it stays a
`BPtr`; loads through it are byte loads (the effective-type rule, §6.5p7, is not modelled). -/
def Ptr.castAligned (p : BPtr) (align : Nat) : M BPtr := do
  let addr ← addrOf p
  if addr.toNat % align != 0 then ub "conversion to a misaligned pointer"
  return p

/-- Look up a source string literal in `strTable` and return its static read-only `BPtr`. -/
def strLitRef (s : String) : M BPtr := fun h =>
  match strTable.findIdx? (· == s) with
  | some i => .ok (.ref (.str i) 0, h)
  | none => .error (.ub "unknown string literal")

/-- `malloc(n)` on LP64: consults `h.allocOk h.nalloc`, returning `.null` on OOM or a fresh block filled from `h.garbage`. -/
def allocB (n : Nat) : M BPtr := fun h =>
  if h.allocOk h.nalloc then
    let b := h.nextBlk
    let arr := Array.ofFn (n := n) (fun i => Junk.of (h.garbage h.nalloc i.val))
    let h' : Heap := {
      h with
      bytes := upd h.bytes b (some arr)
      savedPtrs := upd h.savedPtrs b none
      nextBlk := b + 1
      nalloc := h.nalloc + 1
    }
    .ok (.ref (.heap b) 0, h')
  else
    .ok (.null, { h with nalloc := h.nalloc + 1 })

/-- `free(p)` under ISO C17 §7.22.3.3: `.null` is a no-op; otherwise `p` must be the exact base `.ref (.heap b) 0` of a live heap block. -/
def freeB (p : BPtr) : M Unit := fun h =>
  match p with
  | .null => .ok ((), h)
  | .ref (.heap b) 0 =>
    match h.bytes b with
    | some _ => .ok ((), { h with bytes := upd h.bytes b none, savedPtrs := upd h.savedPtrs b none })
    | none => .error (.ub "double or dangling free")
  | _ => .error (.ub "free of non-heap or interior pointer")

/-- Store an 8-byte `void *` pointer value `val` at `dst` (`memcpy(dst, &val, sizeof(void *))`).
Requires `dst` to point into a writable heap block with `off + 8 ≤ a.size`. -/
def storePtrSlot (dst : BPtr) (val : BPtr) : M Unit := fun h =>
  match dst with
  | .ref (.heap b) off =>
    match h.bytes b with
    | some a =>
      if off + 8 ≤ a.size then
        .ok ((), { h with savedPtrs := upd h.savedPtrs b (some (off, val)) })
      else .error (.ub "pointer slot store outside its object")
    | none => .error (.ub "pointer slot store through a dangling pointer")
  | .null => .error (.ub "pointer slot store to null")
  | .ref _ _ => .error (.ub "pointer slot store into read-only object")

/-- Load an 8-byte `void *` pointer value previously stored at `src` (`*(void **)src`). -/
def loadPtrSlot (src : BPtr) : M BPtr := fun h =>
  match src with
  | .ref (.heap b) off =>
    match h.bytes b, h.savedPtrs b with
    | some a, some (savedOff, val) =>
      if off + 8 ≤ a.size ∧ savedOff = off then
        .ok (val, h)
      else .error (.ub "uninitialised or out-of-bounds pointer slot read")
    | none, _ => .error (.ub "pointer slot read through a dangling pointer")
    | _, none => .error (.ub "uninitialised pointer slot read")
  | .null => .error (.ub "pointer slot read from null")
  | .ref _ _ => .error (.ub "invalid pointer slot read")

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
