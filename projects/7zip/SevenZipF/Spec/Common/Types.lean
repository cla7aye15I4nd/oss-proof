import SevenZipF.Runtime.Libc

/-!
# Common specification predicates (`SevenZipF`)
-/

namespace SevenZipF.Spec

/-- Computation `m` faults with ISO C17 undefined behaviour on heap `h`. -/
def FaultsWithUb {α : Type} (m : C.M α) (h : C.Heap) : Prop :=
  ∃ msg, m h = .error (.ub msg)

/-- Computation `m` terminates normally without undefined behaviour or fuel exhaustion on `h`. -/
def TerminatesSafely {α : Type} (m : C.M α) (h : C.Heap) : Prop :=
  ∃ v h', m h = .ok (v, h')

/-- Readable byte slice `[p, p + len)` in a live object on heap `h` (when `len = 0` and `p = NULL`,
permitted only for APIs whose public C header explicitly allows `(NULL, 0)`). -/
def ReadableSlice (h : C.Heap) (p : C.BPtr) (len : Nat) : Prop :=
  (p = .null ∧ len = 0) ∨
  ∃ r off a, p = .ref r off ∧ C.Space.get h r = some a ∧ off + len ≤ a.size

/-- Writable byte slice `[p, p + cap)` in a mutable live heap block on `h`. -/
def WritableSlice (h : C.Heap) (p : C.BPtr) (cap : Nat) : Prop :=
  (p = .null ∧ cap = 0) ∨
  ∃ b off a, p = .ref (.heap b) off ∧ h.bytes b = some a ∧ off + cap ≤ a.size

/-- Two byte slices reside in distinct heap objects (or either has zero length). -/
def DisjointSlices (p : C.BPtr) (plen : Nat) (q : C.BPtr) (qlen : Nat) : Prop :=
  plen = 0 ∨ qlen = 0 ∨
  ∀ rp op rq oq, p = .ref rp op → q = .ref rq oq → rp ≠ rq

/-- Parameterised one-shot buffer-to-buffer decoder entry signature (`dst, dstCap, src, srcSize`). -/
abbrev BufferEntry := C.BPtr → UInt64 → C.BPtr → UInt64 → C.M Int64

/-- Full safety contract for a translated buffer-to-buffer entry point over arbitrary disjoint caller slices. -/
def BufferEntrySafe (fn : BufferEntry) : Prop :=
  ∀ (h : C.Heap) (dst : C.BPtr) (dstCap : UInt64) (src : C.BPtr) (srcSize : UInt64),
    WritableSlice h dst dstCap.toNat →
    ReadableSlice h src srcSize.toNat →
    DisjointSlices dst dstCap.toNat src srcSize.toNat →
    TerminatesSafely (fn dst dstCap src srcSize) h

end SevenZipF.Spec
