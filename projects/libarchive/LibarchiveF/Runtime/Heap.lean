import LibarchiveF.Runtime.Space

/-!
# Runtime heap (`LibarchiveF`)

Byte-addressed object heap for LP64 Linux translations under strict ISO C17 pointer rules.
-/

namespace C

/-- Reference to a byte array: a dynamically allocated heap block or a read-only static block. -/
inductive BRef where
  | heap (b : Nat)
  | const (b : Nat)
  deriving DecidableEq, Repr, Inhabited

abbrev BPtr := Ptr BRef

/-- Heap state with byte blocks, read-only static blocks, allocation oracle, and uninitialised-memory oracle. -/
structure Heap where
  bytes : Tbl (Option (Array UInt8)) := .empty
  consts : Tbl (Option (Array UInt8)) := .empty
  nalloc : Nat := 0
  allocOk : Nat → Bool := fun _ => true
  garbage : Nat → Nat → UInt64 := fun _ _ => 0

namespace Heap

def empty : Heap := {}

def getBytes (h : Heap) : BRef → Option (Array UInt8)
  | .heap b => h.bytes b
  | .const b => h.consts b

def putBytes (h : Heap) (r : BRef) (a : Array UInt8) : Heap :=
  match r with
  | .heap b => { h with bytes := upd h.bytes b (some a) }
  | .const b => { h with consts := upd h.consts b (some a) }

def isRo (_h : Heap) : BRef → Bool
  | .heap _ => false
  | .const _ => true

def modifyBytes (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) : Heap :=
  match r with
  | .heap b => { h with bytes := h.bytes.modify b (Option.map f) }
  | .const b => { h with consts := h.consts.modify b (Option.map f) }

theorem modifyBytes_eq (h : Heap) (r : BRef) (a : Array UInt8) (f : Array UInt8 → Array UInt8)
    (hg : getBytes h r = some a) :
    modifyBytes h r f = putBytes h r (f a) := by
  cases r with
  | heap b =>
    simp only [getBytes] at hg
    simp only [modifyBytes, putBytes, Tbl.modify_opt h.bytes b f a hg]
  | const b =>
    simp only [getBytes] at hg
    simp only [modifyBytes, putBytes, Tbl.modify_opt h.consts b f a hg]

end Heap

instance : Space Heap BRef UInt8 where
  get := Heap.getBytes
  put := Heap.putBytes
  ro := Heap.isRo
  modify := Heap.modifyBytes
  modify_eq := Heap.modifyBytes_eq

end C
