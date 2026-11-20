/-!
# Shared object-table and space abstractions (`OssProof.Runtime.Space`)

Parameterized, heap-agnostic foundations for strict ISO C17 object-heap verification:
- `Fault`: explicit UB, OOM, and fuel-exhaustion faults;
- `Ptr R`: typed pointer (either `.null` or `.ref r off`);
- `Tbl T`: grow-only live allocation table with read-only flags;
- `Space H R T`: typeclass projecting a live array table out of any project-specific `Heap` `H`.
-/

namespace OssProof

inductive Fault where
  | ub (msg : String)
  | oom
  | fuel
  deriving Repr, DecidableEq, BEq

inductive Ptr (R : Type) where
  | null
  | ref (r : R) (off : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A table of live or freed array objects of element type `T`. -/
structure Tbl (T : Type) where
  slots : Array (Option (Array T × Bool)) := #[]

namespace Tbl

def empty {T : Type} : Tbl T := {}

def get {T : Type} (t : Tbl T) (id : Nat) : Option (Array T) :=
  match t.slots[id]? with
  | some (some (a, _)) => some a
  | _ => none

def ro {T : Type} (t : Tbl T) (id : Nat) : Bool :=
  match t.slots[id]? with
  | some (some (_, r)) => r
  | _ => false

def alloc {T : Type} (t : Tbl T) (a : Array T) (readOnly : Bool := false) : Nat × Tbl T :=
  (t.slots.size, { slots := t.slots.push (some (a, readOnly)) })

def free {T : Type} (t : Tbl T) (id : Nat) : Tbl T :=
  { slots := t.slots.set! id none }

def modify {T : Type} (t : Tbl T) (id : Nat) (f : Array T → Array T) : Tbl T :=
  match t.slots[id]? with
  | some (some (a, r)) => { slots := t.slots.set! id (some (f a, r)) }
  | _ => t

theorem get_empty {T : Type} (id : Nat) : (Tbl.empty (T := T)).get id = none := by
  simp [Tbl.empty, Tbl.get]

theorem get_alloc_self {T : Type} (t : Tbl T) (a : Array T) (readOnly : Bool) :
    (t.alloc a readOnly).2.get (t.alloc a readOnly).1 = some a := by
  simp [Tbl.alloc, Tbl.get]

theorem get_alloc_ne {T : Type} (t : Tbl T) (a : Array T) (readOnly : Bool) (id : Nat)
    (hne : id ≠ t.slots.size) :
    (t.alloc a readOnly).2.get id = t.get id := by
  simp [Tbl.alloc, Tbl.get, Array.getElem?_push, hne]

theorem get_free_self {T : Type} (t : Tbl T) (id : Nat) (h : id < t.slots.size) :
    (t.free id).get id = none := by
  simp [Tbl.free, Tbl.get, Array.set!, h]

theorem get_free_ne {T : Type} (t : Tbl T) (id j : Nat) (hne : j ≠ id) :
    (t.free id).get j = t.get j := by
  have hne' : id ≠ j := Ne.symm hne
  simp only [Tbl.free, Tbl.get, Array.set!]
  by_cases h : id < t.slots.size
  · simp [Array.setIfInBounds, h, hne']
  · simp [Array.setIfInBounds, h]

theorem get_modify_self {T : Type} (t : Tbl T) (id : Nat) (f : Array T → Array T) (a : Array T)
    (hget : t.get id = some a) :
    (t.modify id f).get id = some (f a) := by
  unfold Tbl.get at hget
  cases hs : t.slots[id]? with
  | none => simp [hs] at hget
  | some entry =>
    cases entry with
    | none => simp [hs] at hget
    | some pair =>
      rcases pair with ⟨arr, r⟩
      simp only [hs] at hget
      cases hget
      have hlt : id < t.slots.size := by
        cases Nat.lt_or_ge id t.slots.size with
        | inl h => exact h
        | inr h =>
          have hnone : t.slots[id]? = none := Array.getElem?_eq_none h
          simp [hnone] at hs
      rw [Tbl.modify, hs]
      simp [Tbl.get, Array.set!, hlt]

theorem get_modify_ne {T : Type} (t : Tbl T) (id j : Nat) (f : Array T → Array T) (hne : j ≠ id) :
    (t.modify id f).get j = t.get j := by
  have hne' : id ≠ j := Ne.symm hne
  unfold Tbl.modify
  cases hs : t.slots[id]? with
  | none => rfl
  | some entry =>
    cases entry with
    | none => rfl
    | some pair =>
      simp only [Tbl.get, Array.set!]
      by_cases h : id < t.slots.size
      · simp [Array.setIfInBounds, h, hne']
      · simp [Array.setIfInBounds, h]

end Tbl

/-- Typeclass projecting a typed object table out of any project-specific `Heap` `H`. -/
class Space (H : Type) (R : Type) (T : outParam Type) where
  get : H → R → Option (Array T)
  ro : H → R → Bool
  modify : H → R → (Array T → Array T) → H

/-- Well-behaved `Space` laws needed for generic `Wp` and `Frame` proofs. -/
class LawfulSpace (H : Type) (R : Type) (T : outParam Type) [Space H R T] where
  get_modify_same : ∀ (h : H) (r : R) (f : Array T → Array T) (a : Array T),
    Space.get h r = some a → Space.get (Space.modify h r f) r = some (f a)
  get_modify_other : ∀ (h : H) (r r' : R) (f : Array T → Array T),
    r' ≠ r → Space.get (Space.modify h r f) r' = Space.get h r'
  ro_modify : ∀ (h : H) (r r' : R) (f : Array T → Array T),
    Space.ro (Space.modify h r f) r' = Space.ro h r'

end OssProof
