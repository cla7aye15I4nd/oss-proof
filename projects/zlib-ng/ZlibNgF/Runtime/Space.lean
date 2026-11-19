/-!
# Runtime: heap-independent tables, pointers, and spaces (`ZlibNgF`)
-/

set_option autoImplicit false

namespace C

structure Tbl (α : Type) [Inhabited α] where
  arr : Array α

namespace Tbl
variable {α : Type} [Inhabited α]

def get (t : Tbl α) (k : Nat) : α := t.arr.getD k default
instance : CoeFun (Tbl α) (fun _ => Nat → α) := ⟨Tbl.get⟩

def empty : Tbl α := ⟨#[]⟩
instance : Inhabited (Tbl α) := ⟨empty⟩

def set (t : Tbl α) (k : Nat) (v : α) : Tbl α :=
  if k < t.arr.size then ⟨t.arr.set! k v⟩ else ⟨(t.arr ++ Array.replicate (k - t.arr.size) default).push v⟩

def modify (t : Tbl α) (k : Nat) (f : α → α) : Tbl α := ⟨t.arr.modify k f⟩

theorem get_eq (t : Tbl α) (k : Nat) : t.get k = (t.arr[k]?).getD default := by
  simp [get, Array.getD_eq_getD_getElem?]

theorem get_set (t : Tbl α) (k : Nat) (v : α) (x : Nat) :
    (t.set k v).get x = if x = k then v else t.get x := by
  unfold set
  split
  · rename_i h
    simp [get_eq, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split <;> simp_all [eq_comm]
  · rename_i h
    simp only [get_eq]
    simp [Array.getElem?_push, Array.getElem?_append, Array.getElem?_replicate]
    by_cases h1 : x < t.arr.size
    · have : x ≠ k := by omega
      simp [h1, this]
    · by_cases h2 : x = k
      · subst h2; simp [h1]
      · simp [h1, h2]
        have h3 : x - t.arr.size ≠ k - t.arr.size := by omega
        simp [h3]
        split <;> simp

@[simp] theorem get_empty_opt {β : Type} (k : Nat) : (empty : Tbl (Option β)).get k = none := by
  simp [get_eq, empty]
  rfl

theorem lt_size_of_get_ne (t : Tbl α) (k : Nat) (h : t.get k ≠ default) : k < t.arr.size := by
  by_cases hc : k < t.arr.size
  · exact hc
  · exfalso
    apply h
    simp [get_eq, Array.getElem?_eq_none (by omega : t.arr.size ≤ k)]

theorem modify_eq (t : Tbl α) (k : Nat) (f : α → α) (hk : k < t.arr.size) :
    t.modify k f = t.set k (f (t.get k)) := by
  unfold modify set
  simp only [hk, ite_true]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp [Array.getElem?_modify, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, get_eq, hk]
  split
  · rename_i hki
    subst hki
    simp [Array.getElem?_eq_getElem hk]
  · simp_all

end Tbl

def upd {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) : Tbl α := t.set k v

@[simp] theorem upd_same {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) : upd t k v k = v := by
  have := Tbl.get_set t k v k
  simpa [upd] using this

@[simp] theorem upd_ne {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) (x : Nat) (h : x ≠ k) :
    upd t k v x = t x := by
  have := Tbl.get_set t k v x
  simpa [upd, h] using this

theorem Tbl.modify_opt {β : Type} (t : Tbl (Option β)) (k : Nat) (g : β → β) (a : β) (hg : t k = some a) :
    t.modify k (Option.map g) = upd t k (some (g a)) := by
  have hk : k < t.arr.size := Tbl.lt_size_of_get_ne t k (by simp [Tbl.get] at hg ⊢; simp [hg])
  rw [Tbl.modify_eq t k _ hk]
  simp [upd, show t.get k = some a from hg]

inductive Ptr (R : Type) where
  | null
  | ref (r : R) (off : Nat)
  deriving DecidableEq, Repr

instance {R : Type} : Inhabited (Ptr R) := ⟨.null⟩

class Space (H : Type) (R : Type) (T : outParam Type) where
  get : H → R → Option (Array T)
  put : H → R → Array T → H
  ro : H → R → Bool
  modify : H → R → (Array T → Array T) → H
  modify_eq : ∀ h r a f, get h r = some a → ro h r = false → modify h r f = put h r (f a)

class Junk (T : Type) where
  of : UInt64 → T

instance : Junk UInt8 := ⟨UInt64.toUInt8⟩
instance : Junk UInt16 := ⟨UInt64.toUInt16⟩
instance : Junk UInt32 := ⟨UInt64.toUInt32⟩
instance : Junk UInt64 := ⟨id⟩

end C
