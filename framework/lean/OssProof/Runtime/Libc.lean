import OssProof.Runtime.Ptr

/-!
# Strict ISO C17 memory primitives (`OssProof.Runtime.Libc`)

Implements `memcpy`, `memmove`, `memset`, and `memcmp` under strict ISO C17 §7.24.1p2 and §7.1.4p1:
valid non-null pointers to live objects are required **even when the element count `n` is `0`**,
and `memcpy` additionally faults on overlapping ranges in the same object (§7.24.2.1p2).
-/

namespace OssProof

namespace Ptr

section libc
variable {H R T : Type} [Space H R T]

/-- Write `n` copies of `v` starting at `dst` (`memset`). Requires a live writable object even for
`n = 0` (ISO C17 §7.24.1p2). -/
def memset (dst : Ptr R) (v : T) (n : Nat) : M H Unit := fun h =>
  match dst with
  | .null => .error (.ub "memset on a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "memset on a dangling pointer")
    | some a =>
      if Space.ro h r then .error (.ub "memset on a read-only object")
      else if off + n ≤ a.size then
        let a' := Array.ofFn (n := a.size) fun i =>
          if off ≤ i.1 ∧ i.1 < off + n then v else a[i.1]
        .ok ((), Space.modify h r (fun _ => a'))
      else .error (.ub "memset outside its object")

/-- Copy `n` elements from `src` to `dst` (`memmove`, overlap allowed). Requires live pointers even
for `n = 0` (ISO C17 §7.24.1p2). -/
def memmove (dst src : Ptr R) (n : Nat) : M H Unit := fun h =>
  match dst, src with
  | .ref rd od, .ref rs os =>
    match Space.get h rd, Space.get h rs with
    | some ad, some as =>
      if Space.ro h rd then .error (.ub "memmove into a read-only object")
      else if hb : od + n ≤ ad.size ∧ os + n ≤ as.size then
        let ad' := Array.ofFn (n := ad.size) fun i =>
          if h1 : od ≤ i.1 ∧ i.1 < od + n then
            as[os + (i.1 - od)]'(by omega)
          else ad[i.1]
        .ok ((), Space.modify h rd (fun _ => ad'))
      else .error (.ub "memmove outside object bounds")
    | _, _ => .error (.ub "memmove on a dangling pointer")
  | _, _ => .error (.ub "memmove on a null pointer")

/-- Copy `n` non-overlapping elements from `src` to `dst` (`memcpy`). Faults on overlap when `n > 0`
in the same object (ISO C17 §7.24.2.1p2) and on null/dangling pointers even when `n = 0`. -/
def memcpy [DecidableEq R] (dst src : Ptr R) (n : Nat) : M H Unit := fun h =>
  match dst, src with
  | .ref rd od, .ref rs os =>
    if rd = rs ∧ n > 0 ∧ od < os + n ∧ os < od + n then
      .error (.ub "overlapping memcpy")
    else
      memmove dst src n h
  | _, _ => .error (.ub "memcpy on a null pointer")

/-- Compare `n` bytes starting at `p` and `q` (`memcmp`). Requires live pointers even when `n = 0`
(ISO C17 §7.24.1p2). -/
def memcmp (p q : Ptr R) (n : Nat) (cmp : T → T → Int32) : M H Int32 := fun h =>
  match p, q with
  | .ref rp op, .ref rq oq =>
    match Space.get h rp, Space.get h rq with
    | some ap, some aq =>
      if hb : op + n ≤ ap.size ∧ oq + n ≤ aq.size then
        let rec go (i : Nat) (hi : i ≤ n) : Int32 :=
          if hlt : i < n then
            let d := cmp (ap[op + i]'(by omega)) (aq[oq + i]'(by omega))
            if d ≠ 0 then d else go (i + 1) (by omega)
          else 0
        .ok (go 0 (Nat.zero_le n), h)
      else .error (.ub "memcmp outside object bounds")
    | _, _ => .error (.ub "memcmp on a dangling pointer")
  | _, _ => .error (.ub "memcmp on a null pointer")

/-! ### Reusable `*_ok` and strict-UB fault lemmas -/

theorem memset_ok (h : H) (r : R) (off n : Nat) (v : T) (a : Array T)
    (hget : Space.get h r = some a) (hro : Space.ro h r = false) (hhi : off + n ≤ a.size) :
    ∃ h', memset (H := H) (R := R) (T := T) (.ref r off) v n h = .ok ((), h') ∧
      h' = Space.modify h r (fun _ => Array.ofFn (n := a.size) fun i =>
        if off ≤ i.1 ∧ i.1 < off + n then v else a[i.1]) :=
  ⟨_, by simp [memset, hget, hro, hhi], rfl⟩

theorem memmove_ok (h : H) (rd rs : R) (od os n : Nat) (ad as : Array T)
    (hgd : Space.get h rd = some ad) (hgs : Space.get h rs = some as)
    (hro : Space.ro h rd = false) (hd : od + n ≤ ad.size) (hs : os + n ≤ as.size) :
    ∃ h', memmove (H := H) (R := R) (T := T) (.ref rd od) (.ref rs os) n h = .ok ((), h') := by
  simp only [memmove, hgd, hgs, hro, hd, hs, Bool.false_eq_true, ↓reduceIte, and_self, ↓reduceDIte]
  exact ⟨_, rfl⟩

theorem memcpy_ok [DecidableEq R] (h : H) (rd rs : R) (od os n : Nat) (ad as : Array T)
    (hgd : Space.get h rd = some ad) (hgs : Space.get h rs = some as)
    (hro : Space.ro h rd = false) (hd : od + n ≤ ad.size) (hs : os + n ≤ as.size)
    (hdisj : ¬ (rd = rs ∧ n > 0 ∧ od < os + n ∧ os < od + n)) :
    ∃ h', memcpy (H := H) (R := R) (T := T) (.ref rd od) (.ref rs os) n h = .ok ((), h') := by
  simp only [memcpy, hdisj, ↓reduceIte]
  exact memmove_ok h rd rs od os n ad as hgd hgs hro hd hs

theorem null_memset_zero_ub (h : H) (v : T) :
    ∃ msg, memset (H := H) (R := R) (T := T) .null v 0 h = .error (.ub msg) :=
  ⟨_, rfl⟩

theorem null_memcpy_zero_ub [DecidableEq R] (h : H) (src : Ptr R) :
    ∃ msg, memcpy (H := H) (R := R) (T := T) .null src 0 h = .error (.ub msg) :=
  ⟨_, rfl⟩

theorem null_memcmp_zero_ub (h : H) (q : Ptr R) (cmp : T → T → Int32) :
    ∃ msg, memcmp (H := H) (R := R) (T := T) .null q 0 cmp h = .error (.ub msg) :=
  ⟨_, rfl⟩

end libc
end Ptr
end OssProof
