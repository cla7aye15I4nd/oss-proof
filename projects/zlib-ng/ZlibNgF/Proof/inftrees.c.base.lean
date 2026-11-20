import ZlibNgF.ZlibNg.«inftrees.c»

/-!
# `zng_inflate_table`: run lemmas and the heap shape (`ZlibNgF`)

`Wp m h Q`: `m` run on `h` ends without fault, in a value and heap satisfying `Q`. The loop rule `Wp.cwhile`
takes a variant. The heap during `zng_inflate_table` is the caller's heap with the `codes` and `work` arrays of
one `inflate_state` replaced (`setCW`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees

/-! ## Weakest-precondition style runs -/

/-- `m` terminates on `h` without fault, with a result satisfying `Q`. -/
def Wp {α : Type} (m : M α) (h : Heap) (Q : α → Heap → Prop) : Prop :=
  ∃ v h', m h = .ok (v, h') ∧ Q v h'

theorem Wp.of_eq {α : Type} {m : M α} {h : Heap} {Q : α → Heap → Prop} {v : α} {h' : Heap}
    (e : m h = .ok (v, h')) (q : Q v h') : Wp m h Q := ⟨v, h', e, q⟩

@[simp] theorem Wp.pure_iff {α : Type} {a : α} {h : Heap} {Q : α → Heap → Prop} :
    Wp (pure a) h Q ↔ Q a h :=
  ⟨fun ⟨_, _, e, q⟩ => by cases e; exact q, fun q => ⟨a, h, rfl, q⟩⟩

theorem Wp.bind_iff {α β : Type} {m : M α} {f : α → M β} {h : Heap} {Q : β → Heap → Prop} :
    Wp (m >>= f) h Q ↔ Wp m h (fun a h' => Wp (f a) h' Q) := by
  constructor
  · rintro ⟨v, h2, e, q⟩
    rw [bind_app] at e
    cases hm : m h with
    | error err => rw [hm] at e; cases e
    | ok p =>
      obtain ⟨a, h1⟩ := p
      rw [hm] at e
      exact ⟨a, h1, hm, v, h2, e, q⟩
  · rintro ⟨a, h1, e, v, h2, e2, q⟩
    exact ⟨v, h2, by rw [bind_app, e]; exact e2, q⟩

theorem Wp.bind {α β : Type} {m : M α} {f : α → M β} {h : Heap} {Q : β → Heap → Prop}
    (hm : Wp m h (fun a h' => Wp (f a) h' Q)) : Wp (m >>= f) h Q := Wp.bind_iff.2 hm

theorem Wp.mono {α : Type} {m : M α} {h : Heap} {Q R : α → Heap → Prop} (hm : Wp m h Q)
    (hqr : ∀ a h', Q a h' → R a h') : Wp m h R := by
  obtain ⟨v, h', e, q⟩ := hm
  exact ⟨v, h', e, hqr v h' q⟩

theorem Wp.of_ok {α : Type} {m : M α} {h : Heap} {Q : α → Heap → Prop} {v : α}
    (e : m h = .ok (v, h)) (q : Q v h) : Wp m h Q := ⟨v, h, e, q⟩

/-- Loop rule with a natural-number variant. -/
theorem Wp.cwhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (Inv : Nat → σ → Heap → Prop) (Q : σ → Heap → Prop)
    (hstep : ∀ n s h, Inv n s h → Wp (cond s) h (fun r h1 =>
      (r.1 = true → Wp (body r.2) h1 (fun s2 h2 => ∃ n', n' < n ∧ Inv n' s2 h2)) ∧ (r.1 = false → Q r.2 h1)))
    {n : Nat} {s : σ} {h : Heap} (hI : Inv n s h) (hn : n < fuel) : Wp (C.cwhile cond body s) h Q := by
  unfold C.cwhile
  suffices H : ∀ k n s h, Inv n s h → n < k → Wp (cwhile.go cond body k s) h Q from H fuel n s h hI hn
  intro k
  induction k with
  | zero => intro n s h _ hk; omega
  | succ k ih =>
    intro n s h hI hk
    obtain ⟨⟨c, s1⟩, h1, e1, q1⟩ := hstep n s h hI
    unfold cwhile.go
    rw [Wp.bind_iff]
    refine ⟨(c, s1), h1, e1, ?_⟩
    cases c with
    | true =>
      obtain ⟨s2, h2, e2, n', hn', hI2⟩ := q1.1 rfl
      simp only [ite_true]
      rw [Wp.bind_iff]
      exact ⟨s2, h2, e2, ih n' s2 h2 hI2 (by omega)⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false, Wp.pure_iff]
      exact q1.2 rfl

/-- Loop rule for a loop whose condition is pure. -/
theorem Wp.cwhile_pure {σ : Type} {c : σ → Bool} {body : σ → M σ}
    (Inv : Nat → σ → Heap → Prop) (Q : σ → Heap → Prop)
    (hstep : ∀ n s h, Inv n s h → (c s = true → Wp (body s) h (fun s2 h2 => ∃ n', n' < n ∧ Inv n' s2 h2)) ∧
      (c s = false → Q s h))
    {n : Nat} {s : σ} {h : Heap} (hI : Inv n s h) (hn : n < fuel) :
    Wp (C.cwhile (fun s => pure (c s, s)) body s) h Q :=
  Wp.cwhile Inv Q (fun n s h hI => by rw [Wp.pure_iff]; exact hstep n s h hI) hI hn

/-! ## Primitive operations -/

theorem shl32_ok {x n : UInt32} (hn : n < 32) : shl32 x n = pure (x <<< n) := by
  simp [shl32, hn]

theorem shr32_ok {x n : UInt32} (hn : n < 32) : shr32 x n = pure (x >>> n) := by
  simp [shr32, hn]

theorem chkI32_ok {v : Int} (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) : chkI32 v = pure (Int32.ofInt v) := by
  simp [chkI32, h1, h2]

theorem aget_ok {α : Type} [Inhabited α] {a : Array α} {i : Nat} (hi : i < a.size) : aget a i = pure a[i] := by
  simp [aget, hi]

theorem aset_ok {α : Type} {a : Array α} {i : Nat} {v : α} (hi : i < a.size) : aset a i v = pure (a.set! i v) := by
  simp [aset, hi]

section ptr
variable {R T : Type} [Space Heap R T]

theorem add_ok {r : R} {off : Nat} {k : Int} {a : Array T} {h : Heap} (hg : Space.get h r = some a)
    (h0 : off ≤ a.size) (h1 : 0 ≤ (off : Int) + k) (h2 : (off : Int) + k ≤ a.size) :
    Ptr.add (.ref r off) k h = .ok (.ref r ((off : Int) + k).toNat, h) := by
  simp [Ptr.add, hg, h0, h1, h2]

theorem load_ok {r : R} {off : Nat} {a : Array T} {h : Heap} (hg : Space.get h r = some a)
    (hk : off < a.size) : Ptr.load (.ref r off) h = .ok (a[off], h) := by
  simp [Ptr.load, hg, hk]

theorem index_ok {r : R} {off : Nat} {k : Int} {a : Array T} {h : Heap} (hg : Space.get h r = some a)
    (h0 : off ≤ a.size) (h1 : 0 ≤ (off : Int) + k) (h2 : (off : Int) + k < a.size) :
    Ptr.index (.ref r off) k h = .ok (a[((off : Int) + k).toNat]'(by omega), h) := by
  show (Ptr.add (.ref r off) k >>= fun p => Ptr.load p) h = _
  rw [bind_app, add_ok hg h0 h1 (by omega)]
  exact load_ok hg (by omega)

theorem index_nat [Inhabited T] {r : R} {off i : Nat} {a : Array T} {h : Heap} (hg : Space.get h r = some a)
    (hi : off + i < a.size) : Ptr.index (.ref r off) (Int.ofNat i) h = .ok (a[off + i]!, h) := by
  rw [index_ok hg (by omega) (by simp; omega) (by simp; omega)]
  congr
  rw [getElem!_pos a (off + i) hi]
  congr 1

theorem store_ok {r : R} {off : Nat} {v : T} {a : Array T} {h : Heap} (hg : Space.get h r = some a)
    (hro : Space.ro h r = false) (hk : off < a.size) :
    Ptr.store (.ref r off) v h = .ok ((), Space.modify h r (fun a => a.set! off v)) := by
  simp [Ptr.store, hg, hro, hk]

end ptr

/-! ## The heap during `zng_inflate_table` -/

theorem upd_upd {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v w : α) : upd (upd t k v) k w = upd t k w := by
  unfold upd Tbl.set
  by_cases hk : k < t.arr.size
  · simp [hk, Array.set!_eq_setIfInBounds]
  · simp only [hk, ite_false, Array.size_append, Array.size_push, Array.size_replicate, Array.set!_eq_setIfInBounds]
    have hk' : t.arr.size + (k - t.arr.size) = k := by omega
    rw [hk']
    simp only [Nat.lt_add_one, ↓reduceIte]
    congr 1
    apply Array.ext_getElem?
    intro j
    simp only [Array.getElem?_setIfInBounds, Array.getElem?_append, Array.getElem?_push, Array.size_replicate,
      Array.size_append, Array.size_push, hk']
    by_cases e : k = j
    · subst e; simp
    · have e' : ¬ j = k := fun x => e x.symm
      simp [e, e']

theorem upd_self {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) (hv : t k = v) (hd : v ≠ default) :
    upd t k v = t := by
  have hk : k < t.arr.size := Tbl.lt_size_of_get_ne t k (by rw [show t.get k = t k from rfl, hv]; exact hd)
  unfold upd Tbl.set
  simp only [hk, ite_true]
  cases t with
  | mk arr =>
    congr 1
    apply Array.ext_getElem?
    intro j
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split
    · rename_i e
      subst e
      have : (Tbl.mk arr).get k = v := hv
      rw [Tbl.get_eq] at this
      simp only at this hk
      rw [Array.getElem?_eq_getElem hk] at this ⊢
      simp at this
      rw [this]
    · rfl

/-- The caller's heap `h` with the `codes` and `work` arrays of the `inflate_state` `s` of block `b` replaced. -/
def setCW (h : Heap) (b : Nat) (s : InflateState) (cs : Array Code) (w : Array UInt16) : Heap :=
  { h with istates := upd h.istates b (some { s with codes := cs, work := w }) }

/-- `b` holds the live state `s` in `h`. -/
structure LiveSt (h : Heap) (b : Nat) (s : InflateState) : Prop where
  bytes : (h.bytes b).isSome
  st : h.istates b = some s

theorem LiveSt.istate {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) : h.istate b = some s := by
  unfold Heap.istate
  cases e : h.bytes b with
  | none => have := hl.bytes; rw [e] at this; cases this
  | some _ => exact hl.st

theorem setCW_istate {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) (cs : Array Code)
    (w : Array UInt16) : (setCW h b s cs w).istate b = some { s with codes := cs, work := w } := by
  unfold Heap.istate setCW
  cases e : h.bytes b with
  | none => have := hl.bytes; rw [e] at this; cases this
  | some _ => simp

theorem setCW_self {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) :
    setCW h b s s.codes s.work = h := by
  unfold setCW
  have : ({ s with codes := s.codes, work := s.work } : InflateState) = s := rfl
  rw [this, upd_self _ _ _ hl.st (by simp [default])]

theorem get_lens {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) (cs : Array Code)
    (w : Array UInt16) : Space.get (setCW h b s cs w) (WRef.lens b) = some s.lens := by
  show Heap.getWords _ _ = _
  simp [Heap.getWords, setCW_istate hl]

theorem get_work {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) (cs : Array Code)
    (w : Array UInt16) : Space.get (setCW h b s cs w) (WRef.work b) = some w := by
  show Heap.getWords _ _ = _
  simp [Heap.getWords, setCW_istate hl]

theorem get_codes {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) (cs : Array Code)
    (w : Array UInt16) : Space.get (setCW h b s cs w) (CodeRef.codes b) = some cs := by
  show Heap.getCodes _ _ = _
  simp [Heap.getCodes, setCW_istate hl]

theorem modify_work {h : Heap} {b : Nat} {s : InflateState} (cs : Array Code)
    (w : Array UInt16) (f : Array UInt16 → Array UInt16) :
    Space.modify (setCW h b s cs w) (WRef.work b) f = setCW h b s cs (f w) := by
  show Heap.modifyWords _ _ _ = _
  unfold Heap.modifyWords setCW
  simp only
  rw [Tbl.modify_opt _ b _ { s with codes := cs, work := w } (by simp), upd_upd]

theorem modify_codes {h : Heap} {b : Nat} {s : InflateState} (cs : Array Code)
    (w : Array UInt16) (f : Array Code → Array Code) :
    Space.modify (setCW h b s cs w) (CodeRef.codes b) f = setCW h b s (f cs) w := by
  show Heap.modifyCodes _ _ _ = _
  unfold Heap.modifyCodes setCW
  simp only
  rw [Tbl.modify_opt _ b _ { s with codes := cs, work := w } (by simp), upd_upd]

/-- Store into the `codes` array. -/
theorem store_codes {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) {cs : Array Code}
    {w : Array UInt16} {i : Nat} (hi : i < cs.size) (v : Code) :
    Ptr.store (.ref (CodeRef.codes b) i) v (setCW h b s cs w) = .ok ((), setCW h b s (cs.set! i v) w) := by
  rw [store_ok (get_codes hl cs w) rfl hi, modify_codes]

/-- Store into the `work` array. -/
theorem store_work {h : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h b s) {cs : Array Code}
    {w : Array UInt16} {i : Nat} (hi : i < w.size) (v : UInt16) :
    Ptr.store (.ref (WRef.work b) i) v (setCW h b s cs w) = .ok ((), setCW h b s cs (w.set! i v)) := by
  rw [store_ok (get_work hl cs w) rfl hi, modify_work]

end ZlibNgF.Proof.Inftrees
