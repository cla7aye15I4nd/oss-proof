import ZlibNgF.Runtime.Heap

/-!
# Runtime monad, faults, and loops (`ZlibNgF`)

Every undefined behaviour reachable in ISO C17 raises `Fault.ub`.
-/

set_option autoImplicit false

namespace C

/-- Why a C computation did not produce a value. -/
inductive Fault where
  | ub (what : String)
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-- State-and-fault monad over `Heap`. -/
def M (α : Type) : Type := Heap → Except Fault (α × Heap)

instance : Monad M where
  pure a := fun h => .ok (a, h)
  bind m f := fun h => match m h with
    | .ok (a, h') => f a h'
    | .error e => .error e

/-- Raise ISO C17 undefined behaviour. -/
def ub {α : Type} (what : String) : M α := fun _ => .error (.ub what)

/-- Execute `m` on `h`. -/
def run {α : Type} (m : M α) (h : Heap) : Except Fault (α × Heap) := m h

/-- Loop fuel bound on LP64 address spaces. -/
def fuel : Nat := 2 ^ 64

/-- `while (cond) body` with condition side effects preserved on the final false evaluation. -/
def cwhile {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ) (s : σ) : M σ :=
  go fuel s
where
  go : Nat → σ → M σ
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let (c, s) ← cond s
      if c then go n (← body s) else pure s

/-- `do body while (cond)`. -/
def cdoWhile {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ)) (s : σ) : M σ :=
  go fuel s
where
  go : Nat → σ → M σ
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let s ← body s
      let (c, s) ← cond s
      if c then go n s else pure s

@[simp] theorem bind_app {α β : Type} (m : M α) (f : α → M β) (h : Heap) :
    (m >>= f) h = match m h with | .ok (a, h') => f a h' | .error e => .error e := rfl

@[simp] theorem pure_app {α : Type} (a : α) (h : Heap) : (pure a : M α) h = .ok (a, h) := rfl

@[simp] theorem run_pure {α : Type} (a : α) (h : Heap) : run (pure a) h = .ok (a, h) := rfl

@[simp] theorem run_bind {α β : Type} (m : M α) (f : α → M β) (h : Heap) :
    run (m >>= f) h = match run m h with | .ok (a, h') => run (f a) h' | .error e => .error e := rfl

/-- `m` terminates on `h` with value `v` and leaves `h` unchanged. -/
def OkOn {α : Type} (h : Heap) (m : M α) (v : α) : Prop :=
  run m h = .ok (v, h)

theorem OkOn.pure {α : Type} (h : Heap) (v : α) : OkOn h (Pure.pure v) v := rfl

theorem OkOn.bind {α β : Type} {h : Heap} {m : M α} {f : α → M β} {x : α} {y : β}
    (hm : OkOn h m x) (hf : OkOn h (f x) y) : OkOn h (m >>= f) y := by
  unfold OkOn at *
  rw [run_bind, hm]
  exact hf

theorem OkOn.bind_ex {α β : Type} {h : Heap} {m : M α} {f : α → M β} {R : α → Prop} {y : β}
    (hm : ∃ x, OkOn h m x ∧ R x) (hf : ∀ x, R x → OkOn h (f x) y) : OkOn h (m >>= f) y := by
  obtain ⟨x, hx, hr⟩ := hm
  exact OkOn.bind hx (hf x hr)

theorem cwhile_go_ok {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (cond s) (true, s1) ∧ OkOn h (body s1) s2 ∧ P k s2)
    (hstop : ∀ s, P 0 s → ∃ s1, OkOn h (cond s) (false, s1) ∧ Q s1) :
    ∀ k n s, P k s → k < n → ∃ s', OkOn h (cwhile.go cond body n s) s' ∧ Q s' := by
  intro k
  induction k with
  | zero =>
    intro n s hP hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, hc, hQ⟩ := hstop s hP
    refine ⟨s1, ?_, hQ⟩
    unfold OkOn at *
    simp [cwhile.go, hc]
  | succ k ih =>
    intro n s hP hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hc, hb, hP2⟩ := hstep k s hP
    obtain ⟨s', hgo, hQ⟩ := ih m s2 hP2 (by omega)
    refine ⟨s', ?_, hQ⟩
    unfold OkOn at *
    simp [cwhile.go, hc, hb, hgo]

theorem cwhile_ok {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (cond s) (true, s1) ∧ OkOn h (body s1) s2 ∧ P k s2)
    (hstop : ∀ s, P 0 s → ∃ s1, OkOn h (cond s) (false, s1) ∧ Q s1)
    {k : Nat} {s : σ} (hP : P k s) (hk : k < fuel) :
    ∃ s', OkOn h (cwhile cond body s) s' ∧ Q s' :=
  cwhile_go_ok P Q hstep hstop k fuel s hP hk

theorem cdoWhile_go_ok {σ : Type} {h : Heap} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (true, s2) ∧ P k s2)
    (hlast : ∀ s, P 0 s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (false, s2) ∧ Q s2) :
    ∀ k n s, P k s → k < n → ∃ s', OkOn h (cdoWhile.go body cond n s) s' ∧ Q s' := by
  intro k
  induction k with
  | zero =>
    intro n s hP hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hb, hc, hQ⟩ := hlast s hP
    refine ⟨s2, ?_, hQ⟩
    unfold OkOn at *
    simp [cdoWhile.go, hb, hc]
  | succ k ih =>
    intro n s hP hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s1, s2, hb, hc, hP2⟩ := hstep k s hP
    obtain ⟨s', hgo, hQ⟩ := ih m s2 hP2 (by omega)
    refine ⟨s', ?_, hQ⟩
    unfold OkOn at *
    simp [cdoWhile.go, hb, hc, hgo]

theorem cdoWhile_ok {σ : Type} {h : Heap} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (P : Nat → σ → Prop) (Q : σ → Prop)
    (hstep : ∀ k s, P (k + 1) s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (true, s2) ∧ P k s2)
    (hlast : ∀ s, P 0 s → ∃ s1 s2, OkOn h (body s) s1 ∧ OkOn h (cond s1) (false, s2) ∧ Q s2)
    {k : Nat} {s : σ} (hP : P k s) (hk : k < fuel) :
    ∃ s', OkOn h (cdoWhile body cond s) s' ∧ Q s' :=
  cdoWhile_go_ok P Q hstep hlast k fuel s hP hk

end C
