import MozjpegF.Runtime.Heap

/-!
# Runtime monad, faults, and loops (`MozjpegF`)

Every undefined behaviour reachable in ISO C17 raises `Fault.ub`.
Defined `libjpeg` `ERREXIT*` non-local exits (`error_exit` / `longjmp`) return `JpegRes.errExit` cleanly
after updating `cinfo->err` so they remain distinct from C undefined behaviour.
-/

set_option autoImplicit false

namespace C

/-- Why a C computation did not produce a value. -/
inductive Fault where
  | ub (what : String)
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-- Outcome of a `libjpeg` API function supporting `ERREXIT*` (`longjmp` error unwind). -/
inductive JpegRes (α : Type) where
  | ok (val : α)
  | errExit (code : Int32)
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

@[simp] theorem pure_bind_m {α β : Type} (a : α) (f : α → M β) :
    ((pure a : M α) >>= f) = f a := rfl

@[simp] theorem bind_assoc_m {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  funext h; simp [bind]; cases m h <;> rfl

/-- `m` terminates on `h` with value `v` and leaves `h` unchanged. -/
def OkOn {α : Type} (h : Heap) (m : M α) (v : α) : Prop :=
  run m h = .ok (v, h)

theorem OkOn.pure {α : Type} (h : Heap) (v : α) : OkOn h (Pure.pure v) v := rfl

theorem OkOn.bind {α β : Type} {h : Heap} {m : M α} {f : α → M β} {x : α} {y : β}
    (hm : OkOn h m x) (hf : OkOn h (f x) y) : OkOn h (m >>= f) y := by
  unfold OkOn at *
  rw [run_bind, hm]
  exact hf

end C
