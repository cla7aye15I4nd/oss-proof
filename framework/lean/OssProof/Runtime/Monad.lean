import OssProof.Runtime.Space

/-!
# Parameterized runtime monad, loops, and checked ISO C17 arithmetic (`OssProof.Runtime.Monad`)

Provides:
- `M H α := H → Except Fault (α × H)` with `Monad` instance;
- fuel-bounded structured loops (`cwhile`, `cdoWhile`, `cloop`, `cfor`) with both exact-step and
  decreasing-measure termination lemmas;
- checked ISO C17 LP64 signed integer arithmetic and shift helpers (`chkI32`, `chkI64`, `shl32`,
  `shr32`, `shl64`, `shr64`).
-/

namespace OssProof

abbrev M (H : Type) (α : Type) : Type := H → Except Fault (α × H)

namespace M

def pure {H α : Type} (a : α) : M H α := fun h => .ok (a, h)

def bind {H α β : Type} (m : M H α) (f : α → M H β) : M H β := fun h =>
  match m h with
  | .ok (a, h') => f a h'
  | .error e => .error e

instance {H : Type} : Monad (M H) where
  pure := M.pure
  bind := M.bind

def get {H : Type} : M H H := fun h => .ok (h, h)

def set {H : Type} (h' : H) : M H Unit := fun _ => .ok ((), h')

def modify {H : Type} (f : H → H) : M H Unit := fun h => .ok ((), f h)

def fail {H α : Type} (e : Fault) : M H α := fun _ => .error e

def ub {H α : Type} (msg : String) : M H α := fail (.ub msg)

def guardUB {H : Type} (cond : Bool) (msg : String := "undefined behaviour") : M H Unit :=
  if cond then pure () else ub msg

@[simp] theorem pure_apply {H α : Type} (a : α) (h : H) :
    (Pure.pure a : M H α) h = .ok (a, h) := rfl

@[simp] theorem bind_apply {H α β : Type} (m : M H α) (f : α → M H β) (h : H) :
    (m >>= f) h = match m h with | .ok (a, h') => f a h' | .error e => .error e := rfl

@[simp] theorem get_apply {H : Type} (h : H) : M.get h = .ok (h, h) := rfl
@[simp] theorem set_apply {H : Type} (h h' : H) : M.set h' h = .ok ((), h') := rfl
@[simp] theorem modify_apply {H : Type} (f : H → H) (h : H) : M.modify f h = .ok ((), f h) := rfl

end M

/-! ## Structured fuel-bounded loops -/

inductive LoopStep (σ ρ : Type) where
  | cont (s : σ)
  | brk (s : σ)
  | ret (r : ρ)

def cwhile {H σ : Type} (fuel : Nat) (init : σ)
    (cond : σ → M H Bool) (body : σ → M H σ) : M H σ :=
  match fuel with
  | 0 => M.fail .fuel
  | n + 1 => do
    if ← cond init then
      let next ← body init
      cwhile n next cond body
    else
      pure init

def cdoWhile {H σ : Type} (fuel : Nat) (init : σ)
    (body : σ → M H σ) (cond : σ → M H Bool) : M H σ :=
  match fuel with
  | 0 => M.fail .fuel
  | n + 1 => do
    let next ← body init
    if ← cond next then
      cdoWhile n next body cond
    else
      pure next

def cloop {H σ ρ : Type} (fuel : Nat) (init : σ)
    (step : σ → M H (LoopStep σ ρ)) : M H (Sum σ ρ) :=
  match fuel with
  | 0 => M.fail .fuel
  | n + 1 => do
    match ← step init with
    | .cont s' => cloop n s' step
    | .brk s' => pure (.inl s')
    | .ret r => pure (.inr r)

def cfor {H σ ρ : Type} (fuel : Nat) (init : σ)
    (cond : σ → M H Bool) (body : σ → M H (LoopStep σ ρ)) : M H (Sum σ ρ) :=
  cloop fuel init fun s => do
    if ← cond s then
      body s
    else
      pure (.brk s)

/-! ### Decreasing-measure termination lemmas (shared once across all projects) -/

theorem cwhile_measure {H σ : Type} (I : σ → H → Prop) (μ : σ → H → Nat)
    (cond : σ → M H Bool) (body : σ → M H σ) (Q : σ → H → Prop)
    (hstep : ∀ s h, I s h →
      ∃ c h1, cond s h = .ok (c, h1) ∧
        (c = true → ∃ s' h', body s h1 = .ok (s', h') ∧ I s' h' ∧ μ s' h' < μ s h) ∧
        (c = false → Q s h1)) :
    ∀ fuel s h, I s h → μ s h < fuel →
      ∃ s' h', cwhile fuel s cond body h = .ok (s', h') ∧ Q s' h' := by
  intro fuel
  induction fuel with
  | zero => intro s h _ hlt; omega
  | succ n ih =>
    intro s h hI hlt
    rcases hstep s h hI with ⟨c, h1, hcond, htrue, hfalse⟩
    cases c with
    | false =>
      exact ⟨s, h1, by simp [cwhile, hcond], hfalse rfl⟩
    | true =>
      rcases htrue rfl with ⟨s1, h2, hbody, hI1, hdec⟩
      rcases ih s1 h2 hI1 (by omega) with ⟨sf, hf, hrun, hQ⟩
      exact ⟨sf, hf, by simp [cwhile, hcond, hbody, hrun], hQ⟩

theorem cloop_measure {H σ ρ : Type} (I : σ → H → Prop) (μ : σ → H → Nat)
    (step : σ → M H (LoopStep σ ρ)) (Q : Sum σ ρ → H → Prop)
    (hstep : ∀ s h, I s h →
      ∃ r h', step s h = .ok (r, h') ∧
        match r with
        | .cont s' => I s' h' ∧ μ s' h' < μ s h
        | .brk s' => Q (.inl s') h'
        | .ret rv => Q (.inr rv) h') :
    ∀ fuel s h, I s h → μ s h < fuel →
      ∃ res h', cloop fuel s step h = .ok (res, h') ∧ Q res h' := by
  intro fuel
  induction fuel with
  | zero => intro s h _ hlt; omega
  | succ n ih =>
    intro s h hI hlt
    rcases hstep s h hI with ⟨r, h1, hst, hpost⟩
    cases r with
    | cont s' =>
      rcases hpost with ⟨hI', hdec⟩
      rcases ih s' h1 hI' (by omega) with ⟨res, hf, hrun, hQ⟩
      exact ⟨res, hf, by simp [cloop, hst, hrun], hQ⟩
    | brk s' =>
      exact ⟨.inl s', h1, by simp [cloop, hst], hpost⟩
    | ret rv =>
      exact ⟨.inr rv, h1, by simp [cloop, hst], hpost⟩

theorem cdoWhile_measure {H σ : Type} (I : σ → H → Prop) (μ : σ → H → Nat)
    (body : σ → M H σ) (cond : σ → M H Bool) (Q : σ → H → Prop)
    (hstep : ∀ s h, I s h →
      ∃ s1 h1, body s h = .ok (s1, h1) ∧
        ∃ c h2, cond s1 h1 = .ok (c, h2) ∧
          (c = true → I s1 h2 ∧ μ s1 h2 < μ s h) ∧
          (c = false → Q s1 h2)) :
    ∀ fuel s h, I s h → μ s h < fuel →
      ∃ s' h', cdoWhile fuel s body cond h = .ok (s', h') ∧ Q s' h' := by
  intro fuel
  induction fuel with
  | zero => intro s h _ hlt; omega
  | succ n ih =>
    intro s h hI hlt
    rcases hstep s h hI with ⟨s1, h1, hbody, c, h2, hcond, htrue, hfalse⟩
    cases c with
    | false =>
      exact ⟨s1, h2, by simp [cdoWhile, hbody, hcond], hfalse rfl⟩
    | true =>
      rcases htrue rfl with ⟨hI1, hdec⟩
      rcases ih s1 h2 hI1 (by omega) with ⟨sf, hf, hrun, hQ⟩
      exact ⟨sf, hf, by simp [cdoWhile, hbody, hcond, hrun], hQ⟩

/-! ## Checked ISO C17 LP64 signed arithmetic and shifts (§6.5p5, §6.5.5, §6.5.7) -/

def I32_MIN : Int := -(2 ^ 31)
def I32_MAX : Int := 2 ^ 31 - 1
def I64_MIN : Int := -(2 ^ 63)
def I64_MAX : Int := 2 ^ 63 - 1

def chkI32 {H : Type} (v : Int) : M H Int32 :=
  if I32_MIN ≤ v ∧ v ≤ I32_MAX then pure (Int32.ofInt v)
  else M.ub "signed 32-bit integer overflow"

def chkI64 {H : Type} (v : Int) : M H Int64 :=
  if I64_MIN ≤ v ∧ v ≤ I64_MAX then pure (Int64.ofInt v)
  else M.ub "signed 64-bit integer overflow"

def addI32 {H : Type} (a b : Int32) : M H Int32 := chkI32 (a.toInt + b.toInt)
def subI32 {H : Type} (a b : Int32) : M H Int32 := chkI32 (a.toInt - b.toInt)
def mulI32 {H : Type} (a b : Int32) : M H Int32 := chkI32 (a.toInt * b.toInt)

def divI32 {H : Type} (a b : Int32) : M H Int32 :=
  if b.toInt = 0 then M.ub "division by zero"
  else if a.toInt = I32_MIN ∧ b.toInt = -1 then M.ub "INT32_MIN / -1 overflow"
  else pure (a / b)

def modI32 {H : Type} (a b : Int32) : M H Int32 :=
  if b.toInt = 0 then M.ub "modulo by zero"
  else if a.toInt = I32_MIN ∧ b.toInt = -1 then M.ub "INT32_MIN % -1 overflow"
  else pure (a % b)

def addI64 {H : Type} (a b : Int64) : M H Int64 := chkI64 (a.toInt + b.toInt)
def subI64 {H : Type} (a b : Int64) : M H Int64 := chkI64 (a.toInt - b.toInt)
def mulI64 {H : Type} (a b : Int64) : M H Int64 := chkI64 (a.toInt * b.toInt)

def shlU32 {H : Type} (x : UInt32) (s : Int) : M H UInt32 :=
  if 0 ≤ s ∧ s < 32 then pure (x <<< UInt32.ofNat s.toNat)
  else M.ub "invalid 32-bit shift count"

def shrU32 {H : Type} (x : UInt32) (s : Int) : M H UInt32 :=
  if 0 ≤ s ∧ s < 32 then pure (x >>> UInt32.ofNat s.toNat)
  else M.ub "invalid 32-bit shift count"

def shlU64 {H : Type} (x : UInt64) (s : Int) : M H UInt64 :=
  if 0 ≤ s ∧ s < 64 then pure (x <<< UInt64.ofNat s.toNat)
  else M.ub "invalid 64-bit shift count"

def shrU64 {H : Type} (x : UInt64) (s : Int) : M H UInt64 :=
  if 0 ≤ s ∧ s < 64 then pure (x >>> UInt64.ofNat s.toNat)
  else M.ub "invalid 64-bit shift count"

def shlI32 {H : Type} (x : Int32) (s : Int) : M H Int32 :=
  if 0 ≤ s ∧ s < 32 ∧ 0 ≤ x.toInt then
    chkI32 (x.toInt * (2 ^ s.toNat : Nat))
  else
    M.ub "invalid signed 32-bit left shift"

end OssProof
