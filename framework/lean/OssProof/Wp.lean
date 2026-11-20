import OssProof.Runtime.Libc

/-!
# Compositional Weakest-Precondition Calculus (`OssProof.Wp`)

Shared, heap-parametric weakest-precondition judgement `Wp m h Q` over `M H α`, distilling the
compact calculus that achieved 5.5× proof-to-translation ratio and 0 `maxHeartbeats` overrides:
- sequencing (`bind`, `bind'`, `map`, `pure`, `ite`, `and`, `mono`),
- decreasing-measure structured loops (`cwhile`, `cloop`, `cfor`, `cdoWhile`),
- strict ISO C17 pointer and libc rules (`ptr_add`, `ptr_load`, `ptr_index`, `ptr_store`,
  `ptr_diff`, `ptr_lt`, `ptr_memset`, `ptr_memmove`, `ptr_memcpy`).
-/

namespace OssProof

/-- `Wp m h Q`: running `m` in heap `h` succeeds without fault (`Fault.ub`, `oom`, `fuel`) and
its result `(a, h')` satisfies `Q a h'`. -/
def Wp {H α : Type} (m : M H α) (h : H) (Q : α → H → Prop) : Prop :=
  ∃ a h', m h = .ok (a, h') ∧ Q a h'

namespace Wp

variable {H α β : Type}

theorem mono {m : M H α} {h : H} {Q Q' : α → H → Prop}
    (hw : Wp m h Q) (himp : ∀ a h', Q a h' → Q' a h') : Wp m h Q' := by
  rcases hw with ⟨a, h', he, hq⟩
  exact ⟨a, h', he, himp a h' hq⟩

theorem pure {a : α} {h : H} {Q : α → H → Prop} (hq : Q a h) :
    Wp (Pure.pure a : M H α) h Q :=
  ⟨a, h, rfl, hq⟩

theorem bind {m : M H α} {f : α → M H β} {h : H} {Q : β → H → Prop}
    (hm : Wp m h (fun a h' => Wp (f a) h' Q)) : Wp (m >>= f) h Q := by
  rcases hm with ⟨a, h', he, hq⟩
  rcases hq with ⟨b, h'', he', hq'⟩
  exact ⟨b, h'', by simp only [M.bind_apply, he, he'], hq'⟩

/-- Sequencing with an explicit intermediate postcondition `R`. -/
theorem bind' {m : M H α} {f : α → M H β} {h : H} {Q : β → H → Prop}
    (R : α → H → Prop) (hm : Wp m h R)
    (hf : ∀ a h', R a h' → Wp (f a) h' Q) : Wp (m >>= f) h Q :=
  bind (mono hm hf)

theorem map {m : M H α} {f : α → β} {h : H} {Q : β → H → Prop}
    (hm : Wp m h (fun a h' => Q (f a) h')) : Wp (f <$> m) h Q := by
  rcases hm with ⟨a, h', he, hq⟩
  exact ⟨f a, h', by simp [Functor.map, M.bind, M.pure, he], hq⟩

theorem get {h : H} {Q : H → H → Prop} (hq : Q h h) : Wp M.get h Q :=
  ⟨h, h, rfl, hq⟩

theorem set {h h1 : H} {Q : Unit → H → Prop} (hq : Q () h1) : Wp (M.set h1) h Q :=
  ⟨(), h1, rfl, hq⟩

theorem modify {h : H} {f : H → H} {Q : Unit → H → Prop} (hq : Q () (f h)) :
    Wp (M.modify f) h Q :=
  ⟨(), f h, rfl, hq⟩

theorem guardUB {c : Bool} {msg : String} {h : H} {Q : Unit → H → Prop}
    (hc : c = true) (hq : Q () h) : Wp (M.guardUB c msg) h Q := by
  subst hc
  exact pure hq

theorem ite {c : Prop} [Decidable c] {t e : M H α} {h : H} {Q : α → H → Prop}
    (ht : c → Wp t h Q) (he : ¬ c → Wp e h Q) : Wp (if c then t else e) h Q := by
  split
  · exact ht ‹_›
  · exact he ‹_›

/-- Join two independent `Wp` judgements for the same computation and initial heap. -/
theorem and {m : M H α} {h : H} {Q Q' : α → H → Prop}
    (h1 : Wp m h Q) (h2 : Wp m h Q') : Wp m h (fun a h' => Q a h' ∧ Q' a h') := by
  rcases h1 with ⟨a, h', he, hq⟩
  rcases h2 with ⟨a2, h2', he2, hq2⟩
  rw [he] at he2
  cases he2
  exact ⟨a, h', he, hq, hq2⟩

/-! ## Structured loop rules -/

theorem cwhile {σ : Type} {fuel : Nat} {init : σ} {cond : σ → M H Bool} {body : σ → M H σ}
    {h : H} {Q : σ → H → Prop}
    (I : σ → H → Prop) (μ : σ → H → Nat)
    (hI : I init h) (hμ : μ init h < fuel)
    (hstep : ∀ s h, I s h → Wp (cond s) h (fun c h1 =>
      if c then Wp (body s) h1 (fun s' h' => I s' h' ∧ μ s' h' < μ s h)
      else Q s h1)) :
    Wp (OssProof.cwhile fuel init cond body) h Q := by
  refine cwhile_measure I μ cond body Q ?_ fuel init h hI hμ
  intro s h hs
  rcases hstep s h hs with ⟨c, h1, hcond, hpost⟩
  refine ⟨c, h1, hcond, ?_, ?_⟩
  · intro ht
    subst ht
    simpa [Wp] using hpost
  · intro hf
    subst hf
    simpa [Wp] using hpost

theorem cloop {σ ρ : Type} {fuel : Nat} {init : σ} {step : σ → M H (LoopStep σ ρ)}
    {h : H} {Q : Sum σ ρ → H → Prop}
    (I : σ → H → Prop) (μ : σ → H → Nat)
    (hI : I init h) (hμ : μ init h < fuel)
    (hstep : ∀ s h, I s h → Wp (step s) h (fun r h' =>
      match r with
      | .cont s' => I s' h' ∧ μ s' h' < μ s h
      | .brk s' => Q (.inl s') h'
      | .ret rv => Q (.inr rv) h')) :
    Wp (OssProof.cloop fuel init step) h Q :=
  cloop_measure I μ step Q hstep fuel init h hI hμ

theorem cfor {σ ρ : Type} {fuel : Nat} {init : σ}
    {cond : σ → M H Bool} {body : σ → M H (LoopStep σ ρ)}
    {h : H} {Q : Sum σ ρ → H → Prop}
    (I : σ → H → Prop) (μ : σ → H → Nat)
    (hI : I init h) (hμ : μ init h < fuel)
    (hstep : ∀ s h, I s h → Wp (cond s) h (fun c h1 =>
      if c then
        Wp (body s) h1 (fun r h' =>
          match r with
          | .cont s' => I s' h' ∧ μ s' h' < μ s h
          | .brk s' => Q (.inl s') h'
          | .ret rv => Q (.inr rv) h')
      else Q (.inl s) h1)) :
    Wp (OssProof.cfor fuel init cond body) h Q := by
  unfold OssProof.cfor
  refine cloop I μ hI hμ ?_
  intro s h hIs
  refine bind (mono (hstep s h hIs) ?_)
  intro c h1 hc
  cases c with
  | true => simpa using hc
  | false => exact pure (by simpa using hc)

theorem cdoWhile {σ : Type} {fuel : Nat} {init : σ}
    {body : σ → M H σ} {cond : σ → M H Bool} {h : H} {Q : σ → H → Prop}
    (I : σ → H → Prop) (μ : σ → H → Nat)
    (hI : I init h) (hμ : μ init h < fuel)
    (hstep : ∀ s h, I s h → Wp (body s) h (fun s1 h1 =>
      Wp (cond s1) h1 (fun c h2 =>
        if c then I s1 h2 ∧ μ s1 h2 < μ s h else Q s1 h2))) :
    Wp (OssProof.cdoWhile fuel init body cond) h Q := by
  refine cdoWhile_measure I μ body cond Q ?_ fuel init h hI hμ
  intro s h hs
  rcases hstep s h hs with ⟨s1, h1, hbody, c, h2, hcond, hpost⟩
  refine ⟨s1, h1, hbody, c, h2, hcond, ?_, ?_⟩
  · intro ht; subst ht; simpa using hpost
  · intro hf; subst hf; simpa using hpost

/-! ## Strict pointer and libc `Wp` rules -/

section ptr
variable {R T : Type} [Space H R T]

theorem ptr_add {r : R} {off : Nat} {k : Int} {h : H} {a : Array T} {Q : Ptr R → H → Prop}
    (hget : Space.get h r = some a)
    (hoff : off ≤ a.size) (hlo : 0 ≤ (off : Int) + k) (hhi : (off : Int) + k ≤ (a.size : Int))
    (hq : Q (.ref r ((off : Int) + k).toNat) h) :
    Wp (Ptr.add (H := H) (R := R) (T := T) (.ref r off) k) h Q :=
  ⟨_, h, Ptr.add_ok h r off k a hget hoff hlo hhi, hq⟩

theorem ptr_load {r : R} {off : Nat} {h : H} {a : Array T} {Q : T → H → Prop}
    (hget : Space.get h r = some a) (hlt : off < a.size)
    (hq : Q a[off] h) :
    Wp (Ptr.load (H := H) (R := R) (T := T) (.ref r off)) h Q :=
  ⟨_, h, Ptr.load_ok h r off a hget hlt, hq⟩

theorem ptr_index {r : R} {off : Nat} {i : Int} {h : H} {a : Array T} {Q : T → H → Prop}
    (hget : Space.get h r = some a)
    (hoff : off ≤ a.size) (hlo : 0 ≤ (off : Int) + i) (hhi : (off : Int) + i < (a.size : Int))
    (hq : Q (a[((off : Int) + i).toNat]'(by omega)) h) :
    Wp (Ptr.index (H := H) (R := R) (T := T) (.ref r off) i) h Q :=
  ⟨_, h, Ptr.index_ok h r off i a hget hoff hlo hhi, hq⟩

theorem ptr_store {r : R} {off : Nat} {v : T} {h : H} {a : Array T} {Q : Unit → H → Prop}
    (hget : Space.get h r = some a) (hro : Space.ro h r = false) (hlt : off < a.size)
    (hq : Q () (Space.modify h r (fun arr => arr.set! off v))) :
    Wp (Ptr.store (H := H) (R := R) (T := T) (.ref r off) v) h Q :=
  ⟨(), _, Ptr.store_ok h r off v a hget hro hlt, hq⟩

theorem ptr_diff [DecidableEq R] {r : R} {o1 o2 : Nat} {h : H} {a : Array T}
    {Q : Int64 → H → Prop}
    (hget : Space.get h r = some a) (ho1 : o1 ≤ a.size) (ho2 : o2 ≤ a.size)
    (hlo : I64_MIN ≤ (o1 : Int) - (o2 : Int)) (hhi : (o1 : Int) - (o2 : Int) ≤ I64_MAX)
    (hq : Q (Int64.ofInt ((o1 : Int) - (o2 : Int))) h) :
    Wp (Ptr.diff (H := H) (R := R) (T := T) (.ref r o1) (.ref r o2)) h Q :=
  ⟨_, h, Ptr.diff_ok h r o1 o2 a hget ho1 ho2 hlo hhi, hq⟩

theorem ptr_lt [DecidableEq R] {r : R} {o1 o2 : Nat} {h : H} {a : Array T}
    {Q : Bool → H → Prop}
    (hget : Space.get h r = some a) (ho1 : o1 ≤ a.size) (ho2 : o2 ≤ a.size)
    (hq : Q (decide (o1 < o2)) h) :
    Wp (Ptr.lt (H := H) (R := R) (T := T) (.ref r o1) (.ref r o2)) h Q :=
  ⟨_, h, Ptr.lt_ok h r o1 o2 a hget ho1 ho2, hq⟩

end ptr
end Wp
end OssProof
