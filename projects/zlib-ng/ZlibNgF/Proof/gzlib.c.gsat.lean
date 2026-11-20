import ZlibNgF.Proof.«gzlib.c.reach»

/-!
# Statements about gz computations (`ZlibNgF`)

`GSat w h m Q`: the gz computation `m` returns on world `w` and heap `h`, and its result, world and heap satisfy `Q`;
the rules for `bind`, `pure`, lifted heap computations, the loops `gwhile` / `gdoWhile`, and the reads and stores of a
live `gz_state`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzSat
open C ZlibNgF.Spec ZlibNg.Gz
open ZlibNgF.Proof.InflateSync (Sat)

/-- `m` returns on `w`, `h` with a result, world and heap that satisfy `Q`. -/
def GSat {α : Type} (w : World) (h : Heap) (m : G α) (Q : α → World → Heap → Prop) : Prop :=
  ∃ r w' h', m w h = .ok ((r, w'), h') ∧ Q r w' h'

@[simp] theorem gbind_app {α β : Type} (m : G α) (f : α → G β) (w : World) (h : Heap) :
    (m >>= f) w h = match m w h with | .ok ((a, w'), h') => f a w' h' | .error e => .error e := by
  show (StateT.bind m f w) h = _
  simp only [StateT.bind, bind_app]
  cases m w h with
  | ok v => rfl
  | error e => rfl

@[simp] theorem gpure_app {α : Type} (a : α) (w : World) (h : Heap) : (pure a : G α) w h = .ok ((a, w), h) := rfl

@[simp] theorem lm_app {α : Type} (m : M α) (w : World) (h : Heap) :
    (lm m) w h = match m h with | .ok (a, h') => .ok ((a, w), h') | .error e => .error e := by
  show (StateT.lift m w) h = _
  simp only [StateT.lift, bind_app]
  cases m h with
  | ok v => rfl
  | error e => rfl

@[simp] theorem gget_app (w : World) (h : Heap) : (get : G World) w h = .ok ((w, w), h) := rfl

@[simp] theorem gmodify_app (f : World → World) (w : World) (h : Heap) :
    (modify f : G Unit) w h = .ok (((), f w), h) := rfl

@[simp] theorem gset_app (w0 w : World) (h : Heap) : (set w0 : G Unit) w h = .ok (((), w0), h) := rfl

@[simp] theorem getHeap_app (w : World) (h : Heap) : getHeap w h = .ok ((h, w), h) := rfl

theorem GSat.bind {α β : Type} {w : World} {h : Heap} {m : G α} {f : α → G β} {Q : β → World → Heap → Prop}
    (hm : GSat w h m (fun a w1 h1 => GSat w1 h1 (f a) Q)) : GSat w h (m >>= f) Q := by
  obtain ⟨a, w1, h1, e1, r, w2, h2, e2, q⟩ := hm
  exact ⟨r, w2, h2, by simp only [gbind_app, e1]; exact e2, q⟩

theorem GSat.pure {α : Type} {w : World} {h : Heap} {a : α} {Q : α → World → Heap → Prop} (q : Q a w h) :
    GSat w h (Pure.pure a) Q := ⟨a, w, h, rfl, q⟩

theorem GSat.mono {α : Type} {w : World} {h : Heap} {m : G α} {P Q : α → World → Heap → Prop}
    (hm : GSat w h m P) (hpq : ∀ a w' h', P a w' h' → Q a w' h') : GSat w h m Q := by
  obtain ⟨a, w', h', e, p⟩ := hm; exact ⟨a, w', h', e, hpq a w' h' p⟩

theorem GSat.of_eq {α : Type} {w w' : World} {h h' : Heap} {m : G α} {a : α} {Q : α → World → Heap → Prop}
    (e : m w h = .ok ((a, w'), h')) (q : Q a w' h') : GSat w h m Q := ⟨a, w', h', e, q⟩

theorem GSat.lm {α : Type} {w : World} {h : Heap} {m : M α} {Q : α → World → Heap → Prop}
    (hm : Sat h m (fun a h1 => Q a w h1)) : GSat w h (C.lm m) Q := by
  obtain ⟨a, h1, e, q⟩ := hm
  exact ⟨a, w, h1, by simp [e], q⟩

theorem GSat.ite {α : Type} {w : World} {h : Heap} {c : Prop} [Decidable c] {m1 m2 : G α}
    {Q : α → World → Heap → Prop} (h1 : c → GSat w h m1 Q) (h2 : ¬c → GSat w h m2 Q) :
    GSat w h (if c then m1 else m2) Q := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h1 hc
  · simp only [hc, ite_false]; exact h2 hc

theorem GSat.run {α : Type} {w : World} {h : Heap} {m : G α} {Q : α → World → Heap → Prop} (hm : GSat w h m Q) :
    ∃ r w' h', GzRun m w h r w' h' ∧ Q r w' h' := hm

/-- `while (cond) body` in `G`, with a decreasing measure. -/
theorem gsat_gwhile {σ : Type} {cond : σ → G (Bool × σ)} {body : σ → G σ} (I : σ → World → Heap → Prop)
    (μ : σ → Nat) (Q : σ → World → Heap → Prop)
    (hstep : ∀ s w h, I s w h → GSat w h (cond s) (fun cs w1 h1 =>
      (cs.1 = true → GSat w1 h1 (body cs.2) (fun s2 w2 h2 => I s2 w2 h2 ∧ μ s2 < μ s)) ∧
      (cs.1 = false → Q cs.2 w1 h1)))
    {s : σ} {w : World} {h : Heap} (hI : I s w h) (hμ : μ s < fuel) : GSat w h (gwhile cond body s) Q := by
  unfold gwhile
  suffices ∀ n s w h, I s w h → μ s < n → GSat w h (gwhile.go cond body n s) Q from this _ s w h hI hμ
  intro n
  induction n with
  | zero => intro s _ _ _ hlt; omega
  | succ n ih =>
    intro s w h hI hlt
    obtain ⟨⟨c, s1⟩, w1, h1, ec, ht, hf⟩ := hstep s w h hI
    cases c with
    | false => exact ⟨s1, w1, h1, by simp [gwhile.go, ec], hf rfl⟩
    | true =>
      obtain ⟨s2, w2, h2, eb, hI2, hμ2⟩ := ht rfl
      obtain ⟨s', w', h', eg, q⟩ := ih s2 w2 h2 hI2 (by omega)
      exact ⟨s', w', h', by simp [gwhile.go, ec, eb, eg], q⟩

/-! ## The live `gz_state` -/

theorem ldGz_app {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) :
    (ldGz (some b)) w h = .ok ((s, w), h) := by
  simp only [ldGz, gbind_app, gget_app, getHeap_app, hs]
  rfl

theorem rdG_app' {α : Type} {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (g : GzState → α) : (rdG (some b) g) w h = .ok ((g s, w), h) := by
  simp [rdG, ldGz_app hs]

theorem wrG_app {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (f : GzState → GzState) :
    (wrG (some b) f) w h = .ok (((), { w with gzs := upd w.gzs b (some (f s)) }), h) := by
  simp [wrG, stGz, ldGz_app hs]

theorem gz_upd_same {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (s' : GzState) :
    ({ w with gzs := upd w.gzs b (some s') } : World).gz h b = some s' := by
  unfold World.gz at hs ⊢
  split at hs
  · simp
  · cases hs

theorem gz_upd_ne {w : World} {h : Heap} {b c : Nat} (v : Option GzState) (hne : c ≠ b) :
    ({ w with gzs := upd w.gzs b v } : World).gz h c = w.gz h c := by
  unfold World.gz
  simp [upd_ne _ _ _ _ hne]

theorem strmOf_app {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) :
    (strmOf (some b)) w h = .ok ((some s.strm, w), h) := by
  simp [strmOf, ldGz_app hs]

end ZlibNgF.Proof.GzSat
