import ZlibNgF.Proof.«inffast.dodist»

/-!
# `inflate_fast`: one trip and the main loop (`ZlibNgF`)

`sat_trip`: from the state at the start of a trip (`TS`), `stepTop` and the label loop (`cwhile` over `dolen` /
`common` / `dodist`, terminating by the ghost rank of `PI`) end in `continue` (output advanced) or `break`.
`sat_loop`: the `do { … } while (in < last && out < end)` loop, with measure `safe - out`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastLoop
open C ZlibNg.Inffast ZlibNg.InflateP ZlibNg.Chunkset
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem
open ZlibNgF.Proof.ChunkCopy (B)
open ZlibNgF.Proof.InffastBase
open ZlibNgF.Proof.InffastInv
open ZlibNgF.Proof.InffastSteps
open ZlibNgF.Proof.InffastDodist

theorem sat_trip {H0 G : Heap} {c : FC} {e : FE} {ot : Nat} (EV : EnvOK H0 c e) {l : FL}
    (hT : TS H0 c e ot l G) :
    Sat G (trip c l) (fun x G' => (x.2 = false ∧ PI H0 c e ot 0 (x.1, .cont) G') ∨
      (x.2 = true ∧ PI H0 c e ot 0 (x.1, .brk) G')) := by
  unfold trip
  refine Sat.bind (Sat.mono (sat_stepTop EV hT) ?_)
  rintro ⟨l1, lbl1⟩ G1 ⟨n, hn, hP⟩
  refine Sat.bind (Sat.mono (sat_cwhile_rank (fun n x G => PI H0 c e ot n x G)
    (fun x G => (x.2 = .cont ∨ x.2 = .brk) ∧ PI H0 c e ot 0 x G) ?_ hP (by unfold fuel; omega)) ?_)
  · rintro n ⟨l, lbl⟩ H hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
    · cases lbl with
      | dolen => exact sat_stepDolen EV hI
      | common => exact sat_stepCommon EV hI
      | dodist => exact sat_stepDodist EV hI
      | cont => simp at hc
      | brk => simp at hc
    · cases lbl with
      | cont => exact ⟨Or.inl rfl, hI⟩
      | brk => exact ⟨Or.inr rfl, hI⟩
      | _ => simp at hc
  · rintro ⟨l2, lbl2⟩ G2 ⟨hl, hP2⟩
    simp only at hl
    rcases hl with rfl | rfl
    · exact Sat.pure (Or.inl ⟨rfl, hP2⟩)
    · exact Sat.pure (Or.inr ⟨rfl, hP2⟩)

/-- The offset of a pointer (`0` for `NULL`). -/
def offOf (p : BPtr) : Nat :=
  match p with
  | .ref _ k => k
  | _ => 0

/-- The invariant of the main loop: at the start of a trip. -/
def LoopI (H0 : Heap) (c : FC) (e : FE) (x : FL × Bool) (G : Heap) : Prop :=
  x.2 = false ∧ ∃ ot, TS H0 c e ot x.1 G

/-- The measure of the main loop: `safe - out`. -/
def loopM (e : FE) (x : FL × Bool) : Nat := e.s - offOf x.1.out

/-- The state after the main loop: `out` advanced within `[o0, safe]`, the input and bit accounting, and either no
`break` (some output written and a bit consumed, only output bytes changed) or a `break` (a bit consumed, the mode and
message stored). -/
def LoopQ (H0 : Heap) (sm : Bool) (e : FE) (x : FL × Bool) (G : Heap) : Prop :=
  ∃ po, x.1.out = B e.ob po ∧ e.o0 ≤ po ∧ po ≤ e.s ∧ InOK e x.1 0 ∧
    ((x.2 = false ∧ e.o0 < po ∧ InS e x.1 ∧ RH H0 e G) ∨ (x.2 = true ∧ InS e x.1 ∧ BrkHeap H0 sm e G))

theorem loop_step {H0 : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) :
    ∀ s H, LoopI H0 c e s H → Sat H ((fun ((l, _) : FL × Bool) => trip c l) s) (fun s1 H1 => Sat H1
      ((fun ((l, brk) : FL × Bool) => (do
        if brk then return (false, (l, brk))
        if ← Ptr.lt l.in_ c.last then
          return (← Ptr.lt l.out c.end_, (l, brk))
        return (false, (l, brk)) : M (Bool × FL × Bool))) s1)
      (fun cs H2 => (cs.1 = true → LoopI H0 c e cs.2 H2 ∧ loopM e cs.2 < loopM e s) ∧
        (cs.1 = false → LoopQ H0 c.safeMode e cs.2 H2))) := by
  rintro ⟨l, b⟩ H ⟨hb, ot, hT⟩
  simp only at hb; subst hb
  have hT' := hT
  obtain ⟨⟨hout0, ho0, hroom⟩, -, -⟩ := hT'
  refine Sat.mono (sat_trip EV hT) ?_
  rintro ⟨l1, b1⟩ H1 hres
  have hsN := EV.sN
  have hrm := EV.room
  rcases hres with ⟨hb1, hc⟩ | ⟨hb1, hk⟩
  · simp only at hb1; subst hb1
    obtain ⟨po, hpo, hot, hps, hin, hS, r⟩ := hc
    obtain ⟨p, hp, hp0, hpE, hb64, hacc⟩ := hin
    obtain ⟨A, hA, hAE⟩ := EV.inA
    obtain ⟨A', hA', hsz⟩ := in_get r hA
    have hie := EV.inE
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hp, EV.last]
    refine Sat.bind (Sat.mono (sat_lt hA' (o1 := p) (o2 := e.E - 14) (by omega) (by omega)) ?_)
    rintro cb H2 ⟨rfl, rfl⟩
    by_cases hlt : p < e.E - 14
    · simp only [hlt, decide_true, ↓reduceIte]
      obtain ⟨a, ha, haN⟩ := r.cur
      rw [hpo, EV.endp]
      refine Sat.bind (Sat.mono (sat_lt (space_heap _ e.ob ▸ ha) (o1 := po)
        (o2 := if c.safeMode then e.s - 2 else e.s - 259) (by omega) (by split <;> omega)) ?_)
      rintro cb H3 ⟨rfl, rfl⟩
      refine Sat.pure ⟨fun hc => ⟨⟨rfl, po, ⟨hpo, ?_⟩, r, p, hp, hp0, by omega, hb64, hacc⟩, ?_⟩, fun hc => ?_⟩
      · have hc' : po < (if c.safeMode then e.s - 2 else e.s - 259) := by simpa using hc
        refine ⟨by omega, ?_⟩
        split at hc' <;> split at hrm <;> simp_all <;> omega
      · show e.s - offOf l1.out < e.s - offOf l.out
        rw [show l1.out = B e.ob po from hpo, hout0]; simp only [offOf]; omega
      · exact ⟨po, hpo, by omega, hps, ⟨p, hp, hp0, by omega, hb64, hacc⟩, Or.inl ⟨rfl, by omega, hS, r⟩⟩
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine Sat.pure ⟨fun hc => by simp at hc, fun _ =>
        ⟨po, hpo, by omega, hps, ⟨p, hp, hp0, by omega, hb64, hacc⟩, Or.inl ⟨rfl, by omega, hS, r⟩⟩⟩
  · simp only at hb1; subst hb1
    obtain ⟨po, hpo, hot, hps, hin, hS, hbk⟩ := hk
    simp only [↓reduceIte]
    exact Sat.pure ⟨fun hc => by simp at hc, fun _ => ⟨po, hpo, by omega, hps, hin, Or.inr ⟨rfl, hS, hbk⟩⟩⟩

end ZlibNgF.Proof.InffastLoop
