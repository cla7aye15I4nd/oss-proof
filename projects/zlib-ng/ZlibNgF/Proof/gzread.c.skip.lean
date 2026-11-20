import ZlibNgF.Proof.«gzread.c.fetch»

/-!
# `gz_skip` on a read handle (`ZlibNgF`)

`gz_skip` (`gzread.c:259-284`) loops while a skip is pending: it consumes `min(x.have, skip)` bytes of buffered output,
stops at the end of the input, or calls `gz_fetch` for more output.

**Termination.** The measure is the potential `Phi` of the read handle plus 1 while output is buffered. A consume step
keeps `Phi` (it moves bytes from `x.have` to `x.pos`) and, when a skip is still pending, leaves no output. A `gz_fetch`
that returns 0 from a state that is not at the end of the input lowers `Phi` by 2 with output and by 1 without
(`FetchMu`). The skip itself (up to `2^63` bytes) never enters the measure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzDecomp

/-! ## `gz_skip` in parts (copied from the translation) -/

open ZlibNg.Inflate in
/-- The body of the loop of `gz_skip`. -/
def skipBody (state : GzPtr) (c : Ctl) : G Ctl := do
  if (← rdG state (·.«have»)) != 0 then
    let hv ← rdG state (·.«have»)
    let sk ← rdG state (·.skip)
    let n : UInt32 := if GT_OFF hv || Int64.ofNat hv.toNat > sk then sk.toUInt64.toUInt32 else hv
    wrG state fun s => { s with «have» := s.«have» - n }
    let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
    wrG state fun s => { s with next := .val nx }
    let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
    wrG state fun s => { s with pos := np }
    let sk ← lm (chkI64 ((← rdG state (·.skip)).toInt - n.toNat))
    wrG state fun s => { s with skip := sk }
    return c
  else if (← rdG state (·.eof)) != 0 && (← lm (rdZ (← strmOf state) (·.avail_in))) == 0 then
    return .brk
  else
    if (← gz_fetch state) == -1 then
      return .ret
    return c

/-- The condition of the loop of `gz_skip`. -/
def skipCond (state : GzPtr) (c : Ctl) : G (Bool × Ctl) := do
  if c != .go then return (false, c)
  return ((← rdG state (·.skip)) != 0, c)

theorem gz_skip_eq (state : GzPtr) : gz_skip state = (do
    let lp ← gdoWhile (skipBody state) (skipCond state) .go
    if lp == .ret then
      return -1
    return 0) := by
  unfold gz_skip skipBody skipCond; rfl

/-! ## The measure -/

theorem dD_lt {W : World} (hr : ∀ fd, rdLeft W.fs fd < 2 ^ 62) (H : Heap) (s : GzState) :
    dD s W H < 2 ^ 62 + 2 ^ 32 := by
  have := hr s.fd
  unfold dD; split
  · next z _ => have := z.avail_in.toNat_lt; omega
  · omega

theorem xq_le (s : GzState) : xq s ≤ 2 ^ 64 := by
  unfold xq; have := Int64.le_toInt s.pos; have := gzmax; omega

theorem Phi_lt {W : World} (hr : ∀ fd, rdLeft W.fs fd < 2 ^ 62) (H : Heap) (s : GzState) : Phi W H s + 1 < fuel := by
  have := Phi_le W H s; have := dD_lt hr H s; have := xq_le s; have := ph2_le s
  simp [fuel]; omega

/-- A consume step keeps the potential. -/
theorem Phi_consume {W W2 : World} {H : Heap} {s1 s2 : GzState} (hfs : W2.fs = W.fs)
    (e : s2 = { s1 with «have» := s2.«have», next := s2.next, pos := s2.pos, skip := s2.skip })
    (hph : s2.pos.toInt + s2.«have».toNat = s1.pos.toInt + s1.«have».toNat) : Phi W2 H s2 = Phi W H s1 := by
  have hx : xq s2 = xq s1 := by unfold xq; omega
  have hfd : s2.fd = s1.fd := (congrArg GzState.fd e).trans rfl
  have hst : s2.strm = s1.strm := (congrArg GzState.strm e).trans rfl
  have hd : dD s2 W2 H = dD s1 W H := by unfold dD; rw [hfs, hfd, hst]
  have hp : ph2 s2 = ph2 s1 := (congrArg ph2 e).trans rfl
  have ha : AtEnd H s2 = AtEnd H s1 := (congrArg (AtEnd H) e).trans rfl
  unfold Phi; rw [hx, hd, hp, ha]

open Classical in
/-- The measure of the loop of `gz_skip`: the potential, plus 1 while output is buffered. -/
noncomputable def smu (b : Nat) (W : World) (H : Heap) : Nat :=
  match W.gz H b with
  | some s1 => Phi W H s1 + (if s1.«have» = 0 then 0 else 1)
  | none => 0

theorem smu_of {b : Nat} {W : World} {H : Heap} {s1 : GzState} (hs : W.gz H b = some s1) :
    smu b W H = Phi W H s1 + (if s1.«have» = 0 then 0 else 1) := by
  simp only [smu, hs]

/-! ## The invariant and one trip of the loop -/

/-- The invariant of the loop of `gz_skip` at the start of a trip: a mid-call state with a skip pending. -/
def SInv (w : World) (h : Heap) (b : Nat) (s : GzState) (c : Ctl) (W : World) (H : Heap) : Prop :=
  c = .go ∧ ∃ s1, GzMid W H b s1 ∧ s1.skip ≠ 0 ∧ GStep w h W H b [] ∧ FsRd w.fs W.fs ∧
    s1.pos.toInt + s1.skip.toInt = s.pos.toInt + s.skip.toInt ∧ (s.size ≠ 0 → s1.size ≠ 0) ∧
    (LookIdle w h (some b) → LookIdle W H (some b))

/-- The exit of the loop of `gz_skip`. -/
def SQ (w : World) (h : Heap) (b : Nat) (s : GzState) (c : Ctl) (W : World) (H : Heap) : Prop :=
  GzInvR W H (some b) ∧ GStep w h W H b [] ∧ FsRd w.fs W.fs ∧
    ∃ s', W.gz H b = some s' ∧ s'.pos.toInt + s'.skip.toInt = s.pos.toInt + s.skip.toInt ∧
      (s.size ≠ 0 → s'.size ≠ 0) ∧ (c ≠ .ret → s'.skip = 0 ∨ (s'.«have» = 0 ∧ AtEnd H s')) ∧
      (LookIdle w h (some b) → LookIdle W H (some b))

/-- **One trip of the loop of `gz_skip`** and its condition. -/
theorem skipBody_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hs0 : w.gz h b = some s) {c : Ctl}
    {W : World} {H : Heap} (hI : SInv w h b s c W H) :
    GSat W H (skipBody (some b) c) (fun c1 W1 H1 => GSat W1 H1 (skipCond (some b) c1) (fun cs W2 H2 =>
      (cs.1 = true → SInv w h b s cs.2 W2 H2 ∧ smu b W2 H2 < smu b W H) ∧ (cs.1 = false → SQ w h b s cs.2 W2 H2))) := by
  obtain ⟨rfl, s1, hm, hk1, g, hf, hpk, hsz, hi⟩ := hI
  obtain ⟨hs1, hv0, hout, hph⟩ := hm
  have hμ := smu_of hs1
  unfold skipBody
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  apply GSat.ite
  · intro hh
    have hh' : s1.«have» ≠ 0 := by simpa using hh
    refine consume_specX hv0 hs1 hout hh' hph fun W2 s2 hs2 hv2 g2 hfs2 hpk2 hkh ⟨e1, e2, e3⟩ esh ehp => ?_
    have g' := g.trans g2 ⟨s, hs0⟩ ⟨s1, hs1⟩
    have hf' : FsRd w.fs W2.fs := by rw [hfs2]; exact hf
    have hsz2 : s.size ≠ 0 → s2.size ≠ 0 := fun e => by rw [esh]; exact hsz e
    have hi2 : LookIdle w h (some b) → LookIdle W2 H (some b) := fun hi0 => idle_same (hi hi0) hs1 hs2 e1 e2 e3 rfl
    refine GSat.pure ?_
    unfold skipCond
    refine GSat.ite (fun hc => absurd hc (by decide)) (fun _ => ?_)
    refine GSat.bind (GSat.of_eq (rdG_app' hs2 _) (GSat.pure ⟨fun hc => ?_, fun hc => ?_⟩))
    · have hk2 : s2.skip ≠ 0 := by simpa using hc
      have h02 := hkh hk2
      refine ⟨⟨rfl, s2, mid_of hv2 hs2, hk2, g', hf', by omega, hsz2, hi2⟩, ?_⟩
      rw [smu_of hs2, hμ, Phi_consume hfs2 esh ehp]
      simp [h02, hh']
    · have hk2 : s2.skip = 0 := by simpa using hc
      exact ⟨hv2, g', hf', s2, hs2, by omega, hsz2, fun _ => Or.inl hk2, hi2⟩
  · intro hh
    have h0 : s1.«have» = 0 := by simpa using hh
    have hv : GzInvR W H (some b) := invR_restore hv0 hs1 hout (fun _ => h0) hph
    obtain ⟨z, hz⟩ := mid_strm ⟨hs1, hv0, hout, hph⟩
    refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
    refine GSat.bind (GSat.of_eq (strmOf_app hs1) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz _, ?_⟩)
    apply GSat.ite
    · intro hc
      have hc' : s1.eof ≠ 0 ∧ z.avail_in = 0 := by simpa using hc
      refine GSat.pure ?_
      unfold skipCond
      exact GSat.ite (fun _ => GSat.pure ⟨fun e => absurd e (by simp), fun _ =>
        ⟨hv, g, hf, s1, hs1, hpk, hsz, fun _ => Or.inr ⟨h0, hc'.1, z, hz, hc'.2⟩, hi⟩⟩)
        (fun hc2 => absurd hc2 (by decide))
    · intro hc
      have hne : ¬ AtEnd H s1 := by
        rintro ⟨e1, z', hz', e2⟩
        rw [hz] at hz'; cases hz'
        exact hc (by simp [e1, e2])
      refine GSat.bind (GSat.mono (gz_fetch_specM hv hs1 h0) fun r W1 H1 q => ?_)
      obtain ⟨⟨⟨hr1, g1, hf1, s', hm', hp', hk', hsz', -, -⟩, hid⟩, hmu, hm1⟩ := q
      have g' := g.trans g1 ⟨s, hs0⟩ ⟨s1, hs1⟩
      have hpk' : s'.pos.toInt + s'.skip.toInt = s.pos.toInt + s.skip.toInt := by rw [hp', hk']; exact hpk
      apply GSat.ite
      · intro e
        have hr : r = -1 := by simpa using e
        have h0' := hm1 hr s' hm'.1
        refine GSat.pure ?_
        unfold skipCond
        obtain ⟨hs', hv0', hout', hph'⟩ := hm'
        exact GSat.ite (fun _ => GSat.pure ⟨fun e => absurd e (by simp), fun _ =>
          ⟨invR_restore hv0' hs' hout' (fun _ => h0') hph', g', hf.trans hf1, s', hs', hpk',
            fun e => hsz' (hsz e), fun e => absurd rfl e, fun hi0 => hid (hi hi0)⟩⟩)
          (fun hc2 => absurd hc2 (by decide))
      · intro e
        have hr : r = 0 := hr1.resolve_left (by simpa using e)
        refine GSat.pure ?_
        unfold skipCond
        refine GSat.ite (fun hc2 => absurd hc2 (by decide)) (fun _ => ?_)
        refine GSat.bind (GSat.of_eq (rdG_app' hm'.1 _) (GSat.pure ⟨fun _ => ?_, fun hc2 => ?_⟩))
        · refine ⟨⟨rfl, s', hm', by rw [hk']; exact hk1, g', hf.trans hf1, hpk', fun e => hsz' (hsz e),
            fun hi0 => hid (hi hi0)⟩, ?_⟩
          rw [smu_of hm'.1, hμ]
          have hd := hmu hr hne s' hm'.1
          by_cases hh2 : s'.«have» = 0
          · have := hd.2 hh2; simp [hh2, h0]; omega
          · have := hd.1 hh2; simp [hh2, h0]; omega
        · exfalso; apply hk1; rw [← hk']; simpa using hc2

/-! ## `gz_skip` -/

/-- **`gz_skip`** from a mid-call state with a pending skip, with `LookIdle` kept. -/
theorem gz_skip_specI {w : World} {h : Heap} {b : Nat} {s : GzState} (hm : GzMid w h b s) (hk : s.skip ≠ 0) :
    GSat w h (gz_skip (some b)) (fun r W H => SkipPost w h b s r W H ∧
      (LookIdle w h (some b) → LookIdle W H (some b))) := by
  rw [gz_skip_eq]
  refine GSat.bind (GSat.mono (gsat_gdoWhile (SInv w h b s) (fun _ W H => smu b W H) (SQ w h b s)
    (fun _ _ _ hI => skipBody_spec hm.1 hI) ⟨rfl, s, hm, hk, GStep.refl _ _ _ _, FsRd.refl _, rfl, id, id⟩ ?_)
    fun lp W H q => ?_)
  · rw [smu_of hm.1]
    have := Phi_lt (W := w) (fun fd => rdLeft_lt hm.2.1.2.2 fd) h s
    split <;> omega
  obtain ⟨hv, g, hf, s', hs', hpk, hsz, hend, hi⟩ := q
  apply GSat.ite
  · intro _
    exact GSat.pure ⟨⟨Or.inl rfl, hv, g, hf, s', hs', hpk, hsz, fun e => absurd e (by decide)⟩, hi⟩
  · intro hne
    exact GSat.pure ⟨⟨Or.inr rfl, hv, g, hf, s', hs', hpk, hsz, fun _ => hend (by simpa using hne)⟩, hi⟩

/-- **`gz_skip`** from a mid-call state with a pending skip. -/
theorem gz_skip_spec : GzSkipSpec :=
  fun _ _ _ _ hm hk => (gz_skip_specI hm hk).mono fun _ _ _ q => q.1

/-- **`gz_skip` keeps `LookIdle`.** -/
theorem gz_skip_idle : GzSkipIdle := by
  intro w h b s r W H hm hi hk e
  obtain ⟨r2, W2, H2, e2, q⟩ := (gz_skip_specI hm hk).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact q.2 hi

end ZlibNgF.Proof.GzMode
