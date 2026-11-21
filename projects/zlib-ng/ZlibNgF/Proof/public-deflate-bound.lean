import ZlibNgF.Proof.«public-deflate-control»

/-!
# `deflateBound`, `deflateBound_z` (`ZlibNgF`)

Both only read: every run that returns leaves the heap unchanged (`RO`), so they keep any invariant. On `Z_NULL`, on
a stream with no state, and on a stream with the structural invariant whose registered gzip header is readable, they
do not fault: the header's `name` and `comment` are C strings, read by `countStr` up to their zero byte (the loop
runs `n + 1 < 2^64` times, by `ObjBound`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBound
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.InflateInv (ldStream_app)

/-! ## Read-only actions -/

/-- An action that, when it returns, leaves the heap unchanged. -/
def RO {α : Type} (m : M α) : Prop := ∀ h r h', m h = .ok (r, h') → h' = h

theorem RO.pure {α : Type} (a : α) : RO (pure a : M α) := by
  intro h r h' e; cases e; rfl

theorem RO.bind {α β : Type} {m : M α} {f : α → M β} (hm : RO m) (hf : ∀ a, RO (f a)) : RO (m >>= f) := by
  intro h r h' e
  simp only [bind_app] at e
  cases e1 : m h with
  | error x => rw [e1] at e; cases e
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [e1] at e
    rw [hf a h1 r h' e, hm h a h1 e1]

theorem RO.ub {α : Type} (s : String) : RO (ub s : M α) := by
  intro h r h' e; cases e

theorem RO.ite {α : Type} {c : Prop} [Decidable c] {a b : M α} (ha : RO a) (hb : RO b) :
    RO (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem RO.ldStream (s : StreamPtr) : RO (ldStream s) := by
  intro h r h' e; unfold C.ldStream at e; split at e
  · cases e
  · split at e <;> cases e; rfl

theorem RO.ldDState (s : StatePtr) : RO (ldDState s) := by
  intro h r h' e; unfold C.ldDState at e; split at e
  · cases e
  · split at e <;> cases e; rfl

theorem RO.ldHeader (p : HeaderPtr) : RO (ldHeader p) := by
  intro h r h' e; unfold C.ldHeader at e; split at e
  · cases e
  · split at e <;> cases e; rfl

theorem RO.load (p : BPtr) : RO (Ptr.load p : M UInt8) := by
  intro h r h' e; unfold Ptr.load at e; split at e
  · cases e
  · split at e
    · cases e
    · split at e <;> cases e; rfl

theorem RO.add (p : BPtr) (k : Int) : RO (p.add k) := by
  intro h r h' e; unfold Ptr.add at e; split at e
  · cases e
  · split at e
    · cases e
    · split at e <;> cases e; rfl

theorem RO.get {α : Type} (v : Ival α) : RO v.get := by
  cases v
  · exact RO.ub _
  · exact RO.pure _

theorem RO.cdoWhile {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} (hb : ∀ s, RO (body s))
    (hc : ∀ s, RO (cond s)) (s : σ) : RO (C.cdoWhile body cond s) := by
  unfold C.cdoWhile
  suffices ∀ n s, RO (C.cdoWhile.go body cond n s) from this _ s
  intro n
  induction n with
  | zero => intro s h r h' e; cases e
  | succ n ih =>
    intro s
    unfold C.cdoWhile.go
    refine RO.bind (hb s) fun s1 => RO.bind (hc s1) fun cs => ?_
    obtain ⟨c, s2⟩ := cs
    exact RO.ite (ih s2) (RO.pure _)

theorem RO.stateCheck (s : StreamPtr) : RO (deflateStateCheck s) := by
  unfold deflateStateCheck
  refine RO.ite (RO.pure _) (RO.bind (RO.ldStream s) fun z => ?_)
  refine RO.ite (RO.pure _) ?_
  refine RO.ite (RO.pure _) (RO.bind (RO.ldDState _) fun st => ?_)
  refine RO.bind (RO.get _) fun ab => RO.ite (RO.pure _) (RO.bind (RO.get _) fun sm => ?_)
  exact RO.ite (RO.pure _) (RO.ite (RO.pure _) (RO.pure _))

theorem RO.countStr (p : BPtr) (w : UInt64) : RO (ZlibNg.Deflate.countStr p w) := by
  unfold ZlibNg.Deflate.countStr
  refine RO.bind (RO.cdoWhile (fun _ => RO.pure _) (fun s => ?_) _) fun _ => RO.pure _
  obtain ⟨str, wraplen, c⟩ := s
  exact RO.bind (RO.load str) fun c => RO.bind (RO.add str 1) fun _ => RO.pure _

theorem RO.ctz (v : UInt32) : RO (zng_ctz32 v) := by
  unfold zng_ctz32
  exact RO.ite (RO.ub _) (RO.pure _)

/-- One step of a read-only proof: an atom, a bind, or a case split. -/
macro "ro_step" : tactic => `(tactic| first
  | exact RO.pure _ | exact RO.ub _ | exact RO.ldStream _ | exact RO.ldDState _ | exact RO.ldHeader _
  | exact RO.get _ | exact RO.countStr _ _ | exact RO.ctz _ | exact RO.stateCheck _ | exact RO.add _ _
  | exact RO.load _ | (refine RO.bind ?_ (fun _ => ?_)) | (refine RO.ite ?_ ?_) | split)

theorem RO.deflateBound_z (s : StreamPtr) (n : UInt64) : RO (ZlibNg.Deflate.deflateBound_z s n) := by
  dsimp only [ZlibNg.Deflate.deflateBound_z, dstateOf, rdZ, W_BITS]
  repeat' ro_step

theorem RO.deflateBound (s : StreamPtr) (n : UInt64) : RO (ZlibNg.Deflate.deflateBound s n) := by
  unfold ZlibNg.Deflate.deflateBound
  exact RO.bind (RO.deflateBound_z s n) fun _ => RO.pure _

/-! ## No fault -/

/-- The loop of `countStr` from the `k`-th character of a C string of `n` characters. -/
theorem countStr_go {h : Heap} {r : BRef} {off n : Nat} {data : Array UInt8} (hg : Space.get h r = some data)
    (hsz : off + n + 1 ≤ data.size) (hz : data[off + n]! = 0) (hnz : ∀ i, i < n → data[off + i]! ≠ 0)
    (w : UInt64) : ∀ (m k : Nat) (c : UInt8), k ≤ n → n - k < m →
      C.cdoWhile.go (fun ((str, wraplen, c) : BPtr × UInt64 × UInt8) => (pure (str, wraplen + 1, c) : M _))
        (fun ((str, wraplen, _) : BPtr × UInt64 × UInt8) => do
          let c ← load8 str
          let str ← str.add 1
          pure (c != 0, (str, wraplen, c)))
        m (.ref r (off + k), w + UInt64.ofNat k, c) h =
      .ok ((.ref r (off + n + 1), w + UInt64.ofNat (n + 1), 0), h) := by
  intro m
  induction m with
  | zero => intro k c _ hlt; omega
  | succ m ih =>
    intro k c hk hlt
    have hlt' : off + k < data.size := by omega
    have hget : data[off + k]! = data[off + k] := getElem!_pos data (off + k) hlt'
    have hload : (load8 (.ref r (off + k)) : M UInt8) h = .ok (data[off + k], h) := by
      simp [load8, Ptr.load, hg, hlt']
    have hadd : (Ptr.ref r (off + k) : BPtr).add 1 h = .ok (.ref r (off + k + 1), h) := by
      simp only [Ptr.add, hg]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      congr 3
    have hw : w + UInt64.ofNat k + 1 = w + UInt64.ofNat (k + 1) := by
      rw [UInt64.add_assoc]; congr 1
      apply UInt64.toNat_inj.mp
      simp [UInt64.toNat_ofNat, UInt64.toNat_add, Nat.add_mod]
    rw [C.cdoWhile.go]
    simp only [bind_app, pure_app, hload, hadd, hw]
    by_cases hkn : k = n
    · subst hkn
      have h0 : data[off + k] = 0 := by rw [← hget]; exact hz
      simp [h0]
    · have hne : data[off + k] ≠ 0 := by rw [← hget]; exact hnz k (by omega)
      have := ih (k + 1) (data[off + k]) (by omega) (by omega)
      rw [show off + (k + 1) = off + k + 1 by omega] at this
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by simpa using hne))]
      exact this

theorem cstr_null_iff (h : Heap) (m : Nat) : CStringLen h Ptr.null m ↔ False := by
  constructor
  · intro hs; obtain ⟨_, _, _, e, _⟩ := hs; cases e
  · intro f; exact f.elim

/-- `countStr` on a C string of `n` characters adds `n + 1` and changes nothing. -/
theorem countStr_ok {h : Heap} {p : BPtr} {n : Nat} (hs : CStringLen h p n) (hob : ObjBound h) (w : UInt64) :
    ZlibNg.Deflate.countStr p w h = .ok (w + UInt64.ofNat (n + 1), h) := by
  obtain ⟨r, off, data, rfl, hg, hsz, hz, hnz⟩ := hs
  have hb := hob r data hg
  have := countStr_go hg hsz hz hnz w fuel 0 0 (Nat.zero_le _) (by unfold fuel; omega)
  have e0 : w + UInt64.ofNat 0 = w := by simp
  rw [Nat.add_zero, e0] at this
  simp only [ZlibNg.Deflate.countStr, C.cdoWhile, bind_app]
  rw [this]
  rfl

/-- A run that returns, of a read-only action, returns on the same heap. -/
theorem RO.same {α : Type} {m : M α} (hm : RO m) {h : Heap} (hx : ∃ r h', m h = .ok (r, h')) :
    ∃ r, m h = .ok (r, h) := by
  obtain ⟨r, h', e⟩ := hx
  exact ⟨r, by rw [e, hm h r h' e]⟩

theorem deflateBound_z_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (n : UInt64) :
    ∃ r, C.run (ZlibNg.Deflate.deflateBound_z s n) h = .ok (r, h) := by
  constructor
  simp only [C.run, ZlibNg.Deflate.deflateBound_z, bind_app, stateCheck_noState hn, ↓reduceIte]
  rfl

theorem deflateBound_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (n : UInt64) :
    ∃ r, C.run (ZlibNg.Deflate.deflateBound s n) h = .ok (r, h) := by
  obtain ⟨r, e⟩ := deflateBound_z_noState hn n
  exact ⟨_, by simp only [C.run, ZlibNg.Deflate.deflateBound, bind_app] at e ⊢; rw [e]; rfl⟩

/-- `countStr` of a header string that is `NULL` or a C string. -/
theorem countStr_opt {h : Heap} {p : BPtr} (hs : p = .null ∨ ∃ n, CStringLen h p n) (hob : ObjBound h)
    (w : UInt64) : p ≠ .null → ∃ w', ZlibNg.Deflate.countStr p w h = .ok (w', h) := by
  intro hp
  rcases hs with hs | ⟨n, hs⟩
  · exact absurd hs hp
  · exact ⟨_, countStr_ok hs hob w⟩

set_option maxHeartbeats 2000000 in
theorem deflateBound_z_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) (hr : DHeaderReadable h s)
    (hob : ObjBound h) (n : UInt64) : ∃ r, C.run (ZlibNg.Deflate.deflateBound_z s n) h = .ok (r, h) := by
  refine RO.same (RO.deflateBound_z s n) ?_
  obtain ⟨i, z, b, st, al, rfl, L, _, cr⟩ := live hv
  have hws : st.w_size ≠ 0 := cr.w_size
  have hctz : ∃ c, zng_ctz32 st.w_size h = .ok (c, h) := ⟨_, by simp [zng_ctz32, hws]; rfl⟩
  obtain ⟨c, hc⟩ := hctz
  have haw : (if st.wrap < 0 then -st.wrap else st.wrap) = 0 ∨ (if st.wrap < 0 then -st.wrap else st.wrap) = 1 ∨
      (if st.wrap < 0 then -st.wrap else st.wrap) = 2 := by
    rcases cr.wrap with e | e | e | e | e
    all_goals
      have e' : st.wrap = _ := e
      rw [e']
      decide
  rcases haw with hw | hw | hw
  · have hw' := hw
    simp [ZlibNg.Deflate.deflateBound_z, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hw',
      W_BITS, hc]
    repeat' split
    all_goals exact ⟨_, _, rfl⟩
  · have hw' := hw
    simp [ZlibNg.Deflate.deflateBound_z, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hw',
      W_BITS, hc]
    repeat' split
    all_goals exact ⟨_, _, rfl⟩
  · have hw' := hw
    obtain ⟨hp, hgz⟩ := cr.gzhead
    have hgz' : st.gzhead = .val hp := hgz
    cases hp with
    | none =>
      simp [ZlibNg.Deflate.deflateBound_z, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hw',
        W_BITS, hc, hgz', Ival.get]
      repeat' split
      all_goals exact ⟨_, _, rfl⟩
    | some k =>
      obtain ⟨g, hg, _, hname, hcomm⟩ := hr k ⟨b, st, ⟨⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩, L.dstate⟩, hgz'⟩
      have hld : ldHeader (some k) h = .ok (g, h) := by simp [ldHeader, hg]
      have nn : ∀ (p : BPtr) (m : Nat), CStringLen h p m → (p != Ptr.null) = true := by
        intro p m hs
        obtain ⟨r, off, _, rfl, _⟩ := hs
        rfl
      rcases hname with hn0 | ⟨m1, hm1⟩ <;> rcases hcomm with hc0 | ⟨m2, hm2⟩
      · simp [ZlibNg.Deflate.deflateBound_z, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hw',
          W_BITS, hc, hgz', Ival.get, hld, hn0, hc0]
        repeat' (first | exact ⟨_, _, rfl⟩ | split | (simp only [bind_app, pure_app, hld, hc, hn0, hc0]) | contradiction |
          (exfalso; simp_all [cstr_null_iff]))
      · have K2 := countStr_ok hm2 hob
        simp [ZlibNg.Deflate.deflateBound_z, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hw',
          W_BITS, hgz', Ival.get, hld, hn0]
        repeat' (first | exact ⟨_, _, rfl⟩ | split | (simp only [bind_app, pure_app, hld, hc, K2]) | contradiction |
          (exfalso; simp_all [cstr_null_iff]))
      · have K1 := countStr_ok hm1 hob
        simp [ZlibNg.Deflate.deflateBound_z, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hw',
          W_BITS, hgz', Ival.get, hld]
        repeat' (first | exact ⟨_, _, rfl⟩ | split | (simp only [bind_app, pure_app, hld, hc, hc0, K1]) | contradiction |
          (exfalso; simp_all [cstr_null_iff]))
      · have K1 := countStr_ok hm1 hob
        have K2 := countStr_ok hm2 hob
        simp [ZlibNg.Deflate.deflateBound_z, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hw',
          W_BITS, hgz', Ival.get, hld]
        repeat' (first | exact ⟨_, _, rfl⟩ | split | (simp only [bind_app, pure_app, hld, hc, K1, K2]) | contradiction |
          (exfalso; simp_all [cstr_null_iff]))



theorem deflateBound_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) (hr : DHeaderReadable h s)
    (hob : ObjBound h) (n : UInt64) : ∃ r, C.run (ZlibNg.Deflate.deflateBound s n) h = .ok (r, h) := by
  obtain ⟨r, e⟩ := deflateBound_z_inv hv hr hob n
  exact ⟨_, by simp only [C.run, ZlibNg.Deflate.deflateBound, bind_app] at e ⊢; rw [e]; rfl⟩

end ZlibNgF.Proof.DeflateBound
