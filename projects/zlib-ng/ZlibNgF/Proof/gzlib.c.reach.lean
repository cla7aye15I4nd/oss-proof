import ZlibNgF.Proof.«gzlib.c.invariant»

/-!
# Reachable gz files have the structural invariant (`ZlibNgF`)

`greach_inv (P : GPending) : GzReachable w h f → GzInv w h f`, by induction over `GzReachable`, as for inflate
(`Proof/inflate.c.reach.lean`). `GPending` holds the obligations still to prove: a successful `gzopen`, `gzopen64` or
`gzdopen` leaves the invariant, every public step keeps it, and a caller step keeps it. From `GPending` the goals of
the calls that only read fields, or call only `lseek`, follow here (`gzeof`, `gztell64`, `gztell`, `gzoffset64`,
`gzoffset`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzReach
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv

/-- The obligations still to prove. -/
structure GPending : Prop where
  gzopen : ∀ (w h w' h' : _) (path mode : BPtr) (f : GzPtr),
    GzWF w h → CStr h path → CStr h mode → GzRun (gzopen path mode) w h f w' h' → f ≠ none → GzInv w' h' f
  gzopen64 : ∀ (w h w' h' : _) (path mode : BPtr) (f : GzPtr),
    GzWF w h → CStr h path → CStr h mode → GzRun (gzopen64 path mode) w h f w' h' → f ≠ none → GzInv w' h' f
  gzdopen : ∀ (w h w' h' : _) (fd : Int32) (mode : BPtr) (f : GzPtr),
    GzWF w h → CStr h mode → GzRun (gzdopen fd mode) w h f w' h' → f ≠ none → GzInv w' h' f
  step : ∀ (w h w' h' : _) (f : GzPtr), GzInv w h f → GzStep w h w' h' f → GzInv w' h' f
  caller : ∀ (w h w' h' : _) (f : GzPtr), GzInv w h f → GzCallerStep w h w' h' f → GzInv w' h' f

/-- **The induction.** Every reachable file has the invariant, given the pending obligations. -/
theorem greach_inv (P : GPending) {w : World} {h : Heap} {f : GzPtr} (hr : GzReachable w h f) : GzInv w h f := by
  induction hr with
  | gzopen w h w' h' path mode f hwf hp hm e hne => exact P.gzopen w h w' h' path mode f hwf hp hm e hne
  | gzopen64 w h w' h' path mode f hwf hp hm e hne => exact P.gzopen64 w h w' h' path mode f hwf hp hm e hne
  | gzdopen w h w' h' fd mode f hwf hm e hne => exact P.gzdopen w h w' h' fd mode f hwf hm e hne
  | step w h w' h' f _ hs ih => exact P.step w h w' h' f ih hs
  | caller w h w' h' f _ hc ih => exact P.caller w h w' h' f ih hc

/-- An accepted file is `NULL` or has the invariant. -/
theorem handle_inv (P : GPending) {w : World} {h : Heap} {f : GzPtr} (hh : GzHandle w h f) :
    f = none ∨ GzInv w h f := by
  rcases hh with rfl | hr
  · exact Or.inl rfl
  · exact Or.inr (greach_inv P hr)

/-! ## Calls that only read fields -/

/-- `gzeof` on `NULL` or an open file returns and changes nothing. -/
theorem gzeof_inv {w : World} {h : Heap} {f : GzPtr} (hv : f = none ∨ GzInv w h f) :
    ∃ r, GzRun (gzeof f) w h r w h := by
  rcases hv with rfl | ⟨b, s, rfl, hs, sh⟩
  · exact ⟨0, rfl⟩
  · rcases sh.mode with hm | hm
    · exact ⟨s.past, by simp [GzRun, gzeof, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get,
        getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hm, GZ_READ, GZ_WRITE]⟩
    · exact ⟨0, by simp [GzRun, gzeof, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get,
        getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hm, GZ_READ, GZ_WRITE]⟩

/-- `gztell64` on `NULL` or an open file returns and changes nothing: `x.pos + skip` does not overflow (patch
0004 keeps it at most `GZ_OFF_MAX`, and both are above `-2^63`). -/
theorem gztell64_inv {w : World} {h : Heap} {f : GzPtr} (hv : f = none ∨ GzInv w h f) :
    ∃ r, GzRun (gztell64 f) w h r w h := by
  rcases hv with rfl | ⟨b, s, rfl, hs, sh⟩
  · exact ⟨-1, rfl⟩
  · have p := sh.pos
    have hmax : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide
    have e1 := p.skip_nonneg
    have e2 := p.pos_skip
    have e3 := p.pos_lower
    have r1 : -9223372036854775808 ≤ s.pos.toInt + s.skip.toInt ∧
        s.pos.toInt + s.skip.toInt < 9223372036854775808 := by
      constructor <;> omega
    have r0 : -9223372036854775808 ≤ s.pos.toInt ∧ s.pos.toInt < 9223372036854775808 := by
      constructor <;> omega
    rcases sh.mode with hm | hm <;> by_cases hp : s.past = 0 <;>
      simp [GzRun, gztell64, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
        MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hm, hp, GZ_READ, GZ_WRITE, chkI64, r1, r0, Int.add_zero]

/-- `gztell` is `gztell64`. -/
theorem gztell_inv {w : World} {h : Heap} {f : GzPtr} (hv : f = none ∨ GzInv w h f) :
    ∃ r, GzRun (gztell f) w h r w h := by
  obtain ⟨r, e⟩ := gztell64_inv hv
  refine ⟨r, ?_⟩
  simp only [GzRun, C.run, StateT.run] at e ⊢
  simp only [gztell]
  simp [e]

/-- An `lseek` result in a well-formed world is `-1` or not negative: the regular model returns an offset in
`[0, 2^63)` or `-1`, and `GzWF` admits only such oracle values. -/
theorem lseek_res {w : World} {h : Heap} (hwf : GzWF w h) (fd : Int32) (off : Int64) (wh : Int32) :
    (w.fs.lseekCall fd off wh).1 = -1 ∨ 0 ≤ (w.fs.lseekCall fd off wh).1.toInt := by
  have hl := hwf.2.2.2.2.2.2.2
  unfold Fs.lseekCall
  simp only [Fs.tick]
  split
  · next hc =>
    unfold Fs.lseekReg
    simp only
    split
    · next o _ =>
      split
      · exact Or.inl rfl
      · next b _ =>
        by_cases h1 : b + off.toInt < 0
        · simp [h1]
        · by_cases h2 : b + off.toInt ≥ 2 ^ 63
          · have h2' : (9223372036854775808 : Int) ≤ b + off.toInt := h2
            simp [h1, h2']
          · simp only [h1, h2, ite_false]
            right
            show 0 ≤ (Int64.ofInt (b + off.toInt)).toInt
            rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
            omega
    · exact Or.inl rfl
  · exact Or.inl rfl
  · next v hc =>
    rcases hl _ v hc with e | e
    · exact Or.inl e
    · exact Or.inr (by simpa using Int64.le_iff_toInt_le.mp e)

/-- `gzoffset64` on `NULL` or an open file returns, and changes only the file system (the `lseek` call): the
offset is `-1` (returned at once) or not negative, so `offset - avail_in` does not overflow. -/
theorem gzoffset64_inv {w : World} {h : Heap} {f : GzPtr} (hwf : GzWF w h) (hv : f = none ∨ GzInv w h f) :
    ∃ r w', GzRun (gzoffset64 f) w h r w' h ∧ w'.gzs = w.gzs := by
  rcases hv with rfl | ⟨b, s, rfl, hs, sh⟩
  · exact ⟨-1, w, rfl, rfl⟩
  · obtain ⟨z, hz⟩ := sh.strm
    have hres := lseek_res hwf s.fd 0 SEEK_CUR
    generalize hL : w.fs.lseekCall s.fd 0 SEEK_CUR = L at hres
    obtain ⟨v, fs'⟩ := L
    have hs' : ({ w with fs := fs' } : World).gz h b = some s := hs
    by_cases hv1 : v = -1
    · subst hv1
      rcases sh.mode with hm | hm <;>
      exact ⟨-1, { w with fs := fs' }, by
        simp [GzRun, gzoffset64, C.run, rdG, ldGz, getHeap, lm, lseekG, modifyFs, StateT.run, bind, StateT.bind,
          get, getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, set, StateT.set,
          MonadStateOf.set, hs, hm, hL, GZ_READ, GZ_WRITE], rfl⟩
    · have hv0 : 0 ≤ v.toInt := by simpa [hv1] using hres
      have hai := z.avail_in.toNat_lt
      have r1 : -9223372036854775808 ≤ v.toInt - (z.avail_in.toNat : Int) ∧
          v.toInt - (z.avail_in.toNat : Int) < 9223372036854775808 := by
        have := v.toInt_le
        have hmv : Int64.maxValue.toInt = 9223372036854775807 := by decide
        constructor <;> omega
      rcases sh.mode with hm | hm
      · exact ⟨v - Int64.ofInt (z.avail_in.toNat : Int), { w with fs := fs' }, by
          simp [GzRun, gzoffset64, C.run, rdG, ldGz, getHeap, lm, lseekG, modifyFs, StateT.run, bind,
            StateT.bind, get, getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, set,
            StateT.set, MonadStateOf.set, hs, hm, hL, hv1, GZ_READ, GZ_WRITE, strmOf, ZlibNg.Inflate.rdZ, chkI64, r1, hs',
            InflateInv.ldStream_app hz], rfl⟩
      · exact ⟨v, { w with fs := fs' }, by
          simp [GzRun, gzoffset64, C.run, rdG, ldGz, getHeap, lm, lseekG, modifyFs, StateT.run, bind,
            StateT.bind, get, getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, set,
            StateT.set, MonadStateOf.set, hs, hs', hm, hL, hv1, GZ_READ, GZ_WRITE], rfl⟩

theorem gzeof_safety_of (P : GPending) : Goal.gzeof_safety := by
  intro w h f _ hh
  obtain ⟨r, e⟩ := gzeof_inv (handle_inv P hh)
  exact ⟨r, w, h, e, gzframe_refl w h f []⟩

theorem gztell64_safety_of (P : GPending) : Goal.gztell64_safety := by
  intro w h f _ hh
  obtain ⟨r, e⟩ := gztell64_inv (handle_inv P hh)
  exact ⟨r, w, h, e, gzframe_refl w h f []⟩

theorem gztell_safety_of (P : GPending) : Goal.gztell_safety := by
  intro w h f _ hh
  obtain ⟨r, e⟩ := gztell_inv (handle_inv P hh)
  exact ⟨r, w, h, e, gzframe_refl w h f []⟩

/-- `gzoffset` is `gzoffset64`. -/
theorem gzoffset_inv {w : World} {h : Heap} {f : GzPtr} (hwf : GzWF w h) (hv : f = none ∨ GzInv w h f) :
    ∃ r w', GzRun (gzoffset f) w h r w' h ∧ w'.gzs = w.gzs := by
  obtain ⟨r, w', e, hg⟩ := gzoffset64_inv hwf hv
  refine ⟨r, w', ?_, hg⟩
  simp only [GzRun, C.run, StateT.run] at e ⊢
  simp only [gzoffset]
  simp [e]

/-- A call that changes only the file system (and not the `gz_state` objects) stays in the frame. -/
theorem gzframe_fs {w w' : World} (h : Heap) (f : GzPtr) (hg : w'.gzs = w.gzs) : GzFrame w h w' h f [] :=
  ⟨DeflateInitPublic.dframe_refl h _ _ _ [], fun _ _ e => e, fun _ _ _ => by rw [hg]⟩

theorem gzoffset64_safety_of (P : GPending) : Goal.gzoffset64_safety := by
  intro w h f hwf hh
  obtain ⟨r, w', e, hg⟩ := gzoffset64_inv hwf (handle_inv P hh)
  exact ⟨r, w', h, e, gzframe_fs h f hg⟩

theorem gzoffset_safety_of (P : GPending) : Goal.gzoffset_safety := by
  intro w h f hwf hh
  obtain ⟨r, w', e, hg⟩ := gzoffset_inv hwf (handle_inv P hh)
  exact ⟨r, w', h, e, gzframe_fs h f hg⟩

/-! ## String literals -/

/-- What `gzLit` of a literal of the table does: it returns a pointer and, at the literal's first use, adds one
static string at the next free key; nothing else changes. -/
theorem gzLit_step (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i) (w : World) (h : Heap) :
    ∃ p w' h', C.run ((gzLit lit).run w) h = .ok ((p, w'), h') ∧ w'.gzs = w.gzs ∧
      (h' = h ∨ ∃ a, h' = { h with consts := upd h.consts h.consts.arr.size (some a) }) := by
  cases hk : w.litKeys.find? (·.1 == i) with
  | some e =>
    exact ⟨.ref (.const e.2) 0, w, h, by simp [gzLit, hi, hk, C.run, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure], rfl, Or.inl rfl⟩
  | none =>
    refine ⟨.ref (.const h.consts.arr.size) 0, { w with litKeys := (i, h.consts.arr.size) :: w.litKeys },
      { h with consts := upd h.consts h.consts.arr.size (some (Heap.litBytes lit)) }, ?_, rfl, Or.inr ⟨_, rfl⟩⟩
    simp [gzLit, hi, hk, C.run, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, lm, StateT.lift, newConst, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

/-- Adding a static string at the next free key keeps every static string there. -/
theorem consts_grow (h : Heap) (a : Array UInt8) (k : Nat) (b : Array UInt8) (hk : h.consts k = some b) :
    (upd h.consts h.consts.arr.size (some a)) k = some b := by
  have hne : k ≠ h.consts.arr.size := by
    intro e; subst e
    have : h.consts h.consts.arr.size = none := by
      show h.consts.get h.consts.arr.size = none
      rw [Tbl.get_eq]; simp; rfl
    rw [this] at hk; cases hk
  rw [upd_ne _ _ _ _ hne]; exact hk

/-- A step that changes only static strings (by adding one) and leaves the `gz_state` objects alone is in the
frame. -/
theorem gzframe_lit {w w' : World} {h h' : Heap} (f : GzPtr) (hg : w'.gzs = w.gzs)
    (hh : h' = h ∨ ∃ a, h' = { h with consts := upd h.consts h.consts.arr.size (some a) }) : GzFrame w h w' h' f [] := by
  rcases hh with e | ⟨a, e⟩ <;> rw [e]
  · exact ⟨DeflateInitPublic.dframe_refl h _ _ _ [], fun _ _ e => e, fun _ _ _ => by rw [hg]⟩
  · exact ⟨DeflateInitPublic.dframe_refl h _ _ _ [], fun k b e => consts_grow h a k b e, fun _ _ _ => by rw [hg]⟩

theorem lit_oom : gzLits.findIdx? (· == "out of memory") = some 0 := by simp [gzLits, List.findIdx?_cons]
theorem lit_empty : gzLits.findIdx? (· == "") = some 12 := by simp [gzLits, List.findIdx?_cons]

/-- `gzerror` on `NULL` or an open file returns; it changes only static strings (a literal at its first use). -/
theorem gzerror_inv {w : World} {h : Heap} {f : GzPtr} (e : Bool) (hv : f = none ∨ GzInv w h f) :
    ∃ r w' h', GzRun (gzerror f e) w h r w' h' ∧ GzFrame w h w' h' f [] := by
  rcases hv with rfl | ⟨b, s, rfl, hs, sh⟩
  · exact ⟨_, w, h, rfl, gzframe_refl w h none []⟩
  · have hmode : ¬(¬s.mode = GZ_READ ∧ ¬s.mode = GZ_WRITE) := by
      rcases sh.mode with hm | hm <;> simp [hm]
    by_cases hm : s.err = ZlibNg.Inflate.Z_MEM_ERROR
    · obtain ⟨p, w', h', el, hg, hh⟩ := gzLit_step _ _ lit_oom w h
      simp only [C.run, StateT.run] at el
      cases e
      · refine ⟨(p, none), w', h', ?_, gzframe_lit _ hg hh⟩
        simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
          MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, el]
      · refine ⟨(p, some s.err), w', h', ?_, gzframe_lit _ hg hh⟩
        simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
          MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, el]
    · rcases sh.msg.msg with hn | ⟨c, n, hc, _⟩
      · obtain ⟨p, w', h', el, hg, hh⟩ := gzLit_step _ _ lit_empty w h
        simp only [C.run, StateT.run] at el
        cases e
        · refine ⟨(p, none), w', h', ?_, gzframe_lit _ hg hh⟩
          simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
            MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, hn, el, Ival.get, liftM, monadLift, MonadLift.monadLift]
        · refine ⟨(p, some s.err), w', h', ?_, gzframe_lit _ hg hh⟩
          simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
            MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, hn, el, Ival.get, liftM, monadLift, MonadLift.monadLift]
      · cases e
        · refine ⟨(.ref (.heap c) 0, none), w, h, ?_, gzframe_refl w h _ []⟩
          simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
            MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, hc, Ival.get, liftM, monadLift, MonadLift.monadLift]
        · refine ⟨(.ref (.heap c) 0, some s.err), w, h, ?_, gzframe_refl w h _ []⟩
          simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
            MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, hc, Ival.get, liftM, monadLift, MonadLift.monadLift]

theorem gzerror_safety_of (P : GPending) : Goal.gzerror_safety := by
  intro w h f e _ hh
  exact gzerror_inv e (handle_inv P hh)

end ZlibNgF.Proof.GzReach
