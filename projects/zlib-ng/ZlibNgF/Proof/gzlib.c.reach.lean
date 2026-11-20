import ZlibNgF.Proof.«gzlib.c.invariant»

/-!
# The calls that only read fields, call only `lseek`, or return a message (`ZlibNgF`)

`gzeof`, `gztell64`, `gztell`, `gzoffset64`, `gzoffset`, `gzerror` on `NULL` or an open file (`GzInv`): they return,
and change at most the file system and the static strings. The induction over `GzReachable` is in
`Proof/gzlib.c.mode.lean`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzReach
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv

/-! ## Calls that only read fields -/

/-- `gzeof` on `NULL` or an open file returns and changes nothing. -/
theorem gzeof_inv {w : World} {h : Heap} {f : GzPtr} (hv : f = none ∨ GzInv w h f) :
    ∃ r, GzRun (gzeof f) w h r w h := by
  rcases hv with rfl | ⟨b, s, rfl, hs, sh, -⟩
  · exact ⟨0, rfl⟩
  · rcases sh.mode with hm | hm
    · exact ⟨s.past, by simp [GzRun, gzeof, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get,
        getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hm, GZ_READ, GZ_WRITE]⟩
    · exact ⟨0, by simp [GzRun, gzeof, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get,
        getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hm, GZ_READ, GZ_WRITE]⟩

/-- `gztell64` on `NULL` or an open file returns and changes nothing: `x.pos + skip` does not overflow (patch
0002 keeps it at most `GZ_OFF_MAX`, and both are above `-2^63`). -/
theorem gztell64_inv {w : World} {h : Heap} {f : GzPtr} (hv : f = none ∨ GzInv w h f) :
    ∃ r, GzRun (gztell64 f) w h r w h := by
  rcases hv with rfl | ⟨b, s, rfl, hs, sh, -⟩
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
theorem lseek_res {w : World} (hl : ∀ n v, w.fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v) (fd : Int32)
    (off : Int64) (wh : Int32) :
    (w.fs.lseekCall fd off wh).1 = -1 ∨ 0 ≤ (w.fs.lseekCall fd off wh).1.toInt := by
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
offset is `-1` (returned at once) or, on a read handle in a world whose `lseek` values are `-1` or not negative, not
negative, so `offset - avail_in` does not overflow. -/
theorem gzoffset64_inv {w : World} {h : Heap} {f : GzPtr}
    (hl : ∀ b s, f = some b → w.gz h b = some s → s.mode = GZ_READ →
      ∀ n v, w.fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v) (hv : f = none ∨ GzInv w h f) :
    ∃ r fs', GzRun (gzoffset64 f) w h r { w with fs := fs' } h ∧ (fs' = w.fs ∨ ∃ fd, fs' = (w.fs.lseekCall fd 0 SEEK_CUR).2) := by
  rcases hv with rfl | ⟨b, s, rfl, hs, sh, -⟩
  · exact ⟨-1, w.fs, rfl, Or.inl rfl⟩
  · obtain ⟨z, hz⟩ := sh.strm
    generalize hL : w.fs.lseekCall s.fd 0 SEEK_CUR = L
    obtain ⟨v, fs'⟩ := L
    have hfs : fs' = (w.fs.lseekCall s.fd 0 SEEK_CUR).2 := by rw [hL]
    have hs' : ({ w with fs := fs' } : World).gz h b = some s := hs
    by_cases hv1 : v = -1
    · subst hv1
      rcases sh.mode with hm | hm <;>
      exact ⟨-1, fs', by
        simp [GzRun, gzoffset64, C.run, rdG, ldGz, getHeap, lm, lseekG, modifyFs, StateT.run, bind, StateT.bind,
          get, getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, set, StateT.set,
          MonadStateOf.set, hs, hm, hL, GZ_READ, GZ_WRITE], Or.inr ⟨_, hfs⟩⟩
    · rcases sh.mode with hm | hm
      · have hres := lseek_res (hl b s rfl hs hm) s.fd 0 SEEK_CUR
        rw [hL] at hres
        have hv0 : 0 ≤ v.toInt := by simpa [hv1] using hres
        have hai := z.avail_in.toNat_lt
        have r1 : -9223372036854775808 ≤ v.toInt - (z.avail_in.toNat : Int) ∧
            v.toInt - (z.avail_in.toNat : Int) < 9223372036854775808 := by
          have := v.toInt_le
          have hmv : Int64.maxValue.toInt = 9223372036854775807 := by decide
          constructor <;> omega
        exact ⟨v - Int64.ofInt (z.avail_in.toNat : Int), fs', by
          simp [GzRun, gzoffset64, C.run, rdG, ldGz, getHeap, lm, lseekG, modifyFs, StateT.run, bind,
            StateT.bind, get, getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, set,
            StateT.set, MonadStateOf.set, hs, hm, hL, hv1, GZ_READ, GZ_WRITE, strmOf, ZlibNg.Inflate.rdZ, chkI64, r1, hs',
            InflateInv.ldStream_app hz], Or.inr ⟨_, hfs⟩⟩
      · exact ⟨v, fs', by
          simp [GzRun, gzoffset64, C.run, rdG, ldGz, getHeap, lm, lseekG, modifyFs, StateT.run, bind,
            StateT.bind, get, getThe, MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, set,
            StateT.set, MonadStateOf.set, hs, hs', hm, hL, hv1, GZ_READ, GZ_WRITE], Or.inr ⟨_, hfs⟩⟩

/-- `gzoffset` is `gzoffset64`. -/
theorem gzoffset_inv {w : World} {h : Heap} {f : GzPtr}
    (hl : ∀ b s, f = some b → w.gz h b = some s → s.mode = GZ_READ →
      ∀ n v, w.fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v) (hv : f = none ∨ GzInv w h f) :
    ∃ r fs', GzRun (gzoffset f) w h r { w with fs := fs' } h ∧ (fs' = w.fs ∨ ∃ fd, fs' = (w.fs.lseekCall fd 0 SEEK_CUR).2) := by
  obtain ⟨r, w', e, hg⟩ := gzoffset64_inv hl hv
  refine ⟨r, w', ?_, hg⟩
  simp only [GzRun, C.run, StateT.run] at e ⊢
  simp only [gzoffset]
  simp [e]

/-- A call that changes only the file system (and not the `gz_state` objects) stays in the frame. -/
theorem gzframe_fs {w w' : World} (h : Heap) (f : GzPtr) (hg : w'.gzs = w.gzs) : GzFrame w h w' h f [] :=
  ⟨DeflateInitPublic.dframe_refl h _ _ _ [], fun _ _ e => e, fun _ _ _ => by rw [hg]⟩

/-! ## String literals -/

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

theorem gzLits_of_idx {lit : String} {i : Nat} (hi : gzLits.findIdx? (· == lit) = some i) : gzLits[i]? = some lit := by
  rw [Array.findIdx?_eq_some_iff_getElem] at hi
  obtain ⟨hlt, he, -⟩ := hi
  rw [Array.getElem?_eq_getElem hlt]
  simpa using he

/-- What `gzLit` of a literal of the table does: it returns a pointer and, at the literal's first use, adds one
static string at the next free key; nothing else changes. -/
theorem gzLit_step (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i) (w : World) (h : Heap) :
    ∃ p w' h', C.run ((gzLit lit).run w) h = .ok ((p, w'), h') ∧ w'.gzs = w.gzs ∧ w'.fs = w.fs ∧
      (h' = h ∨ ∃ a, h' = { h with consts := upd h.consts h.consts.arr.size (some a) }) ∧ (LitOk w h → LitOk w' h') := by
  cases hk : w.litKeys.find? (·.1 == i) with
  | some e =>
    exact ⟨.ref (.const e.2) 0, w, h, by simp [gzLit, hi, hk, C.run, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure], rfl, rfl, Or.inl rfl, id⟩
  | none =>
    refine ⟨.ref (.const h.consts.arr.size) 0, { w with litKeys := (i, h.consts.arr.size) :: w.litKeys },
      { h with consts := upd h.consts h.consts.arr.size (some (Heap.litBytes lit)) }, ?_, rfl, rfl, Or.inr ⟨_, rfl⟩,
      fun hw => ?_⟩
    · simp [gzLit, hi, hk, C.run, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        StateT.pure, lm, StateT.lift, newConst, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨lit, gzLits_of_idx hi, by simp⟩
      · exact (LitOk.ext (w' := w) hw rfl fun k a e => consts_grow h _ k a e) p hp

/-- A step that changes only static strings (by adding one) and leaves the `gz_state` objects alone is in the
frame. -/
theorem gzframe_lit {w w' : World} {h h' : Heap} (f : GzPtr) (hg : w'.gzs = w.gzs)
    (hh : h' = h ∨ ∃ a, h' = { h with consts := upd h.consts h.consts.arr.size (some a) }) : GzFrame w h w' h' f [] := by
  rcases hh with e | ⟨a, e⟩ <;> rw [e]
  · exact ⟨DeflateInitPublic.dframe_refl h _ _ _ [], fun _ _ e => e, fun _ _ _ => by rw [hg]⟩
  · exact ⟨DeflateInitPublic.dframe_refl h _ _ _ [], fun k b e => consts_grow h a k b e, fun _ _ _ => by rw [hg]⟩

theorem lit_oom : gzLits.findIdx? (· == "out of memory") = some 0 := by simp [gzLits, List.findIdx?_cons]
theorem lit_empty : gzLits.findIdx? (· == "") = some 12 := by simp [gzLits, List.findIdx?_cons]

/-- `w'`, `h'` differ from `w`, `h` at most by a static string added at the next free key (and its key). -/
def LitStep (w : World) (h : Heap) (w' : World) (h' : Heap) : Prop :=
  w'.gzs = w.gzs ∧ w'.fs = w.fs ∧ (h' = h ∨ ∃ a, h' = { h with consts := upd h.consts h.consts.arr.size (some a) }) ∧
    (LitOk w h → LitOk w' h')

theorem LitStep.refl (w : World) (h : Heap) : LitStep w h w h := ⟨rfl, rfl, Or.inl rfl, id⟩

/-- `gzerror` on `NULL` or an open file returns; it changes only static strings (a literal at its first use). -/
theorem gzerror_inv {w : World} {h : Heap} {f : GzPtr} (e : Bool) (hv : f = none ∨ GzInv w h f) :
    ∃ r w' h', GzRun (gzerror f e) w h r w' h' ∧ GzFrame w h w' h' f [] ∧ LitStep w h w' h' := by
  rcases hv with rfl | ⟨b, s, rfl, hs, sh, -⟩
  · exact ⟨_, w, h, rfl, gzframe_refl w h none [], LitStep.refl w h⟩
  · have hmode : ¬(¬s.mode = GZ_READ ∧ ¬s.mode = GZ_WRITE) := by
      rcases sh.mode with hm | hm <;> simp [hm]
    by_cases hm : s.err = ZlibNg.Inflate.Z_MEM_ERROR
    · obtain ⟨p, w', h', el, hg, hf, hh, hL⟩ := gzLit_step _ _ lit_oom w h
      simp only [C.run, StateT.run] at el
      cases e
      · refine ⟨(p, none), w', h', ?_, gzframe_lit _ hg hh, hg, hf, hh, hL⟩
        simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
          MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, el]
      · refine ⟨(p, some s.err), w', h', ?_, gzframe_lit _ hg hh, hg, hf, hh, hL⟩
        simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
          MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, el]
    · rcases sh.msg.msg with hn | ⟨c, n, hc, _⟩
      · obtain ⟨p, w', h', el, hg, hf, hh, hL⟩ := gzLit_step _ _ lit_empty w h
        simp only [C.run, StateT.run] at el
        cases e
        · refine ⟨(p, none), w', h', ?_, gzframe_lit _ hg hh, hg, hf, hh, hL⟩
          simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
            MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, hn, el, Ival.get, liftM, monadLift, MonadLift.monadLift]
        · refine ⟨(p, some s.err), w', h', ?_, gzframe_lit _ hg hh, hg, hf, hh, hL⟩
          simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
            MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, hn, el, Ival.get, liftM, monadLift, MonadLift.monadLift]
      · cases e
        · refine ⟨(.ref (.heap c) 0, none), w, h, ?_, gzframe_refl w h _ [], LitStep.refl w h⟩
          simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
            MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, hc, Ival.get, liftM, monadLift, MonadLift.monadLift]
        · refine ⟨(.ref (.heap c) 0, some s.err), w, h, ?_, gzframe_refl w h _ [], LitStep.refl w h⟩
          simp [GzRun, gzerror, C.run, rdG, ldGz, getHeap, lm, StateT.run, bind, StateT.bind, get, getThe,
            MonadStateOf.get, StateT.get, StateT.lift, pure, StateT.pure, hs, hmode, hm, hc, Ival.get, liftM, monadLift, MonadLift.monadLift]

end ZlibNgF.Proof.GzReach
