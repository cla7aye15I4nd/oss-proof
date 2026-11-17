import ZlibF.Proof.«inflate.c.meaning-trip-body»
import ZlibF.Proof.«inflate.c.meaning-trip-codes»
import ZlibF.Proof.«inflate.c.meaning-trip-trailer»
import ZlibF.Proof.«inflate.c.meaning-stop-short»

/-!
# inflate.c: why a trip of the mode loop leaves (zlib rows)

`TripMeaning` keeps the format meaning at a leave (`LoopMatches`) and drops its cause. The cause
is what `StopShort` needs: a leave for want of input holds bits that do not complete the field
its mode waits for (`LeaveShort`), so a trip that left that way has not read a whole valid stream
(`LoopMatches.starved_not_end`). `TripLeaveCause` names the causes: a code other than `Z_OK` in `ret`
(`DONE` sets `Z_STREAM_END`), a `Z_BLOCK` or `Z_TREES` stop, no output room at the start of the
trip, or no input with `LeaveShort`. `CauseAt` is the cause row of a group of modes, for every
trip from `LoopMatches` that leaves.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The cause of a leave from the trip start registers `l` to the leave registers `l'`, heap `h'`. -/
def TripLeaveCause (c : Ctx) (h' : Heap) (l l' : IL) : Prop :=
  l'.ret ≠ Z_OK ∨ c.flush = Z_BLOCK ∨ c.flush = Z_TREES ∨ l.left = 0 ∨
    (l'.have_ = 0 ∧ LeaveShort c h' l')

/-- Every trip from a state with `P` that leaves states its cause. -/
def CauseAt (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (P : InflateState → Prop) : Prop :=
  ∀ h l, CallSide c r l h → LoopMatches c f h l →
    (∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → P s) →
    ∀ l' h', runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l'), h') → TripLeaveCause c h' l l'

theorem TripLeaveCause.of_step {c : Ctx} {h' : Heap} {l l' : IL}
    (step : (l'.have_ = 0 ∧ LeaveShort c h' l') ∨ c.flush = Z_TREES ∨ l.left = 0) :
    TripLeaveCause c h' l l' := by
  rcases step with s | s | s
  · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
  · exact Or.inr (Or.inr (Or.inl s))
  · exact Or.inr (Or.inr (Or.inr (Or.inl s)))

/-- A run that is equal to a known one ends the same way. -/
theorem same_leave {p : X Unit} {l l' l1 : IL} {h h' h1 : Heap} {result : Except Ex Unit}
    (run : runX p l h = .ok ((.error Ex.leave, l'), h')) (run1 : runX p l h = .ok ((result, l1), h1)) :
    result = .error Ex.leave ∧ l1 = l' ∧ h1 = h' := by
  have same := run1.symm.trans run
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  exact ⟨same.1.1, same.1.2, same.2⟩

/-- Stored blocks (`STORED`, `COPY_`, `COPY`). -/
theorem cause_stored (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) := by
  intro h l side loop mode l' h' run
  obtain ⟨zs, z, s, E, j⟩ := side.env
  have bounds := at_state (P := fun s => s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) E.st E.hs
    (window_bounds j.good.inv.win)
  rcases mode zs s E.st E.hs with m | m | m
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningBlock.stored_step loop E.strm E.hz (at_state (P := fun s => s.mode = STORED) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_STORED E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · exact TripLeaveCause.of_step cause
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningCopy.copy_start_step loop E.strm E.hz (at_state (P := fun s => s.mode = COPY_) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_COPY_start E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s
      · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl s)))
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningCopy.copy_step loop E.strm E.hz (at_state (P := fun s => s.mode = COPY) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_COPY E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s
      · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl s)))
    · rw [e] at e'; cases e'

/-- `TYPE`/`TYPEDO` before the last block. -/
theorem cause_type_open (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) := by
  intro h l side loop mode l' h' run
  obtain ⟨zs, z, s, E, j⟩ := side.env
  obtain ⟨m, _⟩ := mode zs s E.st E.hs
  rcases m with m | m
  · obtain ⟨result, l1, h1, run1, ends⟩ := MeaningBlock.type_step loop E.strm E.hz j.globals mode
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_TYPE E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s | s
      · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
      · exact Or.inr (Or.inl s)
      · exact Or.inr (Or.inr (Or.inl s))
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ := MeaningBlock.typedo_step loop E.strm E.hz j.globals mode
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_TYPEDO E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s
      · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
      · exact Or.inr (Or.inr (Or.inl s))
    · rw [e] at e'; cases e'

/-- `DONE`: `Z_STREAM_END` in `ret`. -/
theorem cause_done (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = DONE) := by
  intro h l side _ mode l' h' run
  obtain ⟨zs, z, s, E, _⟩ := side.env
  have run1 := (inflate_dispatch_DONE E l (mode zs s E.st E.hs)).trans (inflate_DONE_run c l h)
  obtain ⟨_, rfl, rfl⟩ := same_leave run run1
  exact Or.inl (show Z_STREAM_END ≠ Z_OK by decide)

theorem TripLeaveCause.of_short {c : Ctx} {h' : Heap} {l l' : IL}
    (step : (l'.have_ = 0 ∧ LeaveShort c h' l') ∨ l.left = 0) : TripLeaveCause c h' l l' := by
  rcases step with s | s
  · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl s)))

/-- The cause from the ends of a decode step. -/
theorem cause_of_ends {c : Ctx} {f : LoopFrame} {h' : Heap} {l l' : IL} {result : Except Ex Unit}
    {B : Prop}
    (ends : (result = .error Ex.leave ∧ ((l'.have_ = 0 ∧ LeaveShort c h' l') ∨ l.left = 0) ∧
        LoopMatches c f h' l') ∨
      (result = .ok () ∧ B)) (leave : result = .error Ex.leave) : TripLeaveCause c h' l l' := by
  rcases ends with ⟨_, cause, _⟩ | ⟨e, _⟩
  · exact TripLeaveCause.of_short cause
  · rw [leave] at e; cases e

open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningMatch
open Zlib.Inflate.Proofs.MeaningDistance Zlib.Inflate.Proofs.MeaningLength in
/-- The Huffman codes (`LEN_` to `LIT`). -/
theorem cause_codes (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => LEN_ ≤ s.mode ∧ s.mode ≤ LIT) := by
  intro h l side loop mode l' h' leaveRun
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, _, _⟩ := id side
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  have m0 := mode zs s st E.hs
  have bounds := at_state (P := fun s => s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) st E.hs
    (window_bounds j.good.inv.win)
  have sane := at_state (P := fun s => s.sane ≠ 0) st E.hs (by rw [j.pending.sane]; decide)
  have wsizeBits := at_state (P := fun s => s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat)
    st E.hs (code_wsize_bits j.good.inv.win)
  have ring := at_state (P := fun s => s.whave < s.wsize → s.wnext = s.whave) st E.hs
    (code_ring j.good.inv.win)
  have privateWindow := at_state
    (P := fun s => ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d) st E.hs
    (code_private_window j.good buf)
  have rawWidth := code_raw_width j st E.hs loop
  have binv : BitInv h l (f.inp.drop (loopRead l)) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, binv, _⟩ := loop
    exact binv
  have buffers : DispatchBuffers h r l (f.inp.drop (loopRead l)) :=
    ⟨buf.input, buf.output, buf.separate, binv⟩
  have tablesAt : DataTableMode s.mode → ∀ zs' s', c.st = some (.tab zs') →
      h.istates zs' = some s' → DataTablesSafe h s' :=
    fun dm => at_state (P := fun s => DataTablesSafe h s) st E.hs (j.tables dm)
  rcases code_mode_cases m0 with m | m | m | m | m | m | m
  · -- LEN_
    by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
    · obtain ⟨l1, h1, run, _⟩ := len_start_fast loop E j buffers m fast rawWidth
      obtain ⟨e, _, _⟩ := same_leave leaveRun ((inflate_dispatch_LEN_start E l m).trans run)
      cases e
    · obtain ⟨result, l1, h1, run, ends⟩ := len__step loop E.strm E.hz fast
        (at_state (P := fun s => s.mode = LEN_) st E.hs m)
        (tablesAt (by rw [m]; unfold DataTableMode; decide))
        bounds sane wsizeBits ring privateWindow rawWidth
      obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_LEN_start E l m).trans run)
      exact cause_of_ends ends e
  · -- LEN
    by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
    · obtain ⟨l1, h1, run, _, _⟩ := fast_len_meaning _ _ _ _ _ _ loop E.strm E.hz fast
        (at_state_id (P := fun zs s => s.mode = LEN ∧ Good h r zs z s ∧ DataTablesSafe h s ∧
          DataPendingInvariant s) st E.hs
          ⟨m, j.good, j.tables (by rw [m]; unfold DataTableMode; decide), j.pending⟩)
        j.platform buffers rawWidth
      obtain ⟨e, _, _⟩ := same_leave leaveRun ((inflate_dispatch_LEN E l m).trans run)
      cases e
    · obtain ⟨result, l1, h1, run, ends⟩ := len_slow_step loop E.strm E.hz fast
        (at_state (P := fun s => s.mode = LEN ∨ s.mode = LEN_) st E.hs (Or.inl m))
        (tablesAt (by rw [m]; unfold DataTableMode; decide))
        bounds sane wsizeBits ring privateWindow rawWidth
      obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_LEN E l m).trans run)
      exact cause_of_ends ends e
  · -- LENEXT
    obtain ⟨result, l1, h1, run, ends⟩ := lenext_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = LENEXT) st E.hs m)
      (tablesAt (by rw [m]; unfold DataTableMode; decide))
      (at_state (P := fun s => BackBound s 15) st E.hs (j.pending.lenext m).2.2.2)
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_LENEXT E l m).trans run)
    exact cause_of_ends ends e
  · -- DIST
    obtain ⟨result, l1, h1, run, ends⟩ := dist_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = DIST) st E.hs m)
      (tablesAt (by rw [m]; unfold DataTableMode; decide))
      (at_state (P := fun s => BackBound s 20) st E.hs (j.pending.dist m).2)
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_DIST E l m).trans run)
    exact cause_of_ends ends e
  · -- DISTEXT
    obtain ⟨result, l1, h1, run, ends⟩ := distext_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = DISTEXT) st E.hs m)
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_DISTEXT E l m).trans run)
    exact cause_of_ends ends e
  · -- MATCH
    obtain ⟨result, l1, h1, run, ends⟩ := match_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = MATCH) st E.hs m)
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_MATCH E l m).trans run)
    rcases ends with ⟨_, left, _⟩ | ⟨e', _⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl left)))
    · rw [e] at e'; cases e'
  · -- LIT
    obtain ⟨result, l1, h1, run, ends⟩ := lit_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = LIT) st E.hs m) bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_LIT E l m).trans run)
    rcases ends with ⟨_, left, _⟩ | ⟨e', _⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl left)))
    · rw [e] at e'; cases e'

open MeaningCheck MeaningTrailer in
/-- `CHECK` of a zlib stream: the only leave with `ret = Z_OK` is its `NEEDBITS(32)`; past it
`LENGTH` (no length field: `flags = 0`) ends the stream with `Z_STREAM_END`. -/
theorem cause_check_zlib (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (zlib : f.wrap = .zlib) :
    CauseAt c f r (fun s => s.mode = CHECK) := by
  intro h l side loop check l' h' leaveRun
  obtain ⟨zs, z, s, E, j⟩ := side.env
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    have globals := j.globals
    unfold LibraryGlobals at globals
    rw [Zlib.Crc32.Proofs.StaticsOK, globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨zs0, s0, callOut0, consumed0, held0, stage0, st, hs, _, config0, _, _, binv0, leftLe0, pend0,
    putEq0, outBytes0, _, _, _, _, bitsEq0, heldBits0, parsed0, stageM0, wrapM0, _⟩ := loop
  have e0 : zs0 = zs := by rw [E.st] at st; cases st; rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs.symm.trans E.hs)
  subst e1
  have mode : s0.mode = CHECK := check zs0 s0 st hs
  obtain ⟨header0, out0, bytes0, rfl⟩ := stage_of_check stageM0 mode
  obtain ⟨flagsM, _, ⟨checkFacts0, _, _⟩⟩ := wrapM0
  have wrapped : f.wrap ≠ .raw := by rw [zlib]; decide
  have wrapNZ : s0.wrap ≠ 0 := fun zero => wrapped (wrapCode_zero (config0.1.symm.trans zero))
  have notGzip : ¬ IsGzipHeader header0 := by
    obtain ⟨_, _, _, wh, _⟩ := parsed0
    rw [zlib] at wh
    obtain ⟨window, zh, _⟩ := wh
    exact zlibHeader_not_gzip zh
  have flags0 : s0.flags = 0 := by
    unfold FlagsMatch at flagsM
    rw [zlib] at flagsM
    simpa [notGzip] using flagsM
  have outNat : (l.out_ - l.left).toNat = loopPending l :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr leftLe0)
  have putAt : chkCond s0 (l.out_ - l.left) = true → ∃ ref off array, l.put = .ref ref off ∧
      Space.get h ref = some array ∧ (l.out_ - l.left).toNat ≤ off ∧ off ≤ array.size := by
    intro cond
    have nonzero : (l.out_ - l.left) ≠ 0 := by
      simp only [chkCond, Bool.and_eq_true, bne_iff_ne, ne_eq] at cond
      exact cond.2
    have pos : 0 < (l.out_ - l.left).toNat :=
      Nat.pos_of_ne_zero (fun zero => nonzero (UInt32.toNat_inj.mp (by simpa using zero)))
    rcases outBytes0 with ⟨_, len0, _⟩ | ⟨r0, i0, a0, ptr0, get0, fit0, _⟩
    · have := pend0.1
      omega
    · refine ⟨r0, i0 + callOut0.length, a0, by rw [putEq0, ptr0]; rfl, get0, ?_, fit0⟩
      have := pend0.1
      omega
  obtain ⟨rr, l1, _, needRun, _, _, _, leaveRun1, okRun⟩ :=
    inflate_CHECK_value_run (l.out_ - l.left) rfl E.strm st E.hz hs wrapNZ binv0 statics putAt
  have rrKinds : rr = .ok () ∨ rr = .error Ex.leave := by
    obtain ⟨result, l2, _, run2, _, _, _, _, _, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor binv0 32 (by decide)
    have same := needRun.symm.trans run2
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    rw [same.1.1]
    exact kinds
  have dispatchEq := inflate_dispatch_CHECK E l mode
  cases rr with
  | error x =>
    cases x with
    | leave =>
      obtain ⟨have0, _, bits32, run1⟩ := leaveRun1 rfl
      obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun (dispatchEq.trans run1)
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨have0, LeaveShort.of_state st hs ?_⟩)))
      have len : (natBits l'.bits.toNat l'.hold.toNat).length < 32 := by
        rw [natBits_length]; exact bits32
      unfold ShortAt
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨mode, wrapNZ, len⟩)))))))))))))
    | ret v => rcases rrKinds with e | e <;> cases e
  | ok u =>
    obtain ⟨_, v, _, badRun, matchRun⟩ := okRun rfl
    by_cases bad : (s0.wrap &&& 4) ≠ 0 ∧
        (if s0.flags ≠ 0 then l1.hold else ZSWAP32 l1.hold) ≠ (chkS s0 (l.out_ - l.left) v).check
    · obtain ⟨i, _, run1⟩ := badRun bad.1 bad.2
      obtain ⟨e, _, _⟩ := same_leave leaveRun (dispatchEq.trans run1)
      cases e
    · have run1 := matchRun bad
      have skip := inflate_LENGTH_skip (c := c)
        (l := { l1 with out_ := l.left, hold := 0, bits := 0 }) st
        (s := { chkS s0 (l.out_ - l.left) v with mode := LENGTH })
        (h := setI (chkH h r zs0 z s0 (l.out_ - l.left) v) zs0
          { chkS s0 (l.out_ - l.left) v with mode := LENGTH })
        (by simp [setI, upd]) (Or.inr (by simp [chkS, flags0]))
      obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun ((dispatchEq.trans run1).trans skip)
      exact Or.inl (show Z_STREAM_END ≠ Z_OK by decide)

end Zlib.Inflate.Proofs
