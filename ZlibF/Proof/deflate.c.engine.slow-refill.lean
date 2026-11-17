import ZlibF.Proof.«deflate.c.engine.fill-pending-complete»

/-! # The slow strategy's actual refill and early return -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real fill producing enough lookahead reaches exactly the existing
complete body on its actual returned heap. -/
theorem slow_body_fill_ready {h after : Heap} {ds : Nat} {d filled : DeflateState}
    (state : h.dstates ds = some d) (stateA : after.dstates ds = some filled)
    (short : d.lookahead.toNat < 262) (ready : 262 ≤ filled.lookahead.toNat)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (flush : Int32) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) flush st h =
      deflate_slow_body (some (.tab ds)) flush st after := by
  have before : d.lookahead < MIN_LOOKAHEAD_u := by
    simpa only [UInt32.lt_iff_toNat_lt, show MIN_LOOKAHEAD_u.toNat = 262 from rfl] using short
  have enough : ¬ filled.lookahead < MIN_LOOKAHEAD_u := by
    simpa only [UInt32.lt_iff_toNat_lt, show MIN_LOOKAHEAD_u.toNat = 262 from rfl] using Nat.not_lt.mpr ready
  have nonzero : filled.lookahead ≠ 0 := by
    intro zero
    simp [zero] at ready
  simp [slow_body_source, bind_app, rdD_eq, state, stateA, before, enough, run, nonzero]

/-- With Z_NO_FLUSH the source returns need_more before search when the
actual fill leaves short lookahead. The returned state is that fill's
state; no insertion or tally occurs after it. -/
theorem slow_body_fill_wait {h after : Heap} {ds : Nat} {d filled : DeflateState}
    (state : h.dstates ds = some d) (stateA : after.dstates ds = some filled)
    (short : d.lookahead.toNat < 262) (shortA : filled.lookahead.toNat < 262)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h =
      .ok ({ st with ret := some need_more }, after) := by
  have before : d.lookahead < MIN_LOOKAHEAD_u := by
    simpa only [UInt32.lt_iff_toNat_lt, show MIN_LOOKAHEAD_u.toNat = 262 from rfl] using short
  have smaller : filled.lookahead < MIN_LOOKAHEAD_u := by
    simpa only [UInt32.lt_iff_toNat_lt, show MIN_LOOKAHEAD_u.toNat = 262 from rfl] using shortA
  simp [slow_body_source, bind_app, rdD_eq, state, before, run, stateA, smaller]

/-- A complete resumed strategy call retains short total input under
Z_NO_FLUSH. The actual fill, loop exit and function return are composed.
The logical symbols are unchanged and all caller input is retained in
the private window. Sliding and pending insertions are included.
-/
theorem slow_short_no_flush_boundary {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (shortTotal : d.lookahead.toNat + z.avail_in.toNat < 262)
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      PendingBoundary after r ds z' result extended nextOrigin xs ∧
      StreamAccounting z z' z.avail_in.toNat 0 ∧ z'.avail_in = 0 ∧
      result.lookahead.toNat = d.lookahead.toNat + z.avail_in.toNat ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) := by
  have short : d.lookahead.toNat < 262 := by omega
  obtain ⟨used, after, z', result, extended, nextOrigin, fillRun, boundaryA, account,
      start, look, _, _, prefixA, stopped⟩ :=
    fill_window_pending_boundary_all boundary short wrap buffers inputValid
  have usedBound := account.1
  have shortA : result.lookahead.toNat < 262 := by omega
  have exhausted : z'.avail_in = 0 := stopped.resolve_left (by omega)
  have accepted : used = z.avail_in.toNat := by
    have count := account.2.2.1
    rw [exhausted] at count
    simpa using count
  have body := slow_body_fill_wait boundary.good.live.hs boundaryA.good.live.hs short shortA fillRun {}
  have loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h =
      .ok ({ ret := some need_more }, after) := by
    unfold cwhile
    change cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH)
      (18446744073709551614 + 2) ({} : LoopS) h = _
    rw [cwhile.go, bind_app,
      show forever {} h = .ok ((true, {}), h) from rfl]
    simp only [ite_true, bind_app, body]
    rw [cwhile.go, bind_app,
      show forever { ret := some need_more } after = .ok ((false, { ret := some need_more }), after) from rfl]
    rfl
  refine ⟨after, z', result, extended, nextOrigin, ?_, boundaryA, ?_, exhausted, ?_, start, prefixA⟩
  · unfold deflate_slow
    rw [bind_app, loop]
    rfl
  · rw [← accepted]
    exact account
  · rw [← accepted]
    exact look

end Zlib.Deflate.Engine.Proofs
