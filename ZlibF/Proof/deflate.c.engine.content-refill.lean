import ZlibF.Proof.«deflate.c.engine.content-boundary»
import ZlibF.Proof.«deflate.c.engine.slow-refill»

/-! # Actual streaming iterations retain decoded symbol content -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A complete resumed strategy call retains short total input under
Z_NO_FLUSH. The actual fill, loop exit and function return are composed.
The logical symbols are unchanged and all caller input is retained in
the private window. Sliding and pending insertions are included.
-/
theorem slow_short_content_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (shortTotal : d.lookahead.toNat + z.avail_in.toNat < 262)
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base xs ∧
      StreamAccounting z z' z.avail_in.toNat 0 ∧ z'.avail_in = 0 ∧
      result.lookahead.toNat = d.lookahead.toNat + z.avail_in.toNat ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) := by
  have short : d.lookahead.toNat < 262 := by omega
  obtain ⟨used, after, z', result, extended, nextOrigin, fillRun, boundaryA, account,
      start, look, _, _, prefixA, stopped, _⟩ :=
    fill_window_content_boundary boundary short wrap buffers inputValid
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
