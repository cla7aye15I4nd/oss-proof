import ZlibF.Proof.«inflate.c.completes-cause»
import ZlibF.Proof.«inflate.c.meaning-head-zlib»
import ZlibF.Proof.«inflate.c.head-default-state»

/-!
# inflate.c: why the header trips of a zlib call leave

The cause rows of `ZlibCauseRows` for the zlib header, from the run of the actual header code:
`HEAD` leaves only in its `NEEDBITS(16)`, short of the two header bytes; after them the header
checks end the trip normally (`headDefaultCheck_default_state`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningHeadZlib
set_option autoImplicit false

/-- `HEAD` of a zlib stream. -/
theorem cause_head_zlib (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (zlib : f.wrap = .zlib) :
    CauseAt c f r (fun s => s.mode = HEAD) := by
  intro h l side loop head l' h' leaveRun
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, _, _, _⟩ := id side
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  have mode : s.mode = HEAD := head zs s st E.hs
  obtain ⟨wrap5, headNone, _, _⟩ := zlib_head_entry loop st E.hs mode zlib
  obtain ⟨rr, l1, used, needRun, usedLe, binv1, _, _, shape, _, _, okEnough, leaveFacts, kinds, nextEq⟩ :=
    NEEDBITS_run_cursor buf.bits 16 (by decide)
  have dispatch := inflate_dispatch_HEAD E l mode
  rcases kinds with rfl | rfl
  · have run1 := dispatch.trans (zlib_head_run_ok E wrap5 headNone needRun)
    have shape' : SymbolRegShape l l1 := by
      rw [shape]
    have packet : DispatchBuffers h r l1 (bs.drop used) :=
      buf.consume j.good j.good rfl (fun _ => rfl) (fun _ => rfl) shape' nextEq usedLe binv1
    obtain ⟨_, _, _, _, run2, _⟩ := headDefaultCheck_default_state E j packet (okEnough rfl)
    obtain ⟨e, _, _⟩ := same_leave leaveRun (run1.trans run2)
    cases e
  · obtain ⟨_, have0, below⟩ := leaveFacts rfl
    have run1 := dispatch.trans (zlib_head_run_leave E wrap5 needRun)
    obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun run1
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨have0, LeaveShort.of_state st E.hs ?_⟩)))
    have len : (natBits l1.bits.toNat l1.hold.toNat).length < 16 := by
      rw [natBits_length]; exact below
    have wrapNZ : s.wrap ≠ 0 := by rw [wrap5]; decide
    unfold ShortAt
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨mode, wrapNZ, len⟩))))))))))

end Zlib.Inflate.Proofs
