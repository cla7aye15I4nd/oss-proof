import ZlibF.Proof.«inflate.c.completes-cause»
import ZlibF.Proof.«inflate.c.meaning-head-zlib»
import ZlibF.Proof.«inflate.c.head-default-state»
import ZlibF.Proof.«inflate.c.meaning-dictid»
import ZlibF.Proof.«inflate.c.dictid-dispatch»
import ZlibF.Proof.«inflate.c.dictionary-dispatch»

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

open MeaningDictid in
/-- `DICTID`: it leaves only in its `NEEDBITS(32)`, short of the identifier; after it `DICT`
returns `Z_NEED_DICT`, since no dictionary is installed yet. -/
theorem cause_dictid (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = DICTID) := by
  intro h l side loop dictid l' h' leaveRun
  obtain ⟨zs, z, s, E, _⟩ := side.env
  have loop0 := loop
  obtain ⟨zs0, s0, _, _, _, stage0, st, hs, _, _, _, _, binv0, _, _, _, _, _, _, _, _, _,
    _, _, stageM0, wrapM0, _⟩ := loop
  have e0 : zs0 = zs := by rw [E.st] at st; cases st; rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs.symm.trans E.hs)
  subst e1
  have mode : s0.mode = DICTID := dictid zs0 s0 st hs
  have high : (loopState s0 l).mode ≤ DICTID := by
    show s0.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨bytes0, rfl⟩ := stage_of_header stageM0 high
  obtain ⟨⟨rawHead0, _, _, _, _, wrappedC0, _, _, _⟩, _, _⟩ := wrapM0
  have wrapped : f.wrap ≠ .raw := by
    intro raw
    have headMode : s0.mode = HEAD := rawHead0 raw
    rw [mode] at headMode
    exact absurd headMode (by decide)
  have havedict0 : s0.havedict = 0 := (wrappedC0 wrapped).1
  obtain ⟨rr, l1, _, needRun, _, _, _, _, _, _, _, _, leaveFacts, kinds, _⟩ :=
    NEEDBITS_run_cursor binv0 32 (by decide)
  have dispatch := inflate_dispatch_DICTID E l mode
  rcases kinds with rfl | rfl
  · have cut := inflate_DICTID_parsed_cut E l l1 needRun
    have E2 : Env c (setI (r.put h { z with adler := ZSWAP32 l1.hold }) zs0
        { s0 with check := ZSWAP32 l1.hold, mode := DICT }) r zs0 { z with adler := ZSWAP32 l1.hold }
        { s0 with check := ZSWAP32 l1.hold, mode := DICT } :=
      ⟨E.strm, st, by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same E.hz _,
        setI_istates_same _ _ _⟩
    have wait := inflate_DICT_wait_run E2 { l1 with hold := 0, bits := 0 } havedict0
    obtain ⟨e, _, _⟩ := same_leave leaveRun ((dispatch.trans cut).trans wait)
    cases e
  · obtain ⟨_, have0, below⟩ := leaveFacts rfl
    obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun (dispatch.trans (inflate_DICTID_wait needRun))
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨have0, LeaveShort.of_state st hs ?_⟩)))
    have len : (natBits l1.bits.toNat l1.hold.toNat).length < 32 := by
      rw [natBits_length]; exact below
    unfold ShortAt
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨Or.inr mode, len⟩))))))))))))

end Zlib.Inflate.Proofs
