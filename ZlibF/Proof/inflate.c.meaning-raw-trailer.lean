import ZlibF.Proof.«inflate.c.meaning-type-final»

/-!
# inflate.c: the end of raw data (`TripTypeFinalRaw`, `TripCheckRaw`, `TripRawCheck`)

```
case TYPEDO:
    if (state->last) { BYTEBITS(); state->mode = CHECK; break; }
...
case CHECK:
    if (state->wrap) { ... }
    state->mode = LENGTH;
case LENGTH:
    if (state->wrap && state->flags) { ... }
    state->mode = DONE;
case DONE:
    ret = Z_STREAM_END;
    goto inf_leave;
```

Raw data has no trailer. After the final block `TYPEDO` drops the padding bits and sets `CHECK`;
its trip ends with `break`. The next trip runs `CHECK`, `LENGTH` and `DONE` with nothing to read
(`wrap = 0`) and leaves with `Z_STREAM_END`. So the raw `CHECK` state exists only between these
two trips of one call: it is `RawCheck`, the end stage with the record in `CHECK`, and no
`LoopMatches` state is a raw `CHECK` (`TripCheckRaw` is vacuous).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningTypeFinal
set_option autoImplicit false

namespace MeaningRawTrailer

/-- `BYTEBITS()` at the finished body of raw data: the loop meaning holds at the end stage, for
the heap whose record is in `DONE`. The held bits are the padding of the last body byte, and the
trailer of raw data is empty. -/
theorem final_raw_loop {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat}
    {s : InflateState} (loop : LoopMatches c f h l) (st : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0)
    (raw : f.wrap = .raw) :
    LoopMatches c f (setI h zs { s with mode := DONE }) (bytebits l) := by
  obtain ⟨zs0, s0, callOut, consumed, held, stage, st0, hs0, retOk, config, haveLe, inLen, binv,
    leftLe, pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed,
    stageM, _, outputEq⟩ := loop
  rw [st] at st0
  cases st0
  rw [hs] at hs0
  cases hs0
  obtain ⟨header, out, rfl⟩ := stage_of_final stageM mode last
  obtain ⟨⟨_, _, _, bitsLt⟩, _, _⟩ := stageM
  have bitsLt' : l.bits.toNat < 8 := bitsLt
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  -- the registers after `BYTEBITS()`
  obtain ⟨binv', _, _⟩ := BYTEBITS_inv binv
  have bitsZero : (bytebits l).bits.toNat = 0 := by
    show (l.bits - (l.bits &&& 7)).toNat = 0
    rw [UInt32.toNat_sub_of_le l.bits (l.bits &&& 7) (UInt32.le_iff_toNat_le.mpr (and7_le l)),
      and7_toNat]
    omega
  have readSame : loopRead (bytebits l) = loopRead l := rfl
  have pendSame : loopPending (bytebits l) = loopPending l := rfl
  have heldNil : HeldBits (loopState { s with mode := DONE } (bytebits l)) [] := by
    have small : (loopState { s with mode := DONE } (bytebits l)).hold.toNat <
        2 ^ (loopState { s with mode := DONE } (bytebits l)).bits.toNat := binv'.hold_lt
    have := HeldBits.of_natBits small
    have zero : (loopState { s with mode := DONE } (bytebits l)).bits.toNat = 0 := bitsZero
    rw [zero] at this
    exact this
  -- the held bits are the padding of the last body byte
  have heldLen : held.length = l.bits.toNat := heldBits.1
  have padLen : held.length = (8 - bitsP.length % 8) % 8 := by
    have lengths := congrArg List.length bitsEq
    rw [consumedEq] at lengths
    simp only [List.length_append, bytesToBits_length'] at lengths
    omega
  refine ⟨zs, { s with mode := DONE }, callOut, consumed ++ held, [],
    .done out, st, setI_istates_same _ _ _, retOk,
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
      show DONE ≠ SYNC by decide⟩,
    haveLe, inLen, bitInv_setI binv', leftLe,
    ⟨by rw [pendSame]; exact pendLe.1, fun _ _ e => by cases e⟩, putEq, bytes_setI outBytes,
    MeaningTrailer.writable_setI writable, sepIn, sepWin, sepOutIn,
    by rw [readSame, List.append_nil, bitsEq], heldNil, ?_, rfl, ?_, outputEq⟩
  · refine ⟨header, bodyDict, bitsP, held, wrapHeader, deflate, padLen, ?_⟩
    rw [consumedEq, raw]
    simp [WrapTrailer, bytesToBits]
  · show (bytebits l).bits = 0
    exact UInt32.toNat_inj.mp bitsZero

/-- `case LENGTH:` with `wrap = 0`: `state->mode = DONE` and the fall-through into `DONE`, which
leaves with `Z_STREAM_END`. -/
theorem length_raw_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hw : s.wrap = 0) :
    runX (inflate_LENGTH c) l h =
      .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), setI h zs { s with mode := DONE }) := by
  unfold inflate_LENGTH
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, hw, runX_pure, setMode, wrI_eq,
    inflate_DONE, runX_modify, runX_throw]

end MeaningRawTrailer

open MeaningRawTrailer in
/-- `TYPE`/`TYPEDO` after the last block of raw data: `TYPE` with `Z_BLOCK` or `Z_TREES` leaves
with nothing changed; otherwise `BYTEBITS()` and `CHECK`, ending the trip in the raw `CHECK`
state. -/
theorem trip_type_final_raw : TripTypeFinalRaw := by
  intro c f r raw h l side loop modeAt
  obtain ⟨zs, z, s, E, _⟩ := side.env
  obtain ⟨mode, last⟩ := modeAt zs s E.st E.hs
  have dispatch := inflate_dispatch_block_type E l mode
  have typedo : runX (inflate_dispatch c) l h = runX (inflate_TYPEDO c) l h →
      ∃ result l' h', runX (inflate_dispatch c) l h = .ok ((result, l'), h') ∧
        (TripOutcome c f result h' l' ∨ MeaningDictid.NeedDictExit c f result h' l' ∨
          (result = .ok () ∧ RawCheck c f h' l')) := by
    intro run
    refine ⟨_, _, _, run.trans (inflate_TYPEDO_last E l last), Or.inr (Or.inr ⟨rfl, raw, zs,
      { s with mode := CHECK }, E.st, setI_istates_same _ _ _, rfl, ?_⟩)⟩
    rw [setI_setI]
    exact final_raw_loop (s := s) loop E.st E.hs mode last raw
  by_cases isType : s.mode = TYPE
  · rw [ite_cond_eq_true _ _ (eq_true isType)] at dispatch
    by_cases flush : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
    · exact ⟨_, _, _, dispatch.trans (inflate_TYPE_leave c l h flush),
        Or.inl (Or.inr ⟨rfl, Or.inl loop⟩)⟩
    · have go : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES :=
        ⟨fun e => flush (Or.inl e), fun e => flush (Or.inr e)⟩
      exact typedo (dispatch.trans (inflate_TYPE_go c l h go))
  · rw [ite_cond_eq_false _ _ (eq_false isType)] at dispatch
    exact typedo dispatch

/-- `CHECK` for raw data from `LoopMatches`: vacuous. A `CHECK` state of `LoopMatches` stands for
a trailer position, and a trailer position needs a wrapper. -/
theorem trip_check_raw : TripCheckRaw := by
  intro c f r raw h l _ loop modeAt
  exfalso
  obtain ⟨zs, s, _, _, _, stage, st, hs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, parsed,
    stageM, _, _⟩ := loop
  have mode : (loopState s l).mode = CHECK := modeAt zs s st hs
  obtain ⟨header, out, bytes, rfl⟩ := MeaningCheck.stage_of_check stageM mode
  obtain ⟨_, _, _, _, _, notRaw, _⟩ := parsed
  exact notRaw raw

open MeaningRawTrailer in
/-- The raw `CHECK` state: `CHECK` and `LENGTH` read nothing (`wrap = 0`), `DONE` sets
`Z_STREAM_END` and leaves, with the loop meaning at the end stage in `DONE`. -/
theorem trip_raw_check : TripRawCheck := by
  intro c f r h l side rawState
  obtain ⟨raw, zs, s, st, hs, mode, loop⟩ := rawState
  obtain ⟨zs', z, s', E, _⟩ := side.env
  have e1 : zs' = zs := by
    rw [E.st] at st
    cases st
    rfl
  subst zs
  have e2 : s' = s := Option.some.inj (E.hs.symm.trans hs)
  subst s
  have wrap0 : s'.wrap = 0 := by
    obtain ⟨_, s1, _, _, _, _, st1, hs1, _, config, _⟩ := loop
    rw [E.st] at st1
    cases st1
    simp only [setI_istates_same, Option.some.injEq] at hs1
    subst hs1
    have w : s'.wrap = wrapCode f.wrap := config.1
    rw [raw] at w
    exact w
  have retOk : l.ret = Z_OK := by
    obtain ⟨_, _, _, _, _, _, _, _, ret, _⟩ := loop
    exact ret
  have run := (inflate_dispatch_CHECK E l mode).trans ((inflate_CHECK_nowrap E.st E.hs wrap0).trans
    (length_raw_run (s := { s' with mode := LENGTH }) E.st (setI_istates_same _ _ _) wrap0))
  rw [setI_setI] at run
  refine ⟨_, _, _, run, Or.inr ⟨rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩⟩
  have same : ({ { l with ret := Z_STREAM_END } with ret := Z_OK } : IL) = l := by
    cases l
    simp only at retOk ⊢
    rw [retOk]
  rw [same]
  exact loop

#print axioms trip_type_final_raw
#print axioms trip_check_raw
#print axioms trip_raw_check

end Zlib.Inflate.Proofs
