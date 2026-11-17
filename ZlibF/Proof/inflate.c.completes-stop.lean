import ZlibF.Proof.«inflate.c.completes-cause-zlib»
import ZlibF.Proof.«inflate.c.meaning-stop-short»

/-!
# inflate.c: a call that returns `Z_OK` or `Z_BUF_ERROR` has not read a whole zlib stream

The cause of the leave that ends the call (`loop_cause`, `zlib_cause_rows`) excludes it:
* a leave short of the field its mode waits for (`LoopMatches.starved_not_end`);
* a leave in `LEN_` with fewer than 8 bits held: the rest of the stream still holds an
  end-of-block symbol and the trailer (`lenstart_not_end`);
* a leave for want of output room holds output that is still due, so the output is shorter than
  the decoding.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open HeldWithinBounds MeaningDistance
set_option autoImplicit false

/-- A stage in `LEN_` is a Huffman-code position before a symbol. -/
theorem stage_of_len_start {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (mode : s.mode = LEN_) :
    ∃ header out final L D, stage = .body header ⟨out, final, .codes L D .none⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rw [mode] at lo hi
    exact absurd hi (by decide)
  · have := stageFacts
    simp only [LoopStageMatches] at this
    rw [mode] at this
    exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m | m | m <;> (rw [mode] at m; exact absurd m (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · exact ⟨header, out, final, L, D, rfl⟩
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
  · obtain ⟨m, _⟩ := stageFacts
    rw [mode] at m
    rcases m with m | m <;> exact absurd m (by decide)
  · have m : s.mode = DONE := stageFacts
    rw [mode] at m
    exact absurd m (by decide)

/-- A leave in `LEN_` holding fewer than 8 bits has not read a whole wrapped stream. -/
theorem lenstart_not_end {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL}
    (loop : LoopMatches c f h l)
    (len : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LEN_)
    (small : l.bits.toNat < 8) (wrapped : f.wrap ≠ .raw) {S decoded : List UInt8}
    (valid : Api.Layer.Decodes f.wrap f.configured f.dict S decoded)
    (whole : f.logIn ++ f.inp.take (loopRead l) = S) : False := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have mode : (loopState s l).mode = LEN_ := len zs s st hs
  obtain ⟨header, out, final, L, D, rfl⟩ := stage_of_len_start stageM mode
  obtain ⟨bodyDict, dbits, wh, consumedEq, dparsed⟩ := parsed
  rw [whole, consumedEq] at bitsEq
  obtain ⟨more, tail, aligned, srcEq, blocks, trailer⟩ :=
    body_on_source wh valid (List.prefix_refl S) (rest := held) (by rw [bitsEq])
  have moreEq : more = held := by
    rw [srcEq, List.append_assoc] at bitsEq
    exact (List.append_cancel_left (List.append_cancel_left bitsEq)).symm
  subst moreEq
  have resid := deflateParsed_resid dparsed more tail decoded aligned blocks
  obtain ⟨_, _, r, h', symbols, cont⟩ := resid
  have l1 := symbols_length symbols
  have l2 := cont_length cont
  have nonempty := wrapTrailer_ne_nil wrapped header decoded
  have trailerLen : 8 ≤ tail.length := by
    have e := congrArg List.length trailer
    rw [List.length_drop, bytesToBits_length'] at e
    have pos : 0 < (WrapTrailer f.wrap header decoded).length := by
      cases eq : WrapTrailer f.wrap header decoded with
      | nil => exact absurd eq.symm nonempty
      | cons _ _ => simp
    omega
  have heldLen : more.length = l.bits.toNat := heldBits.1
  omega

end Zlib.Inflate.Proofs
