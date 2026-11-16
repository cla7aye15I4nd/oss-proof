/-
Skeleton: completion of the default zlib decoder (step 2c of the round trip).
Goals: `Goal.default_inflate_progress`, `Goal.default_inflate_completes`
(`ZlibF/Spec/Functional/InflateCompletion.lean`).

Open lemmas (name — meaning — state — estimate):
* `trace_protocol` — a default history is a zlib protocol history with window 15
  (`inflateInit_` is `inflateInit2_` with 15) — open — 2 h
* `trace_state` — on a heap of a default history the decoder record exists, `Good`, reachable,
  header attached, allocator set, never `SYNC`, never `MEM` (every allocation succeeded) — open — 4 h
* `valid_not_bad` — `ParseMeaning` and a consumed prefix of a valid stream exclude `BAD` — open — 2 h
* `prefix_after` — after a call on a prefix of the rest of a valid stream, the consumed input and
  the written output stay prefixes of `S` and `D`, and `Z_STREAM_END` means exactly `S` and `D`
  (zlib case of `SequenceFormat`, from `meaning_zlib`) — open — 3 h
* `need_dict_zlib` — `Z_NEED_DICT` only from a header with `FDICT`, before any output (zlib case
  of `need_dictionary_call`) — open — 2 h
* `call_codes` — the call runs (`inflate_public`), and its return code is `Z_OK`,
  `Z_STREAM_END`, `Z_NEED_DICT` or `Z_BUF_ERROR` (no refusal: buffers valid, `next_out` set; no
  `Z_DATA_ERROR`: `valid_not_bad` after the call; no `Z_MEM_ERROR`: allocation succeeds) — open — 4 h
* `starved_leave` — control flow of one call (as `blocked_leave`): a return of `Z_OK` or
  `Z_BUF_ERROR` with output room left, under an ordinary flush, left in a `NEEDBITS` or
  `PULLBYTE` with no input, holding fewer bits than the mode needs — open — 12 h
* `stop_short_zlib` — a call that returns `Z_OK` or `Z_BUF_ERROR` has not consumed a whole valid
  zlib stream (zlib case of `StopShort`): from `starved_leave` with output room, or
  `blocked_leave` without, and the stage of `ParseMeaning` after the call (the held bits of a stage
  that has consumed all of `S` cover the mode's need; for `LIT`/`MATCH`/`COPY` more output is due,
  so the trailer is not consumed) — open — 16 h
* `blocked_output_due` — a call that returns `Z_OK` or `Z_BUF_ERROR` with input left has not
  written all of `D` (`blocked_leave` and the stage of `ParseMeaning`: `LIT`, `MATCH` or `COPY`
  holds output that is due) — open — 6 h
* `progress` — assembly of the progress goal — open — 3 h
* `completes` — assembly of the completion goal — open — 3 h
Total about 57 h.
-/
import ZlibF.Spec.Functional.InflateCompletion
import ZlibF.Proof.«inflate.c.meaning-zlib»
import ZlibF.Proof.«inflate.c.completes-blocked»
import ZlibF.Proof.«public-inflate»

namespace Zlib.Inflate.Proofs.DefaultCompletes
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A default history is a zlib protocol history with window 15. -/
theorem trace_protocol {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : DefaultInflateTrace r h log) :
    ∃ pending, InflateProtocolTrace 15 r h log pending ∧ log.dictionary = [] ∧
      log.singleDictionary = true := by
  sorry

/-- The decoder on a heap of a default history. -/
theorem trace_state {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    StreamReachable .inflate h r ∧ ActiveHeader h r ∧
      ∃ i z s, Zlib.Inflate.Spec.Good h r i z s ∧ Zlib.Inflate.Spec.DefAlloc z ∧
        s.mode ≠ SYNC ∧ s.mode ≠ MEM := by
  sorry

/-- A valid stream continues the consumed input: the decoder is not in `BAD`. -/
theorem valid_not_bad {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    {S D : List UInt8} {i : Nat} {z : ZStream} {s : InflateState}
    (meaning : ParseMeaning 15 r h log pending) (valid : Zlib.Decodes [] S D)
    (started : log.input <+: S) (good : Zlib.Inflate.Spec.Good h r i z s) :
    s.mode ≠ BAD := by
  sorry

/-- After a call on a prefix of the rest of a valid stream, the consumed input and the output stay
prefixes of the stream and of its decoding; the end of the stream is exactly both. -/
theorem prefix_after {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush rc : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (noFail : NoAllocationFailure h) (valid : Zlib.Decodes [] S D)
    (within : log.input ++ input <+: S)
    (step : DataStep .inflate h after r flush rc input output used) :
    log.output ++ output <+: D ∧
      (rc = Z_STREAM_END → log.input ++ input.take used = S ∧ log.output ++ output = D) := by
  sorry

/-- `Z_NEED_DICT` only from a header that asks for a dictionary, before any output. -/
theorem need_dict_zlib {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (started : log.input <+: S)
    (step : DataStep .inflate h after r flush Z_NEED_DICT input output used) :
    AsksDictionary S ∧ log.output ++ output = [] := by
  sorry

/-- The call runs and returns one of the four codes of a decoder that neither fails nor is
refused. -/
theorem call_codes {r : ZStreamRef} {h : Heap} {log : DataLog} {S D input : List UInt8}
    {z : ZStream} {flush : Int32}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (noFail : NoAllocationFailure h) (buffers : StreamBuffers h r)
    (valid : Zlib.Decodes [] S D) (started : log.input <+: S)
    (hz : r.get h = some z) (out : z.next_out ≠ .null)
    (bytes : Bytes h z.next_in z.avail_in.toNat input) (within : log.input ++ input <+: S)
    (flushes : OrdinaryFlush flush) :
    ∃ rc after output used z', DataStep .inflate h after r flush rc input output used ∧
      r.get after = some z' ∧ DefaultInflateTrace r after (inflateLogStep log rc input output used) ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_BUF_ERROR → flush = Z_FINISH ∨ (used = 0 ∧ output = [])) ∧
      input.length = z.avail_in.toNat ∧ z'.avail_in.toNat ≤ z.avail_in.toNat ∧
      used = z.avail_in.toNat - z'.avail_in.toNat ∧
      z'.avail_out.toNat ≤ z.avail_out.toNat ∧ output.length = z.avail_out.toNat - z'.avail_out.toNat := by
  sorry

/-- The leave of a call that returns `Z_OK` or `Z_BUF_ERROR` with output room left took no input
and was short of bits: the call consumed all its input. (The full statement names the mode and
its need; this is the part `stop_short_zlib` and `progress` use.) -/
theorem starved_leave {r : ZStreamRef} {h after : Heap} {log : DataLog} {flush rc : Int32}
    {input output : List UInt8} {used : Nat} {z' : ZStream}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (step : DataStep .inflate h after r flush rc input output used)
    (hz' : r.get after = some z') (flushes : OrdinaryFlush flush)
    (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR) (room : z'.avail_out ≠ 0) :
    z'.avail_in = 0 := by
  sorry

/-- A call that returns `Z_OK` or `Z_BUF_ERROR` has not consumed a whole valid zlib stream. -/
theorem stop_short_zlib {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush rc : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (flushes : OrdinaryFlush flush)
    (step : DataStep .inflate h after r flush rc input output used)
    (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR) :
    log.input ++ input.take used ≠ S := by
  sorry

/-- A call that returns `Z_OK` or `Z_BUF_ERROR` with input left has not written all of `D`. -/
theorem blocked_output_due {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush rc : Int32} {used : Nat} {z' : ZStream}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (within : log.input ++ input <+: S) (flushes : OrdinaryFlush flush)
    (step : DataStep .inflate h after r flush rc input output used) (hz' : r.get after = some z')
    (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR) (left : z'.avail_in ≠ 0) :
    (log.output ++ output).length < D.length := by
  sorry

private theorem u32_ne_zero {a : UInt32} : a ≠ 0 ↔ a.toNat ≠ 0 := by
  constructor
  · intro h e
    exact h (UInt32.toNat_inj.mp (by simpa using e))
  · intro h e
    exact h (by simp [e])

/-- A call that returns `Z_OK` or `Z_BUF_ERROR` with room, given input when some of `S` is left,
consumed input or wrote output. -/
theorem moves {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {z z' : ZStream} {flush rc : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (flushes : OrdinaryFlush flush)
    (step : DataStep .inflate h after r flush rc input output used) (hz' : r.get after = some z')
    (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR) (room : z.avail_out ≠ 0)
    (nonempty : input ≠ [] ∨ log.input = S)
    (inLen : input.length = z.avail_in.toNat) (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat)
    (outLe : z'.avail_out.toNat ≤ z.avail_out.toNat)
    (outLen : output.length = z.avail_out.toNat - z'.avail_out.toNat) :
    used ≠ 0 ∨ output ≠ [] := by
  by_cases wrote : output = []
  · have room' : z'.avail_out ≠ 0 := by
      rw [u32_ne_zero] at room ⊢
      rw [wrote] at outLen
      simp at outLen
      omega
    have drained := starved_leave trace fit step hz' flushes codes room'
    rw [drained] at usedEq
    simp at usedEq
    rcases nonempty with ne | eq
    · left
      have : input.length ≠ 0 := by simpa [List.length_eq_zero_iff] using ne
      omega
    · by_cases zero : used = 0
      · exfalso
        have inputNil : input = [] := by
          apply List.eq_nil_of_length_eq_zero
          omega
        apply stop_short_zlib trace fit valid flushes step codes
        rw [inputNil, eq]
        simp
      · exact Or.inl zero
  · exact Or.inr wrote

/-- With the whole rest of `S` and room for the rest of `D`, a call does not return `Z_OK` or
`Z_BUF_ERROR`. -/
theorem stuck {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D output : List UInt8}
    {z z' : ZStream} {flush rc : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (flushes : OrdinaryFlush flush)
    (step : DataStep .inflate h after r flush rc (S.drop log.input.length) output used)
    (hz' : r.get after = some z') (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR)
    (started : log.input <+: S) (within : log.input ++ S.drop log.input.length <+: S)
    (room : D.length ≤ log.output.length + z.avail_out.toNat)
    (inLen : (S.drop log.input.length).length = z.avail_in.toNat)
    (inLe : z'.avail_in.toNat ≤ z.avail_in.toNat)
    (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat)
    (outLe : z'.avail_out.toNat ≤ z.avail_out.toNat)
    (outLen : output.length = z.avail_out.toNat - z'.avail_out.toNat)
    (dropLen : (S.drop log.input.length).length = S.length - log.input.length) : False := by
  by_cases left : z'.avail_in = 0
  · apply stop_short_zlib trace fit valid flushes step codes
    have all : used = (S.drop log.input.length).length := by
      rw [left] at usedEq
      simp at usedEq
      omega
    rw [all, List.take_length]
    exact List.prefix_iff_eq_append.mp started
  · have full : z'.avail_out = 0 := by
      by_cases f : z'.avail_out = 0
      · exact f
      · exact absurd (starved_leave trace fit step hz' flushes codes f) left
    have due := blocked_output_due trace fit valid within flushes step hz' codes left
    rw [full] at outLen
    simp only [UInt32.toNat_zero, Nat.sub_zero] at outLen
    simp only [List.length_append] at due
    omega

theorem progress : Goal.default_inflate_progress := by
  intro r h log S D input z flush trace _ valid started fit noFail buffers hz out room bytes within
    nonempty flushes
  obtain ⟨rc, after, output, used, z', step, hz', _, codes, buf, inLen, _, usedEq, outLe, outLen⟩ :=
    call_codes trace fit noFail buffers valid started hz out bytes within flushes
  obtain ⟨_, ends⟩ := prefix_after trace fit noFail valid within step
  refine ⟨rc, after, output, used, step, ?_⟩
  rcases codes with ok | en | nd | be
  · exact Or.inr (Or.inl ⟨Or.inl ok,
      moves trace fit valid flushes step hz' (Or.inl ok) room nonempty inLen usedEq outLe outLen⟩)
  · exact Or.inl ⟨en, ends en⟩
  · subst nd
    have started' : log.input <+: S := started
    exact Or.inr (Or.inr ⟨rfl, need_dict_zlib trace fit valid started' step⟩)
  · have moved := moves trace fit valid flushes step hz' (Or.inr be) room nonempty inLen usedEq outLe outLen
    rcases buf be with fin | ⟨u0, o0⟩
    · exact Or.inr (Or.inl ⟨Or.inr ⟨be, fin⟩, moved⟩)
    · exfalso
      rcases moved with m | m
      · exact m u0
      · exact m o0

theorem completes : Goal.default_inflate_completes := by
  intro r h log S D z flush trace _ valid started fit noFail buffers hz out bytes room flushes
  have within : log.input ++ S.drop log.input.length <+: S := by
    rw [List.prefix_iff_eq_append.mp started]
    exact List.prefix_refl _
  obtain ⟨rc, after, output, used, z', step, hz', _, codes, _, inLen, inLe, usedEq, outLe, outLen⟩ :=
    call_codes trace fit noFail buffers valid started hz out bytes within flushes
  obtain ⟨_, ends⟩ := prefix_after trace fit noFail valid within step
  have prefixLen : log.input.length ≤ S.length := started.length_le
  have dropLen : (S.drop log.input.length).length = S.length - log.input.length := by simp
  refine ⟨rc, after, output, used, step, ?_⟩
  rcases codes with ok | en | nd | be
  · exfalso
    exact stuck trace fit valid flushes step hz' (Or.inl ok) started within room inLen inLe usedEq outLe outLen dropLen
  · obtain ⟨inEq, outEq⟩ := ends en
    refine Or.inl ⟨en, ?_, outEq⟩
    have l := congrArg List.length inEq
    simp only [List.length_append, List.length_take] at l
    omega
  · subst nd
    exact Or.inr ⟨rfl, need_dict_zlib trace fit valid started step⟩
  · exfalso
    exact stuck trace fit valid flushes step hz' (Or.inr be) started within room inLen inLe usedEq outLe outLen dropLen

end Zlib.Inflate.Proofs.DefaultCompletes
