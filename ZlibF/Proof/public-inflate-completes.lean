/-
Skeleton: completion of the default zlib decoder (step 2c of the round trip).
Goals: `Goal.default_inflate_progress`, `Goal.default_inflate_completes`
(`ZlibF/Spec/Functional/InflateCompletion.lean`).

Lemmas (name — meaning — state — estimate):
* `layer_of_zlib` — a valid zlib stream is valid for the configuration `inflateInit` makes — checked
* `trace_direct` — a default history is a decoder history of `deflate_inflate_roundtrip`
  (`DirectRoundtrip.InflateTrace`): `inflateInit_` is `inflateInit2_` with 15 — checked
* `trace_protocol` — a default history is a zlib protocol history with window 15, without a
  dictionary — checked
* `trace_not_mem` — no decoder of a default history is in `MEM` (every allocation succeeded) — checked
* `trace_state` — the decoder on a heap of a default history: reachable, invariant, header
  attached, not `SYNC`, not `MEM` — checked
* `prefix_after` — after a call on a prefix of the rest of a valid stream the output is a prefix
  of `D`, the result is not `Z_DATA_ERROR`, and `Z_STREAM_END` means exactly `S` and `D` — checked
* `need_dict_zlib` — `Z_NEED_DICT` only from a header with `FDICT`, before any output — checked
* `call_codes` — the call runs; its code is `Z_OK`, `Z_STREAM_END`, `Z_NEED_DICT` or
  `Z_BUF_ERROR`, with the progress clauses of `Goal.inflate` — checked
* `blocked_output_due` — a call that returns `Z_OK` or `Z_BUF_ERROR` with input left filled the
  output and has not written all of `D` (`blocked_leave` and the stage) — checked
* `stop_short_zlib` — a call that returns `Z_OK` or `Z_BUF_ERROR` has not consumed a whole valid
  zlib stream (zlib case of `StopShort`). Plan: with input left, `blocked_output_due`; with no
  input left and no output room, the same stage argument; with no input left and output room, a
  new control-flow lemma `starved_leave` (as `blocked_leave`: the leave was a `NEEDBITS` or
  `PULLBYTE` with no input, short of the bits the mode needs) and a heap-free lemma (a stage that
  has consumed all of `S` holds the bits every mode needs) — open — 24 h
* `moves`, `stuck` — the two case splits of the assemblies — checked
* `progress`, `completes` — the two goals — checked (from the lemmas above)
* `witness` — a concrete heap, history and stream on which the premises of both goals hold
  (non-vacuity) — open — 8 h
Total open: about 32 h.
-/
import ZlibF.Spec.Functional.InflateCompletion
import ZlibF.Proof.«inflate.c.meaning-zlib»
import ZlibF.Proof.«inflate.c.completes-stops»
import ZlibF.Proof.«inflate.c.completes-percall»
import ZlibF.Proof.«public-inflate»
import ZlibF.Proof.«public-inflate-init2»
import ZlibF.Proof.«public-deflate-inflate-roundtrip»

namespace Zlib.Inflate.Proofs.DefaultCompletes
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

theorem params15 : Api.inflWbits (15 : Int32).toInt = some (.zlib, 15) := by decide

/-- A valid zlib stream is valid for the configuration `inflateInit` makes. -/
theorem layer_of_zlib {S D : List UInt8} (valid : Zlib.Decodes [] S D) :
    Api.Layer.Decodes .zlib 15 [] S D ∧ Api.FullWindow .zlib 15 S := by
  refine ⟨⟨valid, ?_⟩, Or.inl rfl⟩
  obtain ⟨cmf, flg, pre, s, rfl, ⟨_, ci, _⟩, _⟩ := valid
  exact Or.inr ⟨cmf, rfl, by omega⟩

/-- A default history is a decoder history of `deflate_inflate_roundtrip`. -/
theorem trace_direct {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : DefaultInflateTrace r h log) :
    ZlibF.Spec.Public.Proofs.DirectRoundtrip.InflateTrace r h log := by
  induction trace with
  | init domain actual => exact .init domain actual
  | caller _ edit platform ih => exact .caller ih edit platform
  | step _ platform _ actual ih => exact .step ih platform actual

/-- A default history is a zlib protocol history with window 15, without a dictionary. -/
theorem trace_protocol {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : DefaultInflateTrace r h log) :
    ∃ pending, InflateProtocolTrace 15 r h log pending ∧ log.dictionary = [] ∧
      log.singleDictionary = true := by
  obtain ⟨pending, history⟩ := (trace_direct trace).protocol
  exact ⟨pending, history, (trace_direct trace).dictionary_empty⟩

/-- The decoder invariant on a heap of a default history. -/
theorem trace_inv {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : DefaultInflateTrace r h log) :
    StreamReachable .inflate h r ∧ ∃ i z s, InflateInv h r i z s ∧ s.mode ≠ SYNC ∧ s.head = none := by
  obtain ⟨pending, history, _, _⟩ := trace_protocol trace
  obtain ⟨meaning, _⟩ := meaning_zlib params15 history
  obtain ⟨_, _, i, z, s, _, inv, config, _⟩ := meaning
  exact ⟨InflateProtocolTrace.reachable history, i, z, s, inv, config.2.2.2.2.2, config.2.2.1⟩

/-- No decoder of a default history is in `MEM`: every allocation of the history succeeded. -/
theorem trace_not_mem {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : DefaultInflateTrace r h log) :
    ∀ i z s, Zlib.Inflate.Spec.Good h r i z s → s.mode ≠ MEM := by
  induction trace with
  | @init h after version domain actual =>
    intro i z' s' good'
    obtain ⟨fresh, uniq, globals, value, z0, get, null, _⟩ := domain
    obtain ⟨rc, after', run', _, outcome⟩ :=
      (ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public 15).2.2
        h r z0 version fresh uniq globals get null value
    have run : C.run (Zlib.Inflate.inflateInit2_ (some r) 15 version 112) h = .ok (Z_OK, after) := actual
    have same := Except.ok.inj (run.symm.trans run')
    cases same
    cases failed : h.allocOk h.nalloc
    · rw [failed] at outcome
      simp only [↓reduceIte] at outcome
      exact absurd outcome.1 (by decide)
    · rw [failed] at outcome
      simp only [Bool.true_eq_false, ↓reduceIte] at outcome
      rw [params15] at outcome
      obtain ⟨_, z, s, good, _, _, mode, _⟩ := outcome
      obtain ⟨-, -, es⟩ := good_same good good'
      subst es
      rw [mode]
      decide
  | @caller h after log trace edit _ ih =>
    intro i z' s' good'
    obtain ⟨_, i0, z0, s0, inv, _⟩ := trace_inv trace
    obtain ⟨z1, inv1⟩ := rebuffer_invariant inv edit
    obtain ⟨-, -, es⟩ := good_same inv1.good good'
    subst es
    exact ih i0 z0 s' inv.good
  | @step h after log flush rc input output used trace fit noFail dstep ih =>
    intro i z' s' good'
    obtain ⟨reach, i0, z0, s0, inv, _⟩ := trace_inv trace
    have observed := dstep
    obtain ⟨_, _, _, _, buffers, active, _, _, _, run⟩ := observed
    obtain ⟨rc2, after2, z2, s2, _, _, run2, good2, _⟩ :=
      inflate_public h r i0 z0 s0 flush reach inv.good fit inv.alloc buffers active
    have same : (rc, after) = (rc2, after2) := Except.ok.inj (run.symm.trans run2)
    cases same
    obtain ⟨-, -, es⟩ := good_same good2 good'
    subst es
    intro memory
    obtain ⟨_, memCause, _⟩ := call_keeps_control h r i0 z0 s0 flush rc after z2 s' reach inv.good run good2
    rcases memCause memory with e | e
    · subst e
      obtain ⟨j, _, _, bad⟩ := mem_error_allocates h r i0 z0 s0 flush after z2 s' inv.good
        (ih i0 z0 s0 inv.good) run good2 memory
      rw [noFail j] at bad
      cases bad
    · exact ih i0 z0 s0 inv.good e

/-- The decoder on a heap of a default history. -/
theorem trace_state {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : DefaultInflateTrace r h log) :
    StreamReachable .inflate h r ∧ ActiveHeader h r ∧
      ∃ i z s, InflateInv h r i z s ∧ s.mode ≠ SYNC ∧ s.mode ≠ MEM := by
  obtain ⟨reach, i, z, s, inv, notSync, head⟩ := trace_inv trace
  refine ⟨reach, ⟨z, inv.good.live.hz, fun i' s' zs hs => ?_, fun i' s' zs _ => ?_⟩,
    i, z, s, inv, notSync, trace_not_mem trace i z s inv.good⟩
  · rw [inv.good.live.zst] at zs
    cases zs
    rw [inv.good.live.hs] at hs
    cases hs
    refine ⟨Or.inl head, fun _ _ j g hj _ => ?_⟩
    rw [head] at hj
    cases hj
  · rw [inv.good.live.zst] at zs
    cases zs

/-- After a call on a prefix of the rest of a valid stream: the output is a prefix of `D`, the
result is not `Z_DATA_ERROR`, and `Z_STREAM_END` means exactly `S` and `D`. -/
theorem prefix_after {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush rc : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (within : log.input ++ input <+: S)
    (step : DataStep .inflate h after r flush rc input output used) :
    log.output ++ output <+: D ∧ rc ≠ Z_DATA_ERROR ∧
      (rc = Z_STREAM_END → log.input ++ input.take used = S ∧ log.output ++ output = D) := by
  obtain ⟨pending, history, dictEmpty, single⟩ := trace_protocol trace
  have history' := InflateProtocolTrace.step history fit step
  obtain ⟨meaning, _⟩ := meaning_zlib params15 history'
  obtain ⟨lay, full⟩ := layer_of_zlib valid
  have started : log.input ++ input.take used <+: S :=
    ((List.prefix_append_right_inj log.input).mpr (List.take_prefix used input)).trans within
  have lay' : Api.Layer.Decodes .zlib 15 log.dictionary S D := by rw [dictEmpty]; exact lay
  exact meaning_prefix params15 meaning lay' single full started

/-- `Z_NEED_DICT` only from a header that asks for a dictionary, before any output. -/
theorem need_dict_zlib {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (within : log.input ++ input <+: S)
    (step : DataStep .inflate h after r flush Z_NEED_DICT input output used) :
    AsksDictionary S ∧ log.output ++ output = [] := by
  obtain ⟨pending, history, _, single⟩ := trace_protocol trace
  obtain ⟨reach, _, i0, z0, s0, inv0, _⟩ := trace_state trace
  have observed := step
  obtain ⟨_, _, _, _, buffers, active, _, _, _, run⟩ := observed
  obtain ⟨rc', after', z', s', _, _, run', good', -, -, -, -, -, -, -, -, -, dictMode, -⟩ :=
    inflate_public h r i0 z0 s0 flush reach inv0.good fit inv0.alloc buffers active
  have same : (Z_NEED_DICT, after) = (rc', after') := Except.ok.inj (run.symm.trans run')
  cases same
  have mode : s'.mode = DICT := dictMode rfl
  have history' := InflateProtocolTrace.step history fit step
  obtain ⟨meaning, _⟩ := meaning_zlib params15 history'
  obtain ⟨wrap', configured, i1, z1, s1, params', inv, _, _, _, _, _, stageClause⟩ := meaning
  rw [params15] at params'
  obtain ⟨rfl, rfl⟩ : Api.Wrap.zlib = wrap' ∧ 15 = configured := by
    cases params'
    exact ⟨rfl, rfl⟩
  obtain ⟨-, -, es⟩ := good_same inv.good good'
  subst es
  obtain ⟨consumed, held, stage, inputBits, _, parsed, _, _, outputEq, request⟩ :=
    stageClause single (by rw [mode]; decide) (by rw [mode]; decide) (by rw [mode]; decide)
  obtain ⟨header, rfl, _⟩ := request (by decide)
  obtain ⟨consumedEq, _, cmf, flg, dictid, headerEq, _, _, _, fdict⟩ := parsed
  subst consumedEq headerEq
  have outputNil : log.output ++ output = [] := outputEq
  have pre : [cmf, flg] <+: log.input ++ input.take used := by
    apply bytesToBits_prefix_iff.mp
    rw [inputBits]
    exact ⟨bytesToBits dictid ++ held, by rw [bytesToBits_append', List.append_assoc]⟩
  obtain ⟨tail, tailEq⟩ := pre
  have started : log.input ++ input.take used <+: S :=
    ((List.prefix_append_right_inj log.input).mpr (List.take_prefix used input)).trans within
  obtain ⟨t, ht⟩ := started
  refine ⟨⟨cmf, flg, tail ++ t, ?_, fdict⟩, outputNil⟩
  rw [← ht, ← tailEq]
  rfl

/-- The call runs and returns one of the four codes of a decoder that neither fails nor is
refused, with the progress clauses of `Goal.inflate`. -/
theorem call_codes {r : ZStreamRef} {h : Heap} {log : DataLog} {S D input : List UInt8}
    {z : ZStream} {flush : Int32}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (noFail : NoAllocationFailure h) (buffers : StreamBuffers h r)
    (valid : Zlib.Decodes [] S D)
    (hz : r.get h = some z) (out : z.next_out ≠ .null)
    (bytes : Bytes h z.next_in z.avail_in.toNat input) (within : log.input ++ input <+: S)
    (flushes : OrdinaryFlush flush) :
    ∃ rc after output used z', DataStep .inflate h after r flush rc input output used ∧
      r.get after = some z' ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_BUF_ERROR → flush = Z_FINISH ∨ (used = 0 ∧ output = [])) ∧
      ((rc = Z_OK ∨ rc = Z_BUF_ERROR) → input ≠ [] → z.avail_out ≠ 0 → used ≠ 0 ∨ output ≠ []) ∧
      input.length = z.avail_in.toNat ∧ z'.avail_in.toNat ≤ z.avail_in.toNat ∧
      used = z.avail_in.toNat - z'.avail_in.toNat ∧
      z'.avail_out.toNat ≤ z.avail_out.toNat ∧ output.length = z.avail_out.toNat - z'.avail_out.toNat := by
  obtain ⟨reach, active, i0, z0, s0, inv0, notSync, notMem⟩ := trace_state trace
  have ez : z0 = z := Option.some.inj (inv0.good.live.hz.symm.trans hz)
  subst ez
  obtain ⟨rc, after, z', s', u, o, run, good', acc, written, codes, okProg, sErr, _, bufCl, progCl,
    _, _, _, memCl, _⟩ :=
    inflate_public h r i0 z0 s0 flush reach inv0.good fit inv0.alloc buffers active
  obtain ⟨aU, aO, aIn, aOut, -⟩ := acc
  have inLen : input.length = z0.avail_in.toNat := bytes_length bytes
  have dstep : DataStep .inflate h after r flush rc input o u :=
    ⟨z0, z', hz, good'.live.hz, buffers, active, bytes, by omega,
      by rw [show z0.avail_out.toNat - z'.avail_out.toNat = o.length by omega]; exact written, run⟩
  obtain ⟨_, notData, _⟩ := prefix_after trace fit valid within dstep
  refine ⟨rc, after, o, u, z', dstep, good'.live.hz, ?_, ?_, ?_, inLen, by omega, by omega, by omega,
    by omega⟩
  · rcases codes with c | c | c | c | c | c | c
    · exact Or.inl c
    · exact Or.inr (Or.inl c)
    · exact Or.inr (Or.inr (Or.inl c))
    · exfalso
      rcases sErr.1 c with x | ⟨_, x⟩ | x
      · exact out x
      · have : z0.avail_in.toNat = 0 := by
          rcases bytes with ⟨_, n0, _⟩ | ⟨ref, off, a, eq, _⟩
          · exact n0
          · rw [x] at eq; cases eq
        exact x.2 (UInt32.toNat_inj.mp (by simpa using this))
      · exact notSync x
    · exact absurd c notData
    · exfalso
      subst c
      obtain ⟨j, _, _, bad⟩ := mem_error_allocates h r i0 z0 s0 flush after z' s' inv0.good notMem run
        good' (memCl rfl).1
      rw [noFail j] at bad
      cases bad
    · exact Or.inr (Or.inr (Or.inr c))
  · intro c
    rcases bufCl c with e | e
    · exact Or.inr e
    · exact Or.inl e
  · intro c ne room
    rcases c with c | c
    · exact (okProg c).1
    · have ain : z0.avail_in ≠ 0 := by
        intro e
        apply ne
        apply List.eq_nil_of_length_eq_zero
        rw [inLen, e]
        rfl
      have nb : flush ≠ Z_BLOCK := by
        rcases flushes with f | f | f | f | f <;> rw [f] <;> decide
      have nt : flush ≠ Z_TREES := by
        rcases flushes with f | f | f | f | f <;> rw [f] <;> decide
      exact progCl ain room nb nt c

/-- A call that returns `Z_OK` or `Z_BUF_ERROR` with input left filled the output and has not
written all of `D`. -/
theorem blocked_output_due {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush rc : Int32} {used : Nat} {z' : ZStream}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (within : log.input ++ input <+: S) (flushes : OrdinaryFlush flush)
    (step : DataStep .inflate h after r flush rc input output used) (hz' : r.get after = some z')
    (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR) (left : z'.avail_in ≠ 0) :
    z'.avail_out = 0 ∧ (log.output ++ output).length < D.length := by
  obtain ⟨pending, history, dictEmpty, single⟩ := trace_protocol trace
  obtain ⟨reach, _, i0, z0, s0, inv0, _⟩ := trace_state trace
  have observed := step
  obtain ⟨zb, _, getb, _, buffers, active, _, _, _, run⟩ := observed
  have history' := InflateProtocolTrace.step history fit step
  obtain ⟨meaning, _⟩ := meaning_zlib params15 history'
  obtain ⟨wrap', configured, i, z, s, params', inv, config, _, _, _, _, stageClause⟩ := meaning
  rw [params15] at params'
  obtain ⟨rfl, rfl⟩ : Api.Wrap.zlib = wrap' ∧ 15 = configured := by
    cases params'
    exact ⟨rfl, rfl⟩
  have sameZ : z = z' := Option.some.inj (inv.good.live.hz.symm.trans hz')
  subst sameZ
  have notBlock : flush ≠ Z_BLOCK := by rcases flushes with f | f | f | f | f <;> rw [f] <;> decide
  have notTrees : flush ≠ Z_TREES := by rcases flushes with f | f | f | f | f <;> rw [f] <;> decide
  obtain ⟨full', s', get', holding⟩ :=
    blocked_leave leave_ret_codes gzip_field_leaves h r i0 z0 s0 flush rc after z inv0 fit buffers
      active run hz' notBlock notTrees codes left
  have sameIndex : i = i0 := by
    have zb0 : zb = z0 := Option.some.inj (getb.symm.trans inv0.good.live.hz)
    subst zb0
    obtain ⟨rc2, after2, z2, s2, used2, out2, run2, good2, accounting, -⟩ :=
      inflate_public h r i0 zb s0 flush reach inv0.good fit inv0.alloc buffers active
    have same : (rc, after) = (rc2, after2) := Except.ok.inj (run.symm.trans run2)
    cases same
    have zSame : z2 = z := Option.some.inj (good2.live.hz.symm.trans hz')
    subst zSame
    have st1 := inv.good.live.zst
    have st2 := inv0.good.live.zst
    rw [accounting.2.2.2.2.2.2.1, st2] at st1
    cases st1
    rfl
  subst sameIndex
  have sameS : s' = s := Option.some.inj (get'.symm.trans inv.good.live.hs)
  subst sameS
  have notBad : s'.mode ≠ BAD := by
    rcases holding with e | e | ⟨e, _⟩ <;> rw [e] <;> decide
  have notMem : s'.mode ≠ MEM := by
    rcases holding with e | e | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain ⟨consumed, held, stage, inputBits, _, parsed, stageMatches, _, outputEq, _⟩ :=
    stageClause single notBad notMem config.2.2.2.2.2
  have copies : ∀ header out final L D remaining dist,
      stage = .body header ⟨out, final, .codes L D (.copy remaining dist)⟩ → 0 < remaining := by
    intro header out final L D remaining dist e
    subst e
    obtain ⟨_, _, _, _, dparsed⟩ := parsed
    exact copy_remaining_pos dparsed
  obtain ⟨header, pos, rfl, due⟩ := due_of_mode stageMatches copies holding
  obtain ⟨lay, _⟩ := layer_of_zlib valid
  have lay' : Api.Layer.Decodes .zlib 15 log.dictionary S D := by rw [dictEmpty]; exact lay
  have onStream : log.input ++ input.take used <+: S :=
    ((List.prefix_append_right_inj log.input).mpr (List.take_prefix used input)).trans within
  have shorter := wrapParsed_due parsed due inputBits lay' onStream
  refine ⟨full', ?_⟩
  have lengths := congrArg List.length outputEq
  simp only [List.length_append, WrapStage.output] at lengths ⊢
  omega

/-- A call that returns `Z_OK` or `Z_BUF_ERROR` has not consumed a whole valid zlib stream. -/
theorem stop_short_zlib {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush rc : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (flushes : OrdinaryFlush flush)
    (step : DataStep .inflate h after r flush rc input output used)
    (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR) :
    log.input ++ input.take used ≠ S := by
  sorry

/-- A call that returns `Z_OK` or `Z_BUF_ERROR` with room, given input when some of `S` is left,
consumed input or wrote output. -/
theorem moves {r : ZStreamRef} {h after : Heap} {log : DataLog} {S D input output : List UInt8}
    {flush rc : Int32} {used : Nat}
    (trace : DefaultInflateTrace r h log) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (valid : Zlib.Decodes [] S D) (flushes : OrdinaryFlush flush)
    (step : DataStep .inflate h after r flush rc input output used)
    (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR) (nonempty : input ≠ [] ∨ log.input = S)
    (given : input ≠ [] → used ≠ 0 ∨ output ≠ []) (usedLe : used ≤ input.length) :
    used ≠ 0 ∨ output ≠ [] := by
  rcases nonempty with ne | eq
  · exact given ne
  · by_cases ne : input = []
    · exfalso
      apply stop_short_zlib trace fit valid flushes step codes
      rw [ne, eq]
      simp
    · exact given ne

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
    (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat)
    (outLen : output.length = z.avail_out.toNat - z'.avail_out.toNat) : False := by
  by_cases left : z'.avail_in = 0
  · apply stop_short_zlib trace fit valid flushes step codes
    have all : used = (S.drop log.input.length).length := by
      rw [left] at usedEq
      simp at usedEq
      omega
    rw [all, List.take_length]
    exact List.prefix_iff_eq_append.mp started
  · obtain ⟨full, due⟩ := blocked_output_due trace fit valid within flushes step hz' codes left
    rw [full] at outLen
    simp only [UInt32.toNat_zero, Nat.sub_zero] at outLen
    simp only [List.length_append] at due
    omega

theorem progress : Goal.default_inflate_progress := by
  intro r h log S D input z flush trace _ valid started fit noFail buffers hz out room bytes within
    nonempty flushes
  obtain ⟨rc, after, output, used, z', step, hz', codes, buf, given, inLen, inLe, usedEq, _, _⟩ :=
    call_codes trace fit noFail buffers valid hz out bytes within flushes
  obtain ⟨outPrefix, _, ends⟩ := prefix_after trace fit valid within step
  have inPrefix : log.input ++ input.take used <+: S :=
    ((List.prefix_append_right_inj log.input).mpr (List.take_prefix used input)).trans within
  have usedLe : used ≤ input.length := by omega
  refine ⟨rc, after, output, used, step, ?_⟩
  rcases codes with ok | en | nd | be
  · exact Or.inr (Or.inl ⟨Or.inl ok,
      moves trace fit valid flushes step (Or.inl ok) nonempty (fun ne => given (Or.inl ok) ne room) usedLe,
      inPrefix, outPrefix⟩)
  · exact Or.inl ⟨en, ends en⟩
  · subst nd
    exact Or.inr (Or.inr ⟨rfl, need_dict_zlib trace fit within step⟩)
  · have moved := moves trace fit valid flushes step (Or.inr be) nonempty
      (fun ne => given (Or.inr be) ne room) usedLe
    rcases buf be with fin | ⟨u0, o0⟩
    · exact Or.inr (Or.inl ⟨Or.inr ⟨be, fin⟩, moved, inPrefix, outPrefix⟩)
    · exfalso
      rcases moved with m | m
      · exact m u0
      · exact m o0

theorem completes : Goal.default_inflate_completes := by
  intro r h log S D z flush trace _ valid started fit noFail buffers hz out bytes room flushes
  have within : log.input ++ S.drop log.input.length <+: S := by
    rw [List.prefix_iff_eq_append.mp started]
    exact List.prefix_refl _
  obtain ⟨rc, after, output, used, z', step, hz', codes, _, _, inLen, inLe, usedEq, _, outLen⟩ :=
    call_codes trace fit noFail buffers valid hz out bytes within flushes
  obtain ⟨_, _, ends⟩ := prefix_after trace fit valid within step
  have dropLen : (S.drop log.input.length).length = S.length - log.input.length := by simp
  refine ⟨rc, after, output, used, step, ?_⟩
  rcases codes with ok | en | nd | be
  · exact (stuck trace fit valid flushes step hz' (Or.inl ok) started within room inLen usedEq outLen).elim
  · obtain ⟨inEq, outEq⟩ := ends en
    refine Or.inl ⟨en, ?_, outEq⟩
    have l := congrArg List.length inEq
    simp only [List.length_append, List.length_take] at l
    omega
  · subst nd
    exact Or.inr ⟨rfl, need_dict_zlib trace fit within step⟩
  · exact (stuck trace fit valid flushes step hz' (Or.inr be) started within room inLen usedEq outLen).elim

/-- Non-vacuity: a concrete heap, history and stream on which the premises of both goals hold. -/
theorem witness : ∃ (r : ZStreamRef) (h : Heap) (log : DataLog) (S D : List UInt8) (z : ZStream),
    DefaultInflateTrace r h log ∧ log.finished = false ∧ Zlib.Decodes [] S D ∧ D ≠ [] ∧
    log.input <+: S ∧ ZlibF.PlatformMemory.ByteObjectsFit h ∧ NoAllocationFailure h ∧
    StreamBuffers h r ∧ r.get h = some z ∧ z.next_out ≠ .null ∧ z.avail_out ≠ 0 ∧
    Bytes h z.next_in z.avail_in.toNat (S.drop log.input.length) ∧ S.drop log.input.length ≠ [] ∧
    D.length ≤ log.output.length + z.avail_out.toNat := by
  sorry

end Zlib.Inflate.Proofs.DefaultCompletes
