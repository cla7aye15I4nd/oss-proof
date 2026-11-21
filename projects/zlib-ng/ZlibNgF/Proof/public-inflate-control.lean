import ZlibNgF.Proof.«inflate.c.alloc»

/-!
# Inflate entry points that only check and query the state (`ZlibNgF`)

`inflateUndermine` (proved goal), and for `inflateMark`, `inflateCodesUsed`, `inflateSyncPoint`, `inflateValidate`,
`inflateGetHeader`, `inflateEnd`, `inflateResetKeep`, `inflateReset`, `inflateReset2`, `inflatePrime` the
per-function lemmas (the invariant cases of the resets and of `inflatePrime` are in `Proof/inflate.c.reset.lean`):
on `Z_NULL`, on a stream with no state, and on a stream with the structural invariant, the call does not fault,
changes only what its goal's frame names, and keeps the invariant (`inflateEnd` ends the stream). The registered goals
of these functions follow once every inflate step is shown to keep the invariant (`Proof/inflate.c.reach.lean`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateControl
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNgF.Proof.InflateInv

theorem inflateUndermine_safety : Goal.inflateUndermine_safety := by
  intro h s v _ _
  exact ⟨_, rfl⟩

/-- A stream that the state check rejects: `Z_NULL`, or a live stream with no state. -/
def NoState (h : Heap) (s : StreamPtr) : Prop := s = none ∨ ∃ z, StreamAt h s z ∧ z.state = none

theorem stateCheck_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) :
    C.run (inflateStateCheck s) h = .ok (true, h) := by
  rcases hn with rfl | ⟨z, hz, hs⟩
  · exact stateCheck_none h
  · exact stateCheck_closed h s z hz hs

/-! ## `inflateMark` -/

theorem inflateMark_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) :
    C.run (inflateMark s) h = .ok (-65536, h) := by
  simp [C.run, inflateMark, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]

theorem inflateMark_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ r, C.run (inflateMark s) h = .ok (r, h) := by
  obtain ⟨b, st, h1, _, h2⟩ := InflateInv.stateOf hv
  have h0 : inflateStateCheck s h = .ok (false, h) := InflateInv.stateCheck hv
  have h1' : ZlibNg.Inflate.stateOf s h = .ok (some b, h) := h1
  have h2' : ldState (some b) h = .ok (st, h) := h2
  constructor
  simp only [C.run, inflateMark, bind_app, h0, h1', h2', Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## `inflateSyncPoint` -/

theorem inflateSyncPoint_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) :
    ∃ r, C.run (inflateSyncPoint s) h = .ok (r, h) := by
  constructor
  simp only [C.run, inflateSyncPoint, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]
  rfl

theorem inflateSyncPoint_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ r, C.run (inflateSyncPoint s) h = .ok (r, h) := by
  obtain ⟨b, st, h1, _, h2⟩ := InflateInv.stateOf hv
  have h0 : inflateStateCheck s h = .ok (false, h) := InflateInv.stateCheck hv
  have h1' : ZlibNg.Inflate.stateOf s h = .ok (some b, h) := h1
  have h2' : ldState (some b) h = .ok (st, h) := h2
  constructor
  simp only [C.run, inflateSyncPoint, bind_app, h0, h1', h2', Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## `inflateCodesUsed` -/

theorem inflateCodesUsed_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) :
    ∃ r, C.run (inflateCodesUsed s) h = .ok (r, h) := by
  rcases hn with rfl | ⟨z, ⟨i, rfl, hi⟩, hs⟩
  · exact ⟨_, rfl⟩
  · constructor
    simp [C.run, inflateCodesUsed, bind_app, ldStream_app hi, hs]
    rfl

theorem inflateCodesUsed_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ r, C.run (inflateCodesUsed s) h = .ok (r, h) := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, _, c⟩ := InflateInv.parts hv
  obtain ⟨o, hn0, ho⟩ := c.next
  have hn : st.next = .val (.ref (.codes b) o) := hn0
  have hcodes : Space.get h (CodeRef.codes b) = some st.codes := by
    show Heap.getCodes h (.codes b) = _
    simp [Heap.getCodes, hst]
  have hsz : st.codes.size = ENOUGH := c.codes_size
  have hdiff : Ptr.diff (Ptr.ref (CodeRef.codes b) o) (Ptr.ref (CodeRef.codes b) 0) h =
      .ok (Int64.ofInt ((o : Int) - 0), h) := by
    have hle : o ≤ st.codes.size := by rw [hsz]; exact ho
    have hE : ENOUGH = 1924 := rfl
    have ho' : (o : Int) < 9223372036854775808 := by rw [hE] at ho; omega
    simp [Ptr.diff, hcodes, hle, ho']
  constructor
  simp [C.run, inflateCodesUsed, bind_app, ldStream_app hz, hb, ldState_app hst, hn, Ival.get, codesP, hdiff]
  rfl

/-! ## `inflateValidate` -/

theorem inflateValidate_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) (check : Int32) :
    C.run (inflateValidate s check) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateValidate, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]

theorem inflateValidate_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) (check : Int32) :
    ∃ h', C.run (inflateValidate s check) h = .ok (Z_OK, h') ∧ Inv h' s ∧
      ∃ b, StateBlock h s b ∧ h' = { h with istates := upd h.istates b (h'.istates b) } := by
  have h0 : inflateStateCheck s h = .ok (false, h) := InflateInv.stateCheck hv
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, _, _⟩ := InflateInv.parts hv
  have hso : ZlibNg.Inflate.stateOf (some i) h = .ok (some b, h) := by
    simp [ZlibNg.Inflate.stateOf, rdZ, bind_app, ldStream_app hz, hb]
  have hsa : ∃ z, StreamAt h (some i) z ∧ z.state = some b := ⟨z, ⟨i, rfl, hz⟩, hb⟩
  by_cases hc : (check != 0 && st.wrap != 0) = true
  · obtain ⟨hr, hi⟩ := InflateInv.wrS hv (fun s => { s with wrap := s.wrap ||| 4 }) hsa hst (fun _ _ c => c)
    refine ⟨_, ?_, hi, b, hsa, by simp⟩
    have hr' := hr
    simp only [C.run] at hr'
    have hc' : ¬check = 0 ∧ ¬st.wrap = 0 := by simpa using hc
    simp [C.run, inflateValidate, bind_app, h0, hso, rdS, ldState_app hst, hc'.1, hc'.2, hr']
  · obtain ⟨hr, hi⟩ := InflateInv.wrS hv (fun s => { s with wrap := s.wrap &&& ~~~4 }) hsa hst (fun _ _ c => c)
    refine ⟨_, ?_, hi, b, hsa, by simp⟩
    have hr' := hr
    simp [C.run] at hr'
    have hc' : ¬(¬check = 0 ∧ ¬st.wrap = 0) := by simpa using hc
    simp [C.run, inflateValidate, bind_app, h0, hso, rdS, ldState_app hst, hc', hr']

/-! ## `inflateGetHeader` -/

theorem inflateGetHeader_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) (hp : HeaderPtr) :
    C.run (inflateGetHeader s hp) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateGetHeader, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]

theorem inflateGetHeader_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) (k : Nat) (g : GzHeader)
    (hg : h.gzheaders k = some g) :
    ∃ r h', C.run (inflateGetHeader s (some k)) h = .ok (r, h') ∧
      Inv h' s ∧
      (h' = h ∨ ∃ b st', StateBlock h s b ∧
        h' = { h with istates := upd h.istates b (some st'),
                      gzheaders := upd h.gzheaders k (some { g with done := 0 }) }) := by
  have h0 : inflateStateCheck s h = .ok (false, h) := InflateInv.stateCheck hv
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, _, _⟩ := InflateInv.parts hv
  have hso : ZlibNg.Inflate.stateOf (some i) h = .ok (some b, h) := by
    simp [ZlibNg.Inflate.stateOf, rdZ, bind_app, ldStream_app hz, hb]
  have hsa : ∃ z, StreamAt h (some i) z ∧ z.state = some b := ⟨z, ⟨i, rfl, hz⟩, hb⟩
  by_cases hc : (st.wrap &&& 2) = 0
  · exact ⟨Z_STREAM_ERROR, h, by simp [C.run, inflateGetHeader, bind_app, h0, hso, rdS, ldState_app hst, hc],
      hv, Or.inl rfl⟩
  · have hbytes : ∃ d, h.bytes b = some d := by
      unfold Heap.istate at hst; split at hst <;> simp_all
    obtain ⟨d, hd⟩ := hbytes
    let h1 : Heap := { h with istates := upd h.istates b (some { st with head := .val (some k) }) }
    have hr' : ZlibNg.Inflate.wrS (some b) (fun s => { s with head := .val (some k) }) h = .ok ((), h1) := by
      simp [ZlibNg.Inflate.wrS, bind_app, ldState_app hst, C.stState, hst, h1]
    have hg1 : h1.gzheaders k = some g := hg
    let h2 : Heap := { h1 with gzheaders := upd h1.gzheaders k (some { g with done := 0 }) }
    refine ⟨Z_OK, h2, ?_, ?_, Or.inr ⟨b, _, hsa, rfl⟩⟩
    · simp [C.run, inflateGetHeader, bind_app, h0, hso, rdS, ldState_app hst, hc, hr', ldHeader, stHeader, hg, h1, h2]
    · obtain ⟨_, hi⟩ := InflateInv.wrS hv (fun s => { s with head := .val (some k) }) hsa hst
        (fun _ _ c => { c with
          head := Or.inr ⟨k, g, rfl, hg⟩ })
      obtain ⟨i', z', b', st', al', e, hz', hb', hst', hal', c'⟩ := InflateInv.parts hi
      refine ⟨i', z', b', st', al', e, hz', hb', hst', hal', ?_⟩
      refine { c' with head := ?_ }
      · rcases c'.head with hh | ⟨k', g', hk', _⟩
        · exact Or.inl hh
        · refine Or.inr ⟨k', ?_, hk', ?_⟩
          · exact if k' = k then { g with done := 0 } else g'
          · by_cases e2 : k' = k
            · subst e2; simp [h2]
            · simp [h2, e2]; assumption

/-! ## `inflateEnd` -/

theorem inflateEnd_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) :
    C.run (inflateEnd s) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateEnd, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]

/-- `inflateEnd` on an invariant stream frees the state block and clears `state`. -/
theorem inflateEnd_inv {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      C.run (inflateEnd s) h = .ok (Z_OK,
        { h with
          bytes := upd h.bytes b none
          savedPtrs := upd h.savedPtrs b none
          streams := upd h.streams i (some { z with state := none }) }) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  obtain ⟨d, hd⟩ := L.hd
  have hal' : h.iallocs b = some al := by simpa [Heap.iallocsOf, hd] using hal
  refine ⟨i, z, b, rfl, L.hz, L.hb, ?_⟩
  have e := InflateAlloc.free_run L.hz L.hb hd L.hst c.alloc_bufs hal' c.al_zfree c.al_buf
  simp [C.run, inflateEnd, bind_app, L.check, e]

/-! ## Resets and `inflatePrime` on a stream with no state -/

theorem inflateResetKeep_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) :
    C.run (inflateResetKeep s) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateResetKeep, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]

theorem inflateReset_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) :
    C.run (inflateReset s) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateReset, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]

theorem inflateReset2_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) (w : Int32) :
    C.run (inflateReset2 s w) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateReset2, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]

theorem inflatePrime_noState {h : Heap} {s : StreamPtr} (hn : NoState h s) (bits value : Int32) :
    C.run (inflatePrime s bits value) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflatePrime, bind_app, show inflateStateCheck s h = .ok (true, h) from stateCheck_noState hn]

end ZlibNgF.Proof.InflateControl
