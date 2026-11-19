import ZlibNgF.Proof.«inflate.c.invariant»

/-!
# Inflate entry points that only check and query the state (`ZlibNgF`)

`inflateUndermine` (proved goal), and for `inflateMark`, `inflateCodesUsed`, `inflateSyncPoint`, `inflateValidate`,
`inflateGetHeader` the per-function lemmas: on `Z_NULL`, on a stream with no state, and on a stream with the
structural invariant, the call does not fault, changes at most the state record (and for `inflateGetHeader` the
header's `done`), and keeps the invariant. The registered goals of these functions follow once every inflate step
is shown to keep the invariant (induction over `InflateReachable`).
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
      ∃ b, h' = { h with istates := upd h.istates b (h'.istates b) } := by
  have h0 : inflateStateCheck s h = .ok (false, h) := InflateInv.stateCheck hv
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, _, _⟩ := InflateInv.parts hv
  have hso : ZlibNg.Inflate.stateOf (some i) h = .ok (some b, h) := by
    simp [ZlibNg.Inflate.stateOf, rdZ, bind_app, ldStream_app hz, hb]
  have hsa : ∃ z, StreamAt h (some i) z ∧ z.state = some b := ⟨z, ⟨i, rfl, hz⟩, hb⟩
  by_cases hc : (check != 0 && st.wrap != 0) = true
  · obtain ⟨hr, hi⟩ := InflateInv.wrS hv (fun s => { s with wrap := s.wrap ||| 4 }) hsa hst (fun _ _ c => c)
    refine ⟨_, ?_, hi, b, by simp⟩
    have hr' := hr
    simp only [C.run] at hr'
    have hc' : ¬check = 0 ∧ ¬st.wrap = 0 := by simpa using hc
    simp [C.run, inflateValidate, bind_app, h0, hso, rdS, ldState_app hst, hc'.1, hc'.2, hr']
  · obtain ⟨hr, hi⟩ := InflateInv.wrS hv (fun s => { s with wrap := s.wrap &&& ~~~4 }) hsa hst (fun _ _ c => c)
    refine ⟨_, ?_, hi, b, by simp⟩
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
    ∃ r h', C.run (inflateGetHeader s (some k)) h = .ok (r, h') ∧ Inv h' s := by
  have h0 : inflateStateCheck s h = .ok (false, h) := InflateInv.stateCheck hv
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, _, _⟩ := InflateInv.parts hv
  have hso : ZlibNg.Inflate.stateOf (some i) h = .ok (some b, h) := by
    simp [ZlibNg.Inflate.stateOf, rdZ, bind_app, ldStream_app hz, hb]
  have hsa : ∃ z, StreamAt h (some i) z ∧ z.state = some b := ⟨z, ⟨i, rfl, hz⟩, hb⟩
  by_cases hc : (st.wrap &&& 2) = 0
  · exact ⟨Z_STREAM_ERROR, h, by simp [C.run, inflateGetHeader, bind_app, h0, hso, rdS, ldState_app hst, hc], hv⟩
  · obtain ⟨hr, hi⟩ := InflateInv.wrS hv (fun s => { s with head := .val (some k) }) hsa hst
      (fun al z c => ⟨c.zalloc, c.zfree, c.strm, c.alloc_bufs, c.al_state, c.al_zfree, c.al_buf, c.window,
        c.wbufsize, c.mode_lo, c.mode_hi, c.wbits, c.wsize, c.whave, c.wnext, c.bits, c.codes_size, c.lens_size,
        c.work_size, c.lencode, c.distcode, c.next, c.ncode, c.nlen, c.ndist, c.have_, Or.inr ⟨k, g, rfl, hg⟩⟩)
    have hr' := hr
    simp only [C.run] at hr'
    let h1 : Heap := { h with istates := upd h.istates b (some { st with head := .val (some k) }) }
    have hg1 : h1.gzheaders k = some g := hg
    let h2 : Heap := { h1 with gzheaders := upd h1.gzheaders k (some { g with done := 0 }) }
    refine ⟨Z_OK, h2, ?_, ?_⟩
    · simp [C.run, inflateGetHeader, bind_app, h0, hso, rdS, ldState_app hst, hc, hr', ldHeader, stHeader, hg, h1, h2]
    · obtain ⟨i', z', b', st', al', e, hz', hb', hst', hal', c'⟩ := InflateInv.parts hi
      refine ⟨i', z', b', st', al', e, hz', hb', hst', hal', ?_⟩
      refine ⟨c'.zalloc, c'.zfree, c'.strm, c'.alloc_bufs, c'.al_state, c'.al_zfree, c'.al_buf, c'.window,
        c'.wbufsize, c'.mode_lo, c'.mode_hi, c'.wbits, c'.wsize, c'.whave, c'.wnext, c'.bits, c'.codes_size,
        c'.lens_size, c'.work_size, c'.lencode, c'.distcode, c'.next, c'.ncode, c'.nlen, c'.ndist, c'.have_, ?_⟩
      rcases c'.head with hh | ⟨k', g', hk', _⟩
      · exact Or.inl hh
      · refine Or.inr ⟨k', ?_, hk', ?_⟩
        · exact if k' = k then { g with done := 0 } else g'
        · by_cases e2 : k' = k
          · subst e2; simp [h2]
          · simp [h2, e2]; assumption

end ZlibNgF.Proof.InflateControl
