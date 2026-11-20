import ZlibNgF.Proof.«deflate.c.body.hdr»

/-!
# `deflate`: the trailer (`ZlibNgF`)

`trailer_ok`: `bodyD` (`deflate.c:1100-1118`). For `Z_FINISH`, with no pending bytes and no symbols outside the
header, the gzip trailer (CRC-32 and length, 8 bytes) or the zlib trailer (Adler-32, 4 bytes) goes into
`pending_buf`, the output is flushed, and a positive `wrap` is negated (`-1` / `-2`, allowed by the invariant).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNg.DeflateP (flush_pending flush_pending_inline)

/-- The fact on `last_flush` of the end of a call. -/
def LFok (H : Heap) (b : Nat) : Prop := ∀ st, H.dstate b = some st → 0 < st.last_flush → st.sym_next = 0

/-- `wrap = -wrap` keeps `Run` outside the header states. -/
theorem run_wrap {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = BUSY_STATE ∨ st.status = FINISH_STATE) (hw : 0 < st.wrap) :
    Sat H (wrD (some b) fun s => { s with wrap := -s.wrap })
      (fun _ H' => Run h i b H' ∧ ∀ st', H'.dstate b = some st' → st'.last_flush = st.last_flush ∧
        st'.sym_next = st.sym_next) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  rw [← e]
  refine Sat.of_eq (wrD_SH _) ⟨?_, fun st' hst' => by
    rw [SH_dstate] at hst'; obtain rfl := Option.some.inj hst'; exact ⟨rfl, rfl⟩⟩
  have hwr : -st.wrap = -1 ∨ -st.wrap = -2 := by
    rcases c.wrap with x | x | x | x | x <;> simp only [dview] at x <;> rw [x] at hw ⊢ <;> first
      | exact absurd hw (by decide) | (left; decide) | (right; decide)
  have c' : DCore (SH H i z b { st with wrap := -st.wrap } d) (some i) z b (dview { st with wrap := -st.wrap }) al :=
    DCore.of_heap (by simp [hd]) { c with wrap := Or.inr (Or.inr (Or.inr hwr)) }
  refine run_SH R hz hst hal c' rfl rfl rfl rfl rfl rfl ?_
  obtain ⟨S1, S2, -, S4, S5, S6⟩ := R.side st hst
  exact ⟨S1, S2, hdrOk_busy hs, S4, fun d' hd' => by
    rw [SH_bytes] at hd'; obtain rfl := Option.some.inj hd'; exact S5 d hd, S6⟩

/-- The trailer's end: the flush, `wrap = -wrap`, the result. -/
theorem trEnd_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = BUSY_STATE ∨ st.status = FINISH_STATE) (h0 : st.sym_next = 0) :
    Sat H (do
        flush_pending_inline (some i)
        let s ← ldDState (some b)
        if s.wrap > 0 then
          wrD (some b) fun s => { s with wrap := -s.wrap }
        if (← rdD (some b) (·.pending)) == 0 then return Z_STREAM_END
        return Z_OK) (fun _ H' => Run h i b H' ∧ ∀ st', H'.dstate b = some st' → st'.sym_next = 0) := by
  obtain ⟨H2, e2, R2, k⟩ := run_flush R.w
  obtain ⟨z, hz, -⟩ := R.blk
  obtain ⟨z', st2, -, hst2, hse, -⟩ := k z st hz hst
  refine Sat.bind ⟨(), H2, e2, ?_⟩
  refine Sat.bind (Sat.of_eq (ldDState_app hst2) ?_)
  have hs2 : st2.status = BUSY_STATE ∨ st2.status = FINISH_STATE := by rw [hse]; exact hs
  have h02 : st2.sym_next = 0 := by rw [hse]; exact h0
  -- the end, from a heap in `Run` whose state has no symbols
  have fin : ∀ H3, Run h i b H3 → (∀ st', H3.dstate b = some st' → st'.sym_next = 0) →
      Sat H3 (do
        if (← rdD (some b) (·.pending)) == 0 then return Z_STREAM_END
        return Z_OK) (fun _ H' => Run h i b H' ∧ ∀ st', H'.dstate b = some st' → st'.sym_next = 0) := by
    intro H3 R3 K3
    obtain ⟨z3, st3, -, -, -, -, hst3, -, -, -, -⟩ := R3.live
    refine Sat.bind (Sat.of_eq (rdD_dst hst3 _) ?_)
    split
    · exact Sat.pure ⟨R3, K3⟩
    · exact Sat.pure ⟨R3, K3⟩
  by_cases hw : st2.wrap > 0
  · rw [ite_t hw]
    refine Sat.bind (Sat.mono (run_wrap R2 hst2 hs2 hw) ?_)
    rintro _ H3 ⟨R3, k3⟩
    exact fin H3 R3 fun st' h' => (k3 st' h').2.trans h02
  · rw [ite_f hw]
    exact fin H2 R2 fun st' h' => by obtain rfl := Option.some.inj (hst2.symm.trans h'); exact h02

/-- **The trailer** (`bodyD`). -/
theorem trailer_ok {h H : Heap} {i b : Nat} {st : DeflateState} {flush : Int32} (R : Run h i b H)
    (hst : H.dstate b = some st) (hs : st.status = BUSY_STATE ∨ st.status = FINISH_STATE)
    (hlf : st.last_flush = flush) (hsym : 0 < flush → st.sym_next = 0)
    (hp : flush = Z_FINISH → st.pending = 0) :
    Sat H (bodyD (some b) (some i) flush) (fun _ H' => Run h i b H' ∧ LFok H' b) := by
  unfold bodyD
  by_cases hf : (flush != Z_FINISH) = true
  · rw [ite_t hf]
    exact Sat.pure ⟨R, fun st' h' hl => by
      obtain rfl := Option.some.inj (hst.symm.trans h'); rw [hlf] at hl; exact hsym hl⟩
  rw [ite_f hf]
  have hF : flush = Z_FINISH := by simpa using hf
  have h0 : st.sym_next = 0 := hsym (by rw [hF]; decide)
  have hp0 := hp hF
  have post : ∀ H', Run h i b H' ∧ (∀ st', H'.dstate b = some st' → st'.sym_next = 0) →
      Run h i b H' ∧ LFok H' b := fun H' ⟨R', k⟩ => ⟨R', fun st' h' _ => k st' h'⟩
  obtain ⟨z1, st1, al, d1, -, -, hst1, -, -, -, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  have hpo : st.pending_out = st.pending_buf := c.pout hp0
  obtain ⟨z, d, pbo, e, SS⟩ := segS_of R hst h0 hpo
  have hr : pbo + 64 ≤ d.size := by have := SS.room; omega
  have hfin : st.status = FINISH_STATE → st.sym_next = 0 ∧ st.lookahead = 0 := (R.side st hst).2.1
  have e0 : ({ st with pending := 0 } : DeflateState) = st := by rw [← hp0]
  have P0 : PB H i z b st d pbo 0 (SH H i z b st d) := ⟨d, by rw [e0], rfl, fun _ _ => rfl⟩
  have hsr1 : INIT_STATE ≤ st.status := by rcases hs with x | x <;> rw [x] <;> decide
  have hsr2 : st.status ≤ MAX_STATE := by rcases hs with x | x <;> rw [x] <;> decide
  have hlb := SS.lb
  -- the end after `q` trailer bytes
  have tail : ∀ (q : UInt32) (H2 : Heap), q.toNat ≤ 8 → PB H i z b st d pbo q H2 →
      Sat H2 (do
        flush_pending_inline (some i)
        let s ← ldDState (some b)
        if s.wrap > 0 then
          wrD (some b) fun s => { s with wrap := -s.wrap }
        if (← rdD (some b) (·.pending)) == 0 then return Z_STREAM_END
        return Z_OK) (fun _ H' => Run h i b H' ∧ LFok H' b) := by
    intro q H2 hq P
    obtain ⟨d2, rfl, hs2, hl2⟩ := P
    have R' := seg_run' SS.run SS.pb SS.sym SS.pout z.adler q st.status st.gzindex hs2 hl2 (by omega) hsr1 hsr2 hfin
      (hdrOk_busy hs)
    exact Sat.mono (trEnd_ok R' (SH_dstate _ _ _ _ _ _) hs h0) fun _ => post
  rw [← e]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  by_cases w2 : (st.wrap == 2) = true
  · rw [ite_t w2]
    refine pb_rdZ P0 _ ?_
    refine Sat.bind (Sat.mono (pb_u32 SS.pb hr (by decide) P0 _) ?_)
    rintro _ H1 P1
    refine pb_rdZ P1 _ ?_
    refine Sat.bind (Sat.mono (pb_u32 SS.pb hr (by decide) P1 _) ?_)
    rintro _ H2 P2
    exact tail _ H2 (by decide) P2
  · rw [ite_f w2]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    by_cases w1 : (st.wrap == 1) = true
    · rw [ite_t w1]
      refine pb_rdZ P0 _ ?_
      refine Sat.bind (Sat.mono (pb_u32_msb SS.pb hr (by decide) P0 _) ?_)
      rintro _ H1 P1
      exact tail _ H1 (by decide) P1
    · rw [ite_f w1]
      exact tail 0 _ (by decide) P0

end ZlibNgF.Proof.DeflateBody
