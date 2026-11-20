import ZlibNgF.Proof.«deflate.c.body.hstr»

/-!
# `deflate`: `deflateHeaders` (`ZlibNgF`)

`headers_ok`: from a header state (`INIT_STATE` .. `HCRC_STATE`) with no pending bytes, `deflateHeaders` returns
`Z_OK` with output pending (`last_flush = -1`), or `-1` in `BUSY_STATE` with no pending bytes and no symbols
(`DHP`). The parts from `NAME_STATE` on are restated as `hdN`, `hdC`, `hdH` (`headers_eq`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.DeflateBits (WrIn put_short_SH)

/-- The `HCRC_STATE` part and the end of `deflateHeaders` (`deflate.c:955-980`). -/
def hdH (st : StatePtr) (strm : StreamPtr) : M Int32 := do
  if (← rdD st (·.status)) == HCRC_STATE then
    let gh ← (← ldDState st).gzhead.get
    if (← ldHeader gh).hcrc != 0 then
      let s ← ldDState st
      if s.pending + 2 > s.pending_buf_size then
        flush_pending strm
        if ← pendingReturn st then return Z_OK
      put_short st (← rdZ strm (·.adler)).toUInt16
      wrZ strm fun z => { z with adler := CRC32_INITIAL_VALUE }
    wrD st fun s => { s with status := BUSY_STATE }
    flush_pending_inline strm
    if ← pendingReturn st then return Z_OK
  return -1

/-- The `COMMENT_STATE` part (`deflate.c:933-954`), then `hdH`. -/
def hdC (st : StatePtr) (strm : StreamPtr) : M Int32 := do
  if (← rdD st (·.status)) == COMMENT_STATE then
    let gh ← (← ldDState st).gzhead.get
    if (← ldHeader gh).comment != .null then
      if ← headersString st strm (·.comment) then return Z_OK
    wrD st fun s => { s with status := HCRC_STATE }
  hdH st strm

/-- The `NAME_STATE` part (`deflate.c:912-932`), then `hdC`. -/
def hdN (st : StatePtr) (strm : StreamPtr) : M Int32 := do
  if (← rdD st (·.status)) == NAME_STATE then
    let gh ← (← ldDState st).gzhead.get
    if (← ldHeader gh).name != .null then
      if ← headersString st strm (·.name) then return Z_OK
      wrD st fun s => { s with gzindex := 0 }
    wrD st fun s => { s with status := COMMENT_STATE }
  hdC st strm

theorem headers_eq (st : StatePtr) (strm : StreamPtr) :
    deflateHeaders st strm = (do
      let s ← ldDState st
      if s.status == INIT_STATE then
        if ← headersInit s st strm then return Z_OK
      if (← rdD st (·.status)) == GZIP_STATE then
        if ← headersGzip st strm then return Z_OK
      if (← rdD st (·.status)) == EXTRA_STATE then
        if ← headersExtra st strm then return Z_OK
      hdN st strm) := by
  rfl

/-- What `deflateHeaders` leaves. -/
def DHP (h : Heap) (i b : Nat) (r : Int32) (H : Heap) : Prop :=
  Run h i b H ∧ (r = Z_OK → LastM1 H b) ∧
    (r ≠ Z_OK → ∀ st, H.dstate b = some st → st.status = BUSY_STATE ∧ st.pending = 0 ∧ st.sym_next = 0)

/-- Done with the header, or in one of the states `A` with no symbols, `pending_out` at `pending_buf`, at most
`pending_buf_size` pending bytes. -/
def HKA (A : Int32 → Prop) (st : DeflateState) : Prop :=
  (st.status = BUSY_STATE ∧ st.pending = 0 ∧ st.sym_next = 0) ∨
    (A st.status ∧ st.sym_next = 0 ∧ st.pending_out = st.pending_buf ∧ st.pending ≤ st.pending_buf_size)

/-- The header facts of an `HCRC_STATE`. -/
theorem hdrOk_hcrc {X : Heap} {b : Nat} {st : DeflateState} {k : Nat} {g : GzHeader}
    (hgz : st.gzhead = .val (some k)) (hg : X.gzheaders k = some g) (hw : st.wrap = 2) (hs : st.status = HCRC_STATE) :
    HdrOk X b st :=
  ⟨fun _ => hw, fun _ => ⟨k, g, hgz, hg, fun e => absurd (hs.symm.trans e) (by decide),
    fun e => absurd (hs.symm.trans e) (by decide), fun e => absurd (hs.symm.trans e) (by decide),
    fun e => absurd (hs.symm.trans e) (by decide), fun e => absurd (hs.symm.trans e) (by decide)⟩⟩

/-- The header facts of a `COMMENT_STATE` with `gzindex = 0`. -/
theorem hdrOk_comment {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {k : Nat}
    {g : GzHeader} (hgz : st.gzhead = .val (some k)) (hg : H0.gzheaders k = some g) (hw : st.wrap = 2)
    (hs : st.status = COMMENT_STATE) (h0 : st.gzindex = 0) (hc : g.comment = .null ∨ ∃ n, CStringLen H0 g.comment n)
    (nb : ∀ n, CStringLen H0 g.comment n → NotInBlock b g.comment) : HdrOk (SH H0 i z b st d) b st := by
  refine ⟨fun _ => hw, fun _ => ⟨k, g, hgz, hg, fun e => absurd (hs.symm.trans e) (by decide),
    fun e => absurd (hs.symm.trans e) (by decide), fun _ hnn => ?_,
    fun e => absurd (hs.symm.trans e) (by decide), fun e => absurd (hs.symm.trans e) (by decide)⟩⟩
  obtain ⟨n, c⟩ := hc.resolve_left hnn
  exact ⟨nb n c, n, cstr_SH c (nb n c), by rw [h0]; exact Nat.zero_le _⟩

/-- The registered header of a stream in a header state. -/
theorem hdr_of {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : HdrState st) : st.wrap = 2 ∧ ∃ k g, st.gzhead = .val (some k) ∧ H.gzheaders k = some g ∧
      h.gzheaders k = some g := by
  obtain ⟨hw, H2⟩ := (R.side st hst).2.2.1
  obtain ⟨k, g, hgz, hg, -⟩ := H2 hs
  refine ⟨hw (Or.inr hs), k, g, hgz, hg, ?_⟩
  obtain ⟨⟨-, fg, -⟩, -⟩ := R.frame; rw [← fg k (by simp)]; exact hg

/-- The end of `deflateHeaders` from `HCRC_STATE`: `BUSY_STATE`, the flush. -/
theorem hEnd_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = HCRC_STATE) (h0 : st.sym_next = 0) (hpo : st.pending_out = st.pending_buf)
    (hple : st.pending ≤ st.pending_buf_size) :
    Sat H (do
        wrD (some b) fun s => { s with status := BUSY_STATE }
        flush_pending_inline (some i)
        if ← pendingReturn (some b) then return Z_OK
        return (-1 : Int32)) (DHP h i b) := by
  obtain ⟨z, d, pbo, e, SS⟩ := segS_of R hst h0 hpo
  rw [← e]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hp := UInt32.le_iff_toNat_le.mp hple
  have R' := seg_run SS.run SS.pb SS.sym SS.pout z.adler st.pending BUSY_STATE st.gzindex rfl (fun _ _ => rfl)
    (by have := SS.pbs; omega) (by decide) (by decide) (by decide) (hdrOk_busy (Or.inl rfl))
  refine flush_ret_k R' (SH_dstate _ _ _ _ _ _) fun rr H' q _ _ => ?_
  cases rr with
  | true =>
    rw [ite_t rfl]
    exact Sat.pure ⟨q.1, fun _ => q.2.1 rfl, fun e => absurd rfl e⟩
  | false =>
    rw [ite_f (by simp)]
    refine Sat.pure ⟨q.1, fun e => absurd e (by decide), fun _ st' hst' => ?_⟩
    obtain ⟨k1, k2⟩ := q.2.2 rfl st' hst'
    rw [k2]; exact ⟨rfl, k1, h0⟩

theorem rdD_dst {H : Heap} {b : Nat} {st : DeflateState} (hst : H.dstate b = some st) {α : Type}
    (f : DeflateState → α) : rdD (some b) f H = .ok (f st, H) := by
  simp [rdD, bind_app, ldDState_app hst]

theorem ldHeader_of {H : Heap} {k : Nat} {g : GzHeader} (hg : H.gzheaders k = some g) :
    ldHeader (some k) H = .ok (g, H) := by
  show (match H.gzheaders k with | some g => _ | none => _) = _
  rw [hg]

theorem ival_of {H : Heap} {b : Nat} {st : DeflateState} (hst : H.dstate b = some st) {k : Nat}
    (hgz : st.gzhead = .val (some k)) {β : Type} {f : HeaderPtr → M β} {Q : β → Heap → Prop}
    (kk : Sat H (f (some k)) Q) : Sat H ((ldDState (some b) >>= fun s => s.gzhead.get) >>= f) Q := by
  refine Sat.bind (Sat.bind (Sat.of_eq (ldDState_app hst) (sat_ival hgz (Sat.pure ?_))))
  exact kk

theorem cstr_unSH {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {p : BPtr}
    {n : Nat} (c : CStringLen (SH H0 i z b st d) p n) (nb : NotInBlock b p) : CStringLen H0 p n :=
  DeflateSide.cstr_get c fun r off e => (DeflateSetDict.space_SH_ne (by intro hr; subst hr; exact nb off e)).symm

/-- `put_short` of the header CRC, then the end. -/
theorem hPut_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = HCRC_STATE) (h0 : st.sym_next = 0) (hpo : st.pending_out = st.pending_buf)
    (hroom : st.pending.toNat + 2 ≤ st.pending_buf_size.toNat) {k : Nat} {g : GzHeader}
    (hgz : st.gzhead = .val (some k)) (hg : H.gzheaders k = some g) (hw : st.wrap = 2) :
    Sat H (do
        put_short (some b) (← rdZ (some i) (·.adler)).toUInt16
        wrZ (some i) fun z => { z with adler := CRC32_INITIAL_VALUE }
        wrD (some b) fun s => { s with status := BUSY_STATE }
        flush_pending_inline (some i)
        if ← pendingReturn (some b) then return Z_OK
        return (-1 : Int32)) (DHP h i b) := by
  obtain ⟨z, d, pbo, e, SS⟩ := segS_of R hst h0 hpo
  have hr := SS.room
  have hpbs := SS.pbs
  rw [← e]
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  refine Sat.bind (Sat.mono (put_short_SH SS.pb _ (by omega)) ?_)
  rintro _ _ ⟨d', rfl, w⟩
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  have hp2 : (st.pending + 2).toNat = st.pending.toNat + 2 := u32_add _ _ (by omega)
  have R' := seg_run (d := d') SS.run SS.pb SS.sym SS.pout CRC32_INITIAL_VALUE (st.pending + 2) st.status st.gzindex
    w.1 (fun j hj => w.2 j (Or.inl (by omega))) (by omega) (by rw [hs]; decide) (by rw [hs]; decide)
    (by rw [hs]; decide) (hdrOk_hcrc hgz (by rw [← e] at hg; exact hg) hw hs)
  exact hEnd_ok R' (SH_dstate _ _ _ _ _ _) hs h0 hpo
    (UInt32.le_iff_toNat_le.mpr (by dsimp only; omega))

/-- `hdH`. -/
theorem hdH_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (K : HKA (· = HCRC_STATE) st) : Sat H (hdH (some b) (some i)) (DHP h i b) := by
  unfold hdH
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  rcases K with ⟨hb, hp0, h0⟩ | ⟨hs, h0, hpo, hple⟩
  · rw [ite_f (by rw [hb]; decide)]
    exact Sat.pure ⟨R, fun e => absurd e (by decide), fun _ st' hst' => by
      obtain rfl := Option.some.inj (hst.symm.trans hst'); exact ⟨hb, hp0, h0⟩⟩
  rw [ite_t (by rw [hs]; decide)]
  obtain ⟨hw, k, g, hgz, hg, hg0⟩ := hdr_of R hst (Or.inr (Or.inr (Or.inr hs)))
  refine ival_of hst hgz ?_
  refine Sat.bind (Sat.of_eq (ldHeader_of hg) ?_)
  by_cases hc : (g.hcrc != 0) = true
  · rw [ite_t hc]
    refine Sat.bind (Sat.of_eq (ldDState_app hst) ?_)
    by_cases hf : st.pending + 2 > st.pending_buf_size
    · rw [if_pos hf]
      refine flush_ret_k R hst fun rr H' q _ _ => ?_
      cases rr with
      | true =>
        rw [ite_t rfl]
        exact Sat.pure ⟨q.1, fun _ => q.2.1 rfl, fun e => absurd rfl e⟩
      | false =>
        rw [ite_f (by simp)]
        obtain ⟨z', st', al', d', -, -, hst', -, -, -, c'⟩ := q.1.live
        obtain ⟨k1, k2⟩ := q.2.2 rfl st' hst'
        have hpbs : st'.pending_buf_size.toNat ≥ 512 := by
          obtain ⟨-, -, -, l1, -, l3, -⟩ := c'.sizes; simp only [dview] at l1 l3; omega
        exact hPut_ok q.1 hst' (by rw [k2]; exact hs) (by rw [k2]; exact h0) (c'.pout k1)
          (by rw [k1]; simp; omega) (by rw [k2]; exact hgz) (run_gz q.1 hg0) (by rw [k2]; exact hw)
    · rw [if_neg hf]
      have hle : st.pending.toNat + 2 ≤ st.pending_buf_size.toNat := by
        have h2 : ¬ st.pending_buf_size.toNat < (st.pending + 2).toNat := fun x => hf (UInt32.lt_iff_toNat_lt.mpr x)
        have := UInt32.le_iff_toNat_le.mp hple
        rw [u32_add _ _ (by have := st.pending_buf_size.toNat_lt; omega)] at h2
        simp at h2; omega
      exact hPut_ok R hst hs h0 hpo hle hgz hg hw
  · rw [ite_f hc]
    exact hEnd_ok R hst hs h0 hpo hple

end ZlibNgF.Proof.DeflateBody
