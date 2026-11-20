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
open ZlibNg.DeflateP (flush_pending flush_pending_inline)

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
    (hs : st.status = COMMENT_STATE) (h0 : st.gzindex = 0)
    (hc : g.comment = .null ∨ ∃ n, NotInBlock b g.comment ∧ CStringLen H0 g.comment n) :
    HdrOk (SH H0 i z b st d) b st := by
  refine ⟨fun _ => hw, fun _ => ⟨k, g, hgz, hg, fun e => absurd (hs.symm.trans e) (by decide),
    fun e => absurd (hs.symm.trans e) (by decide), fun _ hnn => ?_,
    fun e => absurd (hs.symm.trans e) (by decide), fun e => absurd (hs.symm.trans e) (by decide)⟩⟩
  obtain ⟨n, nb, c⟩ := hc.resolve_left hnn
  exact ⟨nb, n, cstr_SH c nb, by rw [h0]; exact Nat.zero_le _⟩

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
    (_hs : st.status = HCRC_STATE) (h0 : st.sym_next = 0) (hpo : st.pending_out = st.pending_buf)
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
    (kk : Sat H (f (some k)) Q) : Sat H (ldDState (some b) >>= fun s => s.gzhead.get >>= f) Q := by
  refine Sat.bind (Sat.of_eq (ldDState_app hst) ?_)
  rw [hgz]; exact kk

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
  have hlb2 := SS.lb2
  rw [← e]
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  refine Sat.bind (Sat.mono (put_short_SH SS.pb _ (by omega)) ?_)
  rintro _ _ ⟨d', rfl, w⟩
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  have hp2 : (st.pending + 2).toNat = st.pending.toNat + 2 := u32_add _ _ (by simp; omega)
  have R' := seg_run (d := d') SS.run SS.pb SS.sym SS.pout CRC32_INITIAL_VALUE (st.pending + 2) st.status st.gzindex
    w.1 (fun j hj => w.2 j (Or.inl (by omega))) (by omega) (by rw [hs]; decide) (by rw [hs]; decide)
    (by rw [hs]; decide) (hdrOk_hcrc hgz (by rw [← e] at hg; exact hg) hw hs)
  exact hEnd_ok R' (SH_dstate _ _ _ _ _ _) hs h0 hpo
    (UInt32.le_iff_toNat_le.mpr (by dsimp only; omega))

theorem pbs_of {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st) :
    st.pending_buf_size.toNat = 4 * st.lit_bufsize.toNat ∧ 128 ≤ st.lit_bufsize.toNat ∧
      st.lit_bufsize.toNat ≤ 32768 := by
  obtain ⟨z, st1, al, d, -, -, hst1, -, -, -, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  obtain ⟨-, -, -, k1, k2, k3, -⟩ := c.sizes
  exact ⟨k3, k1, k2⟩

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
    · rw [ite_t hf]
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
    · rw [ite_f hf]
      have hpb := pbs_of R hst
      have hle : st.pending.toNat + 2 ≤ st.pending_buf_size.toNat := by
        have h2 : ¬ st.pending_buf_size.toNat < (st.pending + 2).toNat := fun x => hf (UInt32.lt_iff_toNat_lt.mpr x)
        have := UInt32.le_iff_toNat_le.mp hple
        rw [u32_add _ _ (by have : (2 : UInt32).toNat = 2 := rfl; omega)] at h2
        simp at h2; omega
      exact hPut_ok R hst hs h0 hpo hle hgz hg hw
  · rw [ite_f hc]
    exact hEnd_ok R hst hs h0 hpo hple

/-- `hdC`. -/
theorem hdC_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (K : HKA (fun s => s = COMMENT_STATE ∨ s = HCRC_STATE) st) : Sat H (hdC (some b) (some i)) (DHP h i b) := by
  unfold hdC
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  by_cases hs : st.status = COMMENT_STATE
  · rw [ite_t (by rw [hs]; decide)]
    obtain ⟨-, h0, hpo, hple⟩ : st.status = COMMENT_STATE ∧ st.sym_next = 0 ∧ st.pending_out = st.pending_buf ∧
        st.pending ≤ st.pending_buf_size := by
      rcases K with ⟨hb, -⟩ | ⟨-, x⟩
      · rw [hs] at hb; exact absurd hb (by decide)
      · exact ⟨hs, x⟩
    obtain ⟨hw, k, g, hgz, hg, hg0⟩ := hdr_of R hst (Or.inr (Or.inr (Or.inl hs)))
    refine ival_of hst hgz ?_
    refine Sat.bind (Sat.of_eq (ldHeader_of hg) ?_)
    by_cases hc : (g.comment != .null) = true
    · rw [ite_t hc]
      refine Sat.bind (Sat.mono (string_ok (Or.inr ⟨rfl, rfl⟩) R hst hs h0 hpo hple hgz hg (by simpa using hc)) ?_)
      rintro rr H1 ⟨q1, q2⟩
      cases rr with
      | true =>
        rw [ite_t rfl]
        obtain ⟨R1, l1⟩ := q1 rfl
        exact Sat.pure ⟨R1, fun _ => l1, fun e => absurd rfl e⟩
      | false =>
        rw [ite_f (by simp)]
        obtain ⟨H0, z0, st0, d0, pbo, a, p, s', g', dd, SS, rfl, hsz, hlo, hp, f1, f2, f3, f4, -, f6, hw0⟩ := q2 rfl
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
        have hg' : H0.gzheaders k = some g := run_gz SS.run hg0
        have R' := seg_run (d := dd) SS.run SS.pb SS.sym SS.pout a p HCRC_STATE g' hsz hlo hp (by decide) (by decide)
          (by decide) (hdrOk_hcrc f6 hg' hw0 rfl)
        exact hdH_ok R' (SH_dstate _ _ _ _ _ _) (.inr ⟨rfl, f2, f3, f4⟩)
    · rw [ite_f hc]
      obtain ⟨z, d, pbo, e, SS⟩ := segS_of R hst h0 hpo
      rw [← e]
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      have := pbs_of R hst
      have R' := seg_run (d := d) SS.run SS.pb SS.sym SS.pout z.adler st.pending HCRC_STATE st.gzindex rfl
        (fun _ _ => rfl) (by have := UInt32.le_iff_toNat_le.mp hple; omega) (by decide) (by decide) (by decide)
        (hdrOk_hcrc hgz (by rw [← e] at hg; exact hg) hw rfl)
      exact hdH_ok R' (SH_dstate _ _ _ _ _ _) (.inr ⟨rfl, h0, hpo, hple⟩)
  · rw [ite_f (by simpa using hs)]
    refine hdH_ok R hst ?_
    rcases K with x | ⟨hA, x⟩
    · exact .inl x
    · exact .inr ⟨hA.resolve_left hs, x⟩

/-- `hdN`. -/
theorem hdN_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (K : HKA (fun s => s = NAME_STATE ∨ s = COMMENT_STATE ∨ s = HCRC_STATE) st) :
    Sat H (hdN (some b) (some i)) (DHP h i b) := by
  unfold hdN
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  by_cases hs : st.status = NAME_STATE
  · rw [ite_t (by rw [hs]; decide)]
    obtain ⟨h0, hpo, hple⟩ : st.sym_next = 0 ∧ st.pending_out = st.pending_buf ∧
        st.pending ≤ st.pending_buf_size := by
      rcases K with ⟨hb, -⟩ | ⟨-, x⟩
      · rw [hs] at hb; exact absurd hb (by decide)
      · exact x
    obtain ⟨hw, k, g, hgz, hg, hg0⟩ := hdr_of R hst (Or.inr (Or.inl hs))
    refine ival_of hst hgz ?_
    refine Sat.bind (Sat.of_eq (ldHeader_of hg) ?_)
    by_cases hc : (g.name != .null) = true
    · rw [ite_t hc]
      refine Sat.bind (Sat.mono (string_ok (Or.inl ⟨rfl, rfl⟩) R hst hs h0 hpo hple hgz hg (by simpa using hc)) ?_)
      rintro rr H1 ⟨q1, q2⟩
      cases rr with
      | true =>
        rw [ite_t rfl]
        obtain ⟨R1, l1⟩ := q1 rfl
        exact Sat.pure ⟨R1, fun _ => l1, fun e => absurd rfl e⟩
      | false =>
        rw [ite_f (by simp)]
        obtain ⟨H0, z0, st0, d0, pbo, a, p, s', g', dd, SS, rfl, hsz, hlo, hp, f1, f2, f3, f4, -, f6, hw0⟩ := q2 rfl
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
        have hg' : H0.gzheaders k = some g := run_gz SS.run hg0
        obtain ⟨-, -, -, -, hcm, nbc⟩ := hdr_rd SS.run (SH_dstate _ _ _ _ _ _) f6 hg'
        have R' := seg_run (d := dd) SS.run SS.pb SS.sym SS.pout a p COMMENT_STATE 0 hsz hlo hp (by decide)
          (by decide) (by decide)
          (hdrOk_comment f6 hg' hw0 rfl rfl (hcm.imp id fun ⟨n, c⟩ => ⟨n, nbc n c, cstr_unSH c (nbc n c)⟩))
        exact hdC_ok R' (SH_dstate _ _ _ _ _ _) (.inr ⟨.inl rfl, f2, f3, f4⟩)
    · rw [ite_f hc]
      obtain ⟨z, d, pbo, e, SS⟩ := segS_of R hst h0 hpo
      obtain ⟨-, H2⟩ := (R.side st hst).2.2.1
      obtain ⟨k', g'', hgz', hg'', -, -, -, -, x5⟩ := H2 (Or.inr (Or.inl hs))
      rw [hgz] at hgz'; obtain rfl : k = k' := by injection hgz' with e1; injection e1
      obtain rfl := Option.some.inj (hg.symm.trans hg'')
      have hi0 := x5 hs (by simpa using hc)
      obtain ⟨-, -, -, -, hcm, nbc⟩ := hdr_rd R hst hgz hg
      rw [← e]
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      have := pbs_of R hst
      have R' := seg_run (d := d) SS.run SS.pb SS.sym SS.pout z.adler st.pending COMMENT_STATE st.gzindex rfl
        (fun _ _ => rfl) (by have := UInt32.le_iff_toNat_le.mp hple; omega) (by decide) (by decide) (by decide)
        (hdrOk_comment hgz (by rw [← e] at hg; exact hg) hw rfl hi0
          (hcm.imp id fun ⟨n, c⟩ => ⟨n, nbc n c, c⟩))
      exact hdC_ok R' (SH_dstate _ _ _ _ _ _) (.inr ⟨.inl rfl, h0, hpo, hple⟩)
  · rw [ite_f (by simpa using hs)]
    refine hdC_ok R hst ?_
    rcases K with x | ⟨hA, x⟩
    · exact .inl x
    · exact .inr ⟨hA.resolve_left hs, x⟩

/-- **`deflateHeaders`** from a header state with no pending bytes. -/
theorem headers_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs1 : st.status ≠ BUSY_STATE) (hs2 : st.status ≠ FINISH_STATE) (hp0 : st.pending = 0) :
    Sat H (deflateHeaders (some b) (some i)) (DHP h i b) := by
  obtain ⟨z, st1, al, d, -, -, hst1, -, -, -, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  have h0 : st.sym_next = 0 := c.hdr hs1 hs2
  have hpo : st.pending_out = st.pending_buf := c.pout hp0
  have hpb := pbs_of R hst
  have hlo := c.status_lo
  have hhi := c.status_hi
  simp only [dview] at hlo hhi
  have hlo' := Int32.le_iff_toInt_le.mp hlo
  have hhi' := Int32.le_iff_toInt_le.mp hhi
  -- the rest from `NAME_STATE` on, after a part that went on
  have toN : ∀ H1, Run h i b H1 → (∀ st', H1.dstate b = some st' →
      HKA (fun s => s = NAME_STATE ∨ s = COMMENT_STATE ∨ s = HCRC_STATE) st') →
      Sat H1 (hdN (some b) (some i)) (DHP h i b) := fun H1 R1 K1 => by
    obtain ⟨z', st', al', d', -, -, hst', -, -, -, -⟩ := R1.live
    exact hdN_ok R1 hst' (K1 st' hst')
  -- after `EXTRA_STATE`
  have fromE : ∀ H1, Run h i b H1 → (∀ st', H1.dstate b = some st' → HKs EXTRA_STATE st' ∨
      HKA (fun s => s = NAME_STATE ∨ s = COMMENT_STATE ∨ s = HCRC_STATE) st') →
      Sat H1 (do
        if (← rdD (some b) (·.status)) == EXTRA_STATE then
          if ← headersExtra (some b) (some i) then return Z_OK
        hdN (some b) (some i)) (DHP h i b) := fun H1 R1 K1 => by
    obtain ⟨z', st', al', d', -, -, hst', -, -, -, -⟩ := R1.live
    refine Sat.bind (Sat.of_eq (rdD_dst hst' _) ?_)
    rcases K1 st' hst' with (⟨hb, x⟩ | ⟨hs, x1, x2, x3⟩) | K2
    · rw [ite_f (by rw [hb]; decide)]
      exact toN H1 R1 fun st2 h2 => by obtain rfl := Option.some.inj (hst'.symm.trans h2); exact .inl ⟨hb, x⟩
    · rw [ite_t (by rw [hs]; decide)]
      refine Sat.bind (Sat.mono (extra_ok R1 hst' hs x1 x2 x3) ?_)
      rintro rr H2 ⟨R2, q1, q2⟩
      cases rr with
      | true =>
        rw [ite_t rfl]; exact Sat.pure ⟨R2, fun _ => q1 rfl, fun e => absurd rfl e⟩
      | false =>
        rw [ite_f (by simp)]
        exact toN H2 R2 fun st2 h2 => by
          rcases q2 rfl st2 h2 with x | ⟨y1, y2⟩
          · exact .inl x
          · exact .inr ⟨.inl y1, y2⟩
    · have hne : st'.status ≠ EXTRA_STATE := by
        rcases K2 with ⟨hb, -⟩ | ⟨hA, -⟩
        · rw [hb]; decide
        · rcases hA with e | e | e <;> rw [e] <;> decide
      rw [ite_f (by simpa using hne)]
      exact toN H1 R1 fun st2 h2 => by obtain rfl := Option.some.inj (hst'.symm.trans h2); exact K2
  rw [headers_eq]
  refine Sat.bind (Sat.of_eq (ldDState_app hst) ?_)
  by_cases hI : st.status = INIT_STATE
  · rw [ite_t (by rw [hI]; decide)]
    refine Sat.bind (Sat.mono (init_ok R hst hI hp0) ?_)
    rintro rr H1 ⟨R1, q1, q2⟩
    cases rr with
    | true => rw [ite_t rfl]; exact Sat.pure ⟨R1, fun _ => q1 rfl, fun e => absurd rfl e⟩
    | false =>
      rw [ite_f (by simp)]
      obtain ⟨z', st', al', d', -, -, hst', -, -, -, -⟩ := R1.live
      obtain ⟨k1, k2, k3⟩ := q2 rfl st' hst'
      refine Sat.bind (Sat.of_eq (rdD_dst hst' _) ?_)
      rw [ite_f (by rw [k2]; decide)]
      exact fromE H1 R1 fun st2 h2 => by
        obtain rfl := Option.some.inj (hst'.symm.trans h2); exact .inl (.inl ⟨k2, k1, k3⟩)
  rw [ite_f (by simpa using hI)]
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  by_cases hG : st.status = GZIP_STATE
  · rw [ite_t (by rw [hG]; decide)]
    refine Sat.bind (Sat.mono (gzip_ok R hst hG hp0) ?_)
    rintro rr H1 ⟨R1, q1, q2⟩
    cases rr with
    | true => rw [ite_t rfl]; exact Sat.pure ⟨R1, fun _ => q1 rfl, fun e => absurd rfl e⟩
    | false =>
      rw [ite_f (by simp)]
      exact fromE H1 R1 fun st2 h2 => .inl (q2 rfl st2 h2)
  rw [ite_f (by simpa using hG)]
  refine fromE H R fun st2 h2 => ?_
  obtain rfl := Option.some.inj (hst.symm.trans h2)
  have hpp : st.pending < st.pending_buf_size := by
    rw [hp0, UInt32.lt_iff_toNat_lt]; simp; omega
  by_cases hE : st.status = EXTRA_STATE
  · exact .inl (.inr ⟨hE, h0, hpo, hpp⟩)
  · have t : ∀ x : Int32, st.status ≠ x → st.status.toInt ≠ x.toInt := fun x hx e => hx (Int32.toInt_inj.mp e)
    have a1 := t _ hI; have a2 := t _ hs1; have a3 := t _ hs2; have a4 := t _ hG; have a5 := t _ hE
    have e1 : INIT_STATE.toInt = 1 := rfl
    have e2 : BUSY_STATE.toInt = 2 := rfl
    have e3 : FINISH_STATE.toInt = 3 := rfl
    have e4 : GZIP_STATE.toInt = 4 := rfl
    have e5 : EXTRA_STATE.toInt = 5 := rfl
    have e8 : MAX_STATE.toInt = 8 := rfl
    have e6 : NAME_STATE.toInt = 6 := rfl
    have e7 : COMMENT_STATE.toInt = 7 := rfl
    have e8' : HCRC_STATE.toInt = 8 := rfl
    refine .inr (.inr ⟨?_, h0, hpo, UInt32.le_of_lt hpp⟩)
    rcases (by omega : st.status.toInt = 6 ∨ st.status.toInt = 7 ∨ st.status.toInt = 8) with x | x | x
    · exact .inl (Int32.toInt_inj.mp (x.trans e6.symm))
    · exact .inr (.inl (Int32.toInt_inj.mp (x.trans e7.symm)))
    · exact .inr (.inr (Int32.toInt_inj.mp (x.trans e8'.symm)))

end ZlibNgF.Proof.DeflateBody
