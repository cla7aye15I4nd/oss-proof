import ZlibNgF.Proof.«deflate.c.body.hdr»
import ZlibNgF.Proof.«deflate.c.body.psi»

/-!
# `deflate`: the potential across the header (`ZlibNgF`)

`headers_psi`: with no `gz_header` registered, `deflateHeaders` from `INIT_STATE` (the zlib header, at most 6 bytes)
or `GZIP_STATE` (the ten fixed bytes) moves to `BUSY_STATE`, which releases the 16 of `content`: the budget is kept,
and no input is consumed. The header states from `EXTRA_STATE` on are reached only with a registered header.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflatePsi
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateBits (WrIn put_byte_SH put_short_SH put_short_msb_SH put_uint32_SH put_uint32_msb_SH)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- The end of a header segment with the budget: `flush_pending` then `pendingReturn` keep the budget, the status,
and the input. -/
theorem flush_ret_psi {h H : Heap} {i b : Nat} {f : Int32} {P e : Nat} (R : Run h i b H)
    (B : Bud f P e 0 h i b H) :
    Sat H (do ZlibNg.DeflateP.flush_pending (some i); pendingReturn (some b))
      (fun _ H' => Bud f P e 0 h i b H' ∧ aIn H' i = aIn H i ∧
        ∀ st st', H.dstate b = some st → H'.dstate b = some st' → st'.status = st.status) := by
  obtain ⟨H1, e1, R1, k, hai, bf⟩ := run_flushB R.w
  obtain ⟨z0, hz0, -⟩ := R.blk
  refine Sat.bind ⟨(), H1, e1, ?_⟩
  have B1 := bf f P e 0 B
  have hs1 : ∀ st st', H.dstate b = some st → H1.dstate b = some st' → st'.status = st.status := by
    intro st st' h0 h1
    obtain ⟨z', st'', -, hst'', hse, -⟩ := k z0 st hz0 h0
    obtain rfl := Option.some.inj (hst''.symm.trans h1)
    rw [hse]
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, eH, c⟩ := R1.live
  unfold pendingReturn
  rw [← eH] at B1 ⊢
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  by_cases hp : (st.pending != 0) = true
  · rw [ite_t hp]
    refine Sat.bind (Sat.of_eq (wrD_SH _) (Sat.pure ⟨?_, ?_, fun s0 s2 h0 h2 => ?_⟩))
    · refine B1.step ⟨st, SH_dstate _ _ _ _ _ _⟩ (aIn_congr (by rw [SH_streams, SH_streams]))
        (aOut_congr (by rw [SH_streams, SH_streams])) fun s1 s2 h1 h2 => ?_
      rw [SH_dstate] at h1 h2
      obtain rfl := Option.some.inj h1
      obtain rfl := Option.some.inj h2
      rw [psiS_lf]; omega
    · rw [aIn_congr (by rw [SH_streams, SH_streams] : (SH H1 i z b { st with last_flush := -1 } d).streams i =
        (SH H1 i z b st d).streams i), eH, hai]
    · rw [SH_dstate] at h2; obtain rfl := Option.some.inj h2
      exact hs1 s0 st h0 (by rw [← eH, SH_dstate])
  · rw [ite_f hp]
    refine Sat.pure ⟨B1, by rw [eH, hai], fun s0 s2 h0 h2 => hs1 s0 s2 h0 (by rw [← eH]; exact h2)⟩

/-- The header bytes: `q <= 10` bytes pending from none, `BUSY_STATE` from `INIT_STATE` / `GZIP_STATE`: 6 more in the
budget. -/
theorem bud_hdr {f : Int32} {P e : Nat} {h H0 : Heap} {i b : Nat} {z z' : ZStream} {st : DeflateState}
    {d0 d : Array UInt8} (g : UInt32) {q : UInt32} (B : Bud f P e 0 h i b (SH H0 i z b st d0))
    (hs : st.status = INIT_STATE ∨ st.status = GZIP_STATE) (hp : st.pending = 0) (hq : q.toNat ≤ 10)
    (hz1 : z'.avail_in = z.avail_in) (hz2 : z'.avail_out = z.avail_out) :
    Bud f P (e + 6) 0 h i b (SH H0 i z' b { st with pending := q, status := BUSY_STATE, gzindex := g } d) := by
  refine B.step ⟨st, SH_dstate _ _ _ _ _ _⟩ (by rw [aIn_of (SH_streams _ _ _ _ _ _), aIn_of (SH_streams _ _ _ _ _ _), hz1])
    (by rw [aOut_of (SH_streams _ _ _ _ _ _), aOut_of (SH_streams _ _ _ _ _ _), hz2]) fun s1 s2 h1 h2 => ?_
  rw [SH_dstate] at h1 h2
  have e1 := Option.some.inj h1
  have e2 := Option.some.inj h2
  subst e1; subst e2
  have hb := psiS_busy f st hs
  have c1 : psiS f { st with pending := q, status := BUSY_STATE, gzindex := g } =
      psiS f { st with status := BUSY_STATE } + q.toNat := by
    have x1 : content { st with pending := q, status := BUSY_STATE, gzindex := g } =
        content { st with status := BUSY_STATE } := rfl
    have x2 : quickB f { st with pending := q, status := BUSY_STATE, gzindex := g } =
        quickB f { st with status := BUSY_STATE } := rfl
    have x3 : owed { st with pending := q, status := BUSY_STATE, gzindex := g } =
        q.toNat + (st.bi_valid.toInt.toNat + 7) / 8 := rfl
    have x4 : owed { st with status := BUSY_STATE } = st.pending.toNat + (st.bi_valid.toInt.toNat + 7) / 8 := rfl
    have x5 : st.pending.toNat = 0 := by rw [hp]; rfl
    unfold psiS; rw [x1, x2, x3]; omega
  omega

/-- The `INIT_STATE` part with the budget. -/
theorem init_psi {h H : Heap} {i b : Nat} {st : DeflateState} {f : Int32} {P e : Nat} (R : Run h i b H)
    (hst : H.dstate b = some st) (hs : st.status = INIT_STATE) (hp0 : st.pending = 0) (B : Bud f P e 0 h i b H) :
    Sat H (headersInit st (some b) (some i)) (fun _ H' => Bud f P e 0 h i b H' ∧ aIn H' i = aIn H i ∧
      ∀ st', H'.dstate b = some st' → st'.status = BUSY_STATE) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, eH, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  rw [← eH] at R B ⊢
  obtain ⟨pbo, hpb, hpd, h0, hpo, l1, l2, l3⟩ := hdr_facts c hd hp0 (by rw [hs]; decide) (by rw [hs]; decide)
  have hw : st.w_size ≠ 0 := c.w_size
  have tail : ∀ (q : UInt32) (dq : Array UInt8), q.toNat ≤ 6 → dq.size = d.size → (∀ j, j < pbo → dq[j]! = d[j]!) →
      Sat (SH H i z b { st with pending := q } dq) (do
        wrZ (some i) fun z => { z with adler := ADLER32_INITIAL_VALUE }
        wrD (some b) fun s => { s with status := BUSY_STATE }
        ZlibNg.DeflateP.flush_pending (some i)
        pendingReturn (some b))
      (fun _ H' => Bud f P e 0 h i b H' ∧ aIn H' i = aIn (SH H i z b st d) i ∧
        ∀ st', H'.dstate b = some st' → st'.status = BUSY_STATE) := by
    intro q dq hq hsz hlo
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    have R' := seg_run R hpb h0 hpo ADLER32_INITIAL_VALUE q BUSY_STATE st.gzindex hsz hlo (by omega) (by decide)
      (by decide) (by decide) (hdrOk_busy (Or.inl rfl))
    have B' := bud_hdr (z' := { z with adler := ADLER32_INITIAL_VALUE }) (d := dq) (q := q) st.gzindex B (.inl hs) hp0
      (by omega) rfl rfl
    refine Sat.mono (flush_ret_psi R' (B'.mono (by omega))) fun _ H' ⟨q1, q2, q3⟩ => ⟨q1, ?_, fun st' h' => ?_⟩
    · rw [q2, aIn_of (SH_streams _ _ _ _ _ _), aIn_of (SH_streams _ _ _ _ _ _)]
    · rw [q3 _ st' (SH_dstate _ _ _ _ _ _) h']
  unfold headersInit
  have swb : Sat (SH H i z b st d) (W_BITS st) (fun _ H' => H' = SH H i z b st d) := by
    unfold W_BITS zng_ctz32; rw [ite_f (by simpa using hw)]; exact Sat.pure rfl
  refine Sat.bind (Sat.mono swb ?_)
  rintro wb _ rfl
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine Sat.bind (Sat.mono (put_short_msb_SH hpb _ (by rw [hp0]; simp; omega)) ?_)
  rintro _ _ ⟨d1, rfl, w1⟩
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  have hp2 : (st.pending + 2).toNat = 2 := by rw [hp0]; rfl
  by_cases hss : (st.strstart != 0) = true
  · rw [ite_t hss]
    refine Sat.bind (Sat.of_eq (rdZ_SH _) (Sat.bind (Sat.mono (put_uint32_msb_SH
      (st := { st with pending := st.pending + 2 }) hpb _
      (by show pbo + (st.pending + 2).toNat + 4 ≤ d1.size; rw [hp2, w1.1]; omega)) ?_)))
    rintro _ _ ⟨d2, rfl, w2⟩
    exact tail (st.pending + 2 + 4) d2 (by rw [UInt32.toNat_add, hp2]; simp) (by rw [w2.1, w1.1])
      (fun j hj => by rw [w2.2 j (Or.inl (by omega)), w1.2 j (Or.inl (by omega))])
  · rw [ite_f hss]
    exact tail (st.pending + 2) d1 (by rw [hp2]; decide) w1.1 (fun j hj => w1.2 j (Or.inl (by omega)))

/-- The `GZIP_STATE` part with no header registered, with the budget. -/
theorem gzip_psi {h H : Heap} {i b : Nat} {st : DeflateState} {f : Int32} {P e : Nat} (R : Run h i b H)
    (hst : H.dstate b = some st) (hs : st.status = GZIP_STATE) (hp0 : st.pending = 0) (hg : st.gzhead = .val none)
    (B : Bud f P e 0 h i b H) :
    Sat H (headersGzip (some b) (some i)) (fun _ H' => Bud f P e 0 h i b H' ∧ aIn H' i = aIn H i ∧
      ∀ st', H'.dstate b = some st' → st'.status = BUSY_STATE) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, eH, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  rw [← eH] at R B ⊢
  obtain ⟨pbo, hpb, hpd, h0, hpo, l1, -, l3⟩ := hdr_facts c hd hp0 (by rw [hs]; decide) (by rw [hs]; decide)
  have e0 : ({ st with pending := 0 } : DeflateState) = st := by rw [← hp0]
  rw [gzip_eq]
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  have P0 : PB H i { z with adler := CRC32_INITIAL_VALUE } b st d pbo 0
      (SH H i { z with adler := CRC32_INITIAL_VALUE } b st d) := ⟨d, by rw [e0], rfl, fun _ _ => rfl⟩
  have hr : pbo + 64 ≤ d.size := by omega
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P0 _) ?_)
  rintro _ H1 P1
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P1 _) ?_)
  rintro _ H2 P2
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P2 _) ?_)
  rintro _ H3 P3
  refine pb_ld P3 ?_
  refine sat_ival (a := none) hg ?_
  rw [ite_t (by decide)]
  unfold gzNone
  refine Sat.bind (Sat.mono (pb_u32 hpb hr (by decide) P3 _) ?_)
  rintro _ H4 P4
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P4 _) ?_)
  rintro _ H5 P5
  refine pb_ld P5 ?_
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P5 _) ?_)
  rintro _ H6 P6
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P6 _) ?_)
  rintro _ H7 ⟨d7, rfl, hs7, hl7⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hq : (0 + 1 + 1 + 1 + 4 + 1 + 1 + 1 : UInt32).toNat = 10 := rfl
  have R' := seg_run R hpb h0 hpo CRC32_INITIAL_VALUE (0 + 1 + 1 + 1 + 4 + 1 + 1 + 1) BUSY_STATE
    st.gzindex hs7 hl7 (by omega) (by decide) (by decide) (by decide) (hdrOk_busy (Or.inl rfl))
  have B' := bud_hdr (z' := { z with adler := CRC32_INITIAL_VALUE }) (d := d7) (q := 0 + 1 + 1 + 1 + 4 + 1 + 1 + 1)
    st.gzindex B (.inr hs) hp0 (by omega) rfl rfl
  refine Sat.mono (flush_ret_psi R' (B'.mono (by omega))) fun _ H' ⟨q1, q2, q3⟩ => ⟨q1, ?_, fun st' h' => ?_⟩
  · rw [q2, aIn_of (SH_streams _ _ _ _ _ _), aIn_of (SH_streams _ _ _ _ _ _)]
  · rw [q3 _ st' (SH_dstate _ _ _ _ _ _) h']

/-- The rest of `deflateHeaders` after the header parts, in `BUSY_STATE`: reads only. -/
theorem rest_busy {H : Heap} {i b : Nat} {st : DeflateState} (hst : H.dstate b = some st)
    (hs : st.status = BUSY_STATE) :
    Sat H (do
      if (← rdD (some b) (·.status)) == EXTRA_STATE then
        if ← headersExtra (some b) (some i) then return Z_OK
      hdN (some b) (some i)) (fun _ H' => H' = H) := by
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  rw [ite_f (by rw [hs]; decide)]
  unfold hdN
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  rw [ite_f (by rw [hs]; decide)]
  unfold hdC
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  rw [ite_f (by rw [hs]; decide)]
  unfold hdH
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  rw [ite_f (by rw [hs]; decide)]
  exact Sat.pure rfl

/-- **`deflateHeaders` with no header registered** keeps the budget and the input. -/
theorem headers_psi {h H : Heap} {i b : Nat} {st : DeflateState} {f : Int32} {P e : Nat} (R : Run h i b H)
    (hst : H.dstate b = some st) (hs1 : st.status ≠ BUSY_STATE) (hs2 : st.status ≠ FINISH_STATE)
    (hp0 : st.pending = 0) (hg : st.gzhead = .val none) (B : Bud f P e 0 h i b H) :
    Sat H (deflateHeaders (some b) (some i)) (fun _ H' => Bud f P e 0 h i b H' ∧ aIn H' i = aIn H i) := by
  -- after a header part that went on: `BUSY_STATE`, the rest reads only
  have fin : ∀ H1, Run h i b H1 → Bud f P e 0 h i b H1 → aIn H1 i = aIn H i →
      (∀ st', H1.dstate b = some st' → st'.status = BUSY_STATE) →
      Sat H1 (do
        if (← rdD (some b) (·.status)) == GZIP_STATE then
          if ← headersGzip (some b) (some i) then return Z_OK
        if (← rdD (some b) (·.status)) == EXTRA_STATE then
          if ← headersExtra (some b) (some i) then return Z_OK
        hdN (some b) (some i)) (fun _ H' => Bud f P e 0 h i b H' ∧ aIn H' i = aIn H i) := by
    intro H1 R1 B1 a1 s1
    obtain ⟨z', st', al', d', -, -, hst', -, -, -, -⟩ := R1.live
    refine Sat.bind (Sat.of_eq (rdD_dst hst' _) ?_)
    rw [ite_f (by rw [s1 st' hst']; decide)]
    exact Sat.mono (rest_busy hst' (s1 st' hst')) fun _ _ e => by subst e; exact ⟨B1, a1⟩
  have fin' : ∀ H1, Run h i b H1 → Bud f P e 0 h i b H1 → aIn H1 i = aIn H i →
      (∀ st', H1.dstate b = some st' → st'.status = BUSY_STATE) →
      Sat H1 (do
        if (← rdD (some b) (·.status)) == EXTRA_STATE then
          if ← headersExtra (some b) (some i) then return Z_OK
        hdN (some b) (some i)) (fun _ H' => Bud f P e 0 h i b H' ∧ aIn H' i = aIn H i) := by
    intro H1 R1 B1 a1 s1
    obtain ⟨z', st', al', d', -, -, hst', -, -, -, -⟩ := R1.live
    exact Sat.mono (rest_busy hst' (s1 st' hst')) fun _ _ e => by subst e; exact ⟨B1, a1⟩
  rw [headers_eq]
  refine Sat.bind (Sat.of_eq (ldDState_app hst) ?_)
  by_cases hI : st.status = INIT_STATE
  · rw [ite_t (by rw [hI]; decide)]
    refine Sat.bind (Sat.mono (sat_and (init_ok R hst hI hp0) (init_psi R hst hI hp0 B)) ?_)
    rintro rr H1 ⟨⟨R1, -, -⟩, B1, a1, s1⟩
    cases rr with
    | true => rw [ite_t rfl]; exact Sat.pure ⟨B1, a1⟩
    | false => rw [ite_f (by simp)]; exact fin H1 R1 B1 a1 s1
  rw [ite_f (by simpa using hI)]
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  by_cases hG : st.status = GZIP_STATE
  · rw [ite_t (by rw [hG]; decide)]
    refine Sat.bind (Sat.mono (sat_and (gzip_ok R hst hG hp0) (gzip_psi R hst hG hp0 hg B)) ?_)
    rintro rr H1 ⟨⟨R1, -, -⟩, B1, a1, s1⟩
    cases rr with
    | true => rw [ite_t rfl]; exact Sat.pure ⟨B1, a1⟩
    | false => rw [ite_f (by simp)]; exact fin' H1 R1 B1 a1 s1
  -- a header state from `EXTRA_STATE` on has a registered header
  exfalso
  obtain ⟨z, st1, al, d, -, -, hst1, -, -, -, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  have hlo := Int32.le_iff_toInt_le.mp c.status_lo
  have hhi := Int32.le_iff_toInt_le.mp c.status_hi
  simp only [dview] at hlo hhi
  have hH : HdrState st := by
    have t : ∀ x : Int32, st.status ≠ x → st.status.toInt ≠ x.toInt := fun x hx e => hx (Int32.toInt_inj.mp e)
    have a1 := t _ hI; have a2 := t _ hs1; have a3 := t _ hs2; have a4 := t _ hG
    have e1 : INIT_STATE.toInt = 1 := rfl
    have e2 : BUSY_STATE.toInt = 2 := rfl
    have e3 : FINISH_STATE.toInt = 3 := rfl
    have e4 : GZIP_STATE.toInt = 4 := rfl
    have e5 : EXTRA_STATE.toInt = 5 := rfl
    have e6 : NAME_STATE.toInt = 6 := rfl
    have e7 : COMMENT_STATE.toInt = 7 := rfl
    have e8 : HCRC_STATE.toInt = 8 := rfl
    have e9 : MAX_STATE.toInt = 8 := rfl
    rw [e1] at hlo; rw [e9] at hhi
    rcases (by omega : st.status.toInt = 5 ∨ st.status.toInt = 6 ∨ st.status.toInt = 7 ∨ st.status.toInt = 8)
      with x | x | x | x
    · exact .inl (Int32.toInt_inj.mp (x.trans e5.symm))
    · exact .inr (.inl (Int32.toInt_inj.mp (x.trans e6.symm)))
    · exact .inr (.inr (.inl (Int32.toInt_inj.mp (x.trans e7.symm))))
    · exact .inr (.inr (.inr (Int32.toInt_inj.mp (x.trans e8.symm))))
  obtain ⟨k, g, hgz, -⟩ := (R.side st hst).2.2.1.2 hH
  rw [hg] at hgz
  cases hgz

end ZlibNgF.Proof.DeflateBody
