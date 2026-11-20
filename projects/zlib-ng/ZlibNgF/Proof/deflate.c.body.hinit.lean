import ZlibNgF.Proof.«deflate.c.body.seg»

/-!
# `deflate`: the zlib header and the flush of a header part (`ZlibNgF`)

`pend_ret`: `pendingReturn` (`if (s->pending != 0) { s->last_flush = -1; return Z_OK; }`). `seg_flush`: the end of a
header segment, `flush_pending` then `pendingReturn` (`HRet`). `init_ok`: the `INIT_STATE` part of `deflateHeaders`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateBits (WrIn put_byte_SH put_short_SH put_short_msb_SH put_uint32_SH put_uint32_msb_SH)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- `last_flush` is -1: the call returns `Z_OK` with output pending. -/
def LastM1 (H : Heap) (b : Nat) : Prop := ∀ st, H.dstate b = some st → st.last_flush = -1

/-- What a header part leaves when it returns (`true`: `return Z_OK` with `last_flush = -1`; `false`: the code goes
on, with the facts `K` of the state). -/
def HRet (h : Heap) (i b : Nat) (K : DeflateState → Prop) (r : Bool) (H : Heap) : Prop :=
  Run h i b H ∧ (r = true → LastM1 H b) ∧ (r = false → ∀ st, H.dstate b = some st → K st)

/-- `last_flush = -1` keeps `Run`. -/
theorem run_lf {h H : Heap} {i b : Nat} (R : Run h i b H) :
    Sat H (wrD (some b) fun s => { s with last_flush := -1 }) (fun _ H' => Run h i b H' ∧ LastM1 H' b) := by
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, e, c⟩ := R.live
  rw [← e]
  refine Sat.of_eq (wrD_SH _) ⟨?_, fun st' hst' => by
    rw [SH_dstate] at hst'; obtain rfl := Option.some.inj hst'; rfl⟩
  refine run_SH (z' := z) (st' := { st with last_flush := -1 }) (d' := d) R hz hst hal
    (DCore.of_heap (by simp [hd]) c) rfl rfl rfl rfl rfl rfl ?_
  obtain ⟨S1, S2, S3, S4, S5, S6⟩ := R.side st hst
  refine ⟨S1, S2, ?_, ⟨by show (-2 : Int32) ≤ -1; decide, by show (-1 : Int32) ≤ 5; decide,
    fun e => absurd e (by show ¬ ((-1 : Int32) = -2); decide)⟩, fun d' hd' => ?_,
    ⟨S6.1, S6.2.1, S6.2.2.1, fun e => absurd e (by show ¬ ((-1 : Int32) = -2); decide)⟩⟩
  · exact S3.move (DeflateSide.hdrMove_out rfl fun r hr => DeflateSetDict.space_SH_ne hr)
  · rw [SH_bytes] at hd'; obtain rfl := Option.some.inj hd'
    exact S5 d hd

/-- `pendingReturn`. -/
theorem pend_ret {h H : Heap} {i b : Nat} {K : DeflateState → Prop} (R : Run h i b H)
    (hK : ∀ st, H.dstate b = some st → st.pending = 0 → K st) :
    Sat H (pendingReturn (some b)) (HRet h i b K) := by
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, e, c⟩ := R.live
  unfold pendingReturn
  rw [← e] at R hK ⊢
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  by_cases hp : (st.pending != 0) = true
  · rw [ite_t hp]
    exact Sat.bind (Sat.mono (run_lf R) fun _ H' q => Sat.pure ⟨q.1, fun _ => q.2, nofun⟩)
  · rw [ite_f hp]
    refine Sat.pure ⟨R, nofun, fun _ st' hst' => ?_⟩
    rw [SH_dstate] at hst'
    obtain rfl := Option.some.inj hst'
    exact hK _ (SH_dstate _ _ _ _ _ _) (by simpa using hp)

/-- `HdrMove` along a step that keeps the header records and every byte object. -/
theorem HdrMove.same {H H' H'' : Heap} {b : Nat} {st : DeflateState} (m : HdrMove H H' b b st)
    (hg : H''.gzheaders = H'.gzheaders) (hs : ∀ r : BRef, Space.get H'' r = Space.get H' r) : HdrMove H H'' b b st := by
  intro hh k g hk hgk
  obtain ⟨g', hg', e1, e2, e3, e4, c⟩ := m hh k g hk hgk
  refine ⟨g', by rw [hg]; exact hg', e1, e2, e3, e4, fun p n hp nb cs => ?_⟩
  obtain ⟨c1, c2⟩ := c p n hp nb cs
  exact ⟨DeflateSide.cstr_get c1 fun r _ _ => hs r, c2⟩

/-- `pendingReturn` changes no byte object and no header record. -/
theorem pend_ret_sp {h H : Heap} {i b : Nat} {K : DeflateState → Prop} (R : Run h i b H)
    (hK : ∀ st, H.dstate b = some st → st.pending = 0 → K st) :
    Sat H (pendingReturn (some b)) (fun r H' => HRet h i b K r H' ∧ H'.gzheaders = H.gzheaders ∧
      (∀ r : BRef, Space.get H' r = Space.get H r) ∧ H'.streams = H.streams ∧
      ∀ st st', H.dstate b = some st → H'.dstate b = some st' → st'.pending = st.pending) := by
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, e, c⟩ := R.live
  have sp : ∀ st' (r : BRef), Space.get (SH H i z b st' d) r = Space.get H r := fun st' r => by
    by_cases hr : r = .heap b
    · subst hr; show (SH H i z b st' d).bytes b = H.bytes b; rw [SH_bytes, hd]
    · exact DeflateSetDict.space_SH_ne hr
  have q := pend_ret R hK
  rw [← e] at q ⊢
  unfold pendingReturn at q ⊢
  obtain ⟨r, H', ex, hq⟩ := q
  refine ⟨r, H', ex, hq, ?_⟩
  simp only [bind_app, rdD_SH] at ex
  split at ex
  · simp only [bind_app, wrD_SH] at ex
    cases ex
    refine ⟨rfl, fun r => (sp _ r).trans (sp _ r).symm, rfl, fun s1 s2 h1 h2 => ?_⟩
    rw [SH_dstate] at h1 h2; obtain rfl := Option.some.inj h1; obtain rfl := Option.some.inj h2; rfl
  · cases ex; exact ⟨rfl, fun _ => rfl, rfl, fun s1 s2 h1 h2 => by rw [h1] at h2; obtain rfl := Option.some.inj h2; rfl⟩

/-- The end of a header segment: `flush_pending` then `pendingReturn`, from a heap in `Run`. On going on, no pending
bytes and the state's other fields as before the flush. -/
theorem flush_ret {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st) :
    Sat H (do ZlibNg.DeflateP.flush_pending (some i); pendingReturn (some b))
      (HRet h i b fun st' => st'.pending = 0 ∧ st' = { st with
          pending := st'.pending
          pending_out := st'.pending_out
          bi_buf := st'.bi_buf
          bi_valid := st'.bi_valid }) := by
  obtain ⟨H', e, R', k⟩ := run_flush R.w
  obtain ⟨z, hz, -⟩ := R.blk
  obtain ⟨z', st', hz', hst', hse, -, -, -, -, -⟩ := k z st hz hst
  refine Sat.bind ⟨(), H', e, ?_⟩
  exact pend_ret R' fun st2 hst2 hp => by
    obtain rfl := Option.some.inj (hst'.symm.trans hst2)
    exact ⟨hp, hse⟩

/-- `flush_pending`, `pendingReturn`, then a continuation on the result. -/
theorem flush_ret_k {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    {β : Type} {k : Bool → M β} {Q : β → Heap → Prop}
    (hk : ∀ r H', HRet h i b (fun st' => st'.pending = 0 ∧ st' = { st with
          pending := st'.pending
          pending_out := st'.pending_out
          bi_buf := st'.bi_buf
          bi_valid := st'.bi_valid }) r H' → HdrMove H H' b b st →
        (∀ z z' st', H.streams i = some z → H'.streams i = some z' → H'.dstate b = some st' →
          z'.avail_out.toNat + st.pending.toNat ≤ z.avail_out.toNat + st'.pending.toNat) → Sat H' (k r) Q) :
    Sat H (do ZlibNg.DeflateP.flush_pending (some i); let r ← pendingReturn (some b); k r) Q := by
  obtain ⟨H', e, R', kk⟩ := run_flush R.w
  obtain ⟨z, hz, -⟩ := R.blk
  obtain ⟨z', st', hz', hst', hse, -, -, -, hm, hav⟩ := kk z st hz hst
  refine Sat.bind ⟨(), H', e, ?_⟩
  refine Sat.bind (Sat.mono (pend_ret_sp R' fun st2 hst2 hp => ?_) fun r H'' ⟨q, g1, g2, g3, g4⟩ =>
    hk r H'' q (HdrMove.same hm g1 g2) fun z1 z2 st2 h1 h2 h3 => by
      obtain rfl := Option.some.inj (hz.symm.trans h1)
      rw [g3] at h2; obtain rfl := Option.some.inj (hz'.symm.trans h2)
      rw [g4 st' st2 hst' h3]; exact hav)
  obtain rfl := Option.some.inj (hst'.symm.trans hst2)
  exact ⟨hp, hse⟩

theorem HRet.mono {h : Heap} {i b : Nat} {K K' : DeflateState → Prop} {r : Bool} {H : Heap} (q : HRet h i b K r H)
    (k : ∀ st, K st → K' st) : HRet h i b K' r H :=
  ⟨q.1, q.2.1, fun e st hs => k st (q.2.2 e st hs)⟩

/-- The header facts of a state outside the gzip header. -/
theorem hdrOk_busy {H : Heap} {b : Nat} {st : DeflateState}
    (hs : st.status = BUSY_STATE ∨ st.status = FINISH_STATE) : HdrOk H b st := by
  have : ¬ (st.status = GZIP_STATE ∨ HdrState st) := by
    unfold HdrState; rcases hs with e | e <;> rw [e] <;> decide
  exact ⟨fun hh => absurd hh this, fun hh => absurd (Or.inr hh) this⟩

/-- The facts of a header state at the start of a header part: the pending buffer, no symbols, `pending_out` at
`pending_buf`, the sizes. -/
theorem hdr_facts {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    {d : Array UInt8} (c : DCore H (some i) z b (dview st) al) (hd : H.bytes b = some d) (hp0 : st.pending = 0)
    (hs1 : st.status ≠ BUSY_STATE) (hs2 : st.status ≠ FINISH_STATE) :
    ∃ pbo, st.pending_buf = .val (.ref (.heap b) pbo) ∧ pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size ∧
      st.sym_next = 0 ∧ st.pending_out = st.pending_buf ∧ 128 ≤ st.lit_bufsize.toNat ∧
      st.lit_bufsize.toNat ≤ 32768 ∧ st.pending_buf_size.toNat = 4 * st.lit_bufsize.toNat := by
  obtain ⟨d0, wo, po, ho, pbo, hd0, -, -, -, hpb, -, -, -, l4, -⟩ := c.lay
  obtain rfl := Option.some.inj (hd.symm.trans hd0)
  obtain ⟨-, -, -, k1, k2, k3, -⟩ := c.sizes
  exact ⟨pbo, hpb, l4, c.hdr hs1 hs2, c.pout hp0, k1, k2, k3⟩

/-- The `INIT_STATE` part of `deflateHeaders`: the zlib header, then the flush. -/
theorem init_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = INIT_STATE) (hp0 : st.pending = 0) :
    Sat H (headersInit st (some b) (some i))
      (HRet h i b fun st' => st'.pending = 0 ∧ st'.status = BUSY_STATE ∧ st'.sym_next = 0) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  rw [← e] at R ⊢
  obtain ⟨pbo, hpb, hpd, h0, hpo, l1, l2, l3⟩ := hdr_facts c hd hp0 (by rw [hs]; decide) (by rw [hs]; decide)
  have hw : st.w_size ≠ 0 := c.w_size
  -- the tail after the header bytes: `adler`, the status, the flush
  have tail : ∀ (q : UInt32) (dq : Array UInt8), q.toNat ≤ 6 → dq.size = d.size → (∀ j, j < pbo → dq[j]! = d[j]!) →
      Sat (SH H i z b { st with pending := q } dq) (do
        wrZ (some i) fun z => { z with adler := ADLER32_INITIAL_VALUE }
        wrD (some b) fun s => { s with status := BUSY_STATE }
        ZlibNg.DeflateP.flush_pending (some i)
        pendingReturn (some b))
      (HRet h i b fun st' => st'.pending = 0 ∧ st'.status = BUSY_STATE ∧ st'.sym_next = 0) := by
    intro q dq hq hsz hlo
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    have R' := seg_run R hpb h0 hpo ADLER32_INITIAL_VALUE q BUSY_STATE st.gzindex hsz hlo (by omega) (by decide)
      (by decide) (by decide) (hdrOk_busy (Or.inl rfl))
    exact Sat.mono (flush_ret R' (SH_dstate _ _ _ _ _ _)) fun r H' q' => q'.mono fun st' ⟨k1, k2⟩ => by
      rw [k2]; exact ⟨k1, rfl, h0⟩
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

end ZlibNgF.Proof.DeflateBody
