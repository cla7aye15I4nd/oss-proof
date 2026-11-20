import ZlibNgF.Proof.«deflate.c.body.trail»
import ZlibNgF.Proof.«deflate_strategy.common»

/-!
# `deflate`: after the strategy (`ZlibNgF`)

`run_post`: a strategy's `StratPost` (and `ChainOk` after it) extends `Run`. `runW_emit`: a block emitter of
`TreesFacts` (`zng_tr_align`, `zng_tr_stored_block`) keeps `RunW`. `run_finish`: `status = FINISH_STATE`.
`runW_clear`: `CLEAR_HASH`. `runW_zero`: `strstart = block_start = insert = 0` with no lookahead.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.FlushBlock (dframe_trans dframe_wmono dframe_nil)
open ZlibNgF.Proof.DeflateFlush (OutOnly streamIO_out)
open ZlibNgF.Proof.ChunkMem (fillFold fillFold_size fillFold_get)
open ZlibNgF.Proof.DeflatePsi

/-- `OutTail` composes. -/
theorem out_trans {h H H' : Heap} {i : Nat} (O1 : OutTail h H i) (O2 : OutTail H H' i) : OutTail h H' i := by
  obtain ⟨z0, z1, ob, oo, k, h0, h1, e0, e1, ek⟩ := O1
  obtain ⟨z1', z2, ob', oo', k', h1', h2, e0', e1', ek'⟩ := O2
  obtain rfl := Option.some.inj (h1.symm.trans h1')
  rw [e1] at e0'
  injection e0' with x y
  injection x with x
  subst x; subst y
  exact ⟨z0, z2, ob, oo, k + k', h0, h2, e0, by rw [e1', Nat.add_assoc], by omega⟩

/-- The hash chains of a state that does not walk them (level 1, or `HASHLESS`). -/
theorem chainOk_vac {b : Nat} {d : Array UInt8} {st : DeflateState}
    (h : st.level = 1 ∨ HASHLESS st.level st.strategy = true) : ChainOk b d st := by
  intro h1 h2
  rcases h with e | e
  · exact absurd e h1
  · rw [e] at h2; cases h2

/-- `FlushOk` for a `last_flush` of 0 .. 5. -/
theorem flushOk_of {st : DeflateState} (h0 : 0 ≤ st.last_flush) (h5 : st.last_flush ≤ 5) : FlushOk st := by
  refine ⟨Int32.le_trans (by decide) h0, h5, fun e => ?_⟩
  rw [e] at h0; exact absurd h0 (by decide)

/-- **`Run` after a strategy**: from `Run` at the call (state in `BUSY_STATE`, `last_flush` a flush value), the
strategy's `StratPost` and `ChainOk` after it. -/
theorem run_post {h H H' : Heap} {i b : Nat} {flush : Int32} {bs : BlockState} {st : DeflateState}
    (R : Run h i b H) (hst : H.dstate b = some st) (hbusy : st.status = BUSY_STATE) (hl0 : 0 ≤ st.last_flush)
    (P : StratPost H (some i) flush bs H')
    (hC : ∀ st' d, H'.dstate b = some st' → H'.bytes b = some d → ChainOk b d st') :
    Run h i b H' ∧ ∀ st', H'.dstate b = some st' → StratKeeps st st' ∧
      (flush ≠ Z_NO_FLUSH → (∀ z', StreamAt H' (some i) z' → z'.avail_out ≠ 0) → st'.sym_next = 0) ∧
      (bs = .finish_started ∨ bs = .finish_done → st'.sym_next = 0 ∧ st'.lookahead = 0) ∧
      (bs = .block_done → st'.sym_next = 0 ∧ st'.match_available = 0) ∧
      (bs = .block_done ∨ bs = .finish_done → st'.pending = 0) := by
  obtain ⟨Pinv, Pio, Pset, Pfr, Pout, Pblk, Pinp, -, -, -, Ppend, Pst, -⟩ := P
  obtain ⟨z, hz, hb⟩ := R.blk
  obtain ⟨z', ⟨i', e', hz'⟩, hb'⟩ := Pblk b ⟨z, ⟨i, rfl, hz⟩, hb⟩
  obtain rfl := Option.some.inj e'
  have hD : DStateIs H (some i) b st := ⟨i, z, rfl, hz, hb, hst⟩
  have hsi : stateIds H (some i) = [b] := by simp [stateIds, hz, hb]
  have hdo : dOutputRanges H (some i) = [(z.next_out, z.avail_out.toNat)] := by simp [dOutputRanges, hz]
  have F : DFrame H H' [i] [b] [] [(z.next_out, z.avail_out.toNat)] := by
    have := Pfr; rw [hsi, hdo] at this; exact this
  obtain ⟨-, -, -, ⟨f1, f2, -⟩, -, L⟩ := R.side st hst
  refine ⟨⟨Pinv, Pio, Pset, crc_frame Pfr R.crc, ⟨z', hz', hb'⟩, R.blk0, out_frame R.frame R.out hz F (Nat.le_refl _),
    out_trans R.out (Pout i rfl), R.inp.trans (Pinp i rfl), fun st' hst' => ?_⟩, fun st' hst' => ?_⟩
  · obtain ⟨s1, s2, -, -, -, s6⟩ := Pst b st st' hD ⟨i, z', rfl, hz', hb', hst'⟩
    obtain ⟨k1, -, -, -, -, -, k7, -⟩ := s2
    have hb2 : st'.status = BUSY_STATE := k1.trans hbusy
    refine ⟨s1, fun e => absurd (hb2.symm.trans e) (by decide), hdrOk_busy (.inl hb2),
      flushOk_of (by rw [k7]; exact hl0) (by rw [k7]; exact f2), fun d hd => hC st' d hst' hd, (s6 L).1⟩
  · obtain ⟨-, s2, s3, s4, s5, s6⟩ := Pst b st st' hD ⟨i, z', rfl, hz', hb', hst'⟩
    refine ⟨s2, s3, s4, fun e => ⟨s5 e, (s6 L).2 e⟩, fun e => ?_⟩
    obtain ⟨b2, st2, ⟨i2, z2, e2, hz2, hb2, hst2⟩, hp⟩ := Ppend e
    obtain rfl := Option.some.inj e2
    obtain rfl := Option.some.inj (hz'.symm.trans hz2)
    obtain rfl := Option.some.inj (hb'.symm.trans hb2)
    obtain rfl := Option.some.inj (hst'.symm.trans hst2)
    exact hp

/-- `status = FINISH_STATE` keeps `Run`, with no symbols and no lookahead. -/
theorem run_finish {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (h0 : st.sym_next = 0) (hl : st.lookahead = 0) :
    Sat H (wrD (some b) fun s => { s with status := FINISH_STATE })
      (fun _ H' => Run h i b H' ∧ H'.streams i = H.streams i ∧
        ∀ st', H'.dstate b = some st' → st' = { st with status := FINISH_STATE }) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  rw [← e]
  refine Sat.of_eq (wrD_SH _) ⟨?_, by rw [SH_streams, SH_streams], fun st' hst' => by
    rw [SH_dstate] at hst'; exact (Option.some.inj hst').symm⟩
  have c' : DCore (SH H i z b { st with status := FINISH_STATE } d) (some i) z b
      (dview { st with status := FINISH_STATE }) al :=
    DCore.of_heap (by simp [hd]) { c with
      status_lo := by show INIT_STATE ≤ FINISH_STATE; decide
      status_hi := by show FINISH_STATE ≤ MAX_STATE; decide
      hdr := fun _ _ => h0 }
  refine run_SH R hz hst hal c' rfl rfl rfl rfl rfl rfl ?_
  obtain ⟨S1, -, -, S4, S5, S6⟩ := R.side st hst
  exact ⟨S1, fun _ => ⟨h0, hl⟩, hdrOk_busy (.inr rfl), S4, fun d' hd' => by
    rw [SH_bytes] at hd'; obtain rfl := Option.some.inj hd'; exact S5 d hd, S6⟩

/-- `RunW` after a step to `SH H i z' b st' d'` (no output written) with the working state, the buffer fields of
the stream, the header pointer, and `SideR`. -/
theorem runW_SH {h H : Heap} {i b : Nat} {z z' : ZStream} {st st' : DeflateState} {d' : Array UInt8}
    (R : RunW h i b H) (hz : H.streams i = some z) (hst : H.dstate b = some st)
    (hW : DWork (SH H i z' b st' d') (some i)) (hzs : z'.state = z.state)
    (h1 : z'.next_in = z.next_in) (h2 : z'.avail_in = z.avail_in) (h3 : z'.next_out = z.next_out)
    (h4 : z'.avail_out = z.avail_out) (hgz : st'.gzhead = st.gzhead)
    (hS : SideR (SH H i z' b st' d') b { st' with bi_valid := 0 }) : RunW h i b (SH H i z' b st' d') := by
  obtain ⟨z1, hz1, hb⟩ := R.blk
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  have hb' : z'.state = some b := by rw [hzs]; exact hb
  have fr : DFrame H (SH H i z' b st' d') [i] [b] [] [] := DeflateReset.dframe_SH _ _ _ _ _ _
  obtain ⟨z2, ⟨i2, e2, hz2⟩, hnn, hni⟩ := R.set
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  have hio0 := R.io
  obtain ⟨z3, b3, hp, ⟨i3, e3, hz3⟩, hb3, -, -, -, hout, hnb, -⟩ := hio0
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  obtain rfl : b = b3 := Option.some.inj (hb.symm.trans hb3)
  obtain ⟨ob, oo, ad, hno, had, hoo⟩ := hout.resolve_left hnn
  have O : OutOnly H (SH H i z' b st' d') b ob oo 0 :=
    ⟨rfl, rfl, fun c' hc' data hd => ⟨data, by simp only [SH] at hd ⊢; rw [upd_ne _ _ _ _ hc']; exact hd,
      rfl, fun _ _ => rfl⟩⟩
  refine ⟨hW, streamIO_out R.io hz hb hst hno (Nat.zero_le _) O (SH_streams _ _ _ _ _ _) hzs h1 h2
      (by rw [h3, hno]; rfl) (by rw [h4]; rfl) (SH_dstate _ _ _ _ _ _) hgz,
    ⟨z', ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, by rw [h3]; exact hnn, fun ha => by rw [h1]; exact hni (by rw [← h2]; exact ha)⟩,
    crc_frame fr R.crc, ⟨z', SH_streams _ _ _ _ _ _, hb'⟩, R.blk0, ?_, ?_,
    R.inp.keep hz (SH_streams _ _ _ _ _ _) h1 h2, fun st2 hst2 => ?_⟩
  · exact out_frame R.frame R.out hz (dframe_nil _ fr) (Nat.zero_le _)
  · exact out_tail R.out hz (SH_streams _ _ _ _ _ _) (Nat.zero_le _) (fun _ _ e => by rw [h3, e]; rfl) (by rw [h4]; rfl)
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    exact hS

/-- The fields that a block emitter keeps (`EmitKeeps`). -/
theorem emit_fields {st st' : DeflateState} (k : EmitKeeps st st') :
    st'.status = st.status ∧ st'.level = st.level ∧ st'.strategy = st.strategy ∧ st'.block_start = st.block_start ∧
      st'.lookahead = st.lookahead ∧ st'.strstart = st.strstart ∧ st'.sym_end = st.sym_end ∧
      st'.last_flush = st.last_flush ∧ st'.gzhead = st.gzhead ∧ st'.pending_buf = st.pending_buf ∧
      st'.head = st.head ∧ st'.prev = st.prev ∧ st'.w_size = st.w_size ∧ st'.prev_length = st.prev_length ∧
      st'.match_start = st.match_start ∧ st'.match_available = st.match_available := by
  rw [k]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A block emitter** of `TreesFacts` on a `RunW` stream in `BUSY_STATE` with no symbols: `RunW` after. -/
theorem runW_emit {h H : Heap} {i b : Nat} {st : DeflateState} {pre : DeflateState → Prop}
    {room grow : DeflateState → Nat} {m : M Unit} (R : RunW h i b H) (E : EmitOk (some i) b pre room grow m)
    (hst : H.dstate b = some st) (hpre : pre st) (hr : PendRoom b st (room st) (4 * st.lit_bufsize.toNat + 9))
    (hs0 : st.sym_next = 0) (hbusy : st.status = BUSY_STATE) :
    ∃ H', C.run m H = .ok ((), H') ∧ RunW h i b H' ∧ aIn H' i = aIn H i ∧ aOut H' i = aOut H i ∧
      ∀ st', H'.dstate b = some st' → EmitKeeps st st' ∧
      st'.pending.toNat ≤ st.pending.toNat + grow st ∧ st'.sym_next = 0 := by
  obtain ⟨z, hz, hb⟩ := R.blk
  obtain ⟨H', e, W', -, -, PO, K, shape⟩ := E H st R.work ⟨i, z, rfl, hz, hb, hst⟩ hpre hr (fun hn => absurd hs0 hn)
  obtain ⟨dt, st', d', rfl⟩ := shape i z rfl hz
  have hst' := SH_dstate H i { z with data_type := dt } b st' d'
  obtain ⟨k1, k2, k3⟩ := K st' ⟨i, _, rfl, SH_streams _ _ _ _ _ _, hb, hst'⟩
  have hs2 : st'.sym_next = 0 := by
    have := UInt32.le_iff_toNat_le.mp k3; rw [hs0] at this
    exact UInt32.toNat_inj.mp (by simp at this ⊢; omega)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ := emit_fields k1
  obtain ⟨⟨a1, a2, -, -, -⟩, -, -, s4, s5, s6⟩ := R.side st hst
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, -, -, -, c0, -⟩ := R.work
  obtain rfl := Option.some.inj e0
  obtain rfl := Option.some.inj (hz.symm.trans hz0)
  obtain rfl := Option.some.inj (hb.symm.trans hb0)
  obtain rfl := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  have hb2 : st'.status = BUSY_STATE := f1.trans hbusy
  refine ⟨_, e, runW_SH R hz hst W' rfl rfl rfl rfl rfl f9 ⟨⟨?_, fun hl => ?_, fun _ _ => hs2, fun _ => hs2,
      fun e8 => absurd e8 (by show ¬ (8 : Int32) ≤ 0; decide)⟩, fun hf => absurd (hb2.symm.trans hf) (by decide),
      hdrOk_busy (.inl hb2), ?_, fun d2 hd2 => ?_, LazyOk.of_eq s6 f14 f5 f15 f6 f13 f16 f4 f2 f3 f8⟩,
    by rw [aIn_of (SH_streams _ _ _ _ _ _), aIn_of hz], by rw [aOut_of (SH_streams _ _ _ _ _ _), aOut_of hz],
    fun st2 hst2 => ?_⟩
  · show st'.sym_next < st'.sym_end
    have a1' : st.sym_next < st.sym_end := a1
    rw [hs2, f7]; rw [hs0] at a1'; exact a1'
  · have hl' : st.level = 0 := f2.symm.trans hl
    obtain ⟨x1, -, x3⟩ := a2 hl'
    show 0 ≤ st'.block_start ∧ st'.sym_next = 0 ∧ st'.lookahead = 0
    rw [f4, f5]; exact ⟨x1, hs2, x3⟩
  · exact ⟨by show -2 ≤ st'.last_flush; rw [f8]; exact s4.1, by show st'.last_flush ≤ 5; rw [f8]; exact s4.2.1,
      fun e2 => by
        show (st'.strstart.toNat : Int) = st'.block_start.toInt ∧ st'.lookahead = 0
        rw [f6, f4, f5]; exact s4.2.2 (f8.symm.trans e2)⟩
  · rw [SH_bytes] at hd2; obtain rfl := Option.some.inj hd2
    refine chain_keep c0 hd (s5 d hd) (fun pbo hpb j hj => ?_) f2 f3 f11 f12 f6 f5 f13
    obtain ⟨d3, d4, hd3, hd4, -, hk⟩ := PO pbo hpb
    obtain rfl := Option.some.inj (hd.symm.trans hd3)
    rw [SH_bytes] at hd4; obtain rfl := Option.some.inj hd4
    exact hk j (Or.inl hj)
  · obtain rfl := Option.some.inj (hst'.symm.trans hst2)
    exact ⟨k1, k2, hs2⟩

/-- The invariant's clauses after a change of the bytes of block `b` within `head`. -/
theorem dcore_clear {H H' : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    {d d' : Array UInt8} {ho : Nat} (c : DCore H s z b v al) (hd : H.bytes b = some d) (hd' : H'.bytes b = some d')
    (hh : v.head = .val (.ref (.heap b) ho)) (sz : d'.size = d.size)
    (keep : ∀ j, ho + 131072 ≤ j → d'[j]! = d[j]!) : DCore H' s z b v al := by
  obtain ⟨ho1, d1, hd1, hh1, hho⟩ := c.head
  obtain rfl := Option.some.inj (hd.symm.trans hd1)
  obtain rfl : ho1 = ho := by rw [hh] at hh1; injection hh1 with e; injection e with _ e; exact e.symm
  obtain ⟨d0, wo, po, ho', pbo, hd0, hw, hp, hh', hpb, l1, l2, l3, l4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  obtain rfl := Option.some.inj (hd.symm.trans hd0)
  obtain ⟨d2, sbo, hd2, hsb2, hsym⟩ := c.symv
  obtain rfl := Option.some.inj (hd.symm.trans hd2)
  rw [hh] at hh'
  obtain rfl : ho1 = ho' := by injection hh' with e; injection e
  rw [hsb] at hsb2
  obtain rfl : pbo + v.lit_bufsize.toNat + 8 = sbo := by injection hsb2 with e; injection e
  exact { c with
    head := ⟨ho1, d', hd', hh, by omega⟩
    lay := ⟨d', wo, po, ho1, pbo, hd', hw, hp, hh, hpb, l1, l2, l3, by rw [sz]; exact l4, hsb, poo, hpo, hpoo, hpe⟩
    symv := ⟨d', _, hd', hsb, SymOk.of_eq hsym fun k hk => keep _ (by omega)⟩ }

/-- **`CLEAR_HASH`** on a `RunW` stream in `BUSY_STATE`: `RunW` after, the state kept, `head` cleared. -/
theorem runW_clear {h H : Heap} {i b : Nat} {st : DeflateState} (R : RunW h i b H) (hst : H.dstate b = some st)
    (hbusy : st.status = BUSY_STATE) :
    Sat H (CLEAR_HASH (some b)) (fun _ H' => RunW h i b H' ∧ H'.dstate b = some st ∧
      aIn H' i = aIn H i ∧ aOut H' i = aOut H i ∧
      ∃ ho po d, st.head = .val (.ref (.heap b) ho) ∧ st.prev = .val (.ref (.heap b) po) ∧ H'.bytes b = some d ∧
        HeadClear d st ho) := by
  obtain ⟨z, hz, hb⟩ := R.blk
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, hal, v0, v64, c, pr1, pr2⟩ := R.work
  obtain rfl := Option.some.inj e0
  obtain rfl := Option.some.inj (hz.symm.trans hz0)
  obtain rfl := Option.some.inj (hb.symm.trans hb0)
  obtain rfl := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨d, hd, e⟩ := DeflateSetDict.sh_of hz hst
  obtain ⟨d1, wo, po, ho, pbo, hd1, -, hp, hh, -, -, -, l3, l4, -⟩ := c.lay
  obtain rfl := Option.some.inj (hd.symm.trans hd1)
  have hh' : st.head = .val (.ref (.heap b) ho) := hh
  have hp' : st.prev = .val (.ref (.heap b) po) := hp
  have l3' : ho + 131072 ≤ pbo := l3
  have l4' : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size := l4
  have hH : HASH_SIZE.toNat * 2 = 131072 := rfl
  have sz : (fillFold 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d).size = d.size := fillFold_size _ _ _ _
  have keep : ∀ j, ho + 131072 ≤ j → (fillFold 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d)[j]! = d[j]! :=
    fun j hj => fillFold_get _ _ _ _ _ fun x hx => by simp only [List.mem_range'_1, hH] at hx; omega
  have hc : HeadClear (fillFold 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d) st ho := fun _ j h1 h2 =>
    ZlibNgF.Proof.DeflateAlloc.fillFold_in 0 ho _ d j ⟨j - ho, by
      simp only [List.mem_range'_1]; exact ⟨Nat.zero_le _, by show j - ho < 0 + 65536 * 2; omega⟩, by omega⟩
      (by omega)
  rw [← e]
  refine Sat.of_eq (DeflateSetDict.clear_hash_SH hh' (by omega)) ⟨?_, SH_dstate _ _ _ _ _ _,
    aIn_congr (by rw [SH_streams, SH_streams]), aOut_congr (by rw [SH_streams, SH_streams]),
    ho, po, _, hh', hp', SH_bytes _ _ _ _ _ _, hc⟩
  have W : DWork (SH H i z b st (fillFold 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d)) (some i) :=
    ⟨i, z, b, st, al, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _, by simpa [Heap.dallocsOf, SH, hd] using hal,
      v0, v64, dcore_clear c hd (SH_bytes _ _ _ _ _ _) hh sz keep, pr1, pr2⟩
  obtain ⟨S1, S2, -, S4, -, S6⟩ := R.side st hst
  refine runW_SH R hz hst W rfl rfl rfl rfl rfl rfl ⟨S1, S2, hdrOk_busy (.inl hbusy), S4, fun d2 hd2 => ?_, S6⟩
  rw [SH_bytes] at hd2; obtain rfl := Option.some.inj hd2
  exact DeflateSide.chainOk_clear hh' hp' hc

/-- **`strstart = block_start = insert = 0`** with no lookahead, on a `RunW` stream in `BUSY_STATE` with no symbols,
no pending literal and a clear `head`: `RunW` after. -/
theorem runW_zero {h H : Heap} {i b : Nat} {st : DeflateState} (R : RunW h i b H) (hst : H.dstate b = some st)
    (hbusy : st.status = BUSY_STATE) (hl : st.lookahead = 0) (hs0 : st.sym_next = 0) (hm : st.match_available = 0)
    {ho po : Nat} {d : Array UInt8} (hh : st.head = .val (.ref (.heap b) ho)) (hp : st.prev = .val (.ref (.heap b) po))
    (hd : H.bytes b = some d) (hc : HeadClear d st ho) {β : Type} {k : M β} {Q : β → Heap → Prop}
    (hk : ∀ H', RunW h i b H' → H'.dstate b = some { st with strstart := 0, block_start := 0, insert := 0 } →
      aIn H' i = aIn H i → aOut H' i = aOut H i → Sat H' k Q) :
    Sat H (do
        wrD (some b) fun s => { s with strstart := 0 }
        wrD (some b) fun s => { s with block_start := 0 }
        wrD (some b) fun s => { s with insert := 0 }
        k) Q := by
  obtain ⟨z, hz, hb⟩ := R.blk
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, hal, v0, v64, c, pr1, pr2⟩ := R.work
  obtain rfl := Option.some.inj e0
  obtain rfl := Option.some.inj (hz.symm.trans hz0)
  obtain rfl := Option.some.inj (hb.symm.trans hb0)
  obtain rfl := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨d1, hd1, e⟩ := DeflateSetDict.sh_of hz hst
  obtain rfl := Option.some.inj (hd.symm.trans hd1)
  obtain ⟨⟨a1, -, -, -, -⟩, -, -, s4, -, s6⟩ := R.side st hst
  have hpl : st.prev_length < 3 := by
    by_cases h3 : 3 ≤ st.prev_length
    · have x := (s6.1 h3).2.1
      have y := UInt32.le_iff_toNat_le.mp h3
      change st.prev_length.toNat ≤ st.lookahead.toNat + 1 at x
      rw [hl] at x; simp at x y; omega
    · exact UInt32.not_le.mp h3
  rw [← e]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) (hk _ ?_ (SH_dstate _ _ _ _ _ _)
    (aIn_congr (by rw [SH_streams, hz])) (aOut_congr (by rw [SH_streams, hz]))))
  have c1 := Strategy.dcore_set c 0 0 0 0 (by simp) (by decide) (UInt32.le_refl _) (by decide)
  have ev : dview { st with strstart := 0, block_start := 0, insert := 0, bi_valid := 0 } =
      { dview { st with bi_valid := 0 } with strstart := 0, lookahead := 0, block_start := 0, insert := 0 } := by
    simp only [dview, hl]
  have W : DWork (SH H i z b { st with strstart := 0, block_start := 0, insert := 0 } d) (some i) :=
    ⟨i, z, b, _, al, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _,
      by simpa [Heap.dallocsOf, SH, hd] using hal, v0, v64,
      by rw [ev]; exact DCore.of_heap (by simp [SH_bytes, hd]) c1, pr1, pr2⟩
  refine runW_SH R hz hst W rfl rfl rfl rfl rfl rfl ⟨⟨a1, fun _ => ⟨by show (0 : Int32) ≤ 0; decide, hs0, hl⟩, fun _ _ => hs0,
    fun _ => hs0, fun e8 => absurd e8 (by show ¬ (8 : Int32) ≤ 0; decide)⟩,
    fun hf => absurd (hbusy.symm.trans hf) (by decide), hdrOk_busy (.inl hbusy),
    ⟨s4.1, s4.2.1, fun _ => ⟨by show ((0 : UInt32).toNat : Int) = (0 : Int32).toInt; decide, hl⟩⟩, fun d2 hd2 => ?_, LazyOk.of_clear hpl hm⟩
  rw [SH_bytes] at hd2; obtain rfl := Option.some.inj hd2
  exact DeflateSide.chainOk_clear hh hp hc

/-! ## `afterStrat` in parts -/

/-- `need_more` / `finish_started` (`deflate.c:1074-1084`). -/
def afterNM (st : StatePtr) (strm : StreamPtr) : M Int32 := do
  if (← rdZ strm (·.avail_out)) == 0 then
    wrD st fun s => { s with last_flush := -1 }
  return Z_OK

/-- The end of `block_done` (`deflate.c:1094-1098`), then the trailer. -/
def bdTail (st : StatePtr) (strm : StreamPtr) (flush : Int32) : M Int32 := do
  ZlibNg.DeflateP.flush_pending strm
  if (← rdZ strm (·.avail_out)) == 0 then
    wrD st fun s => { s with last_flush := -1 }
    return Z_OK
  bodyD st strm flush

/-- `block_done` (`deflate.c:1085-1098`), then the trailer. -/
def afterBD (st : StatePtr) (strm : StreamPtr) (flush : Int32) : M Int32 := do
  if flush == Z_PARTIAL_FLUSH then
    ZlibNg.Trees.zng_tr_align st
  else if flush != Z_BLOCK then
    ZlibNg.Trees.zng_tr_stored_block st .null 0 0
    if flush == Z_FULL_FLUSH then
      CLEAR_HASH st
      if (← rdD st (·.lookahead)) == 0 then
        wrD st fun s => { s with strstart := 0 }
        wrD st fun s => { s with block_start := 0 }
        wrD st fun s => { s with insert := 0 }
  bdTail st strm flush

/-- What follows the `FINISH_STATE` store. -/
def afterR (bstate : BlockState) (st : StatePtr) (strm : StreamPtr) (flush : Int32) : M Int32 :=
  if (bstate == .need_more || bstate == .finish_started) = true then afterNM st strm
  else if (bstate == .block_done) = true then afterBD st strm flush
  else bodyD st strm flush

theorem after_eq (bstate : BlockState) (st : StatePtr) (strm : StreamPtr) (flush : Int32) :
    afterStrat bstate st strm flush = (do
      if bstate == .finish_started || bstate == .finish_done then
        wrD st fun s => { s with status := FINISH_STATE }
      afterR bstate st strm flush) := by
  rfl

/-- Room for `n ≤ 64` bytes in `pending_buf` with no pending bytes. -/
theorem pendRoom0 {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hp0 : st.pending = 0) (n : Nat) (hn : n ≤ 64) : PendRoom b st n (4 * st.lit_bufsize.toNat + 9) := by
  obtain ⟨z, st1, al, d, -, -, hst1, -, -, -, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  obtain ⟨_, _, _, _, pbo, _, -, -, -, hpb, -, -, -, -, -, poo, hpoo, -, -⟩ := c.lay
  have hpo := c.pout hp0
  obtain ⟨-, -, -, k1, -⟩ := c.sizes
  simp only [dview] at hpb hpoo hpo k1
  rw [hpo, hpb] at hpoo
  obtain rfl : poo = pbo := by injection hpoo with e; injection e with _ e; exact e.symm
  refine ⟨poo, poo, hpb, by rw [hpo, hpb], ?_⟩
  rw [hp0]; simp; omega

/-- `bdTail`: the flush, then the trailer, from `RunW` in `BUSY_STATE` with no symbols. -/
theorem bdTail_ok {h H : Heap} {i b : Nat} {st : DeflateState} {flush : Int32} {P : Nat} (W : RunW h i b H)
    (hst : H.dstate b = some st) (hbusy : st.status = BUSY_STATE) (hlf : st.last_flush = flush)
    (hs0 : st.sym_next = 0) (hcf : flush ≠ Z_FINISH → aIn H i = 0 ∨ aOut H i = 0) (B : Bud flush P 0 0 h i b H) :
    Sat H (bdTail (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r ∧
      EndOk flush P h i b H') := by
  obtain ⟨H1, e1, R1, k, -, bf⟩ := run_flushB W
  have B1 := bf flush P 0 0 B
  obtain ⟨z, hz, -⟩ := W.blk
  obtain ⟨z1, st1, hz1, hst1, hse, hze, hpz, -, -, hav⟩ := k z st hz hst
  unfold bdTail
  refine Sat.bind ⟨(), H1, e1, ?_⟩
  refine Sat.bind (Sat.of_eq (rdZ_app hz1 _) ?_)
  by_cases ha : (z1.avail_out == 0) = true
  · rw [ite_t ha]
    have ha0 : z1.avail_out = 0 := by simpa using ha
    exact Sat.bind (Sat.mono (run_lfE R1 (fun z' hz' => by obtain rfl := Option.some.inj (hz1.symm.trans hz'); exact ha0)
      B1) fun _ H2 q => Sat.pure ⟨q.1, lfok_m1 q.2.1, DIO.o0 (by
        obtain ⟨z2, -, -, -, hz2, -⟩ := q.1.live; rw [aOut_of hz2, q.2.1.2 z2 hz2]; rfl), q.2.2⟩)
  · rw [ite_f ha]
    have ha' : z1.avail_out ≠ 0 := by simpa using ha
    refine trailer_ok R1 hst1 (.inl (by rw [hse]; exact hbusy)) (by rw [hse]; exact hlf)
      (fun _ => by rw [hse]; exact hs0) (hpz ha') (fun hf => .inl ?_) B1
    have h1 : aIn H1 i = aIn H i := by rw [aIn_of hz1, aIn_of hz, hze]
    rcases hcf hf with h0 | h0
    · rw [h1, h0]
    · exfalso
      rw [aOut_of hz] at h0
      have : z1.avail_out.toNat ≠ 0 := fun e => ha' (UInt32.toNat_inj.mp (by rw [e]; rfl))
      have p0 := hpz ha'
      rw [p0] at hav
      simp at hav; omega

/-- The budget after a block emitter that adds at most `k` bytes owed. -/
theorem bud_emit {h H H2 : Heap} {i b : Nat} {f : Int32} {P k : Nat} {st : DeflateState}
    (B : Bud f P k 0 h i b H) (hst : H.dstate b = some st) (ea : aIn H2 i = aIn H i) (eo : aOut H2 i = aOut H i)
    (K : ∀ st2, H2.dstate b = some st2 → EmitKeeps st st2 ∧ st2.sym_next = 0 ∧ owed st2 ≤ owed st + k)
    (hs0 : st.sym_next = 0) : Bud f P 0 0 h i b H2 := by
  refine B.step ⟨st, hst⟩ ea eo fun s1 s2 h1 h2 => ?_
  obtain rfl := Option.some.inj (hst.symm.trans h1)
  obtain ⟨k1, k2, k3⟩ := K s2 h2
  have := psiS_emit f k1 (by rw [k2, hs0])
  omega

/-- **`block_done`** (`afterBD`), from `Run` in `BUSY_STATE` with no pending bytes, no symbols, no pending literal. -/
theorem afterBD_ok (T : TreesFacts) {h H : Heap} {i b : Nat} {st : DeflateState} {flush : Int32} {P : Nat}
    (R : Run h i b H)
    (hst : H.dstate b = some st) (hbusy : st.status = BUSY_STATE) (hlf : st.last_flush = flush)
    (hs0 : st.sym_next = 0) (hm : st.match_available = 0) (hp0 : st.pending = 0)
    (hcf : flush ≠ Z_FINISH → aIn H i = 0 ∨ aOut H i = 0) (B : Bud flush P (markK flush) 0 h i b H)
    (hfl : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK) :
    Sat H (afterBD (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r ∧
      EndOk flush P h i b H') := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, -, -, -, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  have hb64 : st.bi_valid.toInt.toNat ≤ 63 := by
    have := c.bits; simp only [dview] at this
    have := Int32.lt_iff_toInt_lt.mp this.2; simp at this; omega
  have hD : DStateIs H (some i) b st := ⟨i, z, rfl, hz, hb, hst⟩
  have dst : ∀ H2, RunW h i b H2 → ∀ st2, H2.dstate b = some st2 → DStateIs H2 (some i) b st2 := fun H2 W2 st2 h2 => by
    obtain ⟨z2, hz2, hb2⟩ := W2.blk
    exact ⟨i, z2, rfl, hz2, hb2, h2⟩
  -- after an emitter: the tail
  have tl : ∀ H2, RunW h i b H2 → (∀ st2, H2.dstate b = some st2 → st2.status = BUSY_STATE ∧
      st2.last_flush = flush ∧ st2.sym_next = 0) → aIn H2 i = aIn H i → aOut H2 i = aOut H i →
      Bud flush P 0 0 h i b H2 →
      Sat H2 (bdTail (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r ∧
        EndOk flush P h i b H') := by
    intro H2 W2 K2 ea eo B2
    obtain ⟨z2, hz2, hb2⟩ := W2.blk
    obtain ⟨i2, z3, b3, st2, al2, e2, hz3, hb3, hst2, -⟩ := W2.work
    obtain rfl := Option.some.inj e2
    obtain rfl := Option.some.inj (hz2.symm.trans hz3)
    obtain rfl := Option.some.inj (hb2.symm.trans hb3)
    obtain ⟨k1, k2, k3⟩ := K2 st2 hst2
    exact bdTail_ok W2 hst2 k1 k2 k3 (fun hf => by rw [ea, eo]; exact hcf hf) B2
  unfold afterBD
  by_cases h1 : (flush == Z_PARTIAL_FLUSH) = true
  · rw [ite_t h1]
    have hP : flush = Z_PARTIAL_FLUSH := by simpa using h1
    obtain ⟨H2, e2, W2, ea2, eo2, K2⟩ := runW_emit R.w (T.align (some i) b) hst trivial
      (pendRoom0 R hst hp0 16 (by omega)) hs0 hbusy
    have B2 : Bud flush P 0 0 h i b H2 := bud_emit B hst ea2 eo2 (fun st2 h2 => ⟨(K2 st2 h2).1, (K2 st2 h2).2.2, by
      have := (TreesOwed.align_owed (s := some i) (b := b) H H2 st R.w.work hD trivial
        (pendRoom0 R hst hp0 16 (by omega)) e2 st2 (dst H2 W2 st2 h2)).2
      rw [hP, show markK Z_PARTIAL_FLUSH = 2 by decide]; exact this⟩) hs0
    exact Sat.bind ⟨(), H2, e2, tl H2 W2 (fun st2 h2 => by
      obtain ⟨f1, -, -, -, -, -, -, f8, -⟩ := emit_fields (K2 st2 h2).1
      exact ⟨f1.trans hbusy, f8.trans hlf, (K2 st2 h2).2.2⟩) ea2 eo2 B2⟩
  rw [ite_f h1]
  by_cases h5 : (flush != Z_BLOCK) = true
  · rw [ite_t h5]
    have hroom : storedRoom st 0 ≤ 64 := by
      unfold storedRoom; have : (0 : UInt32).toNat = 0 := rfl; omega
    have hK5 : markK flush = 5 := by
      have n1 : flush ≠ Z_PARTIAL_FLUSH := by simpa using h1
      have n5 : flush ≠ Z_BLOCK := by simpa using h5
      rcases hfl with x | x | x | x
      · exact absurd x n1
      · rw [x]; decide
      · rw [x]; decide
      · exact absurd x n5
    obtain ⟨H2, e2, W2, ea2, eo2, K2⟩ := runW_emit R.w (T.stored_block (some i) b .null 0 0) hst (.inl ⟨rfl, rfl⟩)
      (pendRoom0 R hst hp0 _ hroom) hs0 hbusy
    have B2 : Bud flush P 0 0 h i b H2 := bud_emit B hst ea2 eo2 (fun st2 h2 => ⟨(K2 st2 h2).1, (K2 st2 h2).2.2, by
      have := (TreesOwed.stored_empty_owed (s := some i) (b := b) 0 H H2 st R.w.work hD trivial
        (pendRoom0 R hst hp0 _ hroom) e2 st2 (dst H2 W2 st2 h2)).2
      rw [hK5]; exact this⟩) hs0
    refine Sat.bind ⟨(), H2, e2, ?_⟩
    obtain ⟨z2, hz2, hb2⟩ := W2.blk
    obtain ⟨i2, z3, b3, st2, al2, e3, hz3, hb3, hst2, -⟩ := W2.work
    obtain rfl := Option.some.inj e3
    obtain rfl := Option.some.inj (hz2.symm.trans hz3)
    obtain rfl := Option.some.inj (hb2.symm.trans hb3)
    obtain ⟨k1, -, k3⟩ := K2 st2 hst2
    obtain ⟨f1, -, -, -, -, -, -, f8, -, -, -, -, -, -, -, f16⟩ := emit_fields k1
    have hb2' : st2.status = BUSY_STATE := f1.trans hbusy
    by_cases h3 : (flush == Z_FULL_FLUSH) = true
    · rw [ite_t h3]
      refine Sat.bind (Sat.mono (runW_clear W2 hst2 hb2') ?_)
      rintro _ H3 ⟨W3, hst3, ea3, eo3, ho, po, d3, hh, hp, hd3, hc⟩
      have B3 : Bud flush P 0 0 h i b H3 := B2.step ⟨st2, hst2⟩ ea3 eo3 fun s1 s2 g1 g2 => by
        obtain rfl := Option.some.inj (hst2.symm.trans g1)
        obtain rfl := Option.some.inj (hst3.symm.trans g2)
        omega
      refine Sat.bind (Sat.of_eq (rdD_dst hst3 _) ?_)
      by_cases hl : (st2.lookahead == 0) = true
      · rw [ite_t hl]
        refine runW_zero W3 hst3 hb2' (by simpa using hl) k3 (f16.trans hm) hh hp hd3 hc fun H4 W4 h4 ea4 eo4 => ?_
        have B4 : Bud flush P 0 0 h i b H4 := B3.step ⟨st2, hst3⟩ ea4 eo4 fun s1 s2 g1 g2 => by
          obtain rfl := Option.some.inj (hst3.symm.trans g1)
          obtain rfl := Option.some.inj (h4.symm.trans g2)
          have := psiS_zero flush s1
          omega
        exact tl H4 W4 (fun st4 h4' => by
          obtain rfl := Option.some.inj (h4.symm.trans h4'); exact ⟨hb2', f8.trans hlf, k3⟩)
          (ea4.trans (ea3.trans ea2)) (eo4.trans (eo3.trans eo2)) B4
      · rw [ite_f hl]
        exact tl H3 W3 (fun st4 h4 => by obtain rfl := Option.some.inj (hst3.symm.trans h4); exact ⟨hb2', f8.trans hlf, k3⟩)
          (ea3.trans ea2) (eo3.trans eo2) B3
    · rw [ite_f h3]
      exact tl H2 W2 (fun st4 h4 => by obtain rfl := Option.some.inj (hst2.symm.trans h4); exact ⟨hb2', f8.trans hlf, k3⟩)
        ea2 eo2 B2
  · rw [ite_f h5]
    exact tl H R.w (fun st4 h4 => by
      obtain rfl := Option.some.inj (hst.symm.trans h4)
      exact ⟨hbusy, hlf, hs0⟩) rfl rfl (B.mono (by omega))

/-- `afterNM`. -/
theorem afterNM_ok {h H : Heap} {i b : Nat} {flush : Int32} {P e : Nat} (R : Run h i b H)
    (K : ∀ st, H.dstate b = some st → st.last_flush = flush ∧
      (flush ≠ Z_NO_FLUSH → (∀ z', StreamAt H (some i) z' → z'.avail_out ≠ 0) → st.sym_next = 0))
    (hio : DIO h H i flush Z_OK) (B : Bud flush P e 0 h i b H)
    (hmk : aOut H i ≠ 0 → ∀ st, H.dstate b = some st → mark flush st ≤ e) :
    Sat H (afterNM (some b) (some i)) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r ∧
      EndOk flush P h i b H') := by
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, e', c⟩ := R.live
  obtain ⟨k1, k2⟩ := K st hst
  unfold afterNM
  refine Sat.bind (Sat.of_eq (rdZ_app hz _) ?_)
  by_cases ha : (z.avail_out == 0) = true
  · rw [ite_t ha]
    have ha0 : z.avail_out = 0 := by simpa using ha
    exact Sat.bind (Sat.mono (run_lfE R (fun z' hz' => by obtain rfl := Option.some.inj (hz.symm.trans hz'); exact ha0) B)
      fun _ H2 q => Sat.pure ⟨q.1, lfok_m1 q.2.1, DIO.o0 (by
        obtain ⟨z2, -, -, -, hz2, -⟩ := q.1.live; rw [aOut_of hz2, q.2.1.2 z2 hz2]; rfl), q.2.2⟩)
  · rw [ite_f ha]
    have ha' : z.avail_out ≠ 0 := by simpa using ha
    have hao : aOut H i ≠ 0 := by
      rw [aOut_of hz]; intro e0; exact ha' (UInt32.toNat_inj.mp (by rw [e0]; rfl))
    refine Sat.pure ⟨R, fun st2 h2 hl => ?_, hio, endOk_of B fun st2 h2 => Nat.le_trans (hmk hao st2 h2)
      (Nat.le_add_right _ _)⟩
    obtain rfl := Option.some.inj (hst.symm.trans h2)
    refine k2 (fun e0 => by rw [k1, e0] at hl; exact absurd hl (by decide)) fun z' ⟨i', e', hz'⟩ => ?_
    obtain rfl := Option.some.inj e'
    obtain rfl := Option.some.inj (hz.symm.trans hz')
    exact ha'

/-- **What follows the strategy** (`afterStrat`), from `Run` with the strategy's exit facts: on the state, and on the
stream (`A1`: all input consumed or the output full after `need_more` / `block_done`; `A2`: `finish_started` /
`finish_done` only under `Z_FINISH`; `A3`: progress since the entry of `deflate` after `need_more` /
`finish_started` under `Z_FINISH`), and the budget (`B`, with the strategy's allowance as a debt; `hNM`, `hBD`: the
marker that `need_more` with output room or `block_done` may owe or emit is within it). -/
theorem after_ok (T : TreesFacts) {h H : Heap} {i b : Nat} {flush : Int32} {bs : BlockState} {P e : Nat}
    (R : Run h i b H)
    (K : ∀ st, H.dstate b = some st → st.status = BUSY_STATE ∧ st.last_flush = flush ∧
      (flush ≠ Z_NO_FLUSH → (∀ z', StreamAt H (some i) z' → z'.avail_out ≠ 0) → st.sym_next = 0) ∧
      (bs = .finish_started ∨ bs = .finish_done → st.sym_next = 0 ∧ st.lookahead = 0) ∧
      (bs = .block_done → st.sym_next = 0 ∧ st.match_available = 0) ∧
      (bs = .block_done ∨ bs = .finish_done → st.pending = 0))
    (A1 : bs = .need_more ∨ bs = .block_done → aIn H i = 0 ∨ aOut H i = 0)
    (A2 : bs = .finish_started ∨ bs = .finish_done → flush = Z_FINISH)
    (A3 : flush = Z_FINISH → bs = .need_more ∨ bs = .finish_started → aOut h i ≠ 0 →
      aIn H i < aIn h i ∨ aOut H i < aOut h i)
    (B : Bud flush P e (DeflateFacts.finSlack bs) h i b H)
    (hNM : bs = .need_more → aOut H i ≠ 0 → markK flush ≤ e)
    (hBD : bs = .block_done → markK flush ≤ e ∧
      (flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK)) :
    Sat H (afterStrat bs (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r ∧
      EndOk flush P h i b H') := by
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, e', c⟩ := R.live
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := K st hst
  have dioNM : ∀ H1, H1.streams i = H.streams i → (bs = .need_more ∨ bs = .finish_started) →
      DIO h H1 i flush Z_OK := by
    intro H1 hz1 hb'
    refine DIO.congr ?_ hz1
    refine ⟨fun hf _ => ?_, fun _ ef hne => ?_⟩
    · rcases hb' with rfl | rfl
      · exact A1 (.inl rfl)
      · exact absurd (A2 (.inl rfl)) hf
    · rcases ef with ef | ⟨en, hin⟩
      · exact A3 ef hb' hne
      · rcases hb' with rfl | rfl
        · rcases A1 (.inl rfl) with x | x
          · left; omega
          · right; omega
        · exact absurd ((A2 (.inl rfl)).symm.trans en) (by decide)
  have tr : ∀ H1, H1.streams i = H.streams i → ∀ z', StreamAt H (some i) z' → StreamAt H1 (some i) z' :=
    fun H1 e1 z' ⟨i', e', hz'⟩ => ⟨i', e', by obtain rfl := Option.some.inj e'; rw [e1]; exact hz'⟩
  have rest : ∀ H1 st1, Run h i b H1 → H1.streams i = H.streams i → H1.dstate b = some st1 →
      st1.sym_next = st.sym_next → st1.last_flush = flush → st1.pending = st.pending →
      (st1.status = BUSY_STATE ∨ st1.status = FINISH_STATE) →
      (st1.status = FINISH_STATE → bs = .finish_started ∨ bs = .finish_done) →
      st1.match_available = st.match_available → Bud flush P e 0 h i b H1 →
      (bs = .need_more ∨ bs = .finish_started → aOut H1 i ≠ 0 → mark flush st1 ≤ e) →
      Sat H1 (afterR bs (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r ∧
        EndOk flush P h i b H') := by
    intro H1 st1 R1 hz1 hst1 e1 e2 e3 hs hsf e4 B1 hm1
    have K1 : ∀ st2, H1.dstate b = some st2 → st2.last_flush = flush ∧
        (flush ≠ Z_NO_FLUSH → (∀ z', StreamAt H1 (some i) z' → z'.avail_out ≠ 0) → st2.sym_next = 0) :=
      fun st2 h2 => by
        obtain rfl := Option.some.inj (hst1.symm.trans h2)
        exact ⟨e2, fun hf hav => e1.trans (k3 hf fun z' hz' => hav z' (tr H1 hz1 z' hz'))⟩
    have hm1' : ∀ x, (bs = .need_more ∨ bs = .finish_started) → x = bs → aOut H1 i ≠ 0 →
        ∀ st2, H1.dstate b = some st2 → mark flush st2 ≤ e := fun _ hb' _ ha st2 h2 => by
      obtain rfl := Option.some.inj (hst1.symm.trans h2); exact hm1 hb' ha
    unfold afterR
    cases bs with
    | need_more =>
      rw [ite_t (by decide)]
      exact afterNM_ok R1 K1 (dioNM H1 hz1 (.inl rfl)) B1 (hm1' _ (.inl rfl) rfl)
    | finish_started =>
      rw [ite_t (by decide)]
      exact afterNM_ok R1 K1 (dioNM H1 hz1 (.inr rfl)) B1 (hm1' _ (.inr rfl) rfl)
    | block_done =>
      rw [ite_f (by decide), ite_t (by decide)]
      obtain ⟨m1, m2⟩ := k5 rfl
      have hs1 : st1.status = BUSY_STATE := by
        rcases hs with x | x
        · exact x
        · rcases hsf x with x | x <;> cases x
      exact afterBD_ok T R1 hst1 hs1 e2 (e1.trans m1) (e4.trans m2) (e3.trans (k6 (.inl rfl))) (fun _ => by
        rw [aIn_congr hz1, aOut_congr hz1]; exact A1 (.inr rfl)) (B1.mono (by have := (hBD rfl).1; omega))
        (hBD rfl).2
    | finish_done =>
      rw [ite_f (by decide), ite_f (by decide)]
      exact trailer_ok R1 hst1 hs e2 (fun _ => e1.trans (k4 (.inr rfl)).1) (e3.trans (k6 (.inr rfl)))
        (fun hf => absurd (A2 (.inr rfl)) hf) (B1.mono (by omega))
  rw [after_eq]
  dsimp only
  by_cases hfin : bs = .finish_started ∨ bs = .finish_done
  · rw [ite_t (by rcases hfin with rfl | rfl <;> decide)]
    obtain ⟨x1, x2⟩ := k4 hfin
    have hfs : DeflateFacts.finSlack bs = 2 ^ 18 := by unfold DeflateFacts.finSlack; rw [ite_eq_left hfin]
    refine Sat.bind (Sat.mono (run_finish R hst x1 x2) ?_)
    rintro _ H1 ⟨R1, hz1, K1⟩
    obtain ⟨z1, st1, -, -, -, -, hst1, -, -, -, -⟩ := R1.live
    have := K1 st1 hst1
    subst this
    have B1 : Bud flush P e 0 h i b H1 := B.step ⟨st, hst⟩ (aIn_congr hz1) (aOut_congr hz1) fun s1 s2 g1 g2 => by
      obtain rfl := Option.some.inj (hst.symm.trans g1)
      obtain rfl := Option.some.inj (hst1.symm.trans g2)
      have := psiS_finish flush s1 (by rw [k1]; decide)
      rw [hfs]; omega
    exact rest H1 _ R1 hz1 hst1 rfl k2 rfl (.inr rfl) (fun _ => hfin) rfl B1
      fun _ _ => by rw [mark_fin rfl]; exact Nat.zero_le _
  · rw [ite_f (by
      intro x; apply hfin
      cases bs <;> first | (left; rfl) | (right; rfl) | (exfalso; revert x; decide))]
    have hfs : DeflateFacts.finSlack bs = 0 := by unfold DeflateFacts.finSlack; rw [ite_eq_right hfin]
    rw [hfs] at B
    exact rest H st R rfl hst rfl k2 rfl (.inl k1) (fun x => absurd (k1.symm.trans x) (by decide)) rfl B
      fun hb' ha => by
        rcases hb' with rfl | rfl
        · exact Nat.le_trans (mark_le_markK flush st) (hNM rfl ha)
        · exact absurd (.inl rfl) hfin

end ZlibNgF.Proof.DeflateBody
