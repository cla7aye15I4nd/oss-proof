import ZlibNgF.Proof.«deflate.c.body.base»

/-!
# `deflate`: the running state (`ZlibNgF`)

`Run h i b H`: inside a `deflate` call on stream `i` (state block `b`) that started at heap `h`, the heap `H` has the
invariant, valid and set buffers, the CRC tables, the frame of the call so far (the output buffer at entry and the
library's block), the output buffer a tail of the one at entry (`OutTail`), and the between-call facts except the one
on `last_flush` (`SideR`), which `deflate` sets on entry and settles before every return. `RunW` is the same with up to
63 bits in `bi_buf` (`DWork`; the bit clause of `SymsOk` waived), as after a block emitter; `flush_pending` turns it
into `Run` (`run_flush`). `Run.done` gives the post of `DeflateOk`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.FlushBlock (dframe_trans dframe_wmono dframe_nil dframe_one)
open ZlibNgF.Proof.DeflateFlush (OutOnly FlushPost flush_work streamIO_out cstr_out disj_mono)

/-- The between-call facts without the one on `last_flush` (`SideAt` reads the heap through the header strings and
the hash chains). -/
def SideR (H : Heap) (b : Nat) (st : DeflateState) : Prop :=
  SymsOk st ∧ (st.status = FINISH_STATE → st.sym_next = 0 ∧ st.lookahead = 0) ∧ HdrOk H b st ∧ FlushOk st ∧
    ∀ d, H.bytes b = some d → ChainOk b d st

/-- The running state of a `deflate` call (see the module comment). -/
structure Run (h : Heap) (i b : Nat) (H : Heap) : Prop where
  inv : DInv H (some i)
  io : DStreamIO H (some i)
  set : DBufsSet H (some i)
  crc : CrcGlobals H
  blk : ∃ z, H.streams i = some z ∧ z.state = some b
  blk0 : ∃ z, h.streams i = some z ∧ z.state = some b
  frame : DFrame h H [i] [b] [] (dOutputRanges h (some i))
  out : OutTail h H i
  side : ∀ st, H.dstate b = some st → SideR H b st

/-- `Run` with up to 63 bits in `bi_buf`. -/
structure RunW (h : Heap) (i b : Nat) (H : Heap) : Prop where
  work : DWork H (some i)
  io : DStreamIO H (some i)
  set : DBufsSet H (some i)
  crc : CrcGlobals H
  blk : ∃ z, H.streams i = some z ∧ z.state = some b
  blk0 : ∃ z, h.streams i = some z ∧ z.state = some b
  frame : DFrame h H [i] [b] [] (dOutputRanges h (some i))
  out : OutTail h H i
  side : ∀ st, H.dstate b = some st → SideR H b { st with bi_valid := 0 }

/-! ## Basic facts -/

theorem SideR.zero {H : Heap} {b : Nat} {st : DeflateState} (S : SideR H b st) : SideR H b { st with bi_valid := 0 } := by
  obtain ⟨⟨a1, a2, a3, a4, -⟩, s2, s3, s4, s5⟩ := S
  exact ⟨⟨a1, a2, a3, a4, fun e => absurd e (by show ¬ (8 : Int32) ≤ 0; decide)⟩, s2, s3, s4, s5⟩

theorem SideR.of_zero {H : Heap} {b : Nat} {st : DeflateState} (S : SideR H b { st with bi_valid := 0 })
    (h8 : st.bi_valid < 8) : SideR H b st := by
  obtain ⟨⟨a1, a2, a3, a4, -⟩, s2, s3, s4, s5⟩ := S
  exact ⟨⟨a1, a2, a3, a4, fun e => absurd h8 (Int32.not_lt.mpr e)⟩, s2, s3, s4, s5⟩

theorem Run.w {h H : Heap} {i b : Nat} (R : Run h i b H) : RunW h i b H :=
  ⟨DWork.of_inv R.inv, R.io, R.set, R.crc, R.blk, R.blk0, R.frame, R.out, fun st hs => (R.side st hs).zero⟩

theorem crc_frame {H H' : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : DFrame H H' S B G W)
    (c : CrcGlobals H) : CrcGlobals H' := by
  obtain ⟨⟨-, -, -, -, -, -, e1, e2, -⟩, -⟩ := f
  exact ⟨e1.trans c.1, e2.trans c.2⟩

theorem bytes_of_dstate {H : Heap} {b : Nat} {st : DeflateState} (hst : H.dstate b = some st) :
    ∃ d, H.bytes b = some d := by
  unfold Heap.dstate at hst; split at hst <;> simp_all

theorem dstates_of_dstate {H : Heap} {b : Nat} {st : DeflateState} {d : Array UInt8} (hst : H.dstate b = some st)
    (hd : H.bytes b = some d) : H.dstates b = some st := by
  simpa [Heap.dstate, hd] using hst

/-- The record, state and bytes of the stream under `Run`. -/
theorem Run.live {h H : Heap} {i b : Nat} (R : Run h i b H) :
    ∃ z st al d, H.streams i = some z ∧ z.state = some b ∧ H.dstate b = some st ∧ H.dallocsOf b = some al ∧
      H.bytes b = some d ∧ SH H i z b st d = H ∧ DCore H (some i) z b (dview st) al := by
  obtain ⟨z, hz, hb⟩ := R.blk
  obtain ⟨i', z', b', st, al, e, hz', hb', hst, hal, c⟩ := R.inv
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨d, hd, e⟩ := DeflateSetDict.sh_of hz hst
  exact ⟨z, st, al, d, hz, hb, hst, hal, hd, e, c⟩

/-- A frame of a step that writes at most `n` bytes of the current output buffer gives the frame of the call. -/
theorem out_frame {h H H' : Heap} {i b : Nat} {z : ZStream} {n : Nat} (F : DFrame h H [i] [b] [] (dOutputRanges h (some i)))
    (O : OutTail h H i) (hz : H.streams i = some z) (f : DFrame H H' [i] [b] [] [(z.next_out, n)])
    (hn : n ≤ z.avail_out.toNat) : DFrame h H' [i] [b] [] (dOutputRanges h (some i)) := by
  obtain ⟨z0, z1, ob, oo, k, h0, h1, e0, e1, ek⟩ := O
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans h1)
  have hd : dOutputRanges h (some i) = [(z0.next_out, z0.avail_out.toNat)] := by simp [dOutputRanges, h0]
  rw [hd] at F ⊢
  refine dframe_trans F (dframe_wmono f fun c j hw w hm off he => ?_)
  rw [List.mem_singleton] at hm; subst hm
  dsimp only at he ⊢
  rw [e1] at he
  injection he with he1 he2; injection he1 with he1; subst he1; subst he2
  have := hw _ (List.mem_singleton_self _) oo (by rw [e0])
  dsimp only at this
  omega

/-- `OutTail` after a step that moves the output by `L` bytes. -/
theorem out_tail {h H H' : Heap} {i : Nat} {z z' : ZStream} {L : Nat} (O : OutTail h H i) (hz : H.streams i = some z)
    (hz' : H'.streams i = some z') (hL : L ≤ z.avail_out.toNat)
    (hno : ∀ ob oo, z.next_out = .ref (.heap ob) oo → z'.next_out = .ref (.heap ob) (oo + L))
    (hav : z'.avail_out.toNat = z.avail_out.toNat - L) : OutTail h H' i := by
  obtain ⟨z0, z1, ob, oo, k, h0, h1, e0, e1, ek⟩ := O
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans h1)
  refine ⟨z0, z', ob, oo, k + L, h0, hz', e0, by rw [hno _ _ e1, Nat.add_assoc], by omega⟩

/-! ## The header and the hash chains across a step -/

/-- The registered header's facts move along a step that writes `L` output bytes (`OutOnly`). -/
theorem hdr_out {H H' : Heap} {i b ob oo L : Nat} {z : ZStream} {st : DeflateState} (hio : DStreamIO H (some i))
    (hz : H.streams i = some z) (hb : z.state = some b) (hst : H.dstate b = some st)
    (hno : z.next_out = .ref (.heap ob) oo) (hL : L ≤ z.avail_out.toNat) (O : OutOnly H H' b ob oo L) :
    HdrMove H H' b b st := by
  obtain ⟨z0, b0, hp, ⟨i0, e0, hz0⟩, hb0, ⟨b1, st1, ⟨⟨z1, ⟨i1, e1, hz1⟩, hb1⟩, hst1⟩, hg1⟩, -, -, -, -, hdj⟩ := hio
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  obtain rfl : st = st1 := Option.some.inj (hst.symm.trans hst1)
  intro _ k g hk hg
  have hpk : hp = some k := by rw [hk] at hg1; injection hg1 with e; exact e.symm
  refine ⟨g, by rw [O.2.1]; exact hg, rfl, rfl, rfl, rfl, fun p n hpn nb c => ⟨?_, nb⟩⟩
  have hr : DReadRange H z hp (p, n + 1) := by
    refine .inr ⟨k, hpk, g, hg, .inr ?_⟩
    rcases hpn with rfl | rfl
    · exact .inl ⟨n, c, rfl⟩
    · exact .inr ⟨n, c, rfl⟩
  have hd := (hdj _ hr).1
  rw [hno] at hd
  exact cstr_out O c nb (disj_mono hd hL (Nat.le_refl _))

/-- The hash chains move along a change of the bytes of block `b` outside `head` and `prev` (below `pending_buf` in the
layout), to a state that keeps the fields `ChainOk` reads. -/
theorem chain_keep {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState} {al : DeflateAllocs}
    {d d' : Array UInt8} (c : DCore H (some i) z b (dview st) al) (hd : H.bytes b = some d) (C : ChainOk b d st)
    (hpb : ∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) → ∀ j, j < pbo → d'[j]! = d[j]!)
    (e1 : st'.level = st.level) (e2 : st'.strategy = st.strategy) (e3 : st'.head = st.head) (e4 : st'.prev = st.prev)
    (e5 : st'.strstart = st.strstart) (e6 : st'.lookahead = st.lookahead) (e7 : st'.w_size = st.w_size) :
    ChainOk b d' st' := by
  obtain ⟨d0, wo, po, ho, pbo, hd0, -, hp, hh, hpb0, -, h2, h3, -⟩ := c.lay
  obtain ⟨w1, -⟩ := c.sizes
  simp only [dview] at hp hh hpb0 h2 h3 w1
  obtain rfl := Option.some.inj (hd.symm.trans hd0)
  refine DeflateSide.ChainOk.of_state (DeflateSide.ChainOk.of_bytes C (by omega) fun ho' po' hh' hp' => ?_)
    e1 e2 e3 e4 e5 e6 e7
  rw [hh] at hh'; rw [hp] at hp'
  obtain rfl : ho = ho' := by injection hh' with e; injection e
  obtain rfl : po = po' := by injection hp' with e; injection e
  exact ⟨fun j _ hj => hpb pbo hpb0 j (by omega), fun j _ hj => hpb pbo hpb0 j (by omega)⟩

/-! ## The end of a call -/

/-- `Run` and the fact on `last_flush` give the post of `DeflateOk`. -/
theorem Run.done {h H : Heap} {i b : Nat} (R : Run h i b H)
    (hl : ∀ st, H.dstate b = some st → 0 < st.last_flush → st.sym_next = 0) :
    DFrame h H (streamIds (some i)) (stateIds h (some i)) [] (dOutputRanges h (some i)) ∧
      stateIds H (some i) = stateIds h (some i) ∧ DInv H (some i) ∧ DSide H (some i) := by
  obtain ⟨z0, hz0, hb0⟩ := R.blk0
  obtain ⟨z, hz, hb⟩ := R.blk
  have e0 : stateIds h (some i) = [b] := by simp [stateIds, hz0, hb0]
  have e1 : stateIds H (some i) = [b] := by simp [stateIds, hz, hb]
  refine ⟨by rw [e0]; exact R.frame, by rw [e0, e1], R.inv, fun b' st ⟨i', z', e, hz', hb', hst⟩ => ?_⟩
  obtain rfl := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨s1, s2, s3, s4, s5⟩ := R.side st hst
  exact ⟨s1, hl st hst, s2, s3, s4, s5⟩

/-! ## A change of the stream record, the state and the bytes of the block -/

/-- `Run` after a step to `SH H i z' b st' d'` (no output written) that keeps the invariant's clauses, the buffer
fields of the stream, the header pointer, and `SideR`. -/
theorem run_SH {h H : Heap} {i b : Nat} {z z' : ZStream} {st st' : DeflateState} {d' : Array UInt8}
    {al : DeflateAllocs} (R : Run h i b H) (hz : H.streams i = some z) (hst : H.dstate b = some st)
    (hal : H.dallocsOf b = some al)
    (hc : DCore (SH H i z' b st' d') (some i) z' b (dview st') al) (hzs : z'.state = z.state)
    (h1 : z'.next_in = z.next_in) (h2 : z'.avail_in = z.avail_in) (h3 : z'.next_out = z.next_out)
    (h4 : z'.avail_out = z.avail_out) (hgz : st'.gzhead = st.gzhead) (hS : SideR (SH H i z' b st' d') b st') :
    Run h i b (SH H i z' b st' d') := by
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
  have hob : ob ≠ b := fun e => hnb oo (by rw [hno, e])
  have O : OutOnly H (SH H i z' b st' d') b ob oo 0 :=
    ⟨rfl, rfl, fun c' hc' data hd => ⟨data, by simp only [SH] at hd ⊢; rw [upd_ne _ _ _ _ hc']; exact hd,
      rfl, fun _ _ => rfl⟩⟩
  refine ⟨⟨i, z', b, st', al, rfl, SH_streams _ _ _ _ _ _, hb', SH_dstate _ _ _ _ _ _,
      by obtain ⟨d0, hd0⟩ := bytes_of_dstate hst; simpa [Heap.dallocsOf, SH, hd0] using hal, hc⟩,
    streamIO_out R.io hz hb hst hno (Nat.zero_le _) O (SH_streams _ _ _ _ _ _) hzs h1 h2 (by rw [h3, hno]; rfl)
      (by rw [h4]; rfl) (SH_dstate _ _ _ _ _ _) hgz,
    ⟨z', ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, by rw [h3]; exact hnn, fun ha => by rw [h1]; exact hni (by rw [← h2]; exact ha)⟩,
    crc_frame fr R.crc, ⟨z', SH_streams _ _ _ _ _ _, hb'⟩, R.blk0, ?_, ?_, fun st2 hst2 => ?_⟩
  · exact out_frame R.frame R.out hz (dframe_nil _ fr) (Nat.zero_le _)
  · exact out_tail R.out hz (SH_streams _ _ _ _ _ _) (Nat.zero_le _) (fun _ _ e => by rw [h3, e]; rfl) (by rw [h4]; rfl)
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    exact hS

/-! ## `flush_pending` -/

/-- `flush_pending` from `RunW`: no fault, `Run` after, the state changed in the fields of `flush_pending` only, no
pending bytes when output room is left, fewer than 8 bits. -/
theorem run_flush {h H : Heap} {i b : Nat} (R : RunW h i b H) :
    ∃ H', C.run (ZlibNg.DeflateP.flush_pending (some i)) H = .ok ((), H') ∧ Run h i b H' ∧
      ∀ z st, H.streams i = some z → H.dstate b = some st → ∃ z' st', H'.streams i = some z' ∧
        H'.dstate b = some st' ∧ st' = { st with
          pending := st'.pending
          pending_out := st'.pending_out
          bi_buf := st'.bi_buf
          bi_valid := st'.bi_valid } ∧
        z' = { z with
          next_out := z'.next_out
          avail_out := z'.avail_out
          total_out := z'.total_out } ∧
        (z'.avail_out ≠ 0 → st'.pending = 0) ∧ st'.bi_valid < 8 := by
  obtain ⟨z, hz, hb⟩ := R.blk
  have hw := R.work
  obtain ⟨i', z1, b1, st, al, e1, hz1, hb1, hst, hal, -, -, c0, -⟩ := hw
  obtain rfl : i = i' := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  obtain ⟨z2, ⟨i2, e2, hz2⟩, hnn, hni⟩ := R.set
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  have hio0 := R.io
  obtain ⟨z3, b3, hp, ⟨i3, e3, hz3⟩, hb3, -, -, -, hout, hnb, -⟩ := hio0
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  obtain rfl : b = b3 := Option.some.inj (hb.symm.trans hb3)
  have hws : WriteSlice H z.next_out z.avail_out.toNat := hout.resolve_left hnn
  obtain ⟨ob, oo, ad, hno, -, -⟩ := hws
  obtain ⟨H', e, hv, F⟩ := flush_work R.work hz hb hst (hout.resolve_left hnn) hnb
  obtain ⟨L, z', st', hz', hst', hL, hpen, hsteq, hav, hzeq, hadv, F2, O2, P2, hbits⟩ := F
  have hLo : L ≤ z.avail_out.toNat := by rw [hL]; exact Nat.min_le_right _ _
  have O := O2 ob oo hno
  have hzs : z'.state = z.state := by rw [hzeq]
  have hb' : z'.state = some b := by rw [hzs]; exact hb
  have hpz : z'.avail_out ≠ 0 → st'.pending = 0 := fun ha => by
    have h0 : z'.avail_out.toNat ≠ 0 := fun e => ha (UInt32.toNat_inj.mp (by rw [e]; rfl))
    rw [hav] at h0
    exact UInt32.toNat_inj.mp (by rw [hpen]; show _ = 0; omega)
  refine ⟨H', e, ⟨hv, streamIO_out R.io hz hb hst hno hLo O hz' hzs (by rw [hzeq]) (by rw [hzeq]) (hadv ob oo hno)
      hav hst' (by rw [hsteq]), ⟨z', ⟨i, rfl, hz'⟩, by rw [hadv ob oo hno]; simp, fun ha => by
        have : z'.next_in = z.next_in := by rw [hzeq]
        rw [this]; exact hni (by rw [hzeq] at ha; exact ha)⟩,
      crc_frame F2 R.crc, ⟨z', hz', hb'⟩, R.blk0, out_frame R.frame R.out hz F2 hLo,
      out_tail R.out hz hz' hLo hadv hav, fun st2 hst2 => ?_⟩, fun z4 st4 hz4 hst4 => ?_⟩
  · obtain rfl := Option.some.inj (hst'.symm.trans hst2)
    obtain ⟨⟨a1, a2, a3, a4, -⟩, s2, s3, s4, s5⟩ := R.side st hst
    have hst'' := hsteq
    refine ⟨⟨by rw [hst'']; exact a1, by rw [hst'']; exact a2, by rw [hst'']; exact a3, by rw [hst'']; exact a4,
      fun e8 => absurd hbits (Int32.not_lt.mpr e8)⟩, by rw [hst'']; exact s2, ?_, by rw [hst'']; exact s4, ?_⟩
    · have m := hdr_out R.io hz hb hst hno hLo O
      have := (s3.move m)
      rw [hst'']; exact this
    · intro d' hd'
      obtain ⟨d, hd⟩ := bytes_of_dstate hst
      refine chain_keep c0 hd (s5 d hd) (fun pbo hpb j hj => ?_) (by rw [hst'']) (by rw [hst''])
        (by rw [hst'']) (by rw [hst'']) (by rw [hst'']) (by rw [hst'']) (by rw [hst''])
      obtain ⟨d0, d1, hd0, hd1, -, hk⟩ := P2 pbo hpb
      obtain rfl := Option.some.inj (hd.symm.trans hd0)
      obtain rfl := Option.some.inj (hd'.symm.trans hd1)
      exact hk j (Or.inl hj)
  · obtain rfl := Option.some.inj (hz.symm.trans hz4)
    obtain rfl := Option.some.inj (hst.symm.trans hst4)
    exact ⟨z', st', hz', hst', hsteq, hzeq, hpz, hbits⟩

end ZlibNgF.Proof.DeflateBody
