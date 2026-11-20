import ZlibNgF.Proof.«deflate_quick.c.match»
import ZlibNgF.Proof.«trees.c.compress»
import ZlibNgF.Proof.«deflate_stored.c.frame»

/-!
# `deflate_quick` with `Z_FIXED`: the frame (`ZlibNgF`)

With `static_emit` (`strategy == Z_FIXED`) `deflate_quick` writes every symbol straight into `pending_buf` with the
static trees and never tallies: `sym_next` stays 0 and up to 63 bits may wait in `bi_buf`. The tally framework of
`Proof/deflate_strategy.common.lean` (`SLF`) keeps fewer than 8 bits, so this path has its own frame `QF`: the
invariant (which allows up to 63 bits), valid and set buffers, the CRC tables, a change of the stream record, the
stream's block and the output buffer only, the output a tail of the output at entry, the fields of `StratKeeps`
unchanged, and no symbols.

Unlike the tally framework, the frame is stated on the heap as it is: the locals `strstart` / `lookahead` of
`deflate_quick_impl` only advance past the stale values in the state, and `block_start` is written only right after
`fill_window` (when the state holds the locals) or with the locals written back, so the stale state keeps the
invariant; the locals are tracked by the numbers of `LocOk`.

The steps: a change of the state record and the block's bytes that keeps the invariant (`qf_SH`), the entry
(`qf_entry`), `flush_pending` (`qf_flush`), writing the locals back and `fill_window` (`qf_fill`), an emitter with an
exact bit count (`qf_emit`), and the exit (`qf_post`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.QuickS
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.FlushBlock (dframe_trans dframe_wmono dframe_nil)
open ZlibNgF.Proof.FillIO (FillIO fill_io streamIO_in)
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.DeflateFlush (flush_ok)
open ZlibNg.DeflateP ZlibNg.DeflateQuick
open ZlibNgF.Proof.DeflatePsi (psiS G span owed content quickB)

/-! ## The frame -/

/-- The frame of `deflate_quick` with `Z_FIXED` on stream `i` (block `b`) from its entry heap `h` to `H`. -/
structure QF (h : Heap) (i b : Nat) (H : Heap) : Prop where
  inv : DInv H (some i)
  io : DStreamIO H (some i)
  set : DBufsSet H (some i)
  crc : CrcGlobals H
  blk : ∃ z, H.streams i = some z ∧ z.state = some b
  blk0 : ∃ z, h.streams i = some z ∧ z.state = some b
  frame : DFrame h H [i] [b] [] (dOutputRanges h (some i))
  out : OutTail h H i
  inp : InTail h H i
  win : ∃ st0, h.dstate b = some st0 ∧ ∀ st, H.dstate b = some st → st.window = st0.window
  keeps : ∃ st0, h.dstate b = some st0 ∧ ∀ st, H.dstate b = some st → StratKeeps st0 st
  sym : ∀ st, H.dstate b = some st → st.sym_next = 0

/-- The record and state of stream `i` under `QF`. -/
theorem QF.live {h H : Heap} {i b : Nat} (F : QF h i b H) :
    ∃ z st al, H.streams i = some z ∧ z.state = some b ∧ H.dstate b = some st ∧ H.dallocsOf b = some al ∧
      DCore H (some i) z b (dview st) al := by
  obtain ⟨z, hz, hb⟩ := F.blk
  obtain ⟨i', z', b', st, al, e, hz', hb', hst, hal, c⟩ := F.inv
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  exact ⟨z, st, al, hz, hb, hst, hal, c⟩

/-- The heap of `QF` as an `SH` heap over itself. -/
theorem QF.sh {h H : Heap} {i b : Nat} (F : QF h i b H) :
    ∃ z st d, H.streams i = some z ∧ H.dstate b = some st ∧ H.bytes b = some d ∧ H = SH H i z b st d := by
  obtain ⟨z, st, -, hz, -, hst, -, -⟩ := F.live
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  exact ⟨z, st, d, hz, hst, hd, (ZlibNgF.Proof.DeflateReset.SH_self hz (dstates_of_dstate hst hd) hd).symm⟩

/-- `QF` after a change of the state record and the bytes of block `b` (sizes kept) that keeps the invariant's
clauses, the header pointer, the window, the fields of `StratKeeps`, and no symbols. -/
theorem qf_SH {h H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState} {d d' : Array UInt8}
    (F : QF h i b (SH H0 i z b st d))
    (hc : ∀ al, (SH H0 i z b st d).dallocsOf b = some al → DCore (SH H0 i z b st d) (some i) z b (dview st) al →
      DCore (SH H0 i z b st' d') (some i) z b (dview st') al)
    (hgz : st'.gzhead = st.gzhead) (hwin : st'.window = st.window) (hsym : st'.sym_next = 0)
    (hk : StratKeeps st st') : QF h i b (SH H0 i z b st' d') := by
  obtain ⟨z1, hz1, hb⟩ := F.blk
  obtain rfl : z = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain ⟨al, hal, c⟩ := inv_SH F.inv hb
  have hal' : (SH H0 i z b st' d').dallocsOf b = some al := by
    simpa [Heap.dallocsOf, SH] using hal
  have hS : SH (SH H0 i z b st d) i z b st' d' = SH H0 i z b st' d' := SH_SH _ _ _ _ _ _ _ _ _
  have fr : DFrame (SH H0 i z b st d) (SH H0 i z b st' d') [i] [b] [] [] := by
    rw [← hS]; exact ZlibNgF.Proof.DeflateReset.dframe_SH _ _ _ _ _ _
  obtain ⟨z2, ⟨i2, e2, hz2⟩, hnn, hni⟩ := F.set
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz2)
  have hio0 := F.io
  obtain ⟨z3, b3, hp, ⟨i3, e3, hz3⟩, hb3, -, -, hin0, hout, hnb, hdj⟩ := hio0
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz3)
  obtain rfl : b = b3 := Option.some.inj (hb.symm.trans hb3)
  obtain ⟨ob, oo, ad, hno, had, hoo⟩ := hout.resolve_left hnn
  have O : ZlibNgF.Proof.DeflateFlush.OutOnly (SH H0 i z b st d) (SH H0 i z b st' d') b ob oo 0 :=
    ⟨rfl, rfl, fun c' hc' data hd => ⟨data, by simp only [SH] at hd ⊢; rw [upd_ne _ _ _ _ hc'] at hd ⊢; exact hd,
      rfl, fun _ _ => rfl⟩⟩
  have hrd : NullOrRead (SH H0 i z b st' d') z.next_in z.avail_in.toNat :=
    ZlibNgF.Proof.DeflateFlush.nullOrRead_out O hin0 (hdj _ (.inl rfl)).2
  refine ⟨⟨i, z, b, st', al, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _, hal', hc al hal c⟩,
    streamIO_in F.io (SH_streams _ _ _ _ _ _) hb (SH_dstate _ _ _ _ _ _) hno (Nat.zero_le _) O
      (SH_streams _ _ _ _ _ _) rfl (Nat.le_refl _) (Or.inl ⟨rfl, rfl⟩) hrd (by rw [hno]; rfl) (by simp)
      (SH_dstate _ _ _ _ _ _) hgz,
    ⟨z, ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, hnn, hni⟩, F.crc, ⟨z, SH_streams _ _ _ _ _ _, hb⟩, F.blk0,
    dframe_trans F.frame (dframe_nil _ fr), ?_, F.inp.keep (SH_streams _ _ _ _ _ _) (SH_streams _ _ _ _ _ _) rfl rfl,
    ?_, ?_, fun st2 hst2 => ?_⟩
  · obtain ⟨z0, z4, ob4, oo4, k, h0, h4, e0, e4, ek⟩ := F.out
    obtain rfl : z = z4 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans h4)
    exact ⟨z0, z, ob4, oo4, k, h0, SH_streams _ _ _ _ _ _, e0, e4, ek⟩
  · obtain ⟨st0, h0, hw⟩ := F.win
    refine ⟨st0, h0, fun st2 hst2 => ?_⟩
    obtain rfl : st' = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    rw [hwin]; exact hw st (SH_dstate _ _ _ _ _ _)
  · obtain ⟨st0, h0, hw⟩ := F.keeps
    refine ⟨st0, h0, fun st2 hst2 => ?_⟩
    obtain rfl : st' = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    exact StratKeeps.trans (hw st (SH_dstate _ _ _ _ _ _)) hk
  · obtain rfl : st' = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    exact hsym

/-- The entry of `deflate_quick` with `Z_FIXED`: `QF` of the entry heap. -/
theorem qf_entry {h : Heap} {i b : Nat} {z : ZStream} {flush : Int32} (P : StratPre h (some i) flush)
    (hz : h.streams i = some z) (hb : z.state = some b)
    (hE : ∀ b' st, DStateIs h (some i) b' st → st.level = 1 ∧ st.strategy = Z_FIXED) :
    ∃ st, h.dstate b = some st ∧ st.pending = 0 ∧ SymsOk st ∧ QF h i b h := by
  obtain ⟨hv, hcrc, hio, hset, -, -, b1, st1, ⟨i1, z1, e1, hz1, hb1, hst1⟩, hp0, -, hs1, -⟩ := P
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  obtain ⟨hlv, hfx⟩ := hE b st1 ⟨i, z, rfl, hz, hb, hst1⟩
  have hs0 : st1.sym_next = 0 := hs1.2.2.1 hlv hfx
  refine ⟨st1, hst1, hp0, hs1, hv, hio, hset, hcrc, ⟨z, hz, hb⟩, ⟨z, hz, hb⟩, dframe_refl _ _ _ _ _, ?_,
    InTail.refl hz hz rfl rfl, ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; rfl⟩,
    ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; exact StratKeeps.refl _⟩, fun st h1 => ?_⟩
  · have hio0 := hio
    obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, -, hout, hnb, -⟩ := hio0
    obtain rfl : i = i2 := Option.some.inj e2
    obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
    obtain ⟨z3, ⟨i3, e3, hz3⟩, hnn, -⟩ := hset
    obtain rfl : i = i3 := Option.some.inj e3
    obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
    obtain ⟨ob, oo, ad, hno, -, -⟩ := hout.resolve_left hnn
    exact ⟨z, z, ob, oo, 0, hz, hz, hno, hno, rfl⟩
  · obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans h1)
    exact hs0

/-! ## The bits -/

/-- The clauses of `DCore` after a change of the pending bytes, the bit buffer (up to 63 bits) and `block_start`, with
`pending_out` at `pending_buf` and no symbols. -/
theorem dcore_bits {H : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st st' : DeflateState}
    {al : DeflateAllocs} (c : DCore H s z b (dview st) al)
    (he : dview st' = { dview st with
      pending := st'.pending
      bi_valid := st'.bi_valid
      block_start := st'.block_start })
    {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hpo : st.pending_out = st.pending_buf)
    (hroom : st'.pending.toNat + st'.bi_valid.toInt.toNat / 8 ≤ 4 * st.lit_bufsize.toNat + 9)
    (h0 : 0 ≤ st'.bi_valid) (h64 : st'.bi_valid < 64)
    (hbs : st'.block_start.toInt ≤ st.strstart.toNat)
    (hlo : -(2 ^ 30 + 2 ^ 16) ≤ st'.block_start.toInt) (hsym : st.sym_next = 0) :
    DCore H s z b (dview st') al := by
  obtain ⟨d, wo, po, ho, pbo', hd, hwo, hp, hh, hpb', h1, h2, h3, h4, hsb, -⟩ := c.lay
  simp only [dview] at hpb'
  rw [hpb] at hpb'
  obtain rfl : pbo = pbo' := by injection hpb' with e1; injection e1 with e1
  rw [he]
  exact { c with
    lay := ⟨d, wo, po, ho, pbo, hd, hwo, hp, hh, hpb, h1, h2, h3, h4, hsb, pbo, hpo.trans hpb, Nat.le_refl _, by
      simp only [dview]; omega⟩
    pout := fun _ => hpo
    bits := ⟨h0, h64⟩
    psym := fun hn => absurd hsym hn
    bstart := hbs
    bs_lo := hlo }

/-- `QF` after a change of the pending bytes, the bit buffer (up to 63 bits), `bi_used`, `block_start` and
`block_open`, and of the block's bytes (size kept), with `pending_out` at `pending_buf`. -/
theorem qf_bits {h H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState} {d d' : Array UInt8}
    (F : QF h i b (SH H0 i z b st d))
    (he : st' = { st with
      pending := st'.pending
      bi_buf := st'.bi_buf
      bi_valid := st'.bi_valid
      bi_used := st'.bi_used
      block_start := st'.block_start
      block_open := st'.block_open })
    {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hpo : st.pending_out = st.pending_buf)
    (hs : d'.size = d.size)
    (hroom : st'.pending.toNat + st'.bi_valid.toInt.toNat / 8 ≤ 4 * st.lit_bufsize.toNat + 9)
    (h0 : 0 ≤ st'.bi_valid) (h64 : st'.bi_valid < 64)
    (hbs : st'.block_start.toInt ≤ st.strstart.toNat)
    (hlo : -(2 ^ 30 + 2 ^ 16) ≤ st'.block_start.toInt) :
    QF h i b (SH H0 i z b st' d') := by
  have hsym := F.sym st (SH_dstate _ _ _ _ _ _)
  refine qf_SH F (fun al _ c => ?_) (by rw [he]) (by rw [he]) (by rw [he]; exact hsym)
    (by rw [he]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩)
  have c1 := ZlibNgF.Proof.StoredF.dcore_mv (H' := SH H0 i z b st' d') c (SH_bytes _ _ _ _ _ _)
    (SH_bytes _ _ _ _ _ _) hs (by simpa [dview] using hsym) rfl rfl
  exact dcore_bits c1 ((congrArg dview he).trans rfl) hpb hpo hroom h0 h64 hbs hlo hsym

/-! ## `flush_pending` -/

/-- `s->strm` of a stream under `QF`. -/
theorem strmOf_qf {h H : Heap} {i b : Nat} (F : QF h i b H) : strmOf (some b) H = .ok (some i, H) := by
  obtain ⟨z, st, al, hz, hb, hst, -, c⟩ := F.live
  have hs : st.strm = .val (some i) := c.strm
  simp [strmOf, ldDState_app hst, bind_app, hs, Ival.get]

/-- `flush_pending(s->strm)` under `QF`: `QF` after, the state changed in the pending bytes and the bit buffer only,
fewer than 8 bits, the input kept, and no pending bytes (with `pending_out` back at `pending_buf`) when output room
is left. -/
theorem qf_flush {h H : Heap} {i b : Nat} (F : QF h i b H) :
    Sat H (flush_pending (some i)) (fun _ H' => QF h i b H' ∧ ∃ z st z' st', H.streams i = some z ∧
      H.dstate b = some st ∧ H'.streams i = some z' ∧ H'.dstate b = some st' ∧
      st' = { st with
        pending := st'.pending
        pending_out := st'.pending_out
        bi_buf := st'.bi_buf
        bi_valid := st'.bi_valid } ∧ st'.bi_valid < 8 ∧ z'.avail_in = z.avail_in ∧
      (z'.avail_out ≠ 0 → st'.pending = 0 ∧ st'.pending_out = st'.pending_buf) ∧
      z'.avail_out.toNat ≤ z.avail_out.toNat ∧ owed st' + (z.avail_out.toNat - z'.avail_out.toNat) = owed st) := by
  obtain ⟨z, st, al, hz, hb, hst, hal, c⟩ := F.live
  obtain ⟨H', e, hv, hio, hset, P⟩ := flush_ok (DWork.of_inv F.inv) F.io F.set
  refine ⟨(), H', e, ?_⟩
  obtain ⟨len, z', st', hz', hst', hlen, hpend, hsteq, hav, hzeq, hadv, fr, -, -, hbv⟩ := P z b st hz hb hst
  have hO := ZlibNgF.Proof.TreesOwed.flush_pending_owed' (DWork.of_inv F.inv) F.io F.set H' e z b st z' st' hz hb hst
    hz' hst'
  have hzs : z'.state = some b := by rw [hzeq]; exact hb
  obtain ⟨z0, z4, ob, oo, k, h0, h4, e0, e4, ek⟩ := F.out
  obtain rfl : z = z4 := Option.some.inj (hz.symm.trans h4)
  have hdo : dOutputRanges h (some i) = [(z0.next_out, z0.avail_out.toNat)] := by simp [dOutputRanges, h0]
  have hk : StratKeeps st st' := by rw [hsteq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩
  refine ⟨⟨hv, hio, hset, ?_, ⟨z', hz', hzs⟩, F.blk0, ?_, ?_,
    F.inp.keep hz hz' (by rw [hzeq]) (by rw [hzeq]), ?_, ?_, fun st3 h3 => ?_⟩,
    z, st, z', st', hz, hst, hz', hst', hsteq, hbv, by rw [hzeq], fun ha => ?_, hO.1, hO.2⟩
  · obtain ⟨⟨-, -, -, -, -, -, ec, ex, -, -⟩, -⟩ := fr
    exact ⟨by rw [ec]; exact F.crc.1, by rw [ex]; exact F.crc.2⟩
  · refine dframe_trans F.frame (dframe_wmono fr ?_)
    rw [hdo]
    intro c' j hw w hm off he
    rw [List.mem_singleton] at hm; subst hm
    simp only [] at he
    rw [e4] at he
    injection he with he1 he2
    injection he1 with he1
    subst he1; subst he2
    have := hw _ (List.mem_singleton_self _) oo e0
    simp only [] at this
    omega
  · exact ⟨z0, z', ob, oo, k + len, h0, hz', e0, by rw [hadv ob (oo + k) e4]; rw [Nat.add_assoc], by omega⟩
  · obtain ⟨st0, h0', hw⟩ := F.win
    refine ⟨st0, h0', fun st3 hst3 => ?_⟩
    obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    rw [hsteq]; exact hw st hst
  · obtain ⟨st0, h0', hw⟩ := F.keeps
    refine ⟨st0, h0', fun st3 hst3 => ?_⟩
    obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    exact StratKeeps.trans (hw st hst) hk
  · obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans h3)
    rw [hsteq]; exact F.sym st hst
  · have hp0 : st'.pending = 0 := by
      have : len < z.avail_out.toNat := by
        have : z'.avail_out.toNat ≠ 0 := fun e' => ha (UInt32.toNat_inj.mp (by simpa using e'))
        omega
      apply UInt32.toNat_inj.mp; rw [hpend, UInt32.toNat_zero]; omega
    obtain ⟨i2, z2, b2, st2, al2, e2, hz2, hb2, hst2, -, c2⟩ := hv
    obtain rfl : i = i2 := Option.some.inj e2
    obtain rfl : z' = z2 := Option.some.inj (hz'.symm.trans hz2)
    obtain rfl : b = b2 := Option.some.inj (hzs.symm.trans hb2)
    obtain rfl : st' = st2 := Option.some.inj (hst'.symm.trans hst2)
    exact ⟨hp0, c2.pout hp0⟩

/-! ## The potential -/

/-- The potential of the call with flush `f` spent within `e`, from the entry heap `h` to `H` with the locals `la` /
`ss` written back (`DeflatePsi.PsiAccF`). -/
def QP (f : Int32) (e : Nat) (h : Heap) (i b : Nat) (la ss : UInt32) (H : Heap) : Prop :=
  ∀ z0 z st0 st, h.streams i = some z0 → H.streams i = some z → h.dstate b = some st0 → H.dstate b = some st →
    psiS f (FS st la ss) + (z0.avail_out.toNat - z.avail_out.toNat) ≤
      psiS f st0 + G * (z0.avail_in.toNat - z.avail_in.toNat) + e

theorem QP.mono {f : Int32} {e e' : Nat} {h H : Heap} {i b : Nat} {la ss : UInt32} (A : QP f e h i b la ss H)
    (he : e ≤ e') : QP f e' h i b la ss H := fun z0 z st0 st h0 h1 s0 s1 =>
  Nat.le_trans (A z0 z st0 st h0 h1 s0 s1) (by omega)

/-- `QP` at the entry. -/
theorem qp_entry (f : Int32) {h : Heap} {i b : Nat} {st : DeflateState} (hst : h.dstate b = some st) :
    QP f 0 h i b st.lookahead st.strstart h := by
  intro z0 z st0 st1 h0 h1 s0 s1
  rw [h0] at h1; obtain rfl := Option.some.inj h1
  rw [s0] at s1; obtain rfl := Option.some.inj s1
  rw [hst] at s0; obtain rfl := Option.some.inj s0
  simp

/-- `QP` over one step from `H` to `H'` under `QF` whose change of `psiS` (locals included), with the allowance `e`
before, is paid within `e'` after. -/
theorem qp_next {f : Int32} {e e' : Nat} {h H H' : Heap} {i b : Nat} {la ss la' ss' : UInt32} {z z' : ZStream}
    {st st' : DeflateState} (A : QP f e h i b la ss H) (F : QF h i b H)
    (hz : H.streams i = some z) (hst : H.dstate b = some st) (hz' : H'.streams i = some z')
    (hst' : H'.dstate b = some st') (ho : z'.avail_out.toNat ≤ z.avail_out.toNat)
    (hi : z'.avail_in.toNat ≤ z.avail_in.toNat)
    (S : psiS f (FS st' la' ss') + (z.avail_out.toNat - z'.avail_out.toNat) + e ≤
      psiS f (FS st la ss) + G * (z.avail_in.toNat - z'.avail_in.toNat) + e') : QP f e' h i b la' ss' H' := by
  intro z0 z2 st0 st2 h0 h2 s0 s2
  rw [hz'] at h2; obtain rfl := Option.some.inj h2
  rw [hst'] at s2; obtain rfl := Option.some.inj s2
  have a := A z0 z st0 st h0 hz s0 hst
  have m2 := F.inp.le h0 hz
  obtain ⟨z5, z4, ob, oo, k, h5, h4, -, -, ek⟩ := F.out
  obtain rfl := Option.some.inj (h5.symm.trans h0)
  obtain rfl := Option.some.inj (h4.symm.trans hz)
  rw [ZlibNgF.Proof.DeflatePsi.G_mul_split _ _ _ m2 hi]
  generalize G * (z5.avail_in.toNat - z4.avail_in.toNat) = X at *
  generalize G * (z4.avail_in.toNat - z'.avail_in.toNat) = Y at *
  omega

/-- `QP` with the locals those of the state gives `PsiPost` within `finSlack bs`. -/
theorem qp_post {f : Int32} {e : Nat} {h H : Heap} {i b : Nat} {la ss : UInt32} (F : QF h i b H)
    (A : QP f e h i b la ss H) (hls : ∀ st, H.dstate b = some st → st.lookahead = la ∧ st.strstart = ss)
    (bs : BlockState) (he : e ≤ finSlack bs) : PsiPost h (some i) f bs H := by
  intro i' b' e' hsb
  obtain rfl := Option.some.inj e'
  obtain ⟨z0, hz0, hb0⟩ := F.blk0
  obtain ⟨z1, ⟨i1, e1, hz1⟩, hb1⟩ := hsb
  obtain rfl := Option.some.inj e1
  obtain rfl : z0 = z1 := Option.some.inj (hz0.symm.trans hz1)
  obtain rfl : b = b' := Option.some.inj (hb0.symm.trans hb1)
  intro z2 z st0 st h0 h1 s0 s1
  have a := A z2 z st0 st h0 h1 s0 s1
  obtain ⟨e1, e2⟩ := hls st s1
  have : FS st la ss = st := by rw [← e1, ← e2]
  rw [this] at a
  omega

/-- `QP` does not read the bytes of the block. -/
theorem qp_bytes {f : Int32} {e : Nat} {h H0 : Heap} {i b : Nat} {la ss : UInt32} {z : ZStream} {st : DeflateState}
    {d d' : Array UInt8} (A : QP f e h i b la ss (SH H0 i z b st d)) : QP f e h i b la ss (SH H0 i z b st d') :=
  fun z0 z1 st0 st1 h0 h1 s0 s1 => by
    rw [SH_streams] at h1; rw [SH_dstate] at s1
    exact A z0 z1 st0 st1 h0 (by rw [SH_streams]; exact h1) s0 (by rw [SH_dstate]; exact s1)

/-- `QP` after the locals are written to the state. -/
theorem qp_wb {f : Int32} {e : Nat} {h H0 : Heap} {i b : Nat} {la ss : UInt32} {z : ZStream} {st : DeflateState}
    {d : Array UInt8} (A : QP f e h i b la ss (SH H0 i z b st d)) : QP f e h i b la ss (SH H0 i z b (FS st la ss) d) :=
  fun z0 z1 st0 st1 h0 h1 s0 s1 => by
    rw [SH_streams] at h1; rw [SH_dstate] at s1; obtain rfl := Option.some.inj s1
    exact A z0 z1 st0 st h0 (by rw [SH_streams]; exact h1) s0 (SH_dstate _ _ _ _ _ _)

/-- `psiS` over a change that moves `k` bytes from the lookahead to the window span (or not more), with `quickB`
raised by at most `q` and `owed` by `o` less the `out` bytes written. -/
theorem psiS_gen {f : Int32} {st st' : DeflateState} {k out q o : Nat}
    (e1 : st'.lookahead.toNat + k = st.lookahead.toNat) (hsp : span st' ≤ span st + k)
    (e4 : st'.sym_next = st.sym_next) (e5 : st'.match_available = st.match_available)
    (e6 : st'.status = st.status) (e7 : st'.wrap = st.wrap)
    (hq : quickB f st' ≤ quickB f st + q) (ho : owed st' + out ≤ owed st + o) :
    psiS f st' + out + 2 ^ 19 * k ≤ psiS f st + 6 * k + q + o := by
  unfold psiS content; rw [e4, e5, e6, e7]; omega

/-- The lookahead grows by at most the `n` input bytes taken: `psiS` grows by at most `(2^19 + 64) n`. -/
theorem psiS_read' {f : Int32} {st st' : DeflateState} (n : Nat)
    (e1 : st'.lookahead.toNat ≤ st.lookahead.toNat + n) (e2 : span st' ≤ span st)
    (e3 : st'.sym_next = st.sym_next) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) (e7 : st'.block_open = st.block_open)
    (e8 : owed st' = owed st) : psiS f st' ≤ psiS f st + (2 ^ 19 + 64) * n := by
  have hq := ZlibNgF.Proof.DeflatePsi.quickB_read_le (f := f) n e1 e7
  have hc : content st' ≤ content st + 2 ^ 19 * n := by
    unfold content; rw [e3, e4, e5, e6]; omega
  unfold psiS; rw [e8]; omega

/-- `QP` over a change of the state (and the block's bytes) that does not raise `psiS` with the locals. -/
theorem qp_state {f : Int32} {e : Nat} {h H0 : Heap} {i b : Nat} {la ss la' ss' : UInt32} {z : ZStream}
    {st st' : DeflateState} {d d' : Array UInt8} (A : QP f e h i b la ss (SH H0 i z b st d))
    (hle : psiS f (FS st' la' ss') ≤ psiS f (FS st la ss)) : QP f e h i b la' ss' (SH H0 i z b st' d') :=
  fun z0 z1 st0 st1 h0 h1 s0 s1 => by
    rw [SH_streams] at h1; rw [SH_dstate] at s1; obtain rfl := Option.some.inj s1
    have := A z0 z1 st0 st h0 (by rw [SH_streams]; exact h1) s0 (SH_dstate _ _ _ _ _ _)
    omega

/-- `quickB` with a block open is the same for states with the same `block_open`. -/
theorem quickB_open {f : Int32} {st st' : DeflateState} (h0 : st.block_open ≠ 0)
    (e : st'.block_open = st.block_open) : quickB f st' = quickB f st := by
  unfold quickB; rw [e, ite_eq_left h0, ite_eq_left h0]

/-! ## `fill_window` -/

/-- `fill_window` adds to the lookahead exactly the input it takes. -/
theorem fill_sum {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (hv : DInv H (some i))
    (hio : DStreamIO H (some i)) (hset : DBufsSet H (some i)) (hcrc : CrcGlobals H)
    (hz : H.streams i = some z) (hb : z.state = some b) (hst : H.dstate b = some st)
    (hla : st.lookahead.toNat < 262) {H' : Heap} (e : ZlibNg.Deflate.fill_window (some b) H = .ok ((), H')) :
    ∃ z' st', H'.streams i = some z' ∧ H'.dstate b = some st' ∧
      z'.avail_in.toNat + st'.lookahead.toNat = z.avail_in.toNat + st.lookahead.toNat := by
  have hio0 := hio
  obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, hin0, hout, hnb, hdj⟩ := hio0
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb.symm.trans hb2)
  obtain ⟨z3, ⟨i3, e3, hz3⟩, hnn, hni⟩ := hset
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, hal, c⟩ := hv
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  have hsts : H.dstates b = some st := dstates_of_dstate hst hd
  obtain ⟨wo, po, ho, pbo, HL0, hwo, -, -, -⟩ := ZlibNgF.Proof.FillFacts.hlay_of c hd
  have HL := ZlibNgF.Proof.FillFacts.HLay.of_bs HL0
  obtain ⟨-, w2, wsz, -, -, -, -⟩ := c.sizes
  obtain ⟨f, hf⟩ : ∃ f, st.insert_batch = .val f := ⟨_, c.fns.2⟩
  have C0 := ZlibNgF.Proof.FillFacts.wcore_of c
  have hfl : st.level ≠ 1 → f ≠ .insert_knuth_batch_head := fun hl e1 =>
    ZlibNgF.Proof.FillFacts.insertBatchOf_ne hl (by
      have e2 : st.insert_batch = .val (ZlibNgF.Proof.DeflateInv.insertBatchOf st.level) := c.fns.2
      rw [hf, e1] at e2; injection e2 with e3; exact e3.symm)
  have S := ZlibNgF.Proof.FillWindow.fill_window_SH (H := H) (i := i) (z := z) (b := b) (d := d) f hfl hb c.strm hf HL
    wsz hwo w2 C0 c.look hla (ZlibNgF.Proof.FillFacts.insrc_of hin0 (hdj _ (.inl rfl)).2 hni) (fun _ => hcrc.1)
  rw [ZlibNgF.Proof.DeflateReset.SH_self hz hsts hd] at S
  obtain ⟨_, h', e', z', st', d', rfl, -, -, -, -, -, -, -, -, -, sum, -⟩ := S
  rw [e] at e'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj e')
  exact ⟨z', st', SH_streams _ _ _ _ _ _, SH_dstate _ _ _ _ _ _, sum⟩

/-- Write the locals back (`strstart` at or past the state's, the same end of the lookahead) and call `fill_window`
(with `lookahead < MIN_LOOKAHEAD`): `QF` after, `fill_window`'s fields changed only, the lookahead not smaller, the
lookahead plus the input not grown, and the input dropped when the lookahead changed. -/
theorem qf_fill {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    {fl : Int32} {ep : Nat} (F : QF h i b (SH H0 i z b st d)) (A : QP fl ep h i b la ss (SH H0 i z b st d))
    (hss : st.strstart.toNat ≤ ss.toNat)
    (hsum : ss.toNat + la.toNat = st.strstart.toNat + st.lookahead.toNat) (hla : la.toNat < 262) :
    Sat (SH H0 i z b st d) (wrD (some b) fun s => { s with lookahead := la, strstart := ss }) (fun _ H1 =>
      Sat H1 (ZlibNg.Deflate.fill_window (some b)) (fun _ H2 => ∃ H3 z' st' d', H2 = SH H3 i z' b st' d' ∧
        QF h i b H2 ∧ ZlibNgF.Proof.WinInv.FWS (FS st la ss) st' ∧ la.toNat ≤ st'.lookahead.toNat ∧
        z'.avail_in.toNat + st'.lookahead.toNat ≤ z.avail_in.toNat + la.toNat ∧
        (st'.lookahead ≠ la → z'.avail_in.toNat < z.avail_in.toNat) ∧
        (262 ≤ st'.lookahead.toNat ∨ z'.avail_in = 0) ∧ QP fl ep h i b st'.lookahead st'.strstart H2 ∧
        (z'.avail_in.toNat < z.avail_in.toNat → ep ≤ 33 → QP fl 0 h i b st'.lookahead st'.strstart H2))) := by
  refine Sat.of_eq (wrD_SH _) ?_
  obtain ⟨z1, st1, al, hz1, hb, hst1, -, c⟩ := F.live
  obtain rfl : z = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  have F1 : QF h i b (SH H0 i z b (FS st la ss) d) := by
    refine qf_SH F (fun al' _ c' => ?_) rfl rfl (F.sym st (SH_dstate _ _ _ _ _ _)) (StratKeeps.refl _)
    exact DCore.of_heap (by rw [SH_bytes, SH_bytes]) (dcore_set c' ss la st.insert st.block_start
      (by have := c'.look; simp only [dview] at this ⊢; omega)
      (by have := c'.bstart; simp only [dview] at this ⊢; omega)
      (by have := UInt32.le_iff_toNat_le.mp c'.ins; simp only [dview] at this ⊢;
          exact UInt32.le_iff_toNat_le.mpr (by omega)) c'.bs_lo)
  obtain ⟨H2, e, FI⟩ := fill_io F1.inv F1.io F1.set F1.crc (SH_streams _ _ _ _ _ _) hb (SH_dstate _ _ _ _ _ _) hla
  refine ⟨(), H2, e, ?_⟩
  obtain ⟨z5, z', st5, st', d', hz5, hst5, rfl, zr, fws⟩ := FI.shape
  obtain rfl : z = z5 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz5)
  obtain rfl : FS st la ss = st5 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst5)
  obtain ⟨-, -, -, i6, z6, z7, b6, st6, st7, e6, hz6, hz7, hb6, hst6, hst7, -, -, hlt, hsum2, hspan, -, hend, -⟩ :=
    FI.post
  obtain rfl : i = i6 := Option.some.inj e6
  obtain rfl : z = z6 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz6)
  obtain rfl : z' = z7 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz7)
  obtain rfl : b = b6 := Option.some.inj (hb.symm.trans hb6)
  obtain rfl : FS st la ss = st6 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst6)
  obtain rfl : st' = st7 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst7)
  obtain ⟨z8, st8, hz8, hst8, hs8⟩ := fill_sum F1.inv F1.io F1.set F1.crc (SH_streams _ _ _ _ _ _) hb
    (SH_dstate _ _ _ _ _ _) hla e
  obtain rfl : z' = z8 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz8)
  obtain rfl : st' = st8 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst8)
  have hzs := ZlibNgF.Proof.FillWindow.ZR.state zr
  have zr0 := zr
  obtain ⟨hle, ⟨ni, ai, ti, ad, hze⟩, -⟩ := zr
  obtain ⟨fe, ms, pl, ss', bs', ins', sl, la', ih, hw', hste⟩ := fws
  have hK : StratKeeps (FS st la ss) st' := fill_keeps FI (SH_streams _ _ _ _ _ _) hb (SH_dstate _ _ _ _ _ _)
    (SH_dstate _ _ _ _ _ _)
  refine ⟨_, _, _, d', rfl, ⟨FI.inv, FI.io, FI.set, FI.crc, ⟨_, SH_streams _ _ _ _ _ _, hzs.trans hb⟩, F1.blk0,
      dframe_trans F1.frame (dframe_nil _ FI.frame), ?_,
      F1.inp.trans (ZlibNgF.Proof.FillFacts.inTail_of_zr (SH_streams _ _ _ _ _ _) (SH_streams _ _ _ _ _ _) zr0),
      ?_, ?_, fun st2 h2 => ?_⟩,
    ⟨fe, ms, pl, ss', bs', ins', sl, la', ih, hw', hste⟩, ?_, ?_, hlt, hend, ?_, fun hlt' he => ?_⟩
  · obtain ⟨z0, z4, ob, oo, k, h0, h4, e0, e4, ek⟩ := F1.out
    obtain rfl : z = z4 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans h4)
    exact ⟨z0, _, ob, oo, k, h0, SH_streams _ _ _ _ _ _, e0, by rw [hze]; exact e4, by rw [hze]; exact ek⟩
  · obtain ⟨st0, h0, hw⟩ := F1.win
    refine ⟨st0, h0, fun st2 h2 => ?_⟩
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    rw [hste]; exact hw (FS st la ss) (SH_dstate _ _ _ _ _ _)
  · obtain ⟨st0, h0, hw⟩ := F1.keeps
    refine ⟨st0, h0, fun st2 h2 => ?_⟩
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    exact StratKeeps.trans (hw (FS st la ss) (SH_dstate _ _ _ _ _ _)) hK
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    rw [hste]; exact F1.sym (FS st la ss) (SH_dstate _ _ _ _ _ _)
  · have : z'.avail_in.toNat ≤ z.avail_in.toNat := hle
    simp only at hs8; omega
  · simp only at hsum2; omega
  all_goals
    have hle' : z'.avail_in.toNat ≤ z.avail_in.toNat := hle
    have ea : z'.avail_out = z.avail_out := by rw [hze]
    have hk' : st'.sym_next = (FS st la ss).sym_next ∧ st'.match_available = (FS st la ss).match_available ∧
        st'.status = (FS st la ss).status ∧ st'.wrap = (FS st la ss).wrap ∧
        st'.block_open = (FS st la ss).block_open ∧ owed st' = owed (FS st la ss) := by
      rw [hste]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have q := psiS_read' (f := fl) (st := FS st la ss) (st' := st') (z.avail_in.toNat - z'.avail_in.toNat)
      (by simp only at hs8 ⊢; omega) (by unfold span; simp only at hspan ⊢; omega)
      hk'.1 hk'.2.1 hk'.2.2.1 hk'.2.2.2.1 hk'.2.2.2.2.1 hk'.2.2.2.2.2
    refine qp_next A F (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) (SH_streams _ _ _ _ _ _)
      (SH_dstate _ _ _ _ _ _) (by rw [ea]; exact Nat.le_refl _) hle' ?_
    rw [ea, Nat.sub_self, FS_self]
    have g : (2 ^ 19 + 64) * (z.avail_in.toNat - z'.avail_in.toNat) ≤ G * (z.avail_in.toNat - z'.avail_in.toNat) :=
      Nat.mul_le_mul_right _ (by decide)
    first
    | omega
    | have h1 : 1 ≤ z.avail_in.toNat - z'.avail_in.toNat := by omega
      have g2 : (2 ^ 19 + 64) * (z.avail_in.toNat - z'.avail_in.toNat) + 33 ≤
          G * (z.avail_in.toNat - z'.avail_in.toNat) := by
        generalize z.avail_in.toNat - z'.avail_in.toNat = n at h1 ⊢
        show (2 ^ 19 + 64) * n + 33 ≤ 2 ^ 20 * n
        omega
      omega

/-! ## Exit -/

/-- The exit facts of `deflate_quick` with `Z_FIXED` returning `bs`, on the state after: no pending bytes after
`block_done` / `finish_done`, no lookahead after `finish_started` / `finish_done`, and 8 or more bits only with
lookahead. -/
def QExit (bs : BlockState) (st : DeflateState) : Prop :=
  (bs = .block_done ∨ bs = .finish_done → st.pending = 0) ∧
    (bs = .finish_started ∨ bs = .finish_done → st.lookahead = 0) ∧ (8 ≤ st.bi_valid → st.lookahead ≠ 0)

/-- `StratPost` from `QF` and the exit facts, for a call entered at level 1 with `Z_FIXED`. -/
theorem qf_post {h H : Heap} {i b : Nat} (F : QF h i b H) (flush : Int32) (bs : BlockState)
    (hx : ExitIO H i flush bs) (hE : ∀ st0, h.dstate b = some st0 → st0.level = 1 ∧ st0.strategy = Z_FIXED)
    (hs : ∀ st, H.dstate b = some st → QExit bs st) (hψ : PsiPost h (some i) flush bs H) :
    StratPost h (some i) flush bs H := by
  obtain ⟨z, st, al, hz, hb, hst, -, c⟩ := F.live
  obtain ⟨z0, hz0, hb0⟩ := F.blk0
  have hsi : stateIds h (some i) = [b] := by simp [stateIds, hz0, hb0]
  refine ⟨F.inv, F.io, F.set, ?_, fun i' e => by obtain rfl := Option.some.inj e; exact F.out,
    stateBlock_keep F.blk0 F.blk, fun _ e => by obtain rfl := Option.some.inj e; exact F.inp, hx.1, hx.2.1,
    fun hf e z0 z' _ hz' hn0 => .inr (lt_of_out0 (hx.2.2.1 hf e z' hz') hn0),
    fun e => ⟨b, st, ⟨i, z, rfl, hz, hb, hst⟩, ((hs st hst).1 e)⟩, ?_, hψ, exitIO_bdpost hx⟩
  · rw [hsi]; exact F.frame
  · rintro b1 st1 st' ⟨i1, z1, e1, hz1, hb1, hst1⟩ ⟨i', z', e, hz', hb', hst'⟩
    obtain rfl : i = i' := Option.some.inj e
    obtain rfl : i = i1 := Option.some.inj e1
    obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
    obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb')
    obtain rfl : st = st' := Option.some.inj (hst.symm.trans hst')
    obtain ⟨st0, h0, hk⟩ := F.keeps
    obtain rfl : st0 = st1 := Option.some.inj (h0.symm.trans hst1)
    have K := hk st hst
    obtain ⟨hl1, hfx⟩ := hE st0 h0
    have hlv : st.level = 1 := K.2.2.2.2.1.trans hl1
    have hsf : st.strategy = Z_FIXED := K.2.2.2.2.2.1.trans hfx
    have hs0 := F.sym st hst
    obtain ⟨x1, x2, x3⟩ := hs st hst
    have hse : st.sym_next < st.sym_end := by
      obtain ⟨-, -, -, hl2, -, -, hse⟩ := c.sizes
      simp only [dview] at hse hl2
      rw [hs0]; apply UInt32.lt_iff_toNat_lt.mpr; simp; omega
    refine ⟨⟨hse, fun e0 => absurd (e0.symm.trans hlv) (by decide), fun _ _ => hs0, fun _ => hs0,
      fun e8 => ⟨hlv, hsf, x3 e8⟩⟩, K, fun _ _ => hs0, fun e => ⟨hs0, x2 e⟩, fun _ => hs0, fun L => ?_⟩
    have N := K.lazy L fun ht => by
      have h7 := ht.1; rw [hl1] at h7; exact absurd h7 (by decide)
    exact ⟨N.1, fun _ => N.2⟩

end ZlibNgF.Proof.QuickS
