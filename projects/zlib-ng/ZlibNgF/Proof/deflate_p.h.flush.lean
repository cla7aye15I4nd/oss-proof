import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Proof.«trees_emit.h.bits»
import ZlibNgF.Proof.«inflate.c.dict»
import ZlibNgF.Proof.«deflate.c.reset»

/-!
# `flush_pending` (`ZlibNgF`)

`flush_pending` (= `flush_pending_inline`) on a stream in the working state (`DWork`, up to 63 bits in `bi_buf`)
whose `next_out` has `avail_out` writable bytes outside the library's block: `zng_tr_flush_bits` moves the complete
bytes of `bi_buf` to `pending_buf + pending`, then `len = min(pending, avail_out)` bytes go from `pending_out` to
`next_out`. No fault; the invariant holds after (fewer than 8 bits are left); only the stream record (`next_out`,
`avail_out`, `total_out`), the state (`pending`, `pending_out`, `bi_buf`, `bi_valid`), the bytes of `pending_buf`
and the first `len` output bytes change (`FlushPost`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateFlush
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateBits
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get memcpy_heap)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- `H` with stream `i` holding `z`, block `b` holding the bytes `d` and the state `st`, and block `ob` holding the
bytes `X` (the output block, after a `memcpy` into it). -/
def OH (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (ob : Nat)
    (X : Array UInt8) : Heap :=
  { H with
    streams := upd H.streams i (some z)
    dstates := upd H.dstates b (some st)
    bytes := upd (upd H.bytes b (some d)) ob (some X) }

section OH
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {ob : Nat}
  {X : Array UInt8}

theorem OH_bytes_b (hob : ob ≠ b) : (OH H i z b st d ob X).bytes b = some d := by
  simp [OH, upd_ne _ _ _ _ (Ne.symm hob)]

theorem OH_bytes_ob : (OH H i z b st d ob X).bytes ob = some X := by simp [OH]

theorem OH_dstate (hob : ob ≠ b) : (OH H i z b st d ob X).dstate b = some st := by
  simp [Heap.dstate, OH_bytes_b hob]; simp [OH]

theorem ldDState_OH (hob : ob ≠ b) : ldDState (some b) (OH H i z b st d ob X) = .ok (st, OH H i z b st d ob X) := by
  simp [ldDState, OH_dstate hob]

theorem rdD_OH (hob : ob ≠ b) {α : Type} (f : DeflateState → α) :
    rdD (some b) f (OH H i z b st d ob X) = .ok (f st, OH H i z b st d ob X) := by
  simp [rdD, bind_app, ldDState_OH hob]

theorem wrD_OH (hob : ob ≠ b) (f : DeflateState → DeflateState) :
    wrD (some b) f (OH H i z b st d ob X) = .ok ((), OH H i z b (f st) d ob X) := by
  simp only [wrD, stDState, bind_app, ldDState_OH hob, OH_dstate hob]
  simp [OH, upd_upd]

theorem wrZ_OH (f : ZStream → ZStream) :
    wrZ (some i) f (OH H i z b st d ob X) = .ok ((), OH H i (f z) b st d ob X) := by
  simp [wrZ, stStream, ldStream, bind_app, OH, upd_upd]

theorem rdZ_OH {α : Type} (f : ZStream → α) :
    rdZ (some i) f (OH H i z b st d ob X) = .ok (f z, OH H i z b st d ob X) := by
  simp [rdZ, ldStream, bind_app, OH]

theorem addb_OH (hob : ob ≠ b) {off : Nat} (k : Nat) (hk : off + k ≤ d.size) :
    Ptr.add (Ptr.ref (BRef.heap b) off) (k : Int) (OH H i z b st d ob X) =
      .ok (.ref (.heap b) (off + k), OH H i z b st d ob X) := by
  have : off ≤ d.size := by omega
  simp only [Ptr.add, space_get_heap, OH_bytes_b hob, this, show (0 : Int) ≤ (off : Int) + (k : Int) by omega,
    show ((off : Int) + (k : Int)) ≤ (d.size : Int) by omega, and_self, ↓reduceIte]
  rfl

theorem addo_OH {off : Nat} (k : Nat) (hk : off + k ≤ X.size) :
    Ptr.add (Ptr.ref (BRef.heap ob) off) (k : Int) (OH H i z b st d ob X) =
      .ok (.ref (.heap ob) (off + k), OH H i z b st d ob X) := by
  have : off ≤ X.size := by omega
  simp only [Ptr.add, space_get_heap, OH_bytes_ob, this, show (0 : Int) ≤ (off : Int) + (k : Int) by omega,
    show ((off : Int) + (k : Int)) ≤ (X.size : Int) by omega, and_self, ↓reduceIte]
  rfl

/-- The `memcpy` of `flush_pending`: from block `b` into the output block `ob`. -/
theorem memcpy_SH {ad : Array UInt8} (hob : ob ≠ b) (had : H.bytes ob = some ad) {oo poo n : Nat}
    (h1 : oo + n ≤ ad.size) (h2 : poo + n ≤ d.size) :
    Ptr.memcpy (Ptr.ref (BRef.heap ob) oo) (Ptr.ref (BRef.heap b) poo) n (SH H i z b st d) =
      .ok ((), OH H i z b st d ob (copyFold d oo poo (List.range' 0 n) ad)) := by
  have hb' : (SH H i z b st d).bytes ob = some ad := by simp [SH, upd_ne _ _ _ _ hob, had]
  have hs : Space.get (SH H i z b st d) (BRef.heap b) = some d := by simp [space_get_heap]
  rw [memcpy_heap hb' hs (fun e => hob (by injection e with e; exact e.symm)) h1 h2]
  rfl

end OH

/-- The heap after `flush_pending` on an `SH` heap (`FBPost` followed by the copy of `len` bytes). -/
def FP (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (ob oo : Nat)
    (ad : Array UInt8) (pbo poo : Nat) (H' : Heap) : Prop :=
  ∃ (np : UInt32) (bb : UInt64) (bv : Int32) (d1 : Array UInt8) (len : Nat) (z' : ZStream) (st' : DeflateState),
    H' = OH H i z' b st' d1 ob (copyFold d1 oo poo (List.range' 0 len) ad) ∧
    WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d1 ∧ 0 ≤ bv.toInt ∧ bv.toInt < 8 ∧
    np.toNat = st.pending.toNat + st.bi_valid.toInt.toNat / 8 ∧ len = min np.toNat z.avail_out.toNat ∧
    st' = { st with
      pending := st'.pending
      pending_out := st'.pending_out
      bi_buf := bb
      bi_valid := bv } ∧
    st'.pending.toNat = np.toNat - len ∧
    (st'.pending = 0 → st'.pending_out = st.pending_buf) ∧
    (st'.pending ≠ 0 → st'.pending_out = .val (.ref (.heap b) (poo + len))) ∧
    z' = { z with
      next_out := z'.next_out
      avail_out := z'.avail_out
      total_out := z'.total_out } ∧
    z'.next_out = .ref (.heap ob) (oo + len) ∧ z'.avail_out.toNat = z.avail_out.toNat - len

theorem OH_self {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d ad : Array UInt8} {ob : Nat}
    (hob : ob ≠ b) (had : H.bytes ob = some ad) : OH H i z b st d ob ad = SH H i z b st d := by
  have : upd H.bytes b (some d) ob = some ad := by rw [upd_ne _ _ _ _ hob]; exact had
  simp only [OH, SH, ZlibNgF.Proof.DeflateReset.upd_self _ _ _ this]

theorem flush_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    {ob oo : Nat} {ad : Array UInt8} {pbo poo lb : Nat}
    (hzb : z.state = some b) (hob : ob ≠ b) (had : H.bytes ob = some ad)
    (hno : z.next_out = .ref (.heap ob) oo) (hoo : oo + z.avail_out.toNat ≤ ad.size)
    (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hpo : st.pending_out = .val (.ref (.heap b) poo))
    (hle : pbo ≤ poo) (hroom : poo - pbo + st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ 4 * lb + 9)
    (hd : pbo + 4 * lb + 64 ≤ d.size) (hlb : lb ≤ 32768)
    (h0 : 0 ≤ st.bi_valid.toInt) (h64 : st.bi_valid.toInt < 64)
    (hpout : st.pending = 0 → st.pending_out = st.pending_buf) :
    Sat (SH H i z b st d) (ZlibNg.DeflateP.flush_pending (some i))
      (fun _ H' => FP H i z b st d ob oo ad pbo poo H') := by
  unfold ZlibNg.DeflateP.flush_pending ZlibNg.DeflateP.flush_pending_inline
  refine Sat.bind (Sat.of_eq (by simp only [dstateOf]; exact rdZ_SH _) ?_); try dsimp only
  rw [hzb]
  refine Sat.bind (Sat.mono (flush_bits_SH (pbo := pbo) hpb h0 (by omega) (by omega) (by omega)) ?_)
  rintro _ _ ⟨d1, bb, bv, np, rfl, w1, hb0, hb8, hnp⟩
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  refine Sat.bind (Sat.of_eq ldStream_SH ?_); try dsimp only
  have hnp' : np.toNat = st.pending.toNat + st.bi_valid.toInt.toNat / 8 := by omega
  have hd1 : d1.size = d.size := w1.1
  obtain ⟨L, hL, hLn⟩ : ∃ L : UInt32, (if np > z.avail_out then z.avail_out else np) = L ∧
      L.toNat = min np.toNat z.avail_out.toNat := by
    refine ⟨_, rfl, ?_⟩
    split
    · rename_i hc; have := UInt32.lt_iff_toNat_lt.mp hc; omega
    · rename_i hc; have := UInt32.not_lt.mp hc; have := UInt32.le_iff_toNat_le.mp this; omega
  rw [hL]
  by_cases hL0 : L = 0
  · simp only [hL0, beq_self_eq_true, ↓reduceIte]
    refine Sat.pure ⟨np, bb, bv, d1, 0, z, { st with pending := np, bi_buf := bb, bi_valid := bv }, ?_, w1,
      hb0, hb8, hnp', by rw [← hLn, hL0]; rfl, rfl, by simp, fun hz => ?_, fun _ => by simp [hpo], by simp,
      by simp [hno], by simp⟩
    · rw [show copyFold d1 oo poo (List.range' 0 0) ad = ad from rfl, OH_self hob had]
    · simp only [] at hz ⊢
      have h0' : np.toNat = 0 := by rw [hz]; rfl
      exact hpout (UInt32.toNat_inj.mp (by rw [show (0 : UInt32).toNat = 0 from rfl]; omega))
  · have hLb : (L == 0) = false := by simpa using hL0
    simp only [hLb, Bool.false_eq_true, ↓reduceIte]
    have hL1 : L.toNat ≠ 0 := fun e => hL0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
    simp only [hpo, Ival.get, pure_bind_M, hno]
    have hX := copyFold_size d1 oo poo (List.range' 0 L.toNat) ad
    refine Sat.bind (Sat.of_eq (memcpy_SH hob had (by omega) (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (addo_OH _ (by omega)) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrZ_OH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (addb_OH hob _ (by omega)) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_OH hob _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrZ_OH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrZ_OH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_OH hob _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (ldDState_OH hob) ?_); try dsimp only
    have hsub : (np - L).toNat = np.toNat - L.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    have hav : (z.avail_out - L).toNat = z.avail_out.toNat - L.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    split
    · rename_i hz
      refine Sat.of_eq (wrD_OH hob _) ⟨np, bb, bv, d1, L.toNat, _, _, rfl, w1, hb0, hb8, hnp', hLn, rfl, ?_,
        fun _ => rfl, fun hc => absurd (by simpa using hz) hc, rfl, rfl, by simpa using hav⟩
      simpa using hsub
    · rename_i hz
      refine Sat.pure ⟨np, bb, bv, d1, L.toNat, _, _, rfl, w1, hb0, hb8, hnp', hLn, rfl, ?_,
        fun hc => absurd (by simpa using hc) hz, fun _ => rfl, rfl, rfl, by simpa using hav⟩
      simpa using hsub

/-- `h'` differs from `h` in the bytes only within block `b` and the range `[oo, oo + n)` of block `ob` (sizes
kept), and keeps the constants and the headers. -/
def OutOnly (h h' : Heap) (b ob oo n : Nat) : Prop :=
  h'.consts = h.consts ∧ h'.gzheaders = h.gzheaders ∧
  ∀ c, c ≠ b → ∀ data, h.bytes c = some data → ∃ data', h'.bytes c = some data' ∧ data'.size = data.size ∧
    ∀ j, (c = ob → j < oo ∨ oo + n ≤ j) → data'[j]! = data[j]!

/-- What `flush_pending` leaves (see the module comment): `len = min(pending + bi_valid / 8, avail_out)` bytes
moved, and fewer than 8 bits in `bi_buf` (`zng_tr_flush_bits`). -/
def FlushPost (h h' : Heap) (i b : Nat) (z : ZStream) (st : DeflateState) : Prop :=
  ∃ (len : Nat) (z' : ZStream) (st' : DeflateState), h'.streams i = some z' ∧ h'.dstate b = some st' ∧
    len = min (st.pending.toNat + st.bi_valid.toInt.toNat / 8) z.avail_out.toNat ∧
    st'.pending.toNat = st.pending.toNat + st.bi_valid.toInt.toNat / 8 - len ∧
    st' = { st with
      pending := st'.pending
      pending_out := st'.pending_out
      bi_buf := st'.bi_buf
      bi_valid := st'.bi_valid } ∧
    z'.avail_out.toNat = z.avail_out.toNat - len ∧
    z' = { z with
      next_out := z'.next_out
      avail_out := z'.avail_out
      total_out := z'.total_out } ∧
    (∀ ob off, z.next_out = .ref (.heap ob) off → z'.next_out = .ref (.heap ob) (off + len)) ∧
    DFrame h h' [i] [b] [] [(z.next_out, len)] ∧
    (∀ ob oo, z.next_out = .ref (.heap ob) oo → OutOnly h h' b ob oo len) ∧
    (∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) → PbufOnly h h' b pbo (4 * st.lit_bufsize.toNat + 9)) ∧
    st'.bi_valid < 8

/-- The frame of `OH`: stream `i`, block `b`, and the first `n` bytes from offset `oo` of block `ob`. -/
theorem dframe_OH {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d ad : Array UInt8}
    {ob oo n : Nat} (hob : ob ≠ b) (had : h.bytes ob = some ad) (src : Array UInt8) (os : Nat) :
    DFrame h (OH h i z b st d ob (copyFold src oo os (List.range' 0 n) ad)) [i] [b] []
      [(.ref (.heap ob) oo, n)] := by
  refine ⟨⟨fun j hj => ?_, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun c _ hc data hdc => ?_, fun c _ hc hn => ?_,
    rfl, rfl, rfl, rfl, Nat.le_refl _⟩, fun c _ hc => ⟨?_, rfl⟩⟩
  · simp only [OH]; exact upd_ne _ _ _ _ (by simpa using hj)
  · have hcb : c ≠ b := by simpa using hc
    by_cases hco : c = ob
    · subst hco
      rw [had] at hdc; cases hdc
      refine ⟨_, OH_bytes_ob, copyFold_size _ _ _ _ _, fun j _ hw => ?_⟩
      have hj := hw _ (List.mem_singleton_self _) oo rfl
      exact copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'_1] at hx; omega)
    · refine ⟨data, ?_, rfl, fun _ _ _ => rfl⟩
      simp only [OH]; rw [upd_ne _ _ _ _ hco, upd_ne _ _ _ _ hcb]; exact hdc
  · have hcb : c ≠ b := by simpa using hc
    have hco : c ≠ ob := fun e => by subst e; rw [had] at hn; cases hn
    simp only [OH]; rw [upd_ne _ _ _ _ hco, upd_ne _ _ _ _ hcb]; exact hn
  · simp only [OH]; exact upd_ne _ _ _ _ (by simpa using hc)

/-- `flush_pending` on a stream in the working state, with `avail_out` writable output bytes outside the library's
block: no fault, the invariant after, and `FlushPost`. -/
theorem flush_work {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (hw : DWork h (some i))
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st)
    (hout : WriteSlice h z.next_out z.avail_out.toNat) (hnb : NotInBlock b z.next_out) :
    ∃ h', C.run (ZlibNg.DeflateP.flush_pending (some i)) h = .ok ((), h') ∧ DInv h' (some i) ∧
      FlushPost h h' i b z st := by
  obtain ⟨i', z0, b0, st0, al, e0, hz0, hb0, hst0, hal, v0, v64, c, R1, R2⟩ := hw
  obtain rfl : i = i' := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨-, -, -, l1, l2, -, -⟩ := c.sizes
  obtain ⟨d, wo, po, ho, pbo, hd, hwo, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, -⟩ := c.lay
  simp only [dview] at l1 l2 hwo hp hh hpb h1 h2 h3 h4 hsb hpo hpoo
  obtain ⟨pbo1, poo1, hp1, ho1, hq1⟩ := R1
  rw [hpb] at hp1; rw [hpo] at ho1
  obtain rfl : pbo = pbo1 := by injection hp1 with e1; injection e1
  obtain rfl : poo = poo1 := by injection ho1 with e1; injection e1
  obtain ⟨ob, oo, ad, hno, had, hoo⟩ := hout
  have hob : ob ≠ b := fun e => hnb oo (by rw [hno, e])
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  have hsts : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  have v0' : 0 ≤ st.bi_valid.toInt := by have := Int32.le_iff_toInt_le.mp v0; simpa using this
  have v64' : st.bi_valid.toInt < 64 := by have := Int32.lt_iff_toInt_lt.mp v64; simpa using this
  have hpout : st.pending = 0 → st.pending_out = st.pending_buf := c.pout
  have S := flush_SH (H := h) (i := i) (d := d) (lb := st.lit_bufsize.toNat) hb hob had hno hoo hpb hpo hpoo hq1 h4 l2
    v0' v64' hpout
  rw [ZlibNgF.Proof.DeflateReset.SH_self hz hsts hd] at S
  obtain ⟨r, h', e, np, bb, bv, d1, L, z', st', rfl, w1, hb0', hb8', hnp, hL, hst', hpn, hpz, hpnz, hz', hno', hav⟩ := S
  obtain ⟨P, Q, rfl⟩ : ∃ P Q, st' = { st with pending := P, pending_out := Q, bi_buf := bb, bi_valid := bv } :=
    ⟨_, _, hst'⟩
  obtain ⟨no, av, tt, rfl⟩ : ∃ no av tt, z' = { z with next_out := no, avail_out := av, total_out := tt } :=
    ⟨_, _, _, hz'⟩
  simp only [] at hpn hpz hpnz hno' hav
  have hd1 : d1.size = d.size := w1.1
  have hnpb : np.toNat ≤ poo - pbo + np.toNat := Nat.le_add_left _ _
  -- the bytes at `sym_buf` stay while symbols wait
  have hsymb : st.sym_next ≠ 0 → poo - pbo + np.toNat ≤ st.lit_bufsize.toNat + 8 := fun hn => by
    obtain ⟨pbo2, poo2, hp2, ho2, hq2⟩ := R2 hn
    rw [hpb] at hp2; rw [hpo] at ho2
    obtain rfl : pbo = pbo2 := by injection hp2 with e1; injection e1
    obtain rfl : poo = poo2 := by injection ho2 with e1; injection e1
    omega
  have hLle : L ≤ np.toNat := by omega
  refine ⟨_, e, ⟨i, { z with next_out := no, avail_out := av, total_out := tt }, b,
    { st with pending := P, pending_out := Q, bi_buf := bb, bi_valid := bv }, al, rfl, by simp [OH], hb,
    OH_dstate hob, by simp only [Heap.dallocsOf, OH_bytes_b hob]; exact hda, ?_⟩, ?_⟩
  · obtain ⟨ho', d', hd', hh', hho'⟩ := c.head
    obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
    exact {
      zalloc := c.zalloc
      zfree := c.zfree
      strm := c.strm
      alloc_bufs := c.alloc_bufs
      al_state := c.al_state
      al_zfree := c.al_zfree
      al_buf := c.al_buf
      status_lo := c.status_lo
      status_hi := c.status_hi
      wrap := c.wrap
      gzhead := c.gzhead
      w_size := c.w_size
      pbuf := c.pbuf
      head := ⟨ho', d1, OH_bytes_b hob, hh', by rw [hd1]; exact hho'⟩
      level := c.level
      trees := c.trees
      sizes := c.sizes
      lay := by
        refine ⟨d1, wo, po, ho, pbo, OH_bytes_b hob, hwo, hp, hh, hpb, h1, h2, h3, by rw [hd1]; exact h4, hsb, ?_⟩
        by_cases hP : P = 0
        · refine ⟨pbo, by simp only [dview]; rw [hpz hP, hpb], Nat.le_refl _, ?_⟩
          simp only [dview, hP]
          have h0' : (0 : UInt32).toNat = 0 := rfl
          omega
        · refine ⟨poo + L, by simp only [dview]; rw [hpnz hP], by omega, ?_⟩
          simp only [dview]; omega
      pout := fun hP => by simp only [dview] at hP ⊢; rw [hpz hP]
      syms := c.syms
      bits := ⟨Int32.le_iff_toInt_le.mpr (by rw [show (0 : Int32).toInt = 0 from rfl]; exact hb0'),
        Int32.lt_iff_toInt_lt.mpr (by
          rw [show (64 : Int32).toInt = 64 from rfl]; exact Int.lt_trans hb8' (by decide))⟩
      look := c.look
      strategy := c.strategy
      fns := c.fns
      symv := by
        obtain ⟨d0, sbo, hd0, hs0, hv0⟩ := c.symv
        obtain rfl : d = d0 := Option.some.inj (hd.symm.trans hd0)
        simp only [dview] at hs0 hv0
        rw [hsb] at hs0
        obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hs0 with e1; injection e1
        refine ⟨d1, _, OH_bytes_b hob, hsb, hv0.of_eq fun j hj => ?_⟩
        have hn : st.sym_next ≠ 0 := fun e => by simp [e] at hj
        have := hsymb hn
        exact w1.2 _ (Or.inr (by omega))
      psym := fun hn => by
        simp only [dview] at hn ⊢
        have := hsymb hn
        by_cases hP : P = 0
        · refine ⟨pbo, pbo, hpb, by rw [hpz hP, hpb], ?_⟩
          rw [hP]
          have h0' : (0 : UInt32).toNat = 0 := rfl
          omega
        · exact ⟨pbo, poo + L, hpb, hpnz hP, by omega⟩
      hdr := c.hdr
      bstart := c.bstart
      ins := c.ins
      wpow := c.wpow
      lmod := c.lmod
      lpow := c.lpow
      scratch := c.scratch
      blk := c.blk
      fe_mod := c.fe_mod
      fe_hi := c.fe_hi
      bs_lo := c.bs_lo
      descs := c.descs }
  · refine ⟨L, { z with next_out := no, avail_out := av, total_out := tt },
      { st with pending := P, pending_out := Q, bi_buf := bb, bi_valid := bv }, by simp [OH], OH_dstate hob,
      by rw [hL, hnp], by simp only []; omega, rfl, hav, rfl,
      fun ob' off' h' => ?_, by rw [hno]; exact dframe_OH hob had d1 poo, fun ob' oo' h' => ?_, fun pbo' hpb' => ?_,
      Int32.lt_iff_toInt_lt.mpr (by rw [show (8 : Int32).toInt = 8 from rfl]; exact hb8')⟩
    · rw [hno] at h'
      injection h' with e1 e2; injection e1 with e1
      subst e1; subst e2; exact hno'
    · rw [hno] at h'
      injection h' with e1 e2; injection e1 with e1
      subst e1; subst e2
      refine ⟨rfl, rfl, fun c hcb data hdc => ?_⟩
      by_cases hco : c = ob
      · subst hco
        rw [had] at hdc; cases hdc
        refine ⟨_, OH_bytes_ob, copyFold_size _ _ _ _ _, fun j hj => ?_⟩
        have hj' := hj rfl
        exact copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'_1] at hx; omega)
      · refine ⟨data, ?_, rfl, fun _ _ => rfl⟩
        simp only [OH]; rw [upd_ne _ _ _ _ hco, upd_ne _ _ _ _ hcb]; exact hdc
    · rw [hpb] at hpb'
      obtain rfl : pbo = pbo' := by injection hpb' with e1; injection e1
      exact ⟨d, d1, hd, OH_bytes_b hob, hd1, fun j hj => w1.2 j (by omega)⟩

/-! ## The stream's buffers after `flush_pending` -/

theorem get_out {h h' : Heap} {b ob oo n : Nat} (O : OutOnly h h' b ob oo n) {r : BRef} (hr : r ≠ .heap b)
    {data : Array UInt8} (hg : Space.get h r = some data) :
    ∃ data', Space.get h' r = some data' ∧ data'.size = data.size ∧
      ∀ j, (r = .heap ob → j < oo ∨ oo + n ≤ j) → data'[j]! = data[j]! := by
  obtain ⟨hc, -, hb⟩ := O
  cases r with
  | heap c =>
    obtain ⟨data', h1, h2, h3⟩ := hb c (fun e => hr (by rw [e])) data hg
    exact ⟨data', h1, h2, fun j hj => h3 j (fun e => hj (by rw [e]))⟩
  | const c =>
    refine ⟨data, ?_, rfl, fun _ _ => rfl⟩
    show h'.consts c = some data
    rw [hc]; exact hg
  | str k => exact ⟨data, hg, rfl, fun _ _ => rfl⟩

/-- A range of `[p, p + m)` disjoint from `[oo, oo + n)` of block `ob`: a byte of it is outside. -/
theorem disj_out {r : BRef} {off m ob oo n : Nat} (hd : Disjoint (.ref (.heap ob) oo) n (.ref r off) m) {j : Nat}
    (hj : off ≤ j ∧ j < off + m) : r = .heap ob → j < oo ∨ oo + n ≤ j := by
  intro e; subst e
  rcases hd with hne | h1 | h2
  · exact absurd rfl hne
  · omega
  · omega

theorem disj_mono {p : BPtr} {n n' : Nat} {q : BPtr} {m m' : Nat} (hd : Disjoint p n q m) (hn : n' ≤ n)
    (hm : m' ≤ m) : Disjoint p n' q m' := by
  match p, q, hd with
  | .ref _ _, .ref _ _, .inl hne => exact .inl hne
  | .ref _ _, .ref _ _, .inr (.inl h) => exact .inr (.inl (by omega))
  | .ref _ _, .ref _ _, .inr (.inr h) => exact .inr (.inr (by omega))
  | .null, _, _ => trivial
  | .ref _ _, .null, _ => trivial

theorem readSlice_out {h h' : Heap} {b ob oo n : Nat} (O : OutOnly h h' b ob oo n) {p : BPtr} {m : Nat}
    (hs : ReadSlice h p m) (hnb : NotInBlock b p) : ReadSlice h' p m := by
  obtain ⟨r, off, data, rfl, hg, hle⟩ := hs
  obtain ⟨data', h1, h2, -⟩ := get_out O (fun e => hnb off (by rw [e])) hg
  exact ⟨r, off, data', rfl, h1, by omega⟩

theorem nullOrRead_out {h h' : Heap} {b ob oo n : Nat} (O : OutOnly h h' b ob oo n) {p : BPtr} {m : Nat}
    (hs : NullOrRead h p m) (hnb : NotInBlock b p) : NullOrRead h' p m :=
  hs.imp id (fun hs => readSlice_out O hs hnb)

theorem cstr_out {h h' : Heap} {b ob oo n : Nat} (O : OutOnly h h' b ob oo n) {p : BPtr} {m : Nat}
    (hs : CStringLen h p m) (hnb : NotInBlock b p) (hd : Disjoint (.ref (.heap ob) oo) n p (m + 1)) :
    CStringLen h' p m := by
  obtain ⟨r, off, data, rfl, hg, hle, h0, hnz⟩ := hs
  obtain ⟨data', h1, h2, h3⟩ := get_out O (fun e => hnb off (by rw [e])) hg
  refine ⟨r, off, data', rfl, h1, by omega, ?_, fun k hk => ?_⟩
  · rw [h3 _ (disj_out hd (by omega))]; exact h0
  · rw [h3 _ (disj_out hd (by omega))]; exact hnz k hk

theorem cstr_unique {h : Heap} {p : BPtr} {m m' : Nat} (h1 : CStringLen h p m) (h2 : CStringLen h p m') :
    m = m' := by
  obtain ⟨r, off, data, rfl, hg, -, z1, n1⟩ := h1
  obtain ⟨r', off', data', e, hg', -, z2, n2⟩ := h2
  injection e with e1 e2; subst e1; subst e2
  rw [hg] at hg'; cases hg'
  rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd z1 (n2 m hlt)
  · exact heq
  · exact absurd z2 (n1 m' hgt)

/-- The stream's buffers stay valid when `L` output bytes are written and `next_out` / `avail_out` move past
them. -/
theorem streamIO_out {h h' : Heap} {i : Nat} {z z' : ZStream} {b ob oo L : Nat} {st st' : DeflateState}
    (hio : DStreamIO h (some i)) (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st)
    (hno : z.next_out = .ref (.heap ob) oo) (hL : L ≤ z.avail_out.toNat) (O : OutOnly h h' b ob oo L)
    (hz' : h'.streams i = some z') (hzs : z'.state = z.state) (hin : z'.next_in = z.next_in)
    (hai : z'.avail_in = z.avail_in) (hno' : z'.next_out = .ref (.heap ob) (oo + L))
    (hav : z'.avail_out.toNat = z.avail_out.toNat - L) (hst' : h'.dstate b = some st')
    (hgz : st'.gzhead = st.gzhead) : DStreamIO h' (some i) := by
  obtain ⟨z0, b0, hp, ⟨i0, e0, hz0⟩, hb0, ⟨b1, st1, ⟨⟨z1, ⟨i1, e1, hz1⟩, hb1⟩, hst1⟩, hg1⟩, hhd, hin0, hout0, hnb0,
    hdj⟩ := hio
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  obtain rfl : st = st1 := Option.some.inj (hst.symm.trans hst1)
  have hgz' : h'.gzheaders = h.gzheaders := O.2.1
  have hob : ob ≠ b := fun e => hnb0 oo (by rw [hno, e])
  -- the header strings of `h'` are those of `h`
  have hcs : ∀ p, (p = .null ∨ ∃ n, CStringLen h p n) → (∀ n, CStringLen h p n → Disjoint z.next_out
      z.avail_out.toNat p (n + 1) ∧ NotInBlock b p) →
      (p = .null ∨ ∃ n, CStringLen h' p n) ∧ ∀ n, CStringLen h' p n → CStringLen h p n := by
    intro p hp hpd
    rcases hp with hp | ⟨n, hn⟩
    · refine ⟨.inl hp, fun n hn => ?_⟩
      obtain ⟨_, _, _, e, -⟩ := hn; rw [hp] at e; cases e
    · have ⟨hd1, hnb1⟩ := hpd n hn
      rw [hno] at hd1
      have hn' := cstr_out O hn hnb1 (disj_mono hd1 hL (Nat.le_refl _))
      exact ⟨.inr ⟨n, hn'⟩, fun m hm => by rw [← cstr_unique hn' hm]; exact hn⟩
  refine ⟨z', b, hp, ⟨i, rfl, hz'⟩, by rw [hzs]; exact hb, ⟨b, st', ⟨⟨z', ⟨i, rfl, hz'⟩, by rw [hzs]; exact hb⟩, hst'⟩,
    by rw [hgz]; exact hg1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, hg, hx, hn, hc⟩ := hhd k hk
    have rx : DReadRange h z hp (g.extra, g.extra_len.toNat) := .inr ⟨k, hk, g, hg, .inl rfl⟩
    have dn := hcs g.name hn (fun n hn' => hdj _ (.inr ⟨k, hk, g, hg, .inr (.inl ⟨n, hn', rfl⟩)⟩))
    have dc := hcs g.comment hc (fun n hn' => hdj _ (.inr ⟨k, hk, g, hg, .inr (.inr ⟨n, hn', rfl⟩)⟩))
    exact ⟨g, by rw [hgz']; exact hg, nullOrRead_out O hx (hdj _ rx).2, dn.1, dc.1⟩
  · rw [hin, hai]; exact nullOrRead_out O hin0 (hdj _ (.inl rfl)).2
  · rw [hno', hav]
    rcases hout0 with e | ⟨ob', oo', ad, e, had, hle⟩
    · rw [hno] at e; cases e
    · rw [hno] at e; injection e with e1 e2; injection e1 with e1; subst e1; subst e2
      obtain ⟨ad', h1, h2, -⟩ := O.2.2 _ hob ad had
      exact .inr ⟨_, _, ad', rfl, h1, by omega⟩
  · rw [hno']; intro off e; injection e with e1; injection e1 with e1; exact hob e1
  · intro r hr
    have hr' : DReadRange h z hp r := by
      rcases hr with e | ⟨k, hk, g, hg, hx⟩
      · left; rw [e, hin, hai]
      · rw [hgz'] at hg
        obtain ⟨g0, hg0, -, hn, hc⟩ := hhd k hk
        obtain rfl : g = g0 := Option.some.inj (hg.symm.trans hg0)
        refine .inr ⟨k, hk, g, hg0, ?_⟩
        rcases hx with e | ⟨n, hn', e⟩ | ⟨n, hn', e⟩
        · exact .inl e
        · exact .inr (.inl ⟨n, (hcs g.name hn (fun n hn' => hdj _ (.inr ⟨k, hk, g, hg0,
            .inr (.inl ⟨n, hn', rfl⟩)⟩))).2 n hn', e⟩)
        · exact .inr (.inr ⟨n, (hcs g.comment hc (fun n hn' => hdj _ (.inr ⟨k, hk, g, hg0,
            .inr (.inr ⟨n, hn', rfl⟩)⟩))).2 n hn', e⟩)
    obtain ⟨hd, hn⟩ := hdj r hr'
    refine ⟨?_, hn⟩
    rw [hno', hav]; rw [hno] at hd
    match r, hd with
    | (.ref _ _, _), .inl hne => exact .inl hne
    | (.ref _ _, _), .inr (.inl h) => exact .inr (.inl (by omega))
    | (.ref _ _, _), .inr (.inr h) => exact .inr (.inr (by omega))
    | (.null, _), _ => trivial

/-- `flush_pending` on a stream in the working state with valid and set buffers: no fault, the invariant, valid
and set buffers after, and `FlushPost`. -/
theorem flush_ok {h : Heap} {i : Nat} (hw : DWork h (some i)) (hio : DStreamIO h (some i))
    (hset : DBufsSet h (some i)) :
    ∃ h', C.run (ZlibNg.DeflateP.flush_pending (some i)) h = .ok ((), h') ∧ DInv h' (some i) ∧
      DStreamIO h' (some i) ∧ DBufsSet h' (some i) ∧
      ∀ z b st, h.streams i = some z → z.state = some b → h.dstate b = some st → FlushPost h h' i b z st := by
  have hw0 := hw
  obtain ⟨i', z, b, st, al, e0, hz, hb, hst, -⟩ := hw0
  obtain rfl : i = i' := Option.some.inj e0
  obtain ⟨z1, ⟨i1, e1, hz1⟩, hnn, hni⟩ := hset
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  have hio' := hio
  obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, -, hout, hnb, -⟩ := hio'
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb.symm.trans hb2)
  have hws : WriteSlice h z.next_out z.avail_out.toNat := hout.resolve_left hnn
  obtain ⟨h', e, hv, F⟩ := flush_work hw hz hb hst hws hnb
  refine ⟨h', e, hv, ?_, ?_, fun z' b' st' hz' hb' hst' => ?_⟩
  · obtain ⟨ob, oo, ad, hno, -, -⟩ := hws
    obtain ⟨L, z', st', hz', hst', hL, -, hsteq, hav, hzeq, hadv, -, O, -⟩ := F
    refine streamIO_out hio hz hb hst hno (by omega) (O ob oo hno) hz' (by rw [hzeq]) (by rw [hzeq])
      (by rw [hzeq]) (hadv ob oo hno) hav hst' (by rw [hsteq])
  · obtain ⟨ob, oo, ad, hno, -, -⟩ := hws
    obtain ⟨L, z', st', hz', -, -, -, -, -, hzeq, hadv, -⟩ := F
    refine ⟨z', ⟨i, rfl, hz'⟩, by rw [hadv ob oo hno]; simp, fun ha => ?_⟩
    have : z'.next_in = z.next_in := by rw [hzeq]
    rw [this]; exact hni (by rw [hzeq] at ha; exact ha)
  · obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain rfl : st = st' := Option.some.inj (hst.symm.trans hst')
    exact F

end ZlibNgF.Proof.DeflateFlush
