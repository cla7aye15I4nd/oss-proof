import ZlibNgF.Proof.«deflate.c.dict»
import ZlibNgF.Proof.«trees_emit.h.bits»
import ZlibNgF.Proof.«inffast.base»

/-!
# `deflatePrime` (`ZlibNgF`)

On a stream with the structural invariant, `deflatePrime` either returns early (`Z_BUF_ERROR` for a bad `bits` or
when the primed bytes would reach `sym_buf`) or moves `bits` bits through `bi_buf` with `zng_tr_flush_bits`: the
complete bytes go to `pending_buf + pending`, below `sym_buf` by the call's own check. Only the stream's block
changes. When no pending output was flushed since the last reset (`PrimeReady`: `pending_out == pending_buf`) the
pending bytes stay within `pending_buf` and the invariant is kept.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflatePrime
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateBits
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InffastBase (sat_cdoWhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

theorem shr3_tbl : ∀ n : Fin 129, ((Int32.ofNat n.val) >>> 3).toInt = (n.val : Int) / 8 := by decide

theorem shr3 (k : Int32) (h0 : 0 ≤ k.toInt) (h1 : k.toInt ≤ 128) : (k >>> 3).toInt = k.toInt / 8 := by
  have e : k = Int32.ofNat k.toInt.toNat := by
    apply Int32.toInt_inj.mp; rw [Int32.toInt_ofNat_of_lt (by omega)]; omega
  have := shr3_tbl ⟨k.toInt.toNat, by omega⟩
  rw [e, this]; simp only []; rw [Int32.toInt_ofNat_of_lt (by omega)]

theorem chk_ok (v : Int) (h0 : -2147483648 ≤ v) (h1 : v < 2147483648) : chkI32 v = pure (Int32.ofInt v) := by
  simp [chkI32, h0, h1]

theorem ofInt_toInt (v : Int) (h0 : -2147483648 ≤ v) (h1 : v < 2147483648) : (Int32.ofInt v).toInt = v := by
  rw [Int32.toInt_ofInt]; have : (Int32.size : Int) = 4294967296 := rfl
  rw [Int.bmod_eq_of_le] <;> omega

theorem toUInt32_toNat (x : Int32) (h0 : 0 ≤ x.toInt) : x.toUInt32.toNat = x.toInt.toNat :=
  Int32.toNat_toUInt32_of_le (Int32.le_iff_toInt_le.mpr (by simpa using h0))

theorem lt_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {o1 o2 : Nat}
    (h1 : o1 ≤ d.size) (h2 : o2 ≤ d.size) :
    Ptr.lt (Ptr.ref (BRef.heap b) o1) (Ptr.ref (BRef.heap b) o2) (SH H i z b st d) =
      .ok (decide (o1 < o2), SH H i z b st d) := by
  simp [Ptr.lt, ZlibNgF.Proof.InflateAlloc.space_get_heap, h1, h2]

/-- What `deflatePrime` leaves on the state of block `b`: new `pending`, `bi_buf`, `bi_valid`, the bytes changed
only after the old pending bytes, fewer than 8 bits, and at most `T` pending bytes. -/
def PPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo T : Nat)
    (H' : Heap) : Prop :=
  ∃ np bb bv d', H' = SH H i z b { st with pending := np, bi_buf := bb, bi_valid := bv } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' ∧ 0 ≤ bv.toInt ∧ bv.toInt < 8 ∧
    st.pending.toNat ≤ np.toNat ∧ np.toNat ≤ T

/-- The loop state of `deflatePrime`: `x.1` bits still to insert, all the bits counted. -/
def PInv (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo tot : Nat)
    (x : Int32 × UInt64) (H' : Heap) : Prop :=
  ∃ np bb bv d', H' = SH H i z b { st with pending := np, bi_buf := bb, bi_valid := bv } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' ∧ 0 ≤ bv.toInt ∧ bv.toInt < 8 ∧
    0 ≤ x.1.toInt ∧ x.1.toInt ≤ 64 ∧ np.toNat * 8 + bv.toInt.toNat + x.1.toInt.toNat = tot ∧
    st.pending.toNat ≤ np.toNat

theorem prime_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    {pbo lb : Nat} (k : DOk i z b st) (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hsb : st.sym_buf = .val (.ref (.heap b) (pbo + lb + 8))) (hpend : st.pending.toNat ≤ 4 * lb + 9)
    (hd : pbo + 4 * lb + 64 ≤ d.size) (hlb : lb ≤ 32768) (hv0 : 0 ≤ st.bi_valid.toInt)
    (hv8 : st.bi_valid.toInt < 8) (bits value : Int32) :
    Sat (SH H i z b st d) (deflatePrime (some i) bits value)
      (fun _ H' => PPost H i z b st d pbo (max st.pending.toNat (lb + 8)) H') := by
  have hrefl : PPost H i z b st d pbo (max st.pending.toNat (lb + 8)) (SH H i z b st d) :=
    ⟨st.pending, st.bi_buf, st.bi_valid, d, rfl, WrIn.refl _ _ _, hv0, hv8, Nat.le_refl _, Nat.le_max_left _ _⟩
  unfold deflatePrime
  refine Sat.bind (Sat.of_eq (check_SH k) ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (by simp only [dstateOf]; exact rdZ_SH _) ?_); try dsimp only
  rw [k.hb]
  split
  · exact Sat.pure hrefl
  rename_i hbad
  have e64 : (BIT_BUF_SIZE).toInt = 64 := rfl
  have e0 : (0 : Int32).toInt = 0 := rfl
  have hb0 : 0 ≤ bits.toInt := by
    refine Int.not_lt.mp (fun hc => hbad ?_)
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Int32.lt_iff_toInt_lt.mpr (by rw [e0]; omega))
  have hb64 : bits.toInt ≤ 64 := by
    refine Int.not_lt.mp (fun hc => hbad ?_)
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr (Int32.lt_iff_toInt_lt.mpr (by rw [e64]; omega))
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  rw [chk_ok _ (by omega) (by omega), pure_bind_M]
  have hk := ofInt_toInt (st.bi_valid.toInt + bits.toInt) (by omega) (by omega)
  have hk3 := shr3 (Int32.ofInt (st.bi_valid.toInt + bits.toInt)) (by omega) (by omega)
  rw [hk] at hk3
  simp only [hpb, hsb, Ival.get, pure_bind_M]
  refine Sat.bind (Sat.of_eq (addI_SH (st.pending.toNat : Int) (by omega) (by omega)) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (addI_SH _ (by omega) (by omega)) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (lt_SH (by omega) (by omega)) ?_); try dsimp only
  split
  · exact Sat.pure hrefl
  rename_i hlt
  have G : st.pending.toNat * 8 + st.bi_valid.toInt.toNat + bits.toInt.toNat ≤ (lb + 8) * 8 + 7 := by
    simp only [decide_eq_true_eq] at hlt
    rw [hk3] at hlt
    omega
  refine Sat.bind (Sat.mono (sat_cdoWhile (PInv H i z b st d pbo
      (st.pending.toNat * 8 + st.bi_valid.toInt.toNat + bits.toInt.toNat)) (fun x => x.1.toInt.toNat)
    (fun _ H' => PPost H i z b st d pbo (max st.pending.toNat (lb + 8)) H') ?_
    ⟨st.pending, st.bi_buf, st.bi_valid, d, rfl, WrIn.refl _ _ _, hv0, hv8, hb0, hb64, rfl, Nat.le_refl _⟩
    (by show bits.toInt.toNat < 2 ^ 64; omega)) (fun _ _ q => Sat.pure q))
  rintro ⟨br, v⟩ H1 ⟨np, bb, bv, d1, rfl, w1, hbv0, hbv8, hbr0, hbr64, htot, hnp⟩
  dsimp only at hbr0 hbr64 htot ⊢
  have hnp8 : np.toNat ≤ lb + 8 := by omega
  have hd1 : d1.size = d.size := w1.1
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  rw [chk_ok _ (by omega) (by omega), pure_bind_M]
  have hp0 := ofInt_toInt (BIT_BUF_SIZE.toInt - bv.toInt) (by omega) (by omega)
  obtain ⟨put, hput, hP⟩ : ∃ put : Int32, (if Int32.ofInt (BIT_BUF_SIZE.toInt - bv.toInt) > br then br else
      Int32.ofInt (BIT_BUF_SIZE.toInt - bv.toInt)) = put ∧
      put.toInt = min (64 - bv.toInt) br.toInt := by
    refine ⟨_, rfl, ?_⟩
    split
    · rename_i hc; have := Int32.lt_iff_toInt_lt.mp hc; rw [hp0] at this; omega
    · rename_i hc; have := Int32.not_lt.mp hc; rw [Int32.le_iff_toInt_le, hp0] at this; rw [hp0]; omega
  rw [hput]
  split
  · refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    try simp only [pure_bind_M]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    rw [chk_ok _ (by omega) (by omega), pure_bind_M]
    have hbv2 := ofInt_toInt (bv.toInt + put.toInt) (by omega) (by omega)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (flush_bits_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; rw [hbv2, hd1]; omega) (by dsimp only; omega)) ?_)
    rintro _ _ ⟨d2, bb2, bv2, np2, rfl, w2, h20, h28, he⟩
    dsimp only at w2 he
    rw [hbv2] at he
    have hsub := ZlibNgF.Proof.DeflateBits.sub_toInt br put (by omega) (by omega)
    have hnp2 : np.toNat ≤ np2.toNat := by omega
    have w12 : WrIn d (pbo + st.pending.toNat) (pbo + np2.toNat) d2 :=
      (w1.widen (Nat.le_refl _) (by omega)).trans (w2.widen (by omega) (Nat.le_refl _)) (Nat.le_refl _)
        (Nat.le_refl _)
    refine Sat.pure (Sat.pure ⟨fun hc => ⟨⟨np2, bb2, bv2, d2, rfl, w12, h20, h28, ?_, ?_, ?_, by omega⟩, ?_⟩,
      fun _ => ⟨np2, bb2, bv2, d2, rfl, w12, h20, h28, by omega, ?_⟩⟩)
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only
      have : (br - put) ≠ 0 := by simpa using hc
      have : (br - put).toInt ≠ 0 := fun e => this (Int32.toInt_inj.mp (by rw [e]; rfl))
      omega
    · have : (br - put).toInt = 0 := by
        rename_i hc
        have : (br - put) = 0 := by simpa using hc
        rw [this]; rfl
      omega
  · rename_i hc
    have hP64 : put.toInt < 64 := by
      have : put ≠ BIT_BUF_SIZE := fun e => hc (by rw [e]; rfl)
      have : put.toInt ≠ 64 := fun e => this (Int32.toInt_inj.mp (by rw [e, e64]))
      omega
    have hu1 : put.toUInt32 < 64 := by
      rw [UInt32.lt_iff_toNat_lt, toUInt32_toNat _ (by omega)]; show put.toInt.toNat < 64; omega
    have hu2 : bv.toUInt32 < 64 := by
      rw [UInt32.lt_iff_toNat_lt, toUInt32_toNat _ (by omega)]; show bv.toInt.toNat < 64; omega
    simp only [shl64, hu1, ↓reduceIte, pure_bind_M]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    simp only [hu2, ↓reduceIte, pure_bind_M]
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    try simp only [shr64, hu1, ↓reduceIte, pure_bind_M]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    rw [chk_ok _ (by omega) (by omega), pure_bind_M]
    have hbv2 := ofInt_toInt (bv.toInt + put.toInt) (by omega) (by omega)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (flush_bits_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; rw [hbv2, hd1]; omega) (by dsimp only; omega)) ?_)
    rintro _ _ ⟨d2, bb2, bv2, np2, rfl, w2, h20, h28, he⟩
    dsimp only at w2 he
    rw [hbv2] at he
    have hsub := ZlibNgF.Proof.DeflateBits.sub_toInt br put (by omega) (by omega)
    have hnp2 : np.toNat ≤ np2.toNat := by omega
    have w12 : WrIn d (pbo + st.pending.toNat) (pbo + np2.toNat) d2 :=
      (w1.widen (Nat.le_refl _) (by omega)).trans (w2.widen (by omega) (Nat.le_refl _)) (Nat.le_refl _)
        (Nat.le_refl _)
    refine Sat.pure (Sat.pure ⟨fun hc => ⟨⟨np2, bb2, bv2, d2, rfl, w12, h20, h28, ?_, ?_, ?_, by omega⟩, ?_⟩,
      fun _ => ⟨np2, bb2, bv2, d2, rfl, w12, h20, h28, by omega, ?_⟩⟩)
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only
      have : (br - put) ≠ 0 := by simpa using hc
      have : (br - put).toInt ≠ 0 := fun e => this (Int32.toInt_inj.mp (by rw [e]; rfl))
      omega
    · have : (br - put).toInt = 0 := by
        rename_i hc
        have : (br - put) = 0 := by simpa using hc
        rw [this]; rfl
      omega

theorem dframe_SH0 {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) (b : Nat) (st : DeflateState)
    (d : Array UInt8) : DFrame h (SH h i z b st d) [] [b] [] [] := by
  have e : (SH h i z b st d).streams = h.streams := by simp only [SH, DeflateReset.upd_self _ _ _ hz]
  obtain ⟨⟨_, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩, g⟩ := DeflateReset.dframe_SH h i z b st d
  exact ⟨⟨fun j _ => by rw [e], f2, f3, f4, f5, f6, f7, f8, f9, f10⟩, g⟩

theorem prime_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (bits value : Int32) :
    C.run (deflatePrime s bits value) h = .ok (Z_STREAM_ERROR, h) := by
  simp only [C.run, deflatePrime, bind_app, stateCheck_noState hn, ↓reduceIte]; rfl

/-- `deflatePrime` on an invariant stream: no fault, only the stream's block changes, and the invariant holds after
when no pending output was flushed since the last reset. -/
theorem prime_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) (bits value : Int32) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ ∃ r h',
      C.run (deflatePrime s bits value) h = .ok (r, h') ∧ DFrame h h' [] [b] [] [] ∧
      (PrimeReady h s → DInv h' s) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨-, -, -, l1, l2, -, -⟩ := c.sizes
  obtain ⟨d, wo, po, ho, pbo, hd, hw, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  obtain ⟨b0, b8⟩ := c.bits
  simp only [dview] at l1 l2 hw hp hh hpb h1 h2 h3 h4 hsb hpo hpoo hpe b0 b8
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  have v0 : 0 ≤ st.bi_valid.toInt := by have := Int32.le_iff_toInt_le.mp b0; simpa using this
  have v8 : st.bi_valid.toInt < 8 := by have := Int32.lt_iff_toInt_lt.mp b8; simpa using this
  have S := prime_SH (H := h) (d := d) (lb := st.lit_bufsize.toNat) ⟨L.za, L.zf, L.hb, L.ab, L.sm, L.lo, L.hi⟩
    hpb hsb (by omega) h4 l2 v0 v8 bits value
  rw [DeflateReset.SH_self L.hz L.hst hd] at S
  obtain ⟨r, h', e, np, bb, bv, d', rfl, w, h0, h8, hle, hge⟩ := S
  refine ⟨i, z, b, rfl, L.hz, L.hb, r, _, e, dframe_SH0 L.hz _ _ _, fun hpr => ?_⟩
  obtain ⟨b1, st1, ⟨⟨z1, ⟨i1, hi1, hz1⟩, hb1⟩, hst1⟩, hpo1⟩ := hpr
  obtain rfl := Option.some.inj hi1
  rw [L.hz] at hz1; obtain rfl := Option.some.inj hz1
  rw [L.hb] at hb1; obtain rfl := Option.some.inj hb1
  rw [L.dstate] at hst1; obtain rfl := Option.some.inj hst1
  rw [hpo, hpb] at hpo1
  obtain rfl : pbo = poo := by injection hpo1 with e1; injection e1; omega
  refine ⟨i, z, b, _, al, rfl, SH_streams _ _ _ _ _ _, L.hb, SH_dstate _ _ _ _ _ _,
    by simp [Heap.dallocsOf, SH, hda], ?_⟩
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
    head := ⟨ho, d', by simp [SH], hh, by rw [w.1]; omega⟩
    level := c.level
    trees := c.trees
    sizes := c.sizes
    lay := ⟨d', wo, po, ho, pbo, by simp [SH], hw, hp, hh, hpb, h1, h2, h3, by rw [w.1]; exact h4, hsb, pbo, hpo,
      Nat.le_refl _, by simp only [dview]; omega⟩
    pout := fun _ => by simp only [dview]; rw [hpo, hpb]
    syms := c.syms
    bits := ⟨Int32.le_iff_toInt_le.mpr (by rw [show (0 : Int32).toInt = 0 from rfl]; exact h0),
      Int32.lt_iff_toInt_lt.mpr (by rw [show (8 : Int32).toInt = 8 from rfl]; exact h8)⟩
    look := c.look
    strategy := c.strategy
    fns := c.fns
    symv := by
      obtain ⟨d0, sbo, hd0, hs0, hv0⟩ := c.symv
      obtain rfl : d0 = d := Option.some.inj (hd0.symm.trans hd)
      simp only [dview] at hs0 hv0
      rw [hsb] at hs0
      obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hs0 with e1; injection e1
      refine ⟨d', _, by simp [SH], hsb, hv0.of_eq fun j hj => ?_⟩
      have hn : st.sym_next ≠ 0 := fun e => by simp [e] at hj
      obtain ⟨pbo1, poo1, hp1, ho1, hq⟩ := c.psym hn
      simp only [dview] at hp1 ho1 hq
      rw [hpb] at hp1; rw [hpo] at ho1
      obtain rfl : pbo = pbo1 := by injection hp1 with e1; injection e1
      obtain rfl : pbo = poo1 := by injection ho1 with e1; injection e1
      have hnp : np.toNat ≤ st.lit_bufsize.toNat + 8 := by omega
      exact w.2 _ (Or.inr (by omega))
    psym := fun hn => by
      obtain ⟨pbo1, poo1, hp1, ho1, hq⟩ := c.psym hn
      simp only [dview] at hp1 ho1 hq ⊢
      rw [hpb] at hp1; rw [hpo] at ho1
      obtain rfl : pbo = pbo1 := by injection hp1 with e1; injection e1
      obtain rfl : pbo = poo1 := by injection ho1 with e1; injection e1
      exact ⟨pbo, pbo, hpb, hpo, by omega⟩
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

end ZlibNgF.Proof.DeflatePrime
