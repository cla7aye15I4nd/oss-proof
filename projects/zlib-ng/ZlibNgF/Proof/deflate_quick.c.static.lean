import ZlibNgF.Proof.«deflate_quick.c.frame»
import ZlibNgF.Proof.«deflate_quick.c.safety»
import ZlibNgF.Proof.«deflate_stored.c.safety»

/-!
# `deflate_quick` with `Z_FIXED`: the emitters and the match part (`ZlibNgF`)

With `static_emit`, `quick_emit_lit` / `quick_emit_dist` send the symbol straight into `pending_buf` with the static
trees. A trip of the main loop tests `pending + 8 < pending_buf_size` first (else it flushes), so at most
`8 * (4 * lit_bufsize - 9) + 63` bits wait before the trip's symbols; the trip adds a block header (3 bits) and one
literal (at most 9 bits) or match (at most 31 bits), and a trip of the continuation loop tests the same bound before
its match. `QR` is the state between the test and the symbols: `QF`, the locals `strstart` / `lookahead` past the
stale values in the state with the same end of the lookahead, `pending_out` at `pending_buf`, a block open, and a
budget `B` of bits that still fit (`8 * pending + bi_valid + B <= 32 * lit_bufsize + 32`, so that the complete bytes
stay within `4 * lit_bufsize + 4` and an 8-byte store at `pending_buf + pending` stays in the block).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.QuickS
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.TreesEmitP (APost WDPost)
open ZlibNg.DeflateP ZlibNg.DeflateQuick
open ZlibNgF.Proof.DeflatePsi (psiS G span owed content quickB)

/-! ## Numbers -/

/-- The bits written so far: `8 * pending + bi_valid`. -/
def bitsOf (st : DeflateState) : Nat := st.pending.toNat * 8 + st.bi_valid.toInt.toNat

/-- The numbers of a state under `QF`. -/
theorem qf_nums {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) :
    ∃ wo po ho pbo, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho ∧
      st.pending_buf = .val (.ref (.heap b) pbo) ∧ wo + st.window_size.toNat ≤ po ∧ ho + 131072 ≤ pbo ∧
      pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size ∧ 128 ≤ st.lit_bufsize.toNat ∧
      st.lit_bufsize.toNat ≤ 32768 ∧ st.pending_buf_size.toNat = 4 * st.lit_bufsize.toNat ∧
      st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat ∧ st.window_size.toNat ≤ 65536 ∧
      512 ≤ st.w_size.toNat ∧ st.w_size.toNat ≤ 32768 ∧ 0 ≤ st.bi_valid.toInt ∧ st.bi_valid.toInt < 64 ∧
      st.block_start.toInt ≤ st.strstart.toNat ∧ 0 ≤ st.block_start ∧
      st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ 4 * st.lit_bufsize.toNat + 9 ∧
      st.strm = .val (some i) ∧ st.sym_next = 0 := by
  obtain ⟨z1, st1, al, hz1, hb, hst1, -, c⟩ := F.live
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  obtain ⟨wo, po, ho, pbo, L, hwo, hpb, hho, -⟩ := ZlibNgF.Proof.FillFacts.hlay_of c (SH_bytes _ _ _ _ _ _)
  obtain ⟨d1, -, -, -, pbo1, hd1, -, -, -, hpb1, -, -, -, h4, -, poo, -, hpoo, hpe⟩ := c.lay
  obtain rfl : d = d1 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd1)
  simp only [dview] at hpb1 h4 hpoo hpe
  rw [hpb] at hpb1
  obtain rfl : pbo = pbo1 := by injection hpb1 with e1; injection e1
  obtain ⟨w1, w2, hws, l1, l2, pbs, -⟩ := c.sizes
  simp only [dview] at w1 w2 hws l1 l2 pbs
  have h65 : st.window_size.toNat ≤ 65536 := by
    rw [hws, DeflateInit.wbuf_toNat _ (by omega)]; unfold DeflateAlloc.dWS; split <;> omega
  have hb0 := Int32.le_iff_toInt_le.mp c.bits.1
  have hb64 := Int32.lt_iff_toInt_lt.mp c.bits.2
  have hlook := c.look
  have hbs := c.bstart
  have hlo := F.bs0 st (SH_dstate _ _ _ _ _ _)
  simp only [dview] at hb0 hb64 hlook hbs
  exact ⟨wo, po, ho, pbo, L, hpb, hwo, hho, h4, l1, l2, pbs, hlook, h65, w1, w2, by simpa using hb0,
    by simpa using hb64, hbs, hlo, by omega, c.strm, F.sym st (SH_dstate _ _ _ _ _ _)⟩

theorem bv_toInt32 (bv : UInt32) (h : bv.toNat < 64) : bv.toInt32.toInt = bv.toNat :=
  DeflateAlloc.u32_toInt32_toInt bv (by omega)

/-! ## The state between the room test and the symbols -/

/-- The state of a trip between the room test and the symbols (see the module comment), with the potential of the
call with flush `fl` spent (`QP` with no allowance). -/
def QR (fl : Int32) (h : Heap) (i b : Nat) (B : Nat) (la ss : UInt32) (H : Heap) : Prop :=
  ∃ H0 z st d, H = SH H0 i z b st d ∧ QF h i b H ∧ st.strstart.toNat ≤ ss.toNat ∧
    ss.toNat + la.toNat = st.strstart.toNat + st.lookahead.toNat ∧ st.pending_out = st.pending_buf ∧
    st.block_open ≠ 0 ∧ bitsOf st + B ≤ 32 * st.lit_bufsize.toNat + 32 ∧ QP fl 0 h i b la ss H

/-- The `avail_in` of an `SH` heap is its record's. -/
theorem qr_avIn {fl : Int32} {h H : Heap} {i b B : Nat} {la ss : UInt32} (R : QR fl h i b B la ss H) :
    ∃ H0 z st d, H = SH H0 i z b st d ∧ avIn H i = z.avail_in.toNat := by
  obtain ⟨H0, z, st, d, rfl, -⟩ := R
  exact ⟨H0, z, st, d, rfl, avIn_SH _ _ _ _ _ _⟩

/-- `QR` after an emitter that sent `n <= B` bits (`APost`), with `strstart` advanced by `k <= lookahead`. -/
theorem qr_apost {fl : Int32} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {B n K pbo : Nat}
    {la ss : UInt32} {H' : Heap} (F : QF h i b (SH H0 i z b st d)) (hss : st.strstart.toNat ≤ ss.toNat)
    (hsum : ss.toNat + la.toNat = st.strstart.toNat + st.lookahead.toNat) (hpo : st.pending_out = st.pending_buf)
    (hbo : st.block_open ≠ 0) (hB : bitsOf st + B ≤ 32 * st.lit_bufsize.toNat + 32)
    (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (q : APost H0 i z b st d pbo n K H') (hn : n ≤ B) (k : UInt32) (hk : k.toNat ≤ la.toNat)
    (A : QP fl 0 h i b la ss (SH H0 i z b st d)) (hk1 : 1 ≤ k.toNat) (hn31 : n ≤ 31) :
    QR fl h i b (B - n) (la - k) (ss + k) H' ∧ avIn H' i = avIn (SH H0 i z b st d) i := by
  have hO := ZlibNgF.Proof.TreesOwed.owed_apost q
  obtain ⟨np, bb, bv, d', rfl, w, hacc, hbv, hle, hge⟩ := q
  obtain ⟨wo, po, ho, pbo', L, -, -, -, -, -, -, -, hlook, h65, -, -, -, -, hbs, hlo, -⟩ := qf_nums F
  have e := bv_toInt32 bv hbv
  have z0 : (0 : Int32).toInt = 0 := rfl
  have s64 : (64 : Int32).toInt = 64 := rfl
  have hlk : (la - k).toNat = la.toNat - k.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hk)
  have hsk : (ss + k).toNat = ss.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
  unfold bitsOf at hB
  refine ⟨⟨H0, z, _, d', rfl, qf_bits F rfl hpb hpo w.1 (by dsimp only; rw [e]; omega)
    (Int32.le_iff_toInt_le.mpr (by rw [z0, e]; omega)) (Int32.lt_iff_toInt_lt.mpr (by rw [s64, e]; omega)) hbs hlo,
    by dsimp only; omega, by dsimp only; omega, hpo, hbo, by unfold bitsOf; dsimp only; rw [e]; omega, ?_⟩,
    by rw [avIn_SH, avIn_SH]⟩
  refine qp_next A F (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _)
    (Nat.le_refl _) (Nat.le_refl _) ?_
  rw [Nat.sub_self, Nat.sub_self, Nat.mul_zero]
  have ho := hO _ (SH_dstate _ _ _ _ _ _)
  have g := psiS_gen (f := fl) (st := FS st la ss)
    (st' := FS { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 } (la - k) (ss + k))
    (k := k.toNat) (out := 0) (q := 0) (o := 4) (by show (la - k).toNat + k.toNat = la.toNat; omega)
    (by unfold span; dsimp only; omega) rfl rfl rfl rfl
    (Nat.le_of_eq (by rw [Nat.add_zero]; exact quickB_open (st := FS st la ss) hbo rfl)) (by
      unfold owed at ho ⊢; dsimp only at ho ⊢; rw [e] at ho ⊢; omega)
  omega

theorem qr_mono {fl : Int32} {h H : Heap} {i b B B' : Nat} {la ss : UInt32} (R : QR fl h i b B la ss H)
    (hB : B' ≤ B) : QR fl h i b B' la ss H := by
  obtain ⟨H0, z, st, d, e, F, a1, a2, a3, a4, a5, a6⟩ := R
  exact ⟨H0, z, st, d, e, F, a1, a2, a3, a4, by omega, a6⟩

/-- The room for an emitter under `QR`. -/
theorem qr_room {h H0 : Heap} {i b B : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) (hB : bitsOf st + B ≤ 32 * st.lit_bufsize.toNat + 32) :
    ∃ pbo, st.pending_buf = .val (.ref (.heap b) pbo) ∧ 0 ≤ st.bi_valid.toInt ∧ st.bi_valid.toInt < 64 ∧
      pbo + st.pending.toNat + 16 ≤ d.size ∧ st.pending.toNat + 16 < 2 ^ 32 := by
  obtain ⟨wo, po, ho, pbo, L, hpb, -, -, h4, -, l2, -, -, -, -, -, b0, b64, -⟩ := qf_nums F
  unfold bitsOf at hB
  exact ⟨pbo, hpb, b0, b64, by omega, by omega⟩

/-- `quick_emit_lit(s, lit, &strstart, &lookahead, 1)`: the literal through the static tree (at most 9 bits). -/
theorem qlit_s {fl : Int32} {h H : Heap} {i b B : Nat} {la ss : UInt32} (R : QR fl h i b B la ss H) (hB : 9 ≤ B)
    (hl : 1 ≤ la.toNat) (lit : UInt8) :
    Sat H (quick_emit_lit (some b) lit ss la 1) (fun v H' => v = (false, ss + 1, la - 1) ∧
      QR fl h i b (B - 9) (la - 1) (ss + 1) H' ∧ avIn H' i = avIn H i) := by
  obtain ⟨H0, z, st, d, rfl, F, hss, hsum, hpo, hbo, hBu, A⟩ := R
  obtain ⟨pbo, hpb, b0, b64, hr, hp⟩ := qr_room F hBu
  unfold quick_emit_lit
  simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte]
  have hc : lit.toUInt32.toNat < 256 := by simp; exact lit.toNat_lt
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.TreesCompress.emit_lit_exact hpb b0 b64 (by omega) (by omega)
    lit.toUInt32 hc) ?_)
  intro _ H' q
  have hl9 : (C.static_ltree[lit.toUInt32.toNat]!).dl.toNat ≤ 9 :=
    UInt16.le_iff_toNat_le.mp (ZlibNgF.Proof.TreesEmitP.sl_len ⟨lit.toUInt32.toNat, by omega⟩)
  obtain ⟨R', ha⟩ := qr_apost F hss hsum hpo hbo hBu hpb q (Nat.le_trans hl9 hB) 1 hl A (by decide) (by omega)
  exact Sat.pure ⟨rfl, qr_mono R' (by omega), ha⟩

/-- `quick_emit_dist(s, match_len, dist, &strstart, &lookahead, 1)`: the match through the static trees (at most 31
bits), with `match_len` 3..258 and at most `lookahead`, and `dist` 1..32768. -/
theorem qdist_s {fl : Int32} {h H : Heap} {i b B : Nat} {la ss : UInt32} (R : QR fl h i b B la ss H) (hB : 31 ≤ B)
    (ml dist : UInt32) (hm3 : 3 ≤ ml.toNat) (hm : ml.toNat ≤ 258) (hml : ml.toNat ≤ la.toNat)
    (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) :
    Sat H (quick_emit_dist (some b) ml dist ss la 1) (fun v H' => v = (false, ss + ml, la - ml) ∧
      QR fl h i b (B - 31) (la - ml) (ss + ml) H' ∧ avIn H' i = avIn H i) := by
  obtain ⟨H0, z, st, d, rfl, F, hss, hsum, hpo, hbo, hBu, A⟩ := R
  obtain ⟨pbo, hpb, b0, b64, hr, hp⟩ := qr_room F hBu
  unfold quick_emit_dist
  simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte]
  have hsub : (ml - STD_MIN_MATCH).toNat = ml.toNat - 3 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa [STD_MIN_MATCH] using hm3))
  have hlc : (ml - STD_MIN_MATCH).toNat < 256 := by rw [hsub]; omega
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.TreesCompress.emit_dist_exact hpb b0 b64 (by omega) (by omega)
    (ml - STD_MIN_MATCH) dist hlc hd1 hd2) ?_)
  intro _ H' q
  have hmc : ZlibNgF.Proof.TreesCompress.matchCost C.static_ltree
      C.static_dtree (ml - STD_MIN_MATCH).toNat (dist.toNat - 1) ≤ 31 :=
    ZlibNgF.Proof.TreesOverlayP.staticMatchCost_le _ _ hlc
      (ZlibNgF.Proof.TreesCompress.dCodeOf_lt _ (by omega))
  obtain ⟨R', ha⟩ := qr_apost F hss hsum hpo hbo hBu hpb q (Nat.le_trans hmc hB) ml hml A (by omega) hmc
  exact Sat.pure ⟨rfl, qr_mono R' (by omega), ha⟩

/-! ## The window -/

/-- The window, the hash-table layout and the bytes from the local `strstart` under `QF` and the locals. -/
theorem qf_win {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (F : QF h i b (SH H0 i z b st d)) (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hsum : ss.toNat + la.toNat = st.strstart.toNat + st.lookahead.toNat) :
    st.window = .val (.ref (.heap b) wo) ∧ wo + ss.toNat + la.toNat ≤ d.size ∧ wo + ss.toNat + 259 ≤ d.size ∧
      (∃ po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho) ∧ 512 ≤ st.w_size.toNat ∧
      st.w_size.toNat ≤ 32768 ∧ ss.toNat + la.toNat ≤ 65536 := by
  obtain ⟨wo', po, ho, pbo, L, hpb, hwo, hho, h4, -, -, -, hlook, h65, w1, w2, -⟩ := qf_nums F
  obtain ⟨st0, h0, hw⟩ := F.win
  have hwin : st.window = .val (.ref (.heap b) wo) := (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
  have e := L.win
  rw [hwin] at e
  obtain rfl : wo = wo' := by injection e with e; injection e
  have := L.ph
  exact ⟨hwin, by omega, by omega, ⟨po, ho, L⟩, w1, w2, by omega⟩

/-! ## The room test -/

/-- After the test `pending + 8 < pending_buf_size`, 41 bits fit. -/
theorem qr_test {fl : Int32} {h H : Heap} {i b : Nat} {la ss : UInt32} {st : DeflateState}
    (R : QR fl h i b 0 la ss H)
    (hst : H.dstate b = some st) (hn : ¬ (st.pending + 8 ≥ st.pending_buf_size)) : QR fl h i b 41 la ss H := by
  obtain ⟨H0, z, st1, d, rfl, F, a1, a2, a3, a4, -, a6⟩ := R
  obtain rfl : st = st1 := (Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, l2, pbs, -, -, -, -, b0, b64, -, -, hroom, -⟩ := qf_nums F
  have hp8 : (st.pending + 8).toNat = st.pending.toNat + 8 := by rw [UInt32.toNat_add]; simp; omega
  have hlt : st.pending.toNat + 8 < 4 * st.lit_bufsize.toNat := by
    have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hn); omega
  refine ⟨H0, z, st, d, rfl, F, a1, a2, a3, a4, ?_, a6⟩
  unfold bitsOf; omega

/-! ## The continuation loop -/

/-- The invariant of the continuation loop with `static_emit` over `(strstart, lookahead, exit)`, for a match at
distance `dist` and a bound `K` on `avail_in + lookahead`: it never returns. -/
def CIs (fl : Int32) (h : Heap) (i b : Nat) (dist : UInt32) (K : Nat) (v : UInt32 × UInt32 × QuickExit) (H : Heap) :
    Prop :=
  match v.2.2 with
  | .cont => QR fl h i b 0 v.2.1 v.1 H ∧ 262 ≤ v.2.1.toNat ∧ dist.toNat ≤ v.1.toNat ∧ avIn H i + v.2.1.toNat ≤ K
  | .brk => QR fl h i b 0 v.2.1 v.1 H ∧ 4 ≤ v.2.1.toNat ∧ avIn H i + v.2.1.toNat ≤ K
  | .ret _ => False

/-- One trip of the continuation loop (`quick_cont_trip` with `static_emit`). -/
theorem ctrip_s {fl : Int32} {h H : Heap} {i b wo : Nat} {la ss dist : UInt32} {K : Nat}
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (R : QR fl h i b 0 la ss H)
    (hla : 262 ≤ la.toNat) (hd : dist.toNat ≤ ss.toNat) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768)
    (hK : avIn H i + la.toNat ≤ K) :
    Sat H (quick_cont_trip (some b) (.ref (.heap b) wo) 1 dist ss la) (fun v H2 =>
      CIs fl h i b dist K v H2 ∧ ZlibNgF.Proof.QuickP.CM v < la.toNat + 1) := by
  have R0 := R
  obtain ⟨H0, z, st, d, rfl, F, hss, hsum, -⟩ := R0
  obtain ⟨-, -, hk, -⟩ := qf_win F hw0 hsum
  unfold quick_cont_trip
  simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  by_cases hc : st.pending + 8 ≥ st.pending_buf_size
  · simp only [hc, ↓reduceIte]
    exact Sat.pure ⟨⟨R, show 4 ≤ la.toNat by omega, hK⟩, by simp [ZlibNgF.Proof.QuickP.CM]⟩
  simp only [hc, ↓reduceIte]
  have R41 := qr_test R (SH_dstate _ _ _ _ _ _) hc
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.QuickP.mmc_ok ss dist hk hd) ?_)
  rintro ml _ ⟨rfl, hml⟩
  by_cases h8 : ml < 8
  · simp only [h8, ↓reduceIte]
    exact Sat.pure ⟨⟨R, show 4 ≤ la.toNat by omega, hK⟩, by simp [ZlibNgF.Proof.QuickP.CM]⟩
  simp only [h8, ↓reduceIte]
  have h8' : 8 ≤ ml.toNat := by
    have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h8); simpa using this
  refine Sat.bind (Sat.mono (qdist_s R41 (by omega) ml dist (by omega) hml (by omega) hd1 hd2) ?_)
  rintro ⟨r, ss2, la2⟩ H2 ⟨he, R2, ha⟩
  obtain ⟨rfl, rfl, rfl⟩ : r = false ∧ ss2 = ss + ml ∧ la2 = la - ml := by simpa using he
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hla2 : (la - ml).toNat = la.toNat - ml.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have hss2 : (ss + ml).toNat = ss.toNat + ml.toNat := by
    have := (qf_win F hw0 hsum).2.2.2.2.2.2
    rw [UInt32.toNat_add]; omega
  have R0 := qr_mono R2 (Nat.zero_le _)
  by_cases hl : la - ml < MIN_LOOKAHEAD
  · simp only [hl, ↓reduceIte]
    refine Sat.pure ⟨⟨R0, show 4 ≤ (la - ml).toNat by omega, ?_⟩, by simp [ZlibNgF.Proof.QuickP.CM]⟩
    rw [ha, hla2]; omega
  · simp only [hl, ↓reduceIte]
    have hl' : 262 ≤ (la - ml).toNat := by
      have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hl)
      simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
    refine Sat.pure ⟨⟨R0, hl', show dist.toNat ≤ (ss + ml).toNat by omega, ?_⟩, show (la - ml).toNat + 1 < la.toNat + 1 by omega⟩
    rw [ha, hla2]; omega

/-- The continuation loop with `static_emit`, entered after a match of `STD_MAX_MATCH` bytes with
`lookahead >= MIN_LOOKAHEAD`: it ends with `brk`, at least 4 bytes of lookahead left. -/
theorem cloop_s {fl : Int32} {h H : Heap} {i b wo : Nat} {la ss dist : UInt32} {K : Nat}
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (R : QR fl h i b 0 la ss H)
    (hla : 262 ≤ la.toNat) (hd : dist.toNat ≤ ss.toNat) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768)
    (hK : avIn H i + la.toNat ≤ K) (body : UInt32 × UInt32 × QuickExit → M (UInt32 × UInt32 × QuickExit))
    (hbody : ∀ ss la ex, body (ss, la, ex) = quick_cont_trip (some b) (.ref (.heap b) wo) 1 dist ss la) :
    Sat H (cwhile (fun (v : UInt32 × UInt32 × QuickExit) => pure (v.2.2.isCont, v)) body (ss, la, QuickExit.cont))
      (fun v H2 => CIs fl h i b dist K v H2 ∧ v.2.2.isCont = false) := by
  refine ZlibNgF.Proof.WinInv.sat_cwhileH (CIs fl h i b dist K) (fun v _ => ZlibNgF.Proof.QuickP.CM v)
    (fun v H => CIs fl h i b dist K v H ∧ v.2.2.isCont = false) ?_ (s := (ss, la, .cont)) ⟨R, hla, hd, hK⟩ ?_
  · rintro ⟨ss1, la1, ex⟩ H1 hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, hc⟩⟩
    cases ex with
    | cont =>
      obtain ⟨I1, h1, h2, h3⟩ := hI
      rw [hbody]
      exact Sat.mono (ctrip_s hw0 I1 h1 h2 hd1 hd2 h3) fun v H2 ⟨a, m⟩ => ⟨a, by
        simpa [ZlibNgF.Proof.QuickP.CM] using m⟩
    | brk => cases hc
    | ret r => cases hc
  · have := UInt32.toNat_lt la
    simp only [ZlibNgF.Proof.QuickP.CM, fuel]; omega

/-! ## The match part -/

/-- `QF` after a change of the block's bytes below the end of `head`. -/
theorem qf_hw {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8}
    (F : QF h i b (SH H0 i z b st d))
    (hw : ∀ ho, st.head = .val (.ref (.heap b) ho) → WrIn d 0 (ho + 131072) d') : QF h i b (SH H0 i z b st d') :=
  qf_SH F (fun _ _ c => ZlibNgF.Proof.FillFacts.dcore_fw (H := H0) c (SH_bytes _ _ _ _ _ _) rfl rfl
    ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ (ZlibNgF.Proof.FillFacts.wcore_of c) c.bs_lo c.look hw) rfl rfl
    (F.sym st (SH_dstate _ _ _ _ _ _)) (F.bs0 st (SH_dstate _ _ _ _ _ _)) (StratKeeps.refl _)

/-- What the match part leaves: on `none` the state kept (the `head` store aside), on `some` a `continue` with at
least 4 bytes consumed. -/
def MP (fl : Int32) (h : Heap) (i b B : Nat) (la ss : UInt32) (A : Nat) (o : Option (UInt32 × UInt32 × QuickExit))
    (H : Heap) : Prop :=
  (o = none → QR fl h i b B la ss H ∧ avIn H i = A) ∧
  (∀ v, o = some v → v.2.2 = .cont ∧ QR fl h i b 0 v.2.1 v.1 H ∧ avIn H i + v.2.1.toNat + 4 ≤ A + la.toNat ∧
    (262 ≤ la.toNat → 4 ≤ v.2.1.toNat))

/-- `quick_try_match` with `static_emit` (`deflate_quick.c:168-220`) under `QR` with at least 31 bits of room. -/
theorem smatch_s {fl : Int32} {h H : Heap} {i b wo B : Nat} {la ss : UInt32}
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (R : QR fl h i b B la ss H)
    (hB : 31 ≤ B) (str_val : UInt32) :
    Sat H (quick_try_match (some b) (.ref (.heap b) wo) 1 ss la str_val) (MP fl h i b B la ss (avIn H i)) := by
  have R0 := R
  obtain ⟨H0, z, st, d, rfl, F, hss, hsum, hpo, hbo, hBu, A⟩ := R0
  obtain ⟨-, -, -, ⟨po, ho, L⟩, w1, w2, h65⟩ := qf_win F hw0 hsum
  unfold quick_try_match
  by_cases hl4 : la ≥ WANT_MIN_MATCH
  · simp only [hl4, ↓reduceIte]
    have hl4' : 4 ≤ la.toNat := by simpa [WANT_MIN_MATCH] using UInt32.le_iff_toNat_le.mp hl4
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.InsertSafe.insert_knuth_val_head_SH L ss str_val) ?_)
    rintro hh _ ⟨d1, rfl, W⟩
    have F1 : QF h i b (SH H0 i z b st d1) := qf_hw F fun ho' e => by
      rw [L.head] at e
      obtain rfl : ho = ho' := by injection e with e; injection e
      exact W
    have R1 : QR fl h i b B la ss (SH H0 i z b st d1) := ⟨H0, z, st, d1, rfl, F1, hss, hsum, hpo, hbo, hBu,
      qp_bytes A⟩
    obtain ⟨-, hwd, hk, -⟩ := qf_win F1 hw0 hsum
    have none_ok : MP fl h i b B la ss (avIn (SH H0 i z b st d) i) none (SH H0 i z b st d1) :=
      ⟨fun _ => ⟨R1, by rw [avIn_SH, avIn_SH]⟩, fun v e => by cases e⟩
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    by_cases hc : (decide (ss.toUInt64.toInt64 - hh.toUInt64.toInt64 ≤ (MAX_DIST st).toUInt64.toInt64) &&
        decide (ss.toUInt64.toInt64 - hh.toUInt64.toInt64 > 0)) = true
    · simp only [hc, ↓reduceIte]
      obtain ⟨hlt, hmx, hdv⟩ := ZlibNgF.Proof.QuickP.dist_ok _ _ _ hc
      have hmd : (MAX_DIST st).toNat = st.w_size.toNat - 262 := by
        have e : MAX_DIST st = st.w_size - 262 := rfl
        rw [e, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by show 262 ≤ st.w_size.toNat; omega))]
        rfl
      rw [hmd] at hmx
      refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH hh.toNat (by omega)) ?_)
      obtain ⟨mv, emv⟩ := ZlibNgF.Proof.WinBase.memread4_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d1)
        (off := wo + hh.toNat) (by omega)
      refine Sat.bind (Sat.of_eq emv ?_)
      by_cases he : (str_val == mv) = true
      · simp only [he, ↓reduceIte]
        refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH ss.toNat (by omega)) ?_)
        refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH 2 (by omega)) ?_)
        refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH 2 (by omega)) ?_)
        refine Sat.bind (Sat.mono (ZlibNgF.Proof.Compare256.compare256_ok (SH_bytes H0 i z b st d1) (by omega)
          (by omega)) ?_)
        rintro r _ ⟨rfl, hr⟩
        have hr2 : (r + 2).toNat = r.toNat + 2 := by rw [UInt32.toNat_add]; simp; omega
        by_cases hm4 : r + 2 ≥ WANT_MIN_MATCH
        · simp only [hm4, ↓reduceIte]
          have hm4' : 4 ≤ r.toNat + 2 := by rw [← hr2]; simpa [WANT_MIN_MATCH] using UInt32.le_iff_toNat_le.mp hm4
          obtain ⟨ml, hml, hml1, hml2, hml3⟩ : ∃ ml : UInt32, (if r + 2 > la then la else r + 2) = ml ∧
              4 ≤ ml.toNat ∧ ml.toNat ≤ 258 ∧ ml.toNat ≤ la.toNat := by
            refine ⟨_, rfl, ?_⟩
            by_cases hg : r + 2 > la
            · simp only [hg, ↓reduceIte]; have := UInt32.lt_iff_toNat_lt.mp hg; omega
            · simp only [hg, ↓reduceIte]; have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hg); omega
          rw [hml]
          generalize hdd : (ss.toUInt64.toInt64 - hh.toUInt64.toInt64).toUInt64.toUInt32 = dd at hdv
          refine Sat.bind (Sat.mono (qdist_s R1 hB ml dd (by omega) hml2 hml3 (by omega) (by omega)) ?_)
          rintro ⟨r2, ss2, la2⟩ H2 ⟨he2, R2, ha2⟩
          obtain ⟨rfl, rfl, rfl⟩ : r2 = false ∧ ss2 = ss + ml ∧ la2 = la - ml := by simpa using he2
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hla2 : (la - ml).toNat = la.toNat - ml.toNat :=
            UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
          have hss2 : (ss + ml).toNat = ss.toNat + ml.toNat := by rw [UInt32.toNat_add]; omega
          rw [avIn_SH] at ha2
          have R20 := qr_mono R2 (Nat.zero_le _)
          by_cases hcm : ((ml == STD_MAX_MATCH) && decide (la - ml ≥ MIN_LOOKAHEAD)) = true
          · simp only [hcm, ↓reduceIte]
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcm
            have h262 : 262 ≤ (la - ml).toNat := by
              simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using UInt32.le_iff_toNat_le.mp hcm.2
            refine Sat.bind (Sat.mono (cloop_s (K := avIn H2 i + (la - ml).toNat) hw0 R20 h262 (by omega)
              (by omega) (by omega) (Nat.le_refl _) _ (fun _ _ _ => rfl)) ?_)
            rintro ⟨ss3, la3, ex⟩ H3 ⟨hI3, hc3⟩
            cases ex with
            | cont => cases hc3
            | ret r => exact absurd hI3 id
            | brk =>
              obtain ⟨I3, h43, hK3⟩ := hI3
              refine Sat.pure ⟨fun e => (by cases e), fun v e => ?_⟩
              cases e
              refine ⟨rfl, I3, ?_, fun _ => h43⟩
              dsimp only at hK3 h43 ⊢
              rw [ha2, hla2] at hK3; rw [avIn_SH]; omega
          · simp only [hcm, Bool.false_eq_true, ↓reduceIte]
            refine Sat.pure ⟨fun e => (by cases e), fun v e => ?_⟩
            cases e
            refine ⟨rfl, R20, ?_, fun h2 => ?_⟩
            · show avIn H2 i + (la - ml).toNat + 4 ≤ avIn (SH H0 i z b st d) i + la.toNat
              rw [ha2, hla2, avIn_SH]; omega
            · show 4 ≤ (la - ml).toNat
              omega
        · simp only [hm4, ↓reduceIte]
          exact Sat.pure none_ok
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact Sat.pure none_ok
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact Sat.pure none_ok
  · simp only [hl4, ↓reduceIte]
    exact Sat.pure ⟨fun _ => ⟨R, rfl⟩, fun v e => by cases e⟩

/-- `strstart` fits an `int` under `QF`. -/
theorem ss_toInt32_le {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) : st.strstart.toInt32.toInt = st.strstart.toNat := by
  obtain ⟨z1, st1, al, hz1, hb, hst1, -, c⟩ := F.live
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  exact (strstart_toInt32 c).1


/-! ## `quick_end_block` -/

/-- `zng_tr_emit_end_block` with the static tree and `last` 0 or 1, with 41 bits of room: the pending bytes and the
bit buffer changed, at most 63 bits, the complete bytes within `pending_buf`. -/
theorem eb_s0 {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) (hB : bitsOf st + 41 ≤ 32 * st.lit_bufsize.toNat + 32) (last : Int32)
    (hl : last = 0 ∨ last = 1) :
    Sat (SH H0 i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) static_ltree_p last) (fun _ H1 =>
      ∃ (np : UInt32) (bb : UInt64) (bv : Int32) (bu : Int32) (d1 : Array UInt8),
        H1 = SH H0 i z b { st with pending := np, bi_buf := bb, bi_valid := bv, bi_used := bu } d1 ∧
        d1.size = d.size ∧ np.toNat + bv.toInt.toNat / 8 ≤ 4 * st.lit_bufsize.toNat + 9 ∧ 0 ≤ bv ∧ bv < 64) := by
  obtain ⟨pbo, hpb, b0, b64, hr, hp⟩ := qr_room F hB
  have z0 : (0 : Int32).toInt = 0 := rfl
  have s64 : (64 : Int32).toInt = 64 := rfl
  unfold bitsOf at hB
  rcases hl with rfl | rfl
  · refine Sat.mono (ZlibNgF.Proof.TreesEmitP.end_block_SH hpb b0 b64 hr hp 0) ?_
    rintro _ _ ⟨q, -⟩
    obtain ⟨np, bb, bv, d', rfl, w, hacc, hbv, -, -⟩ := q rfl
    have e := bv_toInt32 bv hbv
    exact ⟨np, bb, bv.toInt32, st.bi_used, d', rfl, w.1, by rw [e]; omega,
      Int32.le_iff_toInt_le.mpr (by rw [z0, e]; omega), Int32.lt_iff_toInt_lt.mpr (by rw [s64, e]; omega)⟩
  · refine Sat.mono (ZlibNgF.Proof.TreesCompress.end_block_last_exact hpb b0 b64 hr hp 1 (by decide)) ?_
    rintro _ _ ⟨np, bu, d', rfl, w, hle, hge⟩
    exact ⟨np, 0, 0, bu, d', rfl, w.1, by rw [z0]; omega, by decide, by decide⟩

/-- `eb_s0` with `owed` raised by at most one byte (`TreesOwed.end_block_owed_SH`). -/
theorem eb_s {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) (hB : bitsOf st + 41 ≤ 32 * st.lit_bufsize.toNat + 32) (last : Int32)
    (hl : last = 0 ∨ last = 1) :
    Sat (SH H0 i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) static_ltree_p last) (fun _ H1 =>
      ∃ (np : UInt32) (bb : UInt64) (bv : Int32) (bu : Int32) (d1 : Array UInt8),
        H1 = SH H0 i z b { st with pending := np, bi_buf := bb, bi_valid := bv, bi_used := bu } d1 ∧
        d1.size = d.size ∧ np.toNat + bv.toInt.toNat / 8 ≤ 4 * st.lit_bufsize.toNat + 9 ∧ 0 ≤ bv ∧ bv < 64 ∧
        owed { st with pending := np, bi_buf := bb, bi_valid := bv, bi_used := bu } ≤ owed st + 1) := by
  obtain ⟨pbo, hpb, b0, b64, hr, hp⟩ := qr_room F hB
  refine Sat.mono (ZlibNgF.Proof.StoredF.sat_and (eb_s0 F hB last hl)
    (ZlibNgF.Proof.TreesOwed.end_block_owed_SH hpb b0 b64 hr hp last)) ?_
  rintro _ _ ⟨⟨np, bb, bv, bu, d1, rfl, a1, a2, a3, a4⟩, q⟩
  exact ⟨np, bb, bv, bu, d1, rfl, a1, a2, a3, a4, (q _ (SH_dstate _ _ _ _ _ _)).2⟩

/-- What `quick_end_block(s, strstart, last, 1)` leaves: nothing when no block is open; else `QF`, fewer than 8
bits, no block open, `lookahead` / `strstart` / `insert` and the input kept, and no pending bytes (with
`pending_out` at `pending_buf`) when it returns 0, a full output when it returns 1. -/
def QEB (fl : Int32) (e0 : Nat) (h : Heap) (i b : Nat) (H0 : Heap) (z : ZStream) (st : DeflateState)
    (d : Array UInt8) (r : Bool) (H' : Heap) : Prop :=
  (st.block_open = 0 → r = false ∧ H' = SH H0 i z b st d) ∧
  (st.block_open ≠ 0 → QF h i b H' ∧ ∃ z' st', H'.streams i = some z' ∧ H'.dstate b = some st' ∧
    st'.bi_valid < 8 ∧ st'.block_open = 0 ∧ st'.lookahead = st.lookahead ∧ st'.strstart = st.strstart ∧
    st'.insert = st.insert ∧ z'.avail_in = z.avail_in ∧
    (r = false → st'.pending = 0 ∧ st'.pending_out = st'.pending_buf) ∧ (r = true → z'.avail_out = 0) ∧
    QP fl e0 h i b st'.lookahead st'.strstart H')

/-- Closing a block (`block_open` to 0, `block_start` to `strstart`, `owed` up by at most one byte before
`flush_pending`) when no lookahead is left or for `Z_FINISH` on an open non-last block: `quickB` drops by at least 32,
so `psiS` drops by the bytes written. -/
theorem psiS_close {f : Int32} {st st4 : DeflateState} {out : Nat} (e1 : st4.lookahead = st.lookahead)
    (e4 : st4.sym_next = st.sym_next) (e5 : st4.match_available = st.match_available) (e6 : st4.status = st.status)
    (e7 : st4.wrap = st.wrap) (hsp : span st4 ≤ span st) (ho : owed st4 + out ≤ owed st + 1)
    (hbo : st.block_open ≠ 0) (hbo4 : st4.block_open = 0)
    (hq : st.lookahead = 0 ∨ (f = Z_FINISH ∧ st.block_open = 1)) : psiS f st4 + out ≤ psiS f st := by
  have q4 : quickB f st4 = if st.lookahead.toNat ≠ 0 then 64 else 0 := by
    unfold quickB; rw [hbo4, e1]; simp
  have q0 : quickB f st = if f = Z_FINISH ∧ st.block_open = 1 then 96 else 32 := by
    unfold quickB; rw [ite_eq_left hbo]
  have hq' : quickB f st4 + 1 ≤ quickB f st := by
    rw [q4, q0]
    rcases hq with h0 | h1
    · rw [h0]; simp only [UInt32.toNat_zero, ne_eq, not_true_eq_false, ↓reduceIte]; split <;> omega
    · rw [ite_eq_left h1]; split <;> omega
  unfold psiS content; rw [e1, e4, e5, e6, e7]; omega

/-- `quick_end_block(s, strstart, last, 1)` (`deflate_quick.c:32-50`) with `strstart` the state's, `last` 0 or 1,
`pending_out` at `pending_buf` and 41 bits of room. -/
theorem qeb_s {fl : Int32} {e0 : Nat} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) (hpo : st.pending_out = st.pending_buf)
    (hB : bitsOf st + 41 ≤ 32 * st.lit_bufsize.toNat + 32) (last : Int32) (hl : last = 0 ∨ last = 1)
    (A : QP fl e0 h i b st.lookahead st.strstart (SH H0 i z b st d))
    (hq : st.lookahead = 0 ∨ (fl = Z_FINISH ∧ st.block_open = 1)) :
    Sat (SH H0 i z b st d) (quick_end_block (some b) st.strstart last 1) (QEB fl e0 h i b H0 z st d) := by
  obtain ⟨wo, po, ho, pbo, L, hpb, -, -, -, -, -, -, hlook, h65, -, -, -, -, -, hlo, -, -, -⟩ := qf_nums F
  unfold quick_end_block
  simp only [show ((1 : Int32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  by_cases hbo : st.block_open = 0
  · simp only [hbo, show ((0 : UInt32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    exact Sat.pure ⟨fun _ => ⟨rfl, rfl⟩, fun h' => absurd hbo h'⟩
  have hbo' : (st.block_open != 0) = true := by simpa using hbo
  simp only [hbo', ↓reduceIte]
  refine Sat.bind (Sat.mono (eb_s F hB last hl) ?_)
  rintro _ _ ⟨np, bb, bv, bu, d1, rfl, hs1, hr1, h01, h641, how⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) (Sat.bind (Sat.of_eq (wrD_SH _) ?_)))
  have hss := ss_toInt32_le F
  have F3 : QF h i b (SH H0 i z b { st with
      pending := np
      bi_buf := bb
      bi_valid := bv
      bi_used := bu
      block_open := 0
      block_start := st.strstart.toInt32 } d1) :=
    qf_bits F rfl hpb hpo hs1 hr1 h01 h641 (by dsimp only; omega)
      (Int32.le_iff_toInt_le.mpr (by dsimp only; rw [show (0 : Int32).toInt = 0 from rfl]; omega))
  refine Sat.bind (Sat.of_eq (strmOf_qf F3) ?_)
  refine Sat.bind (Sat.mono (qf_flush F3) ?_)
  rintro _ H4 ⟨F4, z5, st5, z4, st4, hz5, hst5, hz4, hst4, hste, hbv4, hai, hout, hle4, hOw⟩
  rw [SH_streams] at hz5; obtain rfl := Option.some.inj hz5
  rw [SH_dstate] at hst5; obtain rfl := Option.some.inj hst5
  refine Sat.bind (Sat.of_eq (strmOf_qf F4) (Sat.bind (Sat.of_eq (ZlibNgF.Proof.DeflateInit.rdZ_app hz4 _) ?_)))
  refine Sat.pure ⟨fun e => absurd e hbo, fun _ => ⟨F4, z4, st4, hz4, hst4, hbv4, ?_, ?_, ?_, ?_, hai,
    fun hr => hout (fun e => by simp [e] at hr), (fun hr => by simpa using hr), ?_⟩⟩
  rotate_left 4
  · refine qp_next A F (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) hz4 hst4 hle4
      (by rw [hai]; exact Nat.le_refl _) ?_
    rw [hai, Nat.sub_self, Nat.mul_zero, FS_self, FS_self]
    have hss0 := ss_toInt32_le F
    have q := psiS_close (f := fl) (st := st) (st4 := st4) (out := z.avail_out.toNat - z4.avail_out.toNat)
      (by rw [hste]) (by rw [hste]) (by rw [hste]) (by rw [hste]) (by rw [hste])
      (by rw [hste]; unfold span; dsimp only; rw [hss0]; omega) (by
        unfold owed at hOw how ⊢; dsimp only at hOw how ⊢; omega)
      hbo (by rw [hste]) hq
    omega
  all_goals rw [hste]

/-! ## `quick_start_block` -/

/-- What the start of a block leaves, from the state `st` with lookahead `la`: `QF`, `strstart`, `lookahead`,
`insert` and the input kept, `pending_out` at `pending_buf`, a block open when `last` or lookahead, else nothing
changed, 38 bits of room, and 8 or more bits only if there were or with `last` or lookahead. -/
def QSB (fl : Int32) (ep : Nat) (h : Heap) (i b : Nat) (z : ZStream) (st : DeflateState) (la : UInt32) (last : Int32)
    (H' : Heap) : Prop :=
  ∃ H1 z1 st1 d1, H' = SH H1 i z1 b st1 d1 ∧ QF h i b H' ∧ st1.strstart = st.strstart ∧
    st1.lookahead = st.lookahead ∧ st1.insert = st.insert ∧ st1.pending_out = st1.pending_buf ∧
    z1.avail_in = z.avail_in ∧ (last ≠ 0 ∨ la ≠ 0 → st1.block_open ≠ 0) ∧
    (st1.block_open = 0 → st1.pending = st.pending ∧ st1.bi_valid = st.bi_valid ∧ last = 0 ∧ la = 0) ∧
    bitsOf st1 + 38 ≤ 32 * st1.lit_bufsize.toNat + 32 ∧
    (8 ≤ st1.bi_valid → 8 ≤ st.bi_valid ∨ last ≠ 0 ∨ la ≠ 0) ∧
    QP fl (if la = 0 ∧ last ≠ 0 then ep + 33 else ep) h i b st1.lookahead st1.strstart H' ∧
    st1.pending.toNat ≤ st.pending.toNat + 8

/-- Opening a block (`block_open` to `1 + last`, `block_start` to `strstart`, `owed` up by at most one byte): `quickB`
goes from 64 (lookahead) or 0 (none) to 32, so `psiS` rises by at most 33, and only with no lookahead (the last
block opened at an empty lookahead). -/
theorem psiS_open {f : Int32} {st st1 : DeflateState} {ep : Nat} {la : UInt32} {last : Int32} {z : ZStream}
    (hla : st.lookahead = la) (hc : last ≠ 0 ∨ 0 < la) (e1 : st1.lookahead = st.lookahead)
    (e4 : st1.sym_next = st.sym_next) (e5 : st1.match_available = st.match_available) (e6 : st1.status = st.status)
    (e7 : st1.wrap = st.wrap) (hsp : span st1 ≤ span st) (ho : owed st1 ≤ owed st + 1)
    (hb0 : st.block_open = 0) (hq1 : quickB f st1 = 32) :
    psiS f (FS st1 st1.lookahead st1.strstart) + (z.avail_out.toNat - z.avail_out.toNat) + ep ≤
      psiS f (FS st st.lookahead st.strstart) + G * (z.avail_in.toNat - z.avail_in.toNat) +
        (if la = 0 ∧ last ≠ 0 then ep + 33 else ep) := by
  rw [Nat.sub_self, Nat.sub_self, Nat.mul_zero, FS_self, FS_self]
  have hq : quickB f st = if st.lookahead.toNat ≠ 0 then 64 else 0 := by unfold quickB; rw [hb0]; simp
  by_cases h0 : la = 0
  · rw [ite_eq_left ⟨h0, hc.resolve_right (by rw [h0]; exact UInt32.lt_irrefl 0)⟩]
    have hl : ¬ st.lookahead.toNat ≠ 0 := by rw [hla, h0]; simp
    have : psiS f st1 ≤ psiS f st + 33 := by
      unfold psiS content; rw [e1, e4, e5, e6, e7, hq1, hq, ite_eq_right hl]; omega
    omega
  · rw [ite_eq_right (fun h => h0 h.1)]
    have hl : st.lookahead.toNat ≠ 0 := fun e => h0 (by rw [← hla]; exact UInt32.toNat_inj.mp (by simpa using e))
    have : psiS f st1 ≤ psiS f st := by
      unfold psiS content; rw [e1, e4, e5, e6, e7, hq1, hq, ite_eq_left hl]; omega
    omega

/-- The second half of `quick_start_block(s, strstart, lookahead, last, 1)`: the block header when no block is open
and `last` or lookahead. -/
theorem qsb_tail {fl : Int32} {ep : Nat} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState}
    {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) (hpo : st.pending_out = st.pending_buf)
    (hB : bitsOf st + 41 ≤ 32 * st.lit_bufsize.toNat + 32) (la : UInt32) (last : Int32)
    (hl : last = 0 ∨ last = 1) (A : QP fl ep h i b st.lookahead st.strstart (SH H0 i z b st d))
    (hla : st.lookahead = la) (hfl : last = 0 → fl ≠ Z_FINISH) :
    Sat (SH H0 i z b st d) (do
      let x ← rdD (some b) (·.block_open)
      if (x == 0 && (last != 0 || decide (la > 0))) = true then do
        ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STATIC_TREES last
        let bo ← chkI32 (1 + last.toInt)
        wrD (some b) fun s => { s with block_open := bo.toUInt32 }
        wrD (some b) fun s => { s with block_start := st.strstart.toInt32 }
        pure false
      else pure false) (fun r H' => r = false ∧ QSB fl ep h i b z st la last H') := by
  obtain ⟨wo, po, ho, pbo, L, hpb, -, -, h4, l1, l2, -, hlook, h65, -, -, b0, b64, -, hlo, -, -, -⟩ := qf_nums F
  have hss := ss_toInt32_le F
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  by_cases hc : (st.block_open == 0 && (last != 0 || decide (la > 0))) = true
  · simp only [hc, ↓reduceIte]
    have hc' : st.block_open = 0 ∧ (last ≠ 0 ∨ 0 < la) := by simpa using hc
    unfold bitsOf at hB
    have hlt : last.toInt ≤ 1 := by rcases hl with rfl | rfl <;> decide
    have hl0 : 0 ≤ last.toInt := by rcases hl with rfl | rfl <;> decide
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.TreesEmitP.emit_tree_SH hpb b0 b64 (by omega) (by omega)
      ZlibNg.Trees.STATIC_TREES last (by decide) (by decide) (by
        show 2 * (1 : Int32).toInt + last.toInt < 2147483648; rw [show (1 : Int32).toInt = 1 from rfl]; omega)) ?_)
    rintro _ _ q
    have hO := ZlibNgF.Proof.TreesOwed.owed_apost q
    obtain ⟨np, bb, bv, d', rfl, w, hacc, hbv, hle, hge⟩ := q
    rw [ZlibNgF.Proof.DeflatePrime.chk_ok _ (by omega) (by omega), ZlibNgF.Proof.DeflateAlloc.pure_bind_M]
    refine Sat.bind (Sat.of_eq (wrD_SH _) (Sat.bind (Sat.of_eq (wrD_SH _) ?_)))
    have e := bv_toInt32 bv hbv
    have z0 : (0 : Int32).toInt = 0 := rfl
    have s64 : (64 : Int32).toInt = 64 := rfl
    have hbo : (Int32.ofInt (1 + last.toInt)).toUInt32 ≠ 0 := by rcases hl with rfl | rfl <;> decide
    refine Sat.pure ⟨rfl, _, z, _, d', rfl, qf_bits F rfl hpb hpo w.1 (by dsimp only; rw [e]; omega)
      (Int32.le_iff_toInt_le.mpr (by rw [z0, e]; omega)) (Int32.lt_iff_toInt_lt.mpr (by rw [s64, e]; omega))
      (by dsimp only; omega)
      (Int32.le_iff_toInt_le.mpr (by dsimp only; rw [z0]; omega)), rfl, rfl, rfl, hpo, rfl, fun _ => hbo,
      fun e0 => absurd e0 hbo, by unfold bitsOf; dsimp only; rw [e]; omega, fun _ => ?_, ?_, by dsimp only; omega⟩
    · rcases hc'.2 with h1 | h1
      · exact .inr (.inl h1)
      · exact .inr (.inr (by intro e1; rw [e1] at h1; exact absurd h1 (by decide)))
    · have hq1 : ∀ x : DeflateState, x.block_open = (Int32.ofInt (1 + last.toInt)).toUInt32 → quickB fl x = 32 := by
        intro x hx; unfold quickB; rw [hx]
        rcases hl with rfl | rfl
        · rw [show (Int32.ofInt (1 + (0 : Int32).toInt)).toUInt32 = 1 from by decide]
          simp [hfl rfl]
        · rw [show (Int32.ofInt (1 + (1 : Int32).toInt)).toUInt32 = 2 from by decide]
          simp
      refine qp_next A F (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) (SH_streams _ _ _ _ _ _)
        (SH_dstate _ _ _ _ _ _) (Nat.le_refl _) (Nat.le_refl _) ?_
      refine psiS_open hla (by rcases hc'.2 with h1 | h1; exact .inl h1; exact .inr h1) rfl rfl rfl rfl rfl
        (by unfold span; dsimp only; rw [hss]; omega) ?_ hc'.1 (hq1 _ rfl)
      have := hO _ (SH_dstate _ _ _ _ _ _)
      unfold owed at this ⊢; dsimp only at this ⊢; rw [e] at this ⊢; omega
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    have hc' : st.block_open = 0 → last = 0 ∧ la = 0 := by
      intro e0
      simp only [e0, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq,
        decide_eq_true_eq, not_or] at hc
      exact ⟨Classical.not_not.mp hc.1, UInt32.le_zero_iff.mp (UInt32.not_lt.mp hc.2)⟩
    refine Sat.pure ⟨rfl, H0, z, st, d, rfl, F, rfl, rfl, rfl, hpo, rfl, fun h1 e0 => ?_,
      fun e0 => ⟨rfl, rfl, hc' e0⟩, by omega, fun h8 => .inl h8, A.mono (by split <;> omega), by omega⟩
    obtain ⟨a1, a2⟩ := hc' e0
    rcases h1 with h1 | h1
    · exact h1 a1
    · exact h1 a2

/-- `quick_start_block(s, strstart, lookahead, last, 1)` (`deflate_quick.c:53-71`) with `strstart` the state's,
`last` 0 or 1, `pending_out` at `pending_buf` and 41 bits of room. -/
theorem qsb_s {fl : Int32} {ep : Nat} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState}
    {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) (hpo : st.pending_out = st.pending_buf)
    (hB : bitsOf st + 41 ≤ 32 * st.lit_bufsize.toNat + 32) (la : UInt32) (last : Int32)
    (hl : last = 0 ∨ last = 1) (A : QP fl ep h i b st.lookahead st.strstart (SH H0 i z b st d))
    (hla : st.lookahead = la) (hfl : last = 0 → fl ≠ Z_FINISH) (hfl1 : last = 1 → fl = Z_FINISH) :
    Sat (SH H0 i z b st d) (quick_start_block (some b) st.strstart la last 1) (fun r H' =>
      (r = true → st.block_open = 1 ∧ QF h i b H' ∧ (∀ st', H'.dstate b = some st' → st'.bi_valid < 8 ∧
        st'.lookahead = st.lookahead ∧ st'.strstart = st.strstart) ∧ O0 H' i ∧
        QP fl ep h i b st.lookahead st.strstart H') ∧
      (r = false → QSB fl ep h i b z st la last H')) := by
  unfold quick_start_block
  simp only [show ((1 : Int32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have tail : ∀ {m : M Bool}, Sat (SH H0 i z b st d) m (fun r H' => r = false ∧ QSB fl ep h i b z st la last H') →
      Sat (SH H0 i z b st d) m (fun r H' => (r = true → st.block_open = 1 ∧ QF h i b H' ∧ (∀ st', H'.dstate b = some st' →
        st'.bi_valid < 8 ∧ st'.lookahead = st.lookahead ∧ st'.strstart = st.strstart) ∧ O0 H' i ∧
        QP fl ep h i b st.lookahead st.strstart H') ∧
        (r = false → QSB fl ep h i b z st la last H')) := fun q =>
    Sat.mono q fun r H' x => ⟨fun e => absurd (x.1.symm.trans e) (by decide), fun _ => x.2⟩
  rcases hl with rfl | rfl
  · simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      ZlibNgF.Proof.DeflateAlloc.pure_bind_M]
    exact tail (qsb_tail F hpo hB la 0 (.inl rfl) A hla hfl)
  · simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [ZlibNgF.Proof.DeflateAlloc.pure_bind_M]
    by_cases hb1 : st.block_open = 1
    · simp only [hb1, show ((1 : UInt32) == 1) = true from rfl, ↓reduceIte]
      have hbo : st.block_open ≠ 0 := by rw [hb1]; decide
      refine Sat.bind (Sat.mono (qeb_s F hpo hB 0 (.inl rfl) A (.inr ⟨hfl1 rfl, hb1⟩)) ?_)
      rintro r H1 ⟨-, q⟩
      obtain ⟨F1, z1, st1, hz1, hst1, hbv1, hbo1, hla1, hss1, hins1, hai1, hf, ht, A1⟩ := q hbo
      cases r with
      | true =>
        simp only [↓reduceIte]
        refine Sat.pure ⟨fun _ => ⟨trivial, F1, fun st' h' => ?_, o0_of fun z' h'' => ?_,
          by rw [← hla1, ← hss1]; exact A1⟩, fun e => by cases e⟩
        · obtain rfl := Option.some.inj (hst1.symm.trans h')
          exact ⟨hbv1, hla1, hss1⟩
        · obtain rfl := Option.some.inj (hz1.symm.trans h''); exact ht rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hp1, hpo1⟩ := hf rfl
        obtain ⟨d1, hd1⟩ := bytes_of_dstate hst1
        have e1 := ZlibNgF.Proof.DeflateReset.SH_self hz1 (dstates_of_dstate hst1 hd1) hd1
        rw [← e1] at F1 A1 ⊢
        have hB1 : bitsOf st1 + 41 ≤ 32 * st1.lit_bufsize.toNat + 32 := by
          obtain ⟨-, -, -, -, -, -, -, -, -, l1, -, -, -, -, -, -, b0, -⟩ := qf_nums F1
          have := Int32.lt_iff_toInt_lt.mp hbv1
          rw [show (8 : Int32).toInt = 8 from rfl] at this
          unfold bitsOf; rw [hp1, UInt32.toNat_zero]; omega
        rw [← hss1]
        refine Sat.mono (qsb_tail F1 hpo1 hB1 la 1 (.inr rfl) A1 (hla1.trans hla) (fun e => absurd e (by decide))) ?_
        rintro r H' ⟨rfl, H2, z2, st2, d2, rfl, F2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
        have h10 : (1 : Int32) ≠ 0 ∨ la ≠ 0 := Or.inl (by decide)
        have hp1' : st1.pending.toNat = 0 := by rw [hp1]; rfl
        refine ⟨fun e => absurd e (by decide), fun _ => ⟨H2, z2, st2, d2, rfl, F2, a1.trans hss1, a2.trans hla1,
          a3.trans hins1, a4, a5.trans hai1, fun _ => a6 h10, fun e0 => absurd e0 (a6 h10), a8,
          fun _ => .inr h10, a10, by omega⟩⟩
    · simp only [show (st.block_open == 1) = false from by simpa using hb1, Bool.false_eq_true, ↓reduceIte]
      exact tail (qsb_tail F hpo hB la 1 (.inr rfl) A hla (fun e => absurd e (by decide)))

/-! ## The main loop -/

/-- The potential of the call with flush `fl` with the locals: spent, or at most 33 bytes owed for the header of the
last block opened at an empty lookahead (`quick_start_block` with `last` and no lookahead), with no input taken yet,
few pending bytes, and the lookahead empty: the next `fill_window` takes input (and pays) or the loop breaks to the
last block (`finSlack`). -/
def QD (fl : Int32) (h : Heap) (i b : Nat) (la ss : UInt32) (H : Heap) : Prop :=
  ∃ e, QP fl e h i b la ss H ∧ (e = 0 ∨ (e ≤ 33 ∧ fl = Z_FINISH ∧ la = 0 ∧
    ∀ st, H.dstate b = some st → st.pending.toNat + 8 < 4 * st.lit_bufsize.toNat))

/-- The state at the top of a trip of the main loop: `QF`, the locals past the stale state with the same end of the
lookahead, `pending_out` at `pending_buf`, no block open only before any symbol (no lookahead, nothing pending, fewer
than 8 bits, not the last block), and 8 or more bits only with a flush or lookahead. -/
def QS (h : Heap) (i b : Nat) (flush : Int32) (last la ss : UInt32) (H : Heap) : Prop :=
  ∃ H0 z st d, H = SH H0 i z b st d ∧ QF h i b H ∧ st.strstart.toNat ≤ ss.toNat ∧
    ss.toNat + la.toNat = st.strstart.toNat + st.lookahead.toNat ∧ st.pending_out = st.pending_buf ∧
    (st.block_open = 0 → la = 0 ∧ st.pending = 0 ∧ st.bi_valid < 8 ∧ last = 0) ∧
    (8 ≤ st.bi_valid → flush ≠ Z_NO_FLUSH ∨ la ≠ 0) ∧ QD flush h i b la ss H

/-- `QS` after the room test: 41 bits of room. -/
def QT (h : Heap) (i b : Nat) (flush : Int32) (last la ss : UInt32) (H : Heap) : Prop :=
  ∃ H0 z st d, H = SH H0 i z b st d ∧ QF h i b H ∧ st.strstart.toNat ≤ ss.toNat ∧
    ss.toNat + la.toNat = st.strstart.toNat + st.lookahead.toNat ∧ st.pending_out = st.pending_buf ∧
    (st.block_open = 0 → la = 0 ∧ st.pending = 0 ∧ st.bi_valid < 8 ∧ last = 0) ∧
    (8 ≤ st.bi_valid → flush ≠ Z_NO_FLUSH ∨ la ≠ 0) ∧ bitsOf st + 41 ≤ 32 * st.lit_bufsize.toNat + 32 ∧
    QD flush h i b la ss H

/-- The state at the `break` of the main loop: no lookahead, 41 bits of room. -/
def QB (fl : Int32) (h : Heap) (i b : Nat) (last la ss : UInt32) (H : Heap) : Prop :=
  ∃ H0 z st d, H = SH H0 i z b st d ∧ QF h i b H ∧ st.strstart.toNat ≤ ss.toNat ∧
    ss.toNat = st.strstart.toNat + st.lookahead.toNat ∧ la = 0 ∧ st.pending_out = st.pending_buf ∧
    (st.block_open = 0 → st.pending = 0 ∧ st.bi_valid < 8 ∧ last = 0) ∧
    bitsOf st + 41 ≤ 32 * st.lit_bufsize.toNat + 32 ∧ z.avail_in = 0 ∧ fl ≠ Z_NO_FLUSH ∧ QD fl h i b la ss H

/-- The invariant of the main loop with `static_emit` over `(strstart, lookahead, exit)`. -/
def QIs (h : Heap) (i b : Nat) (flush : Int32) (last : UInt32) (v : UInt32 × UInt32 × QuickExit) (H : Heap) :
    Prop :=
  match v.2.2 with
  | .cont => QS h i b flush last v.2.1 v.1 H
  | .brk => QB flush h i b last v.2.1 v.1 H
  | .ret r => StratPost h (some i) flush r H

theorem qs_of_qr {h H : Heap} {i b B : Nat} {flush : Int32} {last la ss : UInt32} (R : QR flush h i b B la ss H)
    (hn : flush = Z_NO_FLUSH → la ≠ 0) : QS h i b flush last la ss H := by
  obtain ⟨H0, z, st, d, rfl, F, a1, a2, a3, a4, -, A⟩ := R
  refine ⟨H0, z, st, d, rfl, F, a1, a2, a3, fun e => absurd e a4, fun _ => ?_, ⟨0, A, .inl rfl⟩⟩
  by_cases hf : flush = Z_NO_FLUSH
  · exact .inr (hn hf)
  · exact .inl hf

/-- `s->lookahead = lookahead; s->strstart = strstart;` under `QF` with the locals past the state. -/
theorem qf_wb {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (F : QF h i b (SH H0 i z b st d)) (hss : st.strstart.toNat ≤ ss.toNat)
    (hsum : ss.toNat + la.toNat = st.strstart.toNat + st.lookahead.toNat) :
    QF h i b (SH H0 i z b (FS st la ss) d) := by
  have hbs0 := F.bs0 st (SH_dstate _ _ _ _ _ _)
  have hb0 : (0 : Int) ≤ st.block_start.toInt := by
    have := Int32.le_iff_toInt_le.mp hbs0; simpa using this
  refine qf_SH F (fun al' _ c' => ?_) rfl rfl (F.sym st (SH_dstate _ _ _ _ _ _)) hbs0 (StratKeeps.refl _)
  have hws65 : st.window_size.toNat ≤ 65536 := ZlibNgF.Proof.DeflatePsi.window_size_le c'
  have hlk : ss.toNat + la.toNat ≤ st.window_size.toNat := by have := c'.look; simp only [dview] at this; omega
  exact DCore.of_heap (by rw [SH_bytes, SH_bytes]) (dcore_set c' ss la st.insert st.block_start
    hlk
    (by have := c'.bstart; simp only [dview] at this ⊢; omega)
    (by have := UInt32.le_iff_toNat_le.mp c'.ins; simp only [dview] at this ⊢;
        exact UInt32.le_iff_toNat_le.mpr (by omega))
    (by omega))

/-- `quick_flush_pending(s, 1)` (`deflate_quick.c:75-84`) at the top of a trip: on 0 the trip goes on with 41 bits of
room; on 1 (a full output after `flush_pending`) fewer than 8 bits wait. -/
theorem qfp_s {h H : Heap} {i b : Nat} {flush : Int32} {last la ss : UInt32} (I : QS h i b flush last la ss H) :
    Sat H (quick_flush_pending (some b) 1) (fun r H1 =>
      (r = false → QT h i b flush last la ss H1 ∧ avIn H1 i = avIn H i) ∧
      (r = true → ∃ H0 z st d, H1 = SH H0 i z b st d ∧ QF h i b H1 ∧ st.strstart.toNat ≤ ss.toNat ∧
        ss.toNat + la.toNat = st.strstart.toNat + st.lookahead.toNat ∧ st.bi_valid < 8 ∧
        (st.block_open = 0 → last = 0) ∧ O0 H1 i ∧ QP flush 0 h i b la ss H1)) := by
  obtain ⟨H0, z, st, d, rfl, F, hss, hsum, hpo, hbo, h8, D⟩ := I
  obtain ⟨-, -, -, -, -, -, -, -, -, l1, l2, pbs, -, -, -, -, b0, b64, -, -, hroom, -⟩ := qf_nums F
  unfold quick_flush_pending
  simp only [show ((1 : Int32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have hp8 : (st.pending + 8).toNat = st.pending.toNat + 8 := by rw [UInt32.toNat_add]; simp; omega
  by_cases hc : st.pending + 8 ≥ st.pending_buf_size
  · simp only [hc, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (strmOf_qf F) ?_)
    refine Sat.bind (Sat.mono (qf_flush F) ?_)
    rintro _ H4 ⟨F4, z5, st5, z4, st4, hz5, hst5, hz4, hst4, hste, hbv4, hai, hout, hle4, hOw⟩
    rw [SH_streams] at hz5; obtain rfl := Option.some.inj hz5
    rw [SH_dstate] at hst5; obtain rfl := Option.some.inj hst5
    refine Sat.bind (Sat.of_eq (strmOf_qf F4) (Sat.bind (Sat.of_eq (ZlibNgF.Proof.DeflateInit.rdZ_app hz4 _) ?_)))
    obtain ⟨ea, A, hd⟩ := D
    have hea : ea = 0 := by
      rcases hd with h0 | ⟨-, -, -, hsm⟩
      · exact h0
      · exfalso
        have h1 := hsm st (SH_dstate _ _ _ _ _ _)
        have h2 := UInt32.le_iff_toNat_le.mp hc
        omega
    subst hea
    have A4 : QP flush 0 h i b la ss H4 := by
      refine qp_next A F (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) hz4 hst4 hle4
        (by rw [hai]; exact Nat.le_refl _) ?_
      rw [hai, Nat.sub_self, Nat.mul_zero]
      have hbs4 : st4.block_start = st.block_start := by rw [hste]
      have g := psiS_gen (f := flush) (st := FS st la ss) (st' := FS st4 la ss) (k := 0)
        (out := z.avail_out.toNat - z4.avail_out.toNat) (q := 0) (o := 0) rfl
        (by unfold span; dsimp only; rw [hbs4]; omega) (by show st4.sym_next = st.sym_next; rw [hste])
        (by show st4.match_available = st.match_available; rw [hste]) (by show st4.status = st.status; rw [hste])
        (by show st4.wrap = st.wrap; rw [hste])
        (Nat.le_of_eq (by rw [Nat.add_zero]; unfold quickB; dsimp only; rw [show st4.block_open = st.block_open by rw [hste]]))
        (by show owed st4 + _ ≤ owed st + 0; omega)
      omega
    obtain ⟨d4, hd4⟩ := bytes_of_dstate hst4
    have e4 := ZlibNgF.Proof.DeflateReset.SH_self hz4 (dstates_of_dstate hst4 hd4) hd4
    have hss4 : st4.strstart = st.strstart := by rw [hste]
    have hla4 : st4.lookahead = st.lookahead := by rw [hste]
    have hbo4 : st4.block_open = st.block_open := by rw [hste]
    have hlb4 : st4.lit_bufsize = st.lit_bufsize := by rw [hste]
    refine Sat.pure ⟨fun hr => ?_, fun hr => ⟨H4, z4, st4, d4, e4.symm, F4, by rw [hss4]; exact hss,
      by rw [hss4, hla4]; exact hsum, hbv4, fun e0 => (hbo (hbo4 ▸ e0)).2.2.2,
      o0_of (fun z' h'' => by obtain rfl := Option.some.inj (hz4.symm.trans h''); simpa using hr), A4⟩⟩
    have ha : z4.avail_out ≠ 0 := fun e => by simp [e] at hr
    obtain ⟨hp4, hpo4⟩ := hout ha
    have h84 := Int32.lt_iff_toInt_lt.mp hbv4
    rw [show (8 : Int32).toInt = 8 from rfl] at h84
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, b04, -⟩ := qf_nums (show QF h i b (SH H4 i z4 b st4 d4) by rw [e4]; exact F4)
    refine ⟨⟨H4, z4, st4, d4, e4.symm, F4, by rw [hss4]; exact hss, by rw [hss4, hla4]; exact hsum, hpo4,
      fun e0 => ?_, fun e8 => absurd e8 (Int32.not_le.mpr hbv4), ?_, ⟨0, A4, .inl rfl⟩⟩, ?_⟩
    · obtain ⟨a1, -, -, a4⟩ := hbo (hbo4 ▸ e0)
      exact ⟨a1, hp4, hbv4, a4⟩
    · unfold bitsOf; rw [hp4, hlb4, UInt32.toNat_zero]; omega
    · simp only [avIn, hz4, SH_streams]; rw [hai]
  · simp only [hc, ↓reduceIte]
    have hlt : st.pending.toNat + 8 < 4 * st.lit_bufsize.toNat := by
      have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hc); omega
    refine Sat.pure ⟨fun _ => ⟨⟨H0, z, st, d, rfl, F, hss, hsum, hpo, hbo, h8, by unfold bitsOf; omega, D⟩, rfl⟩,
      fun e => by cases e⟩

/-- The end of a trip from `strstart` / `lookahead` with at least one byte, under `QR` with 31 bits of room: the match
part or a literal. -/
theorem tail_s {h H1 : Heap} {i b wo B : Nat} {la1 ss1 : UInt32} {flush : Int32} {last : UInt32} {Mb : Nat}
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (R : QR flush h i b B la1 ss1 H1)
    (hB : 31 ≤ B) (hl : 1 ≤ la1.toNat) (hnf : flush = Z_NO_FLUSH → 262 ≤ la1.toNat)
    (hM : avIn H1 i + la1.toNat ≤ Mb)
    (k : UInt32 → Option (UInt32 × UInt32 × QuickExit) → M (UInt32 × UInt32 × QuickExit))
    (hk1 : ∀ sv r, k sv (some r) = pure r)
    (hk2 : ∀ sv, k sv none = (do
        let x ← quick_emit_lit (some b) sv.toUInt8 ss1 la1 1
        if x.1 = true then pure (x.2.1, x.2.2, QuickExit.ret BlockState.need_more)
        else pure (x.2.1, x.2.2, QuickExit.cont))) :
    Sat H1 ((Ptr.ref (BRef.heap b) wo).add (ss1.toNat : Int) >>= fun p => memread4 p >>= fun sv =>
      quick_try_match (some b) (.ref (.heap b) wo) 1 ss1 la1 sv >>= k sv)
      (fun v H2 => QIs h i b flush last v H2 ∧ ZlibNgF.Proof.QuickP.QM i v H2 < Mb + 1) := by
  have R0 := R
  obtain ⟨H0, z, st, d, rfl, F, -, hsum, -⟩ := R0
  obtain ⟨-, -, hk, -⟩ := qf_win F hw0 hsum
  refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH ss1.toNat (by omega)) ?_)
  obtain ⟨sv, esv⟩ := ZlibNgF.Proof.WinBase.memread4_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
    (off := wo + ss1.toNat) (by omega)
  refine Sat.bind (Sat.of_eq esv ?_)
  refine Sat.bind (Sat.mono (smatch_s hw0 R hB sv) ?_)
  rintro o H2 ⟨hnone, hsome⟩
  cases o with
  | some v =>
    obtain ⟨hc, R2, hm, h4⟩ := hsome v rfl
    rw [hk1]
    obtain ⟨ss2, la2, ex⟩ := v
    dsimp only at hc R2 hm h4
    subst hc
    refine Sat.pure ⟨qs_of_qr R2 fun e => ?_, ?_⟩
    · have := h4 (hnf e); intro e0; simp only at e0; rw [e0] at this; simp at this
    · simp only [ZlibNgF.Proof.QuickP.QM]; rw [avIn_SH] at hm hM; omega
  | none =>
    obtain ⟨R2, ha2⟩ := hnone rfl
    rw [hk2]
    refine Sat.bind (Sat.mono (qlit_s R2 (by omega) hl sv.toUInt8) ?_)
    rintro ⟨r, ss2, la2⟩ H3 ⟨he, R3, ha3⟩
    obtain ⟨rfl, rfl, rfl⟩ : r = false ∧ ss2 = ss1 + 1 ∧ la2 = la1 - 1 := by simpa using he
    have hla2 : (la1 - 1).toNat = la1.toNat - 1 :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using hl))
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Sat.pure ⟨qs_of_qr R3 fun e => ?_, ?_⟩
    · have := hnf e; intro e0; simp only at e0; have := congrArg UInt32.toNat e0; simp only [UInt32.toNat_zero] at this; omega
    · show avIn H3 i + (la1 - 1).toNat + 1 < Mb + 1
      rw [avIn_SH] at hM ha2; omega

/-- One trip of the main loop with `static_emit` (`quick_trip`). -/
theorem trip_s {h H : Heap} {i b wo : Nat} {flush : Int32} {last la ss : UInt32}
    (hE : ∀ st0, h.dstate b = some st0 → st0.level = 1 ∧ st0.strategy = Z_FIXED)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (hlast : last = 0 ∨ last = 1)
    (hlf : last ≠ 0 → flush ≠ Z_NO_FLUSH) (hlF : last = 1 → flush = Z_FINISH)
    (hl0F : last = 0 → flush ≠ Z_FINISH) (I : QS h i b flush last la ss H) :
    Sat H (quick_trip (some b) (.ref (.heap b) wo) flush last 1 ss la) (fun v H2 =>
      QIs h i b flush last v H2 ∧ ZlibNgF.Proof.QuickP.QM i v H2 < avIn H i + la.toNat + 1) := by
  unfold quick_trip
  refine Sat.bind (Sat.mono (qfp_s I) ?_)
  rintro r H1 ⟨hf, ht⟩
  cases r with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨H0, z, st, d, rfl, F, hss, hsum, hbv, hbo, ho, A⟩ := ht rfl
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    have F1 := qf_wb F hss hsum
    have ho1 : O0 (SH H0 i z b (FS st la ss) d) i := o0_of fun z' h'' => by
      rw [SH_streams] at h''; cases h''; exact ho z ⟨i, rfl, SH_streams _ _ _ _ _ _⟩
    have fin : ∀ c : Bool, (c = true → last ≠ 0 ∧ st.block_open = 0) →
        Sat (SH H0 i z b (FS st la ss) d)
          (pure (ss, la, QuickExit.ret (if c = true then BlockState.finish_started else BlockState.need_more)))
          (fun v H2 => QIs h i b flush last v H2 ∧ ZlibNgF.Proof.QuickP.QM i v H2 < avIn H i + la.toNat + 1) := by
      intro c hc
      cases c with
      | true => exact absurd (hbo (hc rfl).2) (hc rfl).1
      | false =>
        refine Sat.pure ⟨qf_post F1 flush .need_more (exitIO_nm ho1) hE (fun st' h' => ?_)
          (qp_post F1 (qp_wb A) (fun st' h' => by rw [SH_dstate] at h'; cases h'; exact ⟨rfl, rfl⟩) .need_more
            (Nat.zero_le _)),
          by simp [ZlibNgF.Proof.QuickP.QM]⟩
        obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h')
        exact ⟨(fun e => by rcases e with e | e <;> cases e), (fun e => by rcases e with e | e <;> cases e),
          fun e8 => absurd e8 (Int32.not_le.mpr hbv)⟩
    by_cases hl : (last != 0) = true
    · simp only [hl, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (strmOf_qf F1) (Sat.bind (Sat.of_eq
        (ZlibNgF.Proof.DeflateInit.rdZ_app (SH_streams _ _ _ _ _ _) _) ?_)))
      have hl' : last ≠ 0 := by simpa using hl
      split
      · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        split
        · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
          simp only [ZlibNgF.Proof.DeflateAlloc.pure_bind_M]
          exact fin _ fun e => ⟨hl', by simpa using e⟩
        · simp only [ZlibNgF.Proof.DeflateAlloc.pure_bind_M]
          exact fin false fun e => by cases e
      · simp only [ZlibNgF.Proof.DeflateAlloc.pure_bind_M]
        exact fin false fun e => by cases e
    · simp only [hl, Bool.false_eq_true, ↓reduceIte, ZlibNgF.Proof.DeflateAlloc.pure_bind_M]
      exact fin false fun e => by cases e
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨T, ha1⟩ := hf rfl
    simp only [QuickExit.isCont]
    by_cases hl : la < MIN_LOOKAHEAD
    · simp only [hl, ↓reduceIte]
      have hl' : la.toNat < 262 := by
        simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using UInt32.lt_iff_toNat_lt.mp hl
      obtain ⟨H0, z, st, d, rfl, F, hss, hsum, hpo, hbo, h8, hB, ea, A, hd⟩ := T
      refine Sat.bind (Sat.mono (qf_fill F A hss hsum hl') fun _ H1 h1 => Sat.bind (Sat.mono h1 ?_))
      rintro _ H2 ⟨H3, z', st0', d', rfl, F2, fws, hmono, hsum2, hne, hend, A2, A2'⟩
      refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.bind (Sat.of_eq (rdD_SH _) ?_)))
      simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      let st' : DeflateState := { st0' with block_start := st0'.strstart.toInt32 }
      have A3 : 1 ≤ st'.lookahead.toNat → QP flush 0 h i b st'.lookahead st'.strstart (SH H3 i z' b st' d') := by
        intro h1
        rcases hd with rfl | ⟨h33, -, hla0, -⟩
        · exact A2
        · refine A2' (hne fun e => ?_) h33
          dsimp only [st'] at h1; rw [e, hla0] at h1; simp at h1
      have hz0 : flush ≠ Z_FINISH → ea = 0 := fun hf => by
        rcases hd with h0 | ⟨-, hF, -⟩
        · exact h0
        · exact absurd hF hf
      obtain ⟨fe, ms, pl, ss', bs', ins', sl, la', ih, hw', hste⟩ := fws
      have e1 : st'.pending = st.pending ∧ st'.bi_valid = st.bi_valid ∧ st'.pending_out = st.pending_out ∧
          st'.pending_buf = st.pending_buf ∧ st'.block_open = st.block_open ∧
          st'.lit_bufsize = st.lit_bufsize :=
        ⟨congrArg (·.pending) hste, congrArg (·.bi_valid) hste, congrArg (·.pending_out) hste,
          congrArg (·.pending_buf) hste, congrArg (·.block_open) hste, congrArg (·.lit_bufsize) hste⟩
      obtain ⟨ep, ebv, epo, epb, ebo, elb⟩ := e1
      have hpo2 : st'.pending_out = st'.pending_buf := by rw [epo, epb]; exact hpo
      have hB2 : bitsOf st' + 41 ≤ 32 * st'.lit_bufsize.toNat + 32 := by unfold bitsOf at hB ⊢; rw [ep, ebv, elb]; exact hB
      have hav : avIn (SH H3 i z' b st' d') i + st'.lookahead.toNat ≤ avIn H i + la.toNat := by
        rw [← ha1, avIn_SH, avIn_SH]; exact hsum2
      by_cases hx : (decide (st0'.lookahead < MIN_LOOKAHEAD) && flush == Z_NO_FLUSH) = true
      · simp only [hx, ↓reduceIte]
        have hfn : flush = Z_NO_FLUSH := by simp at hx; exact hx.2
        have hx2 : st0'.lookahead.toNat < 262 := by
          simp at hx; have hx' : st0'.lookahead < 262 := by simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using hx.1
          exact UInt32.lt_iff_toNat_lt.mp hx'
        refine Sat.pure ⟨qf_post F2 flush .need_more (by rw [hfn]; exact exitIO_nmNF (cf_fill hend hx2)) hE
          (fun st2 h2 => ?_) (qp_post F2 A2 (fun st2 h2 => by rw [SH_dstate] at h2; cases h2; exact ⟨rfl, rfl⟩)
            .need_more (by rw [hz0 (by rw [hfn]; decide)]; exact Nat.zero_le _)),
          by simp [ZlibNgF.Proof.QuickP.QM]⟩
        obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
        refine ⟨(fun e => by rcases e with e | e <;> cases e), (fun e => by rcases e with e | e <;> cases e),
          fun e8 => ?_⟩
        rw [ebv] at e8
        rcases h8 e8 with h | h
        · exact absurd hfn h
        · intro e0
          have : la.toNat = 0 := by rw [e0] at hmono; simpa using hmono
          exact h (UInt32.toNat_inj.mp (by simpa using this))
      simp only [Bool.not_eq_true] at hx; simp only [hx, Bool.false_eq_true, ↓reduceIte]
      have hnf : flush = Z_NO_FLUSH → 262 ≤ st'.lookahead.toNat := by
        intro e
        simp only [e, beq_self_eq_true, Bool.and_true, decide_eq_false_iff_not] at hx
        simpa [st', MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hx)
      by_cases hz : (st0'.lookahead == 0) = true
      · simp only [hz, ↓reduceIte]
        have hz' : st'.lookahead = 0 := by simpa [st'] using hz
        have hai0 : z'.avail_in = 0 := hend.resolve_left (by rw [show st0'.lookahead = 0 from hz']; decide)
        refine Sat.pure ⟨⟨H3, z', st', d', rfl, F2, Nat.le_refl _, by rw [hz']; simp [st'], hz', hpo2,
          fun e0 => ?_, hB2, hai0, fun e => (by rw [show st0'.lookahead = 0 from hz', e] at hx; revert hx; decide), ⟨ea, A2, ?_⟩⟩,
          by simp [ZlibNgF.Proof.QuickP.QM]⟩
        · obtain ⟨-, a2, a3, a4⟩ := hbo (ebo ▸ e0)
          exact ⟨ep.trans a2, by rw [ebv]; exact a3, a4⟩
        · rcases hd with h0 | ⟨h33, hF, -, hsm⟩
          · exact .inl h0
          · refine .inr ⟨h33, hF, hz', fun st2 h2 => ?_⟩
            rw [SH_dstate] at h2; cases h2
            rw [ep, elb]; exact hsm st (SH_dstate _ _ _ _ _ _)
      simp only [Bool.not_eq_true] at hz; simp only [hz, Bool.false_eq_true, ↓reduceIte]
      have hz' : 1 ≤ st'.lookahead.toNat := by
        have h0 : st'.lookahead ≠ 0 := by simpa [st'] using hz
        rcases Nat.eq_zero_or_pos st'.lookahead.toNat with e | e
        · exact absurd (UInt32.toNat_inj.mp (by simpa using e)) h0
        · exact e
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      have F2' := F2
      by_cases hb0 : (st0'.block_open == 0) = true
      · simp only [hb0, ↓reduceIte]
        have hb0' : st'.block_open = 0 := by simpa [st'] using hb0
        have hl32 : last.toInt32 = 0 ∨ last.toInt32 = 1 := by rcases hlast with rfl | rfl <;> decide
        have hl32a : last.toInt32 = 0 → flush ≠ Z_FINISH := fun e => hl0F (by
          rcases hlast with rfl | rfl
          · rfl
          · exact absurd e (by decide))
        have hl32b : last.toInt32 = 1 → flush = Z_FINISH := fun e => hlF (by
          rcases hlast with rfl | rfl
          · exact absurd e (by decide)
          · rfl)
        refine Sat.bind (Sat.mono (qsb_s F2 hpo2 hB2 st'.lookahead last.toInt32 hl32 (A3 hz') rfl hl32a hl32b) ?_)
        rintro r H4 ⟨q1, q2⟩
        cases r with
        | true => exact absurd ((q1 rfl).1) (by rw [hb0']; decide)
        | false =>
          obtain ⟨H5, z5, st5, d5, rfl, F5, a1, a2, a3, a4, a5, a6, -, a8, -, a10, -⟩ := q2 rfl
          have hnz : ¬ (st'.lookahead = 0 ∧ last.toInt32 ≠ 0) := fun ⟨e, _⟩ => by rw [e] at hz'; simp at hz'
          rw [ite_eq_right hnz, a1, a2] at a10
          have R : QR flush h i b 38 st'.lookahead st'.strstart (SH H5 i z5 b st5 d5) :=
            ⟨H5, z5, st5, d5, rfl, F5, by rw [a1]; exact Nat.le_refl _, by rw [a1, a2], a4,
              a6 (.inr (fun e => by rw [e] at hz'; simp at hz')), a8, a10⟩
          exact tail_s hw0 R (by decide) hz' hnf (by rw [avIn_SH, a5, ← avIn_SH H3 i z' b st' d']; exact hav) _
            (fun _ _ => rfl) (fun _ => rfl)
      · simp only [Bool.not_eq_true] at hb0; simp only [hb0, Bool.false_eq_true, ↓reduceIte]
        have hb0' : st'.block_open ≠ 0 := by simpa using hb0
        have R : QR flush h i b 41 st'.lookahead st'.strstart (SH H3 i z' b st' d') :=
          ⟨H3, z', st', d', rfl, F2, Nat.le_refl _, rfl, hpo2, hb0', hB2, A3 hz'⟩
        exact tail_s hw0 R (by decide) hz' hnf hav _ (fun _ _ => rfl) (fun _ => rfl)
    · simp only [hl, ↓reduceIte]
      have hl' : 262 ≤ la.toNat := by
        simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hl)
      obtain ⟨H0, z, st, d, rfl, F, hss, hsum, hpo, hbo, h8, hB, ea, A, hd⟩ := T
      have hbo' : st.block_open ≠ 0 := fun e0 => by rw [(hbo e0).1] at hl'; simp at hl'
      have hea : ea = 0 := by
        rcases hd with h0 | ⟨-, -, hla0, -⟩
        · exact h0
        · rw [hla0] at hl'; simp at hl'
      subst hea
      have R : QR flush h i b 41 la ss (SH H0 i z b st d) := ⟨H0, z, st, d, rfl, F, hss, hsum, hpo, hbo', hB, A⟩
      exact tail_s hw0 R (by decide) (by omega) (fun _ => hl') (by rw [ha1]; exact Nat.le_refl _) _ (fun _ _ => rfl) (fun _ => rfl)

/-- `s->insert = v` with `v <= strstart` under `QF`. -/
theorem qf_ins {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : QF h i b (SH H0 i z b st d)) (v : UInt32) (hv : v ≤ st.strstart) :
    QF h i b (SH H0 i z b { st with insert := v } d) :=
  qf_SH F (fun _ _ c => DCore.of_heap (by rw [SH_bytes, SH_bytes])
    (dcore_set c st.strstart st.lookahead v st.block_start c.look c.bstart hv c.bs_lo)) rfl rfl
    (F.sym st (SH_dstate _ _ _ _ _ _)) (F.bs0 st (SH_dstate _ _ _ _ _ _)) (StratKeeps.refl _)

/-- `deflate_quick` on a stream at level 1 with `Z_FIXED` (`deflate_quick_impl(s, flush, 1)`) keeps the strategy
frame. -/
theorem quick_static_ok :
    StratOkP (fun st => TableAt 1 1 st ∧ st.strategy = Z_FIXED) deflate_quick := by
  intro h s b flush P hsb hE
  obtain ⟨z, ⟨i, rfl, hz⟩, hb⟩ := hsb
  have hE' : ∀ b' st, DStateIs h (some i) b' st → st.level = 1 ∧ st.strategy = Z_FIXED := fun b' st hd => by
    obtain ⟨⟨h1, h2, -, -⟩, h3⟩ := hE b' st hd
    exact ⟨Int32.le_antisymm h2 h1, h3⟩
  obtain ⟨st, hst, hp0, hsy, F0⟩ := qf_entry P hz hb hE'
  have hE0 : ∀ st0, h.dstate b = some st0 → st0.level = 1 ∧ st0.strategy = Z_FIXED := fun st0 h0 =>
    hE' b st0 ⟨i, z, rfl, hz, hb, h0⟩
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  have eSH := ZlibNgF.Proof.DeflateReset.SH_self hz (dstates_of_dstate hst hd) hd
  have F : QF h i b (SH h i z b st d) := by rw [eSH]; exact F0
  obtain ⟨wo, po, ho, pbo, L, hpb, -, -, -, l1, l2, -, -, -, -, -, b0, b64, -, -, -, -, -⟩ := qf_nums F
  have hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo) := fun st0 h0 => by
    rw [hst] at h0; cases h0; exact L.win
  have hpo : st.pending_out = st.pending_buf := by
    obtain ⟨z1, st1, al, hz1, -, hst1, -, c⟩ := F0.live
    obtain rfl : st = st1 := Option.some.inj (hst.symm.trans hst1)
    exact c.pout hp0
  have hB : bitsOf st + 41 ≤ 32 * st.lit_bufsize.toNat + 32 := by unfold bitsOf; rw [hp0, UInt32.toNat_zero]; omega
  suffices S : Sat (SH h i z b st d) (deflate_quick (some b) flush) (fun bs h' => StratPost h (some i) flush bs h') by
    rw [eSH] at S
    obtain ⟨bs, h', e, q⟩ := S
    exact ⟨bs, h', e, q⟩
  unfold deflate_quick
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  have hfx : (st.strategy == Z_FIXED) = true := by simpa using (hE0 st hst).2
  simp only [hfx, ↓reduceIte]
  unfold deflate_quick_impl
  refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.bind (Sat.of_eq (rdD_SH _) ?_)))
  simp only []
  have hlast : (if (flush == Z_FINISH) = true then (1 : UInt32) else 0) = 0 ∨
      (if (flush == Z_FINISH) = true then (1 : UInt32) else 0) = 1 := by split <;> simp
  have hlf : (if (flush == Z_FINISH) = true then (1 : UInt32) else 0) ≠ 0 → flush ≠ Z_NO_FLUSH := by
    split
    · rename_i hf; intro _ e; rw [e] at hf; exact absurd hf (by decide)
    · intro e; exact absurd rfl e
  have hlF : (if (flush == Z_FINISH) = true then (1 : UInt32) else 0) = 1 → flush = Z_FINISH := by
    split
    · rename_i hf; intro _; simpa using hf
    · intro e; exact absurd e (by decide)
  have hl0F : (if (flush == Z_FINISH) = true then (1 : UInt32) else 0) = 0 → flush ≠ Z_FINISH := by
    split
    · intro e; exact absurd e (by decide)
    · rename_i hf; intro _ e; exact hf (by rw [e]; decide)
  generalize (if (flush == Z_FINISH) = true then (1 : UInt32) else 0) = last at hlast hlf hlF hl0F ⊢
  have hl32 : last.toInt32 = 0 ∨ last.toInt32 = 1 := by rcases hlast with rfl | rfl <;> decide
  have hl32a : last.toInt32 = 0 → flush ≠ Z_FINISH := fun e => hl0F (by
    rcases hlast with rfl | rfl
    · rfl
    · exact absurd e (by decide))
  have hl32b : last.toInt32 = 1 → flush = Z_FINISH := fun e => hlF (by
    rcases hlast with rfl | rfl
    · exact absurd e (by decide)
    · rfl)
  have A0 : QP flush 0 h i b st.lookahead st.strstart (SH h i z b st d) := by
    rw [eSH]; exact qp_entry flush hst
  refine Sat.bind (Sat.mono (qsb_s F hpo hB st.lookahead last.toInt32 hl32 A0 rfl hl32a hl32b) ?_)
  rintro r H1 ⟨q1, q2⟩
  cases r with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨-, F1, hb1, ho1, A1⟩ := q1 rfl
    refine Sat.pure (qf_post F1 flush .need_more (exitIO_nm ho1) hE0 (fun st' h' => ?_)
      (qp_post F1 A1 (fun st' h' => ⟨(hb1 st' h').2.1, (hb1 st' h').2.2⟩) .need_more (Nat.zero_le _)))
    exact ⟨(fun e => by rcases e with e | e <;> cases e), (fun e => by rcases e with e | e <;> cases e),
      fun e8 => absurd e8 (Int32.not_le.mpr (hb1 st' h').1)⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨H5, z5, st5, d5, rfl, F5, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := q2 rfl
    have hsum5 : st.strstart.toNat + st.lookahead.toNat = st5.strstart.toNat + st5.lookahead.toNat := by
      rw [a1, a2]
    obtain ⟨hwin5, -⟩ := qf_win F5 hw0 hsum5
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    rw [hwin5]
    refine Sat.bind (Sat.pure ?_)
    obtain ⟨-, -, -, -, -, h8s⟩ := hsy
    have hl0 : last.toInt32 = 0 → last = 0 := by rcases hlast with rfl | rfl <;> decide
    have I0 : QS h i b flush last st.lookahead st.strstart (SH H5 i z5 b st5 d5) := by
      refine ⟨H5, z5, st5, d5, rfl, F5, by rw [a1]; exact Nat.le_refl _, hsum5, a4, fun e0 => ?_, fun e8 => ?_, ?_⟩
      · obtain ⟨e1, e2, e3, e4⟩ := a7 e0
        refine ⟨e4, by rw [e1, hp0], ?_, hl0 e3⟩
        rw [e2]
        exact Int32.not_le.mp fun e => (h8s e).2.2 e4
      · rcases a9 e8 with e | e | e
        · exact .inr (h8s e).2.2
        · exact .inl (hlf fun e0 => e (by rw [e0]; decide))
        · exact .inr e
      · obtain ⟨-, -, -, -, -, -, -, -, -, l15, -⟩ := qf_nums F5
        rw [a1, a2] at a10
        by_cases hc : st.lookahead = 0 ∧ last.toInt32 ≠ 0
        · rw [ite_eq_left hc] at a10
          refine ⟨_, a10, .inr ⟨by omega, hl32b (by rcases hl32 with e | e; exact absurd e hc.2; exact e), hc.1,
            fun st2 h2 => ?_⟩⟩
          rw [SH_dstate] at h2; cases h2
          have : st.pending.toNat = 0 := by rw [hp0]; rfl
          omega
        · rw [ite_eq_right hc] at a10; exact ⟨0, a10, .inl rfl⟩
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cwhileH (QIs h i b flush last) (ZlibNgF.Proof.QuickP.QM i)
      (fun v H => QIs h i b flush last v H ∧ v.2.2.isCont = false) ?_ (s := (st.strstart, st.lookahead, .cont))
      I0 ?_) ?_)
    · rintro ⟨ss, la, ex⟩ H hI
      refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, hc⟩⟩
      cases ex with
      | cont => exact Sat.mono (trip_s hE0 hw0 hlast hlf hlF hl0F hI) fun v H2 ⟨a, m⟩ => ⟨a, by
          simp only [ZlibNgF.Proof.QuickP.QM]; exact m⟩
      | brk => cases hc
      | ret r => cases hc
    · have := ZlibNgF.Proof.Strategy.avIn_lt (SH H5 i z5 b st5 d5) i
      have := UInt32.toNat_lt st.lookahead
      simp only [ZlibNgF.Proof.QuickP.QM, fuel]; omega
    rintro ⟨ss, la, ex⟩ H ⟨hI, hc⟩
    cases ex with
    | cont => cases hc
    | ret r => exact Sat.pure hI
    | brk =>
      obtain ⟨H0, z1, st1, d1, rfl, F1, hss1, hsum1, hla0, hpo1, hbo1, hB1, hai0, hnf0, ea, A1, hd1⟩ := hI
      dsimp only at hss1 hsum1 hla0 A1 hd1
      subst hla0
      have hea33 : ea ≤ 33 := by rcases hd1 with h0 | ⟨h0, -⟩ <;> omega
      simp only []
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      have F2 := qf_wb (la := 0) F1 hss1 (by simpa using hsum1)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      have hv : (if ss < STD_MIN_MATCH - 1 then ss else STD_MIN_MATCH - 1) ≤ (FS st1 0 ss).strstart := by
        show _ ≤ ss
        split
        · exact UInt32.le_refl _
        · rename_i hs; exact UInt32.not_lt.mp hs
      have F3 := qf_ins F2 _ hv
      have A3 := qp_state (st' := { FS st1 0 ss with insert := if ss < STD_MIN_MATCH - 1 then ss else STD_MIN_MATCH - 1 })
        (la' := 0) (ss' := ss) (d' := d1) A1 (Nat.le_of_eq rfl)
      have fin : ∀ (lst : Int32) (b1 b2 : BlockState),
          (lst = 0 ∧ b1 = .need_more ∧ b2 = .block_done) ∨ (lst = 1 ∧ b1 = .finish_started ∧ b2 = .finish_done) →
          (lst = 1 → flush = Z_FINISH) → (lst = 0 → ea = 0) → (b2 = .block_done → flush ≠ Z_FINISH) →
          Sat (SH H0 i z1 b { FS st1 0 ss with insert := if ss < STD_MIN_MATCH - 1 then ss else STD_MIN_MATCH - 1 } d1)
            (do
              if ← quick_end_block (some b) ss lst 1 then return b1
              return b2) (fun r H' => StratPost h (some i) flush r H') := by
        intro lst b1 b2 hc hlF1 hea hbd
        have hfs : ∀ bs, (bs = b1 ∨ bs = b2) → ea ≤ finSlack bs := by
          intro bs hbs
          rcases hc with ⟨h0, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
          · rw [hea h0]; exact Nat.zero_le _
          · rcases hbs with rfl | rfl <;> (unfold finSlack; simp; omega)
        have hl : lst = 0 ∨ lst = 1 := by rcases hc with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e]
        have hF2 : b2 = .finish_started ∨ b2 = .finish_done → flush = Z_FINISH := fun e => by
          rcases hc with ⟨-, -, rfl⟩ | ⟨e1, -, -⟩
          · rcases e with e | e <;> cases e
          · exact hlF1 e1
        have hF1 : b1 = .finish_started ∨ b1 = .finish_done → flush = Z_FINISH := fun e => by
          rcases hc with ⟨-, rfl, -⟩ | ⟨e1, -, -⟩
          · rcases e with e | e <;> cases e
          · exact hlF1 e1
        have hn2 : ¬ (b2 = .need_more ∨ b2 = .finish_started) := fun e => by
          rcases hc with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rcases e with e | e <;> cases e
        refine Sat.bind (Sat.mono (qeb_s F3 hpo1 hB1 lst hl A3 (.inl rfl)) ?_)
        rintro r H' ⟨q0, q1⟩
        by_cases hb : st1.block_open = 0
        · obtain ⟨rfl, rfl⟩ := q0 hb
          obtain ⟨a1, a2, -⟩ := hbo1 hb
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Sat.pure (qf_post F3 flush b2 ⟨fun _ => ?_, hF2, fun _ e => absurd e hn2,
            fun e => ⟨hnf0, hbd e, by rw [avIn_SH, hai0]; rfl⟩⟩ hE0 (fun st' h' => ?_)
            (qp_post F3 A3 (fun st' h' => by rw [SH_dstate] at h'; cases h'; exact ⟨rfl, rfl⟩) b2
              (hfs b2 (.inr rfl))))
          · rintro z' ⟨i', e', h'⟩
            obtain rfl := Option.some.inj e'
            rw [SH_streams] at h'; cases h'; exact .inl hai0
          obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h')
          exact ⟨fun _ => a1, fun _ => rfl, fun e8 => absurd e8 (Int32.not_le.mpr a2)⟩
        · obtain ⟨F4, z4, st4, hz4, hst4, hbv, -, hla4, -, -, hai4, hf, ht, A4⟩ := q1 hb
          have hx : ∀ bs, (bs = b1 → r = true) → (bs = b2 → r = false) → (bs = b1 ∨ bs = b2) →
              StratPost h (some i) flush bs H' := by
            intro bs hb1 hb2 hbs
            have hO : bs = .need_more ∨ bs = .finish_started → O0 H' i := fun e => by
              rcases hbs with rfl | rfl
              · exact o0_of fun z' h'' => by
                  obtain rfl := Option.some.inj (hz4.symm.trans h''); exact ht (hb1 rfl)
              · exact absurd e hn2
            have hX : ExitIO H' i flush bs := by
              refine ⟨fun e => ?_, fun e => ?_, fun _ e => hO e, fun e => ?_⟩
              · rcases hbs with rfl | rfl
                · rcases e with e | e
                  · exact cf_of_o0 (hO (.inl e))
                  · rcases hc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> cases e
                · rintro z' ⟨i', e', h''⟩
                  obtain rfl := Option.some.inj e'
                  obtain rfl := Option.some.inj (hz4.symm.trans h'')
                  exact .inl (hai4.trans hai0)
              · rcases hbs with rfl | rfl
                · exact hF1 e
                · exact hF2 e
              · rcases hbs with rfl | rfl
                · rcases hc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> cases e
                · exact ⟨hnf0, hbd e, by simp only [avIn, hz4, hai4.trans hai0, UInt32.toNat_zero]⟩
            refine qf_post F4 flush bs hX hE0 (fun st' h' => ?_)
              (qp_post F4 A4 (fun st' h' => by obtain rfl := Option.some.inj (hst4.symm.trans h'); exact ⟨rfl, rfl⟩)
                bs (hfs bs hbs))
            obtain rfl := Option.some.inj (hst4.symm.trans h')
            refine ⟨fun e => ?_, fun _ => hla4, fun e8 => absurd e8 (Int32.not_le.mpr hbv)⟩
            rcases hbs with rfl | rfl
            · rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> rcases e with e | e <;> cases e
            · exact (hf (hb2 rfl)).1
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact Sat.pure (hx b1 (fun _ => rfl) (fun e => by
              rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> cases e) (.inl rfl))
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact Sat.pure (hx b2 (fun e => by
              rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> cases e) (fun _ => rfl) (.inr rfl))
      by_cases hl : (last != 0) = true
      · simp only [hl, ↓reduceIte]
        have hl1 : last = 1 := by
          rcases hlast with rfl | rfl
          · exact absurd hl (by decide)
          · rfl
        exact fin 1 .finish_started .finish_done (.inr ⟨rfl, rfl, rfl⟩) (fun _ => hlF hl1)
          (fun e => absurd e (by decide)) (fun e => by cases e)
      · simp only [hl, Bool.false_eq_true, ↓reduceIte]
        have hl0 : last = 0 := by simpa using hl
        refine fin 0 .need_more .block_done (.inl ⟨rfl, rfl, rfl⟩) (fun e => absurd e (by decide)) (fun _ => ?_)
          (fun _ => hl0F hl0)
        rcases hd1 with h0 | ⟨-, hF, -⟩
        · exact h0
        · exact absurd hF (hl0F hl0)

/-- The state record of a stream is unique. -/
theorem dstateIs_unique {h : Heap} {s : StreamPtr} {b b' : Nat} {st st' : DeflateState} (h1 : DStateIs h s b st)
    (h2 : DStateIs h s b' st') : st = st' := by
  obtain ⟨i, z, rfl, hz, hb, hst⟩ := h1
  obtain ⟨i', z', e, hz', hb', hst'⟩ := h2
  obtain rfl := Option.some.inj e
  obtain rfl := Option.some.inj (hz.symm.trans hz')
  obtain rfl := Option.some.inj (hb.symm.trans hb')
  exact Option.some.inj (hst.symm.trans hst')

/-- `deflate_quick` (`deflate_quick.c:240-246`) at level 1: `deflate_quick_impl(s, flush, 1)` with `Z_FIXED`, else
`deflate_quick_impl(s, flush, 0)`. -/
theorem quick_ok (T : TreesFacts) : StratOkP (TableAt 1 1) deflate_quick := by
  intro h s b flush P hsb hE
  obtain ⟨-, -, -, -, -, -, b1, st1, hD, -⟩ := id P
  by_cases hf : st1.strategy = Z_FIXED
  · exact quick_static_ok h s b flush P hsb fun b' st hd => ⟨hE b' st hd, by
      rw [← dstateIs_unique hD hd]; exact hf⟩
  · exact ZlibNgF.Proof.QuickP.quick_tally_ok T h s b flush P hsb fun b' st hd => ⟨hE b' st hd, by
      rw [← dstateIs_unique hD hd]; exact hf⟩

end ZlibNgF.Proof.QuickS

namespace ZlibNgF.Proof.Strategy
open C ZlibNgF.Spec ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts

/-- The four strategies proved so far: `deflate_stored`, `deflate_quick`, `deflate_huff` and `deflate_rle`, given the
block emitters. -/
theorem strategiesA (T : TreesFacts) :
    StratOkP (fun st => st.level = 0) ZlibNg.DeflateStored.deflate_stored ∧
      StratOkP (TableAt 1 1) ZlibNg.DeflateQuick.deflate_quick ∧
      StratOkP (fun st => 0 < st.level ∧ st.strategy = Z_HUFFMAN_ONLY) ZlibNg.DeflateHuff.deflate_huff ∧
      StratOkP (fun st => 0 < st.level ∧ st.strategy = Z_RLE) ZlibNg.DeflateRle.deflate_rle :=
  ⟨ZlibNgF.Proof.StoredSafe.stored_ok T, ZlibNgF.Proof.QuickS.quick_ok T, ZlibNgF.Proof.DeflateHuffP.huff_ok T,
    ZlibNgF.Proof.DeflateRleP.rle_ok T⟩

end ZlibNgF.Proof.Strategy
