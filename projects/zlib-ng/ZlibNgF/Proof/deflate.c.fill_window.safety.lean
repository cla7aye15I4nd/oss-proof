import ZlibNgF.Proof.«deflate.c.fill_window.slide»

/-!
# Safety of `fill_window` (`ZlibNgF`)

Runs on `SH` heaps. `read_SH`: the reading part of one trip of the loop (`read_buf` of
`more = fill_end + MIN_LOOKAHEAD - lookahead - strstart` bytes at `strstart + lookahead`, within the window by
`WCore.fe_hi`; the hash set-up at `str = strstart - insert`, within the data by `WCore.ins`; `insert_batch` of
`count <= insert` positions) reads at least one byte when input is left. `fill_window_SH`: from the window clauses
(`WCore`), the layout (`HLay`), `strstart + lookahead <= window_size`, `lookahead < MIN_LOOKAHEAD` and input that is
empty or lies outside the block (`InSrc`), `fill_window` does not fault and leaves `FWPost`: only the input fields
of the stream record and `fill_window`'s fields of the state change, the window clauses hold, and the lookahead is
at least `MIN_LOOKAHEAD` or the input is used up. The loop terminates: each trip that goes on reads at least one
byte with `lookahead < MIN_LOOKAHEAD`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FillWindow
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase ZlibNgF.Proof.InsertSafe
open ZlibNgF.Proof.WinInv ZlibNgF.Proof.FillSlide ZlibNgF.Proof.ReadBuf
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.ChunkMem (fillFold fillFold_get fillFold_size)
open ZlibNgF.Proof.DeflateFacts (ChainOk chainLim)
open ZlibNgF.Proof.SlideChain (ChainOk.st ChainOk.wrin ChainOk.look)
open ZlibNgF.Proof.InsertGrow (ChainOk.grow call_insert_batch_G insert_knuth_G)

/-- A fill of `n` bytes at offset `od` changes `[od, od + n)` only. -/
theorem fillFold_wr (byte : UInt8) (od n : Nat) (a : Array UInt8) :
    WrIn a od (od + n) (fillFold byte od (List.range' 0 n) a) :=
  ⟨fillFold_size .., fun _ hj => fillFold_get _ _ _ _ _ (fun x hx => by
    simp only [List.mem_range'_1] at hx; omega)⟩

/-- The input of stream record `z` lies in an object of `H` other than block `b`. -/
def InSrc (H : Heap) (b : Nat) (z : ZStream) : Prop :=
  ∃ r os src, z.next_in = .ref r os ∧ r ≠ .heap b ∧ Space.get H r = some src ∧ os + z.avail_in.toNat ≤ src.size

theorem InSrc.rbz {H : Heap} {b : Nat} {z : ZStream} {r : BRef} {os : Nat} {src : Array UInt8} (n : UInt32)
    (a : UInt64) (_hni : z.next_in = .ref r os) (hr : r ≠ .heap b) (hg : Space.get H r = some src)
    (hin : os + z.avail_in.toNat ≤ src.size) (hn : n.toNat ≤ z.avail_in.toNat) : InSrc H b (RBZ z n r os a) :=
  ⟨r, os + n.toNat, src, rfl, hr, hg, by simp only [RBZ]; rw [sub_toNat _ _ hn]; omega⟩

theorem ZR.state {z z' : ZStream} (h : ZR z z') : z'.state = z.state := by
  obtain ⟨-, ⟨_, _, _, _, rfl⟩, -⟩ := h; rfl

theorem FWS.wrap {st st' : DeflateState} (h : FWS st st') : st'.wrap = st.wrap := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := h; rfl

theorem FWS.sizes {st st' : DeflateState} (h : FWS st st') :
    st'.window_size = st.window_size ∧ st'.w_size = st.w_size := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem ZR.rbz (z : ZStream) (n : UInt32) (r : BRef) (os : Nat) (a : UInt64) (hn : n.toNat ≤ z.avail_in.toNat)
    (hni : z.next_in = .ref r os) : ZR z (RBZ z n r os a) :=
  ⟨by simp only [RBZ]; rw [sub_toNat _ _ hn]; omega, ⟨_, _, _, _, rfl⟩, Or.inr ⟨r, os, hni, by
    simp only [RBZ]; rw [sub_toNat _ _ hn]; congr 1; omega⟩⟩

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- What the reading part leaves. -/
def RFin (st st' : DeflateState) : Prop :=
  FWS st st' ∧ st.lookahead.toNat < st'.lookahead.toNat ∧ st'.strstart = st.strstart ∧
    st'.fill_end = st.fill_end ∧ WCore st' ∧ st'.strstart.toNat + st'.lookahead.toNat ≤ st'.window_size.toNat ∧
    st'.block_start = st.block_start ∧ st'.match_start = st.match_start ∧ st'.prev_length = st.prev_length

theorem read_SH {st : DeflateState} {wo po ho : Nat} (level : Int32) (f : InsertBatchFn) (hlev : level = st.level)
    (hfl : st.level ≠ 1 → f ≠ .insert_knuth_batch_head) (hzb : z.state = some b) (L : HLay b d.size st wo po ho) (hws : st.window_size = W_BUF_SIZE st.w_size)
    (hwo : wo + st.window_size.toNat ≤ po) (hw2 : st.w_size.toNat ≤ 32768)
    (C : WCore st) (hlt : st.strstart.toNat < st.fill_end.toNat) (hla : st.lookahead.toNat < 262)
    (hz0 : z.avail_in ≠ 0) (hin : InSrc H b z) (hc : st.wrap = 2 → H.crcTable = ZlibNg.Crc32Tbl.crc_table) :
    Sat (SH H i z b st d) (fill_window_read (some b) (some i) f (.ref (.heap b) wo) level)
      (fun _ H' => ∃ z' st' d', H' = SH H i z' b st' d' ∧ WrIn d 0 (ho + 131072) d' ∧
        (ChainOk b d st → ChainOk b d' st') ∧ ZR z z' ∧ InSrc H b z' ∧
        RFin st st' ∧ z'.avail_in.toNat + st'.lookahead.toNat = z.avail_in.toNat + st.lookahead.toNat) := by
  obtain ⟨r, os, src, hni, hr, hg, hin⟩ := hin
  have hW0 := L.w1
  have hp2 : ∃ k, st.w_size.toNat = 2 ^ k := by obtain ⟨k, -, -, e⟩ := C.wpow; exact ⟨k, e⟩
  have hWS := wbuf_cases st.w_size hw2
  rw [← hws] at hWS
  have hWS65 : st.window_size.toNat ≤ 65536 := by rw [hWS]; split <;> omega
  have hfe := C.fe_hi
  have hpw := L.pw
  have hph := L.ph
  have hins := C.ins
  have hML : MIN_LOOKAHEAD.toNat = 262 := by decide
  have hmore : (st.fill_end + MIN_LOOKAHEAD - st.lookahead - st.strstart).toNat =
      st.fill_end.toNat + 262 - st.lookahead.toNat - st.strstart.toNat := by
    have e1 : (st.fill_end + MIN_LOOKAHEAD).toNat = st.fill_end.toNat + 262 := by
      rw [UInt32.toNat_add, hML]; omega
    rw [sub_toNat _ _ (by rw [sub_toNat _ _ (by omega), e1]; omega), sub_toNat _ _ (by omega), e1]
  have hpos : (st.strstart + st.lookahead).toNat = st.strstart.toNat + st.lookahead.toNat := by
    rw [UInt32.toNat_add]; omega
  unfold fill_window_read
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine Sat.bind (Sat.of_eq (addN_SH _ (by rw [hpos]; omega)) ?_)
  rw [hpos]
  refine Sat.bind (Sat.mono (read_buf_SH hzb hni hr hg hin hc _ (by rw [hmore]; omega)) ?_)
  rintro n _ ⟨hn1, hn2, hn0, d1, a, rfl, hd1w⟩
  rw [hmore] at hn1 hd1w
  have hd1u : WrIn d 0 (ho + 131072) d1 := wr_below hd1w (by omega)
  have hd1 := hd1u.1
  have hnz : n.toNat ≠ 0 := by
    intro h0
    have := (hn0 (UInt32.toNat_inj.mp (by simpa using h0))).2
    rcases this with h | h
    · exact hz0 h
    · have := congrArg UInt32.toNat h; rw [hmore] at this; simp at this; omega
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have hla' : (st.lookahead + n).toNat = st.lookahead.toNat + n.toNat := by rw [UInt32.toNat_add]; omega
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = { st with lookahead := st.lookahead + n } := ⟨_, rfl⟩
  have F1 : FWS st s1 := by rw [hs1]; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  have L1 : HLay b d1.size s1 wo po ho := by rw [hd1]; exact FWS.hlay F1 L
  have e_la : s1.lookahead.toNat = st.lookahead.toNat + n.toNat := by rw [hs1]; exact hla'
  have e_ss : s1.strstart = st.strstart := by rw [hs1]
  have e_in : s1.insert = st.insert := by rw [hs1]
  have e_fe : s1.fill_end = st.fill_end := by rw [hs1]
  have e_ws : s1.window_size = st.window_size := by rw [hs1]
  have e_w : s1.w_size = st.w_size := by rw [hs1]
  have e_bs : s1.block_start = st.block_start := by rw [hs1]
  have e_lv : s1.level = st.level := by rw [hs1]
  have e_sg : s1.strategy = st.strategy := by rw [hs1]
  have e_hd : s1.head = st.head := by rw [hs1]
  have e_pv : s1.prev = st.prev := by rw [hs1]
  have e_ms : s1.match_start = st.match_start := by rw [hs1]
  have e_pl : s1.prev_length = st.prev_length := by rw [hs1]
  have CK1 : ChainOk b d st → ChainOk b d1 s1 := fun Ch =>
    ChainOk.look (ChainOk.wrin Ch L hd1w (by omega)) e_lv e_sg e_hd e_pv e_w e_ss (by omega)
  have C1 : WCore s1 := by rw [hs1]; exact ⟨C.wpow, C.fe_mod, C.fe_hi, C.ins, C.bs_hi, C.bs_lo⟩
  have ZR1 := ZR.rbz z n r os a hn2 hni
  have IS1 := InSrc.rbz n a hni hr hg hin hn2
  have SUM1 : (RBZ z n r os a).avail_in.toNat + s1.lookahead.toNat = z.avail_in.toNat + st.lookahead.toNat := by
    simp only [RBZ]; rw [sub_toNat _ _ hn2, e_la]; omega
  rw [← hs1]
  split
  · rename_i hcond
    have hc3 : 3 ≤ s1.lookahead.toNat + s1.insert.toNat := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have := hcond.2
      rw [ge_iff_le, UInt32.le_iff_toNat_le, UInt32.toNat_add] at this
      have h3 : STD_MIN_MATCH.toNat = 3 := by decide
      rw [h3, e_in, e_la] at this; rw [e_in, e_la]; omega
    extract_lets str jp
    have hstr : str.toNat = st.strstart.toNat - st.insert.toNat := by
      simp only [str]; rw [sub_toNat _ _ (by rw [e_ss, e_in]; omega), e_ss, e_in]
    clear_value str
    have hjp : ∀ (ih : UInt32) (d2 : Array UInt8), WrIn d 0 (ho + 131072) d2 →
        (ChainOk b d st → ChainOk b d2 { s1 with ins_h := ih }) →
        Sat (SH H i (RBZ z n r os a) b { s1 with ins_h := ih } d2) (jp ())
          (fun _ H' => ∃ z' st' d', H' = SH H i z' b st' d' ∧ WrIn d 0 (ho + 131072) d' ∧
            (ChainOk b d st → ChainOk b d' st') ∧ ZR z z' ∧ InSrc H b z' ∧
            RFin st st' ∧ z'.avail_in.toNat + st'.lookahead.toNat = z.avail_in.toNat + st.lookahead.toNat) := by
      intro ih d2 hd2w hc2
      have hd2 := hd2w.1
      dsimp (config := { zeta := false }) only [jp]
      refine Sat.bind (Sat.of_eq ldDState_SH ?_)
      dsimp (config := { zeta := false }) only
      have F2 : FWS st { s1 with ins_h := ih } := F1.trans ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      extract_lets c1 c2
      have hc2le : c2.toNat ≤ st.insert.toNat := by
        simp only [c2, c1]; split
        · rename_i h1
          have : s1.lookahead = 1 := by simpa using h1
          have h1' := congrArg UInt32.toNat this
          simp only [UInt32.toNat_one] at h1'
          rw [sub_toNat _ _ (by simp; omega), e_in]; omega
        · rw [e_in]; exact Nat.le_refl _
      clear_value c2 c1
      split
      · have L2 : HLay b d2.size { s1 with ins_h := ih } wo po ho := by
          rw [hd2, ← hd1]; exact FWS.hlay ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ L1
        have hins : Sat (SH H i (RBZ z n r os a) b { s1 with ins_h := ih } d2)
            (ZlibNg.InsertString.call_insert_batch f (some b) (.ref (.heap b) wo) str c2)
            (fun _ H' => ∃ d3 x, H' = SH H i (RBZ z n r os a) b { { s1 with ins_h := ih } with ins_h := x } d3 ∧
              WrIn d2 0 (ho + 131072) d3 ∧ (ChainOk b d st → ChainOk b d3 { s1 with ins_h := x })) := by
          by_cases hl1 : st.level = 1
          · exact Sat.mono (call_insert_batch_SH L2 f str c2 (by rw [hstr, hd2]; omega)) (fun _ _ ⟨d3, x, e, w⟩ =>
              ⟨d3, x, e, w, fun _ h1 _ => absurd (e_lv.trans hl1) h1⟩)
          · refine Sat.mono (call_insert_batch_G L2 (by rw [e_w]; exact hp2) f (hfl hl1) str c2
              (by rw [hstr, hd2]; omega) (by rw [hstr]; omega)) (fun _ _ ⟨d3, x, e, w, g⟩ =>
              ⟨d3, x, e, w.widen (Nat.zero_le _) (Nat.le_refl _), fun Ch => ChainOk.grow (hc2 Ch) (fun ho' po' hh hp => by
                have e1 : ho' = ho := by
                  rw [L2.head] at hh; injection hh with e; injection e with _ e; exact e.symm
                have e2 : po' = po := by
                  rw [L2.prev] at hp; injection hp with e; injection e with _ e; exact e.symm
                subst e1 e2; exact g) rfl rfl rfl rfl rfl (Nat.le_refl _) (by unfold chainLim; exact Nat.le_refl _)
                (fun q hq _ => Nat.lt_of_lt_of_le (show q < s1.strstart.toNat by
                  have := hq.2; rw [e_ss]; rw [hstr] at this; omega) (Nat.le_add_right _ _))⟩)
        refine Sat.bind (Sat.mono hins ?_)
        rintro _ _ ⟨d3, x, rfl, hd3, hc3⟩
        refine Sat.of_eq (wrD_SH _) ⟨_, _, d3, rfl, wr_tr hd2w hd3,
          fun Ch => ChainOk.st (hc3 Ch) rfl rfl rfl rfl rfl rfl rfl (by rw [e_w]; exact hW0), ZR1, IS1,
          ⟨F2.trans ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩, by simp only []; omega, e_ss, e_fe,
          ⟨C1.wpow, C1.fe_mod, C1.fe_hi, ?_, C1.bs_hi, C1.bs_lo⟩, ?_, e_bs, e_ms, e_pl⟩, SUM1⟩
        · simp only []; rw [sub_toNat _ _ (by rw [e_in]; omega), e_ss, e_in]; omega
        · simp only []; rw [e_la, e_ss, e_ws]; omega
      · exact Sat.pure ⟨_, _, d2, rfl, hd2w, hc2, ZR1, IS1, ⟨F2, by simp only []; omega, e_ss, e_fe,
          ⟨C1.wpow, C1.fe_mod, C1.fe_hi, C1.ins, C1.bs_hi, C1.bs_lo⟩, by simp only []; rw [e_la, e_ss, e_ws]; omega,
          e_bs, e_ms, e_pl⟩, SUM1⟩
    clear_value jp
    split
    · refine Sat.ro (index8_SH _ (by omega) (by simp; rw [hstr, hd1]; omega)) (fun w0 => ?_)
      have hs1' : (str + 1).toNat = str.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
      refine Sat.ro (index8_SH _ (by omega) (by simp only [Int.toNat_natCast]; rw [hs1', hstr, hd1]; omega)) (fun w1 => ?_)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      exact hjp _ _ hd1u (fun Ch => ChainOk.st (CK1 Ch) rfl rfl rfl rfl rfl rfl rfl (by rw [e_w]; exact hW0))
    · split
      · rename_i hs1g
        have hs1g' : 1 ≤ str.toNat := by simpa [UInt32.le_iff_toNat_le] using hs1g
        have e2 : (str + 2 - STD_MIN_MATCH).toNat = str.toNat - 1 := by
          have : STD_MIN_MATCH = 3 := rfl
          rw [this, sub_toNat _ _ (by rw [UInt32.toNat_add]; simp; omega), UInt32.toNat_add]; simp; omega
        split
        · rename_i hl1
          refine Sat.bind (Sat.mono (insert_knuth_head_SH L1 _ (by rw [e2, hstr]; omega)) ?_)
          rintro _ _ ⟨d2, rfl, hd2⟩
          exact hjp s1.ins_h d2 (wr_tr hd1u hd2) (fun _ h1 => absurd (by rw [e_lv, ← hlev]; simpa using hl1) h1)
        · rename_i hl1
          have hl1' : st.level ≠ 1 := by rw [← hlev]; simpa using hl1
          refine Sat.bind (Sat.mono (insert_knuth_G L1 (by rw [e_w]; exact hp2) _ (by rw [e2, hstr]; omega)
            (by rw [e2, hstr]; omega)) ?_)
          rintro _ _ ⟨d2, rfl, hd2, g⟩
          refine hjp s1.ins_h d2 (wr_tr hd1u (hd2.widen (Nat.zero_le _) (Nat.le_refl _))) (fun Ch =>
            ChainOk.grow (CK1 Ch) (fun ho' po' hh hp => by
              have e1 : ho' = ho := by
                rw [L1.head] at hh; injection hh with e; injection e with _ e; exact e.symm
              have e2' : po' = po := by
                rw [L1.prev] at hp; injection hp with e; injection e with _ e; exact e.symm
              subst e1 e2'; exact g) rfl rfl rfl rfl rfl (Nat.le_refl _) (by unfold chainLim; exact Nat.le_refl _)
              (fun q hq _ => Nat.lt_of_lt_of_le (show q < s1.strstart.toNat by
                rw [e_ss, hq, e2, hstr]; omega) (Nat.le_add_right _ _)))
      · exact hjp s1.ins_h d1 hd1u CK1
  · refine Sat.pure ⟨_, s1, d1, rfl, hd1u, CK1, ZR1, IS1, ⟨F1, by omega, e_ss, e_fe, C1, ?_, e_bs, e_ms, e_pl⟩, SUM1⟩
    rw [e_la, e_ss, e_ws]; omega

/-- What `fill_window` leaves: the stream record changed in its input fields only (the input still in its object),
the state changed in `fill_window`'s fields only, the window clauses, the data in the window, and enough lookahead
or no more input; the block's bytes change below `U` only, and the lookahead grows by the input taken. -/
def FWPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st0 : DeflateState) (d : Array UInt8) (U : Nat) (H' : Heap) :
    Prop :=
  ∃ z' st' d', H' = SH H i z' b st' d' ∧ WrIn d 0 U d' ∧ (ChainOk b d st0 → ChainOk b d' st') ∧ LazyK st0 st' ∧
    ZR z z' ∧
    (z' = z ∧ z.avail_in = 0 ∨ InSrc H b z') ∧
    FWS st0 st' ∧ WCore st' ∧ st'.strstart.toNat + st'.lookahead.toNat ≤ st'.window_size.toNat ∧
    (262 ≤ st'.lookahead.toNat ∨ z'.avail_in = 0) ∧
    z'.avail_in.toNat + st'.lookahead.toNat = z.avail_in.toNat + st0.lookahead.toNat ∧
    (st'.strstart.toNat : Int) - st'.block_start.toInt ≤ (st0.strstart.toNat : Int) - st0.block_start.toInt ∧
      ((st'.strstart.toNat : Int) = st'.block_start.toInt → (st0.strstart.toNat : Int) = st0.block_start.toInt)

theorem fill_window_SH {st : DeflateState} {wo po ho : Nat} (f : InsertBatchFn)
    (hfl : st.level ≠ 1 → f ≠ .insert_knuth_batch_head) (hzb : z.state = some b) (hsm : st.strm = .val (some i)) (hib : st.insert_batch = .val f)
    (L : HLay b d.size st wo po ho) (hws : st.window_size = W_BUF_SIZE st.w_size)
    (hwo : wo + st.window_size.toNat ≤ po) (hw2 : st.w_size.toNat ≤ 32768)
    (C : WCore st) (hlook : st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat)
    (hla : st.lookahead.toNat < 262)
    (hin : z.avail_in = 0 ∨ InSrc H b z) (hc : st.wrap = 2 → H.crcTable = ZlibNg.Crc32Tbl.crc_table) :
    Sat (SH H i z b st d) (fill_window (some b))
      (fun _ H' => FWPost H i z b st d (ho + 131072) H') := by
  unfold fill_window
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  rw [hsm, hib, L.win]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.pure ?_)
  extract_lets level
  have hlev : level = st.level := rfl
  clear_value level
  have hWS65 : st.window_size.toNat ≤ 65536 := by
    rw [hws, wbuf_cases _ hw2]; split <;> omega
  have hML : MIN_LOOKAHEAD.toNat = 262 := by decide
  refine Sat.bind (Sat.mono (sat_cdoWhileH (s := false)
    (fun brk H' => brk = false ∧ ∃ z' st' d', H' = SH H i z' b st' d' ∧ WrIn d 0 (ho + 131072) d' ∧
      (ChainOk b d st → ChainOk b d' st') ∧ LazyK st st' ∧ ZR z z' ∧
      (z' = z ∧ z.avail_in = 0 ∨ InSrc H b z') ∧ FWS st st' ∧ WCore st' ∧
      st'.strstart.toNat + st'.lookahead.toNat ≤ st'.window_size.toNat ∧ st'.lookahead.toNat < 262 ∧
      z'.avail_in.toNat + st'.lookahead.toNat = z.avail_in.toNat + st.lookahead.toNat ∧
      (st'.strstart.toNat : Int) - st'.block_start.toInt ≤ (st.strstart.toNat : Int) - st.block_start.toInt ∧
      ((st'.strstart.toNat : Int) = st'.block_start.toInt → (st.strstart.toNat : Int) = st.block_start.toInt))
    (fun _ H' => match H'.dstates b with | some s => 262 - s.lookahead.toNat | none => 0)
    (fun _ H' => FWPost H i z b st d (ho + 131072) H') ?_
    ⟨rfl, z, st, d, rfl, WrIn.refl _ _ _, id, LazyK.of_eq rfl rfl rfl, ZR.refl z, hin.imp (fun h => ⟨rfl, h⟩) id, FWS.refl st, C, hlook, hla, rfl, Int.le_refl _, id⟩
    ?_) ?_)
  · rintro _ _ ⟨rfl, z1, s1, d1, rfl, hd1w, ck1, lz1, zr1, in1, F1, C1, lk1, la1, sm1, df1⟩
    have hd1 := hd1w.1
    have L1 := FWS.hlay F1 L
    rw [← hd1] at L1
    have hsz1 := FWS.sizes F1
    refine Sat.bind (Sat.mono (slide_SH level (hlev.trans (FWS.keeps F1).1.symm) L1 (by rw [hsz1.1, hsz1.2]; exact hws) (by rw [hsz1.1]; exact hwo)
      (by rw [hsz1.2]; exact hw2) C1 lk1) ?_)
    rintro _ _ ⟨s2, d2, rfl, hd2w, ck2, lz2, F2, la2, lt2, C2, lk2, df2⟩
    have hd2u := wr_tr hd1w hd2w
    have hd2 := hd2u.1
    refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
    split
    · rename_i h0
      have h0' : z1.avail_in = 0 := by simpa using h0
      refine Sat.pure ?_
      simp only [↓reduceIte]
      exact Sat.pure ⟨fun h => absurd h (by decide), fun _ => ⟨z1, s2, d2, rfl, hd2u, fun Ch => ck2 (ck1 Ch), lz1.trans lz2, zr1, in1,
        F1.trans F2, C2, lk2, Or.inr h0', by rw [la2]; exact sm1, ⟨Int.le_trans df2.1 df1.1, fun e => df1.2 (df2.2 e)⟩⟩⟩
    · rename_i h0
      have h0' : z1.avail_in ≠ 0 := by simpa using h0
      have in1' : InSrc H b z1 := by
        rcases in1 with ⟨rfl, h⟩ | h
        · exact absurd h h0'
        · exact h
      have L2 := FWS.hlay F2 L1
      rw [← hd2w.1] at L2
      have hsz2 := FWS.sizes (F1.trans F2)
      have kp := FWS.keeps (F1.trans F2)
      refine Sat.bind (Sat.mono (read_SH (z := z1) level f (hlev.trans kp.1.symm)
        (fun h => hfl (by rwa [kp.1] at h)) (by rw [ZR.state zr1]; exact hzb) L2
        (by rw [hsz2.1, hsz2.2]; exact hws) (by rw [hsz2.1]; exact hwo) (by rw [hsz2.2]; exact hw2) C2 lt2 (by rw [la2]; exact la1) h0'
        in1' (fun e => hc (by rw [← FWS.wrap (F1.trans F2)]; exact e))) ?_)
      rintro _ _ ⟨z3, s3, d3, rfl, hd3w, ck3, zr3, in3, ⟨F3, la3, ss3, fe3, C3, lk3, bs3, ms3, pl3⟩, sm3⟩
      have df3 : (s3.strstart.toNat : Int) - s3.block_start.toInt ≤ (st.strstart.toNat : Int) - st.block_start.toInt ∧
          ((s3.strstart.toNat : Int) = s3.block_start.toInt → (st.strstart.toNat : Int) = st.block_start.toInt) := by
        rw [ss3, bs3]; exact ⟨Int.le_trans df2.1 df1.1, fun e => df1.2 (df2.2 e)⟩
      have hd3u := wr_tr hd2u hd3w
      rw [la2] at sm3
      refine Sat.pure ?_
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine Sat.bind (Sat.of_eq ldDState_SH ?_)
      refine Sat.bind (Sat.of_eq (rdZ_SH _) (Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩))
      · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
        have hc1 : s3.lookahead.toNat < 262 := by rw [UInt32.lt_iff_toNat_lt, hML] at hc; exact hc.1
        refine ⟨⟨rfl, z3, s3, d3, rfl, hd3u, fun Ch => ck3 (ck2 (ck1 Ch)),
          lz1.trans (lz2.trans (LazyK.of_eq pl3 ms3 ss3)), zr1.trans zr3, Or.inr in3,
          (F1.trans F2).trans F3, C3, lk3, hc1, by omega, df3⟩, ?_⟩
        simp only [SH_dstates]
        rw [la2] at la3; omega
      · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, bne_eq_false_iff_eq] at hc
        refine ⟨z3, s3, d3, rfl, hd3u, fun Ch => ck3 (ck2 (ck1 Ch)),
          lz1.trans (lz2.trans (LazyK.of_eq pl3 ms3 ss3)), zr1.trans zr3, Or.inr in3, (F1.trans F2).trans F3,
          C3, lk3, ?_, by omega, df3⟩
        rcases hc with hc | hc
        · left; rw [UInt32.lt_iff_toNat_lt, hML] at hc; omega
        · right; exact hc
  · simp only [SH_dstates, fuel]; omega
  rintro _ _ ⟨z1, s1, d1, rfl, hd1w, ck1, lz1, zr1, in1, F1, C1, lk1, hend, sm1, df1⟩
  have hd1 := hd1w.1
  have hpo := L.ph
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have L1 := FWS.hlay F1 L
  rw [← hd1] at L1
  have hpw := L1.pw
  have hws1 : s1.window_size = st.window_size := by obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := F1; rfl
  have hW1 : 0 < s1.w_size.toNat := L1.w1
  have post : ∀ (v : UInt32) (d2 : Array UInt8), WrIn d 0 (ho + 131072) d2 →
      (ChainOk b d st → ChainOk b d2 s1) →
      FWPost H i z b st d (ho + 131072) (SH H i z1 b { s1 with high_water := v } d2) := fun v d2 hd2 hc2 =>
    ⟨z1, _, d2, rfl, hd2, fun Ch => ChainOk.st (hc2 Ch) rfl rfl rfl rfl rfl rfl rfl hW1, lz1, zr1, in1, F1.trans ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩,
      ⟨C1.wpow, C1.fe_mod, C1.fe_hi, C1.ins, C1.bs_hi, C1.bs_lo⟩, lk1, hend, sm1, df1⟩
  have hcur : (s1.strstart + s1.lookahead).toNat = s1.strstart.toNat + s1.lookahead.toNat := by
    rw [UInt32.toNat_add]; have e := congrArg UInt32.toNat hws1; omega
  have e_ws := congrArg UInt32.toNat hws1
  split
  · rename_i hhw
    extract_lets curr
    rename_i i1 i2 j1 j2
    have hc' : curr.toNat = s1.strstart.toNat + s1.lookahead.toNat := hcur
    clear_value curr
    split
    · rename_i hlt
      have hi2 : i2.toNat ≤ s1.window_size.toNat - curr.toNat := by
        simp only [i2, i1]; split
        · rename_i h; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at h
          rw [sub_toNat _ _ (by omega)] at h; have : WIN_INIT.toNat = 258 := by decide
          omega
        · rw [sub_toNat _ _ (by omega)]; exact Nat.le_refl _
      clear_value i2 i1
      refine Sat.bind (Sat.of_eq (addN_SH curr.toNat (by omega)) ?_)
      refine Sat.bind (Sat.of_eq (memset_SH (by omega) 0) ?_)
      exact Sat.of_eq (wrD_SH _) (post _ _ (wr_tr hd1w (wr_below (fillFold_wr ..) (by omega)))
          (fun Ch => ChainOk.wrin (ck1 Ch) L1 (fillFold_wr ..) (by omega)))
    · split
      · rename_i hge hlt
        have hlt' : s1.high_water.toNat < s1.window_size.toNat := by simpa [UInt32.lt_iff_toNat_lt] using hhw
        have hi2 : j2.toNat ≤ s1.window_size.toNat - s1.high_water.toNat := by
          simp only [j2, j1]; split
          · rw [sub_toNat _ _ (by omega)]; exact Nat.le_refl _
          · rename_i h; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at h
            rw [sub_toNat _ _ (by omega)] at h; omega
        clear_value j2 j1
        refine Sat.bind (Sat.of_eq (addN_SH s1.high_water.toNat (by omega)) ?_)
        refine Sat.bind (Sat.of_eq (memset_SH (by omega) 0) ?_)
        exact Sat.of_eq (wrD_SH _) (post _ _ (wr_tr hd1w (wr_below (fillFold_wr ..) (by omega)))
          (fun Ch => ChainOk.wrin (ck1 Ch) L1 (fillFold_wr ..) (by omega)))
      · exact Sat.pure (post s1.high_water d1 hd1w ck1)
  · exact Sat.pure (post s1.high_water d1 hd1w ck1)
end
end ZlibNgF.Proof.FillWindow
