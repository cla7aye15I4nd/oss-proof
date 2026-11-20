import ZlibNgF.Proof.«deflate.c.fill_window.inv»
import ZlibNgF.Proof.«slide_hash_c.c.chain»

/-!
# The slide of `fill_window` (`ZlibNgF`)

`fill_window_slide`: the `fill_end` loop (`fe_loop`), then, when `fill_end` passed `window_size - MIN_LOOKAHEAD`,
the slide by `slide_len = (strstart - MAX_DIST) & ~W_MASK` (a multiple of `w_size`, at least half the data, so the
`memcpy` does not overlap: `ZlibNgF.Math.WinMask.slide_math`), the updates of `match_start`, `strstart`,
`block_start` (the `int` subtraction stays in range by `WCore.bs_lo`), `fill_end`, `insert`, and `slide_hash_c` /
`slide_hash_head_c`. `slide_SH`: no fault, and the window clauses `WCore` after (`SFin`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FillSlide
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase ZlibNgF.Proof.InsertSafe
open ZlibNgF.Proof.WinInv
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)
open ZlibNgF.Proof.SlideSafe (slide_hash_c_SH slide_hash_head_c_SH)
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.ReadBuf (copyFold_wr)
open ZlibNgF.Proof.SlideChain (slide_hash_c_slide ChainOk.slide ChainOk.st ChainOk.wrin)
open ZlibNgF.Proof.DeflateFacts (ChainOk)

theorem wbuf_cases (w : UInt32) (hw : w.toNat ≤ 32768) :
    (W_BUF_SIZE w).toNat = if 2 * w.toNat > 32768 then 2 * w.toNat else 32768 := by
  rw [ZlibNgF.Proof.DeflateInit.wbuf_toNat w hw]; rfl

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- `memcpy` within block `b` between two ranges that do not overlap. -/
theorem memcpy_SH_self {st : DeflateState} {od os n : Nat} (hov : od + n ≤ os ∨ os + n ≤ od)
    (h1 : od + n ≤ d.size) (h2 : os + n ≤ d.size) :
    Ptr.memcpy (Ptr.ref (BRef.heap b) od) (Ptr.ref (BRef.heap b) os) n (SH H i z b st d) =
      .ok ((), SH H i z b st (copyFold d od os (List.range' 0 n) d)) := by
  have hd := SH_bytes H i z b st d
  simp only [Ptr.memcpy, space_get_heap, hd, h1, h2, and_self, ↓reduceIte]
  simp only [Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, Space.modify, Heap.modifyBytes,
    Tbl.modify_opt _ b _ d hd]
  rw [← ZlibNgF.Proof.InflateDict.memcpy_loop]
  simp [SH, upd_upd]
  intro _ _; omega

theorem FWS.hlay {st st' : DeflateState} {D wo po ho : Nat} (f : FWS st st') (L : HLay b D st wo po ho) :
    HLay b D st' wo po ho := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := f
  exact ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩

/-- The fields that `ChainOk` reads and `fill_window` does not write. -/
theorem FWS.keeps {st st' : DeflateState} (f : FWS st st') : st'.level = st.level ∧ st'.strategy = st.strategy ∧
    st'.head = st.head ∧ st'.prev = st.prev ∧ st'.w_size = st.w_size := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := f; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sub_toNat (a c : UInt32) (h : c.toNat ≤ a.toNat) : (a - c).toNat = a.toNat - c.toNat :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h)


/-- The `fill_end` loop of `fill_window`. -/
theorem fe_loop {st : DeflateState} (hW : 1 ≤ st.w_size.toNat) (hw2 : st.w_size.toNat ≤ 32768)
    (hss : st.strstart.toNat ≤ 65536) (hfe0 : st.fill_end.toNat ≤ 65536)
    (hm : (st.fill_end.toNat + 262) % st.w_size.toNat = 0) :
    Sat (SH H i z b st d) (cwhile
      (fun (u : Unit) => do let s ← ldDState (some b); pure (decide (s.strstart ≥ s.fill_end), u))
      (fun (u : Unit) => do wrD (some b) fun s => { s with fill_end := s.fill_end + s.w_size }; pure u) ())
      (fun _ H' => ∃ fe : UInt32, H' = SH H i z b { st with fill_end := fe } d ∧
        (fe.toNat + 262) % st.w_size.toNat = 0 ∧ (fe = st.fill_end ∨ fe.toNat ≤ st.strstart.toNat + st.w_size.toNat) ∧
        st.strstart.toNat < fe.toNat) := by
  refine sat_cwhileH (s := ())
    (fun _ H' => ∃ fe : UInt32, H' = SH H i z b { st with fill_end := fe } d ∧
      (fe.toNat + 262) % st.w_size.toNat = 0 ∧ (fe = st.fill_end ∨ fe.toNat ≤ st.strstart.toNat + st.w_size.toNat))
    (fun _ H' => match H'.dstates b with | some s => s.strstart.toNat + 1 - s.fill_end.toNat | none => 0) _ ?_
    ⟨st.fill_end, rfl, hm, Or.inl rfl⟩ ?_
  · rintro _ _ ⟨fe, rfl, hm', hfe⟩
    refine Sat.bind (Sat.of_eq ldDState_SH (Sat.pure ⟨fun hc => ?_, fun hc => ⟨fe, rfl, hm', hfe, ?_⟩⟩))
    · have hc' : fe.toNat ≤ st.strstart.toNat := by simpa [UInt32.le_iff_toNat_le] using hc
      have e : (fe + st.w_size).toNat = fe.toNat + st.w_size.toNat := by rw [UInt32.toNat_add]; omega
      refine Sat.bind (Sat.of_eq (wrD_SH _) (Sat.pure ⟨⟨fe + st.w_size, rfl, ?_, Or.inr ?_⟩, ?_⟩))
      · rw [e]; exact ZlibNgF.Math.WinMask.fe_step _ _ hm'
      · rw [e]; omega
      · simp only [SH_dstates]; rw [e]; omega
    · simpa [UInt32.le_iff_toNat_le] using hc
  · simp only [SH_dstates, fuel]; omega

/-- The lazy-match fields across `fill_window`: the slide lowers `strstart` and `match_start` together by
`slide_len` when `match_start >= slide_len`, and otherwise sets `match_start` and `prev_length` to 0; nothing else
writes them. So a `prev_length` of 3 or more is the one before, with the same distance `strstart - match_start`
and a `match_start` not above the one before, and `prev_length` does not grow. -/
def LazyK (st st' : DeflateState) : Prop :=
  (3 ≤ st'.prev_length → st'.prev_length = st.prev_length ∧
    (st.strstart.toNat : Int) - st.match_start.toNat = (st'.strstart.toNat : Int) - st'.match_start.toNat ∧
    st'.match_start ≤ st.match_start) ∧ st'.prev_length ≤ st.prev_length

theorem LazyK.of_eq {st st' : DeflateState} (e1 : st'.prev_length = st.prev_length)
    (e2 : st'.match_start = st.match_start) (e3 : st'.strstart = st.strstart) : LazyK st st' :=
  ⟨fun _ => ⟨e1, by rw [e2, e3], by rw [e2]; exact UInt32.le_refl _⟩, by rw [e1]; exact UInt32.le_refl _⟩

theorem LazyK.trans {a c e : DeflateState} (h1 : LazyK a c) (h2 : LazyK c e) : LazyK a e := by
  refine ⟨fun h => ?_, UInt32.le_trans h2.2 h1.2⟩
  obtain ⟨p2, q2, r2⟩ := h2.1 h
  obtain ⟨p1, q1, r1⟩ := h1.1 (by rw [← p2]; exact h)
  exact ⟨p2.trans p1, q1.trans q2, UInt32.le_trans r2 r1⟩

theorem LazyK.mk {st s0 : DeflateState} {sl : Nat} (hs : s0.strstart.toNat = st.strstart.toNat - sl)
    (h : (3 ≤ s0.prev_length → s0.prev_length = st.prev_length ∧
      (st.strstart.toNat : Int) - st.match_start.toNat = ((st.strstart.toNat - sl : Nat) : Int) - s0.match_start.toNat ∧
      s0.match_start ≤ st.match_start) ∧ s0.prev_length ≤ st.prev_length) : LazyK st s0 := by
  unfold LazyK; rw [hs]; exact h

/-- What the slide part leaves: the state changed in the fields of `fill_window` only, with the same `lookahead`,
`strstart` below `fill_end`, the window clauses, and the data within the window. -/
def SFin (st st' : DeflateState) : Prop :=
  FWS st st' ∧ st'.lookahead = st.lookahead ∧ st'.strstart.toNat < st'.fill_end.toNat ∧ WCore st' ∧
    st'.strstart.toNat + st'.lookahead.toNat ≤ st'.window_size.toNat ∧
    (st'.strstart.toNat : Int) - st'.block_start.toInt ≤ (st.strstart.toNat : Int) - st.block_start.toInt ∧
      ((st'.strstart.toNat : Int) = st'.block_start.toInt → (st.strstart.toNat : Int) = st.block_start.toInt)

theorem slide_SH {st : DeflateState} {wo po ho : Nat} (level : Int32) (hlev : level = st.level)
    (L : HLay b d.size st wo po ho) (hws : st.window_size = W_BUF_SIZE st.w_size)
    (hwo : wo + st.window_size.toNat ≤ po) (hw2 : st.w_size.toNat ≤ 32768)
    (C : WCore st) (hlook : st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat) :
    Sat (SH H i z b st d) (fill_window_slide (some b) (.ref (.heap b) wo) level)
      (fun _ H' => ∃ st' d', H' = SH H i z b st' d' ∧ WrIn d 0 (ho + 131072) d' ∧
        (ChainOk b d st → ChainOk b d' st') ∧ LazyK st st' ∧ SFin st st') := by
  obtain ⟨k, hk1, hk2, hwk⟩ := C.wpow
  have hWS := wbuf_cases st.w_size hw2
  rw [← hws] at hWS
  have hp9 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
  have hW512 : 512 ≤ st.w_size.toNat := by rw [hwk]; exact hp9
  have hWS65 : st.window_size.toNat ≤ 65536 := by rw [hWS]; split <;> omega
  have hWS32 : 32768 ≤ st.window_size.toNat := by rw [hWS]; split <;> omega
  have hfe0 := C.fe_hi
  have hpw := L.pw
  have hph := L.ph
  have hML : MIN_LOOKAHEAD.toNat = 262 := by decide
  unfold fill_window_slide
  refine Sat.bind (Sat.mono (fe_loop (by omega) hw2 (by omega) (by omega) C.fe_mod) ?_)
  rintro _ _ ⟨fe, rfl, hm, hfe, hsf⟩
  obtain ⟨st1, hst1⟩ : ∃ st1, st1 = { st with fill_end := fe } := ⟨_, rfl⟩
  have e_ss : st1.strstart = st.strstart := by rw [hst1]
  have e_la : st1.lookahead = st.lookahead := by rw [hst1]
  have e_w : st1.w_size = st.w_size := by rw [hst1]
  have e_ws : st1.window_size = st.window_size := by rw [hst1]
  have e_fe : st1.fill_end = fe := by rw [hst1]
  have e_bs : st1.block_start = st.block_start := by rw [hst1]
  have e_in : st1.insert = st.insert := by rw [hst1]
  have e_ms : st1.match_start = st.match_start := by rw [hst1]
  have e_pl : st1.prev_length = st.prev_length := by rw [hst1]
  rw [← hst1]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  split
  · rename_i hgt
    have hgt' : st.window_size.toNat < fe.toNat + 262 := by
      rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, sub_toNat _ _ (by rw [hML, e_ws]; omega), e_fe, e_ws, hML] at hgt
      omega
    obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := ZlibNgF.Math.WinMask.slide_math k st.w_size.toNat st.window_size.toNat
      st.fill_end.toNat fe.toNat st.strstart.toNat st.lookahead.toNat hk1 hk2 hwk hWS hm hfe0
      (by rcases hfe with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr h) hsf hlook hgt'
    extract_lets sl
    have hsl : sl.toNat = (st.strstart.toNat - (st.w_size.toNat - 262)) -
        (st.strstart.toNat - (st.w_size.toNat - 262)) % st.w_size.toNat := by
      simp only [sl, W_MASK, MAX_DIST]
      rw [ZlibNgF.Math.WinMask.round_down _ _ k (by rw [e_w]; exact hwk) (by omega), e_ss, e_w,
        sub_toNat _ _ (by rw [sub_toNat _ _ (by rw [hML]; omega), hML]; omega),
        sub_toNat _ _ (by rw [hML]; omega), hML, ← hwk]
    clear_value sl
    rw [← hsl] at m2 m3 m4 m5 m6 m7
    have hn : (st1.strstart + st1.lookahead - sl).toNat = st.strstart.toNat + st.lookahead.toNat - sl.toNat := by
      rw [sub_toNat _ _ (by rw [UInt32.toNat_add, e_ss, e_la]; omega), UInt32.toNat_add, e_ss, e_la]; omega
    refine Sat.bind (Sat.of_eq (addN_SH sl.toNat (by omega)) ?_)
    rw [hn]
    refine Sat.bind (Sat.of_eq (memcpy_SH_self (Or.inl (by omega)) (by omega) (by omega)) ?_)
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    rename_i jp1

    have hb31 : sl.toInt32.toInt = sl.toNat := ZlibNgF.Proof.DeflateAlloc.u32_toInt32_toInt sl (by omega)
    have hbs1 := C.bs_hi
    have hbs2 := C.bs_lo
    have hins := C.ins
    let BS : Int := st.block_start.toInt - sl.toNat
    have hBS0 : -2147483648 ≤ BS := by simp only [BS]; omega
    have hBS1 : BS < 2147483648 := by simp only [BS]; omega
    have hjp1 : ∀ (ms pl : UInt32) (d0 : Array UInt8), WrIn d 0 (ho + 131072) d0 →
        (ChainOk b d st → ChainOk b d0 st) →
        ((3 ≤ pl → pl = st.prev_length ∧ (st.strstart.toNat : Int) - st.match_start.toNat =
          ((st.strstart.toNat - sl.toNat : Nat) : Int) - ms.toNat ∧ ms ≤ st.match_start) ∧ pl ≤ st.prev_length) →
        Sat (SH H i z b { st1 with match_start := ms, prev_length := pl } d0) (jp1 ())
          (fun _ H' => ∃ st' d', H' = SH H i z b st' d' ∧ WrIn d 0 (ho + 131072) d' ∧
            (ChainOk b d st → ChainOk b d' st') ∧ LazyK st st' ∧ SFin st st') := by
      intro ms pl d0 hd0 hc0 hlz
      simp only [jp1]
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      refine Sat.bind (Sat.of_eq ldDState_SH ?_)
      simp only []
      rw [e_bs, hb31, ZlibNgF.Proof.DeflatePrime.chk_ok _ hBS0 hBS1]
      -- patch 0018: the bound `(int)slide_len - (1 << 30) - (1 << 16)` and its test
      rw [ZlibNgF.Proof.DeflatePrime.chk_ok (sl.toNat - 1073741824) (by omega) (by omega)]
      refine Sat.bind (Sat.pure ?_)
      rw [ZlibNgF.Proof.DeflatePrime.ofInt_toInt _ (by omega) (by omega),
        ZlibNgF.Proof.DeflatePrime.chk_ok (sl.toNat - 1073741824 - 65536) (by omega) (by omega)]
      refine Sat.bind (Sat.pure ?_)
      by_cases hlim : st.block_start.toInt ≥ (Int32.ofInt (sl.toNat - 1073741824 - 65536)).toInt
      · have hlimN : st.block_start.toInt ≥ (sl.toNat : Int) - 1073741824 - 65536 := by
          rw [ZlibNgF.Proof.DeflatePrime.ofInt_toInt _ (by omega) (by omega)] at hlim; exact hlim
        simp only [hlim, ↓reduceIte]
        refine Sat.bind (Sat.pure ?_)
        rename_i jpX
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
        simp only [jpX]
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
        refine Sat.bind (Sat.of_eq ldDState_SH ?_)
        dsimp (config := { zeta := false }) only
        rename_i jp2
        have hjp2 : ∀ (s0 : DeflateState) (d1 : Array UInt8), WrIn d 0 (ho + 131072) d1 → SFin st s0 →
            s0.strstart.toNat = st.strstart.toNat - sl.toNat → (ChainOk b d st → ChainOk b d1 st) → LazyK st s0 →
            Sat (SH H i z b s0 d1) (jp2 ())
              (fun _ H' => ∃ st' d', H' = SH H i z b st' d' ∧ WrIn d 0 (ho + 131072) d' ∧
                (ChainOk b d st → ChainOk b d' st') ∧ LazyK st st' ∧ SFin st st') := by
          intro s0 d1 hd1 F hs0 hc1 hlk
          obtain ⟨k1, k2, k3, k4, k5⟩ := FWS.keeps F.1
          have hW0 : 0 < st.w_size.toNat := by omega
          have hmod : sl.toNat % st.w_size.toNat = 0 := by
            rw [hsl]; exact Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm
          have hsl65 : sl.toNat < 65536 := by omega
          have L0 := FWS.hlay F.1 L
          rw [← hd1.1] at L0
          have hw0 : s0.w_size = st.w_size := by obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := F.1; rfl
          simp only [jp2]
          refine Sat.bind (Sat.of_eq ldDState_SH ?_)
          split
          · refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
            have L0' := FWS.hlay (⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ : FWS s0 { s0 with slide_len := sl }) L0
            have F' : SFin st { s0 with slide_len := sl } :=
              ⟨F.1.trans ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩, F.2.1, F.2.2.1,
                ⟨F.2.2.2.1.wpow, F.2.2.2.1.fe_mod, F.2.2.2.1.fe_hi, F.2.2.2.1.ins, F.2.2.2.1.bs_hi, F.2.2.2.1.bs_lo⟩,
                F.2.2.2.2.1, F.2.2.2.2.2⟩
            split
            · rename_i hl1
              exact Sat.mono (slide_hash_head_c_SH L0') (fun _ _ ⟨d', e, hs⟩ => ⟨_, d', e, wr_tr hd1 hs,
                fun _ h1 => absurd (by rw [k1, ← hlev]; simpa using hl1) h1, hlk, F'⟩)
            · exact Sat.mono (slide_hash_c_slide L0' (by rw [hw0]; exact hw2) hsl65) (fun _ _ ⟨d', e, hs, hh', hp'⟩ =>
                ⟨_, d', e, wr_tr hd1 (hs.widen (Nat.zero_le _) (Nat.le_refl _)), fun C => ChainOk.slide (hc1 C) k1 k2 k3 k4
                  k5 F.2.1 (by omega) hs0 hmod hW0 (fun ho' po' hh hp => by
                    have e1 : ho' = ho := by
                      rw [← k3, L0.head] at hh; injection hh with e; injection e with _ e; exact e.symm
                    have e2 : po' = po := by
                      rw [← k4, L0.prev] at hp; injection hp with e; injection e with _ e; exact e.symm
                    subst e1 e2
                    exact ⟨hh', fun k hk => hp' k (by rw [k5]; exact hk)⟩), hlk, F'⟩)
          · rename_i hhl
            refine Sat.pure ⟨s0, d1, rfl, hd1, fun _ _ h2 => absurd h2 ?_, hlk, F⟩
            rw [k2] at hhl; rw [k1, k2, ← hlev]; simpa using hhl
        clear_value jp2
        have hss' : (st1.strstart - sl).toNat = st.strstart.toNat - sl.toNat := by
          rw [sub_toNat _ _ (by rw [e_ss]; omega), e_ss]
        have hfe' : (st1.fill_end - sl).toNat = fe.toNat - sl.toNat := by
          rw [sub_toNat _ _ (by rw [e_fe]; omega), e_fe]
        have hbs' : (Int32.ofInt BS).toInt = BS := ZlibNgF.Proof.DeflatePrime.ofInt_toInt _ hBS0 hBS1
        have hws1 := e_ws
        have hw1 := e_w
        split
        · rename_i hgi
          refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
          refine hjp2 _ _ hd0 ⟨?_, e_la, ?_, ⟨⟨k, hk1, hk2, by rw [hw1]; exact hwk⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ hss' hc0 (LazyK.mk hss' hlz)
          · subst hst1; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
          all_goals simp only [hss', hfe', hbs', hws1, hw1, e_la]
          all_goals (try simp only [BS])
          all_goals omega
        · rename_i hgi
          have hgi' : st.insert.toNat ≤ st.strstart.toNat - sl.toNat := by
            rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hss', e_in] at hgi; omega
          refine hjp2 _ _ hd0 ⟨?_, e_la, ?_, ⟨⟨k, hk1, hk2, by rw [hw1]; exact hwk⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ hss' hc0 (LazyK.mk hss' hlz)
          · subst hst1; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
          all_goals simp only [hss', hfe', hbs', hws1, hw1, e_la, e_in]
          all_goals (try simp only [BS])
          all_goals omega
      · have hlimN : st.block_start.toInt < (sl.toNat : Int) - 1073741824 - 65536 := by
          rw [ZlibNgF.Proof.DeflatePrime.ofInt_toInt _ (by omega) (by omega)] at hlim; omega
        simp only [hlim, ↓reduceIte]
        rename_i jpX
        simp only [jpX]
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
        refine Sat.bind (Sat.of_eq ldDState_SH ?_)
        dsimp (config := { zeta := false }) only
        rename_i jp2
        have hjp2 : ∀ (s0 : DeflateState) (d1 : Array UInt8), WrIn d 0 (ho + 131072) d1 → SFin st s0 →
            s0.strstart.toNat = st.strstart.toNat - sl.toNat → (ChainOk b d st → ChainOk b d1 st) → LazyK st s0 →
            Sat (SH H i z b s0 d1) (jp2 ())
              (fun _ H' => ∃ st' d', H' = SH H i z b st' d' ∧ WrIn d 0 (ho + 131072) d' ∧
                (ChainOk b d st → ChainOk b d' st') ∧ LazyK st st' ∧ SFin st st') := by
          intro s0 d1 hd1 F hs0 hc1 hlk
          obtain ⟨k1, k2, k3, k4, k5⟩ := FWS.keeps F.1
          have hW0 : 0 < st.w_size.toNat := by omega
          have hmod : sl.toNat % st.w_size.toNat = 0 := by
            rw [hsl]; exact Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm
          have hsl65 : sl.toNat < 65536 := by omega
          have L0 := FWS.hlay F.1 L
          rw [← hd1.1] at L0
          have hw0 : s0.w_size = st.w_size := by obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := F.1; rfl
          simp only [jp2]
          refine Sat.bind (Sat.of_eq ldDState_SH ?_)
          split
          · refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
            have L0' := FWS.hlay (⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ : FWS s0 { s0 with slide_len := sl }) L0
            have F' : SFin st { s0 with slide_len := sl } :=
              ⟨F.1.trans ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩, F.2.1, F.2.2.1,
                ⟨F.2.2.2.1.wpow, F.2.2.2.1.fe_mod, F.2.2.2.1.fe_hi, F.2.2.2.1.ins, F.2.2.2.1.bs_hi, F.2.2.2.1.bs_lo⟩,
                F.2.2.2.2.1, F.2.2.2.2.2⟩
            split
            · rename_i hl1
              exact Sat.mono (slide_hash_head_c_SH L0') (fun _ _ ⟨d', e, hs⟩ => ⟨_, d', e, wr_tr hd1 hs,
                fun _ h1 => absurd (by rw [k1, ← hlev]; simpa using hl1) h1, hlk, F'⟩)
            · exact Sat.mono (slide_hash_c_slide L0' (by rw [hw0]; exact hw2) hsl65) (fun _ _ ⟨d', e, hs, hh', hp'⟩ =>
                ⟨_, d', e, wr_tr hd1 (hs.widen (Nat.zero_le _) (Nat.le_refl _)), fun C => ChainOk.slide (hc1 C) k1 k2 k3 k4
                  k5 F.2.1 (by omega) hs0 hmod hW0 (fun ho' po' hh hp => by
                    have e1 : ho' = ho := by
                      rw [← k3, L0.head] at hh; injection hh with e; injection e with _ e; exact e.symm
                    have e2 : po' = po := by
                      rw [← k4, L0.prev] at hp; injection hp with e; injection e with _ e; exact e.symm
                    subst e1 e2
                    exact ⟨hh', fun k hk => hp' k (by rw [k5]; exact hk)⟩), hlk, F'⟩)
          · rename_i hhl
            refine Sat.pure ⟨s0, d1, rfl, hd1, fun _ _ h2 => absurd h2 ?_, hlk, F⟩
            rw [k2] at hhl; rw [k1, k2, ← hlev]; simpa using hhl
        clear_value jp2
        have hss' : (st1.strstart - sl).toNat = st.strstart.toNat - sl.toNat := by
          rw [sub_toNat _ _ (by rw [e_ss]; omega), e_ss]
        have hfe' : (st1.fill_end - sl).toNat = fe.toNat - sl.toNat := by
          rw [sub_toNat _ _ (by rw [e_fe]; omega), e_fe]
        have hbs' : (Int32.ofInt BS).toInt = BS := ZlibNgF.Proof.DeflatePrime.ofInt_toInt _ hBS0 hBS1
        have hws1 := e_ws
        have hw1 := e_w
        split
        · rename_i hgi
          refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
          refine hjp2 _ _ hd0 ⟨?_, e_la, ?_, ⟨⟨k, hk1, hk2, by rw [hw1]; exact hwk⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ hss' hc0 (LazyK.mk hss' hlz)
          · subst hst1; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
          all_goals simp only [hss', hfe', hws1, hw1, e_la]
          all_goals (try simp only [BS])
          all_goals omega
        · rename_i hgi
          have hgi' : st.insert.toNat ≤ st.strstart.toNat - sl.toNat := by
            rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hss', e_in] at hgi; omega
          refine hjp2 _ _ hd0 ⟨?_, e_la, ?_, ⟨⟨k, hk1, hk2, by rw [hw1]; exact hwk⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ hss' hc0 (LazyK.mk hss' hlz)
          · subst hst1; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
          all_goals simp only [hss', hfe', hws1, hw1, e_la, e_in]
          all_goals (try simp only [BS])
          all_goals omega
    clear_value jp1
    split
    · rename_i hms
      have hms' : sl.toNat ≤ st.match_start.toNat := by
        rw [← e_ms]; exact UInt32.le_iff_toNat_le.mp hms
      have hsub : (st1.match_start - sl).toNat = st.match_start.toNat - sl.toNat := by
        rw [sub_toNat _ _ (by rw [e_ms]; exact hms'), e_ms]
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      exact hjp1 _ st1.prev_length _ (wr_below (copyFold_wr ..) (by omega))
        (fun C => ChainOk.wrin C L (copyFold_wr ..) (by omega))
        ⟨fun _ => ⟨e_pl, by rw [hsub]; omega, UInt32.le_iff_toNat_le.mpr (by rw [hsub]; omega)⟩,
          by rw [e_pl]; exact UInt32.le_refl _⟩
    · refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      exact hjp1 _ _ _ (wr_below (copyFold_wr ..) (by omega))
        (fun C => ChainOk.wrin C L (copyFold_wr ..) (by omega))
        ⟨fun h => absurd h (by decide), UInt32.le_iff_toNat_le.mpr (by simp)⟩
  · rename_i hle
    have hle' : fe.toNat + 262 ≤ st.window_size.toNat := by
      rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, sub_toNat _ _ (by rw [hML, e_ws]; omega), e_fe, e_ws, hML] at hle
      omega
    refine Sat.pure ⟨st1, d, rfl, WrIn.refl _ _ _, fun Ch => ChainOk.st Ch (by rw [hst1]) (by rw [hst1]) (by rw [hst1])
      (by rw [hst1]) e_w e_la e_ss (by omega), LazyK.of_eq e_pl e_ms e_ss, ⟨by rw [hst1]; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩, e_la, ?_, ?_, ?_,
      by rw [e_ss, e_bs]; exact ⟨Int.le_refl _, id⟩⟩⟩
    · rw [e_ss, e_fe]; exact hsf
    · refine ⟨⟨k, hk1, hk2, by rw [e_w]; exact hwk⟩, by rw [e_fe, e_w]; exact hm, by rw [e_fe, e_ws]; exact hle',
        by rw [e_in, e_ss]; exact C.ins, by rw [e_bs, e_ss]; exact C.bs_hi, by rw [e_bs]; exact C.bs_lo⟩
    · rw [e_ss, e_la, e_ws]; exact hlook

end

end ZlibNgF.Proof.FillSlide
