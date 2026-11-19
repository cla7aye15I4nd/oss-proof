import ZlibNgF.Proof.«inflate.c.dict»

/-!
# `updatewindow` and `inflateSetDictionary` (`ZlibNgF`)

`updatewindow` without a check value (`cksum == 0`), from a source outside the state block: the copies stay inside
the 32768 window bytes of the block, and the window fields keep their clauses (`WinOk`). Then `inflateSetDictionary`
on an invariant stream. Its `DICT` branch calls `adler32_c` on the dictionary; the lemma takes the safety of
`adler32_c` on a readable buffer as `AdlerSafe`, proved in `Proof/adler32_c.c.safety.lean`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateWindow
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNgF.Proof.InflateDict
open ZlibNgF.Proof.InflateInv (Inv Core Shape Live view ldState_app ldStream_app setZS upd_upd)
open ZlibNgF.Proof.InflateAlloc (bind_mf bind_fm bind_ff)

macro "u32_omega" : tactic => `(tactic| (simp only [UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, ← UInt32.toNat_inj,
  UInt32.toNat_add, UInt32.toNat_sub, UInt32.toNat_ofNat, UInt32.toNat_zero, ne_eq] at *; omega))

/-- The window clauses of the invariant for `wsize`, `whave`, `wnext`. -/
structure WinOk (ws wh wn : UInt32) : Prop where
  whave : wh ≤ ws
  wnext : wn = 0 ∨ wn < ws
  le : wn ≤ wh
  eq : wh < ws → wn = wh

/-- `updatewindow` after the `wsize` set-up. -/
def uwTail (strm : StreamPtr) (st : StatePtr) (end_ : BPtr) (len : UInt32) (cksum : Int32) : M Unit := do
  let s ← ldState st
  let window ← s.window.get
  if len >= s.wsize then
    if cksum != 0 then
      if len > s.wsize then
        inf_chksum strm (← end_.add (-(Int.ofNat len.toNat))) (len - s.wsize)
      inf_chksum_cpy strm window (← end_.add (-(Int.ofNat s.wsize.toNat))) s.wsize
    else
      Ptr.memcpy window (← end_.add (-(Int.ofNat s.wsize.toNat))) s.wsize.toNat
    wrS st fun s => { s with wnext := 0 }
    wrS st fun s => { s with whave := s.wsize }
  else
    let dist := s.wsize - s.wnext
    let dist := if dist > len then len else dist
    if cksum != 0 then
      inf_chksum_cpy strm (← window.add (Int.ofNat s.wnext.toNat)) (← end_.add (-(Int.ofNat len.toNat))) dist
    else
      Ptr.memcpy (← window.add (Int.ofNat s.wnext.toNat)) (← end_.add (-(Int.ofNat len.toNat))) dist.toNat
    let len := len - dist
    if len != 0 then
      if cksum != 0 then
        inf_chksum_cpy strm window (← end_.add (-(Int.ofNat len.toNat))) len
      else
        Ptr.memcpy window (← end_.add (-(Int.ofNat len.toNat))) len.toNat
      wrS st fun s => { s with wnext := len }
      wrS st fun s => { s with whave := s.wsize }
    else
      wrS st fun s => { s with wnext := s.wnext + dist }
      if (← rdS st (·.wnext)) == (← rdS st (·.wsize)) then
        wrS st fun s => { s with wnext := 0 }
      if (← rdS st (·.whave)) < (← rdS st (·.wsize)) then
        wrS st fun s => { s with whave := s.whave + dist }

theorem uw_split (strm : StreamPtr) (end_ : BPtr) (len : UInt32) (cksum : Int32) :
    updatewindow strm end_ len cksum = (do
      let st ← stateOf strm
      if (← rdS st (·.wsize)) == 0 then
        let wb ← rdS st (·.wbits)
        let w ← shl32 1 wb
        wrS st fun s => { s with wsize := w }
      uwTail strm st end_ len cksum) := rfl

/-- `p - k` inside an object. -/
theorem add_neg {h : Heap} {r : BRef} {off k : Nat} {a : Array UInt8} (hb : Space.get h r = some a)
    (hk : k ≤ off) (ho : off ≤ a.size) :
    Ptr.add (Ptr.ref r off) (-(Int.ofNat k)) h = .ok (.ref r (off - k), h) := by
  have e : ((off : Int) + -Int.ofNat k).toNat = off - k := by simp only [Int.ofNat_eq_natCast]; omega
  have hc : off ≤ a.size ∧ 0 ≤ (off : Int) + -Int.ofNat k ∧ (off : Int) + -Int.ofNat k ≤ (a.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [Ptr.add, hb, hc, and_self, ↓reduceIte, e]

theorem space_get_ne {h : Heap} {b : Nat} {r : BRef} (x : Option (Array UInt8)) (hr : r ≠ .heap b) :
    Space.get ({ h with bytes := upd h.bytes b x } : Heap) r = Space.get h r := by
  cases r with
  | heap b' =>
    have : b' ≠ b := fun e => hr (e ▸ rfl)
    show upd h.bytes b x b' = h.bytes b'
    exact upd_ne _ _ _ _ this
  | const _ => rfl
  | str _ => rfl

/-- The tail of `updatewindow` without a check value, from `len` bytes of another object ending at `end`. -/
theorem uwTail_ok {H : Heap} {i b woff os : Nat} {data sd : Array UInt8} {s : InflateState} {r : BRef}
    {len : UInt32} (hd : H.bytes b = some data) (hs : H.istates b = some s)
    (hwin : s.window = .val (.ref (.heap b) woff)) (hsz : woff + 32832 ≤ data.size) (hws : s.wsize.toNat ≤ 32768)
    (W : WinOk s.wsize s.whave s.wnext) (hr : r ≠ .heap b) (hsd : Space.get H r = some sd)
    (hos : os + len.toNat ≤ sd.size) :
    ∃ d' wh wn, d'.size = data.size ∧ WinOk s.wsize wh wn ∧
      uwTail (some i) (some b) (.ref r (os + len.toNat)) len 0 H =
        .ok ((), { H with bytes := upd H.bytes b (some d'),
                          istates := upd H.istates b (some { s with wnext := wn, whave := wh }) }) := by
  have hr' : BRef.heap b ≠ r := fun e => hr e.symm
  have hwh := W.whave
  have hwl := W.le
  have hwe := W.eq
  have hwn := W.wnext
  have hist : H.istate b = some s := by simp [Heap.istate, hd, hs]
  by_cases hA : s.wsize ≤ len
  · have hA' : s.wsize.toNat ≤ len.toNat := hA
    have e1 := add_neg (k := s.wsize.toNat) hsd (by omega) hos
    have e2 := memcpy_heap (n := s.wsize.toNat) (od := woff) (os := os + len.toNat - s.wsize.toNat) hd hsd hr
      (by omega) (by omega)
    refine ⟨copyFold sd woff (os + len.toNat - s.wsize.toNat) (List.range' 0 s.wsize.toNat) data, s.wsize, 0,
      copyFold_size .., ⟨UInt32.le_refl _, Or.inl rfl, by u32_omega, fun h => absurd h
      (UInt32.lt_irrefl _)⟩, ?_⟩
    simp only [uwTail, bind_app, ldState_app hist, hwin, Ival.get, pure_app, hA, ↓reduceIte,
      show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, e1, e2]
    simp [ZlibNg.Inflate.wrS, ldState, stState, Heap.istate, upd_upd, hs, hwin]
  · have hB : len < s.wsize := UInt32.not_le.mp hA
    have hB' : len.toNat < s.wsize.toNat := hB
    have hn' : s.wnext.toNat ≤ s.whave.toNat := hwl
    have hh' : s.whave.toNat ≤ s.wsize.toNat := hwh
    obtain ⟨D, hD⟩ : ∃ D, D = (if s.wsize - s.wnext > len then len else s.wsize - s.wnext) := ⟨_, rfl⟩
    have hDn : D.toNat ≤ len.toNat ∧ s.wnext.toNat + D.toNat ≤ s.wsize.toNat ∧
        (D.toNat < len.toNat → D.toNat = s.wsize.toNat - s.wnext.toNat) := by
      have hsub : (s.wsize - s.wnext).toNat = s.wsize.toNat - s.wnext.toNat :=
        UInt32.toNat_sub_of_le _ _ (by u32_omega)
      by_cases hc : s.wsize - s.wnext > len
      · simp only [hD, hc, ↓reduceIte]; have : len.toNat < (s.wsize - s.wnext).toNat := hc; omega
      · simp only [hD, hc, ↓reduceIte]; have : ¬ len.toNat < (s.wsize - s.wnext).toNat := hc; omega
    have e1 := add_heap (off := woff) (k := s.wnext.toNat) hd (by omega)
    have e2 := add_neg (k := len.toNat) hsd (by omega) hos
    rw [Nat.add_sub_cancel] at e2
    have e3 := memcpy_heap (n := D.toNat) (od := woff + s.wnext.toNat) (os := os) hd hsd hr (by omega) (by omega)
    let d1 := copyFold sd (woff + s.wnext.toNat) os (List.range' 0 D.toNat) data
    have hd1 : d1.size = data.size := copyFold_size ..
    let H1 : Heap := { H with bytes := upd H.bytes b (some d1) }
    have hH1 : H1.bytes b = some d1 := upd_same _ _ _
    have hsd1 : Space.get H1 r = some sd := by rw [space_get_ne _ hr]; exact hsd
    have hlen : (len - D).toNat = len.toNat - D.toNat := UInt32.toNat_sub_of_le _ _ (by u32_omega)
    by_cases hL : len - D = 0
    · -- the copy fits before the end of the window
      have hDl : D.toNat = len.toNat := by
        have : (len - D).toNat = 0 := by rw [hL]; rfl
        omega
      have hL0 : (len - D != 0) = false := by simpa using hL
      have hw1 := s.wsize.toNat_lt
      refine ⟨d1, if s.whave < s.wsize then s.whave + D else s.whave,
        if s.wnext + D = s.wsize then 0 else s.wnext + D, hd1, ?_, ?_⟩
      · have hE := hwe
        by_cases hx : s.wnext + D = s.wsize <;> by_cases hy : s.whave < s.wsize <;>
          simp only [hx, hy, ↓reduceIte] <;>
          refine ⟨?_, ?_, ?_, ?_⟩ <;> (try have hE' := hE hy) <;> u32_omega
      · simp only [uwTail, bind_app, ldState_app hist, hwin, Ival.get, pure_app, hA, ↓reduceIte,
          show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, e1, e2, ← hD, e3]
        simp only [hL0, ↓reduceIte, Bool.false_eq_true]
        by_cases hx : s.wnext + D = s.wsize <;> by_cases hy : s.whave < s.wsize <;>
          simp [ZlibNg.Inflate.wrS, rdS, ldState, stState, Heap.istate, upd_upd, hs, hwin, hx, hy, d1]
    · have hL' : len.toNat - D.toNat ≠ 0 := by
        intro h0; apply hL; rw [← UInt32.toNat_inj, hlen, h0]; rfl
      have hDw : D.toNat = s.wsize.toNat - s.wnext.toNat := hDn.2.2 (by omega)
      have e4 := add_neg (h := H1) (k := (len - D).toNat) hsd1 (by omega) hos
      have e5 := memcpy_heap (h := H1) (n := (len - D).toNat) (od := woff) (os := os + len.toNat - (len - D).toNat)
        hH1 hsd1 hr (by omega) (by omega)
      refine ⟨copyFold sd woff (os + len.toNat - (len - D).toNat) (List.range' 0 (len - D).toNat) d1, s.wsize,
        len - D, by rw [copyFold_size, hd1], ⟨UInt32.le_refl _, Or.inr (by u32_omega), by u32_omega,
        fun h => absurd h (UInt32.lt_irrefl _)⟩, ?_⟩
      have hL0 : (len - D != 0) = true := by simpa using hL
      simp only [uwTail, bind_app, ldState_app hist, hwin, Ival.get, pure_app, hA, ↓reduceIte,
        show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, e1, e2, ← hD, e3]
      simp only [hL0, ↓reduceIte]
      simp only [H1, d1, Int.ofNat_eq_natCast] at e4 e5
      simp [ZlibNg.Inflate.wrS, ldState, stState, Heap.istate, upd_upd, hs, hwin, e4, e5, d1]

/-- The invariant after a change of the window bytes (same size) and of the window fields. -/
theorem core_win {h h' : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st : InflateState} {al : InflateAllocs}
    {d' : Array UInt8} (c : Core h s z b (view st) al) (hb : h'.bytes b = some d')
    (hsz : ∀ d, h.bytes b = some d → d'.size = d.size) (hg : h'.gzheaders = h.gzheaders) (ws wh wn : UInt32)
    (hws : ws ≤ 32768) (W : WinOk ws wh wn) :
    Core h' s z b (view { st with wsize := ws, whave := wh, wnext := wn }) al where
  toShape := { c.toShape with
    window := by
      obtain ⟨woff, data, e1, e2, e3, e4⟩ := c.window
      exact ⟨woff, d', e1, e2, hb, by rw [hsz data e3]; exact e4⟩ }
  wbits := c.wbits
  reqbits := c.reqbits
  wsize := hws
  whave := W.whave
  wnext := W.wnext
  wnext_le := W.le
  wnext_eq := W.eq
  bits := c.bits
  lencode := c.lencode
  distcode := c.distcode
  next := c.next
  tables := c.tables
  head := by rw [hg]; exact c.head
  modes := c.modes
  extraLen := by unfold InflateInv.ExtraOK; rw [hg]; exact c.extraLen

theorem shl_toNat (w : UInt32) (hw : w ≤ 15) : ((1 : UInt32) <<< w).toNat = 2 ^ w.toNat := by
  have hw' : w.toNat ≤ 15 := hw
  rw [UInt32.toNat_shiftLeft]
  have e1 : (1 : UInt32).toNat = 1 := rfl
  rw [e1, Nat.mod_eq_of_lt (by omega : w.toNat < 32), Nat.shiftLeft_eq, Nat.one_mul]
  have : 2 ^ w.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hw'
  exact Nat.mod_eq_of_lt (by omega)

/-- `updatewindow(strm, end, len, 0)` on an invariant stream, from `len` bytes of another object ending at `end`:
only the window bytes and the window fields of the state change, and the invariant holds after. -/
theorem updatewindow_ok {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} {al : InflateAllocs}
    {r : BRef} {os : Nat} {sd : Array UInt8} {len : UInt32} (L : Live h i z b st) (hal : h.iallocsOf b = some al)
    (c : Core h (some i) z b (view st) al) (hr : r ≠ .heap b) (hsd : Space.get h r = some sd)
    (hos : os + len.toNat ≤ sd.size) :
    ∃ d' ws wh wn, updatewindow (some i) (.ref r (os + len.toNat)) len 0 h =
        .ok ((), { h with bytes := upd h.bytes b (some d'),
                          istates := upd h.istates b (some { st with wsize := ws, whave := wh, wnext := wn }) }) ∧
      Inv { h with bytes := upd h.bytes b (some d'),
                   istates := upd h.istates b (some { st with wsize := ws, whave := wh, wnext := wn }) } (some i) := by
  obtain ⟨woff, data, hwin, hdata, hwsz, hws, hwh, hwn⟩ := window_nat c
  have hdz : ∀ d, h.bytes b = some d → ∀ d' : Array UInt8, d'.size = data.size → d'.size = d.size := by
    intro d hd d' e; rw [hdata] at hd; cases hd; exact e
  have hinv : ∀ (d' : Array UInt8) (ws wh wn : UInt32), d'.size = data.size →
      ws ≤ 32768 → WinOk ws wh wn →
      Inv { h with bytes := upd h.bytes b (some d'),
                   istates := upd h.istates b (some { st with wsize := ws, whave := wh, wnext := wn }) } (some i) := by
    intro d' ws wh wn hsz hws W
    refine ⟨i, z, b, { st with wsize := ws, whave := wh, wnext := wn }, al, rfl, L.hz, L.hb,
      by simp [Heap.istate], ?_, ?_⟩
    · simp only [Heap.iallocsOf, upd_same]; simpa [Heap.iallocsOf, hdata] using hal
    · refine core_win (h := h) c ?_ (fun d hd => hdz d hd d' hsz) ?_ ws wh wn hws W
      · exact upd_same _ _ _
      · rfl
  by_cases h0 : st.wsize = 0
  · have hwb : st.wbits ≤ 15 := c.wbits
    have hwb' : st.wbits.toNat ≤ 15 := hwb
    let st1 : InflateState := { st with wsize := (1 : UInt32) <<< st.wbits }
    let H0 : Heap := { h with istates := upd h.istates b (some st1) }
    have hwh0 : st.whave = 0 := by have : st.whave ≤ st.wsize := c.whave; rw [h0] at this; u32_omega
    have hwn0 : st.wnext = 0 := by have : st.wnext ≤ st.whave := c.wnext_le; rw [hwh0] at this; u32_omega
    have W1 : WinOk st1.wsize st1.whave st1.wnext := by
      refine ⟨?_, Or.inl hwn0, ?_, fun _ => hwn0.trans hwh0.symm⟩
      · show st.whave ≤ _; rw [hwh0]; u32_omega
      · show st.wnext ≤ st.whave; rw [hwn0, hwh0]; exact UInt32.le_refl _
    have hws1 : st1.wsize.toNat ≤ 32768 := by
      show ((1 : UInt32) <<< st.wbits).toNat ≤ 32768
      rw [shl_toNat _ hwb]
      have : 2 ^ st.wbits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hwb'
      omega
    obtain ⟨d', wh, wn, hsz, W, e⟩ := uwTail_ok (H := H0) (i := i) (s := st1) (os := os) (len := len) hdata
      (by simp [H0]) hwin hwsz hws1 W1 hr hsd hos
    refine ⟨d', (1 : UInt32) <<< st.wbits, wh, wn, ?_, hinv d' _ wh wn hsz (InflateInv.shl_le _ hwb) W⟩
    have hlt : st.wbits < 32 := by u32_omega
    rw [uw_split]
    simp only [bind_app, L.stateOf, rdS, ldState_app L.istate, pure_app, h0, beq_self_eq_true, ↓reduceIte,
      shl32, hlt]
    have ew : ZlibNg.Inflate.wrS (some b) (fun s => { s with wsize := (1 : UInt32) <<< st.wbits }) h =
        .ok ((), H0) := by
      obtain ⟨dd, hdd⟩ := L.hd
      simp [ZlibNg.Inflate.wrS, ldState, stState, Heap.istate, hdd, L.hst, H0, st1]
    rw [ew]
    simp only [e, H0, upd_upd, st1]
  · obtain ⟨d', wh, wn, hsz, W, e⟩ := uwTail_ok (H := h) (i := i) (s := st) (os := os) (len := len) hdata
      L.hst hwin hwsz hws ⟨c.whave, c.wnext, c.wnext_le, c.wnext_eq⟩ hr hsd hos
    refine ⟨d', st.wsize, wh, wn, ?_, hinv d' _ wh wn hsz c.wsize W⟩
    rw [uw_split]
    have h0' : (st.wsize == 0) = false := by simpa using h0
    simp only [bind_app, L.stateOf, rdS, ldState_app L.istate, pure_app, h0', Bool.false_eq_true, ↓reduceIte, e]

/-! ## `inflateSetDictionary` -/

/-- `adler32_c` does not fault on a readable buffer and changes nothing (the safety of the Adler-32 kernel). -/
def AdlerSafe : Prop :=
  ∀ (h : Heap) (a : UInt32) (r : BRef) (o : Nat) (data : Array UInt8) (n : UInt64),
    Space.get h r = some data → o + n.toNat ≤ data.size →
    ∃ v, C.run (ZlibNg.Adler32C.adler32_c a (.ref r o) n) h = .ok (v, h)

/-- `p + k` inside an object. -/
theorem add_ref {h : Heap} {r : BRef} {off k : Nat} {a : Array UInt8} (hb : Space.get h r = some a)
    (hk : off + k ≤ a.size) : Ptr.add (Ptr.ref r off) (Int.ofNat k) h = .ok (.ref r (off + k), h) := by
  have e : ((off : Int) + Int.ofNat k).toNat = off + k := by simp only [Int.ofNat_eq_natCast]; omega
  have hc : off ≤ a.size ∧ 0 ≤ (off : Int) + Int.ofNat k ∧ (off : Int) + Int.ofNat k ≤ (a.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [Ptr.add, hb, hc, and_self, ↓reduceIte, e]

/-- A change of the bytes and the state of block `b` is in the frame that names `b`. -/
theorem frame_blk (h : Heap) (b : Nat) (x : Option (Array UInt8)) (y : Option InflateState) (ss : List Nat) :
    Frame h { h with bytes := upd h.bytes b x, istates := upd h.istates b y } ss [b] [] [] := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun b' _ hb => ?_, fun b' _ hb data hd => ?_, fun b' _ hb hn => ?_,
    rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  · have e : b' ≠ b := by simpa using hb
    exact ⟨upd_ne _ _ _ _ e, rfl⟩
  · have e : b' ≠ b := by simpa using hb
    exact ⟨data, by simp only [upd_ne _ _ _ _ e]; exact hd, rfl, fun _ _ _ => rfl⟩
  · have e : b' ≠ b := by simpa using hb
    simp only [upd_ne _ _ _ _ e]; exact hn

theorem setDict_noState {h : Heap} {s : StreamPtr} (hn : InflateControl.NoState h s) (d : BPtr) (n : UInt32) :
    C.run (inflateSetDictionary s d n) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateSetDictionary, bind_app,
    show inflateStateCheck s h = .ok (true, h) from InflateControl.stateCheck_noState hn]

/-- `inflateSetDictionary` on an invariant stream: no fault (given the safety of `adler32_c`), only the stream's block
changes, the invariant holds after. -/
theorem setDict_inv (A : AdlerSafe) {h : Heap} {s : StreamPtr} {d : BPtr} {n : UInt32} (hv : Inv h s)
    (hd : NullOrRead h d n.toNat) (hnb : ∀ b, StateBlock h s b → NotInBlock b d) :
    ∃ r h', C.run (inflateSetDictionary s d n) h = .ok (r, h') ∧ Inv h' s ∧
      Frame h h' (streamIds s) (stateIds h s) [] [] := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  have hids : stateIds h (some i) = [b] := by simp [stateIds, L.hz, L.hb]
  rw [hids]
  rcases hd with rfl | ⟨r, off, sd, rfl, hsd, hoff⟩
  · exact ⟨Z_STREAM_ERROR, h, by simp [C.run, inflateSetDictionary, bind_app, L.check, L.stateOf], hv,
      InflateInit.frame_refl h _ _ _ _⟩
  have hr : r ≠ .heap b := fun e => by subst e; exact hnb b ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩ off rfl
  have tail : ∃ h', (do
      updatewindow (some i) (← (Ptr.ref r off).add (Int.ofNat n.toNat)) n 0
      ZlibNg.Inflate.wrS (some b) fun s => { s with havedict := 1 }
      return Z_OK : M Int32) h = .ok (Z_OK, h') ∧ Inv h' (some i) ∧ Frame h h' [i] [b] [] [] := by
    obtain ⟨d', ws, wh, wn, eU, hinv1⟩ := updatewindow_ok L hal c hr hsd hoff
    let st1 : InflateState := { st with wsize := ws, whave := wh, wnext := wn }
    let H1 : Heap := { h with bytes := upd h.bytes b (some d'), istates := upd h.istates b (some st1) }
    have hsa : ∃ z', StreamAt H1 (some i) z' ∧ z'.state = some b := ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩
    obtain ⟨eW, hinv2⟩ := InflateInv.wrS (st := st1) hinv1 (fun s => { s with havedict := 1 }) hsa
      (by simp only [Heap.istate, upd_same]; rfl) (fun _ _ c => c)
    refine ⟨_, ?_, hinv2, ?_⟩
    · simp only [bind_app, add_ref hsd hoff, eU]
      simp only [C.run] at eW
      rw [eW]; rfl
    · simp only [upd_upd]
      exact frame_blk h b _ _ _
  have hn0 : (Ptr.ref r off == Ptr.null) = false := rfl
  by_cases hc1 : (st.wrap != 0 && st.mode != DICT) = true
  · exact ⟨Z_STREAM_ERROR, h, by
      simp only [C.run, inflateSetDictionary, bind_app, L.check, L.stateOf, hn0, ldState_app L.istate, hc1,
        Bool.false_eq_true, ↓reduceIte]; rfl, hv, InflateInit.frame_refl h _ _ _ _⟩
  have hc1' : (st.wrap != 0 && st.mode != DICT) = false := by simpa using hc1
  obtain ⟨h', et, hi', hf⟩ := tail
  by_cases hm : st.mode = DICT
  · obtain ⟨v, ev⟩ := A h ADLER32_INITIAL_VALUE.toUInt32 r off sd n.toUInt64 hsd
      (by rw [UInt32.toNat_toUInt64]; exact hoff)
    have ev' : ZlibNg.Adler32C.adler32_c ADLER32_INITIAL_VALUE.toUInt32 (.ref r off) n.toUInt64 h = .ok (v, h) := ev
    have hm'' : (st.mode == DICT) = true := by simp [hm]
    by_cases hck : (v.toUInt64 != st.check) = true
    · exact ⟨Z_DATA_ERROR, h, by
        simp only [C.run, inflateSetDictionary, bind_app, L.check, L.stateOf, hn0, ldState_app L.istate, hc1',
          Bool.false_eq_true, ↓reduceIte, hm'']
        simp only [ev', hck, ↓reduceIte]; rfl, hv, InflateInit.frame_refl h _ _ _ _⟩
    · have hck' : (v.toUInt64 != st.check) = false := by simpa using hck
      refine ⟨Z_OK, h', ?_, hi', hf⟩
      simp only [C.run, inflateSetDictionary, bind_app, L.check, L.stateOf, hn0, ldState_app L.istate, hc1',
        Bool.false_eq_true, ↓reduceIte, hm'']
      simp only [ev', hck', Bool.false_eq_true, ↓reduceIte]
      simp only [bind_app] at et
      exact et
  · have hm' : (st.mode == DICT) = false := by simpa using hm
    refine ⟨Z_OK, h', ?_, hi', hf⟩
    simp only [C.run, inflateSetDictionary, bind_app, L.check, L.stateOf, hn0, ldState_app L.istate, hc1',
      Bool.false_eq_true, ↓reduceIte, hm']
    simp only [bind_app] at et
    exact et

end ZlibNgF.Proof.InflateWindow
