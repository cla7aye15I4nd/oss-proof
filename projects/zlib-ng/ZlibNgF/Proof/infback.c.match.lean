import ZlibNgF.Proof.«infback.c.type»

/-!
# `inflateBack()`: `ROOM` on the loop state, and the mode `MATCH` (`ZlibNgF`)

`MATCH` is entered from `inflate_fast_safe_c` when a match does not fit in `left`. It checks the distance against the
window (`invalid distance too far back`), then copies the match through the window in pieces of at most `left` bytes,
calling `out()` whenever the window is full (`ROOM`). A piece comes from the end of the window (the previous pass,
`chunkcopy_safe` ahead of `put`) or from `offset` bytes back (`chunkmemset_safe_c`); both pointers are in the window.
The check, done once, keeps holding: while the window has not been flushed (`whave == 0`) the distance stays within
the bytes written (`offset <= wsize - left`, and `left` only falls), and after a flush `offset <= wsize`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InfbackRoom
open ZlibNgF.Proof.InflateLoop (withS strIdx)
open ZlibNgF.Proof.ChunkMem (ORun)
open ZlibNgF.Proof.ChunkCopy (B min_toNat)

/-! ## `ROOM` -/

/-- `ROOM()` on a state with `BM`: with room left nothing happens; otherwise `put = window`, `left = wsize`,
`whave = wsize`, and `out()` lets the decoder go on or ends the call. -/
theorem BM.room {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) {Q : Except Ex Unit → IL → Heap → Prop}
    (k1 : l.left ≠ 0 → Q (.ok ()) l H)
    (k2 : l.left = 0 → ∀ H', BM E { l with put := E.w, left := S.wsize } H' t z { S with whave := S.wsize } →
      Q (.error .leave) { l with put := E.w, left := S.wsize, ret := Z_BUF_ERROR } H' ∧
      Q (.ok ()) { l with put := E.w, left := S.wsize } H') :
    SatX H l (ROOM E.c) Q := by
  refine room_ok cb E.c rfl rfl rfl bm.sh.istate bm.sh.win bm.sh.ws bm.inB k1 ?_
  intro h0 r H' hk hin
  have sh1 : BShape E (withS H E.b { S with whave := S.wsize }) z { S with whave := S.wsize } :=
    { bm.sh with
      hs := upd_same _ _ _ }
  have bm' : BM E { l with put := E.w, left := S.wsize } H' t z { S with whave := S.wsize } := by
    refine ⟨sh1.keep hk, hin, bm.tot, ?_, ?_, Or.inr rfl⟩
    · show E.w = _
      have := bm.sh.ws
      simp only [BEnv.w, this, Nat.sub_self, Nat.add_zero]
    · show S.wsize.toNat ≤ E.n
      rw [bm.sh.ws]; exact Nat.le_refl _
  obtain ⟨a, b⟩ := k2 h0 H' bm'
  exact ⟨fun _ => a, fun _ => b⟩

/-! ## Pointers into the window -/

theorem add_heap {H : Heap} {b o : Nat} {a : Array UInt8} (hd : H.bytes b = some a) (k : Int)
    (h1 : o ≤ a.size) (h2 : 0 ≤ (o : Int) + k) (h3 : (o : Int) + k ≤ a.size) :
    (Ptr.ref (BRef.heap b) o : BPtr).add k H = .ok (.ref (.heap b) ((o : Int) + k).toNat, H) := by
  have hc : o ≤ a.size ∧ 0 ≤ (o : Int) + k ∧ (o : Int) + k ≤ (a.size : Int) := ⟨h1, h2, h3⟩
  simp only [Ptr.add, ZlibNgF.Proof.InflateDict.space_get_heap, hd, hc, and_self, ↓reduceIte]

theorem BM.winBytes {E : BEnv} {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) : ∃ a, H.bytes E.wb = some a ∧ E.woff + E.n ≤ a.size := bm.sh.wd

theorem u32_sub_le {a b : UInt32} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h)

theorem min32 (a b : UInt64) (ha : a.toNat < 2 ^ 32) : (ZlibNg.Zbuild.MIN a b).toUInt32.toNat = min a.toNat b.toNat := by
  rw [UInt64.toNat_toUInt32, min_toNat]; exact Nat.mod_eq_of_lt (by omega)

/-- `BM` after a change of the window bytes. -/
theorem BM.winW {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) {a a' : Array UInt8} (hd : H.bytes E.wb = some a) (hsz : a'.size = a.size)
    (hpt : ∀ j, (j < E.woff ∨ E.woff + E.n ≤ j) → a'[j]! = a[j]!) :
    BM E l { H with bytes := upd H.bytes E.wb (some a') } t z S :=
  bm.lstep cb (lstep_win E hd hsz hpt) (bm.sh.wW hd hsz) (Or.inl rfl)

/-- A run that changed only the window bytes. -/
theorem ORun.win {H H' : Heap} {ob N lo hi : Nat} (r : ORun H H' ob N lo hi) {a : Array UInt8}
    (hd : H.bytes ob = some a) :
    ∃ a', H' = { H with bytes := upd H.bytes ob (some a') } ∧ a'.size = a.size ∧
      ∀ j, (j < lo ∨ hi ≤ j) → a'[j]! = a[j]! := by
  obtain ⟨a0, a1, h0, h1, s0, s1, hp⟩ := r.blk
  rw [hd] at h0; cases h0
  refine ⟨a1, ?_, by omega, hp⟩
  have e := r.eq
  rw [h1] at e
  exact e

/-! ## `MATCH` -/

/-- The copy loop of `MATCH` (`infback.c:496-513`), verbatim. -/
def matchRest (c : BCtx) : X Unit := do
    let s ← ldState c.st
    modify fun l => { l with copy := s.wsize - s.offset }
    let l ← get
    if l.copy < l.left then
      let fr ← l.put.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with from_ := fr }
      modify fun l => { l with copy := l.left - l.copy }
      let len ← rdS c.st (·.length)
      modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 len.toUInt64).toUInt32 }
      let l ← get
      let safe ← l.put.add (Int.ofNat l.left.toNat)
      let pt ← chunkcopy_safe l.put l.from_ l.copy.toUInt64 safe
      modify fun l => { l with put := pt }
    else
      let len ← rdS c.st (·.length)
      modify fun l => { l with copy := (ZlibNg.Zbuild.MIN len.toUInt64 l.left.toUInt64).toUInt32 }
      let l ← get
      let off ← rdS c.st (·.offset)
      let src ← l.put.add (-(Int.ofNat off.toNat))
      let pt ← ZlibNg.ChunksetC.chunkmemset_safe_c l.put src l.copy.toUInt64 l.left.toUInt64
      modify fun l => { l with put := pt }
    let copy := (← get).copy
    wrS c.st fun s => { s with length := s.length - copy }
    modify fun l => { l with left := l.left - l.copy }

def matchBody (c : BCtx) : X Unit := do
  ROOM c
  matchRest c

theorem back_MATCH_eq (c : BCtx) : back_MATCH c = (do
    let s ← ldState c.st
    let left := (← get).left
    if s.offset > s.wsize - (if s.whave < s.wsize then left else 0) then
      SET_BAD c.ctx "invalid distance too far back"
      return
    matchBody c
    xwhile (do return (← rdS c.st (·.length)) != 0) (matchBody c)
    setMode c.st LEN) := rfl

theorem add_nat {H : Heap} {b o : Nat} {a : Array UInt8} (hd : H.bytes b = some a) (j : Nat) (h : o + j ≤ a.size) :
    (Ptr.ref (BRef.heap b) o : BPtr).add (Int.ofNat j) H = .ok (.ref (.heap b) (o + j), H) := by
  have e : Int.ofNat j = (j : Int) := rfl
  rw [e, add_heap hd _ (by omega) (by omega) (by omega)]
  congr 2

theorem add_neg {H : Heap} {b o : Nat} {a : Array UInt8} (hd : H.bytes b = some a) (j : Nat) (h : o ≤ a.size)
    (hj : j ≤ o) : (Ptr.ref (BRef.heap b) o : BPtr).add (-(Int.ofNat j)) H = .ok (.ref (.heap b) (o - j), H) := by
  rw [add_heap hd _ h (by simp; omega) (by simp; omega)]
  congr 3
  simp; omega

/-- The state of the copy loop of `MATCH`, entered with `b0` bits held and `h0` input bytes. -/
structure MP (E : BEnv) (b0 : UInt8) (h0 : UInt32) (l : IL) (H : Heap) (t : Nat) (z : ZStream) (S : InflateState) :
    Prop where
  bm : BM E l H t z S
  mode : S.mode = MATCH
  tabs : RTab E.b S.codes S.lencode S.lenbits 28 false ∧ RTab E.b S.codes S.distcode S.distbits 28 true
  bits : l.bits = b0
  hv : l.have_ = h0
  off1 : 1 ≤ S.offset.toNat
  offw : S.offset.toNat ≤ E.n
  near : S.whave = 0 → S.offset.toNat ≤ E.n - l.left.toNat

/-- The outcome of one piece of the copy. -/
def MPost (E : BEnv) (b0 : UInt8) (h0 : UInt32) (t : Nat) (len : Nat) : Except Ex Unit → IL → Heap → Prop
  | .ok (), l, H => ∃ z S, MP E b0 h0 l H t z S ∧ (len ≠ 0 → S.length.toNat < len)
  | .error .leave, l, H => BLv E l H
  | .error (.ret _), _, _ => False

/-- The statements after the copy of one piece: `length -= copy`, `left -= copy`. -/
theorem match_fin {E : BEnv} (cb : E.CB) {b0 : UInt8} {h0 : UInt32} {l l2 : IL} {H H2 : Heap} {t : Nat}
    {z : ZStream} {S : InflateState} (mp : MP E b0 h0 l H t z S) (bmH : BM E l H2 t z S)
    (e1 : l2.next = l.next) (e2 : l2.have_ = l.have_) (e3 : l2.bits = l.bits) (e4 : l2.left = l.left)
    (hput : l2.put = .ref (.heap E.wb) (E.woff + (E.n - l.left.toNat) + l2.copy.toNat))
    (hcl : l2.copy.toNat ≤ l.left.toNat) (hcn : l2.copy.toNat ≤ S.length.toNat)
    (hc1 : S.length ≠ 0 → 1 ≤ l2.copy.toNat) :
    SatX H2 l2 (do
      let __do_lift ← get
      liftM (wrS E.c.st fun s => { s with length := s.length - __do_lift.copy })
      modify fun l => { l with left := l.left - l.copy } : X Unit) (MPost E b0 h0 t S.length.toNat) := by
  refine SatX.bind (SatX.get ?_)
  dsimp only [BEnv.c]
  refine SatX.bind (SatX.lift (Sat.of_eq (bmH.sh.wrS _) ?_))
  have bm3 := bmH.wS cb (S' := { S with length := S.length - l2.copy }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.modify ⟨z, _, ⟨⟨bm3.sh, InB.locals bm3.inB e2 e1, by rw [e2]; exact bm3.tot, ?_, ?_, bm3.whave⟩,
    mp.mode, mp.tabs, e3.trans mp.bits, e2.trans mp.hv, mp.off1, mp.offw, ?_⟩, ?_⟩
  · show l2.put = _
    rw [hput, u32_sub_le (by rw [e4]; exact hcl), e4]
    have := mp.bm.left
    simp only [Ptr.ref.injEq, true_and]; omega
  · show (l2.left - l2.copy).toNat ≤ E.n
    rw [u32_sub_le (by rw [e4]; exact hcl), e4]
    have := mp.bm.left; omega
  · intro hw
    show S.offset.toNat ≤ E.n - (l2.left - l2.copy).toNat
    rw [u32_sub_le (by rw [e4]; exact hcl), e4]
    have := mp.near hw; omega
  · intro hne
    show (S.length - l2.copy).toNat < S.length.toNat
    have h1 := hc1 (fun e => hne (by rw [e]; rfl))
    rw [u32_sub_le hcn]; omega

theorem match_rest {E : BEnv} (cb : E.CB) {b0 : UInt8} {h0 : UInt32} {l : IL} {H : Heap}
    {t : Nat} {z : ZStream} {S : InflateState} (mp : MP E b0 h0 l H t z S) (hl : l.left ≠ 0) :
    SatX H l (matchRest E.c) (MPost E b0 h0 t S.length.toNat) := by
  have bm := mp.bm
  have hn := bm.sh.ws
  have hL : l.left.toNat ≤ E.n := bm.left
  have hL1 : 1 ≤ l.left.toNat := u32_ne_zero hl
  have hD1 := mp.off1
  have hDn := mp.offw
  have hn15 := bm.sh.n_le
  obtain ⟨a, ha, haN⟩ := bm.winBytes
  have hput := bm.put
  unfold matchRest
  refine SatX.bind (liftEq bm.sh.ldState ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  have ec : (S.wsize - S.offset).toNat = E.n - S.offset.toNat := by rw [u32_sub_le (by omega), hn]
  split
  · rename_i hlt
    have hlt' : E.n - S.offset.toNat < l.left.toNat := by rw [← ec]; exact UInt32.lt_iff_toNat_lt.mp hlt
    rw [hput]
    refine SatX.bind (liftEq (add_nat ha _ (by rw [ec]; omega)) ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (liftEq (bm.sh.rdS _) ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.get ?_)
    dsimp only
    refine SatX.bind (liftEq (add_nat ha _ (by omega)) ?_)
    have ec2 : (l.left - (S.wsize - S.offset)).toNat = l.left.toNat - (E.n - S.offset.toNat) := by
      rw [u32_sub_le (by omega), ec]
    have ecp : (ZlibNg.Zbuild.MIN (l.left - (S.wsize - S.offset)).toUInt64 S.length.toUInt64).toUInt32.toNat =
        min (l.left.toNat - (E.n - S.offset.toNat)) S.length.toNat := by
      rw [min32 _ _ (by rw [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _), UInt32.toNat_toUInt64,
        UInt32.toNat_toUInt64, ec2]
    generalize (ZlibNg.Zbuild.MIN (l.left - (S.wsize - S.offset)).toUInt64 S.length.toUInt64).toUInt32 = cp at ecp ⊢
    have r0 := ORun.refl ha rfl E.woff (E.woff + E.n)
    have hcp : cp.toUInt64.toNat = cp.toNat := UInt32.toNat_toUInt64 cp
    obtain ⟨pt, H', e, hpt, r'⟩ := ZlibNgF.Proof.ChunkcopySafe.sat_chunkcopy_safe_ahead r0 cp.toUInt64
      (o := E.woff + (E.n - l.left.toNat)) (f := E.woff + (E.n - l.left.toNat) + (S.wsize - S.offset).toNat)
      (s := E.woff + (E.n - l.left.toNat) + l.left.toNat) (by omega) (by omega) (by omega) (by omega) haN
      (by rw [hcp, ec]; omega) (by omega) (by rw [ec]; omega)
    refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
    obtain ⟨a', rfl, hsz, hout⟩ := ORun.win r' ha
    have bmH := bm.winW cb ha hsz hout
    refine SatX.bind (SatX.modify ?_)
    refine match_fin cb mp bmH rfl rfl rfl rfl ?_ (by rw [ecp]; omega) (by rw [ecp]; omega)
      (fun hne => by have := u32_ne_zero hne; rw [ecp]; omega)
    show pt = _
    have : cp.toNat ≤ l.left.toNat := by rw [ecp]; omega
    rw [hpt, hcp]
    simp only [B, Ptr.ref.injEq, true_and]
    omega
  · rename_i hge
    have hge' : l.left.toNat ≤ E.n - S.offset.toNat := by
      rw [← ec]; exact Nat.le_of_not_lt (fun h => hge (UInt32.lt_iff_toNat_lt.mpr h))
    refine SatX.bind (liftEq (bm.sh.rdS _) ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.get ?_)
    refine SatX.bind (liftEq (bm.sh.rdS _) ?_)
    dsimp only
    rw [hput]
    refine SatX.bind (liftEq (add_neg ha _ (by omega) (by omega)) ?_)
    have ecp : (ZlibNg.Zbuild.MIN S.length.toUInt64 l.left.toUInt64).toUInt32.toNat =
        min S.length.toNat l.left.toNat := by
      rw [min32 _ _ (by rw [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _), UInt32.toNat_toUInt64,
        UInt32.toNat_toUInt64]
    generalize (ZlibNg.Zbuild.MIN S.length.toUInt64 l.left.toUInt64).toUInt32 = cp at ecp ⊢
    have hcp : cp.toUInt64.toNat = cp.toNat := UInt32.toNat_toUInt64 cp
    have hlp : l.left.toUInt64.toNat = l.left.toNat := UInt32.toNat_toUInt64 _
    obtain ⟨a', e, hsz, hout⟩ := ZlibNgF.Proof.InffastFacts.copyFacts.memset H E.wb (E.woff + (E.n - l.left.toNat))
      S.offset.toNat a cp.toUInt64 l.left.toUInt64 ha hD1 (by omega) (by omega) (by rw [hlp]; omega)
      (by rw [UInt64.le_iff_toNat_le, hcp, hlp]; omega) (by rw [UInt64.le_iff_toNat_le, hlp]; exact hL1)
    refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
    have bmH := bm.winW cb ha hsz (fun j hj => hout j (by rw [hlp]; omega))
    refine SatX.bind (SatX.modify ?_)
    refine match_fin cb mp bmH rfl rfl rfl rfl ?_ (by rw [ecp]; omega) (by rw [ecp]; omega)
      (fun hne => by
        have : 1 ≤ S.length.toNat := u32_ne_zero hne
        rw [ecp]; omega)
    show Ptr.ref _ _ = _
    rw [hcp]

theorem match_body {E : BEnv} (cb : E.CB) {b0 : UInt8} {h0 : UInt32} {l : IL} {H : Heap}
    {t : Nat} {z : ZStream} {S : InflateState} (mp : MP E b0 h0 l H t z S) :
    SatX H l (matchBody E.c) (MPost E b0 h0 t S.length.toNat) := by
  unfold matchBody
  refine SatX.bind (mp.bm.room cb (fun hl => match_rest cb mp hl) ?_)
  intro _ H' bm'
  have hn := mp.bm.sh.ws
  have hn1 := mp.bm.sh.n_pos
  have hw0 : S.wsize ≠ 0 := fun e => by rw [e] at hn; simp at hn; omega
  refine ⟨(bm'.locals rfl rfl rfl rfl).leave, ?_⟩
  exact match_rest cb (S := { S with whave := S.wsize }) ⟨bm', mp.mode, mp.tabs, mp.bits, mp.hv, mp.off1, mp.offw,
    fun e => absurd e hw0⟩ hw0

theorem rank_MATCH : rank MATCH = 2 := by decide
theorem rank_LEN : rank LEN = 1 := by decide
theorem rank_BAD : rank BAD = 0 := by decide

/-- The measure of the copy loop: the `length` of the state. -/
def lenRank (E : BEnv) (H : Heap) : Nat := match H.istate E.b with | some S => S.length.toNat | none => 0

theorem MP.rk {E : BEnv} {b0 : UInt8} {h0 : UInt32} {l : IL} {H : Heap} {t : Nat} {z : ZStream}
    {S : InflateState} (mp : MP E b0 h0 l H t z S) : lenRank E H = S.length.toNat := by
  unfold lenRank; rw [mp.bm.sh.istate]

theorem run_MATCH (E : BEnv) : ModeRun E back_MATCH (fun S => S.mode = MATCH) := by
  intro cb l H t z S bl hm m hμ
  have hb8 : l.bits.toNat < 8 := by
    rcases bl.bits with e | e
    · rw [hm] at e; exact absurd e (by decide)
    · exact e
  have hμ' : 32 * (8 * (l.have_.toNat + t) + l.bits.toNat) + 2 ≤ m := by
    unfold μ at hμ; rw [hm, rank_MATCH] at hμ; exact hμ
  have hn := bl.sh.ws
  have hn1 := bl.sh.n_pos
  have hL := bl.left
  rw [back_MATCH_eq]
  refine SatX.bind (liftEq bl.sh.ldState ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  by_cases hc : S.offset > S.wsize - (if S.whave < S.wsize then l.left else 0)
  · simp only [hc, ↓reduceIte]
    obtain ⟨H', z', e, bm'⟩ := bl.toBM.setBad cb "invalid distance too far back"
      (strIdx 20 (by decide) (by decide) (by decide))
    refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
    refine SatX.pure ⟨t, z', _, ⟨bm', Or.inl rfl, BModeOK.quiet _ { S with mode := BAD }
      (by show BAD ≠ LEN; decide) (by show BAD ≠ MATCH; decide)⟩, ?_⟩
    unfold μ; dsimp only; rw [rank_BAD]; omega
  · simp only [hc, ↓reduceIte]
    have hle := hc
    have hx : (if S.whave < S.wsize then l.left else 0).toNat ≤ S.wsize.toNat := by
      split
      · rw [hn]; exact hL
      · exact Nat.zero_le _
    have hle' : S.offset.toNat ≤ E.n - (if S.whave < S.wsize then l.left else 0).toNat := by
      have := Nat.le_of_not_lt (fun h => hle (UInt32.lt_iff_toNat_lt.mpr h))
      rw [u32_sub_le hx, hn] at this; exact this
    have mp0 : MP E l.bits l.have_ l H t z S := by
      refine ⟨bl.toBM, hm, bl.modes.dec (Or.inr hm), rfl, rfl, bl.modes.off hm, by omega, fun hw => ?_⟩
      have : S.whave < S.wsize := by
        rw [hw, UInt32.lt_iff_toNat_lt, hn]; show 0 < E.n; omega
      simp only [this, ↓reduceIte] at hle'; exact hle'
    have fin : ∀ l1 H1 z1 S1, MP E l.bits l.have_ l1 H1 t z1 S1 →
        SatX H1 l1 (setMode E.c.st LEN : X Unit) (Post E m) := by
      intro l1 H1 z1 S1 mp1
      obtain ⟨e, bm2⟩ := mp1.bm.setMode cb LEN
      refine SatX.lift (Sat.of_eq e ⟨t, z1, _, ⟨bm2, Or.inr (by rw [mp1.bits]; exact hb8),
        ⟨fun _ => mp1.tabs, fun e => absurd (show LEN = MATCH from e) (by decide)⟩⟩, ?_⟩)
      unfold μ; dsimp only; rw [rank_LEN, mp1.bits, mp1.hv]; omega
    refine SatX.bind (SatX.mono (match_body cb mp0) ?_)
    rintro r l1 H1 p
    match r, p with
    | .error .leave, p => exact p
    | .ok (), ⟨z1, S1, mp1, _⟩ =>
      dsimp only
      unfold xwhile
      refine SatX.bind (SatX.mono (xwhileBrk_rank (fun l' H' => ∃ z S, MP E l.bits l.have_ l' H' t z S) (fun _ H' => lenRank E H')
        (fun r l' H' => match r with
          | .ok () => ∃ z S, MP E l.bits l.have_ l' H' t z S
          | .error .leave => BLv E l' H'
          | .error (.ret _) => False) ?_ ⟨z1, S1, mp1⟩ ?_) ?_)
      · rintro l2 H2 ⟨z2, S2, mp2⟩
        refine SatX.bind (liftEq (mp2.bm.sh.rdS _) ?_)
        refine SatX.pure ?_
        by_cases hne : S2.length = 0
        · have e : (S2.length != 0) = false := by simp [hne]
          rw [e]
          exact ⟨z2, S2, mp2⟩
        · have e : (S2.length != 0) = true := by simpa using hne
          rw [e]
          refine SatX.bind (SatX.mono (match_body cb mp2) ?_)
          rintro r l3 H3 p
          match r, p with
          | .error .leave, p => exact p
          | .ok (), ⟨z3, S3, mp3, hlt⟩ =>
            refine SatX.pure ⟨⟨z3, S3, mp3⟩, ?_⟩
            rw [mp3.rk, mp2.rk]
            exact hlt (fun h => hne (UInt32.toNat_inj.mp h))
      · rw [mp1.rk]; have := S1.length.toNat_lt; unfold fuel; omega
      · rintro r l2 H2 p
        match r, p with
        | .error .leave, p => exact p
        | .ok (), ⟨z2, S2, mp2⟩ => exact fin l2 H2 z2 S2 mp2

end ZlibNgF.Proof.InfbackLoop
