import ZlibNgF.Proof.«infback.c.decode»

/-!
# `inflateBack()`: the match copy of `LEN` (`ZlibNgF`)

After a length and a distance, `LEN` copies the match through the window in pieces of at most `left` bytes, calling
`out()` when the window is full (`ROOM`). A piece comes from the end of the window (`from = put + (wsize - offset)`,
the previous pass) or from `offset` bytes back, and is copied one byte at a time. Both pointers stay in the window:
the source of a piece ends at or before the window's end, its destination at `put + copy <= window + wsize`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateLoop (withS store_heap set_get)
open ZlibNgF.Proof.ChunkCopy (B)

/-- The byte copy of a piece: `*put++ = *from++`. -/
def byte1 : X Unit := do
  let l ← get
  let v ← load8 l.from_
  Ptr.store l.put v
  let pt ← l.put.add 1
  let fr ← l.from_.add 1
  modify fun l => { l with put := pt, from_ := fr }

theorem load8_heap {H : Heap} {b o : Nat} {a : Array UInt8} (hd : H.bytes b = some a) (ho : o < a.size) :
    load8 (.ref (.heap b) o) H = .ok (a[o]!, H) := by
  simp [load8, Ptr.load, ZlibNgF.Proof.InflateDict.space_get_heap, hd, ho]

/-- One byte from `from` to `put`, both in the window. -/
theorem byte1_ok {E : BEnv} (cb : E.CB) {lF l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E lF H t z S) {p f : Nat} (hp : l.put = .ref (.heap E.wb) p) (hf : l.from_ = .ref (.heap E.wb) f)
    (hpw : E.woff ≤ p) (hpn : p < E.woff + E.n) (hfn : f < E.woff + E.n) :
    SatX H l byte1 (fun r l' H' => r = .ok () ∧ BM E lF H' t z S ∧
      l' = { l with put := .ref (.heap E.wb) (p + 1), from_ := .ref (.heap E.wb) (f + 1) }) := by
  obtain ⟨a, ha, haN⟩ := bm.winBytes
  unfold byte1
  refine SatX.bind (SatX.get ?_)
  dsimp only
  rw [hf, hp]
  refine SatX.bind (liftEq (load8_heap ha (by omega)) ?_)
  refine SatX.bind (SatX.lift (Sat.of_eq (store_heap ha (by omega) _) ?_))
  have hsz : (a.set! p a[f]!).size = a.size := by simp
  have bm1 := bm.winW cb ha hsz (fun j hj => set_get a p j _ (by omega))
  obtain ⟨a1, ha1, ha1N⟩ := bm1.winBytes
  refine SatX.bind (liftEq (ZlibNgF.Proof.InfbackLoop.add_nat ha1 1 (by omega)) ?_)
  refine SatX.bind (liftEq (ZlibNgF.Proof.InfbackLoop.add_nat ha1 1 (by omega)) ?_)
  exact SatX.modify ⟨rfl, bm1, rfl⟩

/-- The byte loop of a piece: the first copy and `while (--copy)`, `k ≥ 1` bytes in all. -/
theorem byte_loop {E : BEnv} (cb : E.CB) {lF l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E lF H t z S) {p f k : Nat} (hp : l.put = .ref (.heap E.wb) p) (hf : l.from_ = .ref (.heap E.wb) f)
    (hk : l.copy.toNat = k) (hk1 : 1 ≤ k) (hpw : E.woff ≤ p) (hpk : p + k ≤ E.woff + E.n)
    (hfk : f + k ≤ E.woff + E.n) :
    SatX H l (do
      byte1
      xwhile (do modify fun l => { l with copy := l.copy - 1 }; return (← get).copy != 0) byte1)
      (fun r l' H' => r = .ok () ∧ BM E lF H' t z S ∧
        l' = { l with put := .ref (.heap E.wb) (p + k), from_ := .ref (.heap E.wb) (f + k), copy := 0 }) := by
  refine SatX.bind (SatX.mono (byte1_ok cb bm hp hf hpw (by omega) (by omega)) ?_)
  rintro r l1 H1 ⟨rfl, bm1, rfl⟩
  unfold xwhile
  refine SatX.mono (xwhileBrk_rank (fun l' H' => ∃ i c, 1 ≤ i ∧ i ≤ k ∧ c.toNat = k - i + 1 ∧ BM E lF H' t z S ∧
      l' = { l with put := .ref (.heap E.wb) (p + i), from_ := .ref (.heap E.wb) (f + i), copy := c })
    (fun l' _ => l'.copy.toNat) (fun r l' H' => r = .ok () ∧ BM E lF H' t z S ∧
      l' = { l with put := .ref (.heap E.wb) (p + k), from_ := .ref (.heap E.wb) (f + k), copy := 0 }) ?_
    ⟨1, l.copy, Nat.le_refl _, hk1, by omega, bm1, rfl⟩ (by show l.copy.toNat + 2 < fuel; have := l.copy.toNat_lt; unfold fuel; omega))
    (fun _ _ _ q => q)
  rintro l2 H2 ⟨i, c, hi1, hik, hc, bm2, rfl⟩
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.get ?_)
  refine SatX.pure ?_
  dsimp only
  have hc1 : (c - 1).toNat = k - i := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 1 ≤ _; omega)]; show c.toNat - 1 = _; omega
  by_cases h0 : i = k
  · subst h0
    have e : (c - 1 != 0) = false := by
      have : c - 1 = 0 := UInt32.toNat_inj.mp (by rw [hc1]; simp)
      simp [this]
    rw [e]
    refine ⟨rfl, bm2, ?_⟩
    have : c - 1 = 0 := UInt32.toNat_inj.mp (by rw [hc1]; simp)
    rw [this]
  · have e : (c - 1 != 0) = true := by
      have : c - 1 ≠ 0 := fun h => by have := congrArg UInt32.toNat h; rw [hc1] at this; simp at this; omega
      simpa using this
    rw [e]
    refine SatX.bind (SatX.mono (byte1_ok cb bm2 (p := p + i) (f := f + i) rfl rfl (by omega) (by omega)
      (by omega)) ?_)
    rintro r l3 H3 ⟨rfl, bm3, rfl⟩
    refine SatX.pure ⟨⟨i + 1, c - 1, by omega, by omega, by rw [hc1]; omega, bm3, rfl⟩, ?_⟩
    show (c - 1).toNat < c.toNat
    rw [hc1]; omega

/-! ## One piece -/

/-- The statements of a piece after `from` and `copy` are set, verbatim. -/
def lenTail (c : BCtx) : X Unit := do
  let len ← rdS c.st (·.length)
  modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 len.toUInt64).toUInt32 }
  let copy := (← get).copy
  wrS c.st fun s => { s with length := s.length - copy }
  modify fun l => { l with left := l.left - l.copy }
  byte1
  xwhile (do modify fun l => { l with copy := l.copy - 1 }; return (← get).copy != 0) byte1

/-- The state of the copy loop of `LEN`, entered with `b0` bits held and `h0` input bytes. -/
structure LP (E : BEnv) (b0 : UInt8) (h0 : UInt32) (l : IL) (H : Heap) (t : Nat) (z : ZStream) (S : InflateState) :
    Prop where
  bm : BM E l H t z S
  mode : S.mode = LEN
  tabs : RTab E.b S.codes S.lencode S.lenbits 28 false ∧ RTab E.b S.codes S.distcode S.distbits 28 true
  bits : l.bits = b0
  hv : l.have_ = h0
  off1 : 1 ≤ S.offset.toNat
  offw : S.offset.toNat ≤ E.n
  near : S.whave = 0 → S.offset.toNat ≤ E.n - l.left.toNat

/-- The outcome of one piece. -/
def LPost (E : BEnv) (b0 : UInt8) (h0 : UInt32) (t : Nat) (len : Nat) : Except Ex Unit → IL → Heap → Prop
  | .ok (), l, H => ∃ z S, LP E b0 h0 l H t z S ∧ S.length.toNat < len
  | .error .leave, l, H => BLv E l H
  | .error (.ret _), _, _ => False

theorem len_tail {E : BEnv} (cb : E.CB) {b0 : UInt8} {h0 : UInt32} {l l2 : IL} {H H2 : Heap} {t : Nat}
    {z : ZStream} {S : InflateState} (lp : LP E b0 h0 l H t z S) (bmH : BM E l H2 t z S)
    (e1 : l2.next = l.next) (e2 : l2.have_ = l.have_) (e3 : l2.bits = l.bits) (e4 : l2.left = l.left)
    (e5 : l2.put = l.put) {f : Nat} (hf : l2.from_ = .ref (.heap E.wb) f)
    (hfk : f + min l2.copy.toNat S.length.toNat ≤ E.woff + E.n) (hcl : l2.copy.toNat ≤ l.left.toNat)
    (hc1 : 1 ≤ l2.copy.toNat) (hne : S.length ≠ 0) :
    SatX H2 l2 (lenTail E.c) (LPost E b0 h0 t S.length.toNat) := by
  have hn1 : 1 ≤ S.length.toNat := u32_ne_zero hne
  have hL := lp.bm.left
  unfold lenTail
  refine SatX.bind (liftEq (bmH.sh.rdS _) ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only [BEnv.c]
  have ecp : (ZlibNg.Zbuild.MIN l2.copy.toUInt64 S.length.toUInt64).toUInt32.toNat =
      min l2.copy.toNat S.length.toNat := by
    rw [min32 _ _ (by rw [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _), UInt32.toNat_toUInt64,
      UInt32.toNat_toUInt64]
  generalize (ZlibNg.Zbuild.MIN l2.copy.toUInt64 S.length.toUInt64).toUInt32 = c at ecp ⊢
  refine SatX.bind (SatX.lift (Sat.of_eq (bmH.sh.wrS _) ?_))
  have bm3 := bmH.wS cb (S' := { S with length := S.length - c }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.bind (SatX.modify ?_)
  have hcl' : c.toNat ≤ l.left.toNat := by rw [ecp]; omega
  have hput := lp.bm.put
  have bmF : BM E { l with
      put := .ref (.heap E.wb) (E.woff + (E.n - l.left.toNat) + c.toNat)
      left := l.left - c } (withS H2 E.b { S with length := S.length - c }) t z { S with length := S.length - c } := by
    refine ⟨bm3.sh, ZlibNgF.Proof.InfbackRoom.InB.locals bm3.inB rfl rfl, bm3.tot, ?_, ?_, bm3.whave⟩
    · show Ptr.ref _ _ = Ptr.ref _ _
      rw [u32_sub_le hcl']; simp only [Ptr.ref.injEq, true_and]; omega
    · show (l.left - c).toNat ≤ E.n
      rw [u32_sub_le hcl']; omega
  refine SatX.mono (byte_loop cb bmF (p := E.woff + (E.n - l.left.toNat)) (f := f) (k := c.toNat)
    (by show l2.put = _; rw [e5, hput]) hf rfl (by rw [ecp]; omega) (by omega) (by omega) (by rw [ecp]; omega)) ?_
  rintro r l3 H3 ⟨rfl, bm4, rfl⟩
  refine ⟨z, _, ⟨bm4.locals (by exact e2) (by exact e1) rfl (by show l2.left - c = l.left - c; rw [e4]),
    lp.mode, lp.tabs, e3.trans lp.bits, e2.trans lp.hv, lp.off1, lp.offw, fun hw => ?_⟩, ?_⟩
  · show S.offset.toNat ≤ E.n - (l2.left - c).toNat
    rw [e4, u32_sub_le hcl']
    have := lp.near hw; omega
  · show (S.length - c).toNat < S.length.toNat
    rw [u32_sub_le (by rw [ecp]; omega), ecp]; omega

/-- The copy loop body of `LEN` (`infback.c:463-486`), verbatim. -/
def lenBody (c : BCtx) : X Unit := do
    ROOM c
    let s ← ldState c.st
    modify fun l => { l with copy := s.wsize - s.offset }
    let l ← get
    if l.copy < l.left then
      let fr ← l.put.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with from_ := fr }
      modify fun l => { l with copy := l.left - l.copy }
    else
      let off ← rdS c.st (·.offset)
      let fr ← l.put.add (-(Int.ofNat off.toNat))
      modify fun l => { l with from_ := fr }
      modify fun l => { l with copy := l.left }
    let len ← rdS c.st (·.length)
    modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 len.toUInt64).toUInt32 }
    let copy := (← get).copy
    wrS c.st fun s => { s with length := s.length - copy }
    modify fun l => { l with left := l.left - l.copy }
    let byte : X Unit := do
      let l ← get
      let v ← load8 l.from_
      Ptr.store l.put v
      let pt ← l.put.add 1
      let fr ← l.from_.add 1
      modify fun l => { l with put := pt, from_ := fr }
    byte
    xwhile (do modify fun l => { l with copy := l.copy - 1 }; return (← get).copy != 0) byte

/-- One piece of `LEN`'s copy, after `ROOM` with room left. -/
theorem len_rest {E : BEnv} (cb : E.CB) {b0 : UInt8} {h0 : UInt32} {l : IL} {H : Heap}
    {t : Nat} {z : ZStream} {S : InflateState} (lp : LP E b0 h0 l H t z S) (hl : l.left ≠ 0) (hne : S.length ≠ 0) :
    SatX H l (do
      let s ← ldState E.c.st
      modify fun l => { l with copy := s.wsize - s.offset }
      let l ← get
      if l.copy < l.left then
        let fr ← l.put.add (Int.ofNat l.copy.toNat)
        modify fun l => { l with from_ := fr }
        modify fun l => { l with copy := l.left - l.copy }
      else
        let off ← rdS E.c.st (·.offset)
        let fr ← l.put.add (-(Int.ofNat off.toNat))
        modify fun l => { l with from_ := fr }
        modify fun l => { l with copy := l.left }
      lenTail E.c) (LPost E b0 h0 t S.length.toNat) := by
  have bm := lp.bm
  have hn := bm.sh.ws
  have hL : l.left.toNat ≤ E.n := bm.left
  have hL1 : 1 ≤ l.left.toNat := u32_ne_zero hl
  have hD1 := lp.off1
  have hDn := lp.offw
  obtain ⟨a, ha, haN⟩ := bm.winBytes
  have hput := bm.put
  refine SatX.bind (liftEq bm.sh.ldState ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  have ec : (S.wsize - S.offset).toNat = E.n - S.offset.toNat := by rw [u32_sub_le (by omega), hn]
  split
  · rename_i hlt
    have hlt' : E.n - S.offset.toNat < l.left.toNat := by rw [← ec]; exact UInt32.lt_iff_toNat_lt.mp hlt
    rw [hput]
    refine SatX.bind (liftEq (add_nat ha (S.wsize - S.offset).toNat (by rw [ec]; omega)) ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.modify ?_)
    refine len_tail cb lp bm rfl rfl rfl rfl (by rw [hput]) rfl ?_ ?_ ?_ hne
    · show E.woff + (E.n - l.left.toNat) + (S.wsize - S.offset).toNat +
        min (l.left - (S.wsize - S.offset)).toNat S.length.toNat ≤ E.woff + E.n
      rw [u32_sub_le (show (S.wsize - S.offset).toNat ≤ l.left.toNat by omega), ec]; omega
    · show (l.left - (S.wsize - S.offset)).toNat ≤ l.left.toNat
      rw [u32_sub_le (show (S.wsize - S.offset).toNat ≤ l.left.toNat by omega)]; omega
    · show 1 ≤ (l.left - (S.wsize - S.offset)).toNat
      rw [u32_sub_le (show (S.wsize - S.offset).toNat ≤ l.left.toNat by omega), ec]; omega
  · rename_i hge
    have hge' : l.left.toNat ≤ E.n - S.offset.toNat := by
      rw [← ec]; exact Nat.le_of_not_lt (fun h => hge (UInt32.lt_iff_toNat_lt.mpr h))
    refine SatX.bind (liftEq (bm.sh.rdS _) ?_)
    dsimp only
    rw [hput]
    refine SatX.bind (liftEq (add_neg ha S.offset.toNat (by omega) (by omega)) ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.modify ?_)
    exact len_tail cb lp bm rfl rfl rfl rfl (by rw [hput]) rfl (by
      show E.woff + (E.n - l.left.toNat) - S.offset.toNat + min l.left.toNat S.length.toNat ≤ E.woff + E.n
      omega)
      (Nat.le_refl _) hL1 hne

theorem lenBody_eq (c : BCtx) : lenBody c = (do
    ROOM c
    let s ← ldState c.st
    modify fun l => { l with copy := s.wsize - s.offset }
    let l ← get
    if l.copy < l.left then
      let fr ← l.put.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with from_ := fr }
      modify fun l => { l with copy := l.left - l.copy }
    else
      let off ← rdS c.st (·.offset)
      let fr ← l.put.add (-(Int.ofNat off.toNat))
      modify fun l => { l with from_ := fr }
      modify fun l => { l with copy := l.left }
    lenTail c) := rfl

theorem len_body {E : BEnv} (cb : E.CB) {b0 : UInt8} {h0 : UInt32} {l : IL} {H : Heap}
    {t : Nat} {z : ZStream} {S : InflateState} (lp : LP E b0 h0 l H t z S) (hne : S.length ≠ 0) :
    SatX H l (lenBody E.c) (LPost E b0 h0 t S.length.toNat) := by
  rw [lenBody_eq]
  refine SatX.bind (lp.bm.room cb (fun hl => len_rest cb lp hl hne) ?_)
  intro _ H' bm'
  have hn := lp.bm.sh.ws
  have hn1 := lp.bm.sh.n_pos
  have hw0 : S.wsize ≠ 0 := fun e => by rw [e] at hn; simp at hn; omega
  refine ⟨(bm'.locals rfl rfl rfl rfl).leave, ?_⟩
  exact len_rest cb (S := { S with whave := S.wsize }) ⟨bm', lp.mode, lp.tabs, lp.bits, lp.hv, lp.off1, lp.offw,
    fun e => absurd e hw0⟩ hw0 hne

theorem LP.rk {E : BEnv} {b0 : UInt8} {h0 : UInt32} {l : IL} {H : Heap} {t : Nat} {z : ZStream}
    {S : InflateState} (lp : LP E b0 h0 l H t z S) : lenRank E H = S.length.toNat := by
  unfold lenRank; rw [lp.bm.sh.istate]

/-- The copy loop of `LEN`: the first piece and `while (state->length != 0)`, ending in `LEN`. -/
theorem len_copy {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (lp : LP E l.bits l.have_ l H t z S) (hne : S.length ≠ 0) (hb8 : l.bits.toNat < 8) {m : Nat}
    (hm : 32 * (8 * (l.have_.toNat + t) + l.bits.toNat) + 1 < m) :
    SatX H l (do
      lenBody E.c
      xwhile (do return (← rdS E.c.st (·.length)) != 0) (lenBody E.c)) (Post E m) := by
  refine SatX.bind (SatX.mono (len_body cb lp hne) ?_)
  rintro r l1 H1 p
  match r, p with
  | .error .leave, p => exact p
  | .ok (), ⟨z1, S1, lp1, _⟩ =>
  unfold xwhile
  refine SatX.mono (xwhileBrk_rank (fun l' H' => ∃ z S, LP E l.bits l.have_ l' H' t z S) (fun _ H' => lenRank E H')
    (fun r l' H' => match r with
      | .ok () => ∃ z S, LP E l.bits l.have_ l' H' t z S
      | .error .leave => BLv E l' H'
      | .error (.ret _) => False) ?_ ⟨z1, S1, lp1⟩ ?_) ?_
  · rintro l2 H2 ⟨z2, S2, lp2⟩
    refine SatX.bind (liftEq (lp2.bm.sh.rdS _) ?_)
    refine SatX.pure ?_
    dsimp only
    by_cases hne2 : S2.length = 0
    · have e : (S2.length != 0) = false := by simp [hne2]
      rw [e]
      exact ⟨z2, S2, lp2⟩
    · have e : (S2.length != 0) = true := by simpa using hne2
      rw [e]
      refine SatX.bind (SatX.mono (len_body cb lp2 hne2) ?_)
      rintro r l3 H3 p
      match r, p with
      | .error .leave, p => exact p
      | .ok (), ⟨z3, S3, lp3, hlt⟩ =>
        refine SatX.pure ⟨⟨z3, S3, lp3⟩, ?_⟩
        rw [lp3.rk, lp2.rk]
        exact hlt
  · rw [lp1.rk]; have := S1.length.toNat_lt; unfold fuel; omega
  · rintro r l2 H2 p
    match r, p with
    | .error .leave, p => exact p
    | .ok (), ⟨z2, S2, lp2⟩ =>
      refine ⟨t, z2, S2, ⟨lp2.bm, Or.inr (by rw [lp2.bits]; exact hb8), ⟨fun _ => lp2.tabs, fun e => absurd
        (lp2.mode.symm.trans e) (by decide)⟩⟩, ?_⟩
      unfold μ; rw [lp2.mode, rank_LEN, lp2.bits, lp2.hv]; omega

end ZlibNgF.Proof.InfbackLoop
