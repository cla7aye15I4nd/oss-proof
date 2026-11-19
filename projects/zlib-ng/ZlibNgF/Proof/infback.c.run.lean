import ZlibNgF.Proof.«infback.c.table»
import ZlibNgF.Proof.«infback.c.stored»
import ZlibNgF.Proof.«infback.c.match»
import ZlibNgF.Proof.«public-inflate»

/-!
# One `inflateBack()` call (`ZlibNgF`)

`tripOK`: every mode of the loop (`TYPE`, `STORED`, `TABLE`, `LEN`, `MATCH`, and the modes that leave) keeps the loop
invariant `BL` or leaves; so the loop ends by `inf_leave` (`loop_ok`). `backLeave_ok`: the code after `inf_leave`
hands the pending window bytes to `out()` and writes `next_in` / `avail_in` back. `inflateBack_shape`: on a stream
whose state has the call-back shape (`BShape`), `inflateBack` sets up the locals (`BL` with mode `TYPE` and no bits
held), runs the loop and returns, and the stream keeps the shape.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateLoop (withS)

/-! ## The trips -/

theorem modeFn_TYPE : modeFn TYPE = back_TYPE := by funext c; rfl
theorem modeFn_STORED : modeFn STORED = back_STORED := by funext c; rfl
theorem modeFn_TABLE : modeFn TABLE = back_TABLE := by funext c; rfl
theorem modeFn_LEN : modeFn LEN = back_LEN := by funext c; rfl
theorem modeFn_MATCH : modeFn MATCH = back_MATCH := by funext c; rfl

/-- One trip of the loop from every state with the invariant. -/
theorem tripOK (E : BEnv) (cb : E.CB) : TripOK E := by
  refine trip_of_modes cb (fun M => ?_)
  by_cases h1 : M = TYPE
  · subst h1; rw [modeFn_TYPE]; exact run_TYPE E
  by_cases h2 : M = STORED
  · subst h2; rw [modeFn_STORED]; exact run_STORED E
  by_cases h3 : M = TABLE
  · subst h3; rw [modeFn_TABLE]; exact run_TABLE E
  by_cases h4 : M = LEN
  · subst h4; rw [modeFn_LEN]; exact run_LEN E
  by_cases h5 : M = MATCH
  · subst h5; rw [modeFn_MATCH]; exact run_MATCH E
  exact run_leave E M ⟨h1, h2, h3, h4, h5⟩

/-! ## `inf_leave` -/

theorem BShape.rdZ {α : Type} {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S)
    (f : ZStream → α) : ZlibNg.Inflate.rdZ (some E.i) f H = .ok (f z, H) := by
  simp [ZlibNg.Inflate.rdZ, bind_app, ldStream, sh.hz]

/-- The shape of a stream after a call: some stream record and state with the call-back shape. -/
def BOut (E : BEnv) (H : Heap) : Prop := ∃ z S, BShape E H z S

/-- The code after `inf_leave:`: the pending window bytes go to `out()`, `next_in` / `avail_in` are written back, and
the call returns `ret`. -/
theorem backLeave_ok {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} (lv : BLv E l H) :
    SatX H l (backLeave E.c) (fun r _ H' => (∃ v, r = .ok v) ∧ BOut E H') := by
  obtain ⟨t, z, S, sh, hin, hput, hleft⟩ := lv
  have fin : ∀ l' H' (z' : ZStream), BShape E H' z' S → SatX H' l' (do
      let l ← get
      wrZ E.c.strm fun z => { z with next_in := l.next, avail_in := l.have_ }
      return (← get).ret) (fun r _ H' => (∃ v, r = .ok v) ∧ BOut E H') := by
    intro l' H' z' sh'
    refine SatX.bind (SatX.get ?_)
    refine SatX.bind (SatX.lift (Sat.of_eq (sh'.wrZ _) ?_))
    refine SatX.bind (SatX.get ?_)
    exact SatX.pure ⟨⟨_, rfl⟩, _, _, sh'.wZ _ rfl rfl⟩
  unfold backLeave
  refine SatX.bind (liftEq sh.ldState ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · rename_i hlt
    rw [sh.win]
    refine SatX.bind (liftEq (ZlibNgF.Proof.InfbackLoop.ival_get _ _) ?_)
    refine SatX.bind (SatX.get ?_)
    obtain ⟨p, m, hI, -, -⟩ := hin
    have hlen : (S.wsize - l.left).toNat ≤ E.n := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hlt), sh.ws]; omega
    obtain ⟨r, H', e, -, hk⟩ := cb.output H (S.wsize - l.left) p m t hlen hI
    refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
    have sh' := sh.keep hk
    refine SatX.bind (SatX.get ?_)
    dsimp only
    split
    · exact SatX.bind (SatX.modify (fin _ _ _ sh'))
    · exact fin _ _ _ sh'
  · exact fin _ _ _ sh

/-- The loop and `inf_leave` from the loop invariant. -/
theorem loopLeave_ok {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bl : BL E l H t z S) :
    SatX H l (do
      tryCatch (xloopBrk (do dispatch E.c; return false)) (fun _ => pure ())
      backLeave E.c) (fun r _ H' => (∃ v, r = .ok v) ∧ BOut E H') := by
  refine SatX.bind (ZlibNgF.Proof.InflateTop.satX_tryCatch ?_)
  refine SatX.mono (loop_ok (tripOK E cb) bl) ?_
  rintro r l' H' p
  match r, p with
  | .error .leave, p => exact SatX.pure (backLeave_ok cb p)

/-! ## The call -/

/-- A store of a new state that keeps the shape fields (any `whave`). -/
theorem BShape.wS0 {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) (S' : InflateState)
    (ab : S'.alloc_bufs = S.alloc_bufs) (win : S'.window = S.window) (ws : S'.wsize = S.wsize)
    (wn : S'.wnext = S.wnext) (ls : S'.lens.size = S.lens.size) (wk : S'.work.size = S.work.size)
    (cs : S'.codes.size = S.codes.size) : BShape E (withS H E.b S') z S' :=
  { sh with
    hs := upd_same _ _ _
    ab := ab.trans sh.ab
    win := win.trans sh.win
    ws := by rw [ws]; exact sh.ws
    wnext := wn.trans sh.wnext
    lens := ls.trans sh.lens
    work := wk.trans sh.work
    codes := cs.trans sh.codes }

/-- `inflateBack` on a stream with the call-back shape, with call-backs well behaved for `I`, which holds of the
first chunk with fewer than `2^48` input bytes in all: it returns, and the stream keeps the shape. -/
theorem inflateBack_shape (E : BEnv) (cb : E.CB) {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S)
    {t : Nat} (hI : E.I H z.next_in (if z.next_in = .null then 0 else z.avail_in.toNat) t)
    (ht : (if z.next_in = .null then 0 else z.avail_in.toNat) + t < 2 ^ 48) :
    ∃ r H', C.run (inflateBack (some E.i) E.inCb E.inDesc E.outCb E.outDesc) H = .ok (r, H') ∧ BOut E H' := by
  -- the entry statements
  let z1 : ZStream := { z with msg := .null }
  have sh1 : BShape E (withZ H E.i z1) z1 S := sh.wZ z1 rfl rfl
  let S2 : InflateState := { S with mode := TYPE, last := 0, whave := 0 }
  have sh2 : BShape E (withS (withZ H E.i z1) E.b S2) z1 S2 := sh1.wS0 S2 rfl rfl rfl rfl rfl rfl rfl
  have hst : LStep E H (withS (withZ H E.i z1) E.b S2) :=
    (lstep_withZ E H z1).trans (lstep_withS E _ S2)
  have hI2 := cb.stable _ _ _ _ _ hI hst.1 hst.2
  -- the locals
  let hv : UInt32 := if z.next_in != .null then z.avail_in else 0
  have hhv : hv.toNat = (if z.next_in = .null then 0 else z.avail_in.toNat) := by
    by_cases hn : z.next_in = .null
    · simp [hv, hn]
    · simp [hv, hn]
  rw [← hhv] at hI2 ht
  have rest : ∀ (v : UInt32) (l : IL), v = hv → l.next = z.next_in → SatX (withS (withZ H E.i z1) E.b S2) l (do
      modify fun l => { l with have_ := v }
      modify fun l => { l with hold := 0 }
      modify fun l => { l with bits := 0 }
      let w ← (← rdS (some E.b) (·.window)).get
      modify fun l => { l with put := w }
      let ws ← rdS (some E.b) (·.wsize)
      modify fun l => { l with left := ws }
      tryCatch (xloopBrk (do dispatch E.c; return false)) (fun _ => pure ())
      backLeave E.c) (fun r _ H' => (∃ v, r = .ok v) ∧ BOut E H') := by
    intro v l hv' hnx
    subst hv'
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (liftEq (sh2.rdS _) ?_)
    rw [sh2.win]
    refine SatX.bind (liftEq (ZlibNgF.Proof.InfbackLoop.ival_get _ _) ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (liftEq (sh2.rdS _) ?_)
    refine SatX.bind (SatX.modify ?_)
    have hn := sh2.n_pos
    have hw := sh2.ws
    refine loopLeave_ok cb (t := t) (z := z1) (S := S2) ⟨⟨sh2, ?_, ?_, ?_, ?_, Or.inl rfl⟩, Or.inr (by show (0 : UInt8).toNat < 8; decide),
      BModeOK.quiet _ S2 (by show TYPE ≠ LEN; decide) (by show TYPE ≠ MATCH; decide)⟩
    · exact InB.fresh hv hI2 rfl hnx (fun hk => chunk_ref cb hI2 hk)
    · exact ht
    · show E.w = _
      show Ptr.ref (BRef.heap E.wb) E.woff = _
      rw [show S2.wsize.toNat = E.n from hw, Nat.sub_self, Nat.add_zero]
    · show S2.wsize.toNat ≤ E.n
      rw [hw]; exact Nat.le_refl _
  suffices hs : Sat H (inflateBack (some E.i) E.inCb E.inDesc E.outCb E.outDesc) (fun _ H' => BOut E H') by
    obtain ⟨r, H', e, q⟩ := hs; exact ⟨r, H', e, q⟩
  unfold inflateBack
  simp only [show ((some E.i : StreamPtr) == none) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (sh.rdZ _) ?_)
  rw [sh.zs]
  simp only [show ((some E.b : StatePtr) == none) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (sh.rdZ _) ?_)
  rw [sh.zs]
  refine Sat.bind (Sat.of_eq (sh.wrZ _) ?_)
  refine Sat.bind (Sat.of_eq (sh1.wrS _) ?_)
  refine Sat.bind (Sat.of_eq (show uninitLocals 2 (withS (withZ H E.i z1) E.b S2) =
    .ok ((withS (withZ H E.i z1) E.b S2).garbage (2 ^ 42 + 2), withS (withZ H E.i z1) E.b S2) from rfl) ?_)
  refine Sat.bind (Sat.mono (P := fun p H' => (∃ v, p.1 = .ok v) ∧ BOut E H') ?_ ?_)
  · show SatX _ _ _ (fun r _ H' => (∃ v, r = .ok v) ∧ BOut E H')
    refine SatX.bind (liftEq (sh2.rdZ _) ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.get ?_)
    dsimp only
    split
    · rename_i hn
      exact SatX.bind (liftEq (sh2.rdZ _) (rest _ _ (by
        show _ = if (z1.next_in != Ptr.null) = true then z.avail_in else 0
        simp only [hn, ↓reduceIte]; rfl) rfl))
    · rename_i hn
      first
        | exact SatX.bind (SatX.pure (rest _ _ (by
            show _ = if (z1.next_in != Ptr.null) = true then z.avail_in else 0
            simp only [hn, Bool.false_eq_true, ↓reduceIte]) rfl))
        | exact rest _ _ (by
            show _ = if (z1.next_in != Ptr.null) = true then z.avail_in else 0
            simp only [hn, Bool.false_eq_true, ↓reduceIte]) rfl
  · rintro ⟨r, l'⟩ H' ⟨⟨v, hr⟩, hb⟩
    dsimp only at hr
    subst hr
    exact Sat.pure hb

end ZlibNgF.Proof.InfbackLoop
