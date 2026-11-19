import ZlibNgF.Proof.«infback.c.loop»
import ZlibNgF.Proof.«inflate.c.type-modes»
import ZlibNgF.Proof.«inflate.c.decode-modes»

/-!
# Steps of `inflateBack()`'s modes (`ZlibNgF`)

A step of the library between two call-back calls changes only the stream record, the state block and the window
bytes, and allocates nothing (`LStep`); the caller's invariant `I` survives it (`BackCallbacks.stable`), so `InB`
does. Stores into the state that keep the shape fields (`SKeep`), stores into the stream record that keep `state` and
`zfree`, and stores into the window keep `BM`. `SET_BAD`, reads of the state, and the split of `dispatch` into the
modes (`modeFn`, `trip_of_modes`); the modes that leave at once (`DONE`, `BAD`, any other value).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InfbackRoom
open ZlibNgF.Proof.InflateLoop (withS istates_of istate_withS wrS_app ldState_withS rdS_withS Frame.trans
  Frame.mono)

/-! ## Library steps -/

/-- A step of the library: the frame of the call-backs' `stable`, and no allocation. -/
def LStep (E : BEnv) (H H' : Heap) : Prop :=
  Frame H H' [E.i] [E.b] [] [(E.w, E.n)] ∧ H'.nextBlk = H.nextBlk

theorem LStep.refl (E : BEnv) (H : Heap) : LStep E H H :=
  ⟨ZlibNgF.Proof.InflateInit.frame_refl H _ _ _ _, rfl⟩

theorem LStep.trans {E : BEnv} {H1 H2 H3 : Heap} (a : LStep E H1 H2) (b : LStep E H2 H3) : LStep E H1 H3 :=
  ⟨Frame.trans a.1 b.1, b.2.trans a.2⟩

/-- `InB` survives a library step. -/
theorem InB.lstep {E : BEnv} (cb : E.CB) {H H' : Heap} {l : IL} {t : Nat} (hin : InB E.I H l t)
    (s : LStep E H H') : InB E.I H' l t :=
  InB.heap hin (fun p m hI => cb.stable H H' p m t hI s.1 s.2)

/-- The heap with the stream record `i` replaced. -/
def withZ (H : Heap) (i : Nat) (z : ZStream) : Heap := { H with streams := upd H.streams i (some z) }

theorem lstep_withS (E : BEnv) (H : Heap) (S : InflateState) : LStep E H (withS H E.b S) :=
  ⟨frame_withS H E.i E.b S _, rfl⟩

theorem lstep_withZ (E : BEnv) (H : Heap) (z : ZStream) : LStep E H (withZ H E.i z) := by
  refine ⟨⟨fun j hj => ?_, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ d hd => ⟨d, hd, rfl, fun _ _ _ => rfl⟩, fun _ _ _ hn => hn, rfl, rfl, rfl, rfl, Nat.le_refl _⟩, rfl⟩
  show upd H.streams E.i (some z) j = _
  rw [upd_ne _ _ _ _ (by simpa using hj)]

/-- A change of the window bytes that keeps the block's size and every byte outside the window. -/
theorem lstep_win (E : BEnv) {H : Heap} {a a' : Array UInt8} (hd : H.bytes E.wb = some a)
    (hsz : a'.size = a.size) (hpt : ∀ j, (j < E.woff ∨ E.woff + E.n ≤ j) → a'[j]! = a[j]!) :
    LStep E H { H with bytes := upd H.bytes E.wb (some a') } :=
  ⟨Frame.mono (ZlibNgF.Proof.InflateDict.frame_bytes hd hsz hpt) (fun _ m => nomatch m) (fun _ m => nomatch m)
    (fun _ m => m) (fun _ m => m), rfl⟩

/-! ## The shape -/

/-- A new state that keeps the shape fields. -/
structure SKeep (S S' : InflateState) : Prop where
  ab : S'.alloc_bufs = S.alloc_bufs
  win : S'.window = S.window
  ws : S'.wsize = S.wsize
  wn : S'.wnext = S.wnext
  whave : S'.whave = S.whave
  lens : S'.lens.size = S.lens.size
  work : S'.work.size = S.work.size
  codes : S'.codes.size = S.codes.size

theorem SKeep.refl (S : InflateState) : SKeep S S := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SKeep.mode (S : InflateState) (m : UInt32) : SKeep S { S with mode := m } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem BShape.wS {E : BEnv} {H : Heap} {z : ZStream} {S S' : InflateState} (sh : BShape E H z S)
    (k : SKeep S S') : BShape E (withS H E.b S') z S' :=
  { sh with
    hs := upd_same _ _ _
    ab := k.ab.trans sh.ab
    win := k.win.trans sh.win
    ws := by rw [k.ws]; exact sh.ws
    wnext := k.wn.trans sh.wnext
    lens := k.lens.trans sh.lens
    work := k.work.trans sh.work
    codes := k.codes.trans sh.codes }

theorem BShape.wZ {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) (z' : ZStream)
    (e1 : z'.state = z.state) (e2 : z'.zfree = z.zfree) : BShape E (withZ H E.i z') z' S :=
  { sh with
    hz := upd_same _ _ _
    zs := e1.trans sh.zs
    zfree := e2.trans sh.zfree }

theorem BShape.wW {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) {a' : Array UInt8}
    {a : Array UInt8} (hd : H.bytes E.wb = some a) (hsz : a'.size = a.size) :
    BShape E { H with bytes := upd H.bytes E.wb (some a') } z S := by
  obtain ⟨wd, hwd, hws⟩ := sh.wd
  rw [hd] at hwd; cases hwd
  have hbb : upd H.bytes E.wb (some a') E.b = H.bytes E.b := upd_ne _ _ _ _ (Ne.symm sh.wbb)
  exact { sh with
    hd := by show ∃ d, upd H.bytes E.wb (some a') E.b = some d; rw [hbb]; exact sh.hd
    wd := ⟨a', upd_same _ _ _, by omega⟩ }

/-! ## `BM` across steps -/

theorem BM.lstep {E : BEnv} (cb : E.CB) {l : IL} {H H' : Heap} {t : Nat} {z z' : ZStream} {S S' : InflateState}
    (bm : BM E l H t z S) (s : LStep E H H') (sh : BShape E H' z' S') (hw : S'.whave = S.whave ∨ S'.whave = 0 ∨
      S'.whave = S'.wsize) : BM E l H' t z' S' := by
  refine ⟨sh, InB.lstep cb bm.inB s, bm.tot, bm.put, bm.left, ?_⟩
  have ews : S'.wsize = S.wsize := UInt32.toNat_inj.mp (sh.ws.trans bm.sh.ws.symm)
  rcases hw with hw | hw | hw
  · rw [hw, ews]; exact bm.whave
  · exact Or.inl hw
  · exact Or.inr hw

theorem BM.wS {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S S' : InflateState}
    (bm : BM E l H t z S) (k : SKeep S S') : BM E l (withS H E.b S') t z S' :=
  bm.lstep cb (lstep_withS E H S') (bm.sh.wS k) (Or.inl k.whave)

theorem BM.wZ {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) (z' : ZStream) (e1 : z'.state = z.state) (e2 : z'.zfree = z.zfree) :
    BM E l (withZ H E.i z') t z' S :=
  bm.lstep cb (lstep_withZ E H z') (bm.sh.wZ z' e1 e2) (Or.inl rfl)

/-- `BM` for new locals that agree on the fields it reads. -/
theorem BM.locals {E : BEnv} {l l' : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) (h1 : l'.have_ = l.have_) (h2 : l'.next = l.next) (h3 : l'.put = l.put)
    (h4 : l'.left = l.left) : BM E l' H t z S :=
  ⟨bm.sh, InB.locals bm.inB h1 h2, by rw [h1]; exact bm.tot, by rw [h3, h4]; exact bm.put, by rw [h4]; exact bm.left,
    bm.whave⟩

/-! ## Reads and stores -/

theorem BShape.rdS {α : Type} {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S)
    (g : InflateState → α) : ZlibNg.Inflate.rdS (some E.b) g H = .ok (g S, H) := by
  simp [ZlibNg.Inflate.rdS, bind_app, InflateInv.ldState_app sh.istate]

theorem BShape.ldState {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) :
    C.ldState (some E.b) H = .ok (S, H) := InflateInv.ldState_app sh.istate

theorem BShape.wrS {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S)
    (f : InflateState → InflateState) : ZlibNg.Inflate.wrS (some E.b) f H = .ok ((), withS H E.b (f S)) :=
  wrS_app sh.istate f

theorem BShape.wrZ {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S)
    (f : ZStream → ZStream) : wrZ (some E.i) f H = .ok ((), withZ H E.i (f z)) := by
  simp [ZlibNg.Inflate.wrZ, bind_app, ldStream, stStream, sh.hz, withZ]

/-- `SET_BAD(msg)` for a message of the string table. -/
theorem BM.setBad {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) (msg : String) {k : Nat} (hm : strTable.findIdx? (· == msg) = some k) :
    ∃ H' z', SET_BAD E.c.ctx msg H = .ok ((), H') ∧ BM E l H' t z' { S with mode := BAD } := by
  have bm1 := bm.wS cb (S' := { S with mode := BAD }) (SKeep.mode S BAD)
  have e1 : strLitRef msg (withS H E.b { S with mode := BAD }) =
      .ok (.ref (.str k) 0, withS H E.b { S with mode := BAD }) := by simp [strLitRef, hm]
  refine ⟨_, _, ?_, bm1.wZ cb { z with msg := .ref (.str k) 0 } rfl rfl⟩
  simp only [SET_BAD, bind_app, BEnv.c, BCtx.ctx, bm.sh.wrS, e1, bm1.sh.wrZ]

/-- `setMode` keeps `BM`. -/
theorem BM.setMode {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) (m : UInt32) :
    setMode (some E.b) m H = .ok ((), withS H E.b { S with mode := m }) ∧
      BM E l (withS H E.b { S with mode := m }) t z { S with mode := m } :=
  ⟨bm.sh.wrS _, bm.wS cb (SKeep.mode S m)⟩

/-! ## Modes -/

/-- A mode statement: from every state with the invariant and `pre`, below the measure bound `m`, the mode runs to
`Post E m`. -/
def ModeRun (E : BEnv) (f : BCtx → X Unit) (pre : InflateState → Prop) : Prop :=
  E.CB → ∀ l H t z S, BL E l H t z S → pre S → ∀ m, μ l t S ≤ m → SatX H l (f E.c) (Post E m)

/-- The mode function of `dispatch` for the mode value `m`. -/
def modeFn (m : UInt32) : BCtx → X Unit := fun c =>
  if m == TYPE then back_TYPE c
  else if m == STORED then back_STORED c
  else if m == TABLE then back_TABLE c
  else if m == LEN then back_LEN c
  else if m == MATCH then back_MATCH c
  else if m == DONE then do
    modify fun l => { l with ret := Z_STREAM_END }
    throw Ex.leave
  else if m == BAD then do
    modify fun l => { l with ret := Z_DATA_ERROR }
    throw Ex.leave
  else do
    modify fun l => { l with ret := Z_STREAM_ERROR }
    throw Ex.leave

theorem dispatch_eq (c : BCtx) : dispatch c = (do let m ← rdS c.st (·.mode); modeFn m c) := rfl

/-- One trip of the loop from the statements of the modes. -/
theorem trip_of_modes {E : BEnv} (cb : E.CB) (hm : ∀ M, ModeRun E (modeFn M) (fun S => S.mode = M)) :
    TripOK E := by
  intro l H t z S bl
  rw [dispatch_eq]
  refine SatX.bind (liftEq (bl.sh.rdS (·.mode)) ?_)
  exact hm S.mode cb l H t z S bl rfl _ (Nat.le_refl _)

/-- `DONE`, `BAD` and every value that is not a mode of `inflateBack`: `goto inf_leave`. -/
theorem run_leave (E : BEnv) (M : UInt32) (hM : M ≠ TYPE ∧ M ≠ STORED ∧ M ≠ TABLE ∧ M ≠ LEN ∧ M ≠ MATCH) :
    ModeRun E (modeFn M) (fun S => S.mode = M) := by
  intro _ l H t z S bl _ m _
  obtain ⟨h1, h2, h3, h4, h5⟩ := hM
  have n1 : (M == TYPE) = false := by simpa using h1
  have n2 : (M == STORED) = false := by simpa using h2
  have n3 : (M == TABLE) = false := by simpa using h3
  have n4 : (M == LEN) = false := by simpa using h4
  have n5 : (M == MATCH) = false := by simpa using h5
  simp only [modeFn, n1, n2, n3, n4, n5, Bool.false_eq_true, ↓reduceIte]
  split
  · exact SatX.bind (SatX.modify (SatX.throw (bl.toBM.locals rfl rfl rfl rfl).leave))
  · split
    · exact SatX.bind (SatX.modify (SatX.throw (bl.toBM.locals rfl rfl rfl rfl).leave))
    · exact SatX.bind (SatX.modify (SatX.throw (bl.toBM.locals rfl rfl rfl rfl).leave))

end ZlibNgF.Proof.InfbackLoop
