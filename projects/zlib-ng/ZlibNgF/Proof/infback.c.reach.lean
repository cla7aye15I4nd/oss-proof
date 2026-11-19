import ZlibNgF.Proof.«infback.c.run»
import ZlibNgF.Spec.Safety.Infback

/-!
# The call-back shape along `BackReachable` (`ZlibNgF`)

`BackShape h s w n`: the stream `s` has a state block whose state has the call-back shape (`BShape`) for the window
`w` of `n` bytes. A caller step keeps it (`BackCallerStep` changes only buffer fields of the stream record and keeps
the library's block and the window's size), and so does an `inflateBack` call (`inflateBack_shape`). With the shape
after a successful `inflateBackInit_` (the premise `InitShape`), every reachable stream has it, and
`Goal.inflateBack_safety` follows (`inflateBack_safety_of_init`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNg.Infback

/-- The environment of the shape: stream `i`, block `b`, window `[woff, woff + n)` of block `wb` (no call-backs). -/
def shapeEnv (i b wb woff n : Nat) : BEnv :=
  ⟨i, b, wb, woff, n, fun _ cur => pure (0, cur), .null, fun _ _ _ => pure 0, .null, fun _ _ _ _ => True⟩

/-- `BShape` depends only on the stream, the block and the window of the environment. -/
theorem BShape.retarget {E E' : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S)
    (hi : E'.i = E.i) (hb : E'.b = E.b) (hw : E'.wb = E.wb) (ho : E'.woff = E.woff) (hn : E'.n = E.n) :
    BShape E' H z S := by
  obtain ⟨hz, zs, zf, hd, hs, al, ab, win, wbb, wd, ws, n1, n2, wn, ls, wk, cs⟩ := sh
  refine ⟨by rw [hi]; exact hz, by rw [hb]; exact zs, zf, by rw [hb]; exact hd, by rw [hb]; exact hs,
    by rw [hb]; exact al, by rw [hb]; exact ab, ?_, by rw [hw, hb]; exact wbb, by rw [hw, ho, hn]; exact wd,
    by rw [hn]; exact ws, by rw [hn]; exact n1, by rw [hn]; exact n2, wn, ls, wk, cs⟩
  show S.window = .val (.ref (.heap E'.wb) E'.woff)
  rw [hw, ho]; exact win

/-- The call-back shape of stream `s` with the window `w` of `n` bytes. -/
def BackShape (h : Heap) (s : StreamPtr) (w : BPtr) (n : Nat) : Prop :=
  ∃ i b wb woff z S, s = some i ∧ w = .ref (.heap wb) woff ∧ BShape (shapeEnv i b wb woff n) h z S

/-- What `inflateBackInit_` establishes (the premise of `inflateBack_safety_of_init`). -/
def InitShape : Prop :=
  ∀ (h h' : Heap) (s : StreamPtr) (windowBits : Int32) (w version : BPtr) (size : Int32),
    FreshBlocks h → InitReady h s → VersionOk h version → WriteSlice h w (2 ^ windowBits.toInt.toNat) →
    C.run (ZlibNg.Infback.inflateBackInit_ s windowBits w version size) h = .ok (ZlibNg.Inflate.Z_OK, h') →
    BackShape h' s w (2 ^ windowBits.toInt.toNat)

/-- A caller step keeps the shape. -/
theorem BackShape.caller {h h' : Heap} {s : StreamPtr} {w : BPtr} {n : Nat} (sh : BackShape h s w n)
    (st : BackCallerStep h h' s w) : BackShape h' s w n := by
  obtain ⟨i, b, wb, woff, z, S, rfl, rfl, bs⟩ := sh
  obtain ⟨⟨i', z1, z', b', hs', hz1, hz', hzb, hzr, hb, hi, ha, -, -, -⟩, hwin⟩ := st
  cases hs'
  have e1 : z1 = z := by have := bs.hz; simp only [shapeEnv] at this; rw [hz1] at this; exact Option.some.inj this
  subst e1
  have e2 : b' = b := by have := bs.zs; simp only [shapeEnv] at this; rw [hzb] at this; exact Option.some.inj this
  subst e2
  obtain ⟨wd, hwd, hws⟩ := bs.wd
  obtain ⟨wd', hwd', hsz⟩ := hwin wb woff wd rfl hwd
  refine ⟨i, b', wb, woff, z', S, rfl, rfl, { bs with
    hz := hz'
    zs := by rw [hzr]; exact bs.zs
    zfree := by rw [hzr]; exact bs.zfree
    hd := by show ∃ d, h'.bytes b' = some d; rw [hb]; exact bs.hd
    hs := by show h'.istates b' = some S; rw [hi]; exact bs.hs
    al := by show ∃ al, h'.iallocs b' = some al ∧ _; rw [ha]; exact bs.al
    wd := ⟨wd', hwd', by rw [hsz]; exact hws⟩ }⟩

/-- An `inflateBack` call keeps the shape. -/
theorem BackShape.back {h : Heap} {s : StreamPtr} {w : BPtr} {n : Nat} (sh : BackShape h s w n)
    {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr} {I : Heap → BPtr → Nat → Nat → Prop}
    (pre : BackCallPre h s w n inCb inDesc outCb outDesc I) :
    ∃ r h', C.run (ZlibNg.Infback.inflateBack s inCb inDesc outCb outDesc) h = .ok (r, h') ∧
      BackShape h' s w n := by
  obtain ⟨i, b, wb, woff, z, S, rfl, rfl, bs⟩ := sh
  obtain ⟨i', z', b', t, hs', hz', hzb, cb, hI, ht⟩ := pre
  cases hs'
  have e1 : z' = z := by have := bs.hz; simp only [shapeEnv] at this; rw [hz'] at this; exact Option.some.inj this
  subst e1
  have e2 : b' = b := by have := bs.zs; simp only [shapeEnv] at this; rw [hzb] at this; exact Option.some.inj this
  subst e2
  let E : BEnv := ⟨i, b', wb, woff, n, inCb, inDesc, outCb, outDesc, I⟩
  obtain ⟨r, H', e, ⟨z2, S2, bs2⟩⟩ := inflateBack_shape E cb (bs.retarget rfl rfl rfl rfl rfl) hI ht
  exact ⟨r, H', e, i, b', wb, woff, z2, S2, rfl, rfl, bs2.retarget rfl rfl rfl rfl rfl⟩

/-- Every reachable call-back stream has the shape, given the shape after `inflateBackInit_`. -/
theorem BackReachable.shape (hinit : InitShape) {h : Heap} {s : StreamPtr} {w : BPtr} {n : Nat}
    (r : BackReachable h s w n) : BackShape h s w n := by
  induction r with
  | init h h' s windowBits w version size hfr hir hv hws hrun => exact hinit h h' s windowBits w version size hfr hir hv hws hrun
  | back h h' s w n inCb inDesc outCb outDesc I r _ hpre hrun ih =>
    obtain ⟨r', H', e, sh'⟩ := ih.back hpre
    rw [hrun] at e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    exact sh'
  | caller h h' s w n _ hst ih => exact ih.caller hst

/-- `Goal.inflateBack_safety` from the shape after `inflateBackInit_`. -/
theorem inflateBack_safety_of_init (hinit : InitShape) : Goal.inflateBack_safety := by
  intro h s inCb inDesc outCb outDesc hh hpre
  rcases hh with rfl | ⟨z, ⟨i, rfl, hz⟩, hzs⟩ | ⟨w, n, hr⟩
  · exact ⟨_, _, rfl⟩
  · refine ⟨Z_STREAM_ERROR, h, ?_⟩
    simp [C.run, inflateBack, bind_app, ZlibNg.Inflate.rdZ, ldStream, hz, hzs]
  · obtain ⟨I, pre⟩ := hpre w n hr
    obtain ⟨r, h', e, -⟩ := (BackReachable.shape hinit hr).back pre
    exact ⟨r, h', e⟩

end ZlibNgF.Proof.InfbackLoop
