import ZlibNgF.Proof.«public-inflate»
import ZlibNgF.Spec.Common.Deflate

/-!
# What the inflate calls keep beyond their frame (`ZlibNgF`)

Facts for the callers of the inflate functions inside the library (the gz functions): an inflate-side call changes no
deflate object, keeps the static bytes, does not shrink `nextBlk`, and keeps the heap well formed (`FreshBlocks`,
`DFreshBlocks`) and the object bound (`ObjBound`). All of it comes from `InflateKeep`: every run of the translated code
that returns keeps `KR`. A successful `inflateInit_` / `inflateInit2_` attaches the block numbered `h.nextBlk` (the
first fresh one) to the stream as its state block, with the invariant.

Bridges to the deflate frame: `IFrame` gives `DFrame`, and `DFrame` gives `Frame`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateExtra
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof
open ZlibNgF.Proof.InflateKeep (Keep KR)

/-- What a run that keeps `KR` keeps. -/
def Keeps (h h' : Heap) : Prop :=
  h'.dstates = h.dstates ∧ h'.dallocs = h.dallocs ∧ h'.consts = h.consts ∧ h.nextBlk ≤ h'.nextBlk ∧
    (ObjBound h → ObjBound h') ∧ (FreshBlocks h → FreshBlocks h') ∧ (DFreshBlocks h → DFreshBlocks h')

theorem keeps_of_kr {h h' : Heap} (k : KR h h') : Keeps h h' := by
  refine ⟨k.ds, k.da, k.cs, k.nb, k.ob, k.fresh, fun ⟨f, d⟩ => ⟨k.fresh f, fun b hb => ?_⟩⟩
  rw [k.ds, k.da]
  exact d b (Nat.le_trans k.nb hb)

theorem keeps_of {α : Type} {m : M α} (hk : Keep m) {h h' : Heap} {r : α} (e : m h = .ok (r, h')) : Keeps h h' :=
  keeps_of_kr (hk.run _ _ _ e)

/-! ## The calls -/

theorem inflate_keeps (s : StreamPtr) (flush : Int32) (h : Heap) (r : Int32) (h' : Heap)
    (e : inflate s flush h = .ok (r, h')) : Keeps h h' := keeps_of (InflateKeep.K.ZlibNg.Inflate.inflate s flush) e

theorem inflateInit__keeps (s : StreamPtr) (version : BPtr) (size : Int32) (h : Heap) (r : Int32) (h' : Heap)
    (e : inflateInit_ s version size h = .ok (r, h')) : Keeps h h' :=
  keeps_of (InflateKeep.K.ZlibNg.Inflate.inflateInit_ s version size) e

theorem inflateInit2__keeps (s : StreamPtr) (wb : Int32) (version : BPtr) (size : Int32) (h : Heap) (r : Int32)
    (h' : Heap) (e : inflateInit2_ s wb version size h = .ok (r, h')) : Keeps h h' :=
  keeps_of (InflateKeep.K.ZlibNg.Inflate.inflateInit2_ s wb version size) e

theorem inflateReset_keeps (s : StreamPtr) (h : Heap) (r : Int32) (h' : Heap)
    (e : inflateReset s h = .ok (r, h')) : Keeps h h' := keeps_of (InflateKeep.K.ZlibNg.Inflate.inflateReset s) e

theorem inflateResetKeep_keeps (s : StreamPtr) (h : Heap) (r : Int32) (h' : Heap)
    (e : inflateResetKeep s h = .ok (r, h')) : Keeps h h' :=
  keeps_of (InflateKeep.K.ZlibNg.Inflate.inflateResetKeep s) e

theorem inflateReset2_keeps (s : StreamPtr) (wb : Int32) (h : Heap) (r : Int32) (h' : Heap)
    (e : inflateReset2 s wb h = .ok (r, h')) : Keeps h h' :=
  keeps_of (InflateKeep.K.ZlibNg.Inflate.inflateReset2 s wb) e

theorem inflateEnd_keeps (s : StreamPtr) (h : Heap) (r : Int32) (h' : Heap)
    (e : inflateEnd s h = .ok (r, h')) : Keeps h h' := keeps_of (InflateKeep.K.ZlibNg.Inflate.inflateEnd s) e

/-! ## The statements for the gz proofs -/

theorem inflate_extra : ∀ h i flush r h', InflateInv.Inv h (some i) → StreamIO h (some i) →
    h.crcTable = ZlibNg.Crc32Tbl.crc_table → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    h'.dstates = h.dstates ∧ h'.dallocs = h.dallocs ∧ (ObjBound h → ObjBound h') ∧
      (FreshBlocks h → FreshBlocks h') := by
  intro h i flush r h' _ _ _ e
  obtain ⟨d, a, _, _, o, f, _⟩ := inflate_keeps _ _ _ _ _ e
  exact ⟨d, a, o, f⟩

/-- `inflate` keeps the static bytes (`Heap.consts`): it neither changes nor adds one. -/
theorem inflate_consts : ∀ s flush h r h', ZlibNg.Inflate.inflate s flush h = .ok (r, h') → h'.consts = h.consts :=
  fun s flush h r h' e => (inflate_keeps s flush h r h' e).2.2.1

/-- `inflateInit2_`, whatever it returns: no deflate object changes, the static bytes stay, `nextBlk` does not
shrink, the heap stays well formed and the object bound holds. On success the stream's state is the block numbered
`h.nextBlk` (the first fresh block, so `nextBlk` grows), with the invariant. -/
theorem inflateInit2__extra : ∀ h s wb version size r h', FreshBlocks h → InitReady h s → VersionOk h version →
    ZlibNg.Inflate.inflateInit2_ s wb version size h = .ok (r, h') →
    Keeps h h' ∧ FreshBlocks h' ∧
      (r = Z_OK → ∃ i z st, s = some i ∧ h'.streams i = some z ∧ z.state = some h.nextBlk ∧
        h'.istate h.nextBlk = some st ∧ h.nextBlk < h'.nextBlk ∧ InflateInv.Inv h' s) := by
  intro h s wb version size r h' hfr hi hv e
  have k := inflateInit2__keeps _ _ _ _ _ _ _ e
  refine ⟨k, k.2.2.2.2.2.1 hfr, fun hr => ?_⟩
  subst hr
  obtain ⟨c, hc⟩ := InflateInit.checkVer_ok h version size hv
  have e2 : inflateInit2 s wb h = .ok (Z_OK, h') := by
    cases c
    · simpa [inflateInit2_, bind_app, hc] using e
    · simp [inflateInit2_, bind_app, hc] at e; exact absurd e.1 (by decide)
  rcases hi with rfl | ⟨z, ⟨i, rfl, hz⟩, hza, hzf⟩
  · simp [inflateInit2] at e2; exact absurd e2.1 (by decide)
  obtain ⟨r1, h1, e1, -, hinv, -, hst, -⟩ :=
    InflateAlloc.init2_ok hz hza hzf (hfr _ (Nat.le_refl _)).1 (hfr _ (Nat.le_refl _)).2.1 wb
  rw [e2] at e1
  cases e1
  obtain ⟨z', st', hz', hzs, hist, -, -, -⟩ := hst rfl
  refine ⟨i, z', st', rfl, hz', hzs, hist, ?_, hinv rfl⟩
  refine Nat.lt_of_not_le fun hle => ?_
  have := (k.2.2.2.2.2.1 hfr) h.nextBlk hle
  simp [Heap.istate, this.1] at hist
  split at hist <;> cases hist

/-- `inflateInit_`: as `inflateInit2__extra`. -/
theorem inflateInit__extra : ∀ h s version size r h', FreshBlocks h → InitReady h s → VersionOk h version →
    ZlibNg.Inflate.inflateInit_ s version size h = .ok (r, h') →
    Keeps h h' ∧ FreshBlocks h' ∧
      (r = Z_OK → ∃ i z st, s = some i ∧ h'.streams i = some z ∧ z.state = some h.nextBlk ∧
        h'.istate h.nextBlk = some st ∧ h.nextBlk < h'.nextBlk ∧ InflateInv.Inv h' s) := by
  intro h s version size r h' hfr hi hv e
  have e' : ZlibNg.Inflate.inflateInit2_ s DEF_WBITS version size h = .ok (r, h') := by
    simpa [inflateInit_, inflateInit2_] using e
  exact inflateInit2__extra h s DEF_WBITS version size r h' hfr hi hv e'

/-- `inflateReset`, `inflateReset2`, `inflateEnd`: `Keeps`, and so `FreshBlocks` is kept. -/
theorem inflateReset_extra : ∀ s h r h', ZlibNg.Inflate.inflateReset s h = .ok (r, h') → Keeps h h' :=
  inflateReset_keeps

theorem inflateReset2_extra : ∀ s wb h r h', ZlibNg.Inflate.inflateReset2 s wb h = .ok (r, h') → Keeps h h' :=
  inflateReset2_keeps

theorem inflateEnd_extra : ∀ s h r h', ZlibNg.Inflate.inflateEnd s h = .ok (r, h') → Keeps h h' :=
  inflateEnd_keeps

/-! ## Bridges between the frames -/

theorem iframe_dframe {h h' : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : IFrame h h' S B G W) :
    DFrame h h' S B G W :=
  ⟨f.1, fun _ _ _ => ⟨by rw [f.2.1], by rw [f.2.2]⟩⟩

theorem dframe_frame {h h' : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : DFrame h h' S B G W) :
    Frame h h' S B G W :=
  f.1

theorem iframe_frame {h h' : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : IFrame h h' S B G W) :
    Frame h h' S B G W :=
  f.1

end ZlibNgF.Proof.InflateExtra
