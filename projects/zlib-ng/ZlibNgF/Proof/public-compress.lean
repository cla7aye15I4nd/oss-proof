import ZlibNgF.Proof.«public-deflate»
import ZlibNgF.Proof.«deflate.c.gz»
import ZlibNgF.Proof.«public-uncompress»
import ZlibNgF.Proof.«deflate.c.gz.io»

/-!
# The safety of `compress2_z`, `compress2`, `compress_z` and `compress` (`ZlibNgF`)

`compress2_z` makes a local `z_stream`, calls `deflateInit`, runs `deflate` in a `do … while` loop that hands the
caller's lengths to the stream in chunks of at most `UINT_MAX` bytes (`Z_NO_FLUSH` while source bytes remain outside
the stream, then `Z_FINISH`), and ends the stream. The loop invariant (`J`): the local stream is reachable
(`DeflateReachable`: `deflateInit_`, then caller steps and `deflate` steps) with no registered header, its state is
in a block that did not exist before the call, its input position is inside the source with `avail_in` plus the
remaining `len` bytes before the end, and its output position is inside the destination with `avail_out` plus the
remaining `left` bytes before the end. The measure is `len + avail_in + left + avail_out`: refilling the stream keeps
it, and every trip that continues the loop (`deflate` returned `Z_OK`) lowers it (`DeflateProgress`). It starts at
`sourceLen` plus `*destLen`, below `2^64` by `ObjBound`.

What the proof takes of the deflate side besides `DeflateOk` (`StrategyFacts`):

* `DInitFresh` (proved: `dInitFresh`, from `DeflateGz.init2_part`): `deflateInit_` on a stream with no state keeps
  the stream record; on success the state is in a block that did not exist before, with no registered header.
* `DeflateProgress`: `deflate` moves `next_in` / `next_out` by the bytes it consumes and produces (`BufAdv`), keeps
  "no registered header", and when it returns `Z_OK` with `Z_FINISH`, or with `Z_NO_FLUSH` on a non-empty input, it
  consumed input or produced output. Not proved yet: the `compress*` goals are proved given it
  (`*_safety_of_progress`). `deflate_nonvacuous` needs only `dInitFresh`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Compress
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Compress ZlibNg.Zbuild
open ZlibNgF.Proof.DeflateInv (DInv)
open ZlibNgF.Proof.DeflateSide (DSide)
open ZlibNgF.Proof.DeflateFacts (StrategyFacts)
open ZlibNgF.Proof.GzWriteNeeds (Adv BufAdv)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.Uncompress (sat_cdoWhile_heap rdZ_app wrZ_app dropStream_app disjoint_symm strLit_app
  get_size_none space_get_streams InJ)

/-! ## What the proof takes of the deflate side -/

/-- `deflateInit_` on a stream with no state keeps the stream record; on success the state is in a block that did
not exist before, and no header is registered. -/
def DInitFresh : Prop :=
  ∀ (h h' : Heap) (s : StreamPtr) (level : Int32) (version : BPtr) (size r : Int32) (z : ZStream),
    StreamAt h s z → z.state = none → DInitReady h s → DFreshBlocks h → VersionOk h version →
    C.run (deflateInit_ s level version size) h = .ok (r, h') →
    (∃ z', StreamAt h' s z') ∧
      (r = Z_OK → ∃ sb, StateBlock h' s sb ∧ h.nextBlk ≤ sb ∧ DRegisteredHeader h' s none)

/-- `deflate` moves the buffer fields by the bytes it consumes and produces, keeps "no registered header", and when it
returns `Z_OK` with `Z_FINISH`, or with `Z_NO_FLUSH` on a non-empty input, it consumed input or produced output. -/
def DeflateProgress : Prop :=
  ∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DInv h s → DSide h s → CrcGlobals h → DStreamIO h s →
    C.run (deflate s flush) h = .ok (r, h') → ∀ z, StreamAt h s z →
    ∃ z', StreamAt h' s z' ∧ BufAdv z z' ∧ (DRegisteredHeader h s none → DRegisteredHeader h' s none) ∧
      (r = Z_OK → (flush = Z_FINISH ∨ (flush = Z_NO_FLUSH ∧ 0 < z.avail_in)) →
        z'.avail_in < z.avail_in ∨ z'.avail_out < z.avail_out)

/-! ## Frames -/

theorem DFrame.mono {h h' : Heap} {S B G S' B' G' : List Nat} {W W' : List (BPtr × Nat)} (f : DFrame h h' S B G W)
    (hS : ∀ x, x ∈ S → x ∈ S') (hB : ∀ x, x ∈ B → x ∈ B') (hG : ∀ x, x ∈ G → x ∈ G') (hW : ∀ x, x ∈ W → x ∈ W') :
    DFrame h h' S' B' G' W' :=
  ⟨ZlibNgF.Proof.InflateLoop.Frame.mono f.1 hS hB hG hW, fun c hc hn => f.2 c hc (fun m => hn (hB c m))⟩

theorem dframe_trans {h1 h2 h3 : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : DFrame h1 h2 S B G W)
    (g : DFrame h2 h3 S B G W) : DFrame h1 h3 S B G W :=
  ZlibNgF.Proof.DeflateSetDict.DFrame.trans f g

/-- A change of the stream records only. -/
theorem dframe_streams (H : Heap) (X : Tbl (Option ZStream)) (i : Nat) (hX : ∀ j, j ≠ i → X j = H.streams j)
    (B G : List Nat) (W : List (BPtr × Nat)) : DFrame H { H with streams := X } [i] B G W :=
  ⟨ZlibNgF.Proof.Uncompress.frame_streams H X i hX B G W, fun _ _ _ => ⟨rfl, rfl⟩⟩

/-- A write range at `NULL` constrains nothing. -/
theorem dframe_null {h h' : Heap} {S B G : List Nat} {n : Nat} (f : DFrame h h' S B G [(.null, n)])
    (W : List (BPtr × Nat)) : DFrame h h' S B G W := by
  obtain ⟨⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩, d1⟩ := f
  refine ⟨⟨s1, g1, i1, fun c hc hn data hd => ?_, n1, c1, r1, x1, a1, k1⟩, d1⟩
  obtain ⟨d2, e2, s2, q2⟩ := b1 c hc hn data hd
  refine ⟨d2, e2, s2, fun j hj _ => q2 j hj ?_⟩
  intro w hw off he
  rw [List.mem_singleton] at hw
  subst hw
  cases he

/-- The end of the call: the local stream is gone again, and its state block is a fresh one. -/
theorem frame_fin {h H : Heap} {i sb : Nat} {W : List (BPtr × Nat)} (f : DFrame h H [i] [sb] [] W)
    (hi : H.streams i = h.streams i) (hsb : h.nextBlk ≤ sb) : DFrame h H [] [] [] W := by
  obtain ⟨⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩, d1⟩ := f
  refine ⟨⟨fun j _ => ?_, g1, fun b hb _ => i1 b hb (by simp; omega), fun b hb _ d hd => b1 b hb (by simp; omega) d hd,
    fun b hb _ hn => n1 b hb (by simp; omega) hn, c1, r1, x1, a1, k1⟩, fun b hb _ => d1 b hb (by simp; omega)⟩
  by_cases e : j = i
  · subst e; exact hi
  · exact s1 j (by simpa using e)

/-! ## The loop invariant -/

/-- What one call fixes: the heap at the start of the loop, the local stream and its state block, the source and the
destination with their lengths. -/
structure Cx where
  h0 : Heap
  i : Nat
  sb : Nat
  src : BPtr
  sl : UInt64
  dst : BPtr
  dl : UInt64

/-- The facts of the call that do not change. -/
structure Cx.OK (C : Cx) : Prop where
  src : ∀ r o, C.src = .ref r o → r ≠ .heap C.sb ∧ ∀ c, r = .heap c → c < C.h0.nextBlk
  dst : ∀ r o, C.dst = .ref r o → ∃ bo, r = .heap bo ∧ bo < C.h0.nextBlk ∧ bo ≠ C.sb
  disj : Disjoint C.dst C.dl.toNat C.src C.sl.toNat
  crc : CrcGlobals C.h0

/-- The loop invariant, with the remaining lengths `left` and `len`. -/
def J (C : Cx) (left len : UInt64) (H : Heap) : Prop :=
  ∃ z, H.streams C.i = some z ∧ z.state = some C.sb ∧ DeflateReachable H (some C.i) ∧
    DRegisteredHeader H (some C.i) none ∧ DFrame C.h0 H [C.i] [C.sb] [] [(C.dst, C.dl.toNat)] ∧
    InJ C.dst C.dl H z.next_out z.avail_out left ∧ InJ C.src C.sl H z.next_in z.avail_in len

/-- The measure of the loop. -/
def μ (C : Cx) (s : Int32 × UInt64 × UInt64) (H : Heap) : Nat :=
  s.2.1.toNat + s.2.2.toNat + match H.streams C.i with
    | some z => z.avail_in.toNat + z.avail_out.toNat
    | none => 0

/-- Where the loop ends: the stream reachable, ready for `deflateEnd`. -/
def Qe (C : Cx) (_ : Int32 × UInt64 × UInt64) (H : Heap) : Prop :=
  DeflateReachable H (some C.i) ∧ DFrame C.h0 H [C.i] [C.sb] [] [(C.dst, C.dl.toNat)] ∧
    ∃ z, H.streams C.i = some z ∧ z.state = some C.sb

theorem crc_of {C : Cx} (ok : C.OK) {H : Heap} {S B G : List Nat} {W : List (BPtr × Nat)}
    (f : DFrame C.h0 H S B G W) : CrcGlobals H :=
  ⟨f.1.2.2.2.2.2.2.1.trans ok.crc.1, f.1.2.2.2.2.2.2.2.1.trans ok.crc.2⟩

/-- The buffers of the invariant are valid for `deflate`. -/
theorem J.io {C : Cx} (ok : C.OK) {left len : UInt64} {H : Heap} (hj : J C left len H) : DStreamIO H (some C.i) := by
  obtain ⟨z, hz, hb, -, hreg, fJ, hout, hin⟩ := hj
  have hnext : C.h0.nextBlk ≤ H.nextBlk := fJ.1.2.2.2.2.2.2.2.2.2
  -- the output
  have hw : NullOrWrite H z.next_out z.avail_out.toNat ∧ NotInBlock C.sb z.next_out := by
    unfold InJ at hout
    revert hout
    rcases hd : C.dst with _ | ⟨r, o⟩
    · rintro ⟨hn, -, -⟩
      exact ⟨Or.inl hn, fun off e => by rw [hn] at e; cases e⟩
    · rintro ⟨⟨d, hg, hds⟩, q, hq, hq1, hq2⟩
      obtain ⟨bo, rfl, -, hne⟩ := ok.dst _ _ hd
      exact ⟨Or.inr ⟨bo, q, d, hq, hg, by omega⟩, fun off e => by
        rw [hq] at e; injection e with e; injection e with e; exact hne e⟩
  -- the input
  have hr : NullOrRead H z.next_in z.avail_in.toNat ∧ NotInBlock C.sb z.next_in := by
    unfold InJ at hin
    revert hin
    rcases hs : C.src with _ | ⟨r, o⟩
    · rintro ⟨hn, -, -⟩
      exact ⟨Or.inl hn, fun off e => by rw [hn] at e; cases e⟩
    · rintro ⟨⟨d, hg, hds⟩, q, hq, hq1, hq2⟩
      exact ⟨Or.inr ⟨r, q, d, hq, hg, by omega⟩, fun off e => by
        rw [hq] at e; injection e with e; exact (ok.src _ _ hs).1 e⟩
  -- the two do not overlap
  have hdj : Disjoint z.next_out z.avail_out.toNat z.next_in z.avail_in.toNat := by
    have dj := ok.disj
    unfold InJ at hout hin
    rcases hd : C.dst with _ | ⟨r, o⟩
    · rw [hd] at hout; rw [hout.1]; simp [Disjoint]
    rcases hs : C.src with _ | ⟨r', o'⟩
    · rw [hs] at hin; rw [hin.1]; rcases z.next_out with _ | _ <;> simp [Disjoint]
    rw [hd] at hout; rw [hs] at hin; rw [hd, hs] at dj
    obtain ⟨-, q, hq, hq1, hq2⟩ := hout
    obtain ⟨-, q', hq', hq'1, hq'2⟩ := hin
    rw [hq, hq']
    simp only [Disjoint] at dj ⊢
    rcases dj with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))
  refine ⟨z, C.sb, none, ⟨C.i, rfl, hz⟩, hb, hreg, (fun k hk => by cases hk), hr.1, hw.1, hw.2, ?_⟩
  rintro r (rfl | ⟨k, hk, -⟩)
  · exact ⟨hdj, hr.2⟩
  · cases hk

/-- What a trip of the loop ends with, below the measure `m`. -/
def Post (C : Cx) (m : Nat) (s : Int32 × UInt64 × UInt64) (H : Heap) : Prop :=
  (s.1 = Z_OK → J C s.2.1 s.2.2 H ∧ μ C s H < m) ∧ Qe C s H

/-- A position that moves by the bytes consumed stays inside its object. -/
theorem inJ_adv {src : BPtr} {sl : UInt64} {H H' : Heap} {p p' : BPtr} {a a' : UInt32} {len : UInt64}
    (hin : InJ src sl H p a len) (hle : a' ≤ a) (hadv : Adv p p' (a.toNat - a'.toNat))
    (hget : ∀ r o, src = .ref r o → ∀ d, Space.get H r = some d → ∃ d', Space.get H' r = some d' ∧ d'.size = d.size) :
    InJ src sl H' p' a' len := by
  have hle' : a'.toNat ≤ a.toNat := hle
  unfold InJ at hin ⊢
  revert hin hget
  rcases src with _ | ⟨r, o⟩
  · rintro ⟨hn, ha, hl⟩ -
    rw [hn] at hadv
    obtain ⟨-, hp'⟩ := hadv
    refine ⟨hp', ?_, hl⟩
    rw [ha] at hle'
    exact UInt32.toNat_inj.mp (by show a'.toNat = 0; simp at hle'; omega)
  · rintro ⟨⟨d, hd, hds⟩, q, hq, hq1, hq2⟩ hget
    rw [hq] at hadv
    obtain ⟨d', e1, e2⟩ := hget r o rfl d hd
    exact ⟨⟨d', e1, by omega⟩, q + (a.toNat - a'.toNat), hadv, by omega, by omega⟩

/-- The sizes of the objects outside the library's block stay. -/
theorem get_dframe {H H' : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : DFrame H H' S B G W) {r : BRef}
    (hr : ∀ c, r = .heap c → c < H.nextBlk ∧ c ∉ B) {d : Array UInt8} (hd : Space.get H r = some d) :
    ∃ d', Space.get H' r = some d' ∧ d'.size = d.size :=
  ZlibNgF.Proof.Uncompress.get_frame f.1 hr hd

theorem src_get {C : Cx} (ok : C.OK) {H H' : Heap} {S G : List Nat} {W : List (BPtr × Nat)}
    (hn : C.h0.nextBlk ≤ H.nextBlk) (f : DFrame H H' S [C.sb] G W) :
    ∀ r o, C.src = .ref r o → ∀ d, Space.get H r = some d → ∃ d', Space.get H' r = some d' ∧ d'.size = d.size := by
  intro r o hs d hd
  refine get_dframe f (fun c hc => ?_) hd
  obtain ⟨h1, h2⟩ := ok.src r o hs
  have := h2 c hc
  refine ⟨by omega, ?_⟩
  simp only [List.mem_singleton]
  rintro rfl; exact h1 hc

theorem dst_get {C : Cx} (ok : C.OK) {H H' : Heap} {S G : List Nat} {W : List (BPtr × Nat)}
    (hn : C.h0.nextBlk ≤ H.nextBlk) (f : DFrame H H' S [C.sb] G W) :
    ∀ r o, C.dst = .ref r o → ∀ d, Space.get H r = some d → ∃ d', Space.get H' r = some d' ∧ d'.size = d.size := by
  intro r o hs d hd
  refine get_dframe f (fun c hc => ?_) hd
  obtain ⟨bo, rfl, h1, h2⟩ := ok.dst r o hs
  cases hc
  exact ⟨by omega, by simpa using h2⟩

/-- The frame of a `deflate` call, widened to the destination. -/
theorem frame_out {C : Cx} (ok : C.OK) {H H' : Heap} {z : ZStream} {left : UInt64}
    (hout : InJ C.dst C.dl H z.next_out z.avail_out left)
    (f : DFrame H H' [C.i] [C.sb] [] [(z.next_out, z.avail_out.toNat)]) :
    DFrame H H' [C.i] [C.sb] [] [(C.dst, C.dl.toNat)] := by
  unfold InJ at hout
  revert hout
  rcases hd : C.dst with _ | ⟨r, o⟩
  · rintro ⟨hn, -, -⟩
    rw [hn] at f
    exact dframe_null f _
  · rintro ⟨-, q, hq, hq1, hq2⟩
    obtain ⟨bo, rfl, -, -⟩ := ok.dst _ _ hd
    rw [hq] at f
    exact ⟨ZlibNgF.Proof.InflateLoop.Frame.widen f.1 (List.mem_singleton_self _) hq1 (by omega), f.2⟩

/-- The call of `deflate` at the end of a trip. -/
theorem step_deflate (SF : StrategyFacts) (N : DeflateProgress) {C : Cx} (ok : C.OK) {left len : UInt64} {H : Heap}
    (hj : J C left len H) (fl : Int32)
    (hfl : fl = Z_FINISH ∨ (fl = Z_NO_FLUSH ∧ ∀ z, H.streams C.i = some z → 0 < z.avail_in)) (e0 : Int32)
    {m : Nat} (hm : μ C (e0, left, len) H ≤ m) :
    Sat H (do let err ← deflate (some C.i) fl; pure (err, left, len)) (Post C m) := by
  have hio := hj.io ok
  obtain ⟨z, hz, hb, hr, hreg, fJ, hout, hin⟩ := hj
  have hcg := crc_of ok fJ
  have hnext : C.h0.nextBlk ≤ H.nextBlk := fJ.1.2.2.2.2.2.2.2.2.2
  obtain ⟨hv, hs⟩ := DeflateReach.dreach (DeflateBody.dpending SF) hr
  obtain ⟨r, H3, e, f3, -, -, -⟩ := DeflateBody.deflate_ok SF H (some C.i) fl hv hs hcg hio
  obtain ⟨z', ⟨i', ei, hz'⟩, ⟨hai, hao, hadvi, hadvo, hst⟩, hreg', hprog⟩ :=
    N H H3 (some C.i) fl r hv hs hcg hio e z ⟨C.i, rfl, hz⟩
  cases ei
  refine Sat.bind ⟨r, H3, e, Sat.pure ?_⟩
  rw [DeflateReach.stateIds_of hz hb] at f3
  have f3o : dOutputRanges H (some C.i) = [(z.next_out, z.avail_out.toNat)] := by simp [dOutputRanges, hz]
  rw [f3o] at f3
  have f3' := frame_out ok hout f3
  have fN := dframe_trans fJ f3'
  have hr3 : DeflateReachable H3 (some C.i) := DeflateReachable.step H H3 _ hr (Or.inl ⟨fl, r, hcg, hio, e⟩)
  have hb3 : z'.state = some C.sb := hst.trans hb
  refine ⟨fun hr0 => ⟨⟨z', hz', hb3, hr3, hreg' hreg, fN, inJ_adv hout hao hadvo (dst_get ok hnext f3),
    inJ_adv hin hai hadvi (src_get ok hnext f3)⟩, ?_⟩, hr3, fN, z', hz', hb3⟩
  have hm' : left.toNat + len.toNat + (z.avail_in.toNat + z.avail_out.toNat) ≤ m := by
    simpa only [μ, hz] using hm
  have hai' : z'.avail_in.toNat ≤ z.avail_in.toNat := hai
  have hao' : z'.avail_out.toNat ≤ z.avail_out.toNat := hao
  have hp : z'.avail_in.toNat < z.avail_in.toNat ∨ z'.avail_out.toNat < z.avail_out.toNat := by
    have := hprog hr0 (by
      rcases hfl with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2 z hz⟩)
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr h
  show left.toNat + len.toNat + (match H3.streams C.i with
    | some z => z.avail_in.toNat + z.avail_out.toNat
    | none => 0) < m
  rw [hz']
  show left.toNat + len.toNat + (z'.avail_in.toNat + z'.avail_out.toNat) < m
  omega

/-! ## Refilling the stream -/

/-- A change of the buffer fields of the local stream is a caller step, and keeps "no registered header". -/
theorem caller_set {H : Heap} {i : Nat} {z z' : ZStream} (hz : H.streams i = some z)
    (hreg : DRegisteredHeader H (some i) none)
    (e : z' = { z with
      next_in := z'.next_in
      avail_in := z'.avail_in
      next_out := z'.next_out
      avail_out := z'.avail_out }) :
    DCallerStep H { H with streams := upd H.streams i (some z') } (some i) ∧
      DRegisteredHeader { H with streams := upd H.streams i (some z') } (some i) none := by
  obtain ⟨b, st, ⟨⟨z0, ⟨i0, ei, hz0⟩, hb⟩, hst⟩, hg⟩ := hreg
  cases ei
  rw [hz] at hz0; cases hz0
  have hs' : z'.state = z.state := by rw [e]
  refine ⟨⟨i, z, z', b, st, rfl, hz, by simp, hb, hst, e, rfl, rfl, rfl, fun k g hk _ => ?_, rfl, Nat.le_refl _⟩,
    b, st, ⟨⟨z', ⟨i, rfl, by simp⟩, hs'.trans hb⟩, hst⟩, hg⟩
  rw [hg] at hk; cases hk

/-- A position at the end of its range gets `a` of the remaining `len` bytes. -/
theorem inJ_set {src : BPtr} {sl : UInt64} {H H' : Heap} {p : BPtr} {len len' : UInt64} {a : UInt32}
    (hin : InJ src sl H p 0 len) (ha : a.toNat + len'.toNat = len.toNat)
    (hg : ∀ r : BRef, (Space.get H' r : Option (Array UInt8)) = Space.get H r) : InJ src sl H' p a len' := by
  unfold InJ at hin ⊢
  revert hin
  rcases src with _ | ⟨r, o⟩
  · rintro ⟨hn, -, hl⟩
    rw [hl] at ha
    have h0 : (0 : UInt64).toNat = 0 := rfl
    refine ⟨hn, UInt32.toNat_inj.mp (by show a.toNat = 0; omega), UInt64.toNat_inj.mp (by rw [h0]; omega)⟩
  · rintro ⟨⟨d, hd, hds⟩, q, hq, hq1, hq2⟩
    refine ⟨⟨d, by rw [hg]; exact hd, hds⟩, q, hq, hq1, ?_⟩
    have h0 : (0 : UInt32).toNat = 0 := rfl
    rw [h0] at hq2
    omega

/-- A refill of the local stream keeps the invariant. -/
theorem J.set {C : Cx} {left len left' len' : UInt64} {H : Heap} (hj : J C left len H) {z z' : ZStream}
    (hz : H.streams C.i = some z)
    (e : z' = { z with
      next_in := z'.next_in
      avail_in := z'.avail_in
      next_out := z'.next_out
      avail_out := z'.avail_out })
    (hout : InJ C.dst C.dl H z.next_out z.avail_out left →
      InJ C.dst C.dl { H with streams := upd H.streams C.i (some z') } z'.next_out z'.avail_out left')
    (hin : InJ C.src C.sl H z.next_in z.avail_in len →
      InJ C.src C.sl { H with streams := upd H.streams C.i (some z') } z'.next_in z'.avail_in len') :
    J C left' len' { H with streams := upd H.streams C.i (some z') } := by
  obtain ⟨z0, hz0, hb, hr, hreg, fJ, ho, hi⟩ := hj
  rw [hz] at hz0; cases hz0
  obtain ⟨hc, hreg'⟩ := caller_set hz hreg e
  have hs' : z'.state = z.state := by rw [e]
  exact ⟨z', by simp, hs'.trans hb, DeflateReachable.caller _ _ _ hr hc, hreg',
    dframe_trans fJ (dframe_streams H _ C.i (fun j hj => upd_ne _ _ _ _ hj) _ _ _), hout ho, hin hi⟩

/-- The chunk `MIN(UINT_MAX, x)` that a trip hands to the stream. -/
theorem min_chunk (x : UInt64) : (MIN UINT_MAX x).toUInt32.toNat ≤ x.toNat ∧
    (x - (MIN UINT_MAX x).toUInt32.toUInt64).toNat = x.toNat - (MIN UINT_MAX x).toUInt32.toNat ∧
    (x.toNat ≤ 4294967295 → (MIN UINT_MAX x).toUInt32.toNat = x.toNat) ∧
    (4294967295 < x.toNat → (MIN UINT_MAX x).toUInt32.toNat = 4294967295) := by
  have hm : UINT_MAX.toNat = 4294967295 := rfl
  have hc : (MIN UINT_MAX x).toUInt32.toNat = min x.toNat 4294967295 := by
    unfold MIN
    split
    · rename_i h
      have h' : x.toNat < 4294967295 := by rw [gt_iff_lt, UInt64.lt_iff_toNat_lt] at h; omega
      rw [UInt64.toNat_toUInt32]; omega
    · rename_i h
      have h' : 4294967295 ≤ x.toNat := by rw [gt_iff_lt, UInt64.lt_iff_toNat_lt] at h; omega
      rw [UInt64.toNat_toUInt32, hm]; omega
  have hle : (MIN UINT_MAX x).toUInt32.toNat ≤ x.toNat := by rw [hc]; omega
  refine ⟨hle, ?_, fun h => by rw [hc]; omega, fun h => by rw [hc]; omega⟩
  rw [UInt64.toNat_sub_of_le]
  · rw [UInt32.toNat_toUInt64]
  · rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]; exact hle

/-- An `InJ` fact reads the heap only through `Space.get`. -/
theorem inJ_heap {src : BPtr} {sl : UInt64} {H H' : Heap} {p : BPtr} {a : UInt32} {len : UInt64}
    (hin : InJ src sl H p a len) (hg : ∀ r : BRef, (Space.get H' r : Option (Array UInt8)) = Space.get H r) :
    InJ src sl H' p a len := by
  unfold InJ at hin ⊢
  revert hin
  rcases src with _ | ⟨r, o⟩
  · exact id
  · rintro ⟨⟨d, hd, hds⟩, rest⟩
    exact ⟨⟨d, by rw [hg]; exact hd, hds⟩, rest⟩

/-- The flush argument of a trip: `Z_NO_FLUSH` only while source bytes remain outside the stream. -/
theorem flush_of {x : UInt64} {P : Prop} (hp : x ≠ 0 → P) :
    (if (x != 0) = true then Z_NO_FLUSH else Z_FINISH) = Z_FINISH ∨
      ((if (x != 0) = true then Z_NO_FLUSH else Z_FINISH) = Z_NO_FLUSH ∧ P) := by
  by_cases h : x = 0
  · left; subst h; rfl
  · right
    have : (x != 0) = true := by simpa using h
    rw [this]
    exact ⟨rfl, hp h⟩

/-- The last call of a trip and the test of `while (err == Z_OK)`. -/
theorem trip_end (SF : StrategyFacts) (N : DeflateProgress) {C : Cx} (ok : C.OK) {L N0 : UInt64} {H : Heap}
    (hj : J C L N0 H) (fl : Int32)
    (hfl : fl = Z_FINISH ∨ (fl = Z_NO_FLUSH ∧ ∀ z, H.streams C.i = some z → 0 < z.avail_in)) (e0 : Int32) {m : Nat}
    (hm : μ C (e0, L, N0) H ≤ m) :
    Sat H (do let err ← deflate (some C.i) fl; pure (err, L, N0)) (fun s1 H1 =>
      Sat H1 (pure (s1.1 == Z_OK, s1)) (fun cs H2 =>
        (cs.1 = true → J C cs.2.2.1 cs.2.2.2 H2 ∧ μ C cs.2 H2 < m) ∧ (cs.1 = false → Qe C cs.2 H2))) := by
  refine Sat.mono (step_deflate SF N ok hj fl hfl e0 hm) ?_
  rintro ⟨e, l, n⟩ H1 ⟨h1, h2⟩
  refine Sat.pure ⟨fun he => ?_, fun _ => h2⟩
  have : e = Z_OK := by simpa using he
  exact h1 this

/-- The `do … while` loop of `compress2_z`, from the invariant. -/
theorem loop_ok (SF : StrategyFacts) (N : DeflateProgress) {C : Cx} (ok : C.OK) {L N0 : UInt64} {H : Heap}
    (hj : J C L N0 H) (hμ : μ C (Z_OK, L, N0) H < fuel) :
    Sat H (cdoWhile
      (fun ((_, left, sourceLen) : Int32 × UInt64 × UInt64) => do
        let mut left := left
        let mut sourceLen := sourceLen
        if (← rdZ (some C.i) (·.avail_out)) == 0 then
          wrZ (some C.i) fun z => { z with avail_out := (MIN UINT_MAX left).toUInt32 }
          let ao : UInt32 ← rdZ (some C.i) (·.avail_out)
          left := left - ao.toUInt64
        if (← rdZ (some C.i) (·.avail_in)) == 0 then
          wrZ (some C.i) fun z => { z with avail_in := (MIN UINT_MAX sourceLen).toUInt32 }
          let ai : UInt32 ← rdZ (some C.i) (·.avail_in)
          sourceLen := sourceLen - ai.toUInt64
        let err ← ZlibNg.Deflate.deflate (some C.i)
          (if sourceLen != 0 then ZlibNg.Deflate.Z_NO_FLUSH else ZlibNg.Inflate.Z_FINISH)
        pure (err, left, sourceLen))
      (fun (x : Int32 × UInt64 × UInt64) => pure (x.1 == ZlibNg.Inflate.Z_OK, x))
      (Z_OK, L, N0)) (Qe C) := by
  refine sat_cdoWhile_heap (fun s H => J C s.2.1 s.2.2 H) (μ C) (Qe C) ?_ hj hμ
  rintro ⟨e0, left, len⟩ H hj
  dsimp only at hj ⊢
  obtain ⟨z, hz, -⟩ := id hj
  have hcl := min_chunk left
  have hcn := min_chunk len
  -- the second half of a trip: refill `avail_in` if empty, then `deflate`
  have tail : ∀ (L' : UInt64) (H' : Heap) (z' : ZStream), J C L' len H' → H'.streams C.i = some z' →
      μ C (e0, L', len) H' = μ C (e0, left, len) H →
      Sat H' (do
        let a ← rdZ (some C.i) (·.avail_in)
        if (a == 0) = true then do
          wrZ (some C.i) fun z => { z with avail_in := (MIN UINT_MAX len).toUInt32 }
          let ai ← rdZ (some C.i) (·.avail_in)
          let err ← deflate (some C.i) (if (len - ai.toUInt64 != 0) = true then Z_NO_FLUSH else Z_FINISH)
          pure (err, L', len - ai.toUInt64)
        else do
          let err ← deflate (some C.i) (if (len != 0) = true then Z_NO_FLUSH else Z_FINISH)
          pure (err, L', len)) (fun s1 H1 =>
        Sat H1 (pure (s1.1 == Z_OK, s1)) (fun cs H2 =>
          (cs.1 = true → J C cs.2.2.1 cs.2.2.2 H2 ∧ μ C cs.2 H2 < μ C (e0, left, len) H) ∧
            (cs.1 = false → Qe C cs.2 H2))) := by
    intro L' H' z' hj' hz' hμ'
    refine Sat.bind (Sat.of_eq (rdZ_app hz' _) ?_)
    split
    · rename_i h0
      have h0' : z'.avail_in = 0 := by simpa using h0
      refine Sat.bind (Sat.of_eq (wrZ_app hz' _) ?_)
      refine Sat.bind (Sat.of_eq (rdZ_app (upd_same _ _ _) _) ?_)
      dsimp only
      have hj2 : J C L' (len - (MIN UINT_MAX len).toUInt32.toUInt64)
          { H' with streams := upd H'.streams C.i (some { z' with avail_in := (MIN UINT_MAX len).toUInt32 }) } := by
        obtain ⟨-, -, -, -, -, -, -, hin⟩ := id hj'
        obtain ⟨z1, hz1, -⟩ := id hj'
        rw [hz'] at hz1; cases hz1
        refine J.set hj' hz' rfl (fun ho => inJ_heap ho (space_get_streams _ _)) (fun hi => ?_)
        rw [h0'] at hi
        have := hcn.2.1
        exact inJ_set hi (by dsimp only; omega) (space_get_streams _ _)
      have hμ2 : μ C (e0, L', len - (MIN UINT_MAX len).toUInt32.toUInt64)
          { H' with streams := upd H'.streams C.i (some { z' with avail_in := (MIN UINT_MAX len).toUInt32 }) } =
          μ C (e0, L', len) H' := by
        simp only [μ, upd_same, hz']
        rw [h0']
        show L'.toNat + (len - (MIN UINT_MAX len).toUInt32.toUInt64).toNat +
            ((MIN UINT_MAX len).toUInt32.toNat + z'.avail_out.toNat) =
          L'.toNat + len.toNat + ((0 : UInt32).toNat + z'.avail_out.toNat)
        have : (0 : UInt32).toNat = 0 := rfl
        have := hcn.2.1
        omega
      refine trip_end SF N ok hj2 _ (flush_of fun hne z2 hz2 => ?_) e0 (Nat.le_of_eq (hμ2.trans hμ'))
      simp only [upd_same, Option.some.injEq] at hz2
      subst hz2
      have : (len - (MIN UINT_MAX len).toUInt32.toUInt64).toNat ≠ 0 := fun e =>
        hne (UInt64.toNat_inj.mp (by rw [e]; rfl))
      show 0 < (MIN UINT_MAX len).toUInt32.toNat
      have := hcn.2.2.1
      have := hcn.2.2.2
      omega
    · rename_i h0
      have h0' : z'.avail_in ≠ 0 := by simpa using h0
      refine trip_end SF N ok hj' _ (flush_of fun _ z2 hz2 => ?_) e0 (Nat.le_of_eq hμ')
      rw [hz'] at hz2; cases hz2
      have : z'.avail_in.toNat ≠ 0 := fun e => h0' (UInt32.toNat_inj.mp (by rw [e]; rfl))
      show 0 < z'.avail_in.toNat
      omega
  refine Sat.bind (Sat.of_eq (rdZ_app hz _) ?_)
  split
  · rename_i h0
    have h0' : z.avail_out = 0 := by simpa using h0
    refine Sat.bind (Sat.of_eq (wrZ_app hz _) ?_)
    refine Sat.bind (Sat.of_eq (rdZ_app (upd_same _ _ _) _) ?_)
    dsimp only
    have hj1 : J C (left - (MIN UINT_MAX left).toUInt32.toUInt64) len
        { H with streams := upd H.streams C.i (some { z with avail_out := (MIN UINT_MAX left).toUInt32 }) } := by
      refine J.set hj hz rfl (fun ho => ?_) (fun hi => inJ_heap hi (space_get_streams _ _))
      rw [h0'] at ho
      have := hcl.2.1
      exact inJ_set ho (by dsimp only; omega) (space_get_streams _ _)
    refine tail _ _ _ hj1 (upd_same _ _ _) ?_
    simp only [μ, upd_same, hz]
    rw [h0']
    show (left - (MIN UINT_MAX left).toUInt32.toUInt64).toNat + len.toNat +
        (z.avail_in.toNat + (MIN UINT_MAX left).toUInt32.toNat) =
      left.toNat + len.toNat + (z.avail_in.toNat + (0 : UInt32).toNat)
    have : (0 : UInt32).toNat = 0 := rfl
    have := hcl.2.1
    omega
  · exact tail _ _ _ hj hz rfl

/-! ## The call -/

theorem sat_gen {α : Type} {H : Heap} {m : M α} {Q : α → Heap → Prop} (k : ∀ H', H' = H → Sat H' m Q) :
    Sat H m Q := k H rfl

/-- `deflateEnd` on the local stream: the state block and the `state` field change. -/
theorem dframe_end (H : Heap) (i sb : Nat) (z : ZStream) (W : List (BPtr × Nat)) :
    DFrame H { H with
      bytes := upd H.bytes sb none
      savedPtrs := upd H.savedPtrs sb none
      streams := upd H.streams i (some { z with state := none }) } [i] [sb] [] W := by
  refine ⟨⟨fun j hj => upd_ne _ _ _ _ (by simpa using hj), fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
    fun c _ hc d hd => ⟨d, ?_, rfl, fun _ _ _ => rfl⟩, fun c _ hc hn => ?_, rfl, rfl, rfl, rfl, Nat.le_refl _⟩,
    fun _ _ _ => ⟨rfl, rfl⟩⟩
  · show upd H.bytes sb none c = some d
    rw [upd_ne _ _ _ _ (by simpa using hc)]; exact hd
  · show upd H.bytes sb none c = none
    rw [upd_ne _ _ _ _ (by simpa using hc)]; exact hn

theorem compress2_z_some (SF : StrategyFacts) (I : DInitFresh) (N : DeflateProgress) (h : Heap) (dest source : BPtr)
    (dl sl : UInt64) (level : Int32) (hcg : CrcGlobals h) (hfr : DFreshBlocks h) (hob : ObjBound h)
    (hdst : NullOrWrite h dest dl.toNat) (hsrc : NullOrRead h source sl.toNat)
    (hdisj : Disjoint dest dl.toNat source sl.toNat) :
    Sat h (compress2_z dest (some dl) source sl level) (fun _ h' => DFrame h h' [] [] [] [(dest, dl.toNat)]) := by
  unfold compress2_z
  dsimp only
  split
  · exact Sat.pure (DeflateReach.dframe_refl h _ _ _ _)
  rename_i hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, not_and] at hc
  obtain ⟨hcs, hcd⟩ := hc
  have h00 : (0 : UInt64).toNat = 0 := rfl
  have pos : ∀ x : UInt64, x ≠ 0 → x > 0 := fun x hx => by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
    have : x.toNat ≠ 0 := fun e => hx (UInt64.toNat_inj.mp (by rw [e]; rfl))
    show 0 < x.toNat; omega
  have hnb_none : ∀ c, h.nextBlk ≤ c → h.bytes c = none := fun c hc => (hfr.1 c hc).2.2
  have old : ∀ c d, h.bytes c = some d → c < h.nextBlk := fun c d hd =>
    Classical.byContradiction fun hlt => by rw [hnb_none c (by omega)] at hd; cases hd
  -- the source and the destination
  have hS : (source = .null ∧ sl = 0) ∨ ∃ r o d, source = .ref r o ∧ Space.get h r = some d ∧ o + sl.toNat ≤ d.size ∧
      d.size < 2 ^ 63 ∧ ∀ c, r = .heap c → c < h.nextBlk := by
    rcases hsrc with e | ⟨r, o, d, e, hg, hle⟩
    · left
      refine ⟨e, Classical.byContradiction fun hne => hcs (pos sl hne) e⟩
    · right
      refine ⟨r, o, d, e, hg, hle, hob r d hg, fun c hrc => ?_⟩
      subst hrc; exact old c d hg
  have hD : (dest = .null ∧ dl = 0) ∨ ∃ bo o d, dest = .ref (.heap bo) o ∧ h.bytes bo = some d ∧
      o + dl.toNat ≤ d.size ∧ d.size < 2 ^ 63 ∧ bo < h.nextBlk := by
    rcases hdst with e | ⟨b, o, d, e, hd, hle⟩
    · left
      refine ⟨e, Classical.byContradiction fun hne => hcd (pos dl hne) e⟩
    · right
      exact ⟨b, o, d, e, hd, hle, hob (.heap b) d hd, old b d hd⟩
  have hsl : sl.toNat < 2 ^ 63 := by
    rcases hS with ⟨-, rfl⟩ | ⟨r, o, d, -, -, h1, h2, -⟩
    · rw [h00]; decide
    · omega
  have hdl : dl.toNat < 2 ^ 63 := by
    rcases hD with ⟨-, rfl⟩ | ⟨r, o, d, -, -, h1, h2, -⟩
    · rw [h00]; decide
    · omega
  -- the local stream
  refine Sat.bind (Sat.of_eq (show newStream {} h = _ from rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
  simp only [ZlibNgF.Proof.InflateInv.upd_upd]
  refine Sat.bind (Sat.of_eq (strLit_app _) ?_)
  have hi0n : h.streams h.streams.arr.size = none := get_size_none _
  generalize h.streams.arr.size = i0 at hi0n ⊢
  refine sat_gen fun H3 hH3 => ?_
  obtain ⟨z3, hz3, hst3, hza3, hzf3⟩ : ∃ z3 : ZStream, H3.streams i0 = some z3 ∧ z3.state = none ∧
      z3.zalloc = .null ∧ z3.zfree = .null := ⟨_, by rw [hH3]; exact upd_same _ _ _, rfl, rfl, rfl⟩
  have hn3 : H3.nextBlk = h.nextBlk := by rw [hH3]
  have f3 : ∀ W, DFrame h H3 [i0] [] [] W := fun W => by
    rw [hH3]; exact dframe_streams h _ i0 (fun j hj => upd_ne _ _ _ _ hj) _ _ _
  have hfr3 : DFreshBlocks H3 := by rw [hH3]; exact hfr
  have hready : DInitReady H3 (some i0) := Or.inr ⟨z3, ⟨i0, rfl, hz3⟩, Or.inl hza3, Or.inl hzf3⟩
  have hver : VersionOk H3 (.ref (.str 0) 0) := Or.inr ⟨.str 0, 0, _, rfl, rfl, by simp [Heap.litBytes]⟩
  obtain ⟨r, H4, e4, f4⟩ := DeflateInitPublic.deflateInit__safety H3 (some i0) level (.ref (.str 0) 0)
    SIZEOF_Z_STREAM.toInt32 hfr3 hready hver
  obtain ⟨⟨z4, i', ei, hz4⟩, hsucc⟩ := I H3 H4 (some i0) level _ _ r z3 ⟨i0, rfl, hz3⟩ hst3 hready hfr3 hver e4
  cases ei
  refine Sat.bind (Sat.of_eq e4 ?_)
  have f4' : DFrame h H4 [i0] [] [] [(dest, dl.toNat)] := dframe_trans (f3 _) (DFrame.mono f4 (fun _ m => m)
    (fun _ m => m) (fun _ m => m) (fun _ m => nomatch m))
  split
  · -- `deflateInit` failed
    refine Sat.bind (Sat.of_eq (dropStream_app hz4) ?_)
    refine Sat.pure (frame_fin (i := i0) (sb := h.nextBlk) ?_ (by simp [hi0n]) (Nat.le_refl _))
    exact DFrame.mono (dframe_trans f4' (dframe_streams H4 _ i0 (fun j hj => upd_ne _ _ _ _ hj) _ _ _))
      (fun _ m => m) (fun _ m => nomatch m) (fun _ m => m) (fun _ m => m)
  rename_i hr0
  have hr : r = Z_OK := by simpa using hr0
  subst hr
  obtain ⟨sb, ⟨z4', ⟨i'', ei, hz4'⟩, hsb⟩, hsb3, hreg4⟩ := hsucc rfl
  cases ei
  rw [hz4] at hz4'; cases hz4'
  rw [hn3] at hsb3
  have hreach4 : DeflateReachable H4 (some i0) := DeflateReachable.init H3 H4 _ _ _ _ hready hver e4
  refine Sat.bind (Sat.of_eq (wrZ_app hz4 _) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
  refine Sat.bind (Sat.of_eq (wrZ_app (upd_same _ _ _) _) ?_)
  simp only [ZlibNgF.Proof.InflateInv.upd_upd]
  refine sat_gen fun H5 hH5 => ?_
  obtain ⟨hc5, hreg5⟩ := caller_set (z' := { z4 with next_out := dest, avail_out := 0, next_in := source, avail_in := 0 })
    hz4 hreg4 rfl
  rw [← hH5] at hc5 hreg5
  have hz5 : H5.streams i0 = some { z4 with next_out := dest, avail_out := 0, next_in := source, avail_in := 0 } := by
    rw [hH5]; exact upd_same _ _ _
  have f5 : DFrame h H5 [i0] [] [] [(dest, dl.toNat)] := by
    refine dframe_trans f4' ?_
    rw [hH5]; exact dframe_streams H4 _ i0 (fun j hj => upd_ne _ _ _ _ hj) _ _ _
  have hn5 : h.nextBlk ≤ H5.nextBlk := f5.1.2.2.2.2.2.2.2.2.2
  let C : Cx := ⟨H5, i0, sb, source, sl, dest, dl⟩
  have ok : C.OK := by
    refine ⟨fun r o hro => ?_, fun r o hro => ?_, hdisj, ?_⟩
    · rcases hS with ⟨hs0, -⟩ | ⟨r', o', d', hs0, -, -, -, hc⟩
      · have : source = .ref r o := hro; rw [hs0] at this; cases this
      · have : source = .ref r o := hro; rw [hs0] at this; injection this with e1 e2; subst e1
        refine ⟨fun e => by have := hc sb e; omega, fun c hc' => by have := hc c hc'; show c < H5.nextBlk; omega⟩
    · rcases hD with ⟨hd0, -⟩ | ⟨bo, o', d', hd0, -, -, -, hc⟩
      · have : dest = .ref r o := hro; rw [hd0] at this; cases this
      · have : dest = .ref r o := hro; rw [hd0] at this; injection this with e1 e2; subst e1
        exact ⟨bo, rfl, by show bo < H5.nextBlk; omega, by show bo ≠ sb; omega⟩
    · exact ⟨f5.1.2.2.2.2.2.2.1.trans hcg.1, f5.1.2.2.2.2.2.2.2.1.trans hcg.2⟩
  have hj : J C dl sl H5 := by
    have h0 : (0 : UInt32).toNat = 0 := rfl
    refine ⟨_, hz5, hsb, DeflateReachable.caller _ _ _ hreach4 hc5, hreg5, DeflateReach.dframe_refl _ _ _ _ _, ?_, ?_⟩
    · show InJ dest dl H5 dest 0 dl
      rcases hD with ⟨rfl, rfl⟩ | ⟨bo, o, d, rfl, hd, hle, -, hb⟩
      · exact ⟨rfl, rfl, rfl⟩
      · obtain ⟨d', e1, e2⟩ := get_dframe f5 (r := .heap bo) (fun c e => by cases e; exact ⟨hb, by simp⟩) hd
        exact ⟨⟨d', e1, by omega⟩, o, rfl, Nat.le_refl _, by rw [h0]; omega⟩
    · show InJ source sl H5 source 0 sl
      rcases hS with ⟨rfl, rfl⟩ | ⟨r, o, d, rfl, hg, hle, -, hc⟩
      · exact ⟨rfl, rfl, rfl⟩
      · obtain ⟨d', e1, e2⟩ := get_dframe f5 (fun c e => ⟨hc c e, by simp⟩) hg
        exact ⟨⟨d', e1, by omega⟩, o, rfl, Nat.le_refl _, by rw [h0]; omega⟩
  have hμ : μ C (Z_OK, dl, sl) H5 < fuel := by
    show dl.toNat + sl.toNat + (match H5.streams i0 with
      | some z => z.avail_in.toNat + z.avail_out.toNat
      | none => 0) < 2 ^ 64
    rw [hz5]
    show dl.toNat + sl.toNat + ((0 : UInt32).toNat + (0 : UInt32).toNat) < 2 ^ 64
    have : (0 : UInt32).toNat = 0 := rfl
    omega
  refine Sat.bind (Sat.mono (loop_ok SF N ok hj hμ) ?_)
  rintro s6 H6 ⟨hr6, f6, z6, hz6, hb6⟩
  refine Sat.bind (Sat.of_eq (rdZ_app hz6 _) ?_)
  obtain ⟨i7, z7, b7, r7, ei, hz7, hb7, e7⟩ :=
    DeflateControl.deflateEnd_inv (DeflateReach.dreach_inv (DeflateBody.dpending SF) hr6)
  cases ei
  rw [hz6] at hz7; cases hz7
  rw [hb6] at hb7; cases hb7
  refine Sat.bind (Sat.of_eq e7 ?_)
  refine Sat.bind (Sat.of_eq (dropStream_app (upd_same _ _ _)) ?_)
  refine Sat.pure (frame_fin (i := i0) (sb := sb) ?_ (by simp [hi0n]) hsb3)
  refine dframe_trans (DFrame.mono f5 (fun _ m => m) (fun _ m => nomatch m) (fun _ m => m) (fun _ m => m)) ?_
  refine dframe_trans f6 ?_
  refine dframe_trans (dframe_end H6 i0 sb z6 _) ?_
  exact dframe_streams _ _ i0 (fun j hj => upd_ne _ _ _ _ hj) _ _ _

theorem compress2_z_safety_of (SF : StrategyFacts) (I : DInitFresh) (N : DeflateProgress) :
    Goal.compress2_z_safety := by
  intro h dest source destLen sourceLen level hcg hfr hob hdst hsrc hdisj
  rcases destLen with _ | dl
  · exact ⟨(Z_STREAM_ERROR, none), h, rfl, DeflateReach.dframe_refl h _ _ _ _⟩
  obtain ⟨r, h', e, f⟩ := compress2_z_some SF I N h dest source dl sourceLen level hcg hfr hob hdst hsrc hdisj
  exact ⟨r, h', e, f⟩

theorem compress2_safety_of (SF : StrategyFacts) (I : DInitFresh) (N : DeflateProgress) : Goal.compress2_safety := by
  intro h dest source destLen sourceLen level hcg hfr hob hdst hsrc hdisj
  obtain ⟨r, h', e, f⟩ := compress2_z_safety_of SF I N h dest source (some (destLen.getD 0)) sourceLen level hcg hfr
    hob hdst hsrc hdisj
  exact ⟨_, h', by simp only [C.run, compress2, bind_app]; rw [show compress2_z _ _ _ _ _ h = _ from e]; rfl, f⟩

theorem compress_safety_of (SF : StrategyFacts) (I : DInitFresh) (N : DeflateProgress) : Goal.compress_safety := by
  intro h dest source destLen sourceLen hcg hfr hob hdst hsrc hdisj
  exact compress2_safety_of SF I N h dest source destLen sourceLen _ hcg hfr hob hdst hsrc hdisj

theorem compress_z_safety_of (SF : StrategyFacts) (I : DInitFresh) (N : DeflateProgress) : Goal.compress_z_safety := by
  intro h dest source destLen sourceLen hcg hfr hob hdst hsrc hdisj
  exact compress2_z_safety_of SF I N h dest source destLen sourceLen _ hcg hfr hob hdst hsrc hdisj

/-! ## Non-vacuity of `deflate_safety` -/

/-- The heap after the caller hands one-byte input and output buffers (fresh blocks `n`, `n + 1`) to stream 0. -/
def ioHeap (H : Heap) (z : ZStream) (n : Nat) : Heap :=
  { H with
    bytes := upd (upd H.bytes n (some #[0])) (n + 1) (some #[0])
    nextBlk := n + 2
    streams := upd H.streams 0 (some { z with
      next_in := .ref (.heap n) 0, avail_in := 1, next_out := .ref (.heap (n + 1)) 0, avail_out := 1 }) }

theorem deflate_nonvacuous_of (SF : StrategyFacts) (I : DInitFresh) : Goal.deflate_nonvacuous := by
  have hfr : DFreshBlocks DeflateInitPublic.initHeap :=
    ⟨fun b _ => ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b, Tbl.get_empty_opt b⟩,
      fun b _ => ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b⟩⟩
  have hz : DeflateInitPublic.initHeap.streams 0 = some {} := upd_same _ _ _
  obtain ⟨r, h1, e, ⟨fr, _⟩, nv⟩ := (DeflateInit.init2_sat hz (Or.inl rfl) (Or.inl rfl) 6
    Z_DEFLATED.toUInt32.toInt32 MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY).sat (hfr.2 _ (Nat.le_refl _))
  have hr : r = Z_OK := nv rfl rfl (by decide) rfl rfl rfl
  subst hr
  have hc : CHECK_VER_STSIZE (.ref (.str 0) 0) 112 DeflateInitPublic.initHeap =
      .ok (false, DeflateInitPublic.initHeap) := rfl
  have hrun : C.run (deflateInit_ (some 0) 6 (.ref (.str 0) 0) 112) DeflateInitPublic.initHeap = .ok (Z_OK, h1) := by
    simp only [C.run, deflateInit_, bind_app, hc, Bool.false_eq_true, ↓reduceIte]
    exact e
  have hready : DInitReady DeflateInitPublic.initHeap (some 0) := Or.inr ⟨{}, ⟨0, rfl, hz⟩, Or.inl rfl, Or.inl rfl⟩
  have hver : VersionOk DeflateInitPublic.initHeap (.ref (.str 0) 0) :=
    Or.inr ⟨.str 0, 0, _, rfl, rfl, by simp [Heap.litBytes]⟩
  have hr1 : DeflateReachable h1 (some 0) := DeflateReachable.init _ h1 (some 0) 6 _ 112 hready hver hrun
  obtain ⟨-, hsucc⟩ := I _ h1 (some 0) 6 _ 112 Z_OK {} ⟨0, rfl, hz⟩ rfl hready hfr hver hrun
  obtain ⟨sb, ⟨z, ⟨i', ei, hz1⟩, hsb⟩, -, hreg⟩ := hsucc rfl
  cases ei
  obtain ⟨b, st, ⟨⟨z0, ⟨i0, ei, hz0⟩, hb0⟩, hst⟩, hg⟩ := hreg
  cases ei
  rw [hz1] at hz0; cases hz0
  rw [hsb] at hb0; cases hb0
  have hcg : CrcGlobals h1 := ⟨fr.1.2.2.2.2.2.2.1, fr.1.2.2.2.2.2.2.2.1⟩
  -- the caller hands one-byte buffers in fresh blocks `n`, `n + 1` to the stream
  let n := h1.nextBlk + sb + 1
  have hn0 : n ≠ sb := by omega
  have hn1 : n + 1 ≠ sb := by omega
  let z2 : ZStream := { z with
    next_in := .ref (.heap n) 0, avail_in := 1, next_out := .ref (.heap (n + 1)) 0, avail_out := 1 }
  have hz2 : (ioHeap h1 z n).streams 0 = some z2 := upd_same _ _ _
  have hbytes : (ioHeap h1 z n).bytes sb = h1.bytes sb := by
    show upd (upd h1.bytes n (some #[0])) (n + 1) (some #[0]) sb = _
    rw [upd_ne _ _ _ _ (Ne.symm hn1), upd_ne _ _ _ _ (Ne.symm hn0)]
  have hdst : (ioHeap h1 z n).dstate sb = h1.dstate sb := by
    simp only [Heap.dstate, hbytes]; rfl
  have hstep : DCallerStep h1 (ioHeap h1 z n) (some 0) :=
    ⟨0, z, z2, sb, st, rfl, hz1, hz2, hsb, hst, rfl, hbytes, rfl, rfl, (fun k g hk _ => by rw [hg] at hk; cases hk),
      rfl, by show h1.nextBlk ≤ n + 2; omega⟩
  have hr2 : DeflateReachable (ioHeap h1 z n) (some 0) := DeflateReachable.caller _ _ _ hr1 hstep
  have hreg2 : DRegisteredHeader (ioHeap h1 z n) (some 0) none :=
    ⟨sb, st, ⟨⟨z2, ⟨0, rfl, hz2⟩, hsb⟩, by rw [hdst]; exact hst⟩, hg⟩
  have hgn : (Space.get (ioHeap h1 z n) (BRef.heap n) : Option (Array UInt8)) = some #[0] := by
    show upd (upd h1.bytes n (some #[0])) (n + 1) (some #[0]) n = _
    rw [upd_ne _ _ _ _ (by omega)]; exact upd_same _ _ _
  have hgn1 : (ioHeap h1 z n).bytes (n + 1) = some #[0] := upd_same _ _ _
  have hio : DStreamIO (ioHeap h1 z n) (some 0) := by
    refine ⟨z2, sb, none, ⟨0, rfl, hz2⟩, hsb, hreg2, (fun k hk => by cases hk),
      Or.inr ⟨.heap n, 0, _, rfl, hgn, by simp [z2]⟩, Or.inr ⟨n + 1, 0, _, rfl, hgn1, by simp [z2]⟩,
      (fun off e => by injection e with e; injection e with e; exact hn1 e), ?_⟩
    rintro r (rfl | ⟨k, hk, -⟩)
    · refine ⟨Or.inl (fun e => by injection e with e; omega), (fun off e => by
        injection e with e; injection e with e; exact hn0 e)⟩
    · cases hk
  obtain ⟨r, h', e2, -⟩ := DeflateReach.deflate_safety_of (DeflateBody.dpending SF) (ioHeap h1 z n) (some 0) 4
    hcg (Or.inr (Or.inr hr2)) (fun _ => hio)
  exact ⟨ioHeap h1 z n, some 0, h', r, z2, hcg, hr2, hio, ⟨0, rfl, hz2⟩, by simp [z2], by simp [z2],
    by simp [z2], by simp [z2], e2⟩

/-! ## `DInitFresh` -/

/-- `deflateInit_` keeps the stream record, and on success puts the state into a fresh block with no registered
header (`DeflateGz.init2_part` and its `DKeep`). -/
theorem dInitFresh : DInitFresh := by
  intro h h' s level version size r z hz hst hready hfr hver e
  have e2 : C.run (deflateInit2_ s level Z_DEFLATED.toUInt32.toInt32 MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY
      version size) h = .ok (r, h') := e
  obtain ⟨z', hz', -, -, -, -, -, ⟨-, -, hk⟩, hs⟩ := DeflateGz.init2_part h h' s level _ _ _ _ version size r z hz
    hready hfr e2
  refine ⟨⟨z', hz'⟩, fun hr => ?_⟩
  subst hr
  obtain ⟨sb, hsb, hle⟩ := hs rfl
  refine ⟨sb, ⟨z', hz', hsb⟩, hle, ?_⟩
  obtain ⟨i, z1, b, st, al, rfl, hz1, hb, hst1, -, c⟩ := (DeflateInitPublic.init_inv h h' s level version size hready
    hver e).1
  obtain ⟨hp, hhp⟩ := c.gzhead
  have hreg : DRegisteredHeader h' (some i) hp := ⟨b, st, ⟨⟨z1, ⟨i, rfl, hz1⟩, hb⟩, hst1⟩, hhp⟩
  rcases hk hp hreg with rfl | ⟨b0, st0, ⟨⟨z0, ⟨i0, ei, hz0⟩, hb0⟩, -⟩, -⟩
  · exact hreg
  · obtain ⟨i1, ei1, hz1'⟩ := hz
    cases ei; cases ei1
    rw [hz0] at hz1'; cases hz1'
    rw [hst] at hb0; cases hb0

/-! ## The goals -/

/-- `deflate_nonvacuous`, with the strategies (`strategyFacts`) and `dInitFresh`. -/
theorem deflate_nonvacuous : Goal.deflate_nonvacuous :=
  deflate_nonvacuous_of DeflatePublic.strategyFacts dInitFresh

/-- `compress2_z` is safe, given `DeflateProgress` (an obligation of the deflate side). -/
theorem compress2_z_safety_of_progress (N : DeflateProgress) : Goal.compress2_z_safety :=
  compress2_z_safety_of DeflatePublic.strategyFacts dInitFresh N

theorem compress2_safety_of_progress (N : DeflateProgress) : Goal.compress2_safety :=
  compress2_safety_of DeflatePublic.strategyFacts dInitFresh N

theorem compress_safety_of_progress (N : DeflateProgress) : Goal.compress_safety :=
  compress_safety_of DeflatePublic.strategyFacts dInitFresh N

theorem compress_z_safety_of_progress (N : DeflateProgress) : Goal.compress_z_safety :=
  compress_z_safety_of DeflatePublic.strategyFacts dInitFresh N

/-- `DeflateProgress` holds (`DeflateGz.deflate_progress`). -/
theorem deflateProgress : DeflateProgress := DeflateGz.deflate_progress

/-- **`compress2_z` is safe.** -/
theorem compress2_z_safety : Goal.compress2_z_safety := compress2_z_safety_of_progress deflateProgress

/-- **`compress2` is safe.** -/
theorem compress2_safety : Goal.compress2_safety := compress2_safety_of_progress deflateProgress

/-- **`compress` is safe.** -/
theorem compress_safety : Goal.compress_safety := compress_safety_of_progress deflateProgress

/-- **`compress_z` is safe.** -/
theorem compress_z_safety : Goal.compress_z_safety := compress_z_safety_of_progress deflateProgress

end ZlibNgF.Proof.Compress
