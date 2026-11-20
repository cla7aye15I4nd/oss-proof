import ZlibNgF.Proof.«gzread.c.readspec»
import ZlibNgF.Proof.«gzread.c.gets»

/-!
# `gz_fetch` on a read handle (`ZlibNgF`)

`gz_fetch` (`gzread.c:227-272`, patch 0016) loops over `gz_look`, `gz_load` (a transparent file) and `gz_decomp` (a
gzip stream) until there is output, an error, or the end of the input. The output asked for is at most
`room = GZ_OFF_MAX - x.pos` (when that is below `UINT_MAX`), so the output never takes `x.pos + x.have` past
`GZ_OFF_MAX` (`PosHave`).

**Termination.** A trip of the loop that does not end it goes from `LOOK` to `GZIP` or `COPY` (`gz_look`), or from
`GZIP` to `LOOK` with no output (the end of a gzip member). The measure is `2 * D + phase` with `D` the input still to
come (`rdLeft` of the descriptor plus `avail_in`): `gz_look` and `gz_decomp` do not raise `D`; `COPY` and a just reset
stream with input weigh 0, `LOOK` 1 (4 when `direct == -1`), any other `GZIP` state 2. A just reset stream with input
that ends a member without output consumed input (`InflateFreshIn`), so `D` dropped.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzDecomp

/-! ## `gz_fetch` in parts (copied from the translation) -/

open ZlibNg.Inflate in
/-- The body of the loop of `gz_fetch`. -/
def fetchBody (state : GzPtr) (strm : StreamPtr) (room : UInt32) (c : Ctl × Int32) : G (Ctl × Int32) := do
  let how ← rdG state (·.how)
  if how == LOOK then
    if (← gz_look state) == -1 then
      return (.ret, -1)
    if (← rdG state (·.how)) == LOOK then
      return (.ret, 0)
    return c
  else if how == ZlibNg.Gz.COPY then
    let (r, _) ← gz_load state (← (← ldGz state).out.get) (min ((← rdG state (·.size)) <<< 1) room) true
    if r == -1 then
      return (.ret, -1)
    let o ← (← ldGz state).out.get
    wrG state fun s => { s with next := .val o }
    return (.ret, 0)
  else if how == GZIP then
    let sz ← rdG state (·.size)
    lm (wrZ strm fun z => { z with avail_out := min (sz <<< 1) room })
    let o ← (← ldGz state).out.get
    lm (wrZ strm fun z => { z with next_out := o })
    if (← gz_decomp state) == -1 then
      return (.ret, -1)
    return c
  else
    gub "Z_UNREACHABLE() reached"

open ZlibNg.Inflate in
/-- The condition of the loop of `gz_fetch`. -/
def fetchCond (state : GzPtr) (strm : StreamPtr) (c : Ctl × Int32) : G (Bool × (Ctl × Int32)) := do
  if c.1 != .go then return (false, c)
  if (← rdG state (·.«have»)) != 0 then return (false, c)
  return ((← rdG state (·.eof)) == 0 || (← lm (rdZ strm (·.avail_in))) != 0, c)

/-- The loop of `gz_fetch` and what follows. -/
def fetchLoop (state : GzPtr) (strm : StreamPtr) (room : UInt32) : G Int32 := do
  let lp ← gdoWhile (fetchBody state strm room) (fetchCond state strm) (.go, 0)
  if lp.1 == .ret then
    return lp.2
  return 0

open ZlibNg.Inflate in
theorem gz_fetch_eq (state : GzPtr) : gz_fetch state = (do
    let strm ← strmOf state
    let pos ← rdG state (·.pos)
    if (decide (pos > 0) && decide ((4294967295 : UInt32).toUInt64 > (GZ_OFF_MAX - pos).toUInt64)) = true then
      if ((GZ_OFF_MAX - pos).toUInt64.toUInt32 == 0) = true then do
        let p ← gzLit "read position does not fit in z_off64_t"
        gz_error state Z_DATA_ERROR p
        pure (-1)
      else fetchLoop state strm (GZ_OFF_MAX - pos).toUInt64.toUInt32
    else fetchLoop state strm 4294967295) := by
  unfold gz_fetch fetchLoop fetchBody fetchCond; rfl

/-! ## What `gz_fetch` needs of `gz_look` -/

/-- What `gz_fetch` needs of `gz_look` beyond `LookPost`: the descriptor and the buffers kept; on `0`, the read measure
`rdLeft + avail_in` did not grow, a switch to `GZIP` comes with a just reset state and input in the buffer or from a
`direct == -1` request, and `gz_look` stays in `LOOK` only at the end of the input. -/
structure LookExtra : Prop where
  ext : ∀ (w : World) (h : Heap) (b : Nat) (s : GzState), GzInvR w h (some b) → w.gz h b = some s →
    s.«have» = 0 → s.how = LOOK →
    GSat w h (gz_look (some b)) (fun r W H => ∀ s', W.gz H b = some s' → s'.fd = s.fd ∧
      (s.size ≠ 0 → s'.size ≠ 0) ∧
      (r = 0 → (∀ z z', h.streams s.strm = some z → H.streams s.strm = some z' →
          rdLeft W.fs s.fd + z'.avail_in.toNat ≤ rdLeft w.fs s.fd + z.avail_in.toNat) ∧
        (s'.how = GZIP → HeadState H s' ∧ ((∀ z', H.streams s.strm = some z' → z'.avail_in ≠ 0) ∨ s.direct = -1)) ∧
        (s'.how = LOOK → AtEnd H s')))

/-! ## Steps that write only blocks of the file -/

/-- A frame with one write range in a library block is a frame with none. -/
theorem frame_drop {h h' : Heap} {S L G : List Nat} {bo oo n : Nat}
    (f : Frame h h' S L G [(.ref (.heap bo) oo, n)]) (hb : bo ∈ L) : Frame h h' S L G [] := by
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f
  refine ⟨s1, g1, i1, fun c hc hn data hd => ?_, n1, c1, r1, x1, a1, k1⟩
  obtain ⟨d2, f2, s2, q2⟩ := b1 c hc hn data hd
  refine ⟨d2, f2, s2, fun j hj _ => q2 j hj ?_⟩
  intro w hw off e
  simp only [List.mem_singleton] at hw
  subst hw
  cases e
  exact absurd hb hn

/-- A step whose only write range lies in a block of the file writes nothing outside the file. -/
theorem GStep.drop {w W : World} {h H : Heap} {b bo oo n : Nat} (g : GStep w h W H b [(.ref (.heap bo) oo, n)])
    (hb : bo ∈ GzOwned w h (some b)) : GStep w h W H b [] := by
  obtain ⟨⟨⟨f1, f2⟩, c, gz⟩, o, t⟩ := g
  exact ⟨⟨⟨frame_drop f1 hb, f2⟩, c, gz⟩, o, t⟩

/-! ## Arithmetic -/

theorem shl1_toNat (x : UInt32) (hx : x.toNat ≤ 2 ^ 30) : (x <<< 1).toNat = 2 * x.toNat := by
  rw [UInt32.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  have : (1 : UInt32).toNat % 32 = 1 := rfl
  rw [this]; omega

/-- The room of `gz_fetch` (patch 0016): `x.pos + room <= GZ_OFF_MAX`. -/
theorem room_ok (pos : Int64) (hlo : -GZ_OFF_MAX.toInt ≤ pos.toInt) (hhi : pos.toInt ≤ GZ_OFF_MAX.toInt) :
    ((decide (pos > 0) && decide ((4294967295 : UInt32).toUInt64 > (GZ_OFF_MAX - pos).toUInt64)) = true →
      pos.toInt + ((GZ_OFF_MAX - pos).toUInt64.toUInt32).toNat ≤ GZ_OFF_MAX.toInt) ∧
    (¬ (decide (pos > 0) && decide ((4294967295 : UInt32).toUInt64 > (GZ_OFF_MAX - pos).toUInt64)) = true →
      pos.toInt + (4294967295 : UInt32).toNat ≤ GZ_OFF_MAX.toInt) := by
  have hmx := gzmax
  have hsub : 0 < pos.toInt → (GZ_OFF_MAX - pos).toInt = GZ_OFF_MAX.toInt - pos.toInt := by
    intro hp
    rw [Int64.toInt_sub, Int.bmod_eq_of_le] <;> omega
  have hge : 0 < pos.toInt → (0 : Int64) ≤ GZ_OFF_MAX - pos := by
    intro hp; rw [Int64.le_iff_toInt_le, hsub hp]; simp; omega
  have hval : 0 < pos.toInt → (GZ_OFF_MAX - pos).toUInt64.toNat = (GZ_OFF_MAX.toInt - pos.toInt).toNat := by
    intro hp; rw [Int64.toNat_toUInt64_of_le (hge hp), ← Int64.toNat_toInt, hsub hp]
  have hpos : (pos > 0) ↔ 0 < pos.toInt := by
    rw [gt_iff_lt, Int64.lt_iff_toInt_lt]; simp
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨h1, h2⟩ := hc
    have hp := hpos.mp h1
    have h2' : (GZ_OFF_MAX - pos).toUInt64.toNat < 4294967295 := by
      have := UInt64.lt_iff_toNat_lt.mp h2; simpa using this
    have e32 : ((GZ_OFF_MAX - pos).toUInt64.toUInt32).toNat = (GZ_OFF_MAX.toInt - pos.toInt).toNat := by
      rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega), hval hp]
    rw [e32]; omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hc
    show pos.toInt + 4294967295 ≤ _
    by_cases hp : 0 < pos.toInt
    · have h2 := hc (hpos.mpr hp)
      have h2' : ¬ (GZ_OFF_MAX - pos).toUInt64.toNat < 4294967295 := by
        intro e; exact h2 (UInt64.lt_iff_toNat_lt.mpr (by simpa using e))
      rw [hval hp] at h2'; omega
    · omega

/-! ## The measure, the invariant and the exits of the loop -/

open Classical in
/-- The phase of the measure of `gz_fetch`: `COPY` 0, `LOOK` 1 (4 when `direct == -1`), a just reset `GZIP` stream
with input 0, any other `GZIP` state 2. -/
noncomputable def fph (H : Heap) (s : GzState) (ai : Nat) : Nat :=
  if s.how = ZlibNg.Gz.COPY then 0
  else if s.how = LOOK then (if s.direct = -1 then 4 else 1)
  else if InflFresh H s ∧ ai ≠ 0 then 0 else 2

/-- The measure of the loop of `gz_fetch`: twice the input still to come, plus the phase. -/
noncomputable def fmu (b : Nat) (fd : Int32) (i : Nat) (W : World) (H : Heap) : Nat :=
  match W.gz H b, H.streams i with
  | some s, some z => 2 * (rdLeft W.fs fd + z.avail_in.toNat) + fph H s z.avail_in.toNat
  | _, _ => 0

theorem fmu_of {b : Nat} {fd : Int32} {i : Nat} {W : World} {H : Heap} {s : GzState} {z : ZStream}
    (hs : W.gz H b = some s) (hz : H.streams i = some z) :
    fmu b fd i W H = 2 * (rdLeft W.fs fd + z.avail_in.toNat) + fph H s z.avail_in.toNat := by
  simp only [fmu, hs, hz]

theorem fph_le (H : Heap) (s : GzState) (ai : Nat) : fph H s ai ≤ 4 := by
  unfold fph; repeat (first | omega | split)

/-- The invariant of the loop of `gz_fetch` at the start of a trip: a read handle with no output, a step of the call. -/
def FInv (w : World) (h : Heap) (b : Nat) (s : GzState) (c : Ctl × Int32) (W : World) (H : Heap) : Prop :=
  c = (.go, 0) ∧ ∃ s1, W.gz H b = some s1 ∧ GzInvR W H (some b) ∧ s1.«have» = 0 ∧ GStep w h W H b [] ∧
    FsRd w.fs W.fs ∧ s1.pos = s.pos ∧ s1.skip = s.skip ∧ s1.fd = s.fd ∧ s1.strm = s.strm ∧
    (s.size ≠ 0 → s1.size ≠ 0)

/-- The exit of the loop of `gz_fetch`. -/
def FQ (w : World) (h : Heap) (b : Nat) (s : GzState) (c : Ctl × Int32) (W : World) (H : Heap) : Prop :=
  FetchPost w h b s c.2 W H ∧ (c.1 ≠ .ret → c.2 = 0)

theorem fetchPost_of {w : World} {h : Heap} {b : Nat} {s : GzState} {W : World} {H : Heap} {s1 : GzState} {r : Int32}
    (hr : r = -1 ∨ r = 0) (hm : GzMid W H b s1) (g : GStep w h W H b []) (hf : FsRd w.fs W.fs)
    (hp : s1.pos = s.pos) (hk : s1.skip = s.skip) (hsz : s.size ≠ 0 → s1.size ≠ 0)
    (he : r = 0 → s1.«have» ≠ 0 ∨ AtEnd H s1) : FetchPost w h b s r W H := by
  refine ⟨hr, g, hf, s1, hm, hp, hk, hsz, fun hk0 => ?_, he⟩
  obtain ⟨hs1, hv0, hout, hph⟩ := hm
  exact invR_restore hv0 hs1 hout (fun e => absurd (hk.trans hk0) e) hph

/-- A return of the loop body (`(.ret, r)`) ends the loop. -/
theorem fetch_ret {w : World} {h : Heap} {b : Nat} {s : GzState} {W : World} {H : Heap} {s1 : GzState} {r : Int32}
    {i : Nat} (M : World → Heap → Nat) (μ0 : Nat)
    (hr : r = -1 ∨ r = 0) (hm : GzMid W H b s1) (g : GStep w h W H b []) (hf : FsRd w.fs W.fs)
    (hp : s1.pos = s.pos) (hk : s1.skip = s.skip) (hsz : s.size ≠ 0 → s1.size ≠ 0)
    (he : r = 0 → s1.«have» ≠ 0 ∨ AtEnd H s1) :
    GSat W H (fetchCond (some b) (some i) (.ret, r)) (fun cs W2 H2 =>
      (cs.1 = true → FInv w h b s cs.2 W2 H2 ∧ M W2 H2 < μ0) ∧ (cs.1 = false → FQ w h b s cs.2 W2 H2)) := by
  unfold fetchCond
  refine GSat.ite (fun _ => GSat.pure ⟨fun e => absurd e (by simp), fun _ => ⟨fetchPost_of hr hm g hf hp hk hsz he,
    fun e => absurd rfl e⟩⟩) (fun hc => absurd rfl hc)

/-- An error return of the loop body from a read handle. -/
theorem fetch_err {w : World} {h : Heap} {b : Nat} {s : GzState} {W : World} {H : Heap} {s1 : GzState}
    {i : Nat} (M : World → Heap → Nat) (μ0 : Nat) (hv : GzInvR W H (some b)) (hs1 : W.gz H b = some s1)
    (g : GStep w h W H b []) (hf : FsRd w.fs W.fs)
    (hp : s1.pos = s.pos) (hk : s1.skip = s.skip) (hsz : s.size ≠ 0 → s1.size ≠ 0) :
    GSat W H (fetchCond (some b) (some i) (.ret, -1)) (fun cs W2 H2 =>
      (cs.1 = true → FInv w h b s cs.2 W2 H2 ∧ M W2 H2 < μ0) ∧ (cs.1 = false → FQ w h b s cs.2 W2 H2)) :=
  fetch_ret M μ0 (Or.inl rfl) (mid_of hv hs1) g hf hp hk hsz (fun e => absurd e (by decide))

/-- The loop body left `(.go, 0)`: the loop ends with output or at the end of the input, or goes on with a smaller
measure. -/
theorem fetch_cont {w : World} {h : Heap} {b : Nat} {s : GzState} {W : World} {H : Heap} {s1 : GzState} {z : ZStream}
    (M : World → Heap → Nat) (μ0 : Nat) (hm : GzMid W H b s1) (g : GStep w h W H b []) (hf : FsRd w.fs W.fs)
    (hp : s1.pos = s.pos) (hk : s1.skip = s.skip) (hfd : s1.fd = s.fd) (hst : s1.strm = s.strm)
    (hsz : s.size ≠ 0 → s1.size ≠ 0) (hz : H.streams s.strm = some z)
    (hdec : s1.«have» = 0 → (s1.eof = 0 ∨ z.avail_in ≠ 0) → M W H < μ0) :
    GSat W H (fetchCond (some b) (some s.strm) (.go, 0)) (fun cs W2 H2 =>
      (cs.1 = true → FInv w h b s cs.2 W2 H2 ∧ M W2 H2 < μ0) ∧ (cs.1 = false → FQ w h b s cs.2 W2 H2)) := by
  have hs1 := hm.1
  unfold fetchCond
  refine GSat.ite (fun hc => absurd hc (by decide)) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  apply GSat.ite
  · intro hh
    have hh' : s1.«have» ≠ 0 := by simpa using hh
    exact GSat.pure ⟨fun e => absurd e (by simp), fun _ =>
      ⟨fetchPost_of (Or.inr rfl) hm g hf hp hk hsz (fun _ => Or.inl hh'), fun _ => rfl⟩⟩
  · intro hh
    have hh' : s1.«have» = 0 := by simpa using hh
    refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz _, GSat.pure ⟨fun hc => ⟨⟨rfl, s1, hs1, ?_, hh', g, hf, hp, hk, hfd,
      hst, hsz⟩, hdec hh' ?_⟩, fun hc => ⟨fetchPost_of (Or.inr rfl) hm g hf hp hk hsz (fun _ => Or.inr ?_),
      fun _ => rfl⟩⟩⟩)
    · obtain ⟨-, hv0, hout, hph⟩ := hm
      exact invR_restore hv0 hs1 hout (fun _ => hh') hph
    · simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
      exact hc
    · simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq, ne_eq] at hc
      exact ⟨hc.1, z, by rw [hst]; exact hz, hc.2⟩

theorem fph_look {H : Heap} {s : GzState} {ai : Nat} (h : s.how = LOOK) :
    fph H s ai = if s.direct = -1 then 4 else 1 := by
  simp (config := {decide := true}) [fph, h]

theorem fph_copy {H : Heap} {s : GzState} {ai : Nat} (h : s.how = ZlibNg.Gz.COPY) : fph H s ai = 0 := by
  simp [fph, h]

theorem fph_fresh {H : Heap} {s : GzState} {ai : Nat} (h : s.how = GZIP) (hf : InflFresh H s) (ha : ai ≠ 0) :
    fph H s ai = 0 := by
  simp (config := {decide := true}) [fph, h, hf, ha]

theorem fph_gzip {H : Heap} {s : GzState} {ai : Nat} (h : s.how = GZIP) (hn : ¬ (InflFresh H s ∧ ai ≠ 0)) :
    fph H s ai = 2 := by
  simp (config := {decide := true}) [fph, h, hn]

theorem fph_gz_le {H : Heap} {s : GzState} {ai : Nat} (h : s.how = GZIP) : fph H s ai ≤ 2 := by
  by_cases hn : InflFresh H s ∧ ai ≠ 0
  · rw [fph_fresh h hn.1 hn.2]; omega
  · rw [fph_gzip h hn]; omega

/-! ## `gz_load` into `x.have`, with the reason the loop stopped -/

/-- `loadLoopX_spec` with the reason the loop stopped: a read that returned at most 0, or `len` bytes counted. -/
theorem loadLoopX_exit {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) {cb p : Nat}
    {a : Array UInt8} (ha : h.bytes cb = some a) (len : UInt32) (hp : p + len.toNat ≤ a.size) (hcb : b ≠ cb) :
    GSat { w with gzs := upd w.gzs b (some { s with «have» := 0 }) } h
      (gdoWhile (loadBodyG (some b) (.ref (.heap cb) p) len true) (loadCondG (some b) len true) ⟨0, 0, .go⟩)
      (fun lp W H => ∃ k : UInt32, k.toNat ≤ len.toNat ∧ (lp.ret ≤ 0 ∨ len.toNat ≤ k.toNat) ∧ ∃ fs', FsRd w.fs fs' ∧
        W = { w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k }) } ∧ HBuf h H cb p (p + len.toNat)) := by
  refine gsat_gdoWhile (fun (st : LoadLoop) W H => st.ctl = .go ∧ ∃ k : UInt32, k.toNat ≤ len.toNat ∧ ∃ fs', FsRd w.fs fs' ∧
        W = { w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k }) } ∧ HBuf h H cb p (p + len.toNat))
    (fun _ W _ => match W.gzs b with | some s' => len.toNat - s'.«have».toNat | none => 0) _ ?_
    ⟨rfl, 0, by simp, w.fs, FsRd.refl _, rfl, HBuf.refl _ _ _ _⟩ (by have := len.toNat_lt; simp [fuel]; omega)
  intro st W H ⟨hgo, k, hle, fs', hfs, hW, x⟩
  subst hW
  have hsW := gzX_upd hs x hcb fs' { s with «have» := k }
  obtain ⟨a1, ha1, hsz⟩ := x.size ha
  unfold loadBodyG getX setX
  simp only [ite_true]
  refine GSat.bind (GSat.of_eq (rdG_app' hsW _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hsW _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, addH ha1 k.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.of_eq (rdG_app' hsW _) ?_)
  have hn : (len - k).toUInt64.toNat = len.toNat - k.toNat := by
    rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hle)]
  have hlen := len.toNat_lt
  refine GSat.bind (GSat.mono (readG_spec ha1 s.fd (len - k).toUInt64 (by rw [hn]; omega)
    (by rw [hn]; omega)) fun r W1 H1 q => ?_)
  obtain ⟨rfl, hr, x1⟩ := q
  have x2 : HBuf h H1 cb p (p + len.toNat) := x.trans x1 (by omega) (by rw [hn]; omega)
  have hfs2 : FsRd w.fs (fs'.readCall s.fd (len - k).toUInt64).2.2 := hfs.trans (readCall_rd _ _ _)
  have hres := readCall_res fs' s.fd (len - k).toUInt64 (by rw [hn]; omega)
  rw [← hr, hn] at hres
  apply GSat.ite
  · intro hr0
    refine GSat.pure ?_
    unfold loadCondG
    exact GSat.pure ⟨fun e => absurd e (by simp), fun _ => ⟨k, hle, Or.inl hr0, _, hfs2, rfl, x2⟩⟩
  · intro hr0
    have h0 : (0 : Int64) ≤ r := by
      rw [Int64.le_iff_toInt_le] at hr0 ⊢; simp at hr0 ⊢; omega
    have hpos : 0 < r.toInt := by
      rw [Int64.le_iff_toInt_le] at hr0; simp at hr0; omega
    have hle2 : r.toInt ≤ (len.toNat - k.toNat : Nat) := by
      rcases hres with ⟨e, -⟩ | ⟨-, e, -⟩
      · rw [e] at hpos; simp at hpos
      · exact e
    have hk : r.toUInt64.toUInt32.toNat = r.toInt.toNat := by
      rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt]; omega
    have hsum : (k + r.toUInt64.toUInt32).toNat = k.toNat + r.toInt.toNat := by
      rw [UInt32.toNat_add, hk]; omega
    have hsW1 := gzX_upd hs x2 hcb (fs'.readCall s.fd (len - k).toUInt64).2.2 { s with «have» := k }
    refine GSat.bind (GSat.of_eq (rdG_app' hsW1 _) ?_)
    refine GSat.bind (GSat.bind (GSat.of_eq (wrG_app hsW1 _) (GSat.pure ?_)))
    refine GSat.pure ?_
    simp only [InflateInv.upd_upd]
    have hsW2 := gzX_upd hs x2 hcb (fs'.readCall s.fd (len - k).toUInt64).2.2
      { s with «have» := k + r.toUInt64.toUInt32 }
    unfold loadCondG getX
    simp only [ite_true]
    apply GSat.ite
    · intro hc
      exact absurd hc (by simp [hgo])
    · intro _
      refine GSat.bind (GSat.of_eq (rdG_app' hsW2 _) ?_)
      refine GSat.pure ⟨fun _ => ⟨⟨hgo, _, by omega, _, hfs2, rfl, x2⟩, ?_⟩,
        fun hc => ⟨_, by omega, Or.inr ?_, _, hfs2, rfl, x2⟩⟩
      · simp only [upd_same]
        omega
      · simp only [decide_eq_false_iff_not] at hc
        have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hc)
        exact this

/-- **`gz_load(state, buf, len, &state->x.have)`** (`gz_load_spec`), with the end of the input: on `0` with fewer than
`len` bytes, `eof` is set. -/
theorem gz_load_x {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) {cb p : Nat} {a : Array UInt8} (ha : h.bytes cb = some a)
    (len : UInt32) (hp : p + len.toNat ≤ a.size) (hcb : b ≠ cb) (hpath : cb ∉ blkOf s.path) (hst : cb ∉ stBlk h s)
    (hown : cb ∈ GzOwned w h (some b)) :
    GSat w h (gz_load (some b) (.ref (.heap cb) p) len true) (fun r W H =>
      (r.1 = -1 ∧ ∃ s', W.gz H b = some s' ∧ ErrOf s Z_ERRNO s' ∧ GzInvR W H (some b) ∧
        GStep w h W H b [] ∧ FsRd w.fs W.fs) ∨
      (r.1 = 0 ∧ ∃ k : UInt32, k.toNat ≤ len.toNat ∧ ∃ (fs' : Fs) (e : Int32), FsRd w.fs fs' ∧
        (k.toNat < len.toNat → e = 1) ∧
        W = { w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k, eof := e }) } ∧
        HBuf h H cb p (p + len.toNat))) := by
  rw [gz_load_eq]
  unfold setX
  simp only [ite_true]
  refine GSat.bind (GSat.bind (GSat.of_eq (wrG_app hs _) (GSat.pure ?_)))
  refine GSat.bind (GSat.mono (loadLoopX_exit hs ha len hp hcb) fun lp W1 H1 q => ?_)
  obtain ⟨k, hk, hex, fs', hfs, rfl, x⟩ := q
  have hs1 := gzX_upd hs x hcb fs' { s with «have» := k }
  unfold loadTail
  apply GSat.ite
  · intro _
    obtain ⟨pm, am, ez, hcs, hmk⟩ := zstrerror_spec { w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k }) } H1
    refine GSat.bind (GSat.of_eq ez ?_)
    have hinv1 : GzInvR { w with fs := fs' } H1 (some b) := invR_hbuf hv hs x hcb hpath hst hfs
    have hinv2 := invR_lit hinv1 am
    have ew : ({ ({ w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k }) } : World) with
        gzs := upd (upd w.gzs b (some { s with «have» := k })) b (some { ({ s with «have» := k } : GzState) with «have» := 0 }) } : World) =
        { w with fs := fs' } := by
      have es : ({ ({ s with «have» := k } : GzState) with «have» := 0 } : GzState) = s := have0_self h0
      rw [InflateInv.upd_upd, es, DeflateReset.upd_self w.gzs b s (gzs_of hs)]
    rw [← ew] at hinv2
    refine GSat.bind (GSat.mono (gz_error_inv0 (w := { w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k }) })
      (s := { s with «have» := k }) (h := { H1 with consts := upd H1.consts H1.consts.arr.size (some am) }) hs1 hinv2 Z_ERRNO (by decide) pm (Or.inr hcs) hmk)
      fun _ W H q => ?_)
    obtain ⟨s', hsW, herr, hvW, -, hfsW, hstep⟩ := q
    refine GSat.pure (Or.inl ⟨rfl, s', hsW, ?_, hvW, ?_, by rw [hfsW]; exact hfs⟩)
    · have es : ({ ({ s with «have» := k } : GzState) with «have» := 0 } : GzState) = s := have0_self h0
      rw [es] at herr; exact herr
    · have g1 := gstep_hbuf hs x hcb hown fs' { s with «have» := k } rfl rfl rfl rfl
      have g2 := gstep_lit hs1 am
      exact (g1.trans g2 ⟨s, hs⟩ ⟨_, hs1⟩).trans hstep ⟨s, hs⟩ ⟨_, hs1⟩
  · intro hneg
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.of_eq (wrG_app hs1 _) (GSat.pure ?_))
      refine Or.inr ⟨rfl, k, hk, fs', 1, hfs, fun _ => rfl, ?_, x⟩
      simp only [InflateInv.upd_upd]
    · intro hn0
      refine GSat.pure (Or.inr ⟨rfl, k, hk, fs', s.eof, hfs, fun hlt => ?_, rfl, x⟩)
      exfalso
      rcases hex with hle | hle
      · have a1 : lp.ret.toInt ≤ 0 := by have := Int64.le_iff_toInt_le.mp hle; simpa using this
        have a2 : ¬ lp.ret.toInt < 0 := fun e => hneg (Int64.lt_iff_toInt_lt.mpr (by simpa using e))
        have a3 : lp.ret ≠ 0 := by simpa using hn0
        exact a3 (Int64.toInt_inj.mp (by simp; omega))
      · omega

/-! ## One trip of the loop -/

/-- The stream of a mid-call state. -/
theorem mid_strm {W : World} {H : Heap} {b : Nat} {s : GzState} (hm : GzMid W H b s) :
    ∃ z, H.streams s.strm = some z := by
  obtain ⟨hs, hv0, -, -⟩ := hm
  obtain ⟨sh, -⟩ := inv_of (gz_upd_same hs _) hv0.1
  exact sh.strm

/-- The fields of `GzRead` of a mid-call state, `x.have` cleared. -/
theorem mid_read {W : World} {H : Heap} {b : Nat} {s : GzState} (hm : GzMid W H b s) :
    GzRead H { s with «have» := 0 } := by
  obtain ⟨hs, hv0, -, -⟩ := hm
  obtain ⟨sh, -⟩ := inv_of (gz_upd_same hs _) hv0.1
  exact sh.read (modeOf (gz_upd_same hs _) hv0.2.1)

/-- **One trip of the loop of `gz_fetch`** and its condition. -/
theorem fetchBody_spec (LX : LookExtra) {w : World} {h : Heap} {b : Nat} {s : GzState} (hs0 : w.gz h b = some s)
    {room : UInt32} (hroom : room ≠ 0) (hpr : s.pos.toInt + room.toNat ≤ GZ_OFF_MAX.toInt)
    {c : Ctl × Int32} {W : World} {H : Heap} (hI : FInv w h b s c W H) :
    GSat W H (fetchBody (some b) (some s.strm) room c) (fun c1 W1 H1 => GSat W1 H1 (fetchCond (some b) (some s.strm) c1)
      (fun cs W2 H2 => (cs.1 = true → FInv w h b s cs.2 W2 H2 ∧ fmu b s.fd s.strm W2 H2 < fmu b s.fd s.strm W H) ∧
        (cs.1 = false → FQ w h b s cs.2 W2 H2))) := by
  obtain ⟨rfl, s1, hs1, hv, h0, g, hf, hp, hk, hfd, hst, hsz⟩ := hI
  obtain ⟨sh, hn⟩ := inv_of hs1 hv.1
  have hr := modeOf hs1 hv.2.1
  have R := sh.read hr
  obtain ⟨z, hz⟩ := sh.strm
  rw [hst] at hz
  have hμ := fmu_of (fd := s.fd) hs1 hz
  unfold fetchBody
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  apply GSat.ite
  · intro hl
    have hlook : s1.how = LOOK := by simpa using hl
    -- `LOOK`: `gz_look`
    refine GSat.bind (GSat.mono (GSat.and (gz_look_spec hv hs1 h0 hlook) (LX.ext W H b s1 hv hs1 h0 hlook))
      fun r W1 H1 q => ?_)
    obtain ⟨⟨hr1, g1, hf1, s', hs', hp', hk', -, -, hv0, hout, hph⟩, X⟩ := q
    obtain ⟨hfd', hsz', X0⟩ := X s' hs'
    have hm : GzMid W1 H1 b s' := ⟨hs', hv0, hout, hph⟩
    have g' : GStep w h W1 H1 b [] := g.trans g1 ⟨s, hs0⟩ ⟨s1, hs1⟩
    have hf' := hf.trans hf1
    have hst' : s'.strm = s.strm := (g1.strm s1 s' hs1 hs').trans hst
    apply GSat.ite
    · intro _
      exact GSat.pure (fetch_ret _ _ (Or.inl rfl) hm g' hf' (hp'.trans hp) (hk'.trans hk) (fun e => hsz' (hsz e))
        (fun e => absurd e (by decide)))
    · intro e
      have hr0 : r = 0 := hr1.resolve_left (by simpa using e)
      obtain ⟨hrd, hgz, hat⟩ := X0 hr0
      refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
      apply GSat.ite
      · intro hl'
        exact GSat.pure (fetch_ret _ _ (Or.inr rfl) hm g' hf' (hp'.trans hp) (hk'.trans hk) (fun e => hsz' (hsz e))
          (fun _ => Or.inr (hat (by simpa using hl'))))
      · intro hl'
        have hl'' : s'.how ≠ LOOK := by simpa using hl'
        obtain ⟨z', hz'⟩ := mid_strm hm
        rw [hst'] at hz'
        refine GSat.pure (fetch_cont _ _ hm g' hf' (hp'.trans hp) (hk'.trans hk) (hfd'.trans hfd) hst'
          (fun e => hsz' (hsz e)) hz' (fun _ _ => ?_))
        rw [hμ, fmu_of hs' hz', fph_look hlook]
        have hz1 : H.streams s1.strm = some z := by rw [hst]; exact hz
        have hz1' : H1.streams s1.strm = some z' := by rw [hst]; exact hz'
        have hd := hrd z z' hz1 hz1'
        rw [hfd] at hd
        have R' := mid_read hm
        rcases R'.how with e1 | e1 | e1
        · exact absurd e1 hl''
        · have e1' : s'.how = ZlibNg.Gz.COPY := e1
          rw [fph_copy e1']; split <;> omega
        · have e1' : s'.how = GZIP := e1
          obtain ⟨hhs, hx⟩ := hgz e1'
          by_cases ha : z'.avail_in.toNat = 0
          · have hd1 : s1.direct = -1 := by
              rcases hx with hx | hx
              · exact absurd (UInt32.toNat_inj.mp (by rw [ha]; rfl)) (hx z' hz1')
              · exact hx
            have := fph_gz_le (H := H1) (ai := z'.avail_in.toNat) e1'
            split
            · omega
            · next hne => exact absurd hd1 hne
          · rw [fph_fresh e1' hhs ha]; split <;> omega
  · intro hl
    apply GSat.ite
    · intro hc
      have hcopy : s1.how = ZlibNg.Gz.COPY := by simpa using hc
      have hsz1 : s1.size ≠ 0 := fun e => by have := R.look e; rw [hcopy] at this; exact absurd this (by decide)
      obtain ⟨c, base, z0, hB, -, -, -, -, -⟩ := R.bufs hsz1
      obtain ⟨hcb, hpath, hstb, hown⟩ := buf_facts hs1 hn hsz1 hB
      obtain ⟨d, hd, hds⟩ := hB.fits
      have hin' : inSize s1 = s1.want.toNat := by simp [inSize, hr, read_ne_write]
      have hout' : outSize s1 = 2 * s1.want.toNat := by simp [outSize, hr, read_ne_write]
      have hwl := sh.want_lo
      have hwh := sh.want_hi
      have hO : s1.out = .val (.ref (.heap c) (base + inSize s1)) := hB.out (by rw [hout']; omega)
      have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
      have h2s := shl1_toNat s1.size (by omega)
      let len : UInt32 := min (s1.size <<< 1) room
      have hlen : len.toNat = min (2 * s1.size.toNat) room.toNat := by
        show (min (s1.size <<< 1) room).toNat = _
        rw [← h2s]; exact u32_min_toNat _ _
      have hroom' : room.toNat ≠ 0 := fun e => hroom (UInt32.toNat_inj.mp (by simpa using e))
      refine GSat.bind (GSat.of_eq (ldGz_app hs1) ?_)
      refine GSat.bind (GSat.lm ⟨_, H, (by rw [hO]; rfl), ?_⟩)
      refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
      refine GSat.bind (GSat.mono (gz_load_x hv hs1 h0 hd len (p := base + inSize s1) (by rw [hlen]; omega) hcb hpath hstb
        hown) fun r W1 H1 q => ?_)
      obtain ⟨r1, r2⟩ := r
      dsimp only
      rcases q with ⟨hr1, s', hs', herr, hv1, gL, hfL⟩ | ⟨hr1, k, hk1, fs', e, hfs, hke, rfl, x⟩
      · simp only at hr1
        subst hr1
        refine GSat.ite (fun _ => GSat.pure ?_) (fun hc' => absurd rfl hc')
        have es := errOf_shape herr h0
        exact fetch_err _ _ hv1 hs' (g.trans gL ⟨s, hs0⟩ ⟨s1, hs1⟩) (hf.trans hfL) (by rw [es]; exact hp)
          (by rw [es]; exact hk) (fun e => by rw [es]; exact hsz1)
      · simp only at hr1
        subst hr1
        refine GSat.ite (fun hc' => absurd hc' (by decide)) (fun _ => ?_)
        let s2 : GzState := { s1 with «have» := k, eof := e }
        have hs2 := gzX_upd hs1 x hcb fs' s2
        refine GSat.bind (GSat.of_eq (ldGz_app hs2) ?_)
        refine GSat.bind (GSat.lm ⟨_, H1, (by show Ival.get s1.out H1 = _; rw [hO]; rfl), ?_⟩)
        refine GSat.bind (GSat.of_eq (wrG_app hs2 _) (GSat.pure ?_))
        simp only [InflateInv.upd_upd]
        let o : BPtr := .ref (.heap c) (base + inSize s1)
        let s3 : GzState := { s1 with «have» := k, eof := e, next := .val o }
        have hs3 : ({ W with fs := fs', gzs := upd W.gzs b (some s3) } : World).gz H1 b = some s3 :=
          gzX_upd hs1 x hcb fs' s3
        have hstrH1 : H1.streams = H.streams := by obtain ⟨t, rfl, -⟩ := x; rfl
        have hvA : GzInvR { W with fs := fs' } H1 (some b) := invR_hbuf hv hs1 x hcb hpath hstb hfs
        have hsA : ({ W with fs := fs' } : World).gz H1 b = some s1 := by rw [x.gz hcb]; exact hs1
        obtain ⟨hvC, -⟩ := invR_look hvA hsA (.val o) ZlibNg.Gz.COPY (Or.inr (Or.inl rfl)) s1.direct e
          (fun e' => absurd e' hsz1) (fun e' => absurd e' (by decide)) (fun e' => absurd e' (by decide))
          (fun _ z2 hz2 => R.copy_in hcopy z2 (by rw [← hstrH1]; exact hz2))
        have es : ({ s1 with «have» := 0, next := .val o, how := ZlibNg.Gz.COPY, direct := s1.direct, eof := e } :
            GzState) = { s3 with «have» := 0 } := by
          cases s1; simp only at hcopy h0; subst hcopy; subst h0; rfl
        rw [es] at hvC
        have hkl : k.toNat ≤ 2 * s1.want.toNat ∧ k.toNat ≤ room.toNat := by rw [hlen] at hk1; omega
        have hm : GzMid { W with fs := fs', gzs := upd W.gzs b (some s3) } H1 b s3 := by
          refine ⟨hs3, ?_, Or.inr ⟨hsz1, fun c' base' hB' => ?_⟩, ?_, fun e' => absurd (hcopy.symm.trans e') (by decide)⟩
          · simp only [InflateInv.upd_upd]; exact hvC
          · have e1 := hB'.buffers; rw [show s3.buffers = s1.buffers from rfl, hB.buffers] at e1; cases e1
            have hi3 : inSize s3 = inSize s1 := rfl
            have ho3 : outSize s3 = outSize s1 := rfl
            refine ⟨_, rfl, inSize s1, rfl, by rw [hi3]; exact Nat.le_refl _, ?_⟩
            rw [hi3, ho3, hout']; show inSize s1 + k.toNat ≤ _; omega
          · show s1.pos.toInt + (k.toNat : Int) ≤ _; rw [hp]; omega
        have g3 : GStep W H { W with fs := fs', gzs := upd W.gzs b (some s3) } H1 b [] :=
          gstep_hbuf hs1 x hcb hown fs' s3 rfl rfl rfl rfl
        refine fetch_ret _ _ (Or.inr rfl) hm (g.trans g3 ⟨s, hs0⟩ ⟨s1, hs1⟩) (hf.trans hfs) hp hk
          (fun _ => hsz1) (fun _ => ?_)
        by_cases hk0 : k.toNat = 0
        · right
          have he1 := hke (by rw [hlen]; omega)
          refine ⟨by show e ≠ 0; rw [he1]; decide, z, by rw [hstrH1]; show H.streams s1.strm = _; rw [hst]; exact hz, ?_⟩
          exact R.copy_in hcopy z (by rw [hst]; exact hz)
        · left; intro e0; exact hk0 (by show k.toNat = 0; rw [show k = 0 from e0]; rfl)
    · intro hc
      apply GSat.ite
      · intro hg
        have hgz : s1.how = GZIP := by simpa using hg
        have hsz1 : s1.size ≠ 0 := fun e => by have := R.look e; rw [hgz] at this; exact absurd this (by decide)
        obtain ⟨c, base, z0, hB, -, hz0, -, hai, -, -⟩ := R.bufs hsz1
        rw [hst, hz] at hz0; cases hz0
        obtain ⟨hcb, hpath, hstb, hown⟩ := buf_facts hs1 hn hsz1 hB
        obtain ⟨d, hd, hds⟩ := hB.fits
        have hout' : outSize s1 = 2 * s1.want.toNat := by simp [outSize, hr, read_ne_write]
        have hwl := sh.want_lo
        have hwh := sh.want_hi
        have hO : s1.out = .val (.ref (.heap c) (base + inSize s1)) := hB.out (by rw [hout']; omega)
        have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
        have h2s := shl1_toNat s1.size (by omega)
        have hroom' : room.toNat ≠ 0 := fun e => hroom (UInt32.toNat_inj.mp (by simpa using e))
        let ao : UInt32 := min (s1.size <<< 1) room
        have hao : ao.toNat = min (2 * s1.size.toNat) room.toNat := by
          show (min (s1.size <<< 1) room).toNat = _
          rw [← h2s]; exact u32_min_toNat _ _
        let o : BPtr := .ref (.heap c) (base + inSize s1)
        let z1 : ZStream := { z with avail_out := ao }
        let z2 : ZStream := { z with avail_out := ao, next_out := o }
        let H3 : Heap := { H with streams := upd H.streams s.strm (some z2) }
        refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
        refine GSat.bind (GSat.lm ⟨(), { H with streams := upd H.streams s.strm (some z1) }, wrZ_app hz _, ?_⟩)
        refine GSat.bind (GSat.of_eq (ldGz_app (show W.gz { H with streams := upd H.streams s.strm (some z1) } b = some s1
          from hs1)) ?_)
        refine GSat.bind (GSat.lm ⟨_, _, (by show Ival.get s1.out _ = _; rw [hO]; rfl), ?_⟩)
        refine GSat.bind (GSat.lm ⟨(), H3, (by rw [wrZ_app (z := z1) (by simp)]; simp [InflateInv.upd_upd, z1, z2, H3, o]),
          ?_⟩)
        have hz3 : H3.streams s1.strm = some z2 := by rw [hst]; simp [H3]
        have hz' : H.streams s1.strm = some z := by rw [hst]; exact hz
        have hv3 : GzInvR W H3 (some b) := by
          have := invR_strm (z' := z2) hv hs1 hsz1 hz' rfl (fun c' base' hB' => by
            have e1 := hB'.buffers; rw [hB.buffers] at e1; cases e1; exact hai) (fun e => absurd (hgz.symm.trans e) (by decide))
          rw [hst] at this; exact this
        have hs3 : W.gz H3 b = some s1 := hs1
        have hB3 : GzBufs H3 s1 c base := ⟨hB.size, hB.buffers, hB.inp, hB.out, ⟨d, hd, hds⟩, hB.hdr⟩
        have hao0 : z2.avail_out ≠ 0 := by
          intro e; have := congrArg UInt32.toNat e; rw [show z2.avail_out = ao from rfl, hao] at this; simp at this; omega
        have ht : OutTgt W H3 b s1 c (base + inSize s1) z2.avail_out.toNat :=
          Or.inl ⟨c, base, hB3, rfl, Nat.le_refl _, by
            rw [show z2.avail_out = ao from rfl, hao, hout']; omega⟩
        have g3 : GStep W H W H3 b [] := by
          have := gstep_strm hs1 z2 hz' rfl; rw [hst] at this; exact this
        have hownc : c ∈ GzOwned W H3 (some b) := owned_buf hs3 hB.buffers
        refine GSat.bind (GSat.mono (gz_decomp_spec hv3 hs3 h0 hsz1 hgz hz3 hao0 rfl ht) fun r W1 H1 q => ?_)
        obtain ⟨hr1, gD, fD, s', hs', hv0, hshape, herr, hok⟩ := q
        have gD' : GStep w h W1 H1 b [] :=
          (g.trans g3 ⟨s, hs0⟩ ⟨s1, hs1⟩).trans (gD.drop hownc) ⟨s, hs0⟩ ⟨s1, hs3⟩
        have hf' : FsRd w.fs W1.fs := hf.trans fD
        have hp' : s'.pos = s.pos := by rw [hshape]; exact hp
        have hk' : s'.skip = s.skip := by rw [hshape]; exact hk
        have hsz' : s'.size ≠ 0 := by rw [hshape]; exact hsz1
        apply GSat.ite
        · intro e
          have he : r = -1 := by simpa using e
          obtain ⟨h0', -, -⟩ := herr he
          have hv1 : GzInvR W1 H1 (some b) := by
            rw [have0_self h0', DeflateReset.upd_self W1.gzs b s' (gzs_of hs')] at hv0; exact hv0
          exact GSat.pure (fetch_err _ _ hv1 hs' gD' hf' hp' hk' (fun _ => hsz'))
        · intro e
          have hr0 : r = 0 := hr1.resolve_left (by simpa using e)
          obtain ⟨z', hz1', hle, hhv, hnx, ht', hdmu, hhow', hfresh, hsame⟩ := hok hr0
          have hst' : s'.strm = s.strm := by rw [hshape]; exact hst
          have hfd' : s'.fd = s.fd := by rw [hshape]; exact hfd
          have hdir : s1.direct = 0 := R.gzip_direct hgz
          have hzs : H1.streams s.strm = some z' := by rw [← hst]; exact hz1'
          have hhvle : s'.«have».toNat ≤ ao.toNat := by rw [hhv]; exact Nat.sub_le _ _
          have hm : GzMid W1 H1 b s' := by
            refine ⟨hs', hv0, Or.inr ⟨hsz', fun c' base' hB' => ?_⟩, ?_, fun _ e' => absurd (by rw [hshape]; exact hdir) e'⟩
            · have e1 := hB'.buffers; rw [show s'.buffers = s1.buffers by rw [hshape], hB.buffers] at e1; cases e1
              have hi : inSize s' = inSize s1 := by rw [hshape]; rfl
              have ho : outSize s' = outSize s1 := by rw [hshape]; rfl
              refine ⟨_, hnx, inSize s1, rfl, by rw [hi]; exact Nat.le_refl _, ?_⟩
              rw [hi, ho, hout']; rw [hao] at hhvle; omega
            · show s'.pos.toInt + (s'.«have».toNat : Int) ≤ _
              rw [hp']; rw [hao] at hhvle; omega
          refine GSat.pure (fetch_cont _ _ hm gD' hf' hp' hk' hfd' hst' (fun _ => hsz') hzs (fun hh hc => ?_))
          have hl : s'.how = LOOK := by
            rcases hhow' with e1 | e1
            · exact e1
            · rcases hsame e1 with e2 | ⟨e2, e3⟩
              · exact absurd hh e2
              · rcases hc with e4 | e4
                · exact absurd e4 e2
                · exact absurd e3 e4
          have hao' : z'.avail_out.toNat = ao.toNat := by
            have : s'.«have».toNat = 0 := by rw [hh]; rfl
            rw [hhv] at this; show _ = z2.avail_out.toNat; omega
          have hd1 := dmu_of (s := s1) (W := W1) hz1'
          have hd0 := dmu_of (s := s1) (W := W) hz3
          rw [hμ, fmu_of hs' hzs, fph_look hl, show s'.direct = s1.direct by rw [hshape], hdir, ← hfd]
          rw [hd1, hd0] at hdmu
          have hai2 : z2.avail_in = z.avail_in := rfl
          rw [hai2, show z2.avail_out = ao from rfl, hao'] at hdmu
          by_cases hfr : InflFresh H s1 ∧ z.avail_in.toNat ≠ 0
          · have hf3 : InflFresh H3 s1 := by
              obtain ⟨z7, sb7, st7, h7, h8, h9, h10⟩ := hfr.1
              rw [hz'] at h7; cases h7
              exact ⟨z2, sb7, st7, hz3, h8, h9, h10⟩
            have hlt := hfresh hl inflateFresh (fun e => hfr.2 (by rw [show z2.avail_in = z.avail_in from rfl] at e; rw [e]; rfl)) hf3
            rw [hd1, hd0, hai2, show z2.avail_out = ao from rfl, hao'] at hlt
            rw [fph_fresh hgz hfr.1 hfr.2]
            have : ¬ ((0 : Int32) = -1) := by decide
            simp only [this, ↓reduceIte]; omega
          · rw [fph_gzip hgz hfr]
            have : ¬ ((0 : Int32) = -1) := by decide
            simp only [this, ↓reduceIte]; omega
      · intro hg
        exfalso
        rcases R.how with e | e | e
        · exact hl (by simp [e])
        · exact hc (by simp [e])
        · exact hg (by simp [e])

/-! ## `gz_fetch` -/

/-- The loop of `gz_fetch` and its end, for a room that is not 0 and fits above `x.pos`. -/
theorem fetchLoop_spec (LX : LookExtra) {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) {room : UInt32} (hroom : room ≠ 0)
    (hpr : s.pos.toInt + room.toNat ≤ GZ_OFF_MAX.toInt) :
    GSat w h (fetchLoop (some b) (some s.strm) room) (FetchPost w h b s) := by
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨z, hz⟩ := sh.strm
  have hI : FInv w h b s (.go, 0) w h :=
    ⟨rfl, s, hs, hv, h0, GStep.refl _ _ _ _, FsRd.refl _, rfl, rfl, rfl, rfl, id⟩
  have hfuel : fmu b s.fd s.strm w h < fuel := by
    rw [fmu_of hs hz]
    have := rdLeft_lt hv.2.2 s.fd
    have := z.avail_in.toNat_lt
    have := fph_le h s z.avail_in.toNat
    simp [fuel]; omega
  unfold fetchLoop
  refine GSat.bind (GSat.mono (gsat_gdoWhile (FInv w h b s) (fun _ W H => fmu b s.fd s.strm W H) (FQ w h b s)
    (fun _ _ _ hI' => fetchBody_spec LX hs hroom hpr hI') hI hfuel) fun lp W H q => ?_)
  obtain ⟨hpost, hgo⟩ := q
  apply GSat.ite
  · intro _; exact GSat.pure hpost
  · intro hne
    have e := hgo (fun e => hne (by rw [e]; rfl))
    rw [e] at hpost
    exact GSat.pure hpost

theorem lit_readpos : gzLits.findIdx? (· == "read position does not fit in z_off64_t") = some 14 := by
  simp [gzLits, List.findIdx?_cons]

/-- **`gz_fetch`**, given what it needs of `gz_look` (`LookExtra`). -/
theorem gz_fetch_spec_of (LX : LookExtra) : GzFetchSpec := by
  intro w h b s hv hs h0
  have P := (inv_of hs hv.1).1.pos
  obtain ⟨hA, hB⟩ := room_ok s.pos P.3 (by have := P.1; have := P.2; omega)
  rw [gz_fetch_eq]
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hc
    have hpr := hA hc
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.mono (errlit_strm hv hs ZlibNg.Inflate.Z_DATA_ERROR _ 14 lit_readpos (by decide))
        fun p W2 H2 q => GSat.bind (GSat.mono q fun _ W3 H3 q3 => ?_))
      obtain ⟨s2, hs2, herr, hv2, hfs2, g2, -⟩ := q3
      have es := errOf_shape herr h0
      refine GSat.pure (fetchPost_of (Or.inl rfl) (mid_of hv2 hs2) g2 (by rw [hfs2]; exact FsRd.refl _)
        (by rw [es]) (by rw [es]) (fun e => by rw [es]; exact e) (fun e => absurd e (by decide)))
    · intro hz0
      exact fetchLoop_spec LX hv hs h0 (fun e => hz0 (by rw [e]; rfl)) hpr
  · intro hc
    exact fetchLoop_spec LX hv hs h0 (by decide) (hB hc)

end ZlibNgF.Proof.GzMode
