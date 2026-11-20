import ZlibNgF.Proof.«gzread.c.init»
import ZlibNgF.Proof.«inflate.c.reset»
import ZlibNgF.Proof.«gzlib.c.seek64»

/-!
# `gz_look` on a read handle (`ZlibNgF`)

`gz_look` runs with `x.have == 0` (every caller checks it). It makes the buffers and the inflate state when the handle
has none (`gz_read_init`), resets the inflate state for a gzip stream (`inflateReset`), fills the input buffer when it
holds fewer than two bytes (`gz_avail`), reads the two magic bytes inside the `in` buffer, and otherwise copies the
input to the `out` buffer for a transparent read (`memcpy` between the two disjoint parts of the buffer block).

After the call `x.have` may be the number of bytes copied while a skip is pending, which `GzRead.skip_have` does not
allow between calls: the post-condition is the invariant of the world with `x.have` cleared, and the bytes `x.have`
from `x.next` inside `out`. The callers consume `min(x.have, skip)` before they return.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-! ## A new stream record and inflate state on a read handle -/

/-- A read handle with buffers stays one when its stream record and the inflate state of its block get new values
(`setZS`) that keep the inflate invariant, the state block, the input inside `in`, and no registered header. -/
theorem invR_setZS {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (hsz : s.size ≠ 0) {z z' : ZStream} {sb : Nat} {st' : InflateState}
    (hz : h.streams s.strm = some z) (hzs : z.state = some sb) (hz's : z'.state = some sb)
    (hinv : InflateInv.Inv (InflateInv.setZS h s.strm z' sb st') (some s.strm)) (hhd : st'.head = .val none)
    (hin : ∀ c base, GzBufs h s c base → z'.avail_in = 0 ∨ Inside c base 0 (inSize s) z'.next_in z'.avail_in.toNat)
    (hmsg : z'.msg = .null ∨ ∃ k, z'.msg = .ref (.str k) 0 ∧ k < strTable.size) :
    GzInvR w (InflateInv.setZS h s.strm z' sb st') (some b) ∧ GStep w h w (InflateInv.setZS h s.strm z' sb st') b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  let H := InflateInv.setZS h s.strm z' sb st'
  have hsH : w.gz H b = some s := hs
  have hzH : H.streams s.strm = some z' := by simp [H, InflateInv.setZS]
  have hst : stBlk H s = stBlk h s := by simp [stBlk, hzH, hz, hzs, hz's]
  have hown : ownL H b s = ownL h b s := by simp only [ownL, hst]
  have shH : GzShape H s := by
    refine ⟨sh.mode, sh.path, ⟨z', hzH⟩, sh.want_lo, sh.want_hi, sh.size, sh.pos, ⟨sh.msg.1, sh.msg.2⟩,
      fun _ => ⟨R.how, fun _ => ?_, R.nobuf, R.skip_have, fun e => absurd e hsz⟩,
      fun e => absurd (hr.symm.trans e) read_ne_write, fun e => absurd e hsz⟩
    obtain ⟨c, base, z0, hB, -, hz0, hhv, -, -⟩ := R.bufs hsz
    refine ⟨c, base, z', ⟨hB.size, hB.buffers, hB.inp, hB.out, hB.fits, hB.hdr⟩, hinv, hzH, hhv, hin c base hB, fun hp hrg => ?_, hmsg⟩
    obtain ⟨sb', st1, ⟨z1, ⟨i', e', hz1⟩, hsb1⟩, hst1, hhd1⟩ := hrg
    cases e'
    change H.streams s.strm = some z1 at hz1
    rw [hzH] at hz1; cases hz1
    rw [hz's] at hsb1; cases hsb1
    have : H.istate sb = some st' := by
      obtain ⟨i, zz, bb, stt, al, e, hzz, hbb, hstt, -⟩ := hinv
      cases e; rw [hzH] at hzz; cases hzz; rw [hz's] at hbb; cases hbb
      have hb' : ∃ d, H.bytes sb = some d := by
        unfold Heap.istate at hstt; split at hstt
        · next d hd => exact ⟨d, hd⟩
        · cases hstt
      obtain ⟨d, hd⟩ := hb'
      have hd' : h.bytes sb = some d := hd
      simp [Heap.istate, hd', H, InflateInv.setZS]
    rw [this] at hst1; cases hst1
    rw [hhd] at hhd1; cases hhd1; rfl
  have hnH : (ownL H b s).Nodup := by rw [hown]; exact hn
  obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hstr, hbud, hnod, hlk, hlit⟩ := hv.2.2
  have fr : FreshBlocks h := hfr
  have hsbl : sb < h.nextBlk := by
    obtain ⟨_, _, _, _, _, e, hzz, hbb, hstt, -⟩ := hinv
    cases e; rw [hzH] at hzz; cases hzz; rw [hz's] at hbb; cases hbb
    unfold Heap.istate at hstt; split at hstt
    · next d hd => exact live_lt fr ⟨d, hd⟩
    · cases hstt
  have wfH : GzWFr w H := by
    refine ⟨hc, ⟨fun c e => ?_, hdf⟩, hgz, fun c s2 e => ?_, hbud, hnod, hlk, hlit⟩
    · have hne : c ≠ sb := by have : H.nextBlk = h.nextBlk := rfl; omega
      refine ⟨?_, (hfr c e).2.1, (hfr c e).2.2⟩
      simp [H, InflateInv.setZS, upd_ne _ _ _ _ hne, (hfr c e).1]
    · obtain ⟨z2, hz2⟩ := hstr c s2 e
      by_cases hj : s2.strm = s.strm
      · rw [hj]; exact ⟨z', hzH⟩
      · exact ⟨z2, by simp [H, InflateInv.setZS, upd_ne _ _ _ _ hj, hz2]⟩
  refine ⟨⟨⟨b, s, rfl, hsH, shH, hnH⟩, ⟨b, s, rfl, hsH, hr⟩, wfH⟩, ?_⟩
  have hsbO : sb ∈ GzOwned w h (some b) := by
    simp only [GzOwned, hs, hz, hzs]; simp
  refine gstep_mk hs hsH rfl (fun _ _ _ => rfl) (fun i hi => by simp [H, InflateInv.setZS, upd_ne _ _ _ _ hi]) rfl
    (fun c _ hno => ?_) (fun _ _ e => e) rfl rfl rfl (Nat.le_refl _) (fun c hc _ => ?_)
  · have hne : c ≠ sb := fun e => hno (e ▸ hsbO)
    exact ⟨rfl, by simp [H, InflateInv.setZS, upd_ne _ _ _ _ hne], rfl, rfl, rfl⟩
  · have e : GzOwned w H (some b) = GzOwned w h (some b) := by
      simp only [GzOwned, hsH, hs, hzH, hz, hz's, hzs]
    have hc' : c ∈ GzOwned w H (some b) := hc
    rwa [e] at hc'

/-! ## `gz_look` in parts (copied from the translation) -/

open ZlibNg.Inflate in
/-- From `if (magic)` of `gz_look` to the end. -/
def lookTail (state : GzPtr) (strm : StreamPtr) (magic : Bool) : G Int32 := do
  if magic then
    let _ ← lm (inflateReset strm)
    wrG state fun s => { s with how := GZIP }
    wrG state fun s => { s with direct := 0 }
    return 0
  if (← rdG state (·.direct)) == 0 then
    lm (wrZ strm fun z => { z with avail_in := 0 })
    wrG state fun s => { s with eof := 1 }
    wrG state fun s => { s with «have» := 0 }
    return 0
  let o ← (← ldGz state).out.get
  wrG state fun s => { s with next := .val o }
  lm (Ptr.memcpy (← (← ldGz state).next.get) (← lm (rdZ strm (·.next_in))) (← lm (rdZ strm (·.avail_in))).toNat)
  let ai ← lm (rdZ strm (·.avail_in))
  wrG state fun s => { s with «have» := ai }
  lm (wrZ strm fun z => { z with avail_in := 0 })
  wrG state fun s => { s with how := COPY }
  wrG state fun s => { s with direct := 1 }
  return 0

open ZlibNg.Inflate in
/-- The magic-number test of `gz_look` and what follows. -/
def lookMagic (state : GzPtr) (strm : StreamPtr) : G Int32 := do
  let magic ← if (← lm (rdZ strm (·.avail_in))) > 1 then do
      if (← lm (index8 (← lm (rdZ strm (·.next_in))) 0)) == 31 then do
        pure ((← lm (index8 (← lm (rdZ strm (·.next_in))) 1)) == 139)
      else pure false
    else pure false
  lookTail state strm magic

open ZlibNg.Inflate in
/-- `gz_look` after the buffers exist. -/
def lookRest (state : GzPtr) (strm : StreamPtr) : G Int32 := do
  if (← rdG state (·.direct)) == -1 then
    let _ ← lm (inflateReset strm)
    wrG state fun s => { s with how := GZIP }
    wrG state fun s => { s with direct := 0 }
    return 0
  if (← lm (rdZ strm (·.avail_in))) < 2 then
    if (← gz_avail state) == -1 then
      return -1
    if (← lm (rdZ strm (·.avail_in))) == 0 then
      return 0
  lookMagic state strm

theorem gz_look_eq (state : GzPtr) : gz_look state = (do
    let strm ← strmOf state
    if (← rdG state (·.size)) == 0 then
      if (← gz_read_init state) == -1 then
        return -1
    lookRest state strm) := rfl

/-! ## The post-condition -/

/-- The inflate state of the stream of `s` is the one `inflateReset` leaves: mode `HEAD`, no bits, not the last
block. -/
def HeadState (H : Heap) (s : GzState) : Prop :=
  ∃ z sb st, H.streams s.strm = some z ∧ z.state = some sb ∧ H.istate sb = some st ∧
    st.mode = ZlibNg.Inflate.HEAD ∧ st.bits = 0 ∧ st.last = 0

/-- What `gz_look` leaves on a read handle with `x.have == 0`: `-1` or `0`; a step of the call that only reads the file
system; a state with the same `x.pos` and `skip`, with buffers when the result is `0`; when it switched to `GZIP`, the
inflate state just reset (`HeadState`); the read invariant of the world with `x.have` cleared; and `x.have` bytes from
`x.next` inside the `out` buffer. -/
def LookPost (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  (r = -1 ∨ r = 0) ∧ GStep w h W H b [] ∧ FsRd w.fs W.fs ∧
  ∃ s', W.gz H b = some s' ∧ s'.pos = s.pos ∧ s'.skip = s.skip ∧ (r = 0 → s'.size ≠ 0) ∧
    (r = 0 → s'.how = GZIP → s.how = GZIP ∨ HeadState H s') ∧
    GzInvR { W with gzs := upd W.gzs b (some { s' with «have» := 0 }) } H (some b) ∧
    (s'.«have» = 0 ∨ (s'.size ≠ 0 ∧ ∀ c base, GzBufs H s' c base →
      ∃ p, s'.next = .val p ∧ Inside c base (inSize s') (inSize s' + outSize s') p s'.«have».toNat))

/-- A read handle whose `x.have` is already 0 gives the post-condition. -/
theorem lookPost_of {w : World} {h : Heap} {b : Nat} {s : GzState} {r : Int32} {W : World} {H : Heap} {s' : GzState}
    (hr : r = -1 ∨ r = 0) (g : GStep w h W H b []) (hf : FsRd w.fs W.fs) (hv : GzInvR W H (some b))
    (hs' : W.gz H b = some s') (hp : s'.pos = s.pos) (hk : s'.skip = s.skip) (hz : r = 0 → s'.size ≠ 0)
    (hg : r = 0 → s'.how = GZIP → s.how = GZIP ∨ HeadState H s')
    (h0 : s'.«have» = 0) : LookPost w h b s r W H := by
  refine ⟨hr, g, hf, s', hs', hp, hk, hz, hg, ?_, Or.inl h0⟩
  rw [have0_self h0, DeflateReset.upd_self W.gzs b s' (gzs_of hs')]
  exact hv

theorem outSize_read {s : GzState} (hr : s.mode = GZ_READ) (d : Int32) :
    outSize { s with direct := d } = outSize s := by
  simp [outSize, hr, read_ne_write]

/-- A store of no output, another `x.next`, `how`, `direct` and `eof` keeps a read handle. -/
theorem invR_look {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (nx : Ival BPtr) (hw : Int32) (hhow : hw = LOOK ∨ hw = ZlibNg.Gz.COPY ∨ hw = GZIP)
    (d e : Int32) :
    GzInvR { w with gzs := upd w.gzs b (some { s with «have» := 0, next := nx, how := hw, direct := d, eof := e }) } h
      (some b) ∧
    GStep w h { w with gzs := upd w.gzs b (some { s with «have» := 0, next := nx, how := hw, direct := d, eof := e }) }
      h b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  have P := sh.pos
  let s' : GzState := { s with «have» := 0, next := nx, how := hw, direct := d, eof := e }
  have hio : outSize s' = outSize s := by
    simp [outSize, s', hr, read_ne_write]
  have sh' : GzShape h s' := by
    refine ⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, sh.size, ⟨P.1, P.2, P.3, P.4⟩,
      ⟨sh.msg.1, sh.msg.2⟩, fun _ => ⟨hhow, fun hsz => ?_, fun _ => rfl, fun _ => ?_,
        fun hz => (R.fresh hz).of_strm rfl⟩, fun e' => absurd (hr.symm.trans e') read_ne_write, fun hz => sh.dead hz⟩
    · obtain ⟨c, base, z, hB, hi, hz, -, hai, hreg, hmsg⟩ := R.bufs hsz
      refine ⟨c, base, z, ⟨hB.size, hB.buffers, hB.inp, fun e' => ?_, ?_, hB.hdr⟩, hi, hz, Or.inl rfl, hai, hreg, hmsg⟩
      · rw [hio] at e'; exact hB.out e'
      · rw [hio]; exact hB.fits
    · show s.pos.toInt + s.skip.toInt + ((0 : UInt32).toNat : Int) ≤ GZ_OFF_MAX.toInt
      simpa using P.2
  have hn' : (ownL h b s').Nodup := hn
  refine ⟨(keeps_store hs (HLess.refl h) (fun _ e' => e') sh' hn' rfl rfl).1 hv, ?_⟩
  exact gstep_st hs w.fs rfl rfl rfl rfl

open ZlibNg.Inflate in
/-- `inflateReset(strm); state->how = GZIP; state->direct = 0; return 0;` on a read handle with buffers. -/
theorem resetTail_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) :
    GSat w h (do
      let _ ← lm (inflateReset (some s.strm))
      wrG (some b) fun s => { s with how := GZIP }
      wrG (some b) fun s => { s with direct := 0 }
      return (0 : Int32)) (LookPost w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  obtain ⟨c, base, z, hB, hinv, hz, -, hai, -⟩ := R.bufs hsz
  obtain ⟨i, z1, sb, st, al, e, L, -, -⟩ := InflateInv.live hinv
  cases e
  have ez : z1 = z := by have := L.hz; rw [hz] at this; cases this; rfl
  subst ez
  have er := InflateReset.reset_run L
  obtain ⟨i2, z2, b2, st2, e2, run2, inv2⟩ := InflateReset.reset_inv hinv
  have run2' : inflateReset (some s.strm) h = _ := run2
  rw [er] at run2'
  injection run2' with run3
  injection run3 with _ run4
  rw [← run4] at inv2
  obtain ⟨hv1, g1⟩ := invR_setZS hv hs hsz hz L.hb (show (InflateReset.rkZ z1 st.wrap).state = some sb from L.hb) inv2
    rfl (fun c' base' hB' => by
      have e1 := hB'.buffers; rw [hB.buffers] at e1; cases e1; exact hai) (Or.inl rfl)
  generalize hH : InflateInv.setZS h s.strm (InflateReset.rkZ z1 st.wrap) sb (InflateReset.rkS sb (InflateReset.rS st)) = H at hv1 g1 er
  have hsH : w.gz H b = some s := by rw [← hH]; exact hs
  refine GSat.bind (GSat.lm ⟨_, H, er, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_app hsH _) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same hsH _) _) ?_)
  refine GSat.pure ?_
  obtain ⟨hv2, g2⟩ := invR_look hv1 hsH s.next GZIP (Or.inr (Or.inr rfl)) 0 s.eof
  simp only [InflateInv.upd_upd]
  have es : ({ ({ s with how := GZIP } : GzState) with direct := 0 } : GzState) =
      { s with «have» := 0, next := s.next, how := GZIP, direct := 0, eof := s.eof } := by
    cases s; simp only at h0 ⊢; rw [h0]
  rw [es]
  have hHS : HeadState H s := by
    obtain ⟨d, hd⟩ := L.hd
    refine ⟨InflateReset.rkZ z1 st.wrap, sb, InflateReset.rkS sb (InflateReset.rS st), ?_, L.hb, ?_, rfl, rfl, rfl⟩
    · rw [← hH]; simp [InflateInv.setZS]
    · rw [← hH]; simp [Heap.istate, InflateInv.setZS, hd]
  exact lookPost_of (Or.inr rfl) (g1.trans g2 ⟨s, hs⟩ ⟨s, hsH⟩) (FsRd.refl _) hv2 (gz_upd_same hsH _) rfl rfl
    (fun _ => hsz) (fun _ _ => Or.inr hHS) rfl

/-! ## The magic bytes and the copy of a transparent file -/

/-- `memcpy` from below `od` to `od` inside one heap block: only the bytes `[od, od + n)` of that block change. -/
theorem memcpy_below {H : Heap} {c od os n : Nat} {a : Array UInt8} (ha : H.bytes c = some a)
    (h1 : od + n ≤ a.size) (hdis : os + n ≤ od) :
    ∃ H', Ptr.memcpy (Ptr.ref (BRef.heap c) od : BPtr) (Ptr.ref (BRef.heap c) os) n H = .ok ((), H') ∧ HBuf H H' c od (od + n) := by
  have h2 : os + n ≤ a.size := by omega
  have hno : ¬ (n > 0 ∧ ¬ (od + n ≤ os ∨ os + n ≤ od)) := fun h => h.2 (Or.inr hdis)
  refine ⟨{ H with bytes := upd H.bytes c (some (InflateDict.copyFold a od os (List.range' 0 n) a)) }, ?_, ?_⟩
  · simp only [Ptr.memcpy, InflateDict.space_get_heap, ha, Space.ro, Heap.isRo, Bool.false_eq_true,
      ↓reduceIte, h1, h2, and_self, true_and, hno]
    rw [ChunkMem.modify_heap _ _ a ha, InflateDict.memcpy_loop]
  · refine ⟨_, rfl, ?_, ?_, ?_⟩
    · intro c' hc'; simp [upd_ne _ _ _ _ hc']
    · intro e; rw [ha] at e; cases e
    intro a' ha'
    rw [ha] at ha'; cases ha'
    refine ⟨InflateDict.copyFold a od os (List.range' 0 n) a, by simp, InflateDict.copyFold_size _ _ _ _ _, fun j hj => ?_⟩
    exact InflateDict.copyFold_get _ _ _ _ _ j fun i hi => ChunkMem.mem_range'_bound hi hj

theorem index8_heap {H : Heap} {c off : Nat} (i : Nat) {a : Array UInt8} (ha : H.bytes c = some a)
    (hi : off + i < a.size) : index8 (.ref (.heap c) off) (Int.ofNat i) H = .ok (a[off + i]!, H) :=
  Inftrees.index_nat (r := BRef.heap c) ha hi

open ZlibNg.Inflate in
/-- The `if (magic)` tail of `gz_look` on a read handle with buffers and input. -/
theorem lookTail_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) {z : ZStream} (hz : h.streams s.strm = some z)
    (hai : z.avail_in ≠ 0) (magic : Bool) :
    GSat w h (lookTail (some b) (some s.strm) magic) (LookPost w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  unfold lookTail
  apply GSat.ite
  · intro _; exact resetTail_spec hv hs h0 hsz
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    -- not a gzip stream and not transparent: no input, end of file
    let z' : ZStream := { z with avail_in := 0 }
    refine GSat.bind (GSat.lm ⟨(), { h with streams := upd h.streams s.strm (some z') }, wrZ_app hz _, ?_⟩)
    have hv1 := invR_strm (z' := z') hv hs hsz hz rfl (fun _ _ _ => Or.inl rfl)
    have g1 := gstep_strm hs z' hz rfl
    have hs1 : w.gz { h with streams := upd h.streams s.strm (some z') } b = some s := hs
    refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
    refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same hs1 _) _) ?_)
    refine GSat.pure ?_
    obtain ⟨hv2, g2⟩ := invR_look hv1 hs1 s.next s.how R.how s.direct 1
    simp only [InflateInv.upd_upd]
    have es : ({ ({ s with eof := 1 } : GzState) with «have» := 0 } : GzState) =
        { s with «have» := 0, next := s.next, how := s.how, direct := s.direct, eof := 1 } := rfl
    rw [es]
    exact lookPost_of (Or.inr rfl) (g1.trans g2 ⟨s, hs⟩ ⟨s, hs1⟩) (FsRd.refl _) hv2 (gz_upd_same hs1 _) rfl rfl
      (fun _ => hsz) (fun _ e => Or.inl e) rfl
  intro _
  -- transparent: copy the input to the output buffer
  obtain ⟨c, base, z0, hB, -, hz0, -, hin, -⟩ := R.bufs hsz
  rw [hz] at hz0; cases hz0
  obtain ⟨k, hnx, -, hkn⟩ := hin.resolve_left hai
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  obtain ⟨d, hd, hds⟩ := hB.fits
  have hin' : inSize s = s.want.toNat := by simp [inSize, hr, read_ne_write]
  have hout' : outSize s = 2 * s.want.toNat := by simp [outSize, hr, read_ne_write]
  have hwl := sh.want_lo
  have hO : s.out = .val (.ref (.heap c) (base + inSize s)) := hB.out (by rw [hout']; omega)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  refine GSat.bind (GSat.lm ⟨_, h, (by rw [hO]; rfl), ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
  let s1 : GzState := { s with next := .val (.ref (.heap c) (base + inSize s)) }
  have hs1 := gz_upd_same hs s1
  refine GSat.bind (GSat.of_eq (ldGz_app hs1) ?_)
  refine GSat.bind (GSat.lm ⟨_, h, rfl, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
  rw [hnx]
  obtain ⟨H1, em, x⟩ := memcpy_below (od := base + inSize s) (os := base + k) (n := z.avail_in.toNat) hd
    (by omega) (by omega)
  refine GSat.bind (GSat.lm ⟨(), H1, em, ?_⟩)
  have hz1 : H1.streams s.strm = some z := by obtain ⟨t, rfl, -⟩ := x; exact hz
  refine GSat.bind (GSat.lm ⟨_, H1, rdZ_app hz1 _, ?_⟩)
  have hsH1 : ({ w with gzs := upd w.gzs b (some s1) } : World).gz H1 b = some s1 := by
    rw [x.gz hcb]; exact hs1
  refine GSat.bind (GSat.of_eq (wrG_app hsH1 _) ?_)
  let z' : ZStream := { z with avail_in := 0 }
  refine GSat.bind (GSat.lm ⟨(), { H1 with streams := upd H1.streams s.strm (some z') }, wrZ_app hz1 _, ?_⟩)
  let H2 : Heap := { H1 with streams := upd H1.streams s.strm (some z') }
  have hsH2 : ({ w with gzs := upd w.gzs b (some s1) } : World).gz H2 b = some s1 := hsH1
  refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same hsH2 _) _) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same (gz_upd_same hsH2 _) _) _) ?_)
  refine GSat.pure ?_
  -- the invariant through the copy, the stream and the state
  have hx : HBuf h H1 c base (base + inSize s + outSize s) := by
    obtain ⟨t, rfl, hne, hnone, hsz'⟩ := x
    refine ⟨t, rfl, hne, hnone, fun a ha => ?_⟩
    obtain ⟨a', e1, e2, e3⟩ := hsz' a ha
    exact ⟨a', e1, e2, fun j hj => e3 j (by omega)⟩
  have hvA : GzInvR { w with fs := w.fs } H1 (some b) := invR_hbuf hv hs hx hcb hpath hst (FsRd.refl _)
  have hvA' : GzInvR w H1 (some b) := hvA
  have hsA : w.gz H1 b = some s := by rw [x.gz hcb]; exact hs
  have hvB := invR_strm (z' := z') hvA' hsA hsz hz1 rfl (fun _ _ _ => Or.inl rfl)
  have hsB : w.gz H2 b = some s := hsA
  obtain ⟨hvC, gC⟩ := invR_look hvB hsB (.val (.ref (.heap c) (base + inSize s))) ZlibNg.Gz.COPY
    (Or.inr (Or.inl rfl)) 1 s.eof
  have gA : GStep w h w H1 b [] := by
    have := gstep_hbuf hs hx hcb hown w.fs s rfl rfl rfl rfl
    rw [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this
    exact this
  have gB := gstep_strm hsA z' hz1 rfl
  simp only [InflateInv.upd_upd]
  let o3 : BPtr := .ref (.heap c) (base + inSize s)
  let s3 : GzState := { s with «have» := z.avail_in, next := .val o3, how := ZlibNg.Gz.COPY, direct := 1 }
  have hsW := gz_upd_same hsB s3
  refine ⟨Or.inr rfl, ?_, FsRd.refl _, s3, hsW, rfl, rfl, fun _ => hsz,
    fun _ e => absurd e (by decide : ZlibNg.Gz.COPY ≠ GZIP), ?_, ?_⟩
  · have g3 := gstep_st hsB w.fs (s' := s3) rfl rfl rfl rfl
    exact (gA.trans gB ⟨s, hs⟩ ⟨s, hsA⟩).trans g3 ⟨s, hs⟩ ⟨s, hsB⟩
  · simp only [InflateInv.upd_upd]; exact hvC
  · refine Or.inr ⟨hsz, fun c' base' hB' => ?_⟩
    have e1 := hB'.buffers; rw [show s3.buffers = s.buffers from rfl, hB.buffers] at e1; cases e1
    have hi3 : inSize s3 = inSize s := rfl
    have ho3 : outSize s3 = outSize s := by simp [outSize, s3, hr, read_ne_write]
    refine ⟨_, rfl, inSize s, rfl, Nat.le_refl _, ?_⟩
    rw [hi3, ho3]; show inSize s + z.avail_in.toNat ≤ _; omega

open ZlibNg.Inflate in
/-- The magic-number test reads `next_in[0]` and `next_in[1]` inside the `in` buffer. -/
theorem lookMagic_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) {z : ZStream} (hz : h.streams s.strm = some z)
    (hai : z.avail_in ≠ 0) :
    GSat w h (lookMagic (some b) (some s.strm)) (LookPost w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  obtain ⟨c, base, z0, hB, -, hz0, -, hin, -⟩ := R.bufs hsz
  rw [hz] at hz0; cases hz0
  obtain ⟨k, hnx, -, hkn⟩ := hin.resolve_left hai
  obtain ⟨d, hd, hds⟩ := hB.fits
  unfold lookMagic
  have T : ∀ m : Bool, GSat w h (lookTail (some b) (some s.strm) m) (LookPost w h b s) :=
    lookTail_spec hv hs h0 hsz hz hai
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
  dsimp only
  apply GSat.ite
  · intro hgt
    have hgt' : 1 < z.avail_in.toNat := UInt32.lt_iff_toNat_lt.mp hgt
    refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
    rw [hnx]
    refine GSat.bind (GSat.lm ⟨_, h, index8_heap 0 hd (by omega), ?_⟩)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
      rw [hnx]
      refine GSat.bind (GSat.lm ⟨_, h, index8_heap 1 hd (by omega), ?_⟩)
      exact GSat.bind (GSat.pure (T _))
    · intro _; exact GSat.bind (GSat.pure (T _))
  · intro _; exact GSat.bind (GSat.pure (T _))

/-- The post-condition of a later part of the call gives the post-condition of the whole. -/
theorem LookPost.pre {w W1 W : World} {h H1 H : Heap} {b : Nat} {s s1 : GzState} {r : Int32}
    (hs : w.gz h b = some s) (g : GStep w h W1 H1 b []) (hf : FsRd w.fs W1.fs) (hs1 : W1.gz H1 b = some s1)
    (hp : s1.pos = s.pos) (hk : s1.skip = s.skip) (hw : s1.how = s.how) (q : LookPost W1 H1 b s1 r W H) :
    LookPost w h b s r W H := by
  obtain ⟨hr, g2, hf2, s', hs', hp', hk', hz, hG, hv, hh⟩ := q
  exact ⟨hr, g.trans g2 ⟨s, hs⟩ ⟨s1, hs1⟩, hf.trans hf2, s', hs', hp'.trans hp, hk'.trans hk, hz,
    fun h1 h2 => (hG h1 h2).imp_left fun e => hw ▸ e, hv, hh⟩

open ZlibNg.Inflate in
/-- `gz_look` once the buffers exist. -/
theorem lookRest_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) :
    GSat w h (lookRest (some b) (some s.strm)) (LookPost w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  obtain ⟨c, base, z, hB, -, hz, -, -, -⟩ := R.bufs hsz
  unfold lookRest
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact resetTail_spec hv hs h0 hsz
  intro _
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.mono (gz_avail_spec hv hs h0 hsz) fun r W H q => ?_)
    obtain ⟨hr1, hv1, g1, hf1, s1, hs1, e1⟩ := q
    have h01 : s1.«have» = 0 := by rw [e1]; exact h0
    have hsz1 : s1.size ≠ 0 := by rw [e1]; exact hsz
    have hp1 : s1.pos = s.pos := by rw [e1]
    have hk1 : s1.skip = s.skip := by rw [e1]
    have hst1 : s1.strm = s.strm := by rw [e1]
    have hw1 : s1.how = s.how := by rw [e1]
    apply GSat.ite
    · intro _
      exact GSat.pure (lookPost_of (Or.inl rfl) g1 hf1 hv1 hs1 hp1 hk1 (fun e => absurd e (by decide)) (fun e => absurd e (by decide)) h01)
    intro _
    obtain ⟨sh1, -⟩ := inv_of hs1 hv1.1
    obtain ⟨c1, base1, z1, -, -, hz1, -, -, -⟩ := (sh1.read (modeOf hs1 hv1.2.1)).bufs hsz1
    rw [hst1] at hz1
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz1 _, ?_⟩)
    apply GSat.ite
    · intro _
      exact GSat.pure (lookPost_of (Or.inr rfl) g1 hf1 hv1 hs1 hp1 hk1 (fun _ => hsz1) (fun _ e => Or.inl (hw1 ▸ e)) h01)
    · intro hne
      have hai : z1.avail_in ≠ 0 := by simpa using hne
      rw [← hst1] at hz1 ⊢
      exact (lookMagic_spec hv1 hs1 h01 hsz1 hz1 hai).mono fun r W' H' q =>
        LookPost.pre hs g1 hf1 hs1 hp1 hk1 hw1 q
  · intro hlt
    have hai : z.avail_in ≠ 0 := by
      intro e; rw [e] at hlt; exact hlt (by decide)
    exact lookMagic_spec hv hs h0 hsz hz hai

/-- **`gz_look`** on a read handle with `x.have == 0`. -/
theorem gz_look_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) :
    GSat w h (gz_look (some b)) (LookPost w h b s) := by
  rw [gz_look_eq]
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hsz0
    have hsz : s.size = 0 := by simpa using hsz0
    refine GSat.bind (GSat.mono (gz_read_init_spec hv hs hsz) fun r W H q => ?_)
    obtain ⟨hv1, g1, hf1, s1, hs1, e1, hres⟩ := q
    have h01 : s1.«have» = 0 := by rw [e1]; exact h0
    have hp1 : s1.pos = s.pos := by rw [e1]
    have hk1 : s1.skip = s.skip := by rw [e1]
    have hst1 : s1.strm = s.strm := by rw [e1]
    have hw1 : s1.how = s.how := by rw [e1]
    have hf1' : FsRd w.fs W.fs := by rw [hf1]; exact FsRd.refl _
    apply GSat.ite
    · intro hr1
      have : r = -1 := by simpa using hr1
      subst this
      exact GSat.pure (lookPost_of (Or.inl rfl) g1 hf1' hv1 hs1 hp1 hk1 (fun e => absurd e (by decide)) (fun e => absurd e (by decide)) h01)
    · intro hr1
      have hne : r ≠ -1 := by simpa using hr1
      obtain ⟨-, hsz1, -⟩ := hres.resolve_right hne
      rw [← hst1]
      exact (lookRest_spec hv1 hs1 h01 hsz1).mono fun r W' H' q => LookPost.pre hs g1 hf1' hs1 hp1 hk1 hw1 q
  · intro hsz0
    have hsz : s.size ≠ 0 := by simpa using hsz0
    exact lookRest_spec hv hs h0 hsz

/-! ## Consuming a pending skip from the output buffer -/

/-- `n = min(x.have, skip)` bytes of the output buffer are skipped (`gzdirect` with patch 0020, and the loop of
`gz_skip`), then `k` runs (copied from the translation). -/
def consumeThen {α : Type} (state : GzPtr) (k : Unit → G α) : G α := do
  let hv ← rdG state (·.«have»)
  let sk ← rdG state (·.skip)
  let n : UInt32 := if GT_OFF hv || Int64.ofNat hv.toNat > sk then sk.toUInt64.toUInt32 else hv
  wrG state fun s => { s with «have» := s.«have» - n }
  let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
  wrG state fun s => { s with next := .val nx }
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
  wrG state fun s => { s with pos := np }
  let sk ← lm (chkI64 ((← rdG state (·.skip)).toInt - n.toNat))
  let r ← wrG state fun s => { s with skip := sk }
  k r

/-- **The consume step.** After `gz_look` (`LookPost`) with a pending skip and output: `min(x.have, skip)` bytes are
skipped; the handle is a read handle again, `x.pos + skip` is unchanged, and when a skip is still pending there is no
output left. -/
theorem consume_spec {α : Type} {W : World} {H : Heap} {b : Nat} {s' : GzState} {k : Unit → G α}
    {Q : α → World → Heap → Prop}
    (hv0 : GzInvR { W with gzs := upd W.gzs b (some { s' with «have» := 0 }) } H (some b))
    (hs' : W.gz H b = some s')
    (hout : s'.«have» = 0 ∨ (s'.size ≠ 0 ∧ ∀ c base, GzBufs H s' c base →
      ∃ p, s'.next = .val p ∧ Inside c base (inSize s') (inSize s' + outSize s') p s'.«have».toNat))
    (hh : s'.«have» ≠ 0)
    (hk : ∀ W2 s2, W2.gz H b = some s2 → GzInvR W2 H (some b) → GStep W H W2 H b [] → W2.fs = W.fs →
      s2.pos.toInt + s2.skip.toInt = s'.pos.toInt + s'.skip.toInt → (s2.skip ≠ 0 → s2.«have» = 0) →
      GSat W2 H (k ()) Q) :
    GSat W H (consumeThen (some b) k) Q := by
  let s0 : GzState := { s' with «have» := 0 }
  have hs0 : ({ W with gzs := upd W.gzs b (some s0) } : World).gz H b = some s0 := gz_upd_same hs' s0
  obtain ⟨sh, hn⟩ := inv_of hs0 hv0.1
  have hr : s0.mode = GZ_READ := modeOf hs0 hv0.2.1
  have R := sh.read hr
  have P := sh.pos
  have P2 : s'.pos.toInt + s'.skip.toInt ≤ GZ_OFF_MAX.toInt := P.2
  have P3 : -GZ_OFF_MAX.toInt ≤ s'.pos.toInt := P.3
  obtain ⟨db, hdb⟩ := gz_live hs'
  have h0 : 0 ≤ s'.skip.toInt := P.1
  have hN := nOf_toNat s'.«have» s'.skip h0
  generalize hn' : (if (GT_OFF s'.«have» || decide (Int64.ofNat s'.«have».toNat > s'.skip)) = true then
    s'.skip.toUInt64.toUInt32 else s'.«have») = n at hN
  have hmx' := gzmax
  have hsz : s'.size ≠ 0 := (hout.resolve_left hh).1
  obtain ⟨c, base, z, hb, -, -, -, -, -⟩ := R.bufs hsz
  have hb' : GzBufs H s' c base := ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩
  obtain ⟨q, hq, kk, hqk, hlo, hhi⟩ := (hout.resolve_left hh).2 c base hb'
  obtain ⟨d, hd, hds⟩ := hb.fits
  have hiS : inSize s0 = inSize s' := rfl
  have hoS : outSize s0 = outSize s' := rfl
  rw [hiS, hoS] at hds
  have hh' : s'.«have».toNat ≠ 0 := fun e => hh (UInt32.toNat_inj.mp (by simpa using e))
  have hnl : n.toNat ≤ s'.«have».toNat := by omega
  have hno : n.toNat ≤ s'.skip.toInt.toNat := by omega
  unfold consumeThen
  refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
  simp only [hn']
  let s1 : GzState := { s' with «have» := s'.«have» - n }
  refine GSat.bind (GSat.of_eq (wrG_app hs' _) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_upd hdb W s1) ?_)
  refine GSat.bind (GSat.lm ⟨q, H, by show Ival.get s'.next H = _; rw [hq]; rfl, ?_⟩)
  rw [hqk]
  refine GSat.bind (GSat.lm ⟨_, H, addH hd (off := base + kk) n.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb W s1 _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_upd hdb W _ _) ?_)
  have hpn : -(2 ^ 63 : Int) ≤ s'.pos.toInt + (n.toNat : Int) ∧ s'.pos.toInt + (n.toNat : Int) < 2 ^ 63 := by
    have := P3; have := P2; constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, H, chkI64_ok hpn.1 hpn.2 H, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb W _ _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_upd hdb W _ _) ?_)
  have hon : -(2 ^ 63 : Int) ≤ s'.skip.toInt - (n.toNat : Int) ∧ s'.skip.toInt - (n.toNat : Int) < 2 ^ 63 := by
    have := s'.skip.toInt_lt; constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, H, chkI64_ok hon.1 hon.2 H, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb W _ _) ?_)
  have e2 := toInt_ofInt' hpn.1 hpn.2
  have e3 := toInt_ofInt' hon.1 hon.2
  have hm1 : (s'.«have» - n).toNat = s'.«have».toNat - n.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hnl)]
  let nxF : BPtr := .ref (.heap c) (base + kk + n.toNat)
  let pF : Int64 := Int64.ofInt (s'.pos.toInt + (n.toNat : Int))
  let kF : Int64 := Int64.ofInt (s'.skip.toInt - (n.toNat : Int))
  let sF : GzState := { s' with «have» := s'.«have» - n, next := .val nxF, pos := pF, skip := kF }
  have hkh : sF.skip ≠ 0 → sF.«have» = 0 := by
    intro hk'
    have hk2 : s'.skip.toInt - (n.toNat : Int) ≠ 0 := by
      intro e; apply hk'; show Int64.ofInt _ = 0; rw [e]; rfl
    apply UInt32.toNat_inj.mp
    show (s'.«have» - n).toNat = _
    rw [hm1]; simp; omega
  have hvF := invR_seek hv0 hs0 (s'.«have» - n) (.val (.ref (.heap c) (base + kk + n.toNat)))
    (Int64.ofInt (s'.pos.toInt + (n.toNat : Int))) (Int64.ofInt (s'.skip.toInt - (n.toNat : Int))) s'.how R.how
    (by rw [e3]; omega) (by rw [e2, e3]; have := P2; omega) (by rw [e2]; have := P3; omega) (by
      by_cases hz2 : s'.«have» - n = 0
      · exact Or.inl hz2
      · refine Or.inr ⟨hsz, fun c' base' hb2 => ?_⟩
        have e1 := hb2.buffers; rw [hb.buffers] at e1; cases e1
        exact ⟨_, rfl, kk + n.toNat, by rw [Nat.add_assoc], by omega, by rw [hm1]; omega⟩) hkh
  simp only [InflateInv.upd_upd] at hvF ⊢
  have hsF : ({ W with gzs := upd W.gzs b (some sF) } : World).gz H b = some sF := gz_upd_same hs' sF
  exact hk _ sF hsF hvF (gstep_st hs' W.fs rfl rfl rfl rfl) rfl
    (by show (Int64.ofInt _).toInt + (Int64.ofInt _).toInt = _; rw [e2, e3]; omega) hkh

/-- Without a pending skip, or without output, the post-condition of `gz_look` gives the read invariant itself. -/
theorem invR_restore {W : World} {H : Heap} {b : Nat} {s' : GzState}
    (hv0 : GzInvR { W with gzs := upd W.gzs b (some { s' with «have» := 0 }) } H (some b))
    (hs' : W.gz H b = some s')
    (hout : s'.«have» = 0 ∨ (s'.size ≠ 0 ∧ ∀ c base, GzBufs H s' c base →
      ∃ p, s'.next = .val p ∧ Inside c base (inSize s') (inSize s' + outSize s') p s'.«have».toNat))
    (hkh : s'.skip ≠ 0 → s'.«have» = 0) : GzInvR W H (some b) := by
  let s0 : GzState := { s' with «have» := 0 }
  have hs0 : ({ W with gzs := upd W.gzs b (some s0) } : World).gz H b = some s0 := gz_upd_same hs' s0
  obtain ⟨sh, -⟩ := inv_of hs0 hv0.1
  have hr : s0.mode = GZ_READ := modeOf hs0 hv0.2.1
  have P := sh.pos
  have hout' : s'.«have» = 0 ∨ (s0.size ≠ 0 ∧ ∀ c base, GzBufs H s0 c base →
      ∃ q, s'.next = .val q ∧ Inside c base (inSize s0) (inSize s0 + outSize s0) q s'.«have».toNat) := by
    rcases hout with e | ⟨hsz, f⟩
    · exact Or.inl e
    · exact Or.inr ⟨hsz, fun c base hb => f c base ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩⟩
  have hv := invR_seek hv0 hs0 s'.«have» s'.next s'.pos s'.skip s'.how (sh.read hr).how P.1 P.2 P.3 hout' hkh
  simp only [InflateInv.upd_upd] at hv
  have es : ({ s0 with «have» := s'.«have», next := s'.next, pos := s'.pos, skip := s'.skip, how := s'.how } :
      GzState) = s' := by cases s'; rfl
  rw [es, DeflateReset.upd_self W.gzs b s' (gzs_of hs')] at hv
  exact hv

/-! ## `gzdirect` -/

/-- `gzdirect` (with patch 0020) on a read handle: a read handle again, and a step of the call. -/
theorem gzdirect_read {w : World} {h : Heap} {b : Nat} (hv : GzInvR w h (some b)) :
    GSat w h (gzdirect (some b)) (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b []) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  have hr := modeOf hs hv.2.1
  -- the end: `return state->direct == 1`
  have J : ∀ W H, GzInvR W H (some b) → GStep w h W H b [] →
      GSat W H (do let d ← rdG (some b) (·.direct); pure (if (d == 1) = true then (1 : Int32) else 0))
        (fun _ W H => GzInvR W H (some b) ∧ GStep w h W H b []) := by
    intro W H hvW g
    obtain ⟨b1, s1, e1, hs1, -, -⟩ := hvW.1
    cases e1
    exact GSat.bind (GSat.of_eq (rdG_app' hs1 _) (GSat.pure ⟨hvW, g⟩))
  have J0 := J w h hv (GStep.refl w h b [])
  unfold gzdirect
  apply GSat.ite
  · intro e; simp at e
  intro _
  dsimp only
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
      apply GSat.ite
      · intro h0
        have h0' : s.«have» = 0 := by simpa using h0
        refine GSat.bind (GSat.mono (gz_look_spec hv hs h0') fun r W H q => ?_)
        obtain ⟨-, g1, -, s', hs', -, -, -, -, hv0, hout⟩ := q
        refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
        refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
        apply GSat.ite
        · intro hc
          have hh : s'.«have» ≠ 0 := by
            intro e; rw [e] at hc; simp at hc
          exact consume_spec hv0 hs' hout hh fun W2 s2 hs2 hv2 g2 _ _ _ =>
            J W2 H hv2 (g1.trans g2 ⟨s, hs⟩ ⟨s', hs'⟩)
        · intro hc
          have hkh : s'.skip ≠ 0 → s'.«have» = 0 := by
            intro hk
            by_cases hh : s'.«have» = 0
            · exact hh
            · exact absurd (by simp [hk, hh]) hc
          exact J W H (invR_restore hv0 hs' hout hkh) g1
      · intro _; exact J0
    · intro _; exact J0
  · intro _; exact J0

theorem direct_keepsR : KeepsR SDirect := by
  intro w h w' h' f hv ⟨r, e⟩
  obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
  obtain ⟨r2, W, H, e2, q⟩ := (gzdirect_read hv).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact q.1

end ZlibNgF.Proof.GzMode
