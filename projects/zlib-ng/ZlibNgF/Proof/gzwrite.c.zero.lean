import ZlibNgF.Proof.«gzwrite.c.compspec»
import ZlibNgF.Proof.«gzread.c.load»
import ZlibNgF.Proof.«chunkset.mem»

/-!
# `gz_zero` (`ZlibNgF`)

`gz_zero_spec`: on a write handle with a pending skip, `gz_zero` (with patch 0019) returns, keeps the invariant
`GzInvWS`, is a step of the file, keeps `x.pos + skip` and the fields of `ZFix`, and on success leaves no skip and
the buffers made. Each batch of zeros is taken off `skip` when it is added to `x.pos`, before `gz_comp` writes it, so
a failing `gz_comp` leaves `x.pos + skip` as it was; the loop ends by `skip`.

`gz_comp` is used through `CompBase`: what the callers of `gz_comp` take of it (pre: the invariant of a write handle;
post: result `0` or `-1`, the invariant, a step of the file, the fields of `WFix`, and on success the buffers and, for
a flush other than `Z_FINISH`, no input left).

Stores into the buffer block of a write handle keep its invariant (`invWS_hbuf`), as for a read handle.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-! ## What the callers use of `gz_comp` -/

/-- The potential of `DeflateGz` meets `DeflatePsi`. -/
theorem psi_of (G : DeflateGz) : ∃ ψ Gr, DeflatePsi ψ Gr := by
  obtain ⟨ψ, Gr, hG, hb, hd, -⟩ := G.2.2
  exact ⟨ψ, Gr, hG, fun h s sb st f a b c => hb h s sb st f a b c, hd⟩

/-- The post-condition of `gz_comp(state, flush)` on a write handle that keeps the invariant. -/
def CompInv (w : World) (h : Heap) (b : Nat) (s : GzState) (flush : Int32) (r : Int32) (W : World) (H : Heap) : Prop :=
  ∃ s' z', W.gz H b = some s' ∧ H.streams s.strm = some z' ∧ GzInvWS W H (some b) ∧ GStep w h W H b [] ∧
    WFix s s' ∧ (s.size ≠ 0 → s'.size = s.size) ∧ (r = 0 ∨ r = -1) ∧
    (r = 0 → s'.size ≠ 0 ∧ (flush ≠ ZlibNg.Inflate.Z_FINISH → z'.avail_in = 0))

/-- **`gz_comp`** on a write handle with the invariant. -/
theorem comp_inv (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (flush : Int32) :
    GSat w h (gz_comp (some b) flush) (CompInv w h b s flush) := by
  obtain ⟨ψ, Gr, hψ⟩ := psi_of G
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨z, hz⟩ := sh.strm
  refine GSat.mono (C G ψ Gr hψ w h b flush s z hs hz (Or.inl hv)) fun r W H q => ?_
  obtain ⟨s', z', hs', hz', fx, hsz, g, -, -, -, -, hinv, -, -, -, hr, hok, -, -⟩ := q
  exact ⟨s', z', hs', hz', hinv hv, g, fx, fun e => (hsz e).1, hr, fun e => ⟨(hok e).1, (hok e).2.1⟩⟩

/-! ## Stores into the buffer block of a write handle -/

/-- The fields of a write handle after stores into one block that is neither its `path` nor the block of its
stream's state. -/
theorem shape_hbufW {h H : Heap} {cb lo hi : Nat} {s : GzState} (sh : GzShape h s) (hw : s.mode = GZ_WRITE)
    (x : HBuf h H cb lo hi) (hp : cb ∉ blkOf s.path) (hst : cb ∉ stBlk h s) : GzShape H s := by
  obtain ⟨t, rfl, hne, hnone, hsz⟩ := x
  have hlive : ∀ c d, h.bytes c = some d → ∃ d', t c = some d' ∧ d'.size = d.size := by
    intro c d hd
    by_cases e : c = cb
    · subst e; obtain ⟨a', e1, e2, -⟩ := hsz d hd; exact ⟨a', e1, e2⟩
    · exact ⟨d, by rw [hne c e]; exact hd, rfl⟩
  have hbufs : ∀ c base, GzBufs h s c base → GzBufs { h with bytes := t } s c base := by
    intro c base hB
    obtain ⟨d, hd, hds⟩ := hB.fits
    obtain ⟨d', e1, e2⟩ := hlive c d hd
    exact ⟨hB.size, hB.buffers, hB.inp, hB.out, ⟨d', e1, by rw [e2]; exact hds⟩, hB.hdr.1, hB.hdr.2⟩
  refine ⟨sh.mode, ownStr_keep sh.path fun c hc => hne c (fun e => hp (e ▸ hc)), sh.strm, sh.want_lo, sh.want_hi,
    sh.size, sh.pos, ⟨?_, sh.msg.mem⟩, fun hr => absurd (hw.symm.trans hr) write_ne_read, fun _ => ?_, fun hz c hc => ?_⟩
  · rcases sh.msg.msg with e | ⟨c, d, e, hd⟩
    · exact Or.inl e
    · obtain ⟨d', e1, -⟩ := hlive c d hd; exact Or.inr ⟨c, d', e, e1⟩
  · have Wr := sh.write hw
    refine ⟨fun hsz' => ?_, Wr.nobuf, Wr.have0⟩
    obtain ⟨c, base, z, hB, hz, W⟩ := Wr.bufs hsz'
    have hnh' : ∀ sb st k, z.state = some sb → Heap.dstate { h with bytes := t } sb = some st →
        st.gzhead ≠ .val (some k) := by
      intro sb st k hsb hst'
      have hsbne : sb ≠ cb := fun e => hst (e ▸ stBlk_of hz hsb)
      refine W.nohdr sb st k hsb ?_
      have e1 : t sb = h.bytes sb := hne sb hsbne
      simp only [Heap.dstate, e1] at hst' ⊢; exact hst'
    refine ⟨c, base, z, hbufs c base hB, hz, ⟨fun hdir => ?_, hnh', W.inp, W.nostate, W.out⟩⟩
    obtain ⟨hd, hsd⟩ := W.deflate hdir
    obtain ⟨i, z0, sb, st, al, e, hz0, hsb, hst0, hal, core⟩ := hd
    cases e
    rw [hz] at hz0; cases hz0
    have hsbne : sb ≠ cb := fun e => hst (e ▸ stBlk_of hz hsb)
    have hc : DCallerStep h { h with bytes := t } (some s.strm) :=
      ⟨s.strm, z, z, sb, st, rfl, hz, hz, hsb, hst0, rfl, hne sb hsbne, rfl, rfl,
        fun k g hk' _ => absurd hk' (W.nohdr sb st k hsb hst0), rfl, Nat.le_refl _⟩
    exact ⟨DeflateReach.caller_inv ⟨s.strm, z, sb, st, al, rfl, hz, hsb, hst0, hal, core⟩ hc,
      DeflateSide.caller_side hsd hc⟩
  · obtain ⟨h1, h2⟩ := sh.dead hz c hc
    refine ⟨?_, h2⟩
    by_cases e : c = cb
    · subst e; exact hnone h1
    · show t c = none; rw [hne c e]; exact h1

/-- **Stores into the buffer block** of a write handle keep its invariant, and are a step of the file. -/
theorem invWS_hbuf {w : World} {h H : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) {cb lo hi : Nat} (x : HBuf h H cb lo hi) (hcb : b ≠ cb) (hp : cb ∉ blkOf s.path)
    (hst : cb ∉ stBlk h s) (hown : cb ∈ GzOwned w h (some b)) :
    GzInvWS w H (some b) ∧ w.gz H b = some s ∧ GStep w h w H b [] := by
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have hwm := modeOf hs hm
  have hsH : w.gz H b = some s := by
    obtain ⟨d, hd⟩ := gz_live hs
    unfold World.gz at hs ⊢; rw [x.bytes_ne hcb, hd]; rw [hd] at hs; exact hs
  have sh' := shape_hbufW sh hwm x hp hst
  have hstB : stBlk H s = stBlk h s := by obtain ⟨t, rfl, -, -, -⟩ := x; rfl
  have hown' : ownL H b s = ownL h b s := by simp only [ownL, hstB]
  obtain ⟨t, rfl, hne, hnone, hsz⟩ := x
  refine ⟨⟨⟨b, s, rfl, hsH, sh', by rw [hown']; exact hn⟩, ⟨b, s, rfl, hsH, hwm⟩, ?_⟩, hsH, ?_⟩
  · obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hstr, hL⟩ := hw
    refine ⟨hc, ⟨fun c hc' => ⟨(hfr c hc').1, (hfr c hc').2.1, ?_⟩, hdf⟩, hgz, fun c s2 e => ?_, hL⟩
    · by_cases e : c = cb
      · subst e; exact hnone (hfr c hc').2.2
      · show t c = none; rw [hne c e]; exact (hfr c hc').2.2
    · refine hstr c s2 ?_
      unfold World.gz at e ⊢
      by_cases e' : c = cb
      · subst e'
        cases h1 : h.bytes c with
        | none => have := hnone h1; simp only [this] at e; cases e
        | some d => obtain ⟨a', e1, -, -⟩ := hsz d h1; simp only [e1] at e; exact e
      · simp only [hne c e'] at e; exact e
  · refine gstep_mk hs hsH rfl (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
      (fun c _ hno => ⟨hne c (fun e => hno (e ▸ hown)), rfl, rfl, rfl, rfl⟩) (fun _ _ e => e) rfl rfl rfl
      (Nat.le_refl _) (fun c hc _ => ?_)
    simp only [GzOwned, hsH, hs] at hc ⊢
    exact hc

/-- `memset` into heap block `c`: the block changes only inside the range. -/
theorem memset_hbuf {H : Heap} {c off : Nat} {a : Array UInt8} (ha : H.bytes c = some a) (v : UInt8) (n : Nat)
    (hn : off + n ≤ a.size) : ∃ H', Ptr.memset (Ptr.ref (BRef.heap c) off : BPtr) v n H = .ok ((), H') ∧ HBuf H H' c off (off + n) := by
  refine ⟨{ H with bytes := upd H.bytes c (some (ChunkMem.fillFold v off (List.range' 0 n) a)) }, ?_, ?_⟩
  · have hg : Space.get H (BRef.heap c) = some a := ha
    simp only [Ptr.memset, hg, Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, hn]
    rw [ChunkMem.modify_heap H c a ha, ChunkMem.memset_loop]
  · refine ⟨upd H.bytes c (some (ChunkMem.fillFold v off (List.range' 0 n) a)), rfl, ?_, ?_, ?_⟩
    · intro c' hc'; exact upd_ne _ _ _ _ hc'
    · intro e; rw [ha] at e; cases e
    intro a' ha'
    rw [ha] at ha'; cases ha'
    exact ⟨_, upd_same _ _ _, ChunkMem.fillFold_size _ _ _ _, fun j hj =>
      ChunkMem.fillFold_get _ _ _ _ j (fun i hi => ChunkMem.mem_range'_bound hi hj)⟩

/-- The blocks of a write handle with buffers in block `c`: `c` is not the state's block, its `path`, nor the block
of its stream's state, and it belongs to the file. -/
theorem bufBlk {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (hn : (ownL h b s).Nodup)
    (hsz : s.size ≠ 0) {c base : Nat} (hB : GzBufs h s c base) :
    b ≠ c ∧ c ∉ blkOf s.path ∧ c ∉ stBlk h s ∧ c ∈ GzOwned w h (some b) := by
  have hsplit : ownL h b s = [b] ++ blkOf s.path ++ blkOf s.msg ++ ([c] ++ stBlk h s) := by
    simp [ownL, hsz, hB.buffers, blkOf]
  rw [hsplit] at hn
  have hcL : c ∈ ownL h b s := by rw [hsplit]; simp
  refine ⟨?_, ?_, ?_, ownL_owned hs c hcL⟩
  · intro e; subst e
    have := (List.nodup_append.mp hn).2.2 b (by simp) b (by simp); exact this rfl
  · intro m
    have := (List.nodup_append.mp hn).2.2 c (by simp [m]) c (by simp); exact this rfl
  · intro m
    have h2 := (List.nodup_append.mp hn).2.1
    rw [List.nodup_append] at h2
    exact h2.2.2 c (by simp) c m rfl

/-! ## The loop of `gz_zero` -/

/-- The end of the body of the loop of `gz_zero`, after the zeros are in `in` (copied from the translation). -/
def zeroTail (state : GzPtr) (strm : StreamPtr) (n : UInt32) (first : Int32) : G (Int32 × Ctl) := do
  lm (ZlibNg.Inflate.wrZ strm fun z => { z with avail_in := n })
  let i ← (← ldGz state).«in».get
  lm (ZlibNg.Inflate.wrZ strm fun z => { z with next_in := i })
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
  wrG state fun st => { st with pos := np }
  let sk ← lm (chkI64 ((← rdG state (·.skip)).toInt - n.toNat))
  wrG state fun st => { st with skip := sk }
  if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
    return (first, .ret)
  return (first, .go)

/-- The body of the loop of `gz_zero` (copied from the translation). -/
def zeroBody (state : GzPtr) (strm : StreamPtr) (s : Int32 × Ctl) : G (Int32 × Ctl) := do
  let mut first := s.1
  let sz ← rdG state (·.size)
  let sk ← rdG state (·.skip)
  let n : UInt32 := if GT_OFF sz || Int64.ofNat sz.toNat > sk then sk.toUInt64.toUInt32 else sz
  if first != 0 then
    lm (Ptr.memset (← (← ldGz state).«in».get) 0 n.toNat)
    first := 0
  zeroTail state strm n first

/-- The condition of the loop of `gz_zero` (copied from the translation). -/
def zeroCond (state : GzPtr) (s : Int32 × Ctl) : G (Bool × (Int32 × Ctl)) := do
  if s.2 != .go then return (false, s)
  return ((← rdG state (·.skip)) != 0, s)

theorem gz_zero_eq (state : GzPtr) : gz_zero state = (do
    let strm ← strmOf state
    if (← rdG state (·.size)) == 0 then
      if (← gz_write_init state) == -1 then
        return -1
    if (← lm (ZlibNg.Inflate.rdZ strm (·.avail_in))) != 0 then
      if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
        return -1
    let lp ← gdoWhile (zeroBody state strm) (zeroCond state) ((1 : Int32), Ctl.go)
    if lp.2 == .ret then
      return -1
    return 0) := rfl

theorem i64_toNat_toUInt64 (sk : Int64) (h : 0 ≤ sk.toInt) : sk.toUInt64.toNat = sk.toInt.toNat := by
  have e := BitVec.toInt_eq_toNat_cond sk.toBitVec
  have h2 : sk.toInt = sk.toBitVec.toInt := rfl
  have h3 := Int64.toNat_toBitVec sk
  have h4 : sk.toBitVec.toNat < 2 ^ 64 := sk.toBitVec.isLt
  split at e <;> omega

theorem i64_toInt_ofNat (k : Nat) (h : k < 2 ^ 62) : (Int64.ofNat k).toInt = k := by
  have e := BitVec.toInt_eq_toNat_cond (Int64.ofNat k).toBitVec
  have h2 : (Int64.ofNat k).toInt = (Int64.ofNat k).toBitVec.toInt := rfl
  have h3 : (Int64.ofNat k).toBitVec.toNat = k % 2 ^ 64 := by simp
  split at e <;> omega

/-- The batch of `gz_zero`: `min(size, skip)` (`GT_OFF` is false on LP64). -/
theorem zero_n (sz : UInt32) (sk : Int64) (h1 : 8 ≤ sz.toNat) (h2 : sz.toNat ≤ 2 ^ 30) (h3 : 0 < sk.toInt) :
    1 ≤ (if GT_OFF sz || Int64.ofNat sz.toNat > sk then sk.toUInt64.toUInt32 else sz).toNat ∧
    (if GT_OFF sz || Int64.ofNat sz.toNat > sk then sk.toUInt64.toUInt32 else sz).toNat ≤ sz.toNat ∧
    ((if GT_OFF sz || Int64.ofNat sz.toNat > sk then sk.toUInt64.toUInt32 else sz).toNat : Int) ≤ sk.toInt := by
  have e1 : (Int64.ofNat sz.toNat).toInt = sz.toNat := i64_toInt_ofNat _ (by omega)
  by_cases hc : Int64.ofNat sz.toNat > sk
  · have hlt : sk.toInt < sz.toNat := by rw [← e1]; exact Int64.lt_iff_toInt_lt.mp hc
    have : sk.toUInt64.toUInt32.toNat = sk.toInt.toNat := by
      rw [UInt64.toNat_toUInt32]
      have : sk.toUInt64.toNat = sk.toInt.toNat := by
        exact i64_toNat_toUInt64 sk (by omega)
      omega
    simp only [GT_OFF, hc, decide_true, Bool.or_true, ite_true, this]
    omega
  · have hle : (sz.toNat : Int) ≤ sk.toInt := by
      rw [← e1]; exact Int64.le_iff_toInt_le.mp (Int64.not_lt.mp hc)
    simp only [GT_OFF, hc, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    omega

/-- The fields of a write handle that `gz_zero` keeps (it moves `skip` to `x.pos`). -/
structure ZFix (s s' : GzState) : Prop where
  want : s'.want = s.want
  direct : s'.direct = s.direct
  mode : s'.mode = s.mode
  level : s'.level = s.level
  strategy : s'.strategy = s.strategy
  fd : s'.fd = s.fd
  strm : s'.strm = s.strm

theorem ZFix.refl (s : GzState) : ZFix s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ZFix.trans {s1 s2 s3 : GzState} (a : ZFix s1 s2) (b : ZFix s2 s3) : ZFix s1 s3 :=
  ⟨b.1.trans a.1, b.2.trans a.2, b.3.trans a.3, b.4.trans a.4, b.5.trans a.5, b.6.trans a.6, b.7.trans a.7⟩

theorem ZFix.of_w {s s' : GzState} (a : WFix s s') : ZFix s s' :=
  ⟨a.want, a.direct, a.mode, a.level, a.strategy, a.fd, a.strm⟩

theorem liftM_get_val {α : Type} (p : α) (w : World) (h : Heap) :
    (liftM (Ival.get (Ival.val p)) : G α) w h = .ok ((p, w), h) := by
  simp [Ival.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, pure, StateT.pure]

theorem chkI64_ok {v : Int} (h1 : -(2 ^ 63 : Int) ≤ v) (h2 : v < 2 ^ 63) (h : Heap) :
    chkI64 v h = .ok (Int64.ofInt v, h) := by
  unfold chkI64; rw [ite_eq_left_iff.mpr (fun hc => absurd ⟨h1, h2⟩ hc)]; rfl

/-- The fields of a write handle with new positions that `GzPos` allows. -/
theorem shape_posW {h : Heap} {s : GzState} (sh : GzShape h s) (hw : s.mode = GZ_WRITE) (p k : Int64)
    (hp : GzPos { s with pos := p, skip := k }) : GzShape h { s with pos := p, skip := k } := by
  refine ⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, sh.size, hp, ⟨sh.msg.1, sh.msg.2⟩,
    fun hr => absurd (hw.symm.trans hr) write_ne_read, fun _ => ?_, sh.dead⟩
  have Wr := sh.write hw
  refine ⟨fun hsz => ?_, Wr.nobuf, Wr.have0⟩
  obtain ⟨c, base, z, hB, hz, WB⟩ := Wr.bufs hsz
  exact ⟨c, base, z, ⟨hB.size, hB.buffers, hB.inp, hB.out, hB.fits, hB.hdr⟩, hz,
    ⟨WB.deflate, WB.nohdr, WB.inp, WB.nostate, WB.out⟩⟩

theorem zero_tail_pre (C : GzCompSpec) (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (hsz : s1.size ≠ 0) (n : UInt32)
    (hn1 : n.toNat ≤ s1.size.toNat) (hn2 : (n.toNat : Int) ≤ s1.skip.toInt) (first : Int32) :
    GSat W H (zeroTail (some b) (some s1.strm) n first) (fun r W' H' => ∃ s2, W'.gz H' b = some s2 ∧
      GzInvWS W' H' (some b) ∧ GStep W H W' H' b [] ∧ ZFix s1 s2 ∧ s2.size ≠ 0 ∧
      s2.pos.toInt + s2.skip.toInt = s1.pos.toInt + s1.skip.toInt ∧ s2.skip.toInt = s1.skip.toInt - n.toNat ∧
      r.1 = first ∧ (r.2 = .go ∨ r.2 = .ret)) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  have hP := sh.pos
  unfold zeroTail
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := setZ H s1.strm { z with avail_in := n })
    (by simp [lm_app, wrZ_app hz]) ?_)
  have hs1 : W.gz (setZ H s1.strm { z with avail_in := n }) b = some s1 := hs
  refine GSat.bind (GSat.of_eq (ldGz_app hs1) ?_)
  rw [hB.inp]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W)
    (h' := setZ H s1.strm { z with next_in := .ref (.heap c) base, avail_in := n })
    (by simp [lm_app, wrZ_app (setZ_streams_same H s1.strm _), InflateInv.upd_upd]) ?_)
  obtain ⟨hv2, hs2, g2⟩ := invWS_setIn hv hs hsz hz (.ref (.heap c) base) n (fun c' base' hb => by
    have e := hb.buffers; rw [hB.buffers] at e; cases e
    exact Or.inl ⟨0, by simp, Nat.le_refl _, by omega⟩)
  have hsk0 := hP.skip_nonneg
  have hps := hP.pos_skip
  have hpl := hP.pos_lower
  have hpw := hP.write_pos hwm
  have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
  refine GSat.bind (GSat.of_eq (rdG_app' hs2 _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (s1.pos.toInt + n.toNat))
    (by simp only [lm_app, chkI64_ok (v := s1.pos.toInt + n.toNat) (by omega) (by omega)]; rfl) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app hs2 _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' (gz_upd_same hs2 _) _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (s1.skip.toInt - n.toNat))
    (by simp only [lm_app, chkI64_ok (v := s1.skip.toInt - n.toNat) (by omega) (by omega)]; rfl) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same hs2 _) _) ?_)
  simp only [InflateInv.upd_upd]
  have hp1 : (Int64.ofInt (s1.pos.toInt + n.toNat)).toInt = s1.pos.toInt + n.toNat :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  have hk1 : (Int64.ofInt (s1.skip.toInt - n.toNat)).toInt = s1.skip.toInt - n.toNat :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  obtain ⟨sh2, hn2'⟩ := inv_of hs2 hv2.1
  have sh3 := shape_posW sh2 hwm (Int64.ofInt (s1.pos.toInt + n.toNat)) (Int64.ofInt (s1.skip.toInt - n.toNat))
    ⟨by dsimp only; rw [hk1]; omega, by dsimp only; rw [hp1, hk1]; omega, by dsimp only; rw [hp1]; omega,
      fun _ => by dsimp only; rw [hp1]; omega⟩
  obtain ⟨hv3, hs3, g3⟩ := invWS_store hv2 hs2 sh3 hn2' hwm rfl (fun c' hc _ => by
    simp only [GzOwned, gz_upd_same hs2, hs2] at hc ⊢; exact hc)
  refine GSat.bind (GSat.mono (comp_inv C G hv3 hs3 _) fun r W4 H4 q => ?_)
  obtain ⟨s4, z4, hs4, hz4, hv4, g4, fx, hsz4, -, -⟩ := q
  have g := (g2.trans g3 ⟨s1, hs⟩ ⟨s1, hs2⟩).trans g4 ⟨s1, hs⟩ ⟨_, hs3⟩
  have hsz' : s4.size ≠ 0 := by rw [hsz4 hsz]; exact hsz
  have z34 := ZFix.of_w fx
  have zf : ZFix s1 s4 := ⟨z34.want, z34.direct, z34.mode, z34.level, z34.strategy, z34.fd, z34.strm⟩
  have e1 : s4.pos.toInt = s1.pos.toInt + n.toNat := by rw [fx.pos]; exact hp1
  have e2 : s4.skip.toInt = s1.skip.toInt - n.toNat := by rw [fx.skip]; exact hk1
  refine GSat.ite (fun _ => GSat.pure ⟨s4, hs4, hv4, g, zf, hsz', by omega, e2, rfl, Or.inr rfl⟩)
    (fun _ => GSat.pure ⟨s4, hs4, hv4, g, zf, hsz', by omega, e2, rfl, Or.inl rfl⟩)

/-- What a round of the loop of `gz_zero` leaves. -/
def ZRound (W : World) (H : Heap) (b : Nat) (s1 : GzState) (W' : World) (H' : Heap) : Prop :=
  ∃ s2, W'.gz H' b = some s2 ∧ GzInvWS W' H' (some b) ∧ GStep W H W' H' b [] ∧ ZFix s1 s2 ∧ s2.size ≠ 0 ∧
    s2.pos.toInt + s2.skip.toInt = s1.pos.toInt + s1.skip.toInt ∧ s2.skip.toInt < s1.skip.toInt

theorem zero_body (C : GzCompSpec) (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (hsz : s1.size ≠ 0) (hsk : 0 < s1.skip.toInt)
    (st : Int32 × Ctl) :
    GSat W H (zeroBody (some b) (some s1.strm) st) (fun r W' H' => ZRound W H b s1 W' H' ∧
      (r.2 = .go ∨ r.2 = .ret)) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
  obtain ⟨hn1, hn2, hn3⟩ := zero_n s1.size s1.skip (by rw [hsw]; exact sh.want_lo) (by rw [hsw]; exact sh.want_hi) hsk
  have tail : ∀ (H' : Heap) (first : Int32), GzInvWS W H' (some b) → W.gz H' b = some s1 → GStep W H W H' b [] →
      GSat W H' (zeroTail (some b) (some s1.strm)
        (if GT_OFF s1.size || Int64.ofNat s1.size.toNat > s1.skip then s1.skip.toUInt64.toUInt32 else s1.size) first)
        (fun r W' H'' => ZRound W H b s1 W' H'' ∧ (r.2 = .go ∨ r.2 = .ret)) := by
    intro H' first hv' hs' g'
    refine GSat.mono (zero_tail_pre C G hv' hs' hsz _ hn2 hn3 first) fun r W2 H2 q => ?_
    obtain ⟨s2, hs2, hv2, g2, zf, hsz2, hps, hk, -, hr⟩ := q
    exact ⟨⟨s2, hs2, hv2, g'.trans g2 ⟨s1, hs⟩ ⟨s1, hs'⟩, zf, hsz2, hps, by omega⟩, hr⟩
  unfold zeroBody
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => ?_) (fun _ => tail H _ hv hs (GStep.refl W H b []))
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  rw [hB.inp]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  obtain ⟨d, hd, hds⟩ := hB.fits
  have hin : inSize s1 = 2 * s1.want.toNat := by simp [inSize, hwm]
  obtain ⟨H1, e1, x1⟩ := memset_hbuf (off := base) hd 0 (if GT_OFF s1.size || Int64.ofNat s1.size.toNat > s1.skip
    then s1.skip.toUInt64.toUInt32 else s1.size).toNat (by have := sh.want_hi; simp only [outSize, hwm] at hds; omega)
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := H1) (by rw [lm_app, e1]) ?_)
  obtain ⟨hcb, hp, hst, hown⟩ := bufBlk hs hn hsz hB
  obtain ⟨hv1, hs1, g1⟩ := invWS_hbuf hv hs x1 hcb hp hst hown
  exact tail H1 _ hv1 hs1 g1

/-- What `gz_zero` leaves (see the module comment). -/
def ZeroPost (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  ∃ s', W.gz H b = some s' ∧ GzInvWS W H (some b) ∧ GStep w h W H b [] ∧ ZFix s s' ∧ (r = 0 ∨ r = -1) ∧
    (r = 0 → s'.skip = 0 ∧ s'.size ≠ 0)

/-- **The loop of `gz_zero`**: from a write handle with buffers and a pending skip, it ends with no skip, or after a
failed `gz_comp`; `x.pos + skip` and the invariant stay. -/
theorem zero_loop (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (zf : ZFix s s1)
    (hsz : s1.size ≠ 0) (hsk : s1.skip ≠ 0) (hs0 : ∃ s0, w.gz h b = some s0) (first : Int32) :
    GSat W H (gdoWhile (zeroBody (some b) (some s.strm)) (zeroCond (some b)) (first, Ctl.go))
      (fun lp W' H' => ∃ s2, W'.gz H' b = some s2 ∧ GzInvWS W' H' (some b) ∧ GStep w h W' H' b [] ∧ ZFix s s2 ∧
        s2.size ≠ 0 ∧ (lp.2 = .go → s2.skip = 0) ∧ (lp.2 = .go ∨ lp.2 = .ret)) := by
  have pos0 : ∀ {W : World} {H : Heap} {s2 : GzState}, GzInvWS W H (some b) → W.gz H b = some s2 →
      0 ≤ s2.skip.toInt := fun hv hs => (GzInv.pos hs hv.1).skip_nonneg
  refine gsat_gdoWhile (fun st W H => st.2 = .go ∧ ∃ s1, W.gz H b = some s1 ∧ GzInvWS W H (some b) ∧
      GStep w h W H b [] ∧ ZFix s s1 ∧ s1.size ≠ 0 ∧ s1.skip ≠ 0)
    (fun _ W H => match W.gz H b with | some s1 => s1.skip.toInt.toNat | none => 0) _ ?_
    ⟨rfl, s1, hs, hv, g, zf, hsz, hsk⟩ ?_
  · rintro st W1 H1 ⟨-, s2, hs2, hv2, g2, zf2, hsz2, hsk2⟩
    have hk : 0 < s2.skip.toInt := by
      have := pos0 hv2 hs2
      rcases Int.lt_or_eq_of_le this with h' | h'
      · exact h'
      · exact absurd (Int64.toInt_inj.mp (by rw [← h']; rfl)) hsk2
    rw [← zf2.strm]
    refine GSat.mono (zero_body C G hv2 hs2 hsz2 hk st) fun r W3 H3 q => ?_
    obtain ⟨⟨s3, hs3, hv3, g3, zf3, hsz3, hps3, hlt3⟩, hr⟩ := q
    have g' := g2.trans g3 hs0 ⟨s2, hs2⟩
    unfold zeroCond
    have h0 := pos0 hv3 hs3
    rcases hr with hr | hr
    · refine GSat.ite (fun hc => by simp [hr] at hc) (fun _ => ?_)
      refine GSat.bind (GSat.of_eq (rdG_app' hs3 _) ?_)
      refine GSat.pure ⟨fun e => ⟨⟨hr, s3, hs3, hv3, g', zf2.trans zf3, hsz3, by simpa using e⟩, ?_⟩,
        fun e => ⟨s3, hs3, hv3, g', zf2.trans zf3, hsz3, fun _ => by simpa using e, Or.inl hr⟩⟩
      simp only [hs3, hs2]
      omega
    · refine GSat.ite (fun _ => GSat.pure ⟨fun e => by simp at e, fun _ => ⟨s3, hs3, hv3, g', zf2.trans zf3, hsz3,
        fun e => by simp [hr] at e, Or.inr hr⟩⟩) (fun hc => by simp [hr] at hc)
  · simp only [hs]
    have : s1.skip.toInt < 2 ^ 63 := s1.skip.toInt_lt
    unfold fuel; omega

/-- `gz_zero` after the buffers are made (copied from the translation). -/
def zeroRest (state : GzPtr) (strm : StreamPtr) : G Int32 := do
  if (← lm (ZlibNg.Inflate.rdZ strm (·.avail_in))) != 0 then
    if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
      return -1
  let lp ← gdoWhile (zeroBody state strm) (zeroCond state) ((1 : Int32), Ctl.go)
  if lp.2 == .ret then
    return -1
  return 0

theorem gz_zero_eq' (state : GzPtr) : gz_zero state = (do
    let strm ← strmOf state
    if (← rdG state (·.size)) == 0 then
      if (← gz_write_init state) == -1 then
        return -1
    zeroRest state strm) := rfl

theorem zero_rest (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (zf : ZFix s s1)
    (hsz : s1.size ≠ 0) (hsk : s1.skip ≠ 0) (hs0 : ∃ s0, w.gz h b = some s0) :
    GSat W H (zeroRest (some b) (some s.strm)) (ZeroPost w h b s) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨z, hz⟩ := sh.strm
  have loop : ∀ {W2 : World} {H2 : Heap} {s2 : GzState}, GzInvWS W2 H2 (some b) → W2.gz H2 b = some s2 →
      GStep w h W2 H2 b [] → ZFix s s2 → s2.size ≠ 0 → s2.skip ≠ 0 →
      GSat W2 H2 (do
        let lp ← gdoWhile (zeroBody (some b) (some s.strm)) (zeroCond (some b)) ((1 : Int32), Ctl.go)
        if lp.2 == .ret then
          return -1
        return 0) (ZeroPost w h b s) := by
    intro W2 H2 s2 hv2 hs2 g2 zf2 hsz2 hsk2
    refine GSat.bind (GSat.mono (zero_loop C G hv2 hs2 g2 zf2 hsz2 hsk2 hs0 1) fun lp W3 H3 q => ?_)
    obtain ⟨s3, hs3, hv3, g3, zf3, hsz3, hgo, hr⟩ := q
    refine GSat.ite (fun _ => GSat.pure ⟨s3, hs3, hv3, g3, zf3, Or.inr rfl, fun e => by simp at e⟩)
      (fun hc => GSat.pure ⟨s3, hs3, hv3, g3, zf3, Or.inl rfl, fun _ => ⟨hgo ?_, hsz3⟩⟩)
    rcases hr with hr | hr
    · exact hr
    · simp [hr] at hc
  unfold zeroRest
  rw [← zf.strm]
  refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  refine GSat.ite (fun _ => ?_) (fun _ => by rw [zf.strm]; exact loop hv hs g zf hsz hsk)
  refine GSat.bind (GSat.mono (comp_inv C G hv hs _) fun r W2 H2 q => ?_)
  obtain ⟨s2, z2, hs2, hz2, hv2, g2, fx, hsz2, hr, -⟩ := q
  have g' := g.trans g2 hs0 ⟨s1, hs⟩
  have zf2 : ZFix s s2 := zf.trans (ZFix.of_w fx)
  refine GSat.ite (fun _ => GSat.pure ⟨s2, hs2, hv2, g', zf2, Or.inr rfl, fun e => by simp at e⟩) (fun _ => ?_)
  rw [zf.strm]
  exact loop hv2 hs2 g' zf2 (by rw [hsz2 hsz]; exact hsz) (by rw [fx.skip]; exact hsk)

/-- **`gz_zero`** on a write handle with a pending skip. -/
theorem gz_zero_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (hsk : s.skip ≠ 0) :
    GSat w h (gz_zero (some b)) (ZeroPost w h b s) := by
  rw [gz_zero_eq']
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  by_cases hz : s.size = 0
  · refine GSat.ite (fun _ => ?_) (fun hc => by simp [hz] at hc)
    refine GSat.bind (GSat.mono (gz_write_init_spec G hv hs hz) fun r W H q => ?_)
    obtain ⟨s', hs', hv', g, -, fx, hr⟩ := q
    refine GSat.ite (fun _ => GSat.pure ⟨s', hs', hv', g, ZFix.of_w fx, Or.inr rfl, fun e => by simp at e⟩)
      (fun hc => ?_)
    rcases hr with ⟨rfl, hsz⟩ | rfl
    · exact zero_rest C G hv' hs' g (ZFix.of_w fx) hsz (by rw [fx.skip]; exact hsk) ⟨s, hs⟩
    · simp at hc
  · refine GSat.ite (fun hc => by simp at hc; exact absurd hc hz) (fun _ => ?_)
    exact zero_rest C G hv hs (GStep.refl w h b []) (ZFix.refl s) hz hsk ⟨s, hs⟩

end ZlibNgF.Proof.GzWrite
