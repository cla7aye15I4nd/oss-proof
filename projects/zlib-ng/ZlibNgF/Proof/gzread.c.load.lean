import ZlibNgF.Proof.«gzlib.c.error»

/-!
# `read` and `gz_load` (`ZlibNgF`)

`read(fd, buf, n)` returns `-1` or at most `n` bytes, stores only into `[buf, buf + n)` and lowers the read budget at
most (`FsRd`). `gz_load` loops while it reads bytes and has room, so it stops after at most `len` reads.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-! ## The file system after reads -/

/-- `fs'` has at most the read budget and the `lseek` oracle of `fs`, and its files are files of `fs` or empty. -/
def FsRd (fs fs' : Fs) : Prop :=
  fs'.budget ≤ fs.budget ∧ fs'.lseekChoice = fs.lseekChoice ∧ ∀ d ∈ fs'.nodes, d ∈ fs.nodes ∨ d.size = 0

theorem FsRd.refl (fs : Fs) : FsRd fs fs := ⟨Nat.le_refl _, rfl, fun _ hd => Or.inl hd⟩

theorem FsRd.trans {a b c : Fs} (x : FsRd a b) (y : FsRd b c) : FsRd a c := by
  refine ⟨Nat.le_trans y.1 x.1, y.2.1.trans x.2.1, fun d hd => ?_⟩
  rcases y.2.2 d hd with e | e
  · exact x.2.2 d e
  · exact Or.inr e

theorem FsRd.of_le {a b : Fs} (x : GzOpen.FsLe a b) : FsRd a b := ⟨Nat.le_of_eq x.1, x.2.1, x.2.2⟩

theorem readReg_rd (fs : Fs) (fd : Int32) (n : UInt64) : FsRd fs (fs.readReg fd n).2.2 := by
  unfold Fs.readReg
  split
  · split
    · exact ⟨Nat.le_refl _, rfl, fun _ hd => Or.inl hd⟩
    · exact FsRd.of_le (GzOpen.setFd_le _ _ _)
  · exact ⟨Nat.le_refl _, rfl, fun _ hd => Or.inl hd⟩

theorem readCall_rd (fs : Fs) (fd : Int32) (n : UInt64) : FsRd fs (fs.readCall fd n).2.2 := by
  unfold Fs.readCall
  simp only
  split
  · exact readReg_rd _ _ _
  · exact ⟨Nat.le_refl _, rfl, fun _ hd => Or.inl hd⟩
  · exact readReg_rd _ _ _
  · exact ⟨by simp [Fs.tick], rfl, fun _ hd => Or.inl hd⟩

/-- The result of a regular read: `-1` with no bytes, or `k ≤ n` bytes. -/
def ReadRes (n : Nat) (r : Int64) (bs : Array UInt8) : Prop :=
  (r = -1 ∧ bs = #[]) ∨ (0 ≤ r.toInt ∧ r.toInt ≤ n ∧ bs.size ≤ n)

theorem readRes_k {n k : Nat} (hk : k ≤ n) (hn : n < 2 ^ 63) (bs : Array UInt8) (hb : bs.size ≤ n) :
    ReadRes n (Int64.ofNat k) bs := by
  right
  have : (Int64.ofNat k).toInt = k := by
    rw [Int64.toInt_ofNat_of_lt (by omega)]
  rw [this]; exact ⟨by omega, by omega, hb⟩

theorem readReg_res (fs : Fs) (fd : Int32) (n : UInt64) (hn : n.toNat < 2 ^ 63) :
    ReadRes n.toNat (fs.readReg fd n).1 (fs.readReg fd n).2.1 := by
  unfold Fs.readReg
  split
  · split
    · exact Or.inl ⟨rfl, rfl⟩
    · exact readRes_k (Nat.min_le_left _ _) hn _ (by simp; omega)
  · exact Or.inl ⟨rfl, rfl⟩

theorem readCall_res (fs : Fs) (fd : Int32) (n : UInt64) (hn : n.toNat < 2 ^ 63) :
    ReadRes n.toNat (fs.readCall fd n).1 (fs.readCall fd n).2.1 := by
  unfold Fs.readCall
  simp only
  split
  · exact readReg_res _ _ _ hn
  · exact Or.inl ⟨rfl, rfl⟩
  · next k _ =>
    have h1 : (min n (UInt64.ofNat k)).toNat ≤ n.toNat := by
      rw [UInt64.min_def]; split
      · exact Nat.le_refl _
      · next hl => have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl); omega
    rcases readReg_res fs.tick fd (min n (UInt64.ofNat k)) (by omega) with e | ⟨e1, e2, e3⟩
    · exact Or.inl e
    · exact Or.inr ⟨e1, by omega, by omega⟩
  · next bs _ =>
    exact readRes_k (Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)) hn _
      (by simp; omega)

theorem wfr_fs {w : World} {h : Heap} (hw : GzWFr w h) {fs' : Fs} (hf : FsRd w.fs fs') :
    GzWFr { w with fs := fs' } h := by
  obtain ⟨hc, hd, hgz, hst, hb, hn, hlk, hL⟩ := hw
  refine ⟨hc, hd, hgz, hst, by have := hf.1; show fs'.budget < _; omega, fun d hd' => ?_, by rw [hf.2.1]; exact hlk, hL⟩
  rcases hf.2.2 d hd' with e | e
  · exact hn d e
  · omega

/-! ## Stores into one block -/

/-- `H'` is `H` with only the bytes of block `cb` changed, inside `[lo, hi)`, and the block keeps its size. -/
def HBuf (H H' : Heap) (cb lo hi : Nat) : Prop :=
  ∃ t, H' = { H with bytes := t } ∧ (∀ c, c ≠ cb → t c = H.bytes c) ∧ (H.bytes cb = none → t cb = none) ∧
    ∀ a, H.bytes cb = some a → ∃ a', t cb = some a' ∧ a'.size = a.size ∧ ∀ j, (j < lo ∨ hi ≤ j) → a'[j]! = a[j]!

theorem HBuf.refl (H : Heap) (cb lo hi : Nat) : HBuf H H cb lo hi :=
  ⟨H.bytes, rfl, fun _ _ => rfl, fun e => e, fun a e => ⟨a, e, rfl, fun _ _ => rfl⟩⟩

theorem HBuf.trans {H1 H2 H3 : Heap} {cb lo hi lo' hi' : Nat} (x : HBuf H1 H2 cb lo hi) (y : HBuf H2 H3 cb lo' hi')
    (hl : lo ≤ lo') (hh : hi' ≤ hi) : HBuf H1 H3 cb lo hi := by
  obtain ⟨t1, rfl, n1, z1, s1⟩ := x
  obtain ⟨t2, rfl, n2, z2, s2⟩ := y
  refine ⟨t2, rfl, fun c hc => (n2 c hc).trans (n1 c hc), fun e => z2 (z1 e), fun a ha => ?_⟩
  obtain ⟨a1, e1, sz1, q1⟩ := s1 a ha
  obtain ⟨a2, e2, sz2, q2⟩ := s2 a1 e1
  exact ⟨a2, e2, sz2.trans sz1, fun j hj => (q2 j (by omega)).trans (q1 j hj)⟩

theorem HBuf.store {H : Heap} {cb off cap : Nat} {a bs : Array UInt8} (ha : H.bytes cb = some a)
    (hc : off + cap ≤ a.size) (hb : bs.size ≤ cap) :
    HBuf H { H with bytes := H.bytes.modify cb (Option.map fun _ => GzOpen.stored a bs off) } cb off (off + cap) := by
  have hg := GzOpen.modify_some H.bytes cb a (fun _ => GzOpen.stored a bs off) ha
  refine ⟨H.bytes.modify cb (Option.map fun _ => GzOpen.stored a bs off), rfl, fun c hc' => (by rw [hg]; simp [hc']),
    fun e => (by rw [ha] at e; cases e), fun a' ha' => ?_⟩
  rw [ha] at ha'; cases ha'
  refine ⟨GzOpen.stored a bs off, by rw [hg]; simp, GzOpen.stored_size _ _ _ (by omega), fun j hj => ?_⟩
  rw [GzOpen.stored_get _ _ _ (by omega)]
  have : ¬(off ≤ j ∧ j < off + bs.size) := by omega
  simp [this]

/-- The fields of a read handle after stores into one block that is neither its `path` nor the block of its stream's
state (the buffer block, or a block outside the file): only the bytes of that block change, and the block keeps
its size and liveness. -/
theorem shape_hbuf {h H : Heap} {cb lo hi : Nat} {s : GzState} (sh : GzShape h s) (hr : s.mode = GZ_READ)
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
    sh.size, sh.pos, ⟨?_, sh.msg.mem⟩, fun _ => ?_, fun hw => absurd (hr.symm.trans hw) read_ne_write, fun hz c hc => ?_⟩
  · rcases sh.msg.msg with e | ⟨c, d, e, hd⟩
    · exact Or.inl e
    · obtain ⟨d', e1, -⟩ := hlive c d hd; exact Or.inr ⟨c, d', e, e1⟩
  · have R := sh.read hr
    refine ⟨R.how, fun hsz' => ?_, R.nobuf, R.skip_have, R.fresh⟩
    obtain ⟨c, base, z, hB, hi, hz, hhv, hai, hreg, hmsg⟩ := R.bufs hsz'
    obtain ⟨i, z0, sb, st, al, e, hz0, hsb, hst0, hal, core⟩ := hi
    cases e
    rw [hz] at hz0; cases hz0
    have hsbne : sb ≠ cb := fun e => hst (e ▸ stBlk_of hz hsb)
    have hcs : InflateInv.Inv { h with bytes := t } (some s.strm) :=
      InflateReach.caller_inv ⟨s.strm, z, sb, st, al, rfl, hz, hsb, hst0, hal, core⟩
        ⟨s.strm, z, z, sb, rfl, hz, hz, hsb, rfl, hne sb hsbne, rfl, rfl,
          fun k g hr' _ => absurd (hreg _ hr') (by simp), rfl, Nat.le_refl _⟩
    refine ⟨c, base, z, hbufs c base hB, hcs, hz, hhv, hai, fun hp' hr' => hreg hp' ?_, hmsg⟩
    obtain ⟨sb', st', ⟨z', ⟨i', e', hz'⟩, hsb'⟩, hst', hhd⟩ := hr'
    cases e'
    change h.streams s.strm = some z' at hz'
    rw [hz] at hz'; cases hz'
    rw [hsb] at hsb'; cases hsb'
    refine ⟨sb, st', ⟨z, ⟨_, rfl, hz⟩, hsb⟩, ?_, hhd⟩
    have e1 : t sb = h.bytes sb := hne sb hsbne
    simp only [Heap.istate, e1] at hst' ⊢; exact hst'
  · obtain ⟨h1, h2⟩ := sh.dead hz c hc
    refine ⟨?_, h2⟩
    by_cases e : c = cb
    · subst e; exact hnone h1
    · show t c = none; rw [hne c e]; exact h1

theorem stored_nil (a : Array UInt8) (off : Nat) : GzOpen.stored a #[] off = a := rfl

/-- `read(fd, buf, n)` into `n` bytes of a live heap block. -/
theorem readG_spec {W : World} {H : Heap} {cb p : Nat} {a : Array UInt8} (ha : H.bytes cb = some a) (fd : Int32)
    (n : UInt64) (hp : p + n.toNat ≤ a.size) (hn : n.toNat < 2 ^ 63) :
    GSat W H (readG fd (.ref (.heap cb) p) n) (fun r W' H' => W' = { W with fs := (W.fs.readCall fd n).2.2 } ∧
      r = (W.fs.readCall fd n).1 ∧ HBuf H H' cb p (p + n.toNat)) := by
  have hres := readCall_res W.fs fd n hn
  generalize hR : W.fs.readCall fd n = R at hres ⊢
  obtain ⟨r, bs, fs'⟩ := R
  have hb : 0 < r → bs.size ≤ n.toNat := by
    intro hr; rcases hres with ⟨rfl, -⟩ | ⟨-, -, e⟩
    · exact absurd hr (by decide)
    · exact e
  -- the store of the second `storeBytes`, on a heap whose block `cb` holds `a`
  have st2 : ∀ H0 : Heap, H0.bytes cb = some a → HBuf H H0 cb p (p + n.toNat) → 0 < r →
      ∃ H1, storeBytes (.ref (.heap cb) p) bs n.toNat H0 = .ok ((), H1) ∧ HBuf H H1 cb p (p + n.toNat) := by
    intro H0 ha0 x0 hr
    exact ⟨_, GzOpen.storeBytes_heap ha0 hp (hb hr), x0.trans (HBuf.store ha0 hp (hb hr)) (Nat.le_refl _) (Nat.le_refl _)⟩
  have e0 := GzOpen.storeBytes_heap ha hp (bs := #[]) (by simp)
  have x0 := HBuf.store ha hp (bs := #[]) (by simp)
  have ha0 : ({ H with bytes := H.bytes.modify cb (Option.map fun _ => GzOpen.stored a #[] p) } : Heap).bytes cb =
      some a := by
    show (H.bytes.modify _ _) cb = _; rw [GzOpen.modify_some _ _ _ _ ha]; simp [stored_nil]
  generalize { H with bytes := H.bytes.modify cb (Option.map fun _ => GzOpen.stored a #[] p) } = H0 at e0 x0 ha0
  by_cases hn0 : n = 0
  · have hn0' : (n != 0) = false := by simp [hn0]
    by_cases hr : 0 < r
    · obtain ⟨H1, e1, x1⟩ := st2 H ha (HBuf.refl _ _ _ _) hr
      exact ⟨r, _, H1, by simp [readG, modifyFs, hR, hn0', hr, e1], rfl, rfl, x1⟩
    · exact ⟨r, _, H, by simp [readG, modifyFs, hR, hn0', hr], rfl, rfl, HBuf.refl _ _ _ _⟩
  · have hn0' : (n != 0) = true := by simp [hn0]
    by_cases hr : 0 < r
    · obtain ⟨H1, e1, x1⟩ := st2 H0 ha0 x0 hr
      exact ⟨r, _, H1, by simp [readG, modifyFs, hR, hn0', hr, e0, e1], rfl, rfl, x1⟩
    · exact ⟨r, _, H0, by simp [readG, modifyFs, hR, hn0', hr, e0], rfl, rfl, x0⟩

/-! ## `do ... while` -/

/-- `do body while (cond)` in `G`, with a measure that may read the world and the heap. -/
theorem gsat_gdoWhile {σ : Type} {body : σ → G σ} {cond : σ → G (Bool × σ)} (I : σ → World → Heap → Prop)
    (μ : σ → World → Heap → Nat) (Q : σ → World → Heap → Prop)
    (hstep : ∀ s w h, I s w h → GSat w h (body s) (fun s1 w1 h1 => GSat w1 h1 (cond s1) (fun cs w2 h2 =>
      (cs.1 = true → I cs.2 w2 h2 ∧ μ cs.2 w2 h2 < μ s w h) ∧ (cs.1 = false → Q cs.2 w2 h2))))
    {s : σ} {w : World} {h : Heap} (hI : I s w h) (hμ : μ s w h < fuel) : GSat w h (gdoWhile body cond s) Q := by
  unfold gdoWhile
  suffices ∀ n s w h, I s w h → μ s w h < n → GSat w h (gdoWhile.go body cond n s) Q from this _ s w h hI hμ
  intro n
  induction n with
  | zero => intro s _ _ _ hlt; omega
  | succ n ih =>
    intro s w h hI hlt
    obtain ⟨s1, w1, h1, eb, ⟨c, s2⟩, w2, h2, ec, ht, hf⟩ := hstep s w h hI
    cases c with
    | false => exact ⟨s2, w2, h2, by simp [gdoWhile.go, eb, ec], hf rfl⟩
    | true =>
      obtain ⟨hI2, hμ2⟩ := ht rfl
      obtain ⟨s', w', h', eg, q⟩ := ih s2 w2 h2 hI2 (by simp only at hμ2; omega)
      exact ⟨s', w', h', by simp [gdoWhile.go, eb, ec, eg], q⟩

/-! ## `strerror` -/

theorem cstr_push0 {h : Heap} {r : BRef} {a : Array UInt8} (hr : Space.get h r = some (a.push 0)) :
    CStr h (.ref r 0) := by
  cases hf : (a.push 0).findIdx? (· == 0) with
  | none =>
    rw [Array.findIdx?_eq_none_iff] at hf
    have := hf 0 (by simp)
    simp at this
  | some i =>
    rw [Array.findIdx?_eq_some_iff_getElem] at hf
    obtain ⟨hi, hz, hb⟩ := hf
    refine ⟨i, r, 0, a.push 0, rfl, hr, by omega, ?_, fun j hj => ?_⟩
    · rw [Nat.zero_add, getElem!_pos (a.push 0) i hi]; simpa using hz
    · rw [Nat.zero_add, getElem!_pos (a.push 0) j (by omega)]
      have := hb j hj; simpa using this

/-- `strerror(errno)`: a new static string. -/
theorem zstrerror_spec (w : World) (h : Heap) :
    ∃ p a, zstrerror w h = .ok ((p, w), { h with consts := upd h.consts h.consts.arr.size (some a) }) ∧
      CStr { h with consts := upd h.consts h.consts.arr.size (some a) } p ∧ ∀ c o, p ≠ .ref (.heap c) o := by
  refine ⟨.ref (.const h.consts.arr.size) 0, (w.strerrorText w.fs.errno).push 0, ?_,
    cstr_push0 (a := w.strerrorText w.fs.errno) (by show (upd _ _ _) _ = _; simp), fun c o e => by cases e⟩
  simp [zstrerror, lm, StateT.lift, newConst, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
    pure, StateT.pure]

/-! ## `gz_error` on an error while `x.have` is being filled -/

/-- A step from the world with `x.have` cleared is a step from the world itself. -/
theorem GStep.of_have0 {w W : World} {h H : Heap} {b : Nat} {s : GzState} {wr : List (BPtr × Nat)}
    (hs : w.gz h b = some s) (x : GStep { w with gzs := upd w.gzs b (some { s with «have» := 0 }) } h W H b wr) :
    GStep w h W H b wr := by
  have hs0 := gz_upd_same hs { s with «have» := 0 }
  have hown : GzOwned { w with gzs := upd w.gzs b (some { s with «have» := 0 }) } h (some b) = GzOwned w h (some b) := by
    simp only [GzOwned, hs0, hs]
  obtain ⟨⟨fr, hc, hg⟩, ho, ht⟩ := x
  refine ⟨⟨?_, hc, fun b' hb' hlt => ?_⟩, fun c hc' hlt => by rw [← hown]; exact ho c hc' hlt, fun s1 s2 e1 e2 => ?_⟩
  · simp only [hs0, hown] at fr; simp only [hs]; exact fr
  · rw [hg b' hb' hlt]
    have : b' ≠ b := fun e => hb' (by rw [e])
    simp [upd_ne _ _ _ _ this]
  · rw [hs] at e1; cases e1; exact ht { s with «have» := 0 } s2 hs0 e2

theorem gz_error_inv0 {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hv : GzInvR { w with gzs := upd w.gzs b (some { s with «have» := 0 }) } h (some b))
    (e : Int32) (he : e ≠ ZlibNg.Inflate.Z_OK ∧ e ≠ ZlibNg.Inflate.Z_BUF_ERROR) (msg : BPtr)
    (hmsg : msg = .null ∨ CStr h msg) (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ W H => ∃ s', W.gz H b = some s' ∧ ErrOf { s with «have» := 0 } e s' ∧
      GzInvR W H (some b) ∧ LitOk W H ∧ W.fs = w.fs ∧ GStep w h W H b []) := by
  have hs0 := gz_upd_same hs { s with «have» := 0 }
  have hv' := hv
  obtain ⟨⟨b0, s0, e0, hs00, sh, hn⟩, -, -⟩ := hv'
  cases e0; rw [hs0] at hs00; cases hs00
  have hm : GzMsg h s := ⟨sh.msg.1, sh.msg.2⟩
  have hbc : ∀ c o, s.msg = .val (.ref (.heap c) o) → c ≠ b := msg_ne_b hn
  have hE : errSt { s with «have» := 0 } e = errSt s e := by simp [errSt, he]
  have e1 : gz_error (some b) e msg w h =
      gz_error (some b) e msg { w with gzs := upd w.gzs b (some { s with «have» := 0 }) } h := by
    rw [gz_error_run hs hm hbc e msg, gz_error_run hs0 sh.msg hbc e msg, hE]
    simp only [InflateInv.upd_upd]
    rfl
  obtain ⟨r, W, H, eq, s', q1, q2, q3, q4, q5, q6⟩ := gz_error_inv hv hs0 e msg hmsg hmk
  exact ⟨r, W, H, by rw [e1]; exact eq, s', q1, q2, q3, q4, q5, GStep.of_have0 hs q6⟩

/-! ## `gz_load` with a local count -/

/-- The body of the read loop of `gz_load` with `toX = false` (copied from the translation). -/
def loadBody (state : GzPtr) (buf : BPtr) (len : UInt32) (s : LoadLoop) : G LoadLoop := do
  let h0 ← (pure s.hv : G UInt32)
  let ret ← readG (← rdG state (·.fd)) (← lm (buf.add (Int.ofNat h0.toNat))) (len - (← (pure s.hv : G UInt32))).toUInt64
  if ret ≤ 0 then
    return { s with ret := ret, ctl := .brk }
  let hv ← (pure ((← (pure s.hv : G UInt32)) + ret.toUInt64.toUInt32) : G UInt32)
  return { s with ret := ret, hv := hv }

/-- The condition of the read loop of `gz_load` with `toX = false`. -/
def loadCond (len : UInt32) (s : LoadLoop) : G (Bool × LoadLoop) := do
  if s.ctl != .go then return (false, s)
  return ((← (pure s.hv : G UInt32)) < len, s)

open ZlibNg.Inflate in
/-- The part of `gz_load` after the loop. -/
def loadTail (state : GzPtr) (lp : LoadLoop) : G (Int32 × UInt32) := do
  if lp.ret < 0 then
    gz_error state Z_ERRNO (← zstrerror)
    return (-1, lp.hv)
  if lp.ret == 0 then
    wrG state fun s => { s with eof := 1 }
  return (0, lp.hv)

theorem gz_load_false (state : GzPtr) (buf : BPtr) (len : UInt32) : gz_load state buf len false = (do
    let hv ← (pure 0 : G UInt32)
    let lp ← gdoWhile (loadBody state buf len) (loadCond len) ⟨0, hv, .go⟩
    loadTail state lp) := rfl

theorem addH {h : Heap} {c off : Nat} {a : Array UInt8} (ha : h.bytes c = some a) (k : Nat) (hk : off + k ≤ a.size) :
    (Ptr.ref (BRef.heap c) off : BPtr).add (Int.ofNat k) h = .ok (.ref (.heap c) (off + k), h) := by
  have hg : Space.get h (BRef.heap c) = some a := ha
  simp only [Ptr.add, hg, Int.ofNat_eq_natCast]
  split
  · congr
  · next hc => exact absurd ⟨by omega, by omega, by omega⟩ hc

theorem HBuf.bytes_ne {H H' : Heap} {cb lo hi : Nat} (x : HBuf H H' cb lo hi) {c : Nat} (hc : c ≠ cb) :
    H'.bytes c = H.bytes c := by
  obtain ⟨t, rfl, hne, -, -⟩ := x; exact hne c hc

theorem HBuf.size {H H' : Heap} {cb lo hi : Nat} (x : HBuf H H' cb lo hi) {a : Array UInt8} (ha : H.bytes cb = some a) :
    ∃ a', H'.bytes cb = some a' ∧ a'.size = a.size := by
  obtain ⟨t, rfl, -, -, hs⟩ := x; obtain ⟨a', e1, e2, -⟩ := hs a ha; exact ⟨a', e1, e2⟩

theorem HBuf.gz {W : World} {H H' : Heap} {cb lo hi b : Nat} (x : HBuf H H' cb lo hi) (hb : b ≠ cb) :
    W.gz H' b = W.gz H b := by
  unfold World.gz; rw [x.bytes_ne hb]

/-- The loop of `gz_load` with `toX = false`: it reads into `[p, p + len)` of block `cb`, lowers the read budget, and
counts at most `len` bytes. -/
theorem loadLoop_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) {cb p : Nat}
    {a : Array UInt8} (ha : h.bytes cb = some a) (len : UInt32) (hp : p + len.toNat ≤ a.size) (hcb : b ≠ cb) :
    GSat w h (gdoWhile (loadBody (some b) (.ref (.heap cb) p) len) (loadCond len) ⟨0, 0, .go⟩)
      (fun lp W H => lp.hv.toNat ≤ len.toNat ∧ ∃ fs', FsRd w.fs fs' ∧ W = { w with fs := fs' } ∧
        HBuf h H cb p (p + len.toNat)) := by
  refine gsat_gdoWhile (fun (st : LoadLoop) W H => st.hv.toNat ≤ len.toNat ∧ ∃ fs', FsRd w.fs fs' ∧
      W = { w with fs := fs' } ∧ HBuf h H cb p (p + len.toNat))
    (fun st _ _ => len.toNat - st.hv.toNat) _ ?_ ⟨by simp, w.fs, FsRd.refl _, rfl, HBuf.refl _ _ _ _⟩
    (by have := len.toNat_lt; simp [fuel]; omega)
  intro st W H ⟨hle, fs', hfs, hW, x⟩
  subst hW
  have hsW : ({ w with fs := fs' } : World).gz H b = some s := by rw [x.gz hcb]; exact hs
  obtain ⟨a1, ha1, hsz⟩ := x.size ha
  unfold loadBody
  refine GSat.bind (GSat.pure ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hsW _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, addH ha1 st.hv.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.pure ?_)
  have hn : (len - st.hv).toUInt64.toNat = len.toNat - st.hv.toNat := by
    rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hle)]
  have hlen := len.toNat_lt
  refine GSat.bind (GSat.mono (readG_spec ha1 s.fd (len - st.hv).toUInt64 (by rw [hn]; omega)
    (by rw [hn]; omega)) fun r W1 H1 q => ?_)
  obtain ⟨rfl, hr, x1⟩ := q
  have x2 : HBuf h H1 cb p (p + len.toNat) := x.trans x1 (by omega) (by rw [hn]; omega)
  have hfs2 : FsRd w.fs (fs'.readCall s.fd (len - st.hv).toUInt64).2.2 := hfs.trans (readCall_rd _ _ _)
  have hres := readCall_res fs' s.fd (len - st.hv).toUInt64 (by rw [hn]; omega)
  rw [← hr, hn] at hres
  apply GSat.ite
  · intro _
    refine GSat.pure (GSat.of_eq rfl ⟨fun e => absurd e (by simp), fun _ => ⟨hle, _, hfs2, rfl, x2⟩⟩)
  · intro hr0
    have h0 : (0 : Int64) ≤ r := by
      rw [Int64.le_iff_toInt_le] at hr0 ⊢; simp at hr0 ⊢; omega
    have hpos : 0 < r.toInt := by
      rw [Int64.le_iff_toInt_le] at hr0; simp at hr0; omega
    have hle2 : r.toInt ≤ (len.toNat - st.hv.toNat : Nat) := by
      rcases hres with ⟨e, -⟩ | ⟨-, e, -⟩
      · rw [e] at hpos; simp at hpos
      · exact e
    have hk : r.toUInt64.toUInt32.toNat = r.toInt.toNat := by
      rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt]; omega
    have hsum : (st.hv + r.toUInt64.toUInt32).toNat = st.hv.toNat + r.toInt.toNat := by
      rw [UInt32.toNat_add, hk]; omega
    refine GSat.bind (GSat.pure ?_)
    refine GSat.bind (GSat.pure ?_)
    refine GSat.pure ?_
    unfold loadCond
    apply GSat.ite
    · intro _
      exact GSat.pure ⟨fun e => absurd e (by simp), fun _ => ⟨by simp only; omega, _, hfs2, rfl, x2⟩⟩
    · intro _
      refine GSat.bind (GSat.pure ?_)
      refine GSat.pure ⟨fun _ => ⟨⟨by simp only; omega, _, hfs2, rfl, x2⟩, by simp only; omega⟩,
        fun _ => ⟨by simp only; omega, _, hfs2, rfl, x2⟩⟩

/-- A read handle stays one after stores into one block that is neither the state's block, its `path`, nor the block
of its stream's state, and reads that lower the read budget. -/
theorem invR_hbuf {w : World} {h H : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) {cb lo hi : Nat} (x : HBuf h H cb lo hi) (hcb : b ≠ cb) (hp : cb ∉ blkOf s.path)
    (hst : cb ∉ stBlk h s) {fs' : Fs} (hf : FsRd w.fs fs') : GzInvR { w with fs := fs' } H (some b) := by
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have hr := modeOf hs hm
  have hsH : ({ w with fs := fs' } : World).gz H b = some s := by rw [x.gz hcb]; exact hs
  have sh' := shape_hbuf sh hr x hp hst
  obtain ⟨t, rfl, hne, hnone, hsz⟩ := x
  refine ⟨⟨b, s, rfl, hsH, sh', hn⟩, ⟨b, s, rfl, hsH, hr⟩, ?_⟩
  have hw' := wfr_fs hw hf
  obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hstr, hb, hn', hlk, hL⟩ := hw'
  refine ⟨hc, ⟨fun c hc' => ⟨(hfr c hc').1, (hfr c hc').2.1, ?_⟩, hdf⟩, hgz, fun c s2 e => ?_, hb, hn', hlk, hL⟩
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

/-! ## `gz_load` into `x.have` -/

/-- `*have` of `gz_load`, read (copied from the translation). -/
def getX (state : GzPtr) (toX : Bool) (hv : UInt32) : G UInt32 := if toX then rdG state (·.«have») else pure hv

/-- `*have = v` of `gz_load` (copied from the translation). -/
def setX (state : GzPtr) (toX : Bool) (v : UInt32) : G UInt32 := do
  if toX then
    wrG state fun s => { s with «have» := v }
    return 0
  else return v

/-- The body of the read loop of `gz_load` (copied from the translation). -/
def loadBodyG (state : GzPtr) (buf : BPtr) (len : UInt32) (toX : Bool) (s : LoadLoop) : G LoadLoop := do
  let h0 ← getX state toX s.hv
  let ret ← readG (← rdG state (·.fd)) (← lm (buf.add (Int.ofNat h0.toNat))) (len - (← getX state toX s.hv)).toUInt64
  if ret ≤ 0 then
    return { s with ret := ret, ctl := .brk }
  let hv ← setX state toX ((← getX state toX s.hv) + ret.toUInt64.toUInt32)
  return { s with ret := ret, hv := hv }

/-- The condition of the read loop of `gz_load` (copied from the translation). -/
def loadCondG (state : GzPtr) (len : UInt32) (toX : Bool) (s : LoadLoop) : G (Bool × LoadLoop) := do
  if s.ctl != .go then return (false, s)
  return ((← getX state toX s.hv) < len, s)

theorem gz_load_eq (state : GzPtr) (buf : BPtr) (len : UInt32) (toX : Bool) : gz_load state buf len toX = (do
    let hv ← setX state toX 0
    let lp ← gdoWhile (loadBodyG state buf len toX) (loadCondG state len toX) ⟨0, hv, .go⟩
    loadTail state lp) := rfl

theorem gzX_upd {w : World} {h H : Heap} {b cb lo hi : Nat} {s : GzState} (hs : w.gz h b = some s)
    (x : HBuf h H cb lo hi) (hcb : b ≠ cb) (fs' : Fs) (s' : GzState) :
    ({ w with fs := fs', gzs := upd w.gzs b (some s') } : World).gz H b = some s' := by
  obtain ⟨d, hd⟩ := gz_live hs
  unfold World.gz; rw [x.bytes_ne hcb, hd]; simp

/-- The loop of `gz_load` with `toX = true`: it reads into `[p, p + len)` of block `cb`, lowers the read budget, and
counts at most `len` bytes in `x.have`. -/
theorem loadLoopX_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) {cb p : Nat}
    {a : Array UInt8} (ha : h.bytes cb = some a) (len : UInt32) (hp : p + len.toNat ≤ a.size) (hcb : b ≠ cb) :
    GSat { w with gzs := upd w.gzs b (some { s with «have» := 0 }) } h
      (gdoWhile (loadBodyG (some b) (.ref (.heap cb) p) len true) (loadCondG (some b) len true) ⟨0, 0, .go⟩)
      (fun _ W H => ∃ k : UInt32, k.toNat ≤ len.toNat ∧ ∃ fs', FsRd w.fs fs' ∧
        W = { w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k }) } ∧ HBuf h H cb p (p + len.toNat)) := by
  refine gsat_gdoWhile (fun (_ : LoadLoop) W H => ∃ k : UInt32, k.toNat ≤ len.toNat ∧ ∃ fs', FsRd w.fs fs' ∧
        W = { w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k }) } ∧ HBuf h H cb p (p + len.toNat))
    (fun _ W _ => match W.gzs b with | some s' => len.toNat - s'.«have».toNat | none => 0) _ ?_
    ⟨0, by simp, w.fs, FsRd.refl _, rfl, HBuf.refl _ _ _ _⟩ (by have := len.toNat_lt; simp [fuel]; omega)
  intro st W H ⟨k, hle, fs', hfs, hW, x⟩
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
  · intro _
    refine GSat.pure ?_
    unfold loadCondG
    exact GSat.pure ⟨fun e => absurd e (by simp), fun _ => ⟨k, hle, _, hfs2, rfl, x2⟩⟩
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
    · intro _
      exact GSat.pure ⟨fun e => absurd e (by simp), fun _ => ⟨_, by omega, _, hfs2, rfl, x2⟩⟩
    · intro _
      refine GSat.bind (GSat.of_eq (rdG_app' hsW2 _) ?_)
      refine GSat.pure ⟨fun _ => ⟨⟨_, by omega, _, hfs2, rfl, x2⟩, ?_⟩,
        fun _ => ⟨_, by omega, _, hfs2, rfl, x2⟩⟩
      simp only [upd_same]
      omega

/-- Stores into a block of the file and a new state that keeps its owned pointers are a step of a call on it. -/
theorem gstep_hbuf {w : World} {h H : Heap} {b cb lo hi : Nat} {s : GzState} (hs : w.gz h b = some s)
    (x : HBuf h H cb lo hi) (hcb : b ≠ cb) (hown : cb ∈ GzOwned w h (some b)) (fs' : Fs) (s' : GzState)
    (hp : s'.path = s.path) (hm : s'.msg = s.msg) (hb : s'.buffers = s.buffers) (ht : s'.strm = s.strm) :
    GStep w h { w with fs := fs', gzs := upd w.gzs b (some s') } H b [] := by
  have hs' := gzX_upd hs x hcb fs' s'
  obtain ⟨t, rfl, hne, -, -⟩ := x
  refine gstep_mk hs hs' ht (fun c hc _ => by simp [upd_ne _ _ _ _ hc]) (fun i _ => rfl) rfl
    (fun c _ hno => ⟨hne c (fun e => hno (e ▸ hown)), rfl, rfl, rfl, rfl⟩) (fun _ _ e => e) rfl rfl rfl
    (Nat.le_refl _) (fun c hc _ => ?_)
  simp only [GzOwned, hs', hs, hp, hm, hb, ht] at hc ⊢
  exact hc

/-- Adding a static string is a step of a call on the file. -/
theorem gstep_lit {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (a : Array UInt8) :
    GStep w h w { h with consts := upd h.consts h.consts.arr.size (some a) } b [] :=
  gstep_mk hs hs rfl (fun _ _ _ => rfl) (fun _ _ => rfl) rfl (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (fun k b e => GzReach.consts_grow h a k b e) rfl rfl rfl (Nat.le_refl _) (fun _ hc _ => hc)

/-- A read handle stays one when a static string is added. -/
theorem invR_lit {w : World} {h : Heap} {f : GzPtr} (hv : GzInvR w h f) (a : Array UInt8) :
    GzInvR w { h with consts := upd h.consts h.consts.arr.size (some a) } f :=
  (keeps_outside (S := fun w h w' h' _ => w' = w ∧ h' = { h with consts := upd h.consts h.consts.arr.size (some a) })
    fun _ _ _ _ _ _ ⟨e1, e2⟩ => ⟨by rw [e1], by rw [e1]; exact GzOpen.FsLe.refl _, Or.inr ⟨a, e2⟩,
      fun l => LitOk.ext l (by rw [e1]) (by rw [e2]; exact fun k b e => GzReach.consts_grow _ a k b e)⟩).1
    _ _ _ _ _ hv ⟨rfl, rfl⟩

theorem have0_self {s : GzState} (h0 : s.«have» = 0) : ({ s with «have» := 0 } : GzState) = s := by
  cases s; simp only at h0; subst h0; rfl

/-- **`gz_load(state, buf, len, &state->x.have)`** on a read handle with `x.have == 0`, reading into `len` bytes of a
block of the file other than its state, `path` and stream state: an error (`-1`, `gz_error` with `Z_ERRNO`; the
handle stays a read handle), or `0` with `x.have` at most `len`, `eof` possibly set, the bytes of `[p, p + len)` of
that block changed and the read budget lowered. -/
theorem gz_load_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) {cb p : Nat} {a : Array UInt8} (ha : h.bytes cb = some a)
    (len : UInt32) (hp : p + len.toNat ≤ a.size) (hcb : b ≠ cb) (hpath : cb ∉ blkOf s.path) (hst : cb ∉ stBlk h s)
    (hown : cb ∈ GzOwned w h (some b)) :
    GSat w h (gz_load (some b) (.ref (.heap cb) p) len true) (fun r W H =>
      (r.1 = -1 ∧ ∃ s', W.gz H b = some s' ∧ ErrOf s Z_ERRNO s' ∧ GzInvR W H (some b) ∧
        GStep w h W H b [] ∧ FsRd w.fs W.fs) ∨
      (r.1 = 0 ∧ ∃ k : UInt32, k.toNat ≤ len.toNat ∧ ∃ (fs' : Fs) (e : Int32), FsRd w.fs fs' ∧
        W = { w with fs := fs', gzs := upd w.gzs b (some { s with «have» := k, eof := e }) } ∧
        HBuf h H cb p (p + len.toNat))) := by
  rw [gz_load_eq]
  unfold setX
  simp only [ite_true]
  refine GSat.bind (GSat.bind (GSat.of_eq (wrG_app hs _) (GSat.pure ?_)))
  refine GSat.bind (GSat.mono (loadLoopX_spec hs ha len hp hcb) fun lp W1 H1 q => ?_)
  obtain ⟨k, hk, fs', hfs, rfl, x⟩ := q
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
  · intro _
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.of_eq (wrG_app hs1 _) (GSat.pure ?_))
      refine Or.inr ⟨rfl, k, hk, fs', 1, hfs, ?_, x⟩
      simp only [InflateInv.upd_upd]
    · intro _
      refine GSat.pure (Or.inr ⟨rfl, k, hk, fs', s.eof, hfs, ?_, x⟩)
      rfl

/-! ## One-byte stores and the copy loop of `gz_avail` -/

theorem store8_heap {H : Heap} {c off : Nat} {a : Array UInt8} (ha : H.bytes c = some a) (hoff : off < a.size)
    (v : UInt8) : store8 (.ref (.heap c) off) v H =
      .ok ((), { H with bytes := H.bytes.modify c (Option.map fun a' => a'.set! off v) }) := by
  have hg : Space.get H (BRef.heap c) = some a := ha
  simp only [store8, Ptr.store, hg]
  simp [Space.ro, Heap.isRo, hoff, Space.modify, Heap.modifyBytes]

theorem HBuf.store8 {H : Heap} {c off lo hi : Nat} {a : Array UInt8} (ha : H.bytes c = some a) (hl : lo ≤ off)
    (hh : off < hi) (v : UInt8) :
    HBuf H { H with bytes := H.bytes.modify c (Option.map fun a' => a'.set! off v) } c lo hi := by
  have hg := GzOpen.modify_some H.bytes c a (fun a' => a'.set! off v) ha
  refine ⟨H.bytes.modify c (Option.map fun a' => a'.set! off v), rfl, fun c' hc' => (by rw [hg]; simp [hc']),
    fun e => (by rw [ha] at e; cases e), fun a' ha' => ?_⟩
  rw [ha] at ha'; cases ha'
  refine ⟨a.set! off v, by rw [hg]; simp, by simp, fun j hj => ?_⟩
  have : off ≠ j := by omega
  simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, this]

theorem load8_heap {H : Heap} {c off : Nat} {a : Array UInt8} (ha : H.bytes c = some a) (hoff : off < a.size) :
    ∃ v, load8 (.ref (.heap c) off) H = .ok (v, H) := by
  have hg : Space.get H (BRef.heap c) = some a := ha
  exact ⟨a[off], by simp [load8, Ptr.load, hg, hoff]⟩

/-- The body of the copy loop of `gz_avail` (copied from the translation). -/
def copyBody (s : CopyLoop) : G CopyLoop := do
  let v ← lm (load8 s.q)
  lm (store8 s.p v)
  return { s with p := ← lm (s.p.add 1), q := ← lm (s.q.add 1) }

/-- The condition of the copy loop of `gz_avail` (copied from the translation). -/
def copyCond (s : CopyLoop) : G (Bool × CopyLoop) := do
  let n := s.n - 1
  return (n != 0, { s with n := n })

/-- The copy loop of `gz_avail`: `n` bytes from `base + j` to `base`, inside `[base, base + j + n)` of block `cb`. -/
theorem copy_spec {w : World} {h : Heap} {cb base j : Nat} {a : Array UInt8} (ha : h.bytes cb = some a)
    (n : UInt32) (hn : n ≠ 0) (hfit : base + j + n.toNat ≤ a.size) :
    GSat w h (gdoWhile copyBody copyCond ⟨.ref (.heap cb) base, .ref (.heap cb) (base + j), n⟩)
      (fun _ W H => W = w ∧ HBuf h H cb base (base + j + n.toNat)) := by
  have hn0 : 0 < n.toNat := by
    have : n.toNat ≠ 0 := fun e => hn (UInt32.toNat_inj.mp (by simpa using e))
    omega
  refine gsat_gdoWhile (fun (st : CopyLoop) W H => W = w ∧ ∃ i, i < n.toNat ∧ st.p = .ref (.heap cb) (base + i) ∧
      st.q = .ref (.heap cb) (base + j + i) ∧ st.n.toNat = n.toNat - i ∧ HBuf h H cb base (base + j + n.toNat))
    (fun st _ _ => st.n.toNat) _ ?_ ⟨rfl, 0, hn0, rfl, rfl, by simp, HBuf.refl _ _ _ _⟩
    (by have := n.toNat_lt; simp [fuel]; omega)
  rintro st W H ⟨rfl, i, hi, hp, hq, hcnt, x⟩
  obtain ⟨a1, ha1, hsz⟩ := x.size ha
  obtain ⟨v, ev⟩ := load8_heap ha1 (off := base + j + i) (by omega)
  unfold copyBody
  rw [hp, hq]
  refine GSat.bind (GSat.lm ⟨v, H, ev, ?_⟩)
  refine GSat.bind (GSat.lm ⟨(), _, store8_heap ha1 (off := base + i) (by omega) v, ?_⟩)
  have x2 := x.trans (HBuf.store8 ha1 (off := base + i) (lo := base) (hi := base + j + n.toNat) (by omega) (by omega) v)
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨a2, ha2, hsz2⟩ := x2.size ha
  refine GSat.bind (GSat.lm ⟨_, _, addH ha2 (off := base + i) 1 (by omega), ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, _, addH ha2 (off := base + j + i) 1 (by omega), ?_⟩)
  refine GSat.pure (GSat.pure ?_)
  have hsub : (st.n - 1).toNat = st.n.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; simp
  refine ⟨fun hc => ⟨⟨rfl, i + 1, ?_, by simp only [Nat.add_assoc], by simp only [Nat.add_assoc], by simp only; omega, x2⟩,
    by simp only; omega⟩, fun _ => ⟨rfl, x2⟩⟩
  have : (st.n - 1) ≠ 0 := by simpa using hc
  have : (st.n - 1).toNat ≠ 0 := fun e => this (UInt32.toNat_inj.mp (by simpa using e))
  omega

/-! ## Changes of the stream's buffer fields on a read handle -/

theorem regHdr_strm {h : Heap} {i : Nat} {z z' : ZStream} (hz : h.streams i = some z) (hzs : z'.state = z.state)
    {hp : HeaderPtr} (hr : RegisteredHeader { h with streams := upd h.streams i (some z') } (some i) hp) :
    RegisteredHeader h (some i) hp := by
  obtain ⟨sb, st, ⟨z1, ⟨i', e, hz1⟩, hsb⟩, hst1, hhd⟩ := hr
  cases e
  simp at hz1
  subst hz1
  exact ⟨sb, st, ⟨z, ⟨i, rfl, hz⟩, by rw [← hzs]; exact hsb⟩, hst1, hhd⟩

/-- New `next_in`, `avail_in`, `next_out`, `avail_out` in the stream of a read handle keep its fields when the input
stays inside the `in` buffer. -/
theorem shape_strm {h : Heap} {b : Nat} {s : GzState} {z z' : ZStream} (sh : GzShape h s) (hr : s.mode = GZ_READ)
    (hsz0 : s.size ≠ 0) (hz : h.streams s.strm = some z)
    (ez : z' = { z with next_in := z'.next_in, avail_in := z'.avail_in, next_out := z'.next_out, avail_out := z'.avail_out })
    (hin : ∀ c base, GzBufs h s c base → z'.avail_in = 0 ∨ Inside c base 0 (inSize s) z'.next_in z'.avail_in.toNat) :
    GzShape { h with streams := upd h.streams s.strm (some z') } s ∧
      ownL { h with streams := upd h.streams s.strm (some z') } b s = ownL h b s := by
  have hzs : z'.state = z.state := by rw [ez]
  have hst : stBlk { h with streams := upd h.streams s.strm (some z') } s = stBlk h s := by simp [stBlk, hz, hzs]
  refine ⟨?_, by simp only [ownL, hst]⟩
  have R := sh.read hr
  refine ⟨sh.mode, ownStr_keep sh.path fun _ _ => rfl, ⟨z', by simp⟩, sh.want_lo, sh.want_hi, sh.size, sh.pos,
    ⟨?_, sh.msg.mem⟩, fun _ => ⟨R.how, fun hsz => ?_, R.nobuf, R.skip_have, fun e => absurd e hsz0⟩,
    fun e => absurd (hr.symm.trans e) read_ne_write, fun hz' c hc => sh.dead hz' c (by rw [hst] at hc; exact hc)⟩
  · rcases sh.msg.msg with e | hm
    · exact Or.inl e
    · exact Or.inr (ownBlk_keep hm fun _ _ => rfl)
  · obtain ⟨c, base, z0, hb, hi, hz0, hhv, -, hreg, hmsg⟩ := R.bufs hsz
    rw [hz] at hz0; cases hz0
    obtain ⟨d, hd, hds⟩ := hb.fits
    obtain ⟨i, z1, sb, st, al, e, hz1, hsb, hst1, hal, core⟩ := hi
    cases e
    rw [hz] at hz1; cases hz1
    refine ⟨c, base, z', ⟨hb.size, hb.buffers, hb.inp, hb.out, ⟨d, hd, hds⟩, hb.hdr⟩, ?_,
      by simp, hhv, hin c base hb, fun hp hr' => hreg hp (regHdr_strm hz hzs hr'), by rw [ez]; exact hmsg⟩
    exact InflateReach.caller_inv ⟨s.strm, z, sb, st, al, rfl, hz, hsb, hst1, hal, core⟩
      ⟨s.strm, z, z', sb, rfl, hz, by simp, hsb, ez, rfl, rfl, rfl, fun k g _ hg => ⟨g, hg⟩, rfl, Nat.le_refl _⟩

theorem HLess.strm (h : Heap) (i : Nat) (z' : ZStream) : HLess h { h with streams := upd h.streams i (some z') } := by
  refine ⟨fun _ _ e => e, fun j z0 e => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩
  by_cases hj : j = i
  · subst hj; exact ⟨z', by simp⟩
  · exact ⟨z0, by simp [upd_ne _ _ _ _ hj, e]⟩

/-- A read handle stays one when its stream gets new buffer fields with the input inside the `in` buffer. -/
theorem invR_strm {w : World} {h : Heap} {b : Nat} {s : GzState} {z z' : ZStream} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (hsz0 : s.size ≠ 0) (hz : h.streams s.strm = some z)
    (ez : z' = { z with next_in := z'.next_in, avail_in := z'.avail_in, next_out := z'.next_out, avail_out := z'.avail_out })
    (hin : ∀ c base, GzBufs h s c base → z'.avail_in = 0 ∨ Inside c base 0 (inSize s) z'.next_in z'.avail_in.toNat) :
    GzInvR w { h with streams := upd h.streams s.strm (some z') } (some b) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨sh', eo⟩ := shape_strm (b := b) sh hr hsz0 hz ez hin
  have := (keeps_store hs (HLess.strm h s.strm z') (fun d e => e) sh' (by rw [eo]; exact hn) rfl rfl).1 hv
  rw [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this
  exact this

/-! ## `gz_avail` -/

theorem rdZ_app {α : Type} {H : Heap} {i : Nat} {z : ZStream} (hz : H.streams i = some z) (f : ZStream → α) :
    ZlibNg.Inflate.rdZ (some i) f H = .ok (f z, H) := by
  simp [ZlibNg.Inflate.rdZ, C.ldStream, hz]

theorem wrZ_app {H : Heap} {i : Nat} {z : ZStream} (hz : H.streams i = some z) (f : ZStream → ZStream) :
    ZlibNg.Inflate.wrZ (some i) f H = .ok ((), { H with streams := upd H.streams i (some (f z)) }) := by
  simp [ZlibNg.Inflate.wrZ, C.ldStream, C.stStream, hz]

/-- A change of the stream of the file only is a step of a call on it. -/
theorem gstep_strm {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) {z : ZStream} (z' : ZStream)
    (hz : h.streams s.strm = some z) (hzs : z'.state = z.state) :
    GStep w h w { h with streams := upd h.streams s.strm (some z') } b [] := by
  have hs' : w.gz { h with streams := upd h.streams s.strm (some z') } b = some s := hs
  refine gstep_mk hs hs' rfl (fun _ _ _ => rfl) (fun i hi => by simp [upd_ne _ _ _ _ hi]) rfl
    (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) (fun _ _ e => e) rfl rfl rfl (Nat.le_refl _) (fun c hc _ => ?_)
  simp only [GzOwned, hs', hs] at hc ⊢
  simp only [upd_same, hz, hzs] at hc ⊢; exact hc

/-- The part of `gz_avail` after the copy (copied from the translation). -/
def availTail (state : GzPtr) (strm : StreamPtr) : G Int32 := do
  let inb ← (← ldGz state).«in».get
  let ai ← lm (ZlibNg.Inflate.rdZ strm (·.avail_in))
  let (r, got) ← gz_load state (← lm (inb.add (Int.ofNat ai.toNat)))
    ((← rdG state (·.size)) - (← lm (ZlibNg.Inflate.rdZ strm (·.avail_in)))) false
  if r == -1 then
    return -1
  lm (ZlibNg.Inflate.wrZ strm fun z => { z with avail_in := z.avail_in + got })
  let inb ← (← ldGz state).«in».get
  lm (ZlibNg.Inflate.wrZ strm fun z => { z with next_in := inb })
  return 0

theorem buf_facts {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (hn : (ownL h b s).Nodup)
    (hsz : s.size ≠ 0) {c base : Nat} (hB : GzBufs h s c base) :
    b ≠ c ∧ c ∉ blkOf s.path ∧ c ∉ stBlk h s ∧ c ∈ GzOwned w h (some b) := by
  have hc : c ∈ ownL h b s := by simp [ownL, hsz, hB.buffers, blkOf]
  have e : ownL h b s = ([b] ++ blkOf s.path ++ blkOf s.msg) ++ ([c] ++ stBlk h s) := by
    simp [ownL, hsz, hB.buffers, blkOf]
  rw [e] at hn
  obtain ⟨-, h2, h3⟩ := List.nodup_append.mp hn
  refine ⟨h3 b (by simp) c (by simp), fun hp => h3 c (by simp [hp]) c (by simp) rfl,
    fun hp => (List.nodup_append.mp h2).2.2 c (by simp) c hp rfl, ownL_owned hs c hc⟩

theorem errOf_shape {s s' : GzState} {e : Int32} (he : ErrOf s e s') (h0 : s.«have» = 0) :
    s' = { s with eof := s'.eof, err := s'.err, msg := s'.msg } := by
  obtain ⟨e1, -⟩ := he
  cases s; cases s'
  simp only [errSt] at e1 h0 ⊢
  simp_all

/-- What `gz_avail` leaves: a read handle, a step of the call, reads only, and a state that differs from `s` at most in
`eof`, `err` and `msg`. -/
def AvailPost (w : World) (H0 : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  (r = -1 ∨ r = 0) ∧ GzInvR W H (some b) ∧ GStep w H0 W H b [] ∧ FsRd w.fs W.fs ∧
    ∃ s', W.gz H b = some s' ∧ s' = { s with eof := s'.eof, err := s'.err, msg := s'.msg }

theorem availTail_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) {c base : Nat} {z : ZStream}
    (hB : GzBufs h s c base) (hz : h.streams s.strm = some z)
    (hai : z.avail_in = 0 ∨ Inside c base 0 (inSize s) z.next_in z.avail_in.toNat)
    {H : Heap} (x : HBuf h H c base (base + inSize s)) :
    GSat w H (availTail (some b) (some s.strm)) (AvailPost w H b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  have hsH : w.gz H b = some s := by rw [x.gz hcb]; exact hs
  have hstrH : H.streams = h.streams := by obtain ⟨t, rfl, -⟩ := x; rfl
  have hzH : H.streams s.strm = some z := by rw [hstrH]; exact hz
  have hownH : c ∈ GzOwned w H (some b) := by
    have : GzOwned w H (some b) = GzOwned w h (some b) := by simp only [GzOwned, hsH, hs, hstrH]
    rw [this]; exact hown
  obtain ⟨d, hd, hds⟩ := hB.fits
  obtain ⟨dH, hdH, hszH⟩ := x.size hd
  have hin : inSize s = s.want.toNat := by simp [inSize, hr, read_ne_write]
  have hsize : s.size.toNat = inSize s := by rw [hin, hB.size]
  have hwl := sh.want_hi
  have hai' : z.avail_in.toNat ≤ inSize s := by
    rcases hai with e | ⟨k, -, -, e⟩
    · rw [e]; simp
    · omega
  unfold availTail
  refine GSat.bind (GSat.of_eq (ldGz_app hsH) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, by rw [hB.inp]; rfl, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hzH _, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, H, addH hdH (off := base) z.avail_in.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.of_eq (rdG_app' hsH _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hzH _, ?_⟩)
  have hlen : (s.size - z.avail_in).toNat = inSize s - z.avail_in.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), hsize]
  refine GSat.bind ?_
  rw [gz_load_false]
  refine GSat.bind (GSat.pure ?_)
  refine GSat.bind (GSat.mono (loadLoop_spec hsH hdH (p := base + z.avail_in.toNat) (s.size - z.avail_in)
    (by rw [hlen]; omega) hcb) fun lp W1 H1 q => ?_)
  obtain ⟨hlp, fs', hfs, rfl, x1⟩ := q
  have x01 : HBuf h H1 c base (base + inSize s) := x.trans x1 (by omega) (by rw [hlen]; omega)
  have hv1 : GzInvR { w with fs := fs' } H1 (some b) := invR_hbuf hv hs x01 hcb hpath hst hfs
  have hs1 : ({ w with fs := fs' } : World).gz H1 b = some s := by rw [x01.gz hcb]; exact hs
  have g1 : GStep w H { w with fs := fs' } H1 b [] := by
    have := gstep_hbuf hsH x1 hcb hownH fs' s rfl rfl rfl rfl
    rw [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this
    exact this
  unfold loadTail
  apply GSat.ite
  · intro _
    obtain ⟨pm, am, ez, hcs, hmk⟩ := zstrerror_spec { w with fs := fs' } H1
    refine GSat.bind (GSat.of_eq ez ?_)
    refine GSat.bind (GSat.mono (gz_error_inv (invR_lit hv1 am) hs1 Z_ERRNO pm (Or.inr hcs) hmk) fun _ W H2 q => ?_)
    obtain ⟨s', hsW, herr, hvW, -, hfsW, hstep⟩ := q
    refine GSat.pure (GSat.pure ⟨Or.inl rfl, hvW, ?_, by rw [hfsW]; exact hfs, s', hsW, errOf_shape herr h0⟩)
    exact (g1.trans (gstep_lit hs1 am) ⟨s, hsH⟩ ⟨s, hs1⟩).trans hstep ⟨s, hsH⟩ ⟨s, hs1⟩
  · intro _
    have hz1 : H1.streams s.strm = some z := by
      obtain ⟨t, rfl, -⟩ := x1; exact hzH
    have tail : ∀ e : Int32, GSat { w with fs := fs', gzs := upd w.gzs b (some { s with eof := e }) } H1
        (match ((0 : Int32), lp.hv) with
          | (r, got) =>
            if (r == -1) = true then (pure (-1) : G Int32)
            else do
              lm (ZlibNg.Inflate.wrZ (some s.strm) fun z => { z with avail_in := z.avail_in + got })
              let inb ← (← ldGz (some b)).«in».get
              lm (ZlibNg.Inflate.wrZ (some s.strm) fun z => { z with next_in := inb })
              return 0) (AvailPost w H b s) := by
      intro e
      have hs2 := gzX_upd hs x01 hcb fs' { s with eof := e }
      let z1 : ZStream := { z with avail_in := z.avail_in + lp.hv }
      let z' : ZStream := { z with avail_in := z.avail_in + lp.hv, next_in := .ref (.heap c) base }
      apply GSat.ite
      · intro hc; exact absurd hc (by decide)
      · intro _
        refine GSat.bind (GSat.lm ⟨(), { H1 with streams := upd H1.streams s.strm (some z1) },
          wrZ_app hz1 _, ?_⟩)
        refine GSat.bind (GSat.of_eq (ldGz_app hs2) ?_)
        refine GSat.bind (GSat.lm ⟨.ref (.heap c) base, { H1 with streams := upd H1.streams s.strm (some z1) },
          (by show Ival.get s.«in» _ = _; rw [hB.inp]; rfl), ?_⟩)
        refine GSat.bind (GSat.lm ⟨(), { H1 with streams := upd H1.streams s.strm (some z') },
          (by rw [wrZ_app (z := z1) (by simp)]; simp [InflateInv.upd_upd, z1, z']), ?_⟩)
        refine GSat.pure ⟨Or.inr rfl, ?_, ?_, hfs, _, hs2, rfl⟩
        · obtain ⟨sh1, hn1⟩ := inv_of hs1 hv1.1
          have sh1' := shape_msg sh1 e s.past s.err s.msg ⟨sh1.msg.1, sh1.msg.2⟩
          have hvE : GzInvR { w with fs := fs', gzs := upd w.gzs b (some { s with eof := e }) } H1 (some b) :=
            (keeps_store hs1 (HLess.refl H1) (fun _ e => e) sh1' hn1 rfl rfl).1 hv1
          refine invR_strm (s := { s with eof := e }) (z := z) (z' := z') hvE hs2 hsz hz1 rfl fun c' base' hB' => Or.inr ⟨0, ?_, Nat.le_refl _, ?_⟩
          · have e1 := hB'.buffers; have e2 := hB.buffers
            rw [show ({ s with eof := e } : GzState).buffers = s.buffers from rfl, e2] at e1; cases e1; rfl
          · show 0 + (z.avail_in + lp.hv).toNat ≤ inSize s
            rw [UInt32.toNat_add]; rw [hlen] at hlp; omega
        · exact (gstep_hbuf hsH x1 hcb hownH fs' { s with eof := e } rfl rfl rfl rfl).trans
            (gstep_strm hs2 z' hz1 rfl) ⟨s, hsH⟩ ⟨_, hs2⟩
    apply GSat.ite
    · intro _
      exact GSat.bind (GSat.of_eq (wrG_app hs1 _) (GSat.pure (tail 1)))
    · intro _
      have t := tail s.eof
      have es : ({ s with eof := s.eof } : GzState) = s := rfl
      rw [es, DeflateReset.upd_self w.gzs b s (gzs_of hs)] at t
      exact GSat.pure t

theorem AvailPost.pre {w : World} {h H : Heap} {b : Nat} {s : GzState} {r : Int32} {W : World} {H' : Heap}
    (g : GStep w h w H b []) (hs : w.gz h b = some s) (hsH : w.gz H b = some s) (p : AvailPost w H b s r W H') :
    AvailPost w h b s r W H' :=
  ⟨p.1, p.2.1, g.trans p.2.2.1 ⟨s, hs⟩ ⟨s, hsH⟩, p.2.2.2⟩

/-- **`gz_avail`** on a read handle with buffers and `x.have == 0`: returns `-1` or `0`, leaves a read handle whose
state differs at most in `eof`, `err` and `msg`, and only reads the file system. -/
theorem gz_avail_spec {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) :
    GSat w h (gz_avail (some b)) (AvailPost w h b s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨c, base, z, hB, -, hz, -, hai, -⟩ := (sh.read hr).bufs hsz
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  obtain ⟨d, hd, hds⟩ := hB.fits
  have done0 : AvailPost w h b s 0 w h := ⟨Or.inr rfl, hv, GStep.refl w h b [], FsRd.refl _, s, hs, rfl⟩
  have tail : ∀ H, HBuf h H c base (base + inSize s) →
      GSat w H (availTail (some b) (some s.strm)) (AvailPost w h b s) := by
    intro H x
    have hsH : w.gz H b = some s := by rw [x.gz hcb]; exact hs
    have g : GStep w h w H b [] := by
      have := gstep_hbuf hs x hcb hown w.fs s rfl rfl rfl rfl
      rw [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this
      exact this
    exact (availTail_spec hv hs h0 hsz hB hz hai x).mono fun r W H' p => AvailPost.pre g hs hsH p
  unfold gz_avail
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact GSat.pure ⟨Or.inl rfl, hv, GStep.refl w h b [], FsRd.refl _, s, hs, rfl⟩
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
      apply GSat.ite
      · intro hne
        have hne' : z.avail_in ≠ 0 := by simpa using hne
        obtain ⟨k, hnx, -, hkn⟩ := hai.resolve_left hne'
        refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
        refine GSat.bind (GSat.lm ⟨.ref (.heap c) base, h, (by show Ival.get s.«in» _ = _; rw [hB.inp]; rfl), ?_⟩)
        refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
        apply GSat.ite
        · intro _
          refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
          rw [hnx]
          refine GSat.bind (GSat.mono (copy_spec hd (base := base) (j := k) z.avail_in hne' (by omega))
            fun _ W H q => ?_)
          obtain ⟨rfl, x⟩ := q
          exact tail H ((HBuf.refl h c base (base + inSize s)).trans x (Nat.le_refl _) (by omega))
        · intro _; exact tail h (HBuf.refl _ _ _ _)
      · intro _; exact tail h (HBuf.refl _ _ _ _)
    · intro _; exact GSat.pure done0

end ZlibNgF.Proof.GzMode
