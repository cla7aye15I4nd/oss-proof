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
    refine ⟨R.how, fun hsz' => ?_, R.nobuf, R.skip_have⟩
    obtain ⟨c, base, z, hB, hi, hz, hhv, hai, hreg⟩ := R.bufs hsz'
    obtain ⟨i, z0, sb, st, al, e, hz0, hsb, hst0, hal, core⟩ := hi
    cases e
    rw [hz] at hz0; cases hz0
    have hsbne : sb ≠ cb := fun e => hst (e ▸ stBlk_of hz hsb)
    have hcs : InflateInv.Inv { h with bytes := t } (some s.strm) :=
      InflateReach.caller_inv ⟨s.strm, z, sb, st, al, rfl, hz, hsb, hst0, hal, core⟩
        ⟨s.strm, z, z, sb, rfl, hz, hz, hsb, rfl, hne sb hsbne, rfl, rfl,
          fun k g hr' _ => absurd (hreg _ hr') (by simp), rfl, Nat.le_refl _⟩
    refine ⟨c, base, z, hbufs c base hB, hcs, hz, hhv, hai, fun hp' hr' => hreg hp' ?_⟩
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

end ZlibNgF.Proof.GzMode
