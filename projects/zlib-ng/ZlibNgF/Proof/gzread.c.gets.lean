import ZlibNgF.Proof.«gzread.c.getc»

/-!
# `gzgets` on a read handle (`ZlibNgF`)

With patch 0021: a pending skip is done first (`gz_skip`); then each round fetches output when there is none and no
skip is pending (`gz_fetch`), looks for a newline in the next `n = min(x.have, left)` bytes (`memchr`), copies up
to and including it into the caller's buffer and consumes it. Every copy stays inside `buf[0, len - 1)`, so the
terminating zero lands at `buf[k]` with `k <= len - 1`. `x.pos + n` does not overflow because `n <= x.have` and a read
handle keeps `x.pos + x.have <= GZ_OFF_MAX`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzDecomp

theorem toNat_diff32 (i : Nat) (hi : i < 2 ^ 32) : (Int64.ofInt (i : Int)).toUInt64.toUInt32.toNat = i := by
  have h0 : (0 : Int64) ≤ Int64.ofInt (i : Int) :=
    Int64.le_iff_toInt_le.mpr (by rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]; simp)
  rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt,
    Int64.toInt_ofInt_of_le (by omega) (by omega)]
  omega

theorem left_toNat (len : Int32) (h : ¬ len < 1) : (len.toUInt32 - 1).toNat = len.toNatClampNeg - 1 := by
  have h1 : 1 ≤ len.toInt := by
    have := mt Int32.lt_iff_toInt_lt.mpr h; simp at this; omega
  have h0 : (0 : Int32) ≤ len := Int32.le_iff_toInt_le.mpr (by simp; omega)
  have e := Int32.toNat_toUInt32_of_le h0
  have e2 : len.toNatClampNeg = len.toInt.toNat := rfl
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, e]; simp; omega), e]; simp

theorem one_le_clamp (len : Int32) (h : ¬ len < 1) : 1 ≤ len.toNatClampNeg := by
  have h1 : 1 ≤ len.toInt := by
    have := mt Int32.lt_iff_toInt_lt.mpr h; simp at this; omega
  have e2 : len.toNatClampNeg = len.toInt.toNat := rfl
  omega

/-- A join point with two arguments. -/
theorem GSat.jp2 {β γ α : Type} {f : β → γ → G α} {k : (β → γ → G α) → G α} {w : World} {h : Heap}
    {Q : α → World → Heap → Prop} (P : β → γ → World → Heap → Prop)
    (hf : ∀ x y W H, P x y W H → GSat W H (f x y) Q)
    (hk : ∀ J : β → γ → G α, (∀ x y W H, P x y W H → GSat W H (J x y) Q) → GSat w h (k J) Q) :
    GSat w h (have J := f; k J) Q := hk f hf

/-- A join point of the translation (`have __do_jp := f; k __do_jp`): prove `f` once under a precondition, and the
rest for any `J` that satisfies it. -/
theorem GSat.jp {β α : Type} {f : β → G α} {k : (β → G α) → G α} {w : World} {h : Heap}
    {Q : α → World → Heap → Prop} (P : β → World → Heap → Prop)
    (hf : ∀ x W H, P x W H → GSat W H (f x) Q)
    (hk : ∀ J : β → G α, (∀ x W H, P x W H → GSat W H (J x) Q) → GSat w h (k J) Q) :
    GSat w h (have J := f; k J) Q := hk f hf

theorem memchrB_heap {H : Heap} {c off n : Nat} {a : Array UInt8} (ha : H.bytes c = some a)
    (hn : off + n ≤ a.size) (v : UInt8) :
    ∃ e, memchrB (.ref (.heap c) off) v n H = .ok (e, H) ∧ (e = .null ∨ ∃ i, i < n ∧ e = .ref (.heap c) (off + i)) := by
  have hg : Space.get H (BRef.heap c) = some a := ha
  have hav : min n (a.size - off) = n := by omega
  simp only [memchrB, hg, hav]
  have hoff : ¬ off > a.size := by omega
  simp only [hoff, ite_false]
  split
  · next i hi =>
    refine ⟨_, rfl, Or.inr ⟨i, ?_, rfl⟩⟩
    obtain ⟨hlt, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp at hlt; omega
  · have : n ≤ a.size - off := by omega
    simp only [this, ite_true]
    exact ⟨_, rfl, Or.inl rfl⟩

theorem diff_heap {H : Heap} {c o1 o2 : Nat} {a : Array UInt8} (ha : H.bytes c = some a) (h1 : o1 ≤ a.size)
    (h2 : o2 ≤ a.size) (hle : o2 ≤ o1) (hb : o1 - o2 < 2 ^ 63) :
    Ptr.diff (Ptr.ref (BRef.heap c) o1 : BPtr) (.ref (.heap c) o2) H = .ok (Int64.ofInt ((o1 : Int) - (o2 : Int)), H) := by
  have hg : Space.get H (BRef.heap c) = some a := ha
  have hr : -(2 ^ 63 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 2 ^ 63 := by omega
  simp only [Ptr.diff, hg, h1, h2, and_self, ite_true, hr]

/-- `memcpy` into block `cb` from another object: only the bytes `[od, od + n)` of `cb` change. -/
theorem memcpy_hbuf {H : Heap} {cb od n : Nat} {rs : BRef} {os : Nat} {ad src : Array UInt8}
    (hd : H.bytes cb = some ad) (hs : Space.get H rs = some src) (hne : rs ≠ .heap cb)
    (h1 : od + n ≤ ad.size) (h2 : os + n ≤ src.size) :
    ∃ H', Ptr.memcpy (.ref (.heap cb) od) (.ref rs os) n H = .ok ((), H') ∧ HBuf H H' cb od (od + n) := by
  refine ⟨_, InflateDict.memcpy_heap hd hs hne h1 h2, ?_⟩
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · intro c hc; simp [upd_ne _ _ _ _ hc]
  · intro e; rw [hd] at e; cases e
  intro a ha
  rw [hd] at ha; cases ha
  refine ⟨InflateDict.copyFold src od os (List.range' 0 n) ad, by simp, InflateDict.copyFold_size _ _ _ _ _,
    fun j hj => ?_⟩
  exact InflateDict.copyFold_get _ _ _ _ _ j fun i hi => ChunkMem.mem_range'_bound hi hj

/-- Stores into a block `cb` outside the file, inside the caller range `[o, o + L)`, are a step of a call. -/
theorem gstep_caller {w : World} {H H' : Heap} {b cb lo hi o L : Nat}
    (x : HBuf H H' cb lo hi) (hcb : cb ∉ GzOwned w H (some b)) (hbc : b ≠ cb) (ho : o ≤ lo) (hL : hi ≤ o + L) :
    GStep w H w H' b [(.ref (.heap cb) o, L)] := by
  obtain ⟨t, rfl, hne, hnone, hsz⟩ := x
  have hgz : w.gz { H with bytes := t } b = w.gz H b := by unfold World.gz; rw [hne b hbc]
  have hown : GzOwned w { H with bytes := t } (some b) = GzOwned w H (some b) := by simp only [GzOwned, hgz]
  refine ⟨⟨⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun c hc hn data hd => ?_,
    fun c hc hn hd => ?_, rfl, rfl, rfl, rfl, Nat.le_refl _⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩, fun _ _ e => e,
    fun _ _ _ => rfl⟩, fun c hc _ => by rwa [hown] at hc, fun s1 s2 e1 e2 => by
      rw [hgz, e1] at e2; cases e2; rfl⟩
  · by_cases e : c = cb
    · subst e
      obtain ⟨a', e1, e2, e3⟩ := hsz data hd
      refine ⟨a', e1, e2, fun j _ hw => e3 j ?_⟩
      rcases hw _ (List.mem_singleton_self _) o rfl with h1 | h1 <;> omega
    · exact ⟨data, by show t c = _; rw [hne c e]; exact hd, rfl, fun _ _ _ => rfl⟩
  · by_cases e : c = cb
    · subst e; exact hnone hd
    · show t c = none; rw [hne c e]; exact hd

/-- A block of the caller that a step of the call does not own stays live with its size, outside the file. -/
theorem caller_blk {w W : World} {h H : Heap} {b cb : Nat} {wr : List (BPtr × Nat)} (g : GStep w h W H b wr)
    (hc : cb < h.nextBlk) (hno : cb ∉ GzOwned w h (some b)) {d : Array UInt8} (hd : h.bytes cb = some d) :
    ∃ d', H.bytes cb = some d' ∧ d'.size = d.size ∧ cb ∉ GzOwned W H (some b) :=
  have ⟨d', e, sz⟩ := frame_live g.frame.1.1 hc hno hd
  ⟨d', e, sz, fun m => hno (g.own _ m hc)⟩

/-- Stores into a block outside the file keep a read handle. -/
theorem invR_caller {W : World} {H H' : Heap} {b cb lo hi : Nat} (hv : GzInvR W H (some b))
    (hno : cb ∉ GzOwned W H (some b)) (x : HBuf H H' cb lo hi) : GzInvR W H' (some b) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  have hb : b ≠ cb := fun e => hno (by subst e; simp [GzOwned, hs])
  have hp : cb ∉ blkOf s.path := fun m => hno (by
    simp only [GzOwned, hs, List.mem_append]; left; left; left; right; unfold blkOf at m; split at m <;> simp_all)
  have hst : cb ∉ stBlk H s := fun m => hno (by
    simp only [GzOwned, hs, List.mem_append]; right; unfold stBlk at m; exact m)
  exact invR_hbuf hv hs x hb hp hst (FsRd.refl _)

theorem u32_min_toNat (a b : UInt32) : (min a b).toNat = min a.toNat b.toNat := by
  rw [UInt32.min_def]
  split
  · next hh => have := UInt32.le_iff_toNat_le.mp hh; omega
  · next hh => have := mt UInt32.le_iff_toNat_le.mpr hh; omega

/-- `past = 1` keeps a read handle. -/
theorem invR_past {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (pa : Int32) :
    GzInvR { W with gzs := upd W.gzs b (some { s with past := pa }) } H (some b) ∧
      GStep W H { W with gzs := upd W.gzs b (some { s with past := pa }) } H b [] := by
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  have R := sh.read (modeOf hs hv.2.1)
  have P := sh.pos
  exact invR_hp hv hs rfl P.3 P.2 (hout_self R) R.skip_have R.pos_have R.look_pos

/-- The condition of the loop of `gzgets` (copied from the translation). -/
def getsCond (s : GetsLoop) : G (Bool × GetsLoop) :=
  if (s.ctl != Ctl.go) = true then pure (false, s) else pure (s.left != 0 && s.eol == .null, s)

theorem cond_stop {W : World} {H : Heap} {s1 : GetsLoop} (h1 : s1.ctl ≠ .go)
    {X : GetsLoop → World → Heap → Prop} {Q : GetsLoop → World → Heap → Prop} (q : Q s1 W H) :
    GSat W H (getsCond s1) (fun cs w2 h2 => (cs.1 = true → X cs.2 w2 h2) ∧ (cs.1 = false → Q cs.2 w2 h2)) := by
  unfold getsCond
  apply GSat.ite
  · intro _; exact GSat.pure ⟨(fun e => by cases e), fun _ => q⟩
  · intro hc; simp [h1] at hc

theorem cond_go {W : World} {H : Heap} {s1 : GetsLoop} (h1 : s1.ctl = .go)
    {X : GetsLoop → World → Heap → Prop} {Q : GetsLoop → World → Heap → Prop}
    (x : s1.left ≠ 0 → s1.eol = .null → X s1 W H) (q : Q s1 W H) :
    GSat W H (getsCond s1) (fun cs w2 h2 => (cs.1 = true → X cs.2 w2 h2) ∧ (cs.1 = false → Q cs.2 w2 h2)) := by
  unfold getsCond
  apply GSat.ite
  · intro hc; simp [h1] at hc
  · intro _
    refine GSat.pure ⟨fun e => ?_, fun _ => q⟩
    simp at e
    exact x e.1 e.2

/-- The copy at the end of a round of the loop of `gzgets` (copied from the translation). -/
def getsCopy (state : GzPtr) (s : GetsLoop) (eol : BPtr) (n : UInt32) : G GetsLoop := do
  lm (Ptr.memcpy s.buf (← (← ldGz state).next.get) n.toNat)
  wrG state fun st => { st with «have» := st.«have» - n }
  let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
  wrG state fun st => { st with next := .val nx }
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
  wrG state fun st => { st with pos := np }
  let buf ← lm (s.buf.add (Int.ofNat n.toNat))
  return { s with buf := buf, left := s.left - n, eol := eol }

/-- **The copy**: `n` bytes, `1 <= n <= x.have`, from `x.next` to `s.buf = buf + k` with `k + n` inside the caller's
`len - 1` bytes. -/
theorem getsCopy_spec {W : World} {H : Heap} {b cb o k L : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (st : GetsLoop) (hbk : st.buf = .ref (.heap cb) (o + k)) (eol : BPtr) (n : UInt32)
    (hn1 : 1 ≤ n.toNat) (hnh : n.toNat ≤ s.«have».toNat) (hkn : k + n.toNat ≤ L - 1)
    {dc : Array UInt8} (hdc : H.bytes cb = some dc) (hfit : o + L ≤ dc.size) (hno : cb ∉ GzOwned W H (some b)) :
    GSat W H (getsCopy (some b) st eol n) (fun s1 W' H' =>
      s1 = { st with buf := .ref (.heap cb) (o + (k + n.toNat)), left := st.left - n, eol := eol } ∧
      GzInvR W' H' (some b) ∧ GStep W H W' H' b [(.ref (.heap cb) o, L)] ∧
      (LookIdle W H (some b) → LookIdle W' H' (some b))) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have R := sh.read (modeOf hs hv.2.1)
  have P := sh.pos
  have hmx := gzmax
  have hh : s.«have» ≠ 0 := fun e => by rw [e] at hnh; simp at hnh; omega
  have hsz : s.size ≠ 0 := fun e => hh (R.nobuf e)
  obtain ⟨c, base, z, hb, -, -, hhv, -, -⟩ := R.bufs hsz
  obtain ⟨p, hp, k1, hpk, hlo, hhi⟩ := hhv.resolve_left hh
  obtain ⟨d, hd, hds⟩ := hb.fits
  have hcO : c ∈ GzOwned W H (some b) := ownL_owned hs c (by simp [ownL, hsz, hb.buffers, blkOf])
  have hcb : c ≠ cb := fun e => hno (e ▸ hcO)
  have hbc : b ≠ cb := fun e => hno (by subst e; simp [GzOwned, hs])
  unfold getsCopy
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  refine GSat.bind (GSat.lm ⟨p, H, by show Ival.get s.next H = _; rw [hp]; rfl, ?_⟩)
  rw [hbk, hpk]
  obtain ⟨H1, em, x⟩ := memcpy_hbuf (od := o + k) (os := base + k1) (n := n.toNat) hdc (rs := .heap c) (src := d) hd
    (fun e => hcb (by cases e; rfl)) (by omega) (by omega)
  refine GSat.bind (GSat.lm ⟨(), H1, em, ?_⟩)
  have hv1 : GzInvR W H1 (some b) := invR_caller hv hno x
  have hs1 : W.gz H1 b = some s := by rw [x.gz hbc]; exact hs
  have g1 : GStep W H W H1 b [(.ref (.heap cb) o, L)] := gstep_caller x hno hbc (by omega) (by omega)
  have hd1 : H1.bytes c = some d := by rw [x.bytes_ne hcb]; exact hd
  have hstr : H1.streams = H.streams := by obtain ⟨t, et, -⟩ := x; rw [et]
  obtain ⟨dc1, hdc1, hsz1⟩ := x.size hdc
  obtain ⟨db, hdb⟩ := gz_live hs1
  let s1 : GzState := { s with «have» := s.«have» - n }
  refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_upd hdb W s1) ?_)
  refine GSat.bind (GSat.lm ⟨_, H1, by show Ival.get s.next H1 = _; rw [hp, hpk]; rfl, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, H1, addH hd1 (off := base + k1) n.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb W s1 _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_upd hdb W _ _) ?_)
  have hph := R.pos_have
  have hb1 : -(2 ^ 63 : Int) ≤ s.pos.toInt + (n.toNat : Int) ∧ s.pos.toInt + (n.toNat : Int) < 2 ^ 63 := by
    have := P.3; constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, H1, chkI64_ok hb1.1 hb1.2 H1, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_upd hdb W _ _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H1, addH hdc1 (off := o + k) n.toNat (by omega), ?_⟩)
  refine GSat.pure ⟨by rw [Nat.add_assoc], ?_⟩
  simp only [InflateInv.upd_upd]
  have e2 := toInt_ofInt' hb1.1 hb1.2
  have hhm : (s.«have» - n).toNat = s.«have».toNat - n.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hnh)]
  let sF : GzState := { s with «have» := s.«have» - n, next := .val (.ref (.heap c) (base + k1 + n.toNat)), pos := Int64.ofInt (s.pos.toInt + (n.toNat : Int)) }
  have f1 : sF.pos.toInt + s.skip.toInt ≤ GZ_OFF_MAX.toInt := by
    show (Int64.ofInt (s.pos.toInt + (n.toNat : Int))).toInt + s.skip.toInt ≤ GZ_OFF_MAX.toInt
    rw [e2]
    by_cases hk : s.skip = 0
    · rw [hk]; simp; omega
    · have := R.skip_have hk; omega
  have f2 : sF.«have» = 0 ∨ (s.size ≠ 0 ∧ ∀ c base, GzBufs H1 s c base →
      ∃ q, sF.next = .val q ∧ Inside c base (inSize s) (inSize s + outSize s) q sF.«have».toNat) := by
    refine Or.inr ⟨hsz, fun c' base' hb' => ?_⟩
    have e1 := hb'.buffers; rw [hb.buffers] at e1; cases e1
    refine ⟨_, rfl, k1 + n.toNat, by rw [Nat.add_assoc], by omega, ?_⟩
    show k1 + n.toNat + (s.«have» - n).toNat ≤ _; rw [hhm]; omega
  have f3 : s.skip ≠ 0 → sF.pos.toInt + s.skip.toInt + sF.«have».toNat ≤ GZ_OFF_MAX.toInt := by
    intro hk
    show (Int64.ofInt (s.pos.toInt + (n.toNat : Int))).toInt + s.skip.toInt + ((s.«have» - n).toNat : Int) ≤ GZ_OFF_MAX.toInt
    rw [e2, hhm]; have := R.skip_have hk; omega
  have f4 : sF.pos.toInt + sF.«have».toNat ≤ GZ_OFF_MAX.toInt := by
    show (Int64.ofInt (s.pos.toInt + (n.toNat : Int))).toInt + ((s.«have» - n).toNat : Int) ≤ GZ_OFF_MAX.toInt
    rw [e2, hhm]; omega
  have f5 : s.how = LOOK → s.direct ≠ 0 → sF.pos.toInt + sF.«have».toNat ≤ 0 := by
    intro hL hD
    show (Int64.ofInt (s.pos.toInt + (n.toNat : Int))).toInt + ((s.«have» - n).toNat : Int) ≤ 0
    rw [e2, hhm]; have := R.look_pos hL hD; omega
  have f0 : -GZ_OFF_MAX.toInt ≤ sF.pos.toInt := by
    show -GZ_OFF_MAX.toInt ≤ (Int64.ofInt (s.pos.toInt + (n.toNat : Int))).toInt
    rw [e2]; have := P.3; omega
  obtain ⟨hvF, gF⟩ := invR_hp hv1 hs1 (s' := sF) rfl f0 f1 f2 f3 f4 f5
  exact ⟨hvF, g1.trans (GzDecomp.GStep.widen gF _) ⟨s, hs⟩ ⟨s, hs1⟩,
    fun hi => idle_same hi hs (gz_upd_same hs1 sF) rfl rfl rfl (by rw [hstr])⟩

/-- A round of the loop of `gzgets` after the fetch (copied from the translation). -/
def getsRest (state : GzPtr) (s : GetsLoop) : G GetsLoop := do
  if (← rdG state (·.«have»)) == 0 then
    wrG state fun st => { st with past := 1 }
    return { s with ctl := .brk }
  let mut n : UInt32 := min (← rdG state (·.«have»)) s.left
  let eol ← lm (memchrB (← (← ldGz state).next.get) 10 n.toNat)
  if eol != .null then
    let d ← lm (Ptr.diff eol (← (← ldGz state).next.get))
    n := d.toUInt64.toUInt32 + 1
  getsCopy state s eol n

theorem getsRest_spec {W : World} {H : Heap} {b cb o k L : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (st : GetsLoop) (hbk : st.buf = .ref (.heap cb) (o + k))
    (hkl : k + st.left.toNat = L - 1) (hl0 : st.left ≠ 0)
    {dc : Array UInt8} (hdc : H.bytes cb = some dc) (hfit : o + L ≤ dc.size) (hno : cb ∉ GzOwned W H (some b)) :
    GSat W H (getsRest (some b) st) (fun s1 W' H' =>
      ((s1 = { st with ctl := .brk }) ∨
        ∃ n e, 1 ≤ n.toNat ∧ n.toNat ≤ st.left.toNat ∧
          s1 = { st with buf := .ref (.heap cb) (o + (k + n.toNat)), left := st.left - n, eol := e }) ∧
      GzInvR W' H' (some b) ∧ GStep W H W' H' b [(.ref (.heap cb) o, L)] ∧
      (LookIdle W H (some b) → LookIdle W' H' (some b))) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have R := sh.read (modeOf hs hv.2.1)
  unfold getsRest
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _
    obtain ⟨hvP, gP⟩ := invR_past hv hs 1
    refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
    exact GSat.pure ⟨Or.inl rfl, hvP, GzDecomp.GStep.widen gP _, fun hi => idle_upd hi hs _ rfl rfl rfl⟩
  intro hh0
  have hh : s.«have» ≠ 0 := by simpa using hh0
  have hsz : s.size ≠ 0 := fun e => hh (R.nobuf e)
  obtain ⟨c, base, z, hb, -, -, hhv, -, -⟩ := R.bufs hsz
  obtain ⟨p, hp, k1, hpk, hlo, hhi⟩ := hhv.resolve_left hh
  obtain ⟨d, hd, hds⟩ := hb.fits
  have hmin := u32_min_toNat s.«have» st.left
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  refine GSat.bind (GSat.lm ⟨p, H, by show Ival.get s.next H = _; rw [hp]; rfl, ?_⟩)
  rw [hpk]
  obtain ⟨e, em, he⟩ := memchrB_heap hd (off := base + k1) (n := (min s.«have» st.left).toNat) (by omega) 10
  refine GSat.bind (GSat.lm ⟨e, H, em, ?_⟩)
  have hl0' : st.left.toNat ≠ 0 := fun e => hl0 (UInt32.toNat_inj.mp (by simpa using e))
  have hh' : s.«have».toNat ≠ 0 := fun e => hh (UInt32.toNat_inj.mp (by simpa using e))
  have hlt := st.left.toNat_lt
  have post : ∀ (e' : BPtr) (n : UInt32), 1 ≤ n.toNat → n.toNat ≤ (min s.«have» st.left).toNat →
      GSat W H (getsCopy (some b) st e' n) (fun s1 W' H' =>
        ((s1 = { st with ctl := .brk }) ∨
          ∃ n e, 1 ≤ n.toNat ∧ n.toNat ≤ st.left.toNat ∧
            s1 = { st with buf := .ref (.heap cb) (o + (k + n.toNat)), left := st.left - n, eol := e }) ∧
        GzInvR W' H' (some b) ∧ GStep W H W' H' b [(.ref (.heap cb) o, L)] ∧
        (LookIdle W H (some b) → LookIdle W' H' (some b))) := by
    intro e' n h1 h2
    exact (getsCopy_spec hv hs st hbk e' n h1 (by omega) (by omega) hdc hfit hno).mono fun s1 W' H' q =>
      ⟨Or.inr ⟨n, e', h1, by omega, q.1⟩, q.2⟩
  apply GSat.ite
  · intro hne
    rcases he with rfl | ⟨i, hi, rfl⟩
    · simp at hne
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    refine GSat.bind (GSat.lm ⟨p, H, by show Ival.get s.next H = _; rw [hp]; rfl, ?_⟩)
    rw [hpk]
    refine GSat.bind (GSat.lm ⟨_, H, diff_heap hd (by omega) (by omega) (by omega) (by omega), ?_⟩)
    have hi' : (((base + k1 + i : Nat) : Int) - ((base + k1 : Nat) : Int)) = (i : Int) := by omega
    rw [hi']
    have e1 := toNat_diff32 i (by omega)
    have e2 : ((Int64.ofInt (i : Int)).toUInt64.toUInt32 + 1).toNat = i + 1 := by
      rw [UInt32.toNat_add, e1]; simp; omega
    exact post _ _ (by omega) (by omega)
  · intro _
    exact post _ _ (by omega) (Nat.le_refl _)

/-! ## `gzgets` -/

theorem gzgets_read (FS : GzFetchSpec) (SS : GzSkipSpec) (FI : GzFetchIdle) (SI : GzSkipIdle) {w : World}
    {h : Heap} {b : Nat} (hv : GzInvR w h (some b)) (hi : LookIdle w h (some b)) (buf : BPtr) (len : Int32)
    (hbuf : len ≥ 1 → GzOut w h (some b) buf len.toNatClampNeg ∨ buf = .null) :
    GSat w h (gzgets (some b) buf len)
      (fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b [(buf, len.toNatClampNeg)]) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  have done : ∀ W H, GzInvR W H (some b) → LookIdle W H (some b) → GStep w h W H b [] →
      GSat W H (pure (.null : BPtr))
      (fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b [(buf, len.toNatClampNeg)]) :=
    fun W H hv hi g => GSat.pure ⟨hv, hi, GzDecomp.GStep.widen g _⟩
  unfold gzgets
  apply GSat.ite
  · intro _; exact done w h hv hi (GStep.refl w h b [])
  intro hc
  simp at hc
  obtain ⟨hnull, hlen0⟩ := hc
  have hlen : ¬ len < 1 := Int32.not_lt.mpr hlen0
  have hL1 := one_le_clamp len hlen
  obtain ⟨⟨cb, o, data, rfl, hd, hfit⟩, hout⟩ : WriteSlice h buf len.toNatClampNeg ∧ OutsideGz w h (some b) buf := by
    rcases (hbuf hlen0).resolve_right hnull with e | x
    · omega
    · exact x
  have hno : cb ∉ GzOwned w h (some b) := fun m => hout cb m o rfl
  have hcbn : cb < h.nextBlk := live_lt hv.2.2.2.1.1 ⟨data, hd⟩
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact done w h hv hi (GStep.refl w h b [])
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  extract_lets str left jpE J
  have hE : ∀ (bv : BPtr) W H, (∃ k, bv = .ref (.heap cb) (o + k) ∧ k ≤ len.toNatClampNeg - 1) ∧
      GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b [(.ref (.heap cb) o, len.toNatClampNeg)] →
      GSat W H (jpE () bv) (fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧
        GStep w h W H b [(.ref (.heap cb) o, len.toNatClampNeg)]) := by
    rintro bv W H ⟨⟨k, rfl, hk⟩, hvW, hiW, gW⟩
    simp only [jpE]
    apply GSat.ite
    · intro _; exact GSat.pure ⟨hvW, hiW, gW⟩
    · intro _
      obtain ⟨d', hd', hsz', hnoW⟩ := caller_blk gW hcbn hno hd
      refine GSat.bind (GSat.lm ⟨_, H, addH hd' 0 (by omega), ?_⟩)
      have x := HBuf.store8 hd' (off := o + k + 0) (lo := o + k) (hi := o + k + 1) (by omega) (by omega) 0
      refine GSat.bind (GSat.lm ⟨(), _, store8_heap hd' (off := o + k + 0) (by omega) 0, ?_⟩)
      obtain ⟨s1, hs1⟩ : ∃ s1, W.gz H b = some s1 := by obtain ⟨b1, s1, e1, h1, -⟩ := hvW.1; cases e1; exact ⟨s1, h1⟩
      have hbc : b ≠ cb := fun e => hnoW (by subst e; simp [GzOwned, hs1])
      have hs1' := (x.gz (W := W) hbc).trans hs1
      exact GSat.pure ⟨invR_caller hvW hnoW x, idle_same hiW hs1 hs1' rfl rfl rfl rfl,
        gW.trans (gstep_caller x hnoW hbc (by omega) (by omega)) ⟨s, hs⟩ ⟨s1, hs1⟩⟩
  clear_value jpE
  have hJ : ∀ x W H, GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b [] → GSat W H (J x)
      (fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧
        GStep w h W H b [(.ref (.heap cb) o, len.toNatClampNeg)]) := by
    intro _ W1 H1 ⟨hv1, hi1, g1⟩
    simp only [J]
    have g1' := GzDecomp.GStep.widen g1 [(.ref (.heap cb) o, len.toNatClampNeg)]
    apply GSat.ite
    · intro hl0
      have hlt : left.toNat = len.toNatClampNeg - 1 := left_toNat len hlen
      have hl0' : left ≠ 0 := by simpa using hl0
      let L := len.toNatClampNeg
      let Q : GetsLoop → World → Heap → Prop := fun lp W H => (∃ k, lp.buf = .ref (.heap cb) (o + k) ∧ k ≤ L - 1) ∧
        GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b [(.ref (.heap cb) o, L)]
      let I : GetsLoop → World → Heap → Prop := fun st W H =>
        (∃ k, st.buf = .ref (.heap cb) (o + k) ∧ k + st.left.toNat = L - 1) ∧ st.left ≠ 0 ∧ st.ctl = .go ∧
        GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b [(.ref (.heap cb) o, L)]
      refine GSat.bind (GSat.mono (gsat_gdoWhile I (fun st _ _ => st.left.toNat) Q ?_
        (s := ⟨str, left, .null, .go⟩) ⟨⟨0, rfl, by show 0 + left.toNat = L - 1; omega⟩, hl0', rfl, hv1, hi1, g1'⟩
        (by show left.toNat < 2 ^ 64; have := left.toNat_lt; omega)) fun lp W H q => ?_)
      · intro st W H ⟨⟨k, hbk, hkl⟩, hl0, hgo, hvW, hiW, gW⟩
        obtain ⟨b2, s2, e2, hs2, -, -⟩ := hvW.1; cases e2
        try dsimp (config := {zeta := false}) only
        refine GSat.bind (GSat.of_eq (rdG_app' hs2 _) ?_)
        have hB : ∀ W' H', GzInvR W' H' (some b) ∧ LookIdle W' H' (some b) ∧
            GStep w h W' H' b [(.ref (.heap cb) o, L)] →
            GSat W' H' (getsRest (some b) st) (fun s1 w1 h1 => GSat w1 h1 (getsCond s1) (fun cs w2 h2 =>
              (cs.1 = true → I cs.2 w2 h2 ∧ cs.2.left.toNat < st.left.toNat) ∧ (cs.1 = false → Q cs.2 w2 h2))) := by
          intro W' H' ⟨hv', hi', g'⟩
          obtain ⟨b3, s3, e3, hs3, -, -⟩ := hv'.1; cases e3
          obtain ⟨dc, hdc, hdcs, hnoW⟩ := caller_blk g' hcbn hno hd
          refine (getsRest_spec hv' hs3 st hbk hkl hl0 hdc (by rw [hdcs]; exact hfit) hnoW).mono
            fun s1 W'' H'' q => ?_
          obtain ⟨hs1, hvF, gF, hiF⟩ := q
          have hiF' := hiF hi'
          have g := g'.trans gF ⟨s, hs⟩ ⟨s3, hs3⟩
          rcases hs1 with rfl | ⟨n, e, h1, h2, rfl⟩
          · exact cond_stop (X := fun s w h => I s w h ∧ s.left.toNat < st.left.toNat) (Q := Q) (by simp)
              ⟨⟨k, hbk, by omega⟩, hvF, hiF', g⟩
          · have hsub : (st.left - n).toNat = st.left.toNat - n.toNat :=
              UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h2)
            let s1' : GetsLoop := { st with buf := .ref (.heap cb) (o + (k + n.toNat)), left := st.left - n, eol := e }
            refine cond_go (s1 := s1') (X := fun s w h => I s w h ∧ s.left.toNat < st.left.toNat) (Q := Q) hgo (fun hl _ => ⟨⟨⟨k + n.toNat, rfl, ?_⟩, hl, hgo, hvF, hiF', g⟩, ?_⟩) ⟨⟨k + n.toNat, rfl, ?_⟩, hvF, hiF', g⟩
            · show k + n.toNat + (st.left - n).toNat = L - 1; rw [hsub]; omega
            · show (st.left - n).toNat < st.left.toNat; rw [hsub]; omega
            · omega
        apply GSat.ite
        · intro hh0
          refine GSat.bind (GSat.of_eq (rdG_app' hs2 _) ?_)
          apply GSat.ite
          · intro hk0
            have hh0' : s2.«have» = 0 := by simpa using hh0
            refine GSat.bind (GSat.mono (GSat.withRun (FS W H b s2 hvW hs2 hh0')) fun r W' H' q => ?_)
            obtain ⟨⟨-, gF, -, s', -, -, -, -, hinv, -⟩, run⟩ := q
            have hi' := FI W H b s2 r W' H' hvW hiW hs2 hh0' run
            have hv' := hinv (by simpa using hk0)
            have g' := gW.trans (GzDecomp.GStep.widen gF _) ⟨s, hs⟩ ⟨s2, hs2⟩
            apply GSat.ite
            · intro _
              exact GSat.pure (cond_stop (X := fun s w h => I s w h ∧ s.left.toNat < st.left.toNat) (Q := Q) (by simp)
                ⟨⟨k, hbk, by omega⟩, hv', hi', g'⟩)
            · intro _; exact hB W' H' ⟨hv', hi', g'⟩
          · intro _; exact hB W H ⟨hvW, hiW, gW⟩
        · intro _; exact hB W H ⟨hvW, hiW, gW⟩
      · apply GSat.ite
        · intro _; exact GSat.pure q.2
        · intro _; exact hE lp.buf W H q
    · intro _
      exact hE str W1 H1 ⟨⟨0, rfl, by omega⟩, hv1, hi1, g1'⟩
  clear_value J
  · apply GSat.ite
    · intro hk
      have hk' : s.skip ≠ 0 := by simpa using hk
      refine GSat.bind (GSat.mono (GSat.withRun (SS w h b s (mid_of hv hs) hk')) fun r W H q => ?_)
      obtain ⟨⟨-, hvW, gW, -, -⟩, run⟩ := q
      have hiW := SI w h b s r W H (mid_of hv hs) hi hk' run
      apply GSat.ite
      · intro _; exact done W H hvW hiW gW
      · intro _; exact hJ () W H ⟨hvW, hiW, gW⟩
    · intro _; exact hJ () w h ⟨hv, hi, GStep.refl w h b []⟩

theorem gets_keepsRI (FS : GzFetchSpec) (SS : GzSkipSpec) (FI : GzFetchIdle) (SI : GzSkipIdle) : KeepsRI SGets := by
  intro w h w' h' f hv hi ⟨buf, len, r, hb, e⟩
  obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
  obtain ⟨r2, W, H, e2, q⟩ := (gzgets_read FS SS FI SI hv hi buf len (fun h1 => (hb h1))).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact ⟨q.1, q.2.1⟩

end ZlibNgF.Proof.GzMode
