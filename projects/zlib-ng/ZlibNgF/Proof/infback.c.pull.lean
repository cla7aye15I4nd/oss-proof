import ZlibNgF.Proof.«inflate.c.xrun»
import ZlibNgF.Spec.Common.Infback

/-!
# `inflateBack`: the call-back macros `PULL`, `PULLBYTE`, `NEEDBITS` (`ZlibNgF`)

The input of the call-back decoder (`InB`): `next` with `have` bytes is the tail of the chunk `(p, m)` that `in()`
handed out last, `t` more bytes are still to come, and the caller's invariant `I` holds of that chunk on the current
heap. A call of `in()` keeps what `BackKeep` names (the stream record, the library's block, the window's block); the
input measure `8 * (have + t) + bits` stays the same across a `PULLBYTE` and falls by the bits a `DROPBITS` drops.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackPull
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)

/-! ## What the call-backs keep -/

theorem BackKeep.refl (h : Heap) (i b : Nat) (w : BPtr) : BackKeep h h i b w :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ d _ hd => ⟨d, hd, rfl⟩, rfl, Nat.le_refl _⟩

theorem BackKeep.trans {h1 h2 h3 : Heap} {i b : Nat} {w : BPtr} (k1 : BackKeep h1 h2 i b w)
    (k2 : BackKeep h2 h3 i b w) : BackKeep h1 h3 i b w := by
  obtain ⟨s1, b1, t1, a1, w1, o1, n1⟩ := k1
  obtain ⟨s2, b2, t2, a2, w2, o2, n2⟩ := k2
  refine ⟨s2.trans s1, b2.trans b1, t2.trans t1, a2.trans a1, fun wb off d hw hd => ?_, o2.trans o1,
    Nat.le_trans n1 n2⟩
  obtain ⟨d1, hd1, hs1⟩ := w1 wb off d hw hd
  obtain ⟨d2, hd2, hs2⟩ := w2 wb off d1 hw hd1
  exact ⟨d2, hd2, hs2.trans hs1⟩

/-! ## The input -/

/-- `next` with `have` bytes is the tail of the chunk `(p, m)`, for which `I` holds with `t` bytes to come. -/
def InB (I : Heap → BPtr → Nat → Nat → Prop) (H : Heap) (l : IL) (t : Nat) : Prop :=
  ∃ p m, I H p m t ∧ l.have_.toNat ≤ m ∧
    (l.have_ ≠ 0 → ∃ r o, p = .ref r o ∧ l.next = .ref r (o + (m - l.have_.toNat)))

/-- A chunk just handed out: all of it is left. -/
theorem InB.fresh {I : Heap → BPtr → Nat → Nat → Prop} {H : Heap} {l : IL} {t : Nat} {q : BPtr} (k : UInt32)
    (hI : I H q k.toNat t) (hl : l.have_ = k) (hn : l.next = q)
    (hq : k ≠ 0 → ∃ r o, q = .ref r o) : InB I H l t := by
  refine ⟨q, k.toNat, hI, by rw [hl]; exact Nat.le_refl _, fun h0 => ?_⟩
  obtain ⟨r, o, rfl⟩ := hq (by rw [← hl]; exact h0)
  exact ⟨r, o, rfl, by rw [hn, hl]; simp⟩

/-- The bytes `[next, next + have)` are readable. -/
theorem InB.bytes {i b : Nat} {w : BPtr} {n : Nat} {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr}
    {I : Heap → BPtr → Nat → Nat → Prop} (cb : BackCallbacks i b w n inCb inDesc outCb outDesc I) {H : Heap}
    {l : IL} {t : Nat} (hin : InB I H l t) (h0 : l.have_ ≠ 0) :
    ∃ r o d, l.next = .ref r o ∧ Space.get H r = some d ∧ o + l.have_.toNat ≤ d.size := by
  obtain ⟨p, m, hI, hle, hat⟩ := hin
  obtain ⟨r, o, rfl, hnx⟩ := hat h0
  have hm : m ≠ 0 := by
    intro e; apply h0; apply UInt32.toNat_inj.mp; simp only [UInt32.toNat_zero]; omega
  obtain ⟨⟨r', o', d, he, hg, hs⟩, -, -⟩ := cb.chunk H _ m t hI hm
  cases he
  exact ⟨r, o + (m - l.have_.toNat), d, hnx, hg, by omega⟩

theorem u32_ne_zero {k : UInt32} (h : k ≠ 0) : 1 ≤ k.toNat := by
  rcases Nat.eq_zero_or_pos k.toNat with e | e
  · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) h
  · exact e

/-- A non-empty chunk is a pointer into an object. -/
theorem chunk_ref {i b : Nat} {w : BPtr} {n : Nat} {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr}
    {I : Heap → BPtr → Nat → Nat → Prop} (cb : BackCallbacks i b w n inCb inDesc outCb outDesc I) {H : Heap}
    {q : BPtr} {k : UInt32} {t : Nat} (hI : I H q k.toNat t) (hk : k ≠ 0) : ∃ r o, q = .ref r o := by
  obtain ⟨⟨r, o, -, he, -, -⟩, -, -⟩ := cb.chunk H q k.toNat t hI (by have := u32_ne_zero hk; omega)
  exact ⟨r, o, he⟩

/-! ## `PULL` -/

/-- `PULL()`: with bytes left, nothing; otherwise one `in()` call, which either hands out a non-empty chunk or ends
the call (`goto inf_leave` with `next = NULL`, `ret = Z_BUF_ERROR`). -/
theorem pull_ok {i b : Nat} {w : BPtr} {n : Nat} {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr}
    {I : Heap → BPtr → Nat → Nat → Prop} (cb : BackCallbacks i b w n inCb inDesc outCb outDesc I) (c : BCtx)
    (hcI : c.inCb = inCb) (hcD : c.inDesc = inDesc) {H : Heap} {l : IL} {t : Nat} (hin : InB I H l t)
    {Q : Except Ex Unit → IL → Heap → Prop}
    (k1 : l.have_ ≠ 0 → Q (.ok ()) l H)
    (k2 : l.have_ = 0 → ∀ H' q, BackKeep H H' i b w → I H' q 0 t →
      Q (.error .leave) { l with have_ := 0, next := .null, ret := Z_BUF_ERROR } H')
    (k3 : l.have_ = 0 → ∀ (k : UInt32) (q : BPtr) H', k ≠ 0 → BackKeep H H' i b w → k.toNat ≤ t →
      InB I H' { l with have_ := k, next := q } (t - k.toNat) →
      Q (.ok ()) { l with have_ := k, next := q } H') :
    SatX H l (PULL c) Q := by
  unfold PULL
  refine SatX.bind (SatX.get ?_)
  dsimp only
  by_cases h0 : l.have_ = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    refine SatX.bind (SatX.get ?_)
    obtain ⟨p, m, hI, -, -⟩ := hin
    obtain ⟨k, q, H', e, hk, hI', hkeep⟩ := cb.input H l.next p m t hI
    refine SatX.bind (SatX.lift (Sat.of_eq (by rw [hcI, hcD]; exact e) ?_))
    dsimp only
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.get ?_)
    dsimp only
    by_cases hk0 : k = 0
    · subst hk0
      simp only [beq_self_eq_true, ↓reduceIte]
      refine SatX.bind (SatX.modify (SatX.bind (SatX.modify (SatX.throw ?_))))
      exact k2 h0 H' q hkeep (by simpa using hI')
    · have hk0' : (k == 0) = false := by simpa using hk0
      simp only [hk0', Bool.false_eq_true, ↓reduceIte]
      refine SatX.pure ?_
      exact k3 h0 k q H' hk0 hkeep hk (InB.fresh k hI' rfl rfl (fun _ => chunk_ref cb hI' hk0))
  · have h0' : (l.have_ == 0) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte]
    exact SatX.pure (k1 h0)

/-! ## `PULLBYTE` -/

/-- The statements of `PULLBYTE()` after its `PULL()`. -/
def pbTail : X Unit := do
  modify fun l => { l with have_ := l.have_ - 1 }
  let l ← get
  let b ← load8 l.next
  let nx ← l.next.add 1
  let sh ← shl64 b.toUInt64 l.bits.toUInt32
  set { l with next := nx, hold := l.hold + sh }
  modify fun l => { l with bits := l.bits + 8 }

theorem pullbyte_eq (c : BCtx) : PULLBYTE c = (PULL c >>= fun _ => pbTail) := rfl

theorem liftEq {α : Type} {H : Heap} {l : IL} {m : M α} {a : α} {Q : Except Ex α → IL → Heap → Prop}
    (e : m H = .ok (a, H)) (q : Q (.ok a) l H) : SatX H l (MonadLiftT.monadLift m : X α) Q :=
  SatX.lift (Sat.of_eq e q)

/-- `l'` differs from `l` only in the bit-buffer locals and `ret`. -/
def Pb (l l' : IL) : Prop :=
  l' = { l with have_ := l'.have_, next := l'.next, hold := l'.hold, bits := l'.bits, ret := l'.ret }

theorem Pb.refl (l : IL) : Pb l l := rfl

theorem Pb.trans {l1 l2 l3 : IL} (a : Pb l1 l2) (b : Pb l2 l3) : Pb l1 l3 := by
  unfold Pb at a b ⊢; rw [b, a]

/-- The byte read of `PULLBYTE()` with a byte left. -/
theorem pbTail_ok {i b : Nat} {w : BPtr} {n : Nat} {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr}
    {I : Heap → BPtr → Nat → Nat → Prop} (cb : BackCallbacks i b w n inCb inDesc outCb outDesc I) {H : Heap}
    {l : IL} {t : Nat} (hin : InB I H l t) (h0 : l.have_ ≠ 0) (hb : l.bits.toNat < 56)
    {Q : Except Ex Unit → IL → Heap → Prop}
    (k : ∀ l', InB I H l' t → l'.have_.toNat + 1 = l.have_.toNat → l'.bits.toNat = l.bits.toNat + 8 →
      Pb l l' → l'.ret = l.ret → Q (.ok ()) l' H) :
    SatX H l pbTail Q := by
  obtain ⟨r, o, d, hnx, hg, hsz⟩ := hin.bytes cb h0
  have hh1 := u32_ne_zero h0
  unfold pbTail
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  rw [hnx]
  have hlo : o < d.size := by omega
  refine SatX.bind (liftEq (a := d[o]) (by simp [load8, Ptr.load, hg, hlo]) ?_)
  have e1 : (Ptr.ref r o).add 1 H = .ok (.ref r (o + 1), H) := by
    have hc : o ≤ d.size ∧ 0 ≤ (o : Int) + 1 ∧ (o : Int) + 1 ≤ (d.size : Int) := by omega
    simp only [Ptr.add, hg, hc, and_self, ↓reduceIte]
    rfl
  refine SatX.bind (liftEq e1 ?_)
  have hb64 : l.bits.toUInt32 < 64 := by
    rw [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32]; show _ < 64; omega
  refine SatX.bind (liftEq (a := (d[o]).toUInt64 <<< l.bits.toUInt32.toUInt64) (by simp [shl64, hb64]) ?_)
  refine SatX.bind (SatX.set ?_)
  refine SatX.modify ?_
  have hb8 : (l.bits + 8).toNat = l.bits.toNat + 8 := by
    rw [UInt8.toNat_add]; show (l.bits.toNat + 8) % 256 = _; omega
  have hsub : (l.have_ - 1).toNat = l.have_.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 1 ≤ _; omega)]; rfl
  refine k _ ?_ (by simp only [hsub]; omega) hb8 rfl rfl
  obtain ⟨p, m, hI, hle, hat⟩ := hin
  obtain ⟨r', o', hp, hn'⟩ := hat h0
  rw [hnx] at hn'
  simp only [Ptr.ref.injEq] at hn'
  obtain ⟨rfl, ho⟩ := hn'
  refine ⟨p, m, hI, by simp only [hsub]; omega, fun _ => ⟨r, o', hp, ?_⟩⟩
  simp only [hsub, Ptr.ref.injEq, true_and]
  omega

/-- `PULLBYTE()` with fewer than 56 bits held: it reads one byte (after an `in()` call when no byte is left) or
leaves; the input measure `8 * (have + t) + bits` stays. -/
theorem pullbyte_ok {i b : Nat} {w : BPtr} {n : Nat} {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr}
    {I : Heap → BPtr → Nat → Nat → Prop} (cb : BackCallbacks i b w n inCb inDesc outCb outDesc I) (c : BCtx)
    (hcI : c.inCb = inCb) (hcD : c.inDesc = inDesc) {H : Heap} {l : IL} {t : Nat} (hin : InB I H l t)
    (hb : l.bits.toNat < 56) {Q : Except Ex Unit → IL → Heap → Prop}
    (kL : ∀ H' q, BackKeep H H' i b w → I H' q 0 t → l.have_ = 0 →
      Q (.error .leave) { l with have_ := 0, next := .null, ret := Z_BUF_ERROR } H')
    (kO : ∀ l' H' t', BackKeep H H' i b w → InB I H' l' t' →
      8 * (l'.have_.toNat + t') + l'.bits.toNat = 8 * (l.have_.toNat + t) + l.bits.toNat →
      l'.bits.toNat = l.bits.toNat + 8 → Pb l l' → l'.ret = l.ret → Q (.ok ()) l' H') :
    SatX H l (PULLBYTE c) Q := by
  rw [pullbyte_eq]
  refine SatX.bind (pull_ok cb c hcI hcD hin ?_ ?_ ?_)
  · intro h0
    exact pbTail_ok cb hin h0 hb fun l' hin' h1 h2 h3 h4 =>
      kO l' H t (BackKeep.refl H i b w) hin' (by omega) h2 h3 h4
  · intro h0 H' q hk hI
    exact kL H' q hk hI h0
  · intro h0 k q H' hk0 hkeep hkt hin'
    have h0' : ({ l with have_ := k, next := q } : IL).have_ ≠ 0 := hk0
    have hh0 : l.have_.toNat = 0 := by rw [h0]; rfl
    exact pbTail_ok cb hin' h0' hb fun l' hin'' h1 h2 h3 h4 =>
      kO l' H' (t - k.toNat) hkeep hin'' (by simp only at h1 h2; omega) h2 (Pb.trans (show Pb l { l with have_ := k, next := q } from rfl) h3) h4

/-! ## `NEEDBITS` -/

/-- `NEEDBITS(n)` of `infback.c` for `n ≤ 32`: it pulls whole bytes until `n` bits are held (the input measure stays),
or leaves with fewer when `in()` has no more input. -/
theorem needbits_ok {i b : Nat} {w : BPtr} {n : Nat} {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr}
    {I : Heap → BPtr → Nat → Nat → Prop} (cb : BackCallbacks i b w n inCb inDesc outCb outDesc I) (c : BCtx)
    (hcI : c.inCb = inCb) (hcD : c.inDesc = inDesc) {H : Heap} {l : IL} {t : Nat} (hin : InB I H l t)
    (k : UInt32) (hk : k.toNat ≤ 32) {Q : Except Ex Unit → IL → Heap → Prop}
    (kL : ∀ l' H' t' q, BackKeep H H' i b w → I H' q 0 t' → Pb l l' → l'.have_ = 0 →
      l'.next = .null → l'.ret = Z_BUF_ERROR → Q (.error .leave) l' H')
    (kO : ∀ l' H' t', BackKeep H H' i b w → InB I H' l' t' →
      8 * (l'.have_.toNat + t') + l'.bits.toNat = 8 * (l.have_.toNat + t) + l.bits.toNat →
      k.toNat ≤ l'.bits.toNat → l'.bits.toNat ≤ max l.bits.toNat (k.toNat + 7) → Pb l l' → l'.ret = l.ret →
      Q (.ok ()) l' H') :
    SatX H l (ZlibNg.Infback.NEEDBITS c k) Q := by
  have hk8 : (k.toUInt8).toNat = k.toNat := by
    rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by omega)
  unfold ZlibNg.Infback.NEEDBITS xwhile
  refine xwhileBrk_rank (fun l' H' => ∃ t', BackKeep H H' i b w ∧ InB I H' l' t' ∧
      8 * (l'.have_.toNat + t') + l'.bits.toNat = 8 * (l.have_.toNat + t) + l.bits.toNat ∧
      l'.bits.toNat ≤ max l.bits.toNat (k.toNat + 7) ∧ Pb l l' ∧ l'.ret = l.ret)
    (fun l' _ => k.toNat - l'.bits.toNat) _ ?_
    ⟨t, BackKeep.refl H i b w, hin, rfl, Nat.le_max_left _ _, Pb.refl l, rfl⟩
    (by unfold fuel; omega)
  rintro l1 H1 ⟨t1, hk1, hin1, hm1, hb1, hp1, hr1⟩
  refine SatX.bind (SatX.get ?_)
  refine SatX.pure ?_
  by_cases hlt : l1.bits < k.toUInt8
  · have hlt' : l1.bits.toNat < k.toNat := by rw [← hk8]; exact hlt
    simp only [hlt, decide_true]
    refine SatX.bind (pullbyte_ok cb c hcI hcD hin1 (by omega) ?_ ?_)
    · intro H' q hk' hI h0
      exact kL _ H' t1 q (BackKeep.trans hk1 hk') hI (Pb.trans hp1 rfl) rfl rfl rfl
    · intro l' H' t' hk' hin' hm' hb' hp' hr'
      exact SatX.pure ⟨⟨t', BackKeep.trans hk1 hk', hin', by omega, by omega, Pb.trans hp1 hp', hr'.trans hr1⟩,
        by omega⟩
  · have hge : k.toNat ≤ l1.bits.toNat := by
      rw [← hk8]; exact Nat.le_of_not_lt (fun h => hlt (UInt8.lt_iff_toNat_lt.mpr h))
    simp only [hlt, decide_false]
    exact kO l1 H1 t1 hk1 hin1 hm1 hge hb1 hp1 hr1

end ZlibNgF.Proof.InfbackPull
