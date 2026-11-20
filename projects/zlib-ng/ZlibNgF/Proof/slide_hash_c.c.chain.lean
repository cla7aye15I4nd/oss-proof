import ZlibNgF.Proof.«slide_hash_c.c.safety»
import ZlibNgF.Proof.«insert_string_p.h.grow»

/-!
# What `slide_hash_c` does to the hash chains (`ZlibNgF`)

`slide_hash_c_chain(table, entries, wsize)` replaces each of the `entries` `Pos` entries `m` from `table` by
`m >= wsize ? m - wsize : 0` (`slid`) and changes no other byte (`SlideTo`). `slide_hash_c` does this on `head`
(`HASH_SIZE` entries) and `prev` (`w_size` entries) with `wsize = (Pos)slide_len`, `slide_hash_head_c` on `head`
only.

In the vocabulary of `ChainSet` (`chain_slide`): the slide by `sl`, a multiple of `w_size` at most `strstart`, maps
the positions `I` to `{q - sl | q ∈ I, q > sl}` and keeps (C1)-(C3) with `strstart - sl` and the limit `lim - sl`;
the slot `q % w` of a kept position does not change. `ChainOk.slide`: the same for `ChainOk`, with the state after
the slide (`strstart` lowered by `sl`, the same lookahead, so `chainLim` lowered by `sl`, also at levels 3..6).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.SlideChain
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNgF.Proof.InsertSafe ZlibNgF.Proof.InsertChain ZlibNgF.Proof.InsertGrow
open ZlibNgF.Proof.DeflateFacts (posAt chainLim ChainOk)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateBits (WrIn)

/-- A `Pos` entry `x` after the slide by `sl`: `x >= sl ? x - sl : 0`. -/
def slid (sl x : Nat) : Nat := if sl ≤ x then x - sl else 0

theorem ite_t' {c : Prop} [Decidable c] {α : Type} {a e : α} (h : c) : (if c then a else e) = a := by simp [h]
theorem ite_f' {c : Prop} [Decidable c] {α : Type} {a e : α} (h : ¬ c) : (if c then a else e) = e := by simp [h]

/-- `d'` is `d` with the `n` `Pos` entries from `base` slid by `sl`, and no other byte changed. -/
def SlideTo (d d' : Array UInt8) (base n sl : Nat) : Prop :=
  WrIn d base (base + 2 * n) d' ∧ ∀ k, k < n → posAt d' base k = slid sl (posAt d base k)

/-- `posAt` of bytes changed only outside the entry. -/
theorem posAt_wrin {d d' : Array UInt8} {lo hi o k : Nat} (w : WrIn d lo hi d')
    (h : o + 2 * k + 1 < lo ∨ hi ≤ o + 2 * k) : posAt d' o k = posAt d o k := by
  unfold posAt; rw [w.2 _ (by omega), w.2 _ (by omega)]

theorem slid_u16 (m w : UInt16) : (if m ≥ w then m - w else 0).toNat = slid w.toNat m.toNat := by
  unfold slid
  by_cases h : w ≤ m
  · have h' : w.toNat ≤ m.toNat := UInt16.le_iff_toNat_le.mp h
    rw [ite_t' h, ite_t' h', UInt16.toNat_sub_of_le _ _ h]
  · have h' : ¬ w.toNat ≤ m.toNat := fun e => h (UInt16.le_iff_toNat_le.mpr e)
    rw [ite_f' h, ite_f' h']; rfl

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem memread2_eq {off : Nat} (hk : off + 2 ≤ d.size) :
    memread2 (Ptr.ref (BRef.heap b) off) (SH H i z b st d) =
      .ok (d[off]!.toUInt16 ||| (d[off + 1]!.toUInt16 <<< 8), SH H i z b st d) := by
  have e0 : index8 (Ptr.ref (BRef.heap b) off) 0 (SH H i z b st d) = .ok (d[off + 0]!, SH H i z b st d) :=
    index8_eq 0 (by omega)
  have e1 : index8 (Ptr.ref (BRef.heap b) off) 1 (SH H i z b st d) = .ok (d[off + 1]!, SH H i z b st d) :=
    index8_eq 1 (by omega)
  simp only [memread2, bind_app, e0, e1]
  rfl

/-- `slide_hash_c_chain` on `entries` entries from `base` in block `b`: no fault, the entries slid by `wsize`. -/
theorem chain_slide_SH {base : Nat} (entries : UInt32) (wsize : UInt16) (he : entries.toNat ≤ 65536)
    (hr : base + 2 * entries.toNat ≤ d.size) :
    Sat (SH H i z b st d) (ZlibNg.SlideHash.slide_hash_c_chain (.ref (.heap b) base) entries wsize)
      (fun _ H' => ∃ d', H' = SH H i z b st d' ∧ SlideTo d d' base entries.toNat wsize.toNat) := by
  unfold ZlibNg.SlideHash.slide_hash_c_chain
  refine Sat.bind (Sat.mono (sat_cwhile (s := ((0 : UInt32), Ptr.ref (BRef.heap b) base))
    (fun (x : UInt32 × BPtr) H' => ∃ k, k ≤ entries.toNat ∧ x.1.toNat = k ∧ x.2 = .ref (.heap b) (base + 2 * k) ∧
      ∃ d0 : Array UInt8, H' = SH H i z b st d0 ∧ SlideTo d d0 base k wsize.toNat)
    (fun x => entries.toNat - x.1.toNat) (fun _ H' => ∃ d', H' = SH H i z b st d' ∧
      SlideTo d d' base entries.toNat wsize.toNat) ?_
    ⟨0, by omega, rfl, by simp, d, rfl, WrIn.refl _ _ _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩ ?_) ?_)
  · rintro ⟨idx, q⟩ H1 ⟨k, hk, hi, hq, d0, rfl, hs, hv⟩
    simp only at hi hq; subst hq
    have hs0 := hs.1
    refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
    · have hk' : k < entries.toNat := by
        have : idx < entries := by simpa using hc
        rw [UInt32.lt_iff_toNat_lt] at this; omega
      refine Sat.bind (Sat.of_eq (memread2_eq (by omega)) ?_)
      refine Sat.bind (Sat.of_eq (memwrite2_eq (d := d0) _ (by omega)) ?_)
      have hw2 := wr2_wrin (d := d0) (off := base + 2 * k)
        (if (d0[base + 2 * k]!.toUInt16 ||| (d0[base + 2 * k + 1]!.toUInt16 <<< 8)) ≥ wsize then
          (d0[base + 2 * k]!.toUInt16 ||| (d0[base + 2 * k + 1]!.toUInt16 <<< 8)) - wsize else 0) (by omega)
      have hold : posAt d0 base k = posAt d base k := posAt_wrin hs (Or.inr (by omega))
      refine Sat.bind (Sat.of_eq (addN_SH 2 (by rw [wr2_size]; omega)) (Sat.pure ⟨⟨k + 1, by omega, ?_, by simp; omega,
        _, rfl, ⟨(hs.widen (lo' := base) (hi' := base + 2 * (k + 1)) (Nat.le_refl _) (by omega)).trans
          (hw2.widen (lo' := base) (hi' := base + 2 * (k + 1)) (by omega) (by omega)) (Nat.le_refl _) (Nat.le_refl _),
          fun j hj => ?_⟩⟩, ?_⟩))
      · rw [UInt32.toNat_add, hi]; simp; omega
      · by_cases ej : j = k
        · subst ej
          rw [posAt_wr2_same _ (by omega), slid_u16, ← hold]
          congr 1
          exact pv_toNat d0 base j
        · rw [posAt_wr2_other _ (by omega) (by omega)]
          exact hv j (by omega)
      · simp only; rw [UInt32.toNat_add, hi]; simp; omega
    · have hk' : k = entries.toNat := by
        have : ¬ idx < entries := by simpa using hc
        rw [UInt32.lt_iff_toNat_lt] at this; omega
      subst hk'
      exact ⟨d0, rfl, hs, hv⟩
  · simp only [fuel]; have := entries.toNat_lt; omega
  · rintro _ _ ⟨d', rfl, hs⟩; exact Sat.pure ⟨d', rfl, hs⟩

/-- `slide_hash_c`: the `head` and `prev` entries slid by `slide_len`, no byte outside the two tables changed. -/
theorem slide_hash_c_slide {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hw : st.w_size.toNat ≤ 32768)
    (hsl : st.slide_len.toNat < 65536) :
    Sat (SH H i z b st d) (ZlibNg.SlideHash.slide_hash_c (some b)) (fun _ H' => ∃ d', H' = SH H i z b st d' ∧
      WrIn d po (ho + 131072) d' ∧
      (∀ k, k < 65536 → posAt d' ho k = slid st.slide_len.toNat (posAt d ho k)) ∧
      (∀ k, k < st.w_size.toNat → posAt d' po k = slid st.slide_len.toNat (posAt d po k))) := by
  have e16 : st.slide_len.toUInt16.toNat = st.slide_len.toNat := by simp; omega
  unfold ZlibNg.SlideHash.slide_hash_c
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  have hhd := L.hd
  have hpw := L.pw
  have hph := L.ph
  refine Sat.bind (Sat.mono (chain_slide_SH (base := ho) HASH_SIZE _ (by decide) (by simp [HASH_SIZE]; omega)) ?_)
  rintro _ _ ⟨d1, rfl, s1⟩
  have hd1 := s1.1.1
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  simp only [L.prev]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.mono (chain_slide_SH (base := po) _ _ (by omega) (by omega)) ?_
  rintro _ _ ⟨d2, rfl, s2⟩
  have hH : HASH_SIZE.toNat = 65536 := rfl
  rw [hH, e16] at s1
  rw [e16] at s2
  refine ⟨d2, rfl, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · exact (s1.1.widen (lo' := po) (hi' := ho + 131072) (by omega) (by omega)).trans
      (s2.1.widen (lo' := po) (hi' := ho + 131072) (by omega) (by omega)) (Nat.le_refl _) (Nat.le_refl _)
  · rw [posAt_wrin s2.1 (Or.inr (by omega))]; exact s1.2 k hk
  · rw [s2.2 k hk, posAt_wrin s1.1 (Or.inl (by omega))]

/-- `slide_hash_head_c`: the `head` entries slid by `slide_len`, no byte outside `head` changed. -/
theorem slide_hash_head_c_slide {wo po ho : Nat} (L : HLay b d.size st wo po ho)
    (hsl : st.slide_len.toNat < 65536) :
    Sat (SH H i z b st d) (ZlibNg.SlideHash.slide_hash_head_c (some b)) (fun _ H' => ∃ d', H' = SH H i z b st d' ∧
      SlideTo d d' ho 65536 st.slide_len.toNat) := by
  have e16 : st.slide_len.toUInt16.toNat = st.slide_len.toNat := by simp; omega
  unfold ZlibNg.SlideHash.slide_hash_head_c
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  have hhd := L.hd
  refine Sat.mono (chain_slide_SH (base := ho) HASH_SIZE _ (by decide) (by simp [HASH_SIZE]; omega)) ?_
  rintro _ _ ⟨d1, rfl, s1⟩
  have hH : HASH_SIZE.toNat = 65536 := rfl
  rw [hH, e16] at s1
  exact ⟨d1, rfl, s1⟩

end

/-! ## The chains after the slide -/

/-- The slide by `sl` (a multiple of `w`, at most `ss`) keeps (C1)-(C3) for the slid positions, with `ss - sl` and
`lim - sl`. -/
theorem chain_slide {d d' : Array UInt8} {ho po w ss lim sl : Nat} {I : Nat → Prop} (hw : 0 < w)
    (C : ChainSet d ho po w ss lim I) (hm : sl % w = 0) (hss : sl ≤ ss)
    (Hh : ∀ k, k < 65536 → posAt d' ho k = slid sl (posAt d ho k))
    (Hp : ∀ k, k < w → posAt d' po k = slid sl (posAt d po k)) :
    ChainSet d' ho po w (ss - sl) (lim - sl) (fun q => 0 < q ∧ I (q + sl)) := by
  refine ⟨fun q hq => ⟨hq.1, by have := (C.c1 _ hq.2).2; omega⟩, fun k hk hne => ?_, fun q hq hin => ?_⟩
  · rw [Hh k hk] at hne ⊢
    unfold slid at hne ⊢
    by_cases e : sl ≤ posAt d ho k
    · rw [ite_t' e] at hne ⊢
      refine ⟨by omega, ?_⟩
      rw [Nat.sub_add_cancel e]
      exact C.c2 k hk (by omega)
    · rw [ite_f' e] at hne; exact absurd rfl hne
  · have hmod : (q + sl) % w = q % w := by
      rw [Nat.add_mod, hm, Nat.add_zero, Nat.mod_mod]
    have h3 := C.c3 _ hq.2 (by omega)
    rw [hmod] at h3
    rw [Hp _ (Nat.mod_lt _ hw)]
    unfold slid
    rcases h3 with h0 | h1
    · rw [h0]; left; split <;> omega
    · by_cases e : sl ≤ posAt d po (q % w)
      · rw [ite_t' e]
        by_cases e2 : posAt d po (q % w) - sl = 0
        · left; exact e2
        · right; exact ⟨by omega, by rw [Nat.sub_add_cancel e]; exact h1⟩
      · rw [ite_f' e]; left; rfl

/-- `ChainOk` after the slide: the state `st'` keeps what `ChainOk` reads except `strstart`, lowered by `sl` (a multiple
of `w_size`, at most `strstart`), and the `head` and `prev` entries of `d'` are those of `d` slid by `sl`. -/
theorem ChainOk.slide {b : Nat} {d d' : Array UInt8} {st st' : DeflateState} {sl : Nat} (C : ChainOk b d st)
    (e1 : st'.level = st.level) (e2 : st'.strategy = st.strategy) (e3 : st'.head = st.head)
    (e4 : st'.prev = st.prev) (e5 : st'.w_size = st.w_size) (e6 : st'.lookahead = st.lookahead)
    (hss : sl ≤ st.strstart.toNat) (e7 : st'.strstart.toNat = st.strstart.toNat - sl)
    (hm : sl % st.w_size.toNat = 0) (hw : 0 < st.w_size.toNat)
    (H : ∀ ho po, st.head = .val (.ref (.heap b) ho) → st.prev = .val (.ref (.heap b) po) →
      (∀ k, k < 65536 → posAt d' ho k = slid sl (posAt d ho k)) ∧
      (∀ k, k < st.w_size.toNat → posAt d' po k = slid sl (posAt d po k))) :
    ChainOk b d' st' := by
  intro h1 h2
  rw [e1] at h1; rw [e1, e2] at h2
  obtain ⟨I, ho, po, hh, hp, c1, c2, c3⟩ := C h1 h2
  obtain ⟨Hh, Hp⟩ := H ho po hh hp
  have CS := chain_slide hw (⟨c1, c2, c3⟩ : ChainSet d ho po st.w_size.toNat st.strstart.toNat (chainLim st) I)
    hm hss Hh Hp
  have hl : chainLim st' = chainLim st - sl := by
    unfold chainLim; rw [e7, e1, e6]; split <;> omega
  refine ⟨fun q => 0 < q ∧ I (q + sl), ho, po, by rw [e3]; exact hh, by rw [e4]; exact hp, fun p hp' => ?_, CS.c2, fun p hp' hs => ?_⟩
  · rw [hl]; exact CS.c1 p hp'
  · rw [e5]; exact CS.c3 p hp' (by rw [← e7, ← e5]; exact hs)

theorem slid_zero (x : Nat) : slid 0 x = x := by simp [slid]

/-- `ChainOk` of a state and bytes that keep what it reads: `level`, `strategy`, `head`, `prev`, `w_size`,
`lookahead`, `strstart`, and the `head` and `prev` entries. -/
theorem ChainOk.keep {b : Nat} {d d' : Array UInt8} {st st' : DeflateState} (C : ChainOk b d st)
    (e1 : st'.level = st.level) (e2 : st'.strategy = st.strategy) (e3 : st'.head = st.head)
    (e4 : st'.prev = st.prev) (e5 : st'.w_size = st.w_size) (e6 : st'.lookahead = st.lookahead)
    (e7 : st'.strstart = st.strstart) (hw : 0 < st.w_size.toNat)
    (H : ∀ ho po, st.head = .val (.ref (.heap b) ho) → st.prev = .val (.ref (.heap b) po) →
      (∀ k, k < 65536 → posAt d' ho k = posAt d ho k) ∧
      (∀ k, k < st.w_size.toNat → posAt d' po k = posAt d po k)) :
    ChainOk b d' st' :=
  ChainOk.slide (sl := 0) C e1 e2 e3 e4 e5 e6 (Nat.zero_le _) (by rw [e7]; rfl) (Nat.zero_mod _) hw
    (fun ho po hh hp => by
      obtain ⟨a, c⟩ := H ho po hh hp
      exact ⟨fun k hk => by rw [slid_zero]; exact a k hk, fun k hk => by rw [slid_zero]; exact c k hk⟩)

/-- `ChainOk` survives a change of the bytes below `prev` (the window). -/
theorem ChainOk.wrin {b D wo po ho lo hi : Nat} {d d' : Array UInt8} {st : DeflateState} (C : ChainOk b d st)
    (L : HLay b D st wo po ho) (w : WrIn d lo hi d') (hhi : hi ≤ po) : ChainOk b d' st :=
  ChainOk.keep C rfl rfl rfl rfl rfl rfl rfl L.w1 (fun ho' po' hh hp => by
    have e1 : ho' = ho := by rw [L.head] at hh; injection hh with e; injection e with _ e; exact e.symm
    have e2 : po' = po := by rw [L.prev] at hp; injection hp with e; injection e with _ e; exact e.symm
    subst e1 e2
    have := L.ph
    exact ⟨fun k _ => posAt_wrin w (Or.inr (by omega)), fun k _ => posAt_wrin w (Or.inr (by omega))⟩)

/-- `ChainOk` of a state that keeps what it reads, on the same bytes. -/
theorem ChainOk.st {b : Nat} {d : Array UInt8} {st st' : DeflateState} (C : ChainOk b d st)
    (e1 : st'.level = st.level) (e2 : st'.strategy = st.strategy) (e3 : st'.head = st.head)
    (e4 : st'.prev = st.prev) (e5 : st'.w_size = st.w_size) (e6 : st'.lookahead = st.lookahead)
    (e7 : st'.strstart = st.strstart) (hw : 0 < st.w_size.toNat) : ChainOk b d st' :=
  ChainOk.keep C e1 e2 e3 e4 e5 e6 e7 hw (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)

/-- `ChainOk` survives a larger lookahead (a larger `chainLim` at levels 3..6). -/
theorem ChainOk.look {b : Nat} {d : Array UInt8} {st st' : DeflateState} (C : ChainOk b d st)
    (e1 : st'.level = st.level) (e2 : st'.strategy = st.strategy) (e3 : st'.head = st.head)
    (e4 : st'.prev = st.prev) (e5 : st'.w_size = st.w_size) (e7 : st'.strstart = st.strstart)
    (hla : st.lookahead.toNat ≤ st'.lookahead.toNat) : ChainOk b d st' :=
  ChainOk.grow (S := fun _ => False) C (fun ho po _ _ => Grow.refl d ho po _ _) e1 e2 e3 e4 e5
    (by rw [e7]; exact Nat.le_refl _) (by unfold chainLim; rw [e7, e1]; split <;> omega) (fun _ h => h.elim)

end ZlibNgF.Proof.SlideChain
