import ZlibNgF.Proof.«inftrees.c.loop»
import ZlibNgF.Proof.«inftrees.c.count»

/-!
# `zng_inflate_table`: before the table-filling loop (`ZlibNgF`)

The loops that find the longest and shortest length, check the Kraft sum (`left`), compute the offsets `offs` and
sort the symbols by length into `work`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

section counts
variable {count : Array UInt16} {h : Heap}

/-- `for (max = MAX_BITS; max >= 1; max--) if (count[max] != 0) break;` -/
theorem max_loop_wp (hcs : count.size = 16) :
    Wp (cwhile
      (fun ((max, done) : UInt32 × Bool) => pure (!done && max >= 1, (max, done)))
      (fun ((max, _) : UInt32 × Bool) => do
        if (← aget count max.toNat) != 0 then pure (max, true) else pure (max - 1, false))
      (MAX_BITS, false)) h
      (fun r h' => h' = h ∧ r.1.toNat ≤ 15 ∧ (∀ L, r.1.toNat < L → L ≤ 15 → cnt count L = 0) ∧
        (1 ≤ r.1.toNat → cnt count r.1.toNat ≠ 0)) := by
  refine Wp.cwhile (fun n (st : UInt32 × Bool) h' => h' = h ∧ st.1.toNat ≤ 15 ∧
      (∀ L, st.1.toNat < L → L ≤ 15 → cnt count L = 0) ∧
      (st.2 = true → 1 ≤ st.1.toNat ∧ cnt count st.1.toNat ≠ 0 ∧ n = 0) ∧
      (st.2 = false → n = st.1.toNat + 1)) _ ?_ (n := 16)
    ⟨rfl, by decide, fun L h1 h2 => by simp [MAX_BITS] at h1; omega, fun e => by simp at e, fun _ => rfl⟩
    (by unfold fuel; omega)
  rintro n ⟨m, dn⟩ h' ⟨rfl, hm, habove, hdone, hnd⟩
  dsimp only at hm habove hdone hnd
  simp only [Wp.pure_iff]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hdn : dn = false := by cases dn <;> simp_all
    subst hdn
    have hm1 : 1 ≤ m.toNat := by
      simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq, ge_iff_le, UInt32.le_iff_toNat_le] at hc
      exact hc
    have hn := hnd rfl
    rw [Wp.bind_iff, aget_ok (by rw [hcs]; omega), Wp.pure_iff]
    have hce : (count[m.toNat]'(by rw [hcs]; omega)).toNat = cnt count m.toNat := cnt_eq _
    by_cases hz : (count[m.toNat]'(by rw [hcs]; omega) != 0) = true
    · rw [ite_eq_left hz, Wp.pure_iff]
      refine ⟨0, by omega, rfl, hm, habove, fun _ => ⟨hm1, ?_, rfl⟩, fun e => by simp at e⟩
      rw [← hce]
      intro e
      apply (bne_iff_ne.mp hz)
      exact UInt16.toNat_inj.mp (by rw [e]; rfl)
    · rw [ite_eq_right hz, Wp.pure_iff]
      have hz' : cnt count m.toNat = 0 := by
        rw [← hce]
        have : count[m.toNat]'(by rw [hcs]; omega) = 0 := by simpa using hz
        rw [this]; rfl
      have hsub : (m - 1).toNat = m.toNat - 1 := u32_sub (by simp; omega)
      refine ⟨m.toNat, by omega, rfl, by dsimp only; omega, fun L h1 h2 => ?_, fun e => by simp at e,
        fun _ => by dsimp only; omega⟩
      dsimp only at h1
      by_cases e : L = m.toNat
      · rw [e]; exact hz'
      · exact habove L (by omega) h2
  · refine ⟨trivial, hm, habove, fun h1 => ?_⟩
    cases dn with
    | true => exact (hdone rfl).2.1
    | false =>
      simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, ge_iff_le, UInt32.le_iff_toNat_le] at hc
      exact absurd h1 hc

/-- `for (min = 1; min < max; min++) if (count[min] != 0) break;` -/
theorem min_loop_wp (hcs : count.size = 16) (mx : UInt32) (hmx : mx.toNat ≤ 15) (hmx1 : 1 ≤ mx.toNat)
    (hcmx : cnt count mx.toNat ≠ 0) (one : (1 : UInt32).toNat = 1 := rfl) :
    Wp (cwhile
      (fun ((min, done) : UInt32 × Bool) => pure (!done && min < mx, (min, done)))
      (fun ((min, _) : UInt32 × Bool) => do
        if (← aget count min.toNat) != 0 then pure (min, true) else pure (min + 1, false))
      ((1 : UInt32), false)) h
      (fun r h' => h' = h ∧ 1 ≤ r.1.toNat ∧ r.1.toNat ≤ mx.toNat ∧ (∀ L, 1 ≤ L → L < r.1.toNat → cnt count L = 0) ∧
        cnt count r.1.toNat ≠ 0) := by
  refine Wp.cwhile (fun n (st : UInt32 × Bool) h' => h' = h ∧ 1 ≤ st.1.toNat ∧ st.1.toNat ≤ mx.toNat ∧
      (∀ L, 1 ≤ L → L < st.1.toNat → cnt count L = 0) ∧
      (st.2 = true → cnt count st.1.toNat ≠ 0 ∧ n = 0) ∧
      (st.2 = false → n = mx.toNat - st.1.toNat + 1)) _ ?_ (n := mx.toNat)
    ⟨rfl, by decide, by dsimp only; omega, fun L h1 h2 => by simp at h2; omega, fun e => by simp at e,
      fun _ => by dsimp only; omega⟩
    (by unfold fuel; omega)
  rintro n ⟨m, dn⟩ h' ⟨rfl, hm1, hm, hbelow, hdone, hnd⟩
  dsimp only at hm1 hm hbelow hdone hnd
  simp only [Wp.pure_iff]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hdn : dn = false := by cases dn <;> simp_all
    subst hdn
    have hlt : m.toNat < mx.toNat := by
      simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq, UInt32.lt_iff_toNat_lt] at hc
      exact hc
    have hn := hnd rfl
    rw [Wp.bind_iff, aget_ok (by rw [hcs]; omega), Wp.pure_iff]
    have hce : (count[m.toNat]'(by rw [hcs]; omega)).toNat = cnt count m.toNat := cnt_eq _
    by_cases hz : (count[m.toNat]'(by rw [hcs]; omega) != 0) = true
    · rw [ite_eq_left hz, Wp.pure_iff]
      refine ⟨0, by omega, rfl, hm1, hm, hbelow, fun _ => ⟨?_, rfl⟩, fun e => by simp at e⟩
      rw [← hce]
      intro e
      apply (bne_iff_ne.mp hz)
      exact UInt16.toNat_inj.mp (by rw [e]; rfl)
    · rw [ite_eq_right hz, Wp.pure_iff]
      have hz' : cnt count m.toNat = 0 := by
        rw [← hce]
        have : count[m.toNat]'(by rw [hcs]; omega) = 0 := by simpa using hz
        rw [this]; rfl
      have one : (1 : UInt32).toNat = 1 := rfl
      have hadd : (m + 1).toNat = m.toNat + 1 := by rw [u32_add (by rw [one]; omega), one]
      refine ⟨mx.toNat - (m.toNat + 1) + 1, by omega, rfl, by dsimp only; omega, by dsimp only; omega,
        fun L h1 h2 => ?_, fun e => by simp at e, fun _ => by dsimp only; omega⟩
      dsimp only at h2
      by_cases e : L = m.toNat
      · rw [e]; exact hz'
      · exact hbelow L h1 (by omega)
  · refine ⟨trivial, hm1, hm, hbelow, ?_⟩
    cases dn with
    | true => exact (hdone rfl).1
    | false =>
      simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, UInt32.lt_iff_toNat_lt] at hc
      have : m.toNat = mx.toNat := by omega
      rw [this]; exact hcmx

/-- The over-subscription check: `left = 2 ^ len - (weight of the lengths below len)`. -/
theorem left_loop_wp (hcs : count.size = 16) :
    Wp (cwhile
      (fun ((left, len, over) : Int32 × UInt32 × Bool) => pure (!over && len <= MAX_BITS, (left, len, over)))
      (fun ((left, len, _) : Int32 × UInt32 × Bool) => do
        let left ← chkI32 (left.toInt * 2)
        let left ← chkI32 (left.toInt - ((← aget count len.toNat).toNat : Int))
        if left < 0 then pure (left, len, true) else pure (left, len + 1, false))
      ((1 : Int32), (1 : UInt32), false)) h
      (fun r h' => h' = h ∧ (r.2.2 = false →
        0 ≤ r.1.toInt ∧ r.1.toInt * 2 + (wsum (cnt count) 15 : Int) = 2 ^ 16)) := by
  refine Wp.cwhile (fun n (st : Int32 × UInt32 × Bool) h' => h' = h ∧
      (st.2.2 = false → 1 ≤ st.2.1.toNat ∧ st.2.1.toNat ≤ 16 ∧ 0 ≤ st.1.toInt ∧
        st.1.toInt * ((2 ^ (17 - st.2.1.toNat) : Nat) : Int) + (wsum (cnt count) (st.2.1.toNat - 1) : Int) =
          2 ^ 16 ∧ n = 17 - st.2.1.toNat) ∧
      (st.2.2 = true → n = 0)) _ ?_ (n := 16)
    ⟨rfl, fun _ => ⟨by decide, by decide, by decide, by dsimp only; simp, by decide⟩, fun e => by simp at e⟩
    (by unfold fuel; omega)
  rintro n ⟨lf, len, ov⟩ h' ⟨rfl, hnov, hov⟩
  dsimp only at hnov hov
  simp only [Wp.pure_iff]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hdn : ov = false := by cases ov <;> simp_all
    subst hdn
    obtain ⟨hl1, hl16, hlf0, hinv, rfl⟩ := hnov rfl
    have hl15 : len.toNat ≤ 15 := by
      simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq, UInt32.le_iff_toNat_le] at hc
      exact hc
    have hB : 2 ^ (17 - len.toNat) = 2 * 2 ^ (16 - len.toNat) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hpos := Nat.two_pow_pos (16 - len.toNat)
    have hle : lf.toInt ≤ 32768 := by
      have : lf.toInt * 2 ≤ lf.toInt * ((2 ^ (17 - len.toNat) : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left (by rw [hB]; exact_mod_cast (show 2 ≤ 2 * 2 ^ (16 - len.toNat) by omega)) hlf0
      omega
    rw [Wp.bind_iff, chkI32_ok (by omega) (by omega), Wp.pure_iff, Wp.bind_iff,
      aget_ok (by rw [hcs]; omega), Wp.pure_iff, Wp.bind_iff]
    rw [cnt_eq]
    have hcb : cnt count len.toNat ≤ 65535 := by
      unfold cnt; have := (count[len.toNat]!).toNat_lt; omega
    have e1 := i32_ok (v := lf.toInt * 2) (by omega) (by omega)
    rw [e1, chkI32_ok (by omega) (by omega), Wp.pure_iff]
    have e2 := i32_ok (v := lf.toInt * 2 - (cnt count len.toNat : Int)) (by omega) (by omega)
    have hw : wsum (cnt count) len.toNat = wsum (cnt count) (len.toNat - 1) +
        cnt count len.toNat * 2 ^ (16 - len.toNat) := by
      have := wsum_succ (cnt count) (len.toNat - 1)
      rw [show len.toNat - 1 + 1 = len.toNat by omega, show 15 - (len.toNat - 1) = 16 - len.toNat by omega] at this
      exact this
    by_cases hneg : Int32.ofInt (lf.toInt * 2 - (cnt count len.toNat : Int)) < 0
    · rw [ite_eq_left hneg, Wp.pure_iff]
      exact ⟨0, by omega, rfl, fun e => by simp at e, fun _ => rfl⟩
    · rw [ite_eq_right hneg, Wp.pure_iff]
      rw [Int32.lt_iff_toInt_lt, e2] at hneg
      have : (0 : Int32).toInt = 0 := rfl
      rw [this] at hneg
      have one : (1 : UInt32).toNat = 1 := rfl
      have hadd : (len + 1).toNat = len.toNat + 1 := by rw [u32_add (by rw [one]; omega), one]
      refine ⟨17 - (len.toNat + 1), by omega, rfl, fun _ => ⟨by rw [hadd]; omega, by rw [hadd]; omega,
        by rw [e2]; omega, ?_, by rw [hadd]⟩, fun e => by simp at e⟩
      rw [hadd, e2, show len.toNat + 1 - 1 = len.toNat by omega, hw,
        show 17 - (len.toNat + 1) = 16 - len.toNat by omega]
      rw [hB] at hinv
      push_cast at hinv ⊢
      have : (lf.toInt * 2 - (cnt count len.toNat : Int)) * (2 : Int) ^ (16 - len.toNat) =
          lf.toInt * (2 * (2 : Int) ^ (16 - len.toNat)) - (cnt count len.toNat : Int) * (2 : Int) ^ (16 - len.toNat) := by
        rw [Int.sub_mul, Int.mul_assoc]
      rw [this]
      omega
  · refine ⟨trivial, fun hov' => ?_⟩
    obtain ⟨hl1, hl16, hlf0, hinv, -⟩ := hnov hov'
    subst hov'
    have h16 : len.toNat = 16 := by
      simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, UInt32.le_iff_toNat_le] at hc
      have : (MAX_BITS : UInt32).toNat = 15 := rfl
      omega
    rw [h16] at hinv
    exact ⟨hlf0, by simpa using hinv⟩

/-- `for` over `List.range' k n` with an invariant indexed by the next element. -/
theorem forIn_range'_wp {β : Type} (f : Nat → β → M (ForInStep β)) (I : Nat → β → Heap → Prop) :
    ∀ n k b h, I k b h →
      (∀ j b h, k ≤ j → j < k + n → I j b h → Wp (f j b) h (fun r h' => ∃ b', r = .yield b' ∧ I (j + 1) b' h')) →
      Wp (forIn (List.range' k n) b f) h (fun b' h' => I (k + n) b' h') := by
  intro n
  induction n with
  | zero => intro k b h hI _; simpa using hI
  | succ n ih =>
    intro k b h hI hstep
    rw [List.range'_succ, List.forIn_cons, Wp.bind_iff]
    refine Wp.mono (hstep k b h (Nat.le_refl _) (by omega) hI) ?_
    rintro r h' ⟨b', rfl, hI'⟩
    simp only
    have := ih (k + 1) b' h' hI' (fun j b h h1 h2 hI => hstep j b h (by omega) (by omega) hI)
    rw [show k + 1 + n = k + (n + 1) by omega] at this
    exact this

/-- `offs[len + 1] = offs[len] + count[len]` for `len = 1 .. 14`. -/
theorem offs_loop_wp (hcs : count.size = 16) (hn : nsum (cnt count) 15 < 2 ^ 16) (o0 : Array UInt16)
    (ho0 : o0.size = 16) (ho1 : cnt o0 1 = 0) :
    Wp (forIn [1:15] o0 (fun len (offs : Array UInt16) => do
        let a ← aget offs len
        let c ← aget count len
        let x ← aset offs (len + 1) (a + c)
        pure (ForInStep.yield x))) h
      (fun offs h' => h' = h ∧ offs.size = 16 ∧ ∀ L, 1 ≤ L → L ≤ 15 → cnt offs L = nsum (cnt count) (L - 1)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have := forIn_range'_wp (fun len (offs : Array UInt16) => do
        let a ← aget offs len
        let c ← aget count len
        let x ← aset offs (len + 1) (a + c)
        pure (ForInStep.yield x))
    (fun k offs h' => h' = h ∧ offs.size = 16 ∧ ∀ L, 1 ≤ L → L ≤ k → cnt offs L = nsum (cnt count) (L - 1))
    14 1 o0 h ⟨rfl, ho0, fun L h1 h2 => by have : L = 1 := by omega
                                           subst this; simpa using ho1⟩ ?_
  · refine Wp.mono this ?_
    rintro offs h' ⟨rfl, hs, hv⟩
    exact ⟨rfl, hs, fun L h1 h2 => hv L h1 (by omega)⟩
  · rintro j offs h' h1 h2 ⟨rfl, hs, hv⟩
    rw [Wp.bind_iff, aget_ok (by omega), Wp.pure_iff, Wp.bind_iff, aget_ok (by omega), Wp.pure_iff,
      Wp.bind_iff, aset_ok (by omega), Wp.pure_iff, Wp.pure_iff]
    refine ⟨_, rfl, rfl, by simp [hs], fun L hL1 hL2 => ?_⟩
    rw [cnt_set (by omega)]
    split
    · rename_i e
      subst e
      rw [UInt16.toNat_add, cnt_eq, cnt_eq, hv j h1 (Nat.le_refl _)]
      have := nsum_succ (cnt count) (j - 1)
      rw [show j - 1 + 1 = j by omega] at this
      have hm := nsum_mono (cnt count) (show j ≤ 15 by omega)
      rw [show j + 1 - 1 = j by omega, Nat.mod_eq_of_lt (by omega)]
      omega
    · exact hv L hL1 (by omega)

end counts

theorem lcount_mono (f : Nat → Nat) {k n : Nat} (h : k ≤ n) (v : Nat) : lcount f k v ≤ lcount f n v := by
  induction n with
  | zero => have : k = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    by_cases e : k = n + 1
    · subst e; exact Nat.le_refl _
    · rw [lcount_succ]; have := ih (by omega); omega

theorem nsum_lcount_le (f : Nat → Nat) (n m : Nat) : nsum (fun L => lcount f n L) m ≤ n := by
  induction n with
  | zero => exact Nat.le_of_eq (nsum_eq_zero (fun L _ _ => rfl))
  | succ n ih =>
    have e : nsum (fun L => lcount f (n + 1) L) m =
        nsum (fun L => lcount f n L) m + nsum (fun L => if f n = L then 1 else 0) m := by
      unfold nsum
      rw [← ssum_add]
      apply ssum_congr
      intro i _
      exact lcount_succ f n (i + 1)
    rw [e, nsum_ind]
    split <;> omega

/-- `lens[lo + j]` as a number. -/
def lensf (s : InflateState) (lo j : Nat) : Nat := (s.lens[lo + j]!).toNat

/-- The sort of the symbols by length into `work`. -/
theorem sort_loop_wp {h0 : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h0 b s) {lo : Nat} {codes : UInt32}
    (hlo : lo + codes.toNat ≤ s.lens.size) (hc : codes.toNat ≤ 288)
    (hval : ∀ j, j < codes.toNat → lensf s lo j ≤ 15) (hwork : codes.toNat ≤ s.work.size)
    {c0 : Nat → Nat} (hc0 : ∀ L, 1 ≤ L → L ≤ 15 → c0 L = lcount (lensf s lo) codes.toNat L)
    (o0 : Array UInt16) (ho0 : o0.size = 16) (ho : ∀ L, 1 ≤ L → L ≤ 15 → cnt o0 L = nsum c0 (L - 1)) :
    Wp (cwhile
      (fun ((offs, sym) : Array UInt16 × UInt32) => pure (sym < codes, (offs, sym)))
      (fun ((offs, sym) : Array UInt16 × UInt32) => do
        let l ← Ptr.index (.ref (WRef.lens b) lo) (Int.ofNat sym.toNat)
        if l != 0 then
          let o ← aget offs l.toNat
          Ptr.store (← (Ptr.ref (WRef.work b) 0).add (Int.ofNat o.toNat)) sym.toUInt16
          let offs ← aset offs l.toNat (o + 1)
          pure (offs, sym + 1)
        else pure (offs, sym + 1))
      (o0, 0)) (setCW h0 b s s.codes s.work)
      (fun _ h' => ∃ W, h' = setCW h0 b s s.codes W ∧ W.size = s.work.size ∧
        ∀ L, 1 ≤ L → L ≤ 15 → ∀ j, nsum c0 (L - 1) ≤ j → j < nsum c0 L →
          (W[j]!).toNat < codes.toNat ∧ lensf s lo (W[j]!).toNat = L) := by
  have hn : nsum c0 15 ≤ codes.toNat := by
    rw [nsum_congr (fun L h1 h2 => hc0 L h1 h2)]
    exact nsum_lcount_le _ _ _
  have hns : ∀ L, 1 ≤ L → L ≤ 15 → nsum c0 (L - 1) + c0 L = nsum c0 L := by
    intro L h1 h2
    have := nsum_succ c0 (L - 1)
    rw [show L - 1 + 1 = L by omega] at this
    omega
  refine Wp.cwhile (fun n (st : Array UInt16 × UInt32) h' => ∃ W, h' = setCW h0 b s s.codes W ∧
      W.size = s.work.size ∧ st.1.size = 16 ∧ st.2.toNat ≤ codes.toNat ∧ n = codes.toNat - st.2.toNat ∧
      (∀ L, 1 ≤ L → L ≤ 15 → cnt st.1 L = nsum c0 (L - 1) + lcount (lensf s lo) st.2.toNat L) ∧
      (∀ L, 1 ≤ L → L ≤ 15 → ∀ j, nsum c0 (L - 1) ≤ j →
        j < nsum c0 (L - 1) + lcount (lensf s lo) st.2.toNat L →
        (W[j]!).toNat < st.2.toNat ∧ lensf s lo (W[j]!).toNat = L)) _ ?_
    ⟨s.work, rfl, rfl, ho0, by simp, rfl, fun L h1 h2 => by simp [ho L h1 h2],
      fun L h1 h2 j hj1 hj2 => by simp at hj2; omega⟩ (by unfold fuel; omega)
  rintro n ⟨offs, sym⟩ h' ⟨W, rfl, hWs, hos, hk, rfl, hcnt, hsorted⟩
  dsimp only at hos hk hcnt hsorted
  simp only [Wp.pure_iff]
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have hlt' : sym.toNat < codes.toNat := by simpa [UInt32.lt_iff_toNat_lt] using hlt
    have one : (1 : UInt32).toNat = 1 := rfl
    have hs1 : (sym + 1).toNat = sym.toNat + 1 := by rw [u32_add (by rw [one]; omega), one]
    rw [Wp.bind_iff]
    refine Wp.of_eq (index_nat (get_lens hl s.codes W) (by omega)) ?_
    have hl15 := hval sym.toNat hlt'
    unfold lensf at hl15
    by_cases hz : (s.lens[lo + sym.toNat]! != 0) = true
    · rw [ite_eq_left hz]
      have hL1 : 1 ≤ (s.lens[lo + sym.toNat]!).toNat := by
        have : s.lens[lo + sym.toNat]! ≠ 0 := bne_iff_ne.mp hz
        have : (s.lens[lo + sym.toNat]!).toNat ≠ 0 := fun e => this (UInt16.toNat_inj.mp (by rw [e]; rfl))
        omega
      generalize hLd : (s.lens[lo + sym.toNat]!).toNat = L at hL1 hl15
      have hLf : lensf s lo sym.toNat = L := hLd
      rw [Wp.bind_iff, aget_ok (by omega), Wp.pure_iff]
      have ho' := hcnt L hL1 hl15
      rw [← cnt_eq (a := offs) (L := L) (by omega)] at ho'
      have hlc : lcount (lensf s lo) (sym.toNat + 1) L = lcount (lensf s lo) sym.toNat L + 1 := by
        rw [lcount_succ, ite_eq_left hLf]
      have hlcm := lcount_mono (lensf s lo) (show sym.toNat + 1 ≤ codes.toNat by omega) L
      have hcL := hc0 L hL1 hl15
      have hnsL := hns L hL1 hl15
      have hnmono := nsum_mono c0 (show L ≤ 15 by omega)
      have hob : (offs[L]'(by omega)).toNat + 1 ≤ nsum c0 L := by omega
      rw [Wp.bind_iff]
      have hio : Int.ofNat (offs[L]'(by omega)).toNat = ((offs[L]'(by omega)).toNat : Int) := rfl
      rw [hio]
      refine Wp.of_eq (add_ok (get_work hl s.codes W) (by simp) (by omega) (by simp; omega)) ?_
      rw [show ((0 : Nat) : Int) + ((offs[L]'(by omega)).toNat : Int) = ((offs[L]'(by omega)).toNat : Nat) by simp,
        Int.toNat_natCast, Wp.bind_iff]
      refine Wp.of_eq (store_work hl (by omega) _) ?_
      rw [Wp.bind_iff, aset_ok (by omega), Wp.pure_iff, Wp.pure_iff]
      refine ⟨codes.toNat - (sym.toNat + 1), by omega, _, rfl, by simp [hWs], by simp [hos],
        by dsimp only; rw [hs1]; omega, by dsimp only; rw [hs1], ?_, ?_⟩
      · intro L' h1 h2
        rw [cnt_set (by omega), hs1, lcount_succ]
        split
        · rename_i e; subst e
          rw [UInt16.toNat_add, Nat.mod_eq_of_lt (by have : (1 : UInt16).toNat = 1 := rfl; rw [this]; omega)]
          rw [ite_eq_left hLf]
          have : (1 : UInt16).toNat = 1 := rfl
          omega
        · rename_i e
          rw [ite_eq_right (by rw [hLf]; exact Ne.symm e)]
          simpa using hcnt L' h1 h2
      · intro L' h1 h2 j hj1 hj2
        dsimp only at hj2
        have hj2o := hj2
        rw [hs1] at hj2o
        have hlm' := lcount_mono (lensf s lo) (show sym.toNat + 1 ≤ codes.toNat by omega) L'
        have hc0' := hc0 L' h1 h2
        rw [hs1, lcount_succ] at hj2
        have hset : ∀ i, (W.set! (offs[L]'(by omega)).toNat sym.toUInt16)[i]! =
            if i = (offs[L]'(by omega)).toNat then sym.toUInt16 else W[i]! := by
          intro i
          by_cases e : i = (offs[L]'(by omega)).toNat
          · rw [e, ite_eq_left rfl, getElem!_pos (W.set! (offs[L]'(by omega)).toNat sym.toUInt16) _ (by simp; omega)]
            simp
          · rw [ite_eq_right e]
            by_cases hi : i < W.size
            · rw [getElem!_pos (W.set! (offs[L]'(by omega)).toNat sym.toUInt16) i (by simp; omega),
                getElem!_pos W i hi]
              simp only [Array.set!_eq_setIfInBounds]
              rw [Array.getElem_setIfInBounds_ne hi (Ne.symm e)]
            · rw [getElem!_neg (W.set! (offs[L]'(by omega)).toNat sym.toUInt16) i (by simp; omega),
                getElem!_neg W i hi]
        rw [hset]
        by_cases e : j = (offs[L]'(by omega)).toNat
        · rw [ite_eq_left e]
          have hsym16 : sym.toUInt16.toNat = sym.toNat := by
            rw [UInt32.toNat_toUInt16]; exact Nat.mod_eq_of_lt (by omega)
          rw [hsym16]
          refine ⟨by dsimp only; rw [hs1]; omega, ?_⟩
          rw [hLf]
          -- the class of j is L
          apply Classical.byContradiction
          intro hne
          rcases Nat.lt_or_gt_of_ne hne with hlt2 | hgt2
          · have := nsum_mono c0 (show L ≤ L' - 1 by omega)
            omega
          · have := nsum_mono c0 (show L' ≤ L - 1 by omega)
            have := hns L' h1 h2
            omega
        · rw [ite_eq_right e]
          have hj2' : j < nsum c0 (L' - 1) + lcount (lensf s lo) sym.toNat L' := by
            split at hj2
            · rename_i e2
              have : L' = L := by rw [← hLf, e2]
              subst this
              omega
            · omega
          have := hsorted L' h1 h2 j hj1 hj2'
          exact ⟨by dsimp only; rw [hs1]; omega, this.2⟩
    · rw [ite_eq_right hz, Wp.pure_iff]
      have hL0 : lensf s lo sym.toNat = 0 := by
        unfold lensf
        have : s.lens[lo + sym.toNat]! = 0 := by simpa using hz
        rw [this]; rfl
      refine ⟨codes.toNat - (sym.toNat + 1), by omega, W, rfl, hWs, hos, by dsimp only; rw [hs1]; omega,
        by dsimp only; rw [hs1], ?_, ?_⟩
      · intro L h1 h2
        rw [hs1, lcount_succ, ite_eq_right (by omega)]
        simpa using hcnt L h1 h2
      · intro L h1 h2 j hj1 hj2
        rw [hs1, lcount_succ, ite_eq_right (by omega)] at hj2
        have := hsorted L h1 h2 j hj1 (by simpa using hj2)
        exact ⟨by dsimp only; rw [hs1]; omega, this.2⟩
  · have hk' : sym.toNat = codes.toNat := by
      have : ¬ sym.toNat < codes.toNat := by simpa [UInt32.lt_iff_toNat_lt] using hge
      omega
    refine ⟨W, rfl, hWs, fun L h1 h2 j hj1 hj2 => ?_⟩
    have := hsorted L h1 h2 j hj1 (by rw [hk', ← hc0 L h1 h2, hns L h1 h2]; exact hj2)
    exact ⟨by omega, this.2⟩

end ZlibNgF.Proof.Inftrees
