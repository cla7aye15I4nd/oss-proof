import ZlibNgF.Proof.«adler32_c.c.kernel»
import ZlibNgF.Spec.Safety.Goals

/-!
# `adler32_c` does not fault on a readable buffer (`ZlibNgF`)

The safety half of the Adler-32 kernel: `adler32_c` on `len` readable bytes terminates without fault and leaves the
heap unchanged (`adler32_c_safe`). The alignment prefix (`adler32_copy_align`), the `NMAX` blocks of 64-bit SWAR
chunks (`swar_ok`) and the tail (`adler32_copy_tail`) stay inside the buffer; the sums are not tracked here.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Adler32Safe
open C ZlibNg.Zbuild ZlibNg.Adler32P ZlibNg.Adler32C
open ZlibNgF.Proof.Adler32Kernel

theorem nat_and_mask (n : Nat) (hn : n < 2 ^ 64) : n &&& ((2 ^ 61 - 1) <<< 3) = (n / 8) <<< 3 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hi : 3 ≤ i
  · have e : (n / 8).testBit (i - 3) = n.testBit i := by
      rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_div_two_pow]; congr 1; omega
    rw [e]
    by_cases h2 : i - 3 < 61
    · simp [hi, h2]
    · have : n.testBit i = false := by
        apply Nat.testBit_lt_two_pow
        calc n < 2 ^ 64 := hn
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      simp [hi, h2, this]
  · simp [hi]

theorem align_down8 (v : UInt64) : (ALIGN_DOWN v 8).toNat = v.toNat / 8 * 8 := by
  unfold ALIGN_DOWN
  rw [UInt64.toNat_and]
  have : (~~~((8 : UInt64) - 1)).toNat = (2 ^ 61 - 1) <<< 3 := by decide
  rw [this, nat_and_mask _ v.toNat_lt, Nat.shiftLeft_eq]

theorem and7 (v : UInt64) : (v &&& 7).toNat = v.toNat % 8 := by
  rw [UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod v.toNat 3

/-- A `size_t` below 4 is one of 0, 1, 2, 3. -/
theorem lt4 (v : UInt64) (h : v.toNat < 4) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  have e : v = UInt64.ofNat v.toNat := by simp
  rcases (by omega : v.toNat = 0 ∨ v.toNat = 1 ∨ v.toNat = 2 ∨ v.toNat = 3) with h0 | h0 | h0 | h0 <;>
    rw [e, h0] <;> simp

theorem fuel_lt (v : UInt64) : v.toNat < fuel := by unfold fuel; exact v.toNat_lt

theorem min_chunk (v : UInt64) (h8 : 8 ≤ v.toNat) :
    let c := MIN (ALIGN_DOWN v 8) ADLER32_SWAR_MAX_BYTES
    8 ≤ c.toNat ∧ c.toNat ≤ 184 ∧ c.toNat % 8 = 0 ∧ c.toNat ≤ v.toNat := by
  intro c
  have ha := align_down8 v
  have e184 : ADLER32_SWAR_MAX_BYTES.toNat = 184 := rfl
  by_cases hc : ALIGN_DOWN v 8 > ADLER32_SWAR_MAX_BYTES
  · have : c = ADLER32_SWAR_MAX_BYTES := by simp [c, MIN, hc]
    rw [this, e184]
    have : 184 < (ALIGN_DOWN v 8).toNat := by rw [← e184]; exact hc
    omega
  · have : c = ALIGN_DOWN v 8 := by simp [c, MIN, hc]
    have hc' : ¬ 184 < (ALIGN_DOWN v 8).toNat := by rw [← e184]; exact hc
    rw [this, ha]
    omega

/-- `adler32_copy_tail` without copy on `len` readable bytes. -/
theorem tail_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data) (a s : UInt32)
    (o : Nat) (len : UInt64) (REBASE MAX : Int32) (hle : o + len.toNat ≤ data.size) :
    Ok h (adler32_copy_tail a .null (.ref r o) len s REBASE MAX 0) (fun _ => True) := by
  unfold adler32_copy_tail
  simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have fin : ∀ (x y : UInt32), Ok h ((have __do_jp := fun (_ : Unit) (adler sum2 : UInt32) =>
      (pure (adler ||| sum2 <<< 16) : M UInt32)
    if (REBASE != 0) = true then __do_jp () (x % BASE) (y % BASE) else __do_jp () x y)) (fun _ => True) := by
    intro x y; dsimp only; split <;> exact Ok.pure trivial
  split
  · refine Ok.bind (cwhile_measure (fun st : TailState => st.dst = .null ∧ ∃ o', st.buf = .ref r o' ∧
      o' + st.len.toNat ≤ data.size) (fun st => st.len.toNat) (fun st : TailState => st.dst = .null ∧ ∃ o',
      st.buf = .ref r o' ∧ o' + st.len.toNat ≤ data.size) ?_ ⟨rfl, o, rfl, hle⟩ (fuel_lt _)) (fun s1 hs1 => ?_)
    · rintro ⟨a1, s1, d1, b1, l1⟩ ⟨hd, o', hb, hl⟩
      dsimp only at hd hb hl ⊢
      subst hd hb
      split
      · rename_i h8
        have h8' : 8 ≤ l1.toNat := h8
        refine Ok.bind (P := fun v => v = h.baseAddr r + UInt64.ofNat o') ⟨_, rfl, rfl⟩
          (fun addr haddr => Ok.pure ⟨fun hc => ?_, fun _ => ⟨rfl, o', rfl, hl⟩⟩)
        subst haddr
        have hal : (h.baseAddr r + UInt64.ofNat o').toNat % 8 = 0 := by
          have : ((h.baseAddr r + UInt64.ofNat o') &&& 7) = 0 := by simpa using hc
          rw [← and7, this]; rfl
        obtain ⟨c8, c184, cm, cle⟩ := min_chunk l1 h8'
        dsimp only
        refine Ok.bind (swar_ok hg a1 s1 o' _ hal c8 c184 cm (by omega)) (fun v _ => ?_)
        obtain ⟨va, vs⟩ := v
        dsimp only
        refine Ok.bind (ptr_add_ok hg _ (by omega)) (fun p hp => ?_)
        subst hp
        refine Ok.pure ⟨⟨rfl, _, rfl, ?_⟩, ?_⟩
        · show o' + _ + (l1 - _).toNat ≤ data.size
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; omega
        · show (l1 - _).toNat < l1.toNat
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; omega
      · exact Ok.pure ⟨fun hc => absurd hc (by simp), fun _ => ⟨rfl, o', rfl, hl⟩⟩
    · refine Ok.bind (cwhile_measure (fun st : TailState => st.dst = .null ∧ ∃ o', st.buf = .ref r o' ∧
        o' + st.len.toNat ≤ data.size) (fun st => st.len.toNat) (fun st : TailState => (st.dst = .null ∧ ∃ o',
        st.buf = .ref r o' ∧ o' + st.len.toNat ≤ data.size) ∧ st.len.toNat < 4) ?_ hs1 (fuel_lt _))
        (fun s2 hs2 => ?_)
      · rintro ⟨a1, s1, d1, b1, l1⟩ ⟨hd, o', hb, hl⟩
        dsimp only at hd hb hl ⊢
        subst hd hb
        refine Ok.pure ⟨fun hc => ?_, fun hc => ⟨⟨rfl, o', rfl, hl⟩, ?_⟩⟩
        · have h4 : 4 ≤ l1.toNat := by simpa [UInt64.le_iff_toNat_le] using hc
          dsimp only
          refine Ok.bind (adler_do4_ok hg a1 s1 (o := o') 0 (by decide) (by simp; omega)) (fun v _ => ?_)
          obtain ⟨va, vs⟩ := v
          dsimp only
          refine Ok.bind (ptr_add_ok hg 4 (by omega)) (fun p hp => ?_)
          subst hp
          have e4 : (l1 - 4).toNat = l1.toNat - 4 := UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le]; simpa using h4)
          exact Ok.pure ⟨⟨rfl, _, rfl, by show o' + 4 + (l1 - 4).toNat ≤ _; omega⟩,
            by show (l1 - 4).toNat < l1.toNat; omega⟩
        · simpa [UInt64.le_iff_toNat_le] using hc
      · obtain ⟨⟨hd, o', hb, hl⟩, h4⟩ := hs2
        obtain ⟨a2, s2', d2, b2, l2⟩ := s2
        dsimp only at hd hb hl h4 ⊢
        subst hd hb
        rcases lt4 l2 h4 with rfl | rfl | rfl | rfl
        · simp only [show ((0 : UInt64) &&& 2 != 0) = false from rfl, show ((0 : UInt64) &&& 1 != 0) = false from rfl,
            Bool.false_eq_true, ↓reduceIte]
          exact fin a2 s2'
        · simp only [show ((1 : UInt64) &&& 2 != 0) = false from rfl, show ((1 : UInt64) &&& 1 != 0) = true from rfl,
            Bool.false_eq_true, ↓reduceIte]
          refine Ok.bind (adler_do1_ok hg a2 s2' (o := o') 0 (by decide) (by simp at hl ⊢; omega)) (fun v _ => ?_)
          obtain ⟨va, vs⟩ := v
          exact fin va vs
        · simp only [show ((2 : UInt64) &&& 2 != 0) = true from rfl, show ((2 : UInt64) &&& 1 != 0) = false from rfl,
            Bool.false_eq_true, ↓reduceIte]
          refine Ok.bind (adler_do2_ok hg a2 s2' (o := o') 0 (by decide) (by simp at hl ⊢; omega)) (fun v _ => ?_)
          obtain ⟨va, vs⟩ := v
          refine Ok.bind (ptr_add_ok hg 2 (by simp at hl; omega)) (fun p hp => ?_)
          exact fin va vs
        · simp only [show ((3 : UInt64) &&& 2 != 0) = true from rfl, show ((3 : UInt64) &&& 1 != 0) = true from rfl,
            ↓reduceIte]
          refine Ok.bind (adler_do2_ok hg a2 s2' (o := o') 0 (by decide) (by simp at hl ⊢; omega)) (fun v _ => ?_)
          obtain ⟨va, vs⟩ := v
          refine Ok.bind (ptr_add_ok hg 2 (by simp at hl; omega)) (fun p hp => ?_)
          subst hp
          refine Ok.bind (adler_do1_ok hg va vs (o := o' + 2) 0 (by decide) (by simp at hl ⊢; omega))
            (fun w _ => ?_)
          obtain ⟨wa, ws⟩ := w
          exact fin wa ws
  · exact fin a s

/-- A `size_t` below 8. -/
theorem lt8 (v : UInt64) (h : v.toNat < 8) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by
  have e : v = UInt64.ofNat v.toNat := by simp
  rcases (by omega : v.toNat = 0 ∨ v.toNat = 1 ∨ v.toNat = 2 ∨ v.toNat = 3 ∨ v.toNat = 4 ∨ v.toNat = 5 ∨
    v.toNat = 6 ∨ v.toNat = 7) with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 <;> rw [e, h0] <;> simp

/-- `adler32_copy_align`'s loop over the whole groups of four bytes. -/
theorem align_loop {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data) (st : Do4State)
    (o' : Nat) (hb : st.buf = .ref r o') (hd : st.dst = .null) (hle : o' + 4 * (st.len.toNat / 4) ≤ data.size) :
    Ok h (cwhile (fun (s : Do4State) => pure (decide (s.len ≥ 4), s))
      (fun (s : Do4State) => do
        let mut dst := s.dst
        if (0 : Int32) != 0 then
          Ptr.memcpy dst s.buf 4
          dst ← dst.add 4
        let len := s.len - 4
        let (adler, sum2) ← adler_do4 s.adler s.sum2 s.buf 0
        let buf ← s.buf.add 4
        pure { adler, sum2, dst, buf, len }) st) (fun _ => True) := by
  refine cwhile_measure (fun st : Do4State => st.dst = .null ∧ ∃ o', st.buf = .ref r o' ∧
    o' + 4 * (st.len.toNat / 4) ≤ data.size) (fun st => st.len.toNat) (fun _ => True) ?_ ⟨hd, o', hb, hle⟩
    (fuel_lt _)
  rintro ⟨a1, s1, d1, b1, l1⟩ ⟨hd, o', hb, hl⟩
  dsimp only at hd hb hl ⊢
  subst hd hb
  refine Ok.pure ⟨fun hc => ?_, fun _ => trivial⟩
  have h4 : 4 ≤ l1.toNat := by simpa [UInt64.le_iff_toNat_le] using hc
  simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Ok.bind (adler_do4_ok hg a1 s1 (o := o') 0 (by decide) (by simp; omega)) (fun v _ => ?_)
  obtain ⟨va, vs⟩ := v
  dsimp only
  refine Ok.bind (ptr_add_ok hg 4 (by omega)) (fun p hp => ?_)
  subst hp
  have e4 : (l1 - 4).toNat = l1.toNat - 4 := UInt64.toNat_sub_of_le _ _ (by
    rw [UInt64.le_iff_toNat_le]; simpa using h4)
  exact Ok.pure ⟨⟨rfl, _, rfl, by show o' + 4 + 4 * ((l1 - 4).toNat / 4) ≤ _; omega⟩,
    by show (l1 - 4).toNat < l1.toNat; omega⟩

/-- `adler32_copy_align` without copy on `len < 8` readable bytes. -/
theorem align_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data) (a s : UInt32)
    (o : Nat) (len : UInt64) (hl8 : len.toNat < 8) (hle : o + len.toNat ≤ data.size) :
    Ok h (adler32_copy_align a .null (.ref r o) len s 7 0) (fun _ => True) := by
  unfold adler32_copy_align
  rcases lt8 len hl8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := { decide := true }) only [↓reduceIte] <;>
  (try (refine Ok.bind (adler_do1_ok hg _ _ 0 (by decide) (by simp at hle ⊢; omega)) (fun v _ => ?_)
        obtain ⟨va, vs⟩ := v
        refine Ok.bind (ptr_add_ok hg 1 (by simp at hle; omega)) (fun p hp => ?_)
        subst hp)) <;>
  (try (refine Ok.bind (adler_do2_ok hg _ _ 0 (by decide) (by simp at hle ⊢; omega)) (fun v _ => ?_)
        obtain ⟨va, vs⟩ := v
        refine Ok.bind (ptr_add_ok hg 2 (by simp at hle; omega)) (fun p hp => ?_)
        subst hp)) <;>
  exact Ok.bind (align_loop hg _ _ rfl rfl (by simp at hle ⊢; omega)) (fun _ _ => Ok.pure trivial)

/-- The address of `.ref r o` is a multiple of 8. -/
def Al8 (h : Heap) (r : BRef) (o : Nat) : Prop := (h.baseAddr r + UInt64.ofNat o).toNat % 8 = 0

theorem al8_add {h : Heap} {r : BRef} {o c : Nat} (ha : Al8 h r o) (hc : c % 8 = 0) : Al8 h r (o + c) := by
  unfold Al8 at *
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at *
  omega

/-- `adler32_c` after the alignment prefix: the `NMAX` blocks and the tail. -/
def adlerBlocks (nmax : UInt64) (adler sum2 : UInt32) (buf : BPtr) (len : UInt64) : M UInt32 := do
  let s ← cwhile
    (fun (s : BlockState) => pure (s.len >= s.nmax, s))
    (fun (s : BlockState) => do
      let len := s.len - s.nmax
      let n := s.nmax
      let s ← cdoWhile
        (fun (s : BlockState) => do
          let chunk := MIN (ALIGN_DOWN s.n 8) ADLER32_SWAR_MAX_BYTES
          let (adler, sum2) ← adler32_swar s.adler .null s.buf chunk s.sum2 0
          let buf ← s.buf.add (Int.ofNat chunk.toNat)
          let n := s.n - chunk
          pure { s with adler, sum2, buf, n })
        (fun (s : BlockState) => pure (s.n >= 8, s))
        { s with len, n }
      pure { s with adler := s.adler % BASE, sum2 := s.sum2 % BASE, nmax := NMAX_ALIGNED8 })
    { adler, sum2, buf, len, n := 0, nmax }
  adler32_copy_tail s.adler .null s.buf s.len s.sum2 (if s.len != 0 then 1 else 0) (NMAX - 1).toUInt32.toInt32 0

theorem blocks_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data) (nmax : UInt64)
    (adler sum2 : UInt32) (o : Nat) (len : UInt64) (ha : Al8 h r o) (hle : o + len.toNat ≤ data.size)
    (hn8 : 8 ≤ nmax.toNat) (hnm : nmax.toNat % 8 = 0) :
    Ok h (adlerBlocks nmax adler sum2 (.ref r o) len) (fun _ => True) := by
  unfold adlerBlocks
  refine Ok.bind (cwhile_measure (fun s : BlockState => ∃ o', s.buf = .ref r o' ∧ Al8 h r o' ∧
    o' + s.len.toNat ≤ data.size ∧ 8 ≤ s.nmax.toNat ∧ s.nmax.toNat % 8 = 0) (fun s => s.len.toNat)
    (fun s : BlockState => ∃ o', s.buf = .ref r o' ∧ o' + s.len.toNat ≤ data.size) ?_
    ⟨o, rfl, ha, hle, hn8, hnm⟩ (fuel_lt _)) (fun s hs => ?_)
  · rintro ⟨a1, s1, b1, l1, n1, m1⟩ ⟨o', hb, ha', hl, hm8, hmm⟩
    dsimp only at hb hl hm8 hmm ⊢
    subst hb
    refine Ok.pure ⟨fun hc => ?_, fun _ => ⟨o', rfl, hl⟩⟩
    have hlm : m1.toNat ≤ l1.toNat := by simpa [UInt64.le_iff_toNat_le] using hc
    have esub : (l1 - m1).toNat = l1.toNat - m1.toNat :=
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hlm)
    dsimp only
    refine Ok.bind (cdoWhile_measure (fun t : BlockState => ∃ o', t.buf = .ref r o' ∧ Al8 h r o' ∧
      o' + t.n.toNat + t.len.toNat ≤ data.size ∧ 8 ≤ t.n.toNat ∧ t.n.toNat % 8 = 0 ∧ t.len = l1 - m1)
      (fun t => t.n.toNat) (fun t : BlockState => ∃ o', t.buf = .ref r o' ∧ Al8 h r o' ∧
        o' + t.len.toNat ≤ data.size ∧ t.len = l1 - m1) ?_ ⟨o', rfl, ha', by show o' + m1.toNat + (l1 - m1).toNat ≤ _; omega, hm8, hmm, rfl⟩
      (fuel_lt _)) (fun t ht => ?_)
    · rintro ⟨a2, s2, b2, l2, n2, m2⟩ ⟨o2, hb2, ha2, hl2, hn2, hnm2, hl2e⟩
      dsimp only at hb2 hl2 hn2 hnm2 hl2e ⊢
      subst hb2
      obtain ⟨c8, c184, cm, cle⟩ := min_chunk n2 hn2
      refine Ok.bind (swar_ok hg a2 s2 o2 _ ha2 c8 c184 cm (by omega)) (fun v _ => ?_)
      obtain ⟨va, vs⟩ := v
      dsimp only
      refine Ok.bind (ptr_add_ok hg _ (by omega)) (fun p hp => ?_)
      subst hp
      have esub2 : (n2 - MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat =
          n2.toNat - (MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat :=
        UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact cle)
      refine Ok.pure (Ok.pure ⟨fun hc2 => ⟨⟨_, rfl, al8_add ha2 cm, ?_, ?_, ?_, hl2e⟩, ?_⟩, fun hc2 => ⟨_, rfl, al8_add ha2 cm, ?_, hl2e⟩⟩)
      · show _ + (n2 - _).toNat + l2.toNat ≤ _; rw [esub2]; omega
      · have : 8 ≤ (n2 - MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat := by
          simpa [UInt64.le_iff_toNat_le] using hc2
        exact this
      · show (n2 - _).toNat % 8 = 0; rw [esub2]; omega
      · show (n2 - _).toNat < n2.toNat; rw [esub2]; omega
      · show _ + l2.toNat ≤ _; rw [esub2] at *; omega
    · obtain ⟨o3, hb3, ha3, hl3, hl3e⟩ := ht
      refine Ok.pure ⟨⟨o3, hb3, ha3, hl3, by show 8 ≤ NMAX_ALIGNED8.toNat; decide,
        by show NMAX_ALIGNED8.toNat % 8 = 0; decide⟩, ?_⟩
      · show t.len.toNat < l1.toNat; rw [hl3e, esub]; omega
  · obtain ⟨o3, hb3, hl3⟩ := hs
    rw [hb3]
    exact tail_ok hg _ _ o3 _ _ _ hl3

/-- **`adler32_c` on `len` readable bytes does not fault and changes nothing.** -/
theorem adler32_c_safe {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data) (a : UInt32)
    (o : Nat) (len : UInt64) (hle : o + len.toNat ≤ data.size) :
    Ok h (adler32_c a (.ref r o) len) (fun _ => True) := by
  unfold adler32_c
  by_cases h1 : (len == 1) = true
  · have : len = 1 := by simpa using h1
    subst this
    simp only [beq_self_eq_true, ↓reduceIte]
    exact tail_ok hg _ _ o 1 1 1 hle
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h16 : len < 16
  · simp only [h16, ↓reduceIte]
    exact tail_ok hg _ _ o len 1 15 hle
  have h16' : 16 ≤ len.toNat := by simpa [UInt64.lt_iff_toNat_lt] using h16
  simp only [h16, ↓reduceIte]
  have hA := (h.baseAddr r + UInt64.ofNat o).toNat_lt
  refine Ok.bind (P := fun v => v.toNat = (8 - (h.baseAddr r + UInt64.ofNat o).toNat % 8) % 8) ⟨_, rfl, ?_⟩
    (fun ad had => ?_)
  · show (((8 : UInt64) - ((h.baseAddr r + UInt64.ofNat o) &&& (8 - 1))) &&& (8 - 1)).toNat = _
    have e7 : (8 : UInt64) - 1 = 7 := rfl
    rw [e7, and7, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, and7]; show _ ≤ 8; omega), and7]
    rfl
  have had8 : ad.toNat < 8 := by rw [had]; omega
  have hal : Al8 h r (o + ad.toNat) := by
    unfold Al8; rw [had]
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at hA ⊢
    omega
  by_cases hz : (ad != 0) = true
  · simp only [hz, ↓reduceIte]
    refine Ok.bind (align_ok hg _ _ o ad had8 (by omega)) (fun v _ => ?_)
    obtain ⟨va, vs⟩ := v
    dsimp only
    refine Ok.bind (ptr_add_ok hg ad.toNat (by omega)) (fun p hp => ?_)
    subst hp
    have esub : (len - ad).toNat = len.toNat - ad.toNat :=
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)
    have hnm : (ALIGN_DOWN (NMAX_ALIGNED8 - ad) 8).toNat = (5552 - ad.toNat) / 8 * 8 := by
      rw [align_down8, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; show _ ≤ 5552; omega)]
      rfl
    exact blocks_ok hg _ va vs (o + ad.toNat) (len - ad) hal (by rw [esub]; omega) (by rw [hnm]; omega)
      (by rw [hnm]; omega)
  · have hz' : (ad != 0) = false := by simpa using hz
    have ha0 : ad.toNat = 0 := by have : ad = 0 := by simpa using hz
                                  rw [this]; rfl
    simp only [hz', Bool.false_eq_true, ↓reduceIte]
    rw [ha0] at hal
    exact blocks_ok hg _ _ _ o len hal hle (by decide) (by decide)

/-! ## The public entry points -/

open ZlibNgF.Spec.Safety in
theorem adler32_safety : Goal.adler32_safety := by
  intro h seed buf len bytes hb
  rcases hb with ⟨rfl, -⟩ | ⟨r, off, data, rfl, hg, hle, -⟩
  · exact ⟨_, rfl⟩
  · obtain ⟨v, e, -⟩ := adler32_c_safe hg seed.toUInt32 off len.toUInt64 (by simpa using hle)
    have e' : adler32_c seed.toUInt32 (.ref r off) len.toUInt64 h = .ok (v, h) := e
    exact ⟨v.toUInt64, by simp [C.run, ZlibNg.Adler32.adler32, bind_app, e']⟩

open ZlibNgF.Spec.Safety in
theorem adler32_z_safety : Goal.adler32_z_safety := by
  intro h seed buf len bytes hb
  rcases hb with ⟨rfl, -⟩ | ⟨r, off, data, rfl, hg, hle, -⟩
  · exact ⟨_, rfl⟩
  · obtain ⟨v, e, -⟩ := adler32_c_safe hg seed.toUInt32 off len hle
    have e' : adler32_c seed.toUInt32 (.ref r off) len h = .ok (v, h) := e
    exact ⟨v.toUInt64, by simp [C.run, ZlibNg.Adler32.adler32_z, bind_app, e']⟩

end ZlibNgF.Proof.Adler32Safe
