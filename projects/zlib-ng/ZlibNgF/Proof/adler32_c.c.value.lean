import ZlibNgF.Proof.«adler32_c.c.safety»

/-!
# The value of `adler32_c` (`ZlibNgF`)

`adler32_c` on `len` readable bytes returns the packed reduced RFC 1950 sums of the bytes, started from the two
16-bit halves of the seed reduced modulo `BASE` (`adler32_c_val`). The proof follows `adler32_c_safe`: the
alignment prefix, the `NMAX` blocks of SWAR chunks and the tail add the unreduced sums of their bytes modulo
`2^32` (`R32`). Between two reductions at most `NMAX = 5552` bytes are added to halves below `2^16`, so
(`rawSums_lt_u32`) the 32-bit accumulators hold the exact unreduced sums, and each `% BASE` sees them.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Adler32Value
open C ZlibNg.Zbuild ZlibNg.Adler32P ZlibNg.Adler32C
open ZlibNgF.Math.Adler32 hiding BASE NMAX
open ZlibNgF.Proof.Adler32Kernel ZlibNgF.Proof.Adler32Safe

/-! ## Chaining slices -/

theorem chainR {data : Array UInt8} {o q c o' : Nat} {p : Nat × Nat} {v w : UInt32 × UInt32}
    (h1 : R32 v (rawSums p (slice data o q)))
    (h2 : R32 w (rawSums (v.1.toNat, v.2.toNat) (slice data o' c))) (ho : o' = o + q) :
    R32 w (rawSums p (slice data o (q + c))) := by
  subst ho
  rw [slice_split]
  exact R32_chain h1 h2

theorem slice_zero (data : Array UInt8) (o : Nat) : slice data o 0 = [] := by
  simp [slice]

theorem do1_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    (a s : UInt32) {o : Nat} (hle : o + 1 ≤ data.size) :
    Ok h (adler_do1 a s (.ref r o) 0) (fun v => R32 v (rawSums (a.toNat, s.toNat) (slice data o 1))) :=
  Ok.mono (adler_do1_ok hg a s (o := o) 0 (by decide) (by simpa using hle)) (fun _ hv => by
    rwa [show (0 : Int).toNat = 0 from rfl, Nat.add_zero] at hv)

theorem do2_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    (a s : UInt32) {o : Nat} (hle : o + 2 ≤ data.size) :
    Ok h (adler_do2 a s (.ref r o) 0) (fun v => R32 v (rawSums (a.toNat, s.toNat) (slice data o 2))) :=
  Ok.mono (adler_do2_ok hg a s (o := o) 0 (by decide) (by simpa using hle)) (fun _ hv => by
    rwa [show (0 : Int).toNat = 0 from rfl, Nat.add_zero] at hv)

theorem do4_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    (a s : UInt32) {o : Nat} (hle : o + 4 ≤ data.size) :
    Ok h (adler_do4 a s (.ref r o) 0) (fun v => R32 v (rawSums (a.toNat, s.toNat) (slice data o 4))) :=
  Ok.mono (adler_do4_ok hg a s (o := o) 0 (by decide) (by simpa using hle)) (fun _ hv => by
    rwa [show (0 : Int).toNat = 0 from rfl, Nat.add_zero] at hv)

/-! ## `adler32_copy_tail` -/

/-- The value of `adler32_copy_tail`: the accumulators `(x, y)` after the bytes `xs`, reduced if `REBASE`. -/
def TailPost (a s : UInt32) (xs : List UInt8) (REBASE : Int32) (res : UInt32) : Prop :=
  ∃ x y : UInt32, R32 (x, y) (rawSums (a.toNat, s.toNat) xs) ∧
    res = (if (REBASE != 0) = true then x % ZlibNg.Adler32P.BASE else x) |||
      ((if (REBASE != 0) = true then y % ZlibNg.Adler32P.BASE else y) <<< 16)

/-- `adler32_copy_tail` without copy on `len` readable bytes. -/
theorem tail_val {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data) (a s : UInt32)
    (o : Nat) (len : UInt64) (REBASE MAX : Int32) (hle : o + len.toNat ≤ data.size) :
    Ok h (adler32_copy_tail a .null (.ref r o) len s REBASE MAX 0)
      (TailPost a s (slice data o len.toNat) REBASE) := by
  unfold adler32_copy_tail
  simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have fin : ∀ (x y : UInt32) (q : Nat), R32 (x, y) (rawSums (a.toNat, s.toNat) (slice data o q)) →
      q = len.toNat →
      Ok h ((have __do_jp := fun (_ : Unit) (adler sum2 : UInt32) =>
        (pure (adler ||| sum2 <<< 16) : M UInt32)
      if (REBASE != 0) = true then __do_jp () (x % BASE) (y % BASE) else __do_jp () x y))
      (TailPost a s (slice data o len.toNat) REBASE) := by
    intro x y q hR hq
    subst hq
    dsimp only
    split <;> rename_i hc <;> exact Ok.pure ⟨x, y, hR, by simp [hc]⟩
  let I : TailState → Prop := fun st => st.dst = .null ∧ ∃ q, st.buf = .ref r (o + q) ∧
    q + st.len.toNat = len.toNat ∧ R32 (st.adler, st.sum2) (rawSums (a.toNat, s.toNat) (slice data o q))
  have hI0 : I { adler := a, sum2 := s, dst := .null, buf := .ref r o, len := len } :=
    ⟨rfl, 0, rfl, by simp, by rw [slice_zero]; exact R32_nil a s⟩
  split
  · refine Ok.bind (cwhile_measure I (fun st => st.len.toNat) I ?_ hI0 (fuel_lt _)) (fun s1 hs1 => ?_)
    · rintro ⟨a1, s1, d1, b1, l1⟩ ⟨hd, q, hb, hl, hR⟩
      dsimp only at hd hb hl hR ⊢
      subst hd hb
      split
      · rename_i h8
        have h8' : 8 ≤ l1.toNat := h8
        refine Ok.bind (P := fun v => v = h.baseAddr r + UInt64.ofNat (o + q)) ⟨_, rfl, rfl⟩
          (fun addr haddr => Ok.pure ⟨fun hc => ?_, fun _ => ⟨rfl, q, rfl, hl, hR⟩⟩)
        subst haddr
        have hal : (h.baseAddr r + UInt64.ofNat (o + q)).toNat % 8 = 0 := by
          have : ((h.baseAddr r + UInt64.ofNat (o + q)) &&& 7) = 0 := by simpa using hc
          rw [← and7, this]; rfl
        obtain ⟨c8, c184, cm, cle⟩ := min_chunk l1 h8'
        dsimp only
        refine Ok.bind (swar_ok hg a1 s1 (o + q) _ hal c8 c184 cm (by omega)) (fun v hv => ?_)
        obtain ⟨va, vs⟩ := v
        dsimp only
        refine Ok.bind (ptr_add_ok hg _ (by omega)) (fun p hp => ?_)
        subst hp
        have esub : (l1 - MIN (ALIGN_DOWN l1 8) ADLER32_SWAR_MAX_BYTES).toNat =
            l1.toNat - (MIN (ALIGN_DOWN l1 8) ADLER32_SWAR_MAX_BYTES).toNat :=
          UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)
        refine Ok.pure ⟨⟨rfl, q + (MIN (ALIGN_DOWN l1 8) ADLER32_SWAR_MAX_BYTES).toNat,
          by show Ptr.ref r (o + q + _) = _; rw [Nat.add_assoc], ?_, chainR hR hv rfl⟩, ?_⟩
        · show _ + (l1 - _).toNat = _
          rw [esub]; omega
        · show (l1 - _).toNat < l1.toNat
          rw [esub]; omega
      · exact Ok.pure ⟨fun hc => absurd hc (by simp), fun _ => ⟨rfl, q, rfl, hl, hR⟩⟩
    · refine Ok.bind (cwhile_measure I (fun st => st.len.toNat) (fun st => I st ∧ st.len.toNat < 4) ?_ hs1
        (fuel_lt _)) (fun s2 hs2 => ?_)
      · rintro ⟨a1, s1, d1, b1, l1⟩ ⟨hd, q, hb, hl, hR⟩
        dsimp only at hd hb hl hR ⊢
        subst hd hb
        refine Ok.pure ⟨fun hc => ?_, fun hc => ⟨⟨rfl, q, rfl, hl, hR⟩, ?_⟩⟩
        · have h4 : 4 ≤ l1.toNat := by simpa [UInt64.le_iff_toNat_le] using hc
          dsimp only
          refine Ok.bind (do4_ok hg a1 s1 (o := o + q) (by omega)) (fun v hv => ?_)
          obtain ⟨va, vs⟩ := v
          dsimp only
          refine Ok.bind (ptr_add_ok hg 4 (by omega)) (fun p hp => ?_)
          subst hp
          have e4 : (l1 - 4).toNat = l1.toNat - 4 := UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le]; simpa using h4)
          exact Ok.pure ⟨⟨rfl, q + 4, by show Ptr.ref r (o + q + 4) = _; rw [Nat.add_assoc],
            by show _ + (l1 - 4).toNat = _; omega, chainR hR hv rfl⟩,
            by show (l1 - 4).toNat < l1.toNat; omega⟩
        · simpa [UInt64.le_iff_toNat_le] using hc
      · obtain ⟨⟨hd, q, hb, hl, hR⟩, h4⟩ := hs2
        obtain ⟨a2, s2', d2, b2, l2⟩ := s2
        dsimp only at hd hb hl hR h4 ⊢
        subst hd hb
        rcases lt4 l2 h4 with rfl | rfl | rfl | rfl
        · simp only [show ((0 : UInt64) &&& 2 != 0) = false from rfl, show ((0 : UInt64) &&& 1 != 0) = false from rfl,
            Bool.false_eq_true, ↓reduceIte]
          exact fin a2 s2' q hR (by simpa using hl)
        · simp only [show ((1 : UInt64) &&& 2 != 0) = false from rfl, show ((1 : UInt64) &&& 1 != 0) = true from rfl,
            Bool.false_eq_true, ↓reduceIte]
          have hl' : q + 1 = len.toNat := by simpa using hl
          refine Ok.bind (do1_ok hg a2 s2' (o := o + q) (by omega)) (fun v hv => ?_)
          obtain ⟨va, vs⟩ := v
          exact fin va vs (q + 1) (chainR hR hv rfl) hl'
        · simp only [show ((2 : UInt64) &&& 2 != 0) = true from rfl, show ((2 : UInt64) &&& 1 != 0) = false from rfl,
            Bool.false_eq_true, ↓reduceIte]
          have hl' : q + 2 = len.toNat := by simpa using hl
          refine Ok.bind (do2_ok hg a2 s2' (o := o + q) (by omega)) (fun v hv => ?_)
          obtain ⟨va, vs⟩ := v
          refine Ok.bind (ptr_add_ok hg 2 (by omega)) (fun p hp => ?_)
          exact fin va vs (q + 2) (chainR hR hv rfl) hl'
        · simp only [show ((3 : UInt64) &&& 2 != 0) = true from rfl, show ((3 : UInt64) &&& 1 != 0) = true from rfl,
            ↓reduceIte]
          have hl' : q + 3 = len.toNat := by simpa using hl
          refine Ok.bind (do2_ok hg a2 s2' (o := o + q) (by omega)) (fun v hv => ?_)
          obtain ⟨va, vs⟩ := v
          refine Ok.bind (ptr_add_ok hg 2 (by omega)) (fun p hp => ?_)
          subst hp
          refine Ok.bind (do1_ok hg va vs (o := o + q + 2) (by omega)) (fun w hw => ?_)
          obtain ⟨wa, ws⟩ := w
          exact fin wa ws (q + 2 + 1) (chainR (chainR hR hv rfl) hw (by omega)) (by omega)
  · rename_i hz
    have h0 : len.toNat = 0 := by
      have : len = 0 := by simpa using hz
      rw [this]; rfl
    exact fin a s 0 (by rw [slice_zero]; exact R32_nil a s) h0.symm

/-! ## `adler32_copy_align` -/

/-- `adler32_copy_align`'s loop over the whole groups of four bytes adds the sums of `4 (len / 4)` bytes. -/
theorem align_loop_val {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    (p : Nat × Nat) (o T q0 : Nat) (st : Do4State) (hb : st.buf = .ref r (o + q0)) (hd : st.dst = .null)
    (hT : q0 + 4 * (st.len.toNat / 4) = T) (hle : o + T ≤ data.size)
    (hR : R32 (st.adler, st.sum2) (rawSums p (slice data o q0))) :
    Ok h (cwhile (fun (s : Do4State) => pure (decide (s.len ≥ 4), s))
      (fun (s : Do4State) => do
        let mut dst := s.dst
        if (0 : Int32) != 0 then
          Ptr.memcpy dst s.buf 4
          dst ← dst.add 4
        let len := s.len - 4
        let (adler, sum2) ← adler_do4 s.adler s.sum2 s.buf 0
        let buf ← s.buf.add 4
        pure { adler, sum2, dst, buf, len }) st)
      (fun st' => R32 (st'.adler, st'.sum2) (rawSums p (slice data o T))) := by
  let I : Do4State → Prop := fun st => st.dst = .null ∧ ∃ q, st.buf = .ref r (o + q) ∧
    q + 4 * (st.len.toNat / 4) = T ∧ R32 (st.adler, st.sum2) (rawSums p (slice data o q))
  refine cwhile_measure I (fun st => st.len.toNat) _ ?_ ⟨hd, q0, hb, hT, hR⟩ (fuel_lt _)
  rintro ⟨a1, s1, d1, b1, l1⟩ ⟨hd, q, hb, hl, hR⟩
  dsimp only at hd hb hl hR ⊢
  subst hd hb
  refine Ok.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · have h4 : 4 ≤ l1.toNat := by simpa [UInt64.le_iff_toNat_le] using hc
    simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine Ok.bind (do4_ok hg a1 s1 (o := o + q) (by omega)) (fun v hv => ?_)
    obtain ⟨va, vs⟩ := v
    dsimp only
    refine Ok.bind (ptr_add_ok hg 4 (by omega)) (fun p hp => ?_)
    subst hp
    have e4 : (l1 - 4).toNat = l1.toNat - 4 := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; simpa using h4)
    exact Ok.pure ⟨⟨rfl, q + 4, by show Ptr.ref r (o + q + 4) = _; rw [Nat.add_assoc],
      by show _ + 4 * ((l1 - 4).toNat / 4) = _; omega, chainR hR hv rfl⟩,
      by show (l1 - 4).toNat < l1.toNat; omega⟩
  · have h4 : l1.toNat < 4 := by simpa [UInt64.le_iff_toNat_le] using hc
    have hq : q = T := by omega
    subst hq
    exact hR

/-- `adler32_copy_align` without copy on `len < 8` readable bytes adds the sums of the `len` bytes. -/
theorem align_val {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data) (a s : UInt32)
    (o : Nat) (len : UInt64) (hl8 : len.toNat < 8) (hle : o + len.toNat ≤ data.size) :
    Ok h (adler32_copy_align a .null (.ref r o) len s 7 0)
      (fun v => R32 v (rawSums (a.toNat, s.toNat) (slice data o len.toNat))) := by
  have h0 : R32 (a, s) (rawSums (a.toNat, s.toNat) (slice data o 0)) := by rw [slice_zero]; exact R32_nil a s
  unfold adler32_copy_align
  rcases lt8 len hl8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := { decide := true }) only [↓reduceIte]
  · exact Ok.bind (align_loop_val hg _ o (UInt64.toNat 0) (0) _ (rfl) rfl (by simp) (by simpa using hle) h0)
      (fun _ hst => Ok.pure hst)
  · refine Ok.bind (do1_ok hg a s (o := o) (by simp at hle; omega)) (fun v hv => ?_)
    obtain ⟨va, vs⟩ := v
    refine Ok.bind (ptr_add_ok hg 1 (by simp at hle; omega)) (fun p hp => ?_)
    subst hp
    exact Ok.bind (align_loop_val hg _ o (UInt64.toNat 1) (1) _ (rfl) rfl (by simp) (by simpa using hle) hv)
      (fun _ hst => Ok.pure hst)
  · refine Ok.bind (do2_ok hg a s (o := o) (by simp at hle; omega)) (fun w hw => ?_)
    obtain ⟨wa, ws⟩ := w
    refine Ok.bind (ptr_add_ok hg 2 (by simp at hle; omega)) (fun p hp => ?_)
    subst hp
    exact Ok.bind (align_loop_val hg _ o (UInt64.toNat 2) (2) _ (rfl) rfl (by simp) (by simpa using hle) hw)
      (fun _ hst => Ok.pure hst)
  · refine Ok.bind (do1_ok hg a s (o := o) (by simp at hle; omega)) (fun v hv => ?_)
    obtain ⟨va, vs⟩ := v
    refine Ok.bind (ptr_add_ok hg 1 (by simp at hle; omega)) (fun p hp => ?_)
    subst hp
    refine Ok.bind (do2_ok hg va vs (o := o + 1) (by simp at hle; omega)) (fun w hw => ?_)
    obtain ⟨wa, ws⟩ := w
    refine Ok.bind (ptr_add_ok hg 2 (by simp at hle; omega)) (fun p hp => ?_)
    subst hp
    exact Ok.bind (align_loop_val hg _ o (UInt64.toNat 3) (1 + 2) _ (by simp [Nat.add_assoc]) rfl (by simp) (by simpa using hle) (chainR hv hw rfl))
      (fun _ hst => Ok.pure hst)
  · exact Ok.bind (align_loop_val hg _ o (UInt64.toNat 4) (0) _ (rfl) rfl (by simp) (by simpa using hle) h0)
      (fun _ hst => Ok.pure hst)
  · refine Ok.bind (do1_ok hg a s (o := o) (by simp at hle; omega)) (fun v hv => ?_)
    obtain ⟨va, vs⟩ := v
    refine Ok.bind (ptr_add_ok hg 1 (by simp at hle; omega)) (fun p hp => ?_)
    subst hp
    exact Ok.bind (align_loop_val hg _ o (UInt64.toNat 5) (1) _ (rfl) rfl (by simp) (by simpa using hle) hv)
      (fun _ hst => Ok.pure hst)
  · refine Ok.bind (do2_ok hg a s (o := o) (by simp at hle; omega)) (fun w hw => ?_)
    obtain ⟨wa, ws⟩ := w
    refine Ok.bind (ptr_add_ok hg 2 (by simp at hle; omega)) (fun p hp => ?_)
    subst hp
    exact Ok.bind (align_loop_val hg _ o (UInt64.toNat 6) (2) _ (rfl) rfl (by simp) (by simpa using hle) hw)
      (fun _ hst => Ok.pure hst)
  · refine Ok.bind (do1_ok hg a s (o := o) (by simp at hle; omega)) (fun v hv => ?_)
    obtain ⟨va, vs⟩ := v
    refine Ok.bind (ptr_add_ok hg 1 (by simp at hle; omega)) (fun p hp => ?_)
    subst hp
    refine Ok.bind (do2_ok hg va vs (o := o + 1) (by simp at hle; omega)) (fun w hw => ?_)
    obtain ⟨wa, ws⟩ := w
    refine Ok.bind (ptr_add_ok hg 2 (by simp at hle; omega)) (fun p hp => ?_)
    subst hp
    exact Ok.bind (align_loop_val hg _ o (UInt64.toNat 7) (1 + 2) _ (by simp [Nat.add_assoc]) rfl (by simp) (by simpa using hle) (chainR hv hw rfl))
      (fun _ hst => Ok.pure hst)

/-! ## Exact accumulators between two reductions -/

/-- After the first `q` bytes from `o0`, the accumulators `v` are the exact unreduced sums of the last `m` of
them from halves `c1, c2 < 2^16` that reduce to the reduced sums of the first `q - m` bytes from `S0`, and `k`
more bytes may be added before the next reduction. -/
def Acc (data : Array UInt8) (o0 : Nat) (S0 : Nat × Nat) (q k : Nat) (v : UInt32 × UInt32) : Prop :=
  ∃ c1 c2 m, m ≤ q ∧ c1 ≤ 65535 ∧ c2 ≤ 65535 ∧ m + k ≤ 5552 ∧
    (c1 % 65521, c2 % 65521) = sums S0 (slice data o0 (q - m)) ∧
    v.1.toNat = (rawSums (c1, c2) (slice data (o0 + (q - m)) m)).1 ∧
    v.2.toNat = (rawSums (c1, c2) (slice data (o0 + (q - m)) m)).2

theorem acc_init (data : Array UInt8) (o0 : Nat) (x y : UInt32) (hx : x.toNat ≤ 65535) (hy : y.toNat ≤ 65535) :
    Acc data o0 (x.toNat % 65521, y.toNat % 65521) 0 5552 (x, y) :=
  ⟨x.toNat, y.toNat, 0, Nat.le_refl _, hx, hy, by omega, by rw [Nat.sub_zero, slice_zero]; rfl,
    by rw [slice_zero]; rfl, by rw [slice_zero]; rfl⟩

theorem acc_weaken {data : Array UInt8} {o0 : Nat} {S0 : Nat × Nat} {q k k' : Nat} {v : UInt32 × UInt32}
    (hA : Acc data o0 S0 q k v) (hk : k' ≤ k) : Acc data o0 S0 q k' v := by
  obtain ⟨c1, c2, m, hm, h1, h2, hmk, hS, e1, e2⟩ := hA
  exact ⟨c1, c2, m, hm, h1, h2, by omega, hS, e1, e2⟩

theorem acc_step {data : Array UInt8} {o0 : Nat} {S0 : Nat × Nat} {q n k : Nat} {v w : UInt32 × UInt32}
    (hA : Acc data o0 S0 q (n + k) v) (hR : R32 w (rawSums (v.1.toNat, v.2.toNat) (slice data (o0 + q) n)))
    (hle : o0 + q + n ≤ data.size) : Acc data o0 S0 (q + n) k w := by
  obtain ⟨c1, c2, m, hm, h1, h2, hmk, hS, e1, e2⟩ := hA
  have hv : (v.1.toNat, v.2.toNat) = rawSums (c1, c2) (slice data (o0 + (q - m)) m) := Prod.ext e1 e2
  have hsp : slice data (o0 + (q - m)) (m + n) = slice data (o0 + (q - m)) m ++ slice data (o0 + q) n := by
    rw [slice_split]; congr 2; omega
  rw [hv, ← rawSums_append, ← hsp] at hR
  have hlen : (slice data (o0 + (q - m)) (m + n)).length = m + n := slice_len (by omega)
  have hb := rawSums_lt_u32 (c1, c2) (slice data (o0 + (q - m)) (m + n)) h1 h2 (by show _ ≤ 5552; omega)
  obtain ⟨r1, r2⟩ := hR
  refine ⟨c1, c2, m + n, by omega, h1, h2, by omega, ?_, ?_, ?_⟩
  · rw [show q + n - (m + n) = q - m by omega]; exact hS
  · rw [show q + n - (m + n) = q - m by omega, r1, Nat.mod_eq_of_lt hb.1]
  · rw [show q + n - (m + n) = q - m by omega, r2, Nat.mod_eq_of_lt hb.2]

theorem acc_mod {data : Array UInt8} {o0 : Nat} {S0 : Nat × Nat} {q k : Nat} {v : UInt32 × UInt32}
    (hA : Acc data o0 S0 q k v) :
    (v.1.toNat % 65521, v.2.toNat % 65521) = sums S0 (slice data o0 q) := by
  obtain ⟨c1, c2, m, hm, h1, h2, hmk, hS, e1, e2⟩ := hA
  have hmod := rawSums_mod (c1, c2) (slice data (o0 + (q - m)) m)
  have hsp : slice data o0 q = slice data o0 (q - m) ++ slice data (o0 + (q - m)) m := by
    rw [← slice_split]; congr 1; omega
  rw [e1, e2, hsp, sums_append, ← hS]
  exact hmod

theorem acc_reduce {data : Array UInt8} {o0 : Nat} {S0 : Nat × Nat} {q k : Nat} {v : UInt32 × UInt32}
    (hA : Acc data o0 S0 q k v) (k' : Nat) (hk' : k' ≤ 5552) :
    Acc data o0 S0 q k' (v.1 % ZlibNg.Adler32P.BASE, v.2 % ZlibNg.Adler32P.BASE) := by
  have hm := acc_mod hA
  have hB : (ZlibNg.Adler32P.BASE).toNat = 65521 := rfl
  have l1 : v.1.toNat % 65521 < 65521 := Nat.mod_lt _ (by decide)
  have l2 : v.2.toNat % 65521 < 65521 := Nat.mod_lt _ (by decide)
  refine ⟨v.1.toNat % 65521, v.2.toNat % 65521, 0, Nat.zero_le _, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rw [Nat.mod_mod, Nat.mod_mod, Nat.sub_zero]; exact hm
  · rw [slice_zero]; simp only [rawSums_nil]; rw [UInt32.toNat_mod, hB]
  · rw [slice_zero]; simp only [rawSums_nil]; rw [UInt32.toNat_mod, hB]

/-! ## The packed result -/

theorem or_shift32 (x y : UInt32) (hx : x.toNat < 65536) (hy : y.toNat < 65536) :
    (x ||| (y <<< 16)).toNat = x.toNat + 65536 * y.toNat := by
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft]
  have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
  rw [h16]
  have hs : (y.toNat <<< 16) % (2 ^ 32) = y.toNat * 65536 := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hs, Nat.or_comm,
    show y.toNat * 65536 = y.toNat <<< 16 by rw [Nat.shiftLeft_eq],
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

/-- The packed Adler-32 value of the reduced sums of `xs` from `S0`. -/
def AdlerVal (S0 : Nat × Nat) (xs : List UInt8) (res : UInt32) : Prop :=
  res.toNat = (sums S0 xs).1 + 65536 * (sums S0 xs).2

/-- The final `adler32_copy_tail` of `adler32_c`: the remaining `len` bytes, then the packed result. Without
`REBASE` the tail is empty and the accumulators are already reduced. -/
theorem tail_final {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o0 : Nat} {S0 : Nat × Nat} (q : Nat) (a s : UInt32) (len : UInt64) (REBASE MAX : Int32)
    (hA : Acc data o0 S0 q len.toNat (a, s)) (hle : o0 + q + len.toNat ≤ data.size)
    (hre : (REBASE != 0) = false → len.toNat = 0 ∧ a.toNat < 65521 ∧ s.toNat < 65521) :
    Ok h (adler32_copy_tail a .null (.ref r (o0 + q)) len s REBASE MAX 0)
      (AdlerVal S0 (slice data o0 (q + len.toNat))) := by
  refine Ok.mono (tail_val hg a s (o0 + q) len REBASE MAX hle) (fun res hres => ?_)
  obtain ⟨x, y, hR, hres⟩ := hres
  have hA' := acc_step (k := 0) (by simpa using hA) hR hle
  have hm := acc_mod hA'
  have hB : (ZlibNg.Adler32P.BASE).toNat = 65521 := rfl
  unfold AdlerVal
  rw [← hm, hres]
  cases hc : (REBASE != 0)
  · obtain ⟨h0, ha, hs⟩ := hre hc
    have hR0 : R32 (x, y) (rawSums (a.toNat, s.toNat) []) := by
      rw [h0, slice_zero] at hR; exact hR
    obtain ⟨ex, ey⟩ := hR0
    simp only [rawSums_nil] at ex ey
    rw [Nat.mod_eq_of_lt a.toNat_lt] at ex
    rw [Nat.mod_eq_of_lt s.toNat_lt] at ey
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [or_shift32 x y (by omega) (by omega), Nat.mod_eq_of_lt (by omega : x.toNat < 65521),
      Nat.mod_eq_of_lt (by omega : y.toNat < 65521)]
  · simp only [↓reduceIte]
    have l1 : x.toNat % 65521 < 65521 := Nat.mod_lt _ (by decide)
    have l2 : y.toNat % 65521 < 65521 := Nat.mod_lt _ (by decide)
    rw [or_shift32 _ _ (by rw [UInt32.toNat_mod, hB]; omega) (by rw [UInt32.toNat_mod, hB]; omega),
      UInt32.toNat_mod, UInt32.toNat_mod, hB]

/-! ## The `NMAX` blocks -/

theorem blocks_val {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o0 : Nat} {S0 : Nat × Nat} (L : Nat) (nmax : UInt64) (adler sum2 : UInt32) (q : Nat) (len : UInt64)
    (ha : Al8 h r (o0 + q)) (hL : q + len.toNat = L) (hle : o0 + L ≤ data.size) (hlen0 : len.toNat ≠ 0)
    (hn8 : 8 ≤ nmax.toNat) (hnm : nmax.toNat % 8 = 0) (hA : Acc data o0 S0 q nmax.toNat (adler, sum2)) :
    Ok h (adlerBlocks nmax adler sum2 (.ref r (o0 + q)) len) (AdlerVal S0 (slice data o0 L)) := by
  unfold adlerBlocks
  refine Ok.bind (cwhile_measure (fun s : BlockState => ∃ q, s.buf = .ref r (o0 + q) ∧ Al8 h r (o0 + q) ∧
    q + s.len.toNat = L ∧ 8 ≤ s.nmax.toNat ∧ s.nmax.toNat % 8 = 0 ∧ Acc data o0 S0 q s.nmax.toNat (s.adler, s.sum2) ∧
    (s.len.toNat = 0 → s.adler.toNat < 65521 ∧ s.sum2.toNat < 65521)) (fun s => s.len.toNat)
    (fun s : BlockState => ∃ q, s.buf = .ref r (o0 + q) ∧ q + s.len.toNat = L ∧
      Acc data o0 S0 q s.len.toNat (s.adler, s.sum2) ∧
      (s.len.toNat = 0 → s.adler.toNat < 65521 ∧ s.sum2.toNat < 65521)) ?_
    ⟨q, rfl, ha, hL, hn8, hnm, hA, fun h0 => absurd h0 hlen0⟩ (fuel_lt _)) (fun s hs => ?_)
  · rintro ⟨a1, s1, b1, l1, n1, m1⟩ ⟨q1, hb, ha', hl, hm8, hmm, hA1, hz⟩
    dsimp only at hb hl hm8 hmm hA1 hz ⊢
    subst hb
    refine Ok.pure ⟨fun hc => ?_, fun hc => ⟨q1, rfl, hl, acc_weaken hA1 ?_, hz⟩⟩
    rotate_left
    · have : ¬ (m1.toNat ≤ l1.toNat) := by simpa [UInt64.le_iff_toNat_le] using hc
      show l1.toNat ≤ m1.toNat
      omega
    have hlm : m1.toNat ≤ l1.toNat := by simpa [UInt64.le_iff_toNat_le] using hc
    have esub : (l1 - m1).toNat = l1.toNat - m1.toNat :=
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hlm)
    dsimp only
    refine Ok.bind (cdoWhile_measure (fun t : BlockState => ∃ q, t.buf = .ref r (o0 + q) ∧ Al8 h r (o0 + q) ∧
      q + t.n.toNat + t.len.toNat = L ∧ 8 ≤ t.n.toNat ∧ t.n.toNat % 8 = 0 ∧ t.len = l1 - m1 ∧
      Acc data o0 S0 q t.n.toNat (t.adler, t.sum2))
      (fun t => t.n.toNat) (fun t : BlockState => ∃ q, t.buf = .ref r (o0 + q) ∧ Al8 h r (o0 + q) ∧
        q + t.len.toNat = L ∧ t.len = l1 - m1 ∧ Acc data o0 S0 q 0 (t.adler, t.sum2)) ?_
      ⟨q1, rfl, ha', by show q1 + m1.toNat + (l1 - m1).toNat = L; omega, hm8, hmm, rfl, hA1⟩
      (fuel_lt _)) (fun t ht => ?_)
    · rintro ⟨a2, s2, b2, l2, n2, m2⟩ ⟨q2, hb2, ha2, hl2, hn2, hnm2, hl2e, hA2⟩
      dsimp only at hb2 hl2 hn2 hnm2 hl2e hA2 ⊢
      subst hb2
      obtain ⟨c8, c184, cm, cle⟩ := min_chunk n2 hn2
      refine Ok.bind (swar_ok hg a2 s2 (o0 + q2) _ ha2 c8 c184 cm (by omega)) (fun v hv => ?_)
      obtain ⟨va, vs⟩ := v
      dsimp only
      refine Ok.bind (ptr_add_ok hg _ (by omega)) (fun p hp => ?_)
      subst hp
      have esub2 : (n2 - MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat =
          n2.toNat - (MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat :=
        UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact cle)
      have hA3 := acc_step (n := (MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat)
        (k := (n2 - MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat)
        (by rw [esub2, Nat.add_sub_cancel' cle]; exact hA2) hv (by omega)
      have hal3 : Al8 h r (o0 + (q2 + (MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat)) := by
        rw [← Nat.add_assoc]; exact al8_add ha2 cm
      have hbuf3 : Ptr.ref r (o0 + q2 + (MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat) =
          Ptr.ref r (o0 + (q2 + (MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat)) := by
        rw [Nat.add_assoc]
      refine Ok.pure (Ok.pure ⟨fun hc2 => ⟨⟨_, hbuf3, hal3, ?_, ?_, ?_, hl2e, hA3⟩, ?_⟩,
        fun hc2 => ⟨_, hbuf3, hal3, ?_, hl2e, ?_⟩⟩)
      · show _ + (n2 - _).toNat + l2.toNat = L; rw [esub2]; omega
      · have : 8 ≤ (n2 - MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat := by
          simpa [UInt64.le_iff_toNat_le] using hc2
        exact this
      · show (n2 - _).toNat % 8 = 0; rw [esub2]; omega
      · show (n2 - _).toNat < n2.toNat; rw [esub2]; omega
      · have : ¬ (8 ≤ (n2 - MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat) := by
          simpa [UInt64.le_iff_toNat_le] using hc2
        show _ + l2.toNat = L
        rw [esub2] at this; omega
      · have : ¬ (8 ≤ (n2 - MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat) := by
          simpa [UInt64.le_iff_toNat_le] using hc2
        have h0 : (n2 - MIN (ALIGN_DOWN n2 8) ADLER32_SWAR_MAX_BYTES).toNat = 0 := by
          rw [esub2] at this ⊢; omega
        rw [h0] at hA3; exact hA3
    · obtain ⟨q3, hb3, ha3, hl3, hl3e, hA3⟩ := ht
      refine Ok.pure ⟨⟨q3, hb3, ha3, hl3, by show 8 ≤ NMAX_ALIGNED8.toNat; decide,
        by show NMAX_ALIGNED8.toNat % 8 = 0; decide, acc_reduce hA3 _ (by show NMAX_ALIGNED8.toNat ≤ 5552; decide), fun _ => ?_⟩, ?_⟩
      · have hB : (ZlibNg.Adler32P.BASE).toNat = 65521 := rfl
        show (t.adler % ZlibNg.Adler32P.BASE).toNat < 65521 ∧ (t.sum2 % ZlibNg.Adler32P.BASE).toNat < 65521
        rw [UInt32.toNat_mod, UInt32.toNat_mod, hB]
        exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
      · show t.len.toNat < l1.toNat; rw [hl3e, esub]; omega
  · obtain ⟨q3, hb3, hl3, hA3, hz3⟩ := hs
    rw [hb3, ← hl3]
    refine tail_final hg q3 _ _ _ _ _ hA3 (by omega) (fun hc => ?_)
    by_cases h0 : s.len.toNat = 0
    · exact ⟨h0, hz3 h0⟩
    · exfalso
      have : (s.len != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; intro he; rw [he] at h0; exact h0 rfl
      simp [this] at hc

/-! ## `adler32_c` -/

/-- **`adler32_c` on `len` readable bytes returns the packed reduced RFC 1950 sums of the bytes, started from the
two 16-bit halves of the seed reduced modulo `BASE`, and changes nothing.** -/
theorem adler32_c_val {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data) (a : UInt32)
    (o : Nat) (len : UInt64) (hle : o + len.toNat ≤ data.size) :
    Ok h (adler32_c a (.ref r o) len)
      (AdlerVal ((a &&& 0xffff).toNat % 65521, ((a >>> 16) &&& 0xffff).toNat % 65521) (slice data o len.toNat)) := by
  have hx : (a &&& 0xffff).toNat ≤ 65535 := by
    rw [UInt32.toNat_and]; exact Nat.le_trans Nat.and_le_right (by decide)
  have hy : ((a >>> 16) &&& 0xffff).toNat ≤ 65535 := by
    rw [UInt32.toNat_and]; exact Nat.le_trans Nat.and_le_right (by decide)
  have A0 := acc_init data o (a &&& 0xffff) ((a >>> 16) &&& 0xffff) hx hy
  unfold adler32_c
  by_cases h1 : (len == 1) = true
  · have : len = 1 := by simpa using h1
    subst this
    simp only [beq_self_eq_true, ↓reduceIte]
    exact Ok.mono (tail_final hg (o0 := o) 0 _ _ 1 1 1 (acc_weaken A0 (by decide)) (by simpa using hle)
      (fun hc => absurd hc (by decide))) (fun res hr => by rwa [Nat.zero_add] at hr)
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h16 : len < 16
  · simp only [h16, ↓reduceIte]
    have hl16 : len.toNat < 16 := by simpa [UInt64.lt_iff_toNat_lt] using h16
    exact Ok.mono (tail_final hg (o0 := o) 0 _ _ len 1 15 (acc_weaken A0 (by omega)) (by simpa using hle)
      (fun hc => absurd hc (by decide))) (fun res hr => by rwa [Nat.zero_add] at hr)
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
    refine Ok.bind (align_val hg _ _ o ad had8 (by omega)) (fun v hv => ?_)
    obtain ⟨va, vs⟩ := v
    dsimp only
    refine Ok.bind (ptr_add_ok hg ad.toNat (by omega)) (fun p hp => ?_)
    subst hp
    have esub : (len - ad).toNat = len.toNat - ad.toNat :=
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)
    have hnm : (ALIGN_DOWN (NMAX_ALIGNED8 - ad) 8).toNat = (5552 - ad.toNat) / 8 * 8 := by
      rw [align_down8, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; show _ ≤ 5552; omega)]
      rfl
    have hA1 := acc_step (q := 0) (n := ad.toNat) (k := 5552 - ad.toNat)
      (by rw [show ad.toNat + (5552 - ad.toNat) = 5552 by omega]; exact A0) hv (by omega)
    rw [Nat.zero_add] at hA1
    exact blocks_val hg (o0 := o) len.toNat _ va vs ad.toNat (len - ad) hal (by rw [esub]; omega) hle
      (by rw [esub]; omega) (by rw [hnm]; omega) (by rw [hnm]; omega) (acc_weaken hA1 (by rw [hnm]; omega))
  · have hz' : (ad != 0) = false := by simpa using hz
    have ha0 : ad.toNat = 0 := by have : ad = 0 := by simpa using hz
                                  rw [this]; rfl
    simp only [hz', Bool.false_eq_true, ↓reduceIte]
    rw [ha0] at hal
    exact blocks_val hg (o0 := o) len.toNat NMAX_ALIGNED8 _ _ 0 len hal (by omega) hle (by omega) (by decide)
      (by decide) (acc_weaken A0 (by decide))

end ZlibNgF.Proof.Adler32Value
