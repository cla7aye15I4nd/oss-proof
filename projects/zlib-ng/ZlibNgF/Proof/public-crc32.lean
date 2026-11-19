import ZlibNgF.Spec.Safety.Goals
import ZlibNgF.Spec.Functional.Goals

/-!
# Proofs of `crc32.c`, `arch/generic/crc32_braid_c.c`, `crc32_braid_comb.c` and `crc32_braid_comb_p.h` (`ZlibNgF`)

Proves safety and termination of `get_crc_table`, `crc32`, `crc32_z` and the five `crc32_combine*`
entry points, the rejection values of the patched `crc32_combine*` functions, and a concrete
non-vacuity witness for the braided kernel on an unaligned buffer.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Crc32
open C ZlibNg.Crc32Tbl ZlibNg.Crc32Braid ZlibNg.Crc32CombP ZlibNg.Crc32Comb ZlibNg.Crc32
open ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNgF.Spec.Functional

/-! ## Heap-preserving runs -/

/-- `m` terminates on `h` without fault, leaves `h` unchanged, and its value satisfies `Q`. -/
private def Ok {α : Type} (h : Heap) (m : M α) (Q : α → Prop) : Prop :=
  ∃ v, C.run m h = .ok (v, h) ∧ Q v

private theorem Ok.pure {α : Type} {h : Heap} {Q : α → Prop} {v : α} (hq : Q v) :
    Ok h (Pure.pure v) Q := ⟨v, rfl, hq⟩

private theorem Ok.bind {α β : Type} {h : Heap} {m : M α} {f : α → M β} {P : α → Prop} {Q : β → Prop}
    (hm : Ok h m P) (hf : ∀ v, P v → Ok h (f v) Q) : Ok h (m >>= f) Q := by
  obtain ⟨v, hv, hp⟩ := hm
  obtain ⟨w, hw, hq⟩ := hf v hp
  exact ⟨w, by rw [C.run_bind, hv]; exact hw, hq⟩

private theorem Ok.mono {α : Type} {h : Heap} {m : M α} {P Q : α → Prop}
    (hm : Ok h m P) (hpq : ∀ v, P v → Q v) : Ok h m Q := by
  obtain ⟨v, hv, hp⟩ := hm
  exact ⟨v, hv, hpq v hp⟩

/-- Loop rule with a decreasing measure: `I` is preserved by every iteration, the measure drops,
and `Q` holds of the state left by the final (false) evaluation of the condition. -/
private theorem cwhile_go_measure {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Prop) (μ : σ → Nat) (Q : σ → Prop)
    (hstep : ∀ s, I s → Ok h (cond s) (fun cs =>
      (cs.1 = true → Ok h (body cs.2) (fun s2 => I s2 ∧ μ s2 < μ s)) ∧ (cs.1 = false → Q cs.2))) :
    ∀ n s, I s → μ s < n → Ok h (cwhile.go cond body n s) Q := by
  intro n
  induction n with
  | zero => intro s _ hlt; omega
  | succ n ih =>
    intro s hI hlt
    obtain ⟨⟨c, s1⟩, hc, ht, hf⟩ := hstep s hI
    cases c with
    | false =>
      refine ⟨s1, ?_, hf rfl⟩
      unfold C.run at *
      simp [cwhile.go, hc]
    | true =>
      obtain ⟨s2, hb, hI2, hμ⟩ := ht rfl
      obtain ⟨s', hgo, hq⟩ := ih s2 hI2 (by omega)
      refine ⟨s', ?_, hq⟩
      unfold C.run at *
      simp [cwhile.go, hc, hb, hgo]

private theorem cwhile_measure {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Prop) (μ : σ → Nat) (Q : σ → Prop) {s : σ}
    (hstep : ∀ s, I s → Ok h (cond s) (fun cs =>
      (cs.1 = true → Ok h (body cs.2) (fun s2 => I s2 ∧ μ s2 < μ s)) ∧ (cs.1 = false → Q cs.2)))
    (hI : I s) (hμ : μ s < fuel) : Ok h (cwhile cond body s) Q :=
  cwhile_go_measure I μ Q hstep fuel s hI hμ

/-! ## `multmodp` -/

private theorem and_or_eq_zero {a x y : UInt32} (h1 : a &&& x = 0) (h2 : a &&& y = 0) :
    a &&& (x ||| y) = 0 := by
  apply UInt32.toBitVec_inj.mp
  have e1 := congrArg UInt32.toBitVec h1
  have e2 := congrArg UInt32.toBitVec h2
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or] at *
  rw [BitVec.and_or_distrib_left, e1, e2]
  rfl

/-- The single set bit `2 ^ i` of the mask `m`. -/
private def bit (i : Nat) : UInt32 := UInt32.ofNat (2 ^ i)

private theorem bit_facts : ∀ i, i < 32 →
    (bit i).toNat = 2 ^ i ∧
    (i = 0 → bit i - 1 = 0) ∧
    (0 < i → bit i >>> 1 = bit (i - 1) ∧ bit i - 1 = (bit (i - 1) - 1) ||| bit (i - 1)) := by
  decide

/-- `multmodp(a, b)` terminates for every non-zero `a`. -/
private theorem multmodp_ok (h : Heap) (a b : UInt32) (ha : a ≠ 0) :
    Ok h (multmodp a b) (fun _ => True) := by
  unfold multmodp
  refine Ok.bind (P := fun _ => True) ?_ (fun _ _ => Ok.pure trivial)
  refine cwhile_measure
    (I := fun s => s.2.2.2 = true ∨
      ∃ i, i < 32 ∧ s.1 = bit i ∧ (a &&& (bit i - 1) ≠ 0 ∨ a &&& bit i ≠ 0))
    (μ := fun s => if s.2.2.2 then 0 else s.1.toNat + 1)
    (Q := fun _ => True) ?_ ?_ ?_
  · rintro ⟨m, p, b, brk⟩ hI
    cases brk with
    | true =>
      exact ⟨(false, m, p, b, true), rfl, fun hc => absurd hc Bool.false_ne_true, fun _ => trivial⟩
    | false =>
      refine ⟨(true, m, p, b, false), rfl, fun _ => ?_, fun hc => absurd hc.symm Bool.false_ne_true⟩
      rcases hI with hI | ⟨i, hi, hm, hinv⟩
      · cases hI
      obtain ⟨hnat, h0, hpos⟩ := bit_facts i hi
      dsimp only at hm
      subst hm
      by_cases hlow : a &&& (bit i - 1) = 0
      · -- the lowest set bit of `a` is bit `i`: the loop breaks here
        have hbit : a &&& bit i ≠ 0 := by
          rcases hinv with h1 | h1
          · exact absurd hlow h1
          · exact h1
        refine ⟨(bit i, p ^^^ b, b, true), ?_, Or.inl rfl, by simp⟩
        simp [C.run, hbit, hlow]
      · -- a lower bit of `a` is set: shift the mask
        have hipos : 0 < i := by
          rcases Nat.eq_zero_or_pos i with h1 | h1
          · exact absurd (by rw [h0 h1]; exact UInt32.and_zero) hlow
          · exact h1
        obtain ⟨hshift, hsplit⟩ := hpos hipos
        obtain ⟨hnat', _, _⟩ := bit_facts (i - 1) (by omega)
        have hinv' : a &&& (bit (i - 1) - 1) ≠ 0 ∨ a &&& bit (i - 1) ≠ 0 := by
          by_cases h1 : a &&& (bit (i - 1) - 1) = 0
          · right
            intro h2
            apply hlow
            rw [hsplit]
            exact and_or_eq_zero h1 h2
          · exact Or.inl h1
        have hμ : (bit (i - 1)).toNat + 1 < (bit i).toNat + 1 := by
          rw [hnat, hnat']
          have : 2 ^ i = 2 * 2 ^ (i - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          have : 0 < 2 ^ (i - 1) := Nat.pow_pos (by omega)
          omega
        by_cases hbit : a &&& bit i = 0
        · refine ⟨(bit (i - 1), p, if b &&& 1 != 0 then (b >>> 1) ^^^ POLY else b >>> 1, false),
            ?_, Or.inr ⟨i - 1, by omega, rfl, hinv'⟩, by simpa using hμ⟩
          simp [C.run, hbit, hshift]
        · refine ⟨(bit (i - 1), p ^^^ b, if b &&& 1 != 0 then (b >>> 1) ^^^ POLY else b >>> 1, false),
            ?_, Or.inr ⟨i - 1, by omega, rfl, hinv'⟩, by simpa using hμ⟩
          simp [C.run, hbit, hlow, hshift]
  · refine Or.inr ⟨31, by omega, rfl, ?_⟩
    by_cases h1 : a &&& bit 31 = 0
    · left
      intro h2
      apply ha
      have hall : (bit 31 - 1) ||| bit 31 = 0xffffffff := by decide
      have : a &&& 0xffffffff = 0 := by
        rw [← hall]; exact and_or_eq_zero h2 h1
      rw [← this]
      exact (UInt32.and_neg_one).symm
    · exact Or.inr h1
  · show (bit 31).toNat + 1 < fuel
    decide

/-! ## `x2nmodp` -/

private theorem u32_index_ok {h : Heap} {r : URef} {a : Array UInt32}
    (hg : Space.get h r = some a) {i : Nat} (hi : i < a.size) :
    Ok h (Ptr.index (Ptr.ref r 0) (Int.ofNat i) : M UInt32) (fun v => v = a[i]!) := by
  refine ⟨a[i], ?_, (getElem!_pos a i hi).symm⟩
  have hc : (0 : Nat) ≤ a.size ∧ 0 ≤ ((0 : Nat) : Int) + Int.ofNat i ∧
      ((0 : Nat) : Int) + Int.ofNat i ≤ (a.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  have hnat : (((0 : Nat) : Int) + Int.ofNat i).toNat = i := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [C.run, Ptr.index, Ptr.add, Ptr.load, bind_app, hg, hc, and_self, ↓reduceIte, hnat, hi,
    ↓reduceDIte]

private theorem x2n_table_facts :
    x2n_table.size = 32 ∧ ∀ i, i < 32 → x2n_table[i]! ≠ 0 := by
  decide

private theorem int64_shr1 (n : Int64) : (n >>> 1).toInt = n.toInt / 2 := by
  have h1 : (n >>> 1).toBitVec = n.toBitVec.sshiftRight 1 := rfl
  rw [← Int64.toInt_toBitVec, h1, BitVec.toInt_sshiftRight, Int64.toInt_toBitVec,
    Int.shiftRight_eq_div_pow]
  rfl

/-- `x2nmodp(n, k)` terminates for every non-negative `n` once `x2n_table` is initialised. -/
private theorem x2nmodp_ok (h : Heap) (hx : h.x2nTable = x2n_table) (n : Int64) (k : UInt32)
    (hn : 0 ≤ n.toInt) : Ok h (x2nmodp n k) (fun _ => True) := by
  unfold x2nmodp
  refine Ok.bind (P := fun _ => True) ?_ (fun _ _ => Ok.pure trivial)
  refine cwhile_measure (I := fun s => 0 ≤ s.2.1.toInt) (μ := fun s => s.2.1.toInt.toNat)
    (Q := fun _ => True) ?_ hn ?_
  · rintro ⟨p, n, k⟩ hI
    refine ⟨(n != 0, p, n, k), rfl, fun hc => ?_, fun _ => trivial⟩
    dsimp only at hc hI ⊢
    have hne : n ≠ 0 := by simpa using hc
    have hpos : 0 < n.toInt := by
      have : n.toInt ≠ 0 := fun h0 => hne (Int64.toInt_inj.mp (h0.trans Int64.toInt_zero.symm))
      omega
    have hfin : ∀ p' : UInt32, Ok h (pure (p', n >>> 1, k + 1) : M (UInt32 × Int64 × UInt32))
        (fun s2 => 0 ≤ s2.2.1.toInt ∧ s2.2.1.toInt.toNat < n.toInt.toNat) := by
      intro p'
      refine Ok.pure ?_
      dsimp only
      rw [int64_shr1]
      omega
    by_cases hb : (n &&& 1 != 0) = true
    · simp only [hb, ↓reduceIte]
      have hidx : (k &&& 31).toNat < h.x2nTable.size := by
        rw [hx, x2n_table_facts.1, UInt32.toNat_and]
        exact Nat.lt_succ_of_le Nat.and_le_right
      refine Ok.bind (P := fun t => t ≠ 0) ?_
        (fun t ht => Ok.bind (multmodp_ok h t p ht) (fun p' _ => hfin p'))
      refine Ok.mono (u32_index_ok (r := URef.st_x2n_table) (a := h.x2nTable) rfl hidx) ?_
      intro v hv
      rw [hv, hx]
      exact x2n_table_facts.2 _ (by rw [hx, x2n_table_facts.1] at hidx; exact hidx)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact hfin p
  · show n.toInt.toNat < fuel
    have := Int64.toInt_lt n
    unfold fuel
    omega

/-! ## Read-only buffer and table primitives -/

private theorem ptr_add_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (k : Nat) (hle : o + k ≤ data.size) :
    Ok h ((Ptr.ref r o).add (Int.ofNat k)) (fun p => p = .ref r (o + k)) := by
  refine ⟨.ref r (o + k), ?_, rfl⟩
  dsimp only [C.run, Ptr.add]
  rw [hg]
  dsimp only
  have hc : o ≤ data.size ∧ 0 ≤ (o : Int) + Int.ofNat k ∧ (o : Int) + Int.ofNat k ≤ (data.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  have hnat : ((o : Int) + Int.ofNat k).toNat = o + k := by
    simp only [Int.ofNat_eq_natCast]; omega
  split
  · rw [hnat]
  · rename_i hn; exact absurd hc hn

private theorem load8_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (hlt : o < data.size) : Ok h (load8 (.ref r o)) (fun _ => True) := by
  refine ⟨data[o], ?_, trivial⟩
  dsimp only [C.run, load8, Ptr.load]
  rw [hg]
  dsimp only
  split
  · rfl
  · rename_i hn; exact absurd hlt hn

private theorem index8_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (i : Nat) (hlt : o + i < data.size) :
    Ok h (index8 (.ref r o) (Int.ofNat i)) (fun _ => True) := by
  unfold index8 Ptr.index
  refine Ok.bind (ptr_add_ok hg i (by omega)) ?_
  intro p hp
  subst hp
  exact load8_ok hg hlt

set_option maxRecDepth 100000 in
private theorem crc_table_size : crc_table.size = 256 := by decide

set_option maxRecDepth 100000 in
private theorem braid_table_facts :
    crc_braid_table.size = 8 ∧ ∀ k, k < 8 → (crc_braid_table[k]!).size = 256 := by
  decide

private theorem crcTab_ok {h : Heap} (hc : h.crcTable = crc_table) (i : UInt64) (hi : i.toNat < 256) :
    Ok h (crcTab i) (fun _ => True) := by
  unfold crcTab
  refine Ok.mono (u32_index_ok (r := URef.st_crc_table) (a := h.crcTable) rfl ?_) (fun _ _ => trivial)
  rw [hc, crc_table_size]
  exact hi

private theorem braidTab_ok (h : Heap) (k i : Nat) (hk : k < 8) (hi : i < 256) :
    Ok h (braidTab k i) (fun _ => True) := by
  obtain ⟨hsz, hrow⟩ := braid_table_facts
  have hk' : k < crc_braid_table.size := by rw [hsz]; exact hk
  have hrow' := hrow k hk
  rw [getElem!_pos crc_braid_table k hk'] at hrow'
  have hi' : i < (crc_braid_table[k]'hk').size := by rw [hrow']; exact hi
  unfold braidTab
  rw [Array.getElem?_eq_getElem hk']
  dsimp only
  rw [Array.getElem?_eq_getElem hi']
  exact Ok.pure trivial

private theorem and_ff_32 (x : UInt32) : (x &&& 0xff).toUInt64.toNat < 256 := by
  rw [UInt32.toNat_toUInt64, UInt32.toNat_and]
  exact Nat.lt_succ_of_le Nat.and_le_right

private theorem and_ff_64 (x : UInt64) : (x &&& 0xff).toNat < 256 := by
  rw [UInt64.toNat_and]
  exact Nat.lt_succ_of_le Nat.and_le_right

/-! ## `CRC_DO1`, `CRC_DO8`, `crc_word` -/

private theorem crc_do1_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) {o : Nat} (hlt : o + 1 ≤ data.size) :
    Ok h (crc_do1 c (.ref r o)) (fun p => p.2 = .ref r (o + 1)) := by
  unfold crc_do1
  refine Ok.bind (load8_ok hg (by omega)) ?_
  intro b _
  refine Ok.bind (ptr_add_ok hg 1 hlt) ?_
  intro p hp
  refine Ok.bind (crcTab_ok hc _ (and_ff_32 _)) ?_
  intro t _
  exact Ok.pure hp

private theorem crc_do8_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) {o : Nat} (hle : o + 8 ≤ data.size) :
    Ok h (crc_do8 c (.ref r o)) (fun p => p.2 = .ref r (o + 8)) := by
  unfold crc_do8
  refine Ok.bind (crc_do1_ok hc hg _ (by omega)) ?_
  rintro ⟨_, _⟩ hb
  dsimp only at hb ⊢
  subst hb
  refine Ok.bind (crc_do1_ok hc hg _ (by omega)) ?_
  rintro ⟨_, _⟩ hb
  dsimp only at hb ⊢
  subst hb
  refine Ok.bind (crc_do1_ok hc hg _ (by omega)) ?_
  rintro ⟨_, _⟩ hb
  dsimp only at hb ⊢
  subst hb
  refine Ok.bind (crc_do1_ok hc hg _ (by omega)) ?_
  rintro ⟨_, _⟩ hb
  dsimp only at hb ⊢
  subst hb
  refine Ok.bind (crc_do1_ok hc hg _ (by omega)) ?_
  rintro ⟨_, _⟩ hb
  dsimp only at hb ⊢
  subst hb
  refine Ok.bind (crc_do1_ok hc hg _ (by omega)) ?_
  rintro ⟨_, _⟩ hb
  dsimp only at hb ⊢
  subst hb
  refine Ok.bind (crc_do1_ok hc hg _ (by omega)) ?_
  rintro ⟨_, _⟩ hb
  dsimp only at hb ⊢
  subst hb
  exact Ok.mono (crc_do1_ok hc hg _ (by omega)) (fun p hp => by rw [hp])

/-- Facts about the constant-trip `for (k = …; k < 8; k++)` loops over `int`. -/
private theorem kloop_facts : ∀ j, j < 9 →
    (Int32.ofNat j < BRAID_W_I32 ↔ j < 8) ∧
    (Int32.ofNat j).toInt.toNat = j ∧
    (j < 8 → Int32.ofNat j + 1 = Int32.ofNat (j + 1)) := by
  decide

private theorem crc_word_ok {h : Heap} (hc : h.crcTable = crc_table) (d : UInt64) :
    Ok h (crc_word d) (fun _ => True) := by
  unfold crc_word
  refine Ok.bind (P := fun _ => True) ?_ (fun v _ => by obtain ⟨_, _⟩ := v; exact Ok.pure trivial)
  refine cwhile_measure (I := fun s => ∃ j, j ≤ 8 ∧ s.2 = Int32.ofNat j)
    (μ := fun s => 8 - s.2.toInt.toNat) (Q := fun _ => True) ?_ ⟨0, by omega, rfl⟩
    (by show 8 - (0 : Int32).toInt.toNat < fuel; unfold fuel; decide)
  rintro ⟨d, k⟩ ⟨j, hj, hk⟩
  dsimp only at hk
  subst hk
  obtain ⟨hlt, hnat, hsucc⟩ := kloop_facts j (by omega)
  refine ⟨_, rfl, fun hcnd => ?_, fun _ => trivial⟩
  have hj8 : j < 8 := hlt.mp (by simpa using hcnd)
  refine Ok.bind (crcTab_ok hc _ (and_ff_64 _)) (fun t _ => Ok.pure ⟨⟨j + 1, by omega, hsucc hj8⟩, ?_⟩)
  dsimp only
  rw [hsucc hj8, hnat, (kloop_facts (j + 1) (by omega)).2.1]
  omega

private theorem loadWordAt_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (w : Nat) (hle : o + 8 * w + 8 ≤ data.size) :
    Ok h (loadWordAt (.ref r o) w) (fun _ => True) := by
  unfold loadWordAt
  refine Ok.bind (index8_ok hg (8 * w) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 1) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 2) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 3) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 4) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 5) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 6) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 7) (by omega)) (fun _ _ => ?_)
  exact Ok.pure trivial

private theorem u64_ge_toNat {a : UInt64} {n : Nat} (hn : n < 2 ^ 64) :
    (a ≥ UInt64.ofNat n) ↔ n ≤ a.toNat := by
  rw [GE.ge, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hn]

private theorem and_seven (x : UInt64) : (x &&& (BRAID_W - 1)).toNat = x.toNat % 8 := by
  rw [UInt64.toNat_and, show (BRAID_W - 1).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

private theorem res_succ (b : UInt64) (o : Nat) :
    (b + UInt64.ofNat (o + 1)).toNat % 8 = ((b + UInt64.ofNat o).toNat % 8 + 1) % 8 := by
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-- The two tail loops `while (len >= 8) CRC_DO8; while (len) CRC_DO1;`. -/
private theorem tail_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) (o : Nat) (len : UInt64)
    (hle : o + len.toNat ≤ data.size) :
    Ok h (do
      let (c8, buf8, len8) ← cwhile
        (fun ((c, buf, len) : UInt32 × BPtr × UInt64) => pure (len >= 8, (c, buf, len)))
        (fun ((c, buf, len) : UInt32 × BPtr × UInt64) => do
          let len := len - 8
          let (c, buf) ← crc_do8 c buf
          pure (c, buf, len))
        (c, Ptr.ref r o, len)
      let (cf, _, _) ← cwhile
        (fun ((c, buf, len) : UInt32 × BPtr × UInt64) => pure (len != 0, (c, buf, len)))
        (fun ((c, buf, len) : UInt32 × BPtr × UInt64) => do
          let len := len - 1
          let (c, buf) ← crc_do1 c buf
          pure (c, buf, len))
        (c8, buf8, len8)
      return cf : M UInt32) (fun _ => True) := by
  have hfuel : ∀ l : UInt64, l.toNat < fuel := fun l => by unfold fuel; exact l.toNat_lt
  let I : UInt32 × BPtr × UInt64 → Prop := fun s => ∃ o', s.2.1 = .ref r o' ∧ o' + s.2.2.toNat ≤ data.size
  refine Ok.bind (P := I) ?_ ?_
  · refine cwhile_measure (I := I) (μ := fun s => s.2.2.toNat) (Q := I) ?_ ⟨o, rfl, hle⟩ (hfuel len)
    rintro ⟨c, b, l⟩ ⟨o', hb, hl⟩
    dsimp only at hb hl
    subst hb
    refine ⟨_, rfl, fun hcnd => ?_, fun _ => ⟨o', rfl, hl⟩⟩
    have h8 : 8 ≤ l.toNat := (u64_ge_toNat (n := 8) (by decide)).mp (by simpa using hcnd)
    dsimp only
    refine Ok.bind (crc_do8_ok hc hg c (o := o') (by omega)) ?_
    rintro ⟨c', b'⟩ hb'
    dsimp only at hb' ⊢
    subst hb'
    have hsub : (l - 8).toNat = l.toNat - 8 := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; exact h8)
    exact Ok.pure ⟨⟨o' + 8, rfl, by dsimp only; omega⟩, by dsimp only; omega⟩
  · rintro ⟨c8, b8, l8⟩ hI
    dsimp only
    refine Ok.bind (P := fun _ => True) ?_ (fun v _ => by obtain ⟨_, _, _⟩ := v; exact Ok.pure trivial)
    refine cwhile_measure (I := I) (μ := fun s => s.2.2.toNat) (Q := fun _ => True) ?_ hI (hfuel l8)
    rintro ⟨c, b, l⟩ ⟨o', hb, hl⟩
    dsimp only at hb hl
    subst hb
    refine ⟨_, rfl, fun hcnd => ?_, fun _ => trivial⟩
    have h1 : 1 ≤ l.toNat := by
      have : l ≠ 0 := by simpa using hcnd
      have : l.toNat ≠ 0 := fun h0 => this (UInt64.toNat_inj.mp (by rw [h0]; rfl))
      omega
    dsimp only
    refine Ok.bind (crc_do1_ok hc hg c (o := o') (by omega)) ?_
    rintro ⟨c', b'⟩ hb'
    dsimp only at hb' ⊢
    subst hb'
    have hsub : (l - 1).toNat = l.toNat - 1 := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; exact h1)
    exact Ok.pure ⟨⟨o' + 1, rfl, by dsimp only; omega⟩, by dsimp only; omega⟩

private theorem braid_internal_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) (o : Nat) (len : UInt64)
    (hle : o + len.toNat ≤ data.size) :
    Ok h (crc32_braid_internal c (.ref r o) len) (fun _ => True) := by
  unfold crc32_braid_internal
  dsimp only
  split
  · rename_i hge
    have h47 : 47 ≤ len.toNat := by
      have : BRAID_N * BRAID_W + BRAID_W - 1 = UInt64.ofNat 47 := by decide
      rw [this] at hge
      exact (u64_ge_toNat (by decide)).mp hge
    let res : Nat → Nat := fun o' => (h.baseAddr r + UInt64.ofNat o').toNat % 8
    let IA : UInt32 × BPtr × UInt64 → Prop := fun s => ∃ o', s.2.1 = .ref r o' ∧ o ≤ o' ∧
      o' + s.2.2.toNat = o + len.toNat ∧ (o' - o) + (8 - res o') % 8 ≤ 7
    have hfuel : ∀ l : UInt64, l.toNat < fuel := fun l => by unfold fuel; exact l.toNat_lt
    refine Ok.bind (P := IA) ?_ ?_
    · refine cwhile_measure (I := IA) (μ := fun s => s.2.2.toNat) (Q := IA) ?_
        ⟨o, rfl, Nat.le_refl o, rfl, by omega⟩ (hfuel len)
      rintro ⟨c, b, l⟩ ⟨o', hb, ho, hsum, hres⟩
      dsimp only at hb ho hsum hres
      subst hb
      dsimp only
      split
      · rename_i hl0
        have hl1 : 1 ≤ l.toNat := by
          have : l ≠ 0 := by simpa using hl0
          have : l.toNat ≠ 0 := fun h0 => this (UInt64.toNat_inj.mp (by rw [h0]; rfl))
          omega
        refine Ok.bind (P := fun a => a = h.baseAddr r + UInt64.ofNat o') ⟨_, rfl, rfl⟩ ?_
        intro a ha
        subst ha
        refine Ok.pure ⟨fun hcnd => ?_, fun _ => ⟨o', rfl, ho, hsum, hres⟩⟩
        have hr0 : res o' ≠ 0 := by
          have h7 : ((h.baseAddr r + UInt64.ofNat o') &&& (BRAID_W - 1)).toNat ≠ 0 := by
            intro h0
            have : ((h.baseAddr r + UInt64.ofNat o') &&& (BRAID_W - 1)) = 0 :=
              UInt64.toNat_inj.mp (by rw [h0]; rfl)
            simp [this] at hcnd
          rw [and_seven] at h7
          exact h7
        have hsucc := res_succ (h.baseAddr r) o'
        dsimp only
        refine Ok.bind (crc_do1_ok hc hg c (o := o') (by omega)) ?_
        rintro ⟨c', b'⟩ hb'
        dsimp only at hb' ⊢
        subst hb'
        have hsub : (l - 1).toNat = l.toNat - 1 := UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le]; exact hl1)
        refine Ok.pure ⟨⟨o' + 1, rfl, by omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        show (o' + 1 - o) + (8 - res (o' + 1)) % 8 ≤ 7
        simp only [res] at hres hr0 ⊢
        omega
      · exact Ok.pure ⟨fun hcnd => absurd hcnd (by simp), fun _ => ⟨o', rfl, ho, hsum, hres⟩⟩
    · rintro ⟨c', b', l'⟩ ⟨o', hb, ho, hsum, hres⟩
      dsimp only at hb ho hsum hres
      subst hb
      dsimp only
      have hl40 : 40 ≤ l'.toNat := by omega
      have hB : (l' / (BRAID_N * BRAID_W)).toNat = l'.toNat / 40 := by
        rw [UInt64.toNat_div]; rfl
      have hlt := l'.toNat_lt
      have hBNW : (l' / (BRAID_N * BRAID_W) * BRAID_N * BRAID_W).toNat = l'.toNat / 40 * 40 := by
        rw [UInt64.toNat_mul, UInt64.toNat_mul, hB, show BRAID_N.toNat = 5 from rfl,
          show BRAID_W.toNat = 8 from rfl]
        simp only [Nat.reducePow] at hlt ⊢
        omega
      have hrem : (l' - l' / (BRAID_N * BRAID_W) * BRAID_N * BRAID_W).toNat = l'.toNat % 40 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hBNW]; omega), hBNW]
        omega
      let IB : BraidState → Prop := fun s => 1 ≤ s.blks.toNat ∧
        ∃ o2, s.words = .ref r o2 ∧ o2 + 40 * s.blks.toNat + l'.toNat % 40 ≤ data.size
      refine Ok.bind (P := fun st => ∃ o2, st.words = .ref r o2 ∧ o2 + 40 + l'.toNat % 40 ≤ data.size)
        ?_ ?_
      · refine cwhile_measure (I := IB) (μ := fun s => s.blks.toNat)
          (Q := fun st => ∃ o2, st.words = .ref r o2 ∧ o2 + 40 + l'.toNat % 40 ≤ data.size) ?_
          ⟨by dsimp only; omega, o', rfl, by dsimp only; rw [hB]; omega⟩ (hfuel _)
        rintro st ⟨hb1, o2, hw, hsz⟩
        have hsub : (st.blks - 1).toNat = st.blks.toNat - 1 := UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le]; exact hb1)
        refine Ok.pure ⟨fun hcnd => ?_, fun hcnd => ?_⟩
        · have hb2 : 2 ≤ st.blks.toNat := by
            have : st.blks - 1 ≠ 0 := by simpa using hcnd
            have : (st.blks - 1).toNat ≠ 0 := fun h0 => this (UInt64.toNat_inj.mp (by rw [h0]; rfl))
            omega
          dsimp only
          rw [hw]
          refine Ok.bind (loadWordAt_ok hg 0 (by omega)) (fun w0 _ => ?_)
          refine Ok.bind (loadWordAt_ok hg 1 (by omega)) (fun w1 _ => ?_)
          refine Ok.bind (loadWordAt_ok hg 2 (by omega)) (fun w2 _ => ?_)
          refine Ok.bind (loadWordAt_ok hg 3 (by omega)) (fun w3 _ => ?_)
          refine Ok.bind (loadWordAt_ok hg 4 (by omega)) (fun w4 _ => ?_)
          refine Ok.bind (ptr_add_ok hg 40 (by omega)) (fun wd hwd => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (P := fun _ => True) ?_ (fun v _ => ?_)
          · refine cwhile_measure (I := fun s => ∃ j, j ≤ 8 ∧ s.2 = Int32.ofNat j)
              (μ := fun s => 8 - s.2.toInt.toNat) (Q := fun _ => True) ?_ ⟨1, by omega, rfl⟩
              (by show 8 - (1 : Int32).toInt.toNat < fuel; unfold fuel; decide)
            rintro ⟨⟨a0, a1, a2, a3, a4⟩, k⟩ ⟨j, hj, hk⟩
            dsimp only at hk
            subst hk
            obtain ⟨hltj, hnat, hsucc⟩ := kloop_facts j (by omega)
            refine ⟨_, rfl, fun hcnd => ?_, fun _ => trivial⟩
            have hj8 : j < 8 := hltj.mp (by simpa using hcnd)
            dsimp only
            rw [hnat]
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.pure ⟨⟨j + 1, by omega, hsucc hj8⟩, ?_⟩
            dsimp only
            rw [hsucc hj8, (kloop_facts (j + 1) (by omega)).2.1]
            omega
          · obtain ⟨⟨_, _, _, _, _⟩, _⟩ := v
            subst hwd
            refine Ok.pure ⟨⟨by dsimp only; omega, o2 + 40, rfl, by dsimp only; omega⟩, by dsimp only; omega⟩
        · have hb2 : st.blks.toNat = 1 := by
            have : st.blks - 1 = 0 := by simpa using hcnd
            have : (st.blks - 1).toNat = 0 := by rw [this]; rfl
            omega
          exact ⟨o2, hw, by omega⟩
      · rintro st ⟨o2, hw, hsz⟩
        rw [hw]
        refine Ok.bind (loadWordAt_ok hg 0 (by omega)) (fun w0 _ => ?_)
        refine Ok.bind (loadWordAt_ok hg 1 (by omega)) (fun w1 _ => ?_)
        refine Ok.bind (loadWordAt_ok hg 2 (by omega)) (fun w2 _ => ?_)
        refine Ok.bind (loadWordAt_ok hg 3 (by omega)) (fun w3 _ => ?_)
        refine Ok.bind (loadWordAt_ok hg 4 (by omega)) (fun w4 _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (ptr_add_ok hg 40 (by omega)) (fun wd hwd => ?_)
        subst hwd
        exact tail_ok hc hg _ (o2 + 40) _ (by rw [hrem]; omega)
  · exact tail_ok hc hg c o len hle


/-! ## Public `get_crc_table`, `crc32`, `crc32_z` -/

theorem get_crc_table_safety : Goal.get_crc_table_safety := by
  intro h hg
  exact ⟨_, h.crcTable, rfl, rfl, rfl, rfl, by rw [hg.1]; exact crc_table_size⟩

theorem crc32_z_safety : Goal.crc32_z_safety := by
  intro h seed buf len bytes hg hb
  rcases hb with ⟨rfl, _⟩ | ⟨r, off, data, rfl, hget, hle, _⟩
  · exact ⟨0, rfl⟩
  · obtain ⟨v, hv, _⟩ := braid_internal_ok hg.1 hget (~~~seed.toUInt32) off len hle
    refine ⟨(v ^^^ 0xffffffff).toUInt64, ?_⟩
    have hne : (Ptr.ref r off == (.null : BPtr)) = false := by simp
    unfold crc32_z crc32_braid
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [C.run_bind, C.run_bind, hv]
    rfl

theorem crc32_safety : Goal.crc32_safety := by
  intro h seed buf len bytes hg hb
  exact crc32_z_safety h _ buf len.toUInt64 bytes hg (by rw [UInt32.toNat_toUInt64]; exact hb)

theorem crc32_nonvacuous : Goal.crc32_nonvacuous := by
  let arr : Array UInt8 := Array.replicate 128 0x41
  let h : Heap :=
    { bytes := upd Heap.empty.bytes 0 (some arr), nextBlk := 1, crcTable := crc_table,
      x2nTable := x2n_table, baseAddr := (fun _ => 3) }
  let buf : BPtr := .ref (.heap 0) 0
  let bytes : List UInt8 := (arr.toList.drop 0).take 128
  have hg : Space.get h (BRef.heap 0) = some arr := by
    simp only [Space.get, Heap.getBytes, h, upd_same]
  have harr_sz : arr.size = 128 := Array.size_replicate
  have hlen_bytes : bytes.length = 128 := by
    dsimp [bytes]
    rw [List.length_take, List.length_drop, Array.length_toList, harr_sz]
    omega
  have hbuf_ne : buf ≠ .null := by dsimp [buf]; intro hc; cases hc
  have hglob : CrcGlobals h := ⟨rfl, rfl⟩
  have hbb : BufferBytes h buf 128 bytes := Or.inr ⟨BRef.heap 0, 0, arr, rfl, hg, by omega, rfl⟩
  obtain ⟨r, hrun⟩ := crc32_z_safety h 0 buf 128 bytes hglob hbb
  exact ⟨h, buf, bytes, r, hglob, hbuf_ne, hlen_bytes, hbb, hrun⟩

/-! ## `crc32_combine*` -/

private theorem crc32_combine_op__ok (h : Heap) (crc1 crc2 op : UInt32) :
    Ok h (crc32_combine_op_ crc1 crc2 op) (fun r => op = 0 → r = 0) := by
  unfold crc32_combine_op_
  by_cases hop : op = 0
  · subst hop
    exact ⟨0, rfl, fun _ => rfl⟩
  · have hb : (op == 0) = false := by simpa using hop
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact Ok.bind (multmodp_ok h op crc1 hop) (fun m _ => Ok.pure (fun h0 => absurd h0 hop))

private theorem crc32_combine_gen__ok (h : Heap) (hx : h.x2nTable = x2n_table) (len2 : Int64) :
    Ok h (crc32_combine_gen_ len2) (fun r => len2 < 0 → r = 0) := by
  unfold crc32_combine_gen_
  by_cases hneg : len2 < 0
  · simp only [hneg, ↓reduceIte]
    exact Ok.pure (fun _ => rfl)
  · have hn : 0 ≤ len2.toInt := by
      have h1 : ¬ len2.toInt < (0 : Int64).toInt := fun h2 => hneg (Int64.lt_iff_toInt_lt.mpr h2)
      rw [Int64.toInt_zero] at h1
      omega
    simp only [hneg, ↓reduceIte]
    exact Ok.mono (x2nmodp_ok h hx len2 3 hn) (fun _ _ h0 => by simp_all)

/-- A negative `len2` is rejected before any table is read. -/
private theorem crc32_combine_gen__neg (h : Heap) (len2 : Int64) (hneg : len2 < 0) :
    C.run (crc32_combine_gen_ len2) h = .ok (0, h) := by
  unfold crc32_combine_gen_
  simp only [hneg, ↓reduceIte]
  rfl

private theorem crc32_combine__ok (h : Heap) (hx : h.x2nTable = x2n_table) (crc1 crc2 : UInt32)
    (len2 : Int64) : Ok h (crc32_combine_ crc1 crc2 len2) (fun _ => True) := by
  unfold crc32_combine_
  exact Ok.bind (crc32_combine_gen__ok h hx len2)
    (fun op _ => Ok.mono (crc32_combine_op__ok h crc1 crc2 op) (fun _ _ => trivial))

private theorem crc32_combine__neg (h : Heap) (crc1 crc2 : UInt32) (len2 : Int64) (hneg : len2 < 0) :
    C.run (crc32_combine_ crc1 crc2 len2) h = .ok (0, h) := by
  unfold crc32_combine_
  rw [C.run_bind, crc32_combine_gen__neg h len2 hneg]
  rfl

private theorem ok_toUInt64 {h : Heap} {m : M UInt32} {Q : UInt32 → Prop} (hm : Ok h m Q) :
    ∃ r, C.run (m >>= fun r => pure r.toUInt64) h = .ok (r, h) := by
  obtain ⟨v, hv, _⟩ := hm
  exact ⟨v.toUInt64, by rw [C.run_bind, hv]; rfl⟩

theorem crc32_combine_gen_safety : Goal.crc32_combine_gen_safety := by
  intro h len2 hg
  exact ok_toUInt64 (crc32_combine_gen__ok h hg.2 len2)

theorem crc32_combine_gen64_safety : Goal.crc32_combine_gen64_safety := by
  intro h len2 hg
  exact ok_toUInt64 (crc32_combine_gen__ok h hg.2 len2)

theorem crc32_combine_op_safety : Goal.crc32_combine_op_safety := by
  intro h crc1 crc2 op
  exact ok_toUInt64 (crc32_combine_op__ok h crc1.toUInt32 crc2.toUInt32 op.toUInt32)

theorem crc32_combine_safety : Goal.crc32_combine_safety := by
  intro h crc1 crc2 len2 hg
  exact ok_toUInt64 (crc32_combine__ok h hg.2 crc1.toUInt32 crc2.toUInt32 len2)

theorem crc32_combine64_safety : Goal.crc32_combine64_safety := by
  intro h crc1 crc2 len2 hg
  exact ok_toUInt64 (crc32_combine__ok h hg.2 crc1.toUInt32 crc2.toUInt32 len2)

theorem crc32_combine_rejection_functional : Goal.crc32_combine_rejection_functional := by
  intro h crc1 crc2 op len2
  refine ⟨fun hneg => ⟨?_, ?_, ?_, ?_⟩, fun hop => ?_⟩
  · show C.run (crc32_combine_ crc1.toUInt32 crc2.toUInt32 len2 >>= fun r => pure r.toUInt64) h = _
    rw [C.run_bind, crc32_combine__neg h _ _ len2 hneg]
    rfl
  · show C.run (crc32_combine_ crc1.toUInt32 crc2.toUInt32 len2 >>= fun r => pure r.toUInt64) h = _
    rw [C.run_bind, crc32_combine__neg h _ _ len2 hneg]
    rfl
  · show C.run (crc32_combine_gen_ len2 >>= fun r => pure r.toUInt64) h = _
    rw [C.run_bind, crc32_combine_gen__neg h len2 hneg]
    rfl
  · show C.run (crc32_combine_gen_ len2 >>= fun r => pure r.toUInt64) h = _
    rw [C.run_bind, crc32_combine_gen__neg h len2 hneg]
    rfl
  · show C.run (crc32_combine_op_ crc1.toUInt32 crc2.toUInt32 op.toUInt32 >>= fun r => pure r.toUInt64) h = _
    obtain ⟨r, hr, hz⟩ := crc32_combine_op__ok h crc1.toUInt32 crc2.toUInt32 op.toUInt32
    rw [C.run_bind, hr, hz hop]
    rfl

end ZlibNgF.Proof.Crc32
