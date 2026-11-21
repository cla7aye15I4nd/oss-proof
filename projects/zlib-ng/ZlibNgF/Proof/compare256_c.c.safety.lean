import ZlibNgF.Proof.«chunkset.mem»
import ZlibNgF.ZlibNg.arch.generic.«compare256_c.c»

/-!
# Safety of `compare256_c` (`ZlibNgF`)

`compare256_c` is `compare256_64_static` (`compare256_c.c:43-63`): sixteen trips of two 8-byte loads at
`src0 + len`, `src1 + len` (`len = 0, 8, ..., 248`). The last load of each pointer starts at offset 248 and is 8 bytes
wide, so the bytes read are exactly `[src0, src0 + 256)` and `[src1, src1 + 256)` (fewer on an early mismatch), and the
pointers formed are `src + 8k` for `k ≤ 32`, ending at `src + 256`. Both pointers must therefore point into one live
byte block with 256 bytes after them; the result is at most 256, and the heap is unchanged (`compare256_c_ok`).

`zng_first_diff_byte64` of a non-zero word is `zng_ctz64 / 8`, at most 8 (`first_diff_ok`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Compare256
open C ZlibNg.Deflate ZlibNg.Compare256
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.ChunkMem (sat_add sat_memread8)

/-! ## `zng_ctz64` -/

/-- A `for` loop in `Id` whose steps raise the measure `g` by at most one while it stays below `N`. -/
theorem forIn_le {σ : Type} (g : σ → Nat) (f : Nat → σ → Id (ForInStep σ)) (N : Nat)
    (hf : ∀ a r, g r + 1 < N → ∃ r', f a r = .yield r' ∧ g r' ≤ g r + 1) :
    ∀ (l : List Nat) (r : σ), g r + l.length < N → g (Id.run (forIn l r f)) ≤ g r + l.length := by
  intro l
  induction l with
  | nil => intro r _; exact Nat.le_refl _
  | cons x l ih =>
    intro r hN
    simp only [List.length_cons] at hN
    obtain ⟨r', e, hr⟩ := hf x r (by omega)
    have := ih r' (by omega)
    simp only [List.forIn_cons, e, List.length_cons] at this ⊢
    exact Nat.le_trans this (by omega)

theorem ctz64_le (value : UInt64) (hv : value ≠ 0) :
    ∃ n : UInt32, zng_ctz64 value = pure n ∧ n.toNat ≤ 64 := by
  have hne : (value == 0) = false := by simpa using hv
  refine ⟨_, by simp only [zng_ctz64, hne, Bool.false_eq_true, ↓reduceIte]; rfl, ?_⟩
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have key := forIn_le (fun r : UInt32 × UInt64 => r.1.toNat)
    (fun _ (r : UInt32 × UInt64) => if (r.2 &&& 1 == 0) = true then pure (ForInStep.yield (r.1 + 1, r.2 >>> 1))
      else pure (ForInStep.yield (r.1, r.2))) (2 ^ 32) ?_ (List.range' 0 [:64].size)
    ((0 : UInt32), value) (by simp)
  · exact Nat.le_trans key (by simp)
  · intro a r hr
    split
    · refine ⟨(r.1 + 1, r.2 >>> 1), rfl, ?_⟩
      simp only []; rw [UInt32.toNat_add]; simp only [UInt32.toNat_one]; omega
    · exact ⟨(r.1, r.2), rfl, by simp⟩

theorem first_diff_ok {H : Heap} (diff : UInt64) (hd : diff ≠ 0) :
    Sat H (zng_first_diff_byte64 diff) (fun r H' => H' = H ∧ r.toNat ≤ 8) := by
  obtain ⟨n, e, hn⟩ := ctz64_le diff hd
  refine ⟨n / 8, H, by simp [zng_first_diff_byte64, e], rfl, ?_⟩
  rw [UInt32.toNat_div]; simp; omega

/-! ## `compare256_64_static` -/

/-- `do body while (cond)` over a changing heap, with a decreasing measure. -/
theorem sat_cdoWhile {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} (I : σ → Heap → Prop) (μ : σ → Nat)
    (Q : σ → Heap → Prop)
    (hstep : ∀ s H, I s H → Sat H (body s) (fun s1 H1 => Sat H1 (cond s1) (fun cs H2 =>
      (cs.1 = true → I cs.2 H2 ∧ μ cs.2 < μ s) ∧ (cs.1 = false → Q cs.2 H2))))
    {s : σ} {H : Heap} (hI : I s H) (hμ : μ s < fuel) : Sat H (cdoWhile body cond s) Q := by
  unfold cdoWhile
  suffices ∀ n s H, I s H → μ s < n → Sat H (cdoWhile.go body cond n s) Q from this _ s H hI hμ
  intro n
  induction n with
  | zero => intro s _ _ hlt; omega
  | succ n ih =>
    intro s H hI hlt
    obtain ⟨s1, H1, eb, ⟨c, s2⟩, H2, ec, ht, hf⟩ := hstep s H hI
    cases c with
    | false => exact ⟨s2, H2, by simp [cdoWhile.go, bind_app, eb, ec], hf rfl⟩
    | true =>
      obtain ⟨hI2, hμ2⟩ := ht rfl
      have hμ3 : μ s2 < μ s := hμ2
      obtain ⟨s', H', eg, q⟩ := ih s2 H2 hI2 (by omega)
      exact ⟨s', H', by simp [cdoWhile.go, bind_app, eb, ec, eg], q⟩

/-- The loop state of `compare256_64_static` at the start of trip `j`. -/
def cmpSt (r : BRef) (o0 o1 j : Nat) : BPtr × BPtr × UInt32 × Option UInt32 :=
  (.ref r (o0 + 16 * j), .ref r (o1 + 16 * j), (16 * j : Nat).toUInt32, none)

theorem u32_small (n : Nat) (h : n < 2 ^ 32) : (n.toUInt32).toNat = n := by
  simp [Nat.toUInt32]; omega

/-- `compare256_64_static(src0, src1)` with both pointers in the live byte object `a` and 256 bytes after each:
no fault, the heap unchanged, a result of at most 256. The bytes read are those of `[o0, o0 + 256)` and
`[o1, o1 + 256)`. -/
theorem compare256_ok {H : Heap} {r : BRef} {a : Array UInt8} {o0 o1 : Nat} (hb : Space.get H r = some a)
    (h0 : o0 + 256 ≤ a.size) (h1 : o1 + 256 ≤ a.size) :
    Sat H (compare256_64_static (.ref r o0) (.ref r o1)) (fun v H' => H' = H ∧ v.toNat ≤ 256) := by
  unfold compare256_64_static
  refine Sat.bind (Sat.mono (sat_cdoWhile
    (fun s H' => H' = H ∧ ∃ j, j < 16 ∧ s = cmpSt r o0 o1 j)
    (fun s => 256 - s.2.2.1.toNat)
    (fun s H' => H' = H ∧ ∀ v, s.2.2.2 = some v → v.toNat ≤ 256) ?_ ⟨rfl, 0, by decide, rfl⟩
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by unfold fuel; decide))) ?_)
  rotate_left
  · rintro ⟨_, _, _, r'⟩ H' ⟨rfl, hr⟩
    cases r' with
    | none => exact Sat.pure ⟨rfl, by decide⟩
    | some v => exact Sat.pure ⟨rfl, hr v rfl⟩
  rintro s H' ⟨rfl, j, hj, rfl⟩
  have hl : ((16 * j : Nat).toUInt32).toNat = 16 * j := u32_small _ (by omega)
  simp only [cmpSt]
  refine Sat.bind (Sat.mono (sat_memread8 hb (by omega)) ?_); rintro sv _ rfl
  refine Sat.bind (Sat.mono (sat_memread8 hb (by omega)) ?_); rintro mv _ rfl
  by_cases hd : (sv ^^^ mv != 0) = true
  · simp only [hd, ↓reduceIte]
    refine Sat.bind (Sat.mono (first_diff_ok _ (fun e => by simp [e] at hd)) ?_)
    rintro x _ ⟨rfl, hx⟩
    refine Sat.pure (Sat.pure ⟨fun e => by simp at e, fun _ => ⟨rfl, fun v ev => ?_⟩⟩)
    simp only [Option.some.injEq] at ev; subst ev
    rw [UInt32.toNat_add, hl]; omega
  · simp only [hd, Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.mono (sat_add hb (by omega) 8 (o0 + 16 * j + 8) (by omega) (by omega)) ?_)
    rintro _ _ ⟨rfl, rfl⟩
    refine Sat.bind (Sat.mono (sat_add hb (by omega) 8 (o1 + 16 * j + 8) (by omega) (by omega)) ?_)
    rintro _ _ ⟨rfl, rfl⟩
    refine Sat.bind (Sat.mono (sat_memread8 hb (by omega)) ?_); rintro sv2 _ rfl
    refine Sat.bind (Sat.mono (sat_memread8 hb (by omega)) ?_); rintro mv2 _ rfl
    have hl8 : ((16 * j : Nat).toUInt32 + 8).toNat = 16 * j + 8 := by rw [UInt32.toNat_add, hl]; simp; omega
    by_cases hd2 : (sv2 ^^^ mv2 != 0) = true
    · simp only [hd2, ↓reduceIte]
      refine Sat.bind (Sat.mono (first_diff_ok _ (fun e => by simp [e] at hd2)) ?_)
      rintro x _ ⟨rfl, hx⟩
      refine Sat.pure (Sat.pure ⟨fun e => by simp at e, fun _ => ⟨rfl, fun v ev => ?_⟩⟩)
      simp only [Option.some.injEq] at ev; subst ev
      rw [UInt32.toNat_add, hl8]; omega
    · simp only [hd2, Bool.false_eq_true, ↓reduceIte]
      refine Sat.bind (Sat.mono (sat_add hb (by omega) 8 (o0 + 16 * j + 16) (by omega) (by omega)) ?_)
      rintro _ _ ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (sat_add hb (by omega) 8 (o1 + 16 * j + 16) (by omega) (by omega)) ?_)
      rintro _ _ ⟨rfl, rfl⟩
      have hl16 : ((16 * j : Nat).toUInt32 + 8 + 8).toNat = 16 * (j + 1) := by
        rw [UInt32.toNat_add, hl8]; simp; omega
      refine Sat.pure (Sat.pure ⟨fun e => ?_, fun _ => ⟨rfl, fun v ev => by simp at ev⟩⟩)
      simp only [Option.isNone_none, Bool.true_and, decide_eq_true_eq] at e
      rw [UInt32.lt_iff_toNat_lt, hl16] at e
      have e' : 16 * (j + 1) < 256 := by simpa using e
      refine ⟨⟨rfl, j + 1, by omega, ?_⟩, ?_⟩
      · simp only [Prod.mk.injEq]
        refine ⟨by congr 1, by congr 1, UInt32.toNat_inj.mp (by rw [hl16, u32_small _ (by omega)]), trivial⟩
      · simp only []; rw [hl16, hl]; omega

/-- `compare256_c(src0, src1)`: see `compare256_ok`. -/
theorem compare256_c_ok {H : Heap} {r : BRef} {a : Array UInt8} {o0 o1 : Nat} (hb : Space.get H r = some a)
    (h0 : o0 + 256 ≤ a.size) (h1 : o1 + 256 ≤ a.size) :
    Sat H (compare256_c (.ref r o0) (.ref r o1)) (fun v H' => H' = H ∧ v.toNat ≤ 256) :=
  compare256_ok hb h0 h1

end ZlibNgF.Proof.Compare256
