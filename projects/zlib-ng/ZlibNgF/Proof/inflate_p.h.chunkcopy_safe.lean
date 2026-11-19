import ZlibNgF.Proof.«chunkset.copy»

/-!
# `chunkcopy_safe` of `inflate_p.h` (`ZlibNgF`)

Callers: `inflate_fast_safe_c` with `from = out - dist` (`dist ≥ 1`) and `safe` the end of the output, all in the
output buffer (`sat_chunkcopy_safe`); and, where the output is the window (`inflateBack`, patch 0007's `window ==
beg` branch, and `infback.c`'s `MATCH`), with `from` at or ahead of `out` in the window (`sat_chunkcopy_safe_ahead`).
The pointer comparisons are then between pointers of one object; the copy writes exactly `[out, out + MIN(len, safe -
out))`, with `memcpy` calls on non-overlapping ranges only, and returns `out + MIN(len, safe - out)`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.ChunkcopySafe
open C ZlibNg.InflateP ZlibNg.Zbuild
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem
open ZlibNgF.Proof.ChunkCopy (B u64_sub min_toNat u64_lt u64_le beq_B)

/-- The state of a copy loop of `chunkcopy_safe`: `j` bytes done, `T` to go, at `o + j` and `f + j`. -/
def CS (H0 : Heap) (ob N lo hi o f t : Nat) (x : BPtr × BPtr × UInt64) (G : Heap) : Prop :=
  ∃ j, x = (B ob (o + j), B ob (f + j), x.2.2) ∧ j + x.2.2.toNat = t ∧ ORun H0 G ob N lo hi

/-- `memcpy(out, from, c); out += c; from += c; tocopy -= c;` on non-overlapping ranges. -/
theorem cs_step {H0 G : Heap} {ob N lo hi o f t j : Nat} {T : UInt64} (rG : ORun H0 G ob N lo hi)
    (c : Nat) (ci : Int) (cu : UInt64) (hci : ci = c) (hcu : cu.toNat = c) (hjt : j + T.toNat = t)
    (hT : c ≤ T.toNat) (hd : f + t ≤ o) (h1 : lo ≤ o) (h2 : o + t ≤ hi) (hN : hi ≤ N) :
    Sat G (do
        Ptr.memcpy (B ob (o + j)) (B ob (f + j)) c
        pure (← (B ob (o + j)).add ci, ← (B ob (f + j)).add ci, T - cu))
      (fun x G2 => CS H0 ob N lo hi o f t x G2 ∧ x.2.2.toNat + c = T.toNat) := by
  refine Sat.bind (Sat.mono (rG.sat_memcpy c (od := o + j) (os := f + j) (by omega) (by omega) (by omega)
    (by omega) (by omega)) ?_)
  intro _ G1 r1
  obtain ⟨a1, ha1, ha1N⟩ := r1.cur
  have hg1 : Space.get G1 (BRef.heap ob) = some a1 := ha1
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) ci (o + (j + c)) (by rw [hci]; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) ci (f + (j + c)) (by rw [hci]; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  have e : (T - cu).toNat = T.toNat - c := by rw [u64_sub _ _ (by omega), hcu]
  exact Sat.pure ⟨⟨j + c, rfl, by simp only [e]; omega, r1⟩, by simp only [e]; omega⟩

/-- `cs_step` followed by a continuation. -/
theorem cs_step_k {H0 G : Heap} {ob N lo hi o f t j : Nat} {T : UInt64} (rG : ORun H0 G ob N lo hi)
    (c : Nat) (ci : Int) (cu : UInt64) (hci : ci = c) (hcu : cu.toNat = c) (hjt : j + T.toNat = t)
    (hT : c ≤ T.toNat) (hd : f + t ≤ o) (h1 : lo ≤ o) (h2 : o + t ≤ hi) (hN : hi ≤ N)
    {β : Type} (k : BPtr × BPtr × UInt64 → M β) (Q : β → Heap → Prop)
    (hk : ∀ x G', CS H0 ob N lo hi o f t x G' → x.2.2.toNat + c = T.toNat → Sat G' (k x) Q) :
    Sat G (do
        Ptr.memcpy (B ob (o + j)) (B ob (f + j)) c
        let a ← (B ob (o + j)).add ci
        let b ← (B ob (f + j)).add ci
        let x ← pure (a, b, T - cu)
        k x) Q := by
  refine Sat.bind (Sat.mono (rG.sat_memcpy c (od := o + j) (os := f + j) (by omega) (by omega) (by omega)
    (by omega) (by omega)) ?_)
  intro _ G1 r1
  obtain ⟨a1, ha1, ha1N⟩ := r1.cur
  have hg1 : Space.get G1 (BRef.heap ob) = some a1 := ha1
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) ci (o + (j + c)) (by rw [hci]; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) ci (f + (j + c)) (by rw [hci]; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  have e : (T - cu).toNat = T.toNat - c := by rw [u64_sub _ _ (by omega), hcu]
  exact Sat.bind (Sat.pure (hk _ _ ⟨j + c, rfl, by simp only [e]; omega, r1⟩ (by simp only [e]; omega)))

theorem sat_chunkcopy_safe {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {o f s : Nat}
    (len : UInt64) (hfo : f < o) (hos : o ≤ s) (h1 : lo ≤ o) (h2 : s ≤ hi) (hN : hi ≤ N) (hd63 : s - f < 2 ^ 63) :
    Sat H (chunkcopy_safe (B ob o) (B ob f) len (B ob s))
      (fun p H' => p = B ob (o + min len.toNat (s - o)) ∧ ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hg : Space.get H (BRef.heap ob) = some a := ha
  unfold chunkcopy_safe
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkCopy.sat_diff_r hg (o1 := s) (o2 := o) (by omega) (by omega) (by omega)) ?_)
  rintro d G ⟨rfl, hG⟩
  rw [hG]
  have hsl : (Int64.ofInt ((s : Int) - o)).toUInt64.toNat = s - o := by
    rw [toNat_ofInt_nonneg _ (by omega) (by omega)]; omega
  generalize (Int64.ofInt ((s : Int) - o)).toUInt64 = safelen at hsl ⊢
  have hm := min_toNat len safelen
  have hl : o + (MIN len safelen).toNat ≤ s := by omega
  -- olap_src
  refine Sat.bind (Sat.mono (P := fun (c : Bool) G => c = false ∧ G = H) ?_ ?_)
  · refine Sat.bind (Sat.mono (sat_le hg (o1 := o) (o2 := f) (by omega) (by omega)) ?_)
    rintro c G ⟨rfl, hG⟩
    rw [hG]
    have : decide (o ≤ f) = false := by simp; omega
    rw [this]; exact Sat.pure ⟨rfl, rfl⟩
  rintro src G ⟨rfl, hG⟩
  rw [hG]
  -- olap_dst
  refine Sat.bind (Sat.mono (P := fun (c : Bool) G => c = decide (o < f + (MIN len safelen).toNat) ∧ G = H) ?_ ?_)
  · refine Sat.bind (Sat.mono (sat_le hg (o1 := f) (o2 := o) (by omega) (by omega)) ?_)
    rintro c G ⟨rfl, hG⟩
    rw [hG]
    have : decide (f ≤ o) = true := by simp; omega
    rw [this]
    simp only [↓reduceIte]
    refine Sat.bind (Sat.mono (sat_add hg (by omega) _ (f + (MIN len safelen).toNat) (by simp) (by omega)) ?_)
    rintro p G ⟨rfl, hG⟩
    rw [hG]
    exact sat_lt hg (o1 := o) (o2 := f + (MIN len safelen).toNat) (by omega) (by omega)
  rintro dst G ⟨rfl, hG⟩
  rw [hG]
  simp only [Bool.false_or]
  by_cases hov : o < f + (MIN len safelen).toNat
  · have : decide (o < f + (MIN len safelen).toNat) = true := by simp; omega
    rw [this]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [beq_B ob o f (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkCopy.sat_diff_r hg (o1 := f) (o2 := o) (by omega) (by omega) (by omega)) ?_)
    rintro d G ⟨rfl, hG⟩
    rw [hG]
    have hnos := absI64 ((f : Int) - o) (by omega) (by omega)
    generalize (if Int64.ofInt ((f : Int) - o) < 0 then -Int64.ofInt ((f : Int) - o)
      else Int64.ofInt ((f : Int) - o)).toUInt64 = nos at hnos ⊢
    have hnos' : nos.toNat = o - f := by omega
    refine Sat.bind (Sat.mono (sat_cwhile (CS H0 ob N lo hi o f (MIN len safelen).toNat) (fun x => x.2.2.toNat)
      (fun x G => x.1 = B ob (o + (MIN len safelen).toNat) ∧ ORun H0 G ob N lo hi) ?_
      ⟨0, by simp, by simp, r⟩ (UInt64.toNat_lt _)) ?_)
    · rintro ⟨out, fr, L⟩ G ⟨k, hx, hk, rG⟩
      simp only [Prod.mk.injEq] at hx hk
      obtain ⟨rfl, rfl, -⟩ := hx
      refine ⟨_, _, rfl, fun hc => ?_, fun hc => ?_⟩
      · have hL : L.toNat ≠ 0 := by
          have : L ≠ 0 := by simpa using hc
          exact fun e => this (UInt64.toNat_inj.mp (by simpa using e))
        have htc := min_toNat nos L
        rw [hnos'] at htc
        have hsub : (L - MIN nos L).toNat = L.toNat - min (o - f) L.toNat := by
          rw [u64_sub _ _ (by omega), htc]
        simp only
        -- copies of 16 bytes
        refine Sat.bind (Sat.mono (sat_cwhile
          (CS H0 ob N lo hi (o + k) (f + k) (min (o - f) L.toNat)) (fun x => x.2.2.toNat)
          (fun x G => CS H0 ob N lo hi (o + k) (f + k) (min (o - f) L.toNat) x G ∧ x.2.2.toNat < 16) ?_
          ⟨0, by simp, by simp [htc], rG⟩ (UInt64.toNat_lt _)) ?_)
        · rintro ⟨out, fr, T⟩ G ⟨j, hx, hj, rG⟩
          simp only [Prod.mk.injEq] at hx hj
          obtain ⟨rfl, rfl, -⟩ := hx
          refine ⟨_, _, rfl, fun hc => ?_, fun hc => ?_⟩
          · have hT : 16 ≤ T.toNat := by
              have := of_decide_eq_true hc; rw [GE.ge, UInt64.le_iff_toNat_le] at this; simpa using this
            exact Sat.mono (cs_step rG 16 16 16 rfl rfl hj hT (by omega) (by omega) (by omega) hN)
              fun x G ⟨hx, hlt⟩ => ⟨hx, by simp only at hlt; show x.2.2.toNat < T.toNat; omega⟩
          · have hT : T.toNat < 16 := by
              have := of_decide_eq_false hc; rw [GE.ge, UInt64.le_iff_toNat_le] at this; simpa using this
            exact ⟨⟨j, rfl, hj, rG⟩, hT⟩
        rintro ⟨out, fr, T⟩ G ⟨⟨j, hx, hj, rG⟩, hT16⟩
        simp only [Prod.mk.injEq] at hx hj hT16
        obtain ⟨rfl, rfl, -⟩ := hx
        simp only
        have hbyte : ∀ (y : BPtr × BPtr × UInt64) (G : Heap),
            CS H0 ob N lo hi (o + k) (f + k) (min (o - f) L.toNat) y G →
            Sat G (do
              let z ← cwhile (fun x => pure (x.2.snd != 0, x.fst, x.2.fst, x.2.snd - 1))
                (fun x => do
                  let v ← load8 x.2.fst
                  Ptr.store x.fst v
                  let p1 ← Ptr.add x.fst 1
                  let p2 ← Ptr.add x.2.fst 1
                  pure (p1, p2, x.2.snd))
                (y.fst, y.2.fst, y.2.snd)
              pure (z.fst, z.2.fst, L - MIN nos L))
              (fun s2 G2 => CS H0 ob N lo hi o f (MIN len safelen).toNat s2 G2 ∧ s2.2.2.toNat < L.toNat) := by
          rintro ⟨out, fr, T⟩ G ⟨j, hx, hj, rG⟩
          simp only [Prod.mk.injEq] at hx hj
          obtain ⟨rfl, rfl, -⟩ := hx
          refine Sat.bind (Sat.mono (sat_cwhile
            (fun (x : BPtr × BPtr × UInt64) G => ∃ i, x = (B ob (o + k + i), B ob (f + k + i), x.2.2) ∧
              i + x.2.2.toNat = min (o - f) L.toNat ∧ ORun H0 G ob N lo hi)
            (fun x => x.2.2.toNat)
            (fun x G => x.1 = B ob (o + k + min (o - f) L.toNat) ∧ x.2.1 = B ob (f + k + min (o - f) L.toNat) ∧
              ORun H0 G ob N lo hi) ?_
            ⟨j, rfl, hj, rG⟩ (UInt64.toNat_lt _)) ?_)
          · rintro ⟨out, fr, T⟩ G ⟨i, hx, hi', rG⟩
            simp only [Prod.mk.injEq] at hx hi'
            obtain ⟨rfl, rfl, -⟩ := hx
            refine ⟨_, _, rfl, fun hc => ?_, fun hc => ?_⟩
            · have hT : T.toNat ≠ 0 := by
                have : T ≠ 0 := by simpa using hc
                exact fun e => this (UInt64.toNat_inj.mp (by simpa using e))
              have e1 : (T - 1).toNat = T.toNat - 1 := u64_sub _ _ (by simp; omega)
              obtain ⟨a2, ha2, ha2N⟩ := rG.cur
              have hg2 : Space.get G (BRef.heap ob) = some a2 := ha2
              refine Sat.bind (Sat.mono (sat_load hg2 (k := f + k + i) (by omega)) ?_); rintro v G1 hG1
              rw [hG1]
              refine Sat.bind (Sat.mono (rG.sat_store v (k := o + k + i) (by omega) (by omega) (by omega)) ?_)
              intro _ G1 r1
              obtain ⟨a3, ha3, ha3N⟩ := r1.cur
              have hg3 : Space.get G1 (BRef.heap ob) = some a3 := ha3
              refine Sat.bind (Sat.mono (sat_add hg3 (by omega) 1 (o + k + (i + 1)) (by simp; omega)
                (by omega)) ?_)
              rintro p G2 ⟨rfl, hG2⟩
              rw [hG2]
              refine Sat.bind (Sat.mono (sat_add hg3 (by omega) 1 (f + k + (i + 1)) (by simp; omega)
                (by omega)) ?_)
              rintro p G2 ⟨rfl, hG2⟩
              rw [hG2]
              exact Sat.pure ⟨⟨i + 1, rfl, by simp only [e1]; omega, r1⟩, by simp only [e1]; omega⟩
            · have hT : T.toNat = 0 := by
                have : T = 0 := by simpa using hc
                simp [this]
              exact ⟨by show B ob _ = B ob _; congr 1; omega, by show B ob _ = B ob _; congr 1; omega, rG⟩
          rintro ⟨out, fr, T⟩ G ⟨hx, hy, rG⟩
          simp only at hx hy
          subst hx hy
          refine Sat.pure ⟨⟨k + min (o - f) L.toNat, by simp [Nat.add_assoc], ?_, rG⟩, ?_⟩
          · show _ + (L - MIN nos L).toNat = _; omega
          · show (L - MIN nos L).toNat < L.toNat; omega
        have h4 : ∀ (x : BPtr × BPtr × UInt64) (G : Heap),
            CS H0 ob N lo hi (o + k) (f + k) (min (o - f) L.toNat) x G → x.2.2.toNat < 8 →
            Sat G (if x.2.snd ≥ 4 then do
                Ptr.memcpy x.fst x.2.fst 4
                let a ← x.fst.add 4
                let b ← x.2.fst.add 4
                let y ← pure (a, b, x.2.snd - 4)
                let z ← cwhile (fun x => pure (x.2.snd != 0, x.fst, x.2.fst, x.2.snd - 1))
                  (fun x => do
                    let v ← load8 x.2.fst
                    Ptr.store x.fst v
                    let p1 ← Ptr.add x.fst 1
                    let p2 ← Ptr.add x.2.fst 1
                    pure (p1, p2, x.2.snd))
                  (y.fst, y.2.fst, y.2.snd)
                pure (z.fst, z.2.fst, L - MIN nos L)
              else do
                let y ← pure (x.fst, x.2.fst, x.2.snd)
                let z ← cwhile (fun x => pure (x.2.snd != 0, x.fst, x.2.fst, x.2.snd - 1))
                  (fun x => do
                    let v ← load8 x.2.fst
                    Ptr.store x.fst v
                    let p1 ← Ptr.add x.fst 1
                    let p2 ← Ptr.add x.2.fst 1
                    pure (p1, p2, x.2.snd))
                  (y.fst, y.2.fst, y.2.snd)
                pure (z.fst, z.2.fst, L - MIN nos L))
              (fun s2 G2 => CS H0 ob N lo hi o f (MIN len safelen).toNat s2 G2 ∧ s2.2.2.toNat < L.toNat) := by
          rintro ⟨out, fr, T⟩ G ⟨j, hx, hj, rG⟩ hT8
          simp only [Prod.mk.injEq] at hx hj hT8
          obtain ⟨rfl, rfl, -⟩ := hx
          dsimp only
          split
          · rename_i hc
            have hT : 4 ≤ T.toNat := by rw [GE.ge, UInt64.le_iff_toNat_le] at hc; simpa using hc
            exact cs_step_k rG 4 4 4 rfl rfl hj hT (by omega) (by omega) (by omega) hN _ _
              fun y G hy _ => hbyte y G hy
          · exact Sat.bind (Sat.pure (hbyte _ G ⟨j, rfl, hj, rG⟩))
        split
        · rename_i hc
          have hT : 8 ≤ T.toNat := by rw [GE.ge, UInt64.le_iff_toNat_le] at hc; simpa using hc
          exact cs_step_k rG 8 8 8 rfl rfl hj hT (by omega) (by omega) (by omega) hN _ _
            fun y G hy hy8 => h4 y G hy (by omega)
        · rename_i hc
          have hT : T.toNat < 8 := by rw [GE.ge, UInt64.le_iff_toNat_le] at hc; simpa using hc
          first
            | exact h4 (B ob (o + k + j), B ob (f + k + j), T) G ⟨j, rfl, hj, rG⟩ hT
            | exact Sat.bind (Sat.pure (h4 (B ob (o + k + j), B ob (f + k + j), T) G ⟨j, rfl, hj, rG⟩ hT))
      · have hL : L.toNat = 0 := by
          have : L = 0 := by simpa using hc
          simp [this]
        exact ⟨by show B ob _ = B ob _; congr 1; omega, rG⟩
    rintro ⟨out, fr, L⟩ G ⟨hx, rG⟩
    simp only at hx
    exact Sat.pure ⟨by rw [hx, hm, hsl], rG⟩
  · have : decide (o < f + (MIN len safelen).toNat) = false := by simp; omega
    rw [this]
    simp only [Bool.not_false, ↓reduceIte]
    refine Sat.bind (Sat.mono (r.sat_memcpy (MIN len safelen).toNat (od := o) (os := f) h1 (by omega) (by omega) (by omega)
      (by omega)) ?_)
    intro _ G1 r1
    obtain ⟨a1, ha1, ha1N⟩ := r1.cur
    exact Sat.mono (sat_add (space_heap G1 ob ▸ ha1) (by omega) _ (o + (MIN len safelen).toNat) (by simp) (by omega))
      fun p G2 ⟨hp, hG⟩ => ⟨by rw [hp, hm, hsl], hG ▸ r1⟩

/-- `chunkcopy_safe(out, out - dist, len, safe)` alone: no fault, result `out + MIN(len, safe - out)`, only the bytes
`[out, out + MIN(len, safe - out))` of the output block change. -/
theorem chunkcopy_safe_safe {H : Heap} {ob N : Nat} {a : Array UInt8} (ha : H.bytes ob = some a)
    (hN : a.size = N) {o f s : Nat} (hd63 : s - f < 2 ^ 63) (len : UInt64) (hf : f < o) (hos : o ≤ s) (hs : s ≤ N) :
    Sat H (chunkcopy_safe (B ob o) (B ob f) len (B ob s))
      (fun p H' => p = B ob (o + min len.toNat (s - o)) ∧ ORun H H' ob N o s) :=
  sat_chunkcopy_safe (ORun.refl ha hN _ _) len hf hos (Nat.le_refl _) (Nat.le_refl _) hs hd63

/-- `memcpy(out, from, c); out += c; from += c; tocopy -= c;` on non-overlapping ranges, the source ahead of the destination. -/
theorem cs_stepA {H0 G : Heap} {ob N lo hi o f t j : Nat} {T : UInt64} (rG : ORun H0 G ob N lo hi)
    (c : Nat) (ci : Int) (cu : UInt64) (hci : ci = c) (hcu : cu.toNat = c) (hjt : j + T.toNat = t)
    (hT : c ≤ T.toNat) (hd : o + t ≤ f) (hfN : f + t ≤ N) (h1 : lo ≤ o) (h2 : o + t ≤ hi) (hN : hi ≤ N) :
    Sat G (do
        Ptr.memcpy (B ob (o + j)) (B ob (f + j)) c
        pure (← (B ob (o + j)).add ci, ← (B ob (f + j)).add ci, T - cu))
      (fun x G2 => CS H0 ob N lo hi o f t x G2 ∧ x.2.2.toNat + c = T.toNat) := by
  refine Sat.bind (Sat.mono (rG.sat_memcpy c (od := o + j) (os := f + j) (by omega) (by omega) (by omega)
    (by omega) (by omega)) ?_)
  intro _ G1 r1
  obtain ⟨a1, ha1, ha1N⟩ := r1.cur
  have hg1 : Space.get G1 (BRef.heap ob) = some a1 := ha1
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) ci (o + (j + c)) (by rw [hci]; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) ci (f + (j + c)) (by rw [hci]; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  have e : (T - cu).toNat = T.toNat - c := by rw [u64_sub _ _ (by omega), hcu]
  exact Sat.pure ⟨⟨j + c, rfl, by simp only [e]; omega, r1⟩, by simp only [e]; omega⟩

/-- `cs_stepA` followed by a continuation. -/
theorem cs_step_kA {H0 G : Heap} {ob N lo hi o f t j : Nat} {T : UInt64} (rG : ORun H0 G ob N lo hi)
    (c : Nat) (ci : Int) (cu : UInt64) (hci : ci = c) (hcu : cu.toNat = c) (hjt : j + T.toNat = t)
    (hT : c ≤ T.toNat) (hd : o + t ≤ f) (hfN : f + t ≤ N) (h1 : lo ≤ o) (h2 : o + t ≤ hi) (hN : hi ≤ N)
    {β : Type} (k : BPtr × BPtr × UInt64 → M β) (Q : β → Heap → Prop)
    (hk : ∀ x G', CS H0 ob N lo hi o f t x G' → x.2.2.toNat + c = T.toNat → Sat G' (k x) Q) :
    Sat G (do
        Ptr.memcpy (B ob (o + j)) (B ob (f + j)) c
        let a ← (B ob (o + j)).add ci
        let b ← (B ob (f + j)).add ci
        let x ← pure (a, b, T - cu)
        k x) Q := by
  refine Sat.bind (Sat.mono (rG.sat_memcpy c (od := o + j) (os := f + j) (by omega) (by omega) (by omega)
    (by omega) (by omega)) ?_)
  intro _ G1 r1
  obtain ⟨a1, ha1, ha1N⟩ := r1.cur
  have hg1 : Space.get G1 (BRef.heap ob) = some a1 := ha1
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) ci (o + (j + c)) (by rw [hci]; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) ci (f + (j + c)) (by rw [hci]; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  have e : (T - cu).toNat = T.toNat - c := by rw [u64_sub _ _ (by omega), hcu]
  exact Sat.bind (Sat.pure (hk _ _ ⟨j + c, rfl, by simp only [e]; omega, r1⟩ (by simp only [e]; omega)))


/-- `chunkcopy_safe(out, from, len, safe)` with `from` at or ahead of `out` in the same block (`inflateBack`'s window
copy, whose output is the window): no fault, result `out + MIN(len, safe - out)`, only `[out, safe)` changes. -/
theorem sat_chunkcopy_safe_ahead {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {o f s : Nat}
    (len : UInt64) (hof : o ≤ f) (hos : o ≤ s) (h1 : lo ≤ o) (h2 : s ≤ hi) (hN : hi ≤ N)
    (hfN : f + min len.toNat (s - o) ≤ N) (hN63 : N < 2 ^ 63) :
    Sat H (chunkcopy_safe (B ob o) (B ob f) len (B ob s))
      (fun p H' => p = B ob (o + min len.toNat (s - o)) ∧ ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hg : Space.get H (BRef.heap ob) = some a := ha
  unfold chunkcopy_safe
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkCopy.sat_diff_r hg (o1 := s) (o2 := o) (by omega) (by omega) (by omega)) ?_)
  rintro d G ⟨rfl, hG⟩
  rw [hG]
  have hsl : (Int64.ofInt ((s : Int) - o)).toUInt64.toNat = s - o := by
    rw [toNat_ofInt_nonneg _ (by omega) (by omega)]; omega
  generalize (Int64.ofInt ((s : Int) - o)).toUInt64 = safelen at hsl ⊢
  have hm := min_toNat len safelen
  have hl : o + (MIN len safelen).toNat ≤ s := by omega
  have hfl : f + (MIN len safelen).toNat ≤ N := by omega
  -- olap_src
  refine Sat.bind (Sat.mono (P := fun (c : Bool) G => c = decide (f < o + (MIN len safelen).toNat) ∧ G = H) ?_ ?_)
  · refine Sat.bind (Sat.mono (sat_le hg (o1 := o) (o2 := f) (by omega) (by omega)) ?_)
    rintro c G ⟨rfl, hG⟩
    rw [hG]
    have : decide (o ≤ f) = true := by simp; omega
    rw [this]
    simp only [↓reduceIte]
    refine Sat.bind (Sat.mono (sat_add hg (by omega) _ (o + (MIN len safelen).toNat) (by simp) (by omega)) ?_)
    rintro p G ⟨rfl, hG⟩
    rw [hG]
    exact sat_lt hg (o1 := f) (o2 := o + (MIN len safelen).toNat) (by omega) (by omega)
  rintro src G ⟨rfl, hG⟩
  rw [hG]
  by_cases hfo : f = o
  · subst hfo
    -- olap_dst
    refine Sat.bind (Sat.mono (P := fun (c : Bool) G => c = decide (f < f + (MIN len safelen).toNat) ∧ G = H) ?_ ?_)
    · refine Sat.bind (Sat.mono (sat_le hg (o1 := f) (o2 := f) (by omega) (by omega)) ?_)
      rintro c G ⟨rfl, hG⟩
      rw [hG]
      have : decide (f ≤ f) = true := by simp
      rw [this]
      simp only [↓reduceIte]
      refine Sat.bind (Sat.mono (sat_add hg (by omega) _ (f + (MIN len safelen).toNat) (by simp) (by omega)) ?_)
      rintro p G ⟨rfl, hG⟩
      rw [hG]
      exact sat_lt hg (o1 := f) (o2 := f + (MIN len safelen).toNat) (by omega) (by omega)
    rintro dst G ⟨rfl, hG⟩
    rw [hG]
    by_cases hL0 : (MIN len safelen).toNat = 0
    · have : decide (f < f + (MIN len safelen).toNat) = false := by simp; omega
      rw [this]
      simp only [Bool.or_false, Bool.not_false, ↓reduceIte]
      refine Sat.bind (Sat.mono (r.sat_memcpy (MIN len safelen).toNat (od := f) (os := f) h1 (by omega) (by omega)
        (by omega) (by omega)) ?_)
      intro _ G1 r1
      obtain ⟨a1, ha1, ha1N⟩ := r1.cur
      exact Sat.mono (sat_add (space_heap G1 ob ▸ ha1) (by omega) _ (f + (MIN len safelen).toNat) (by simp)
        (by omega)) fun p G2 ⟨hp, hG⟩ => ⟨by rw [hp, hm, hsl], hG ▸ r1⟩
    · have : decide (f < f + (MIN len safelen).toNat) = true := by simp; omega
      rw [this]
      simp only [Bool.or_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
      exact Sat.mono (sat_add hg (by omega) _ (f + (MIN len safelen).toNat) (by simp) (by omega))
        fun p G2 ⟨hp, hG⟩ => ⟨by rw [hp, hm, hsl], hG ▸ r⟩
  -- f > o: olap_dst is false
  refine Sat.bind (Sat.mono (P := fun (c : Bool) G => c = false ∧ G = H) ?_ ?_)
  · refine Sat.bind (Sat.mono (sat_le hg (o1 := f) (o2 := o) (by omega) (by omega)) ?_)
    rintro c G ⟨rfl, hG⟩
    rw [hG]
    have : decide (f ≤ o) = false := by simp; omega
    rw [this]; exact Sat.pure ⟨rfl, rfl⟩
  rintro dst G ⟨rfl, hG⟩
  rw [hG]
  simp only [Bool.or_false]
  by_cases hov : f < o + (MIN len safelen).toNat
  · have : decide (f < o + (MIN len safelen).toNat) = true := by simp; omega
    rw [this]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [beq_B ob o f hfo]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.ChunkCopy.sat_diff_r hg (o1 := f) (o2 := o) (by omega) (by omega) (by omega)) ?_)
    rintro d G ⟨rfl, hG⟩
    rw [hG]
    have hnos := absI64 ((f : Int) - o) (by omega) (by omega)
    generalize (if Int64.ofInt ((f : Int) - o) < 0 then -Int64.ofInt ((f : Int) - o)
      else Int64.ofInt ((f : Int) - o)).toUInt64 = nos at hnos ⊢
    have hnos' : nos.toNat = f - o := by omega
    refine Sat.bind (Sat.mono (sat_cwhile (CS H0 ob N lo hi o f (MIN len safelen).toNat) (fun x => x.2.2.toNat)
      (fun x G => x.1 = B ob (o + (MIN len safelen).toNat) ∧ ORun H0 G ob N lo hi) ?_
      ⟨0, by simp, by simp, r⟩ (UInt64.toNat_lt _)) ?_)
    · rintro ⟨out, fr, L⟩ G ⟨k, hx, hk, rG⟩
      simp only [Prod.mk.injEq] at hx hk
      obtain ⟨rfl, rfl, -⟩ := hx
      refine ⟨_, _, rfl, fun hc => ?_, fun hc => ?_⟩
      · have hL : L.toNat ≠ 0 := by
          have : L ≠ 0 := by simpa using hc
          exact fun e => this (UInt64.toNat_inj.mp (by simpa using e))
        have htc := min_toNat nos L
        rw [hnos'] at htc
        have hsub : (L - MIN nos L).toNat = L.toNat - min (f - o) L.toNat := by
          rw [u64_sub _ _ (by omega), htc]
        simp only
        -- copies of 16 bytes
        refine Sat.bind (Sat.mono (sat_cwhile
          (CS H0 ob N lo hi (o + k) (f + k) (min (f - o) L.toNat)) (fun x => x.2.2.toNat)
          (fun x G => CS H0 ob N lo hi (o + k) (f + k) (min (f - o) L.toNat) x G ∧ x.2.2.toNat < 16) ?_
          ⟨0, by simp, by simp [htc], rG⟩ (UInt64.toNat_lt _)) ?_)
        · rintro ⟨out, fr, T⟩ G ⟨j, hx, hj, rG⟩
          simp only [Prod.mk.injEq] at hx hj
          obtain ⟨rfl, rfl, -⟩ := hx
          refine ⟨_, _, rfl, fun hc => ?_, fun hc => ?_⟩
          · have hT : 16 ≤ T.toNat := by
              have := of_decide_eq_true hc; rw [GE.ge, UInt64.le_iff_toNat_le] at this; simpa using this
            exact Sat.mono (cs_stepA rG 16 16 16 rfl rfl hj hT (by omega) (by omega) (by omega) (by omega) hN)
              fun x G ⟨hx, hlt⟩ => ⟨hx, by simp only at hlt; show x.2.2.toNat < T.toNat; omega⟩
          · have hT : T.toNat < 16 := by
              have := of_decide_eq_false hc; rw [GE.ge, UInt64.le_iff_toNat_le] at this; simpa using this
            exact ⟨⟨j, rfl, hj, rG⟩, hT⟩
        rintro ⟨out, fr, T⟩ G ⟨⟨j, hx, hj, rG⟩, hT16⟩
        simp only [Prod.mk.injEq] at hx hj hT16
        obtain ⟨rfl, rfl, -⟩ := hx
        simp only
        have hbyte : ∀ (y : BPtr × BPtr × UInt64) (G : Heap),
            CS H0 ob N lo hi (o + k) (f + k) (min (f - o) L.toNat) y G →
            Sat G (do
              let z ← cwhile (fun x => pure (x.2.snd != 0, x.fst, x.2.fst, x.2.snd - 1))
                (fun x => do
                  let v ← load8 x.2.fst
                  Ptr.store x.fst v
                  let p1 ← Ptr.add x.fst 1
                  let p2 ← Ptr.add x.2.fst 1
                  pure (p1, p2, x.2.snd))
                (y.fst, y.2.fst, y.2.snd)
              pure (z.fst, z.2.fst, L - MIN nos L))
              (fun s2 G2 => CS H0 ob N lo hi o f (MIN len safelen).toNat s2 G2 ∧ s2.2.2.toNat < L.toNat) := by
          rintro ⟨out, fr, T⟩ G ⟨j, hx, hj, rG⟩
          simp only [Prod.mk.injEq] at hx hj
          obtain ⟨rfl, rfl, -⟩ := hx
          refine Sat.bind (Sat.mono (sat_cwhile
            (fun (x : BPtr × BPtr × UInt64) G => ∃ i, x = (B ob (o + k + i), B ob (f + k + i), x.2.2) ∧
              i + x.2.2.toNat = min (f - o) L.toNat ∧ ORun H0 G ob N lo hi)
            (fun x => x.2.2.toNat)
            (fun x G => x.1 = B ob (o + k + min (f - o) L.toNat) ∧ x.2.1 = B ob (f + k + min (f - o) L.toNat) ∧
              ORun H0 G ob N lo hi) ?_
            ⟨j, rfl, hj, rG⟩ (UInt64.toNat_lt _)) ?_)
          · rintro ⟨out, fr, T⟩ G ⟨i, hx, hi', rG⟩
            simp only [Prod.mk.injEq] at hx hi'
            obtain ⟨rfl, rfl, -⟩ := hx
            refine ⟨_, _, rfl, fun hc => ?_, fun hc => ?_⟩
            · have hT : T.toNat ≠ 0 := by
                have : T ≠ 0 := by simpa using hc
                exact fun e => this (UInt64.toNat_inj.mp (by simpa using e))
              have e1 : (T - 1).toNat = T.toNat - 1 := u64_sub _ _ (by simp; omega)
              obtain ⟨a2, ha2, ha2N⟩ := rG.cur
              have hg2 : Space.get G (BRef.heap ob) = some a2 := ha2
              refine Sat.bind (Sat.mono (sat_load hg2 (k := f + k + i) (by omega)) ?_); rintro v G1 hG1
              rw [hG1]
              refine Sat.bind (Sat.mono (rG.sat_store v (k := o + k + i) (by omega) (by omega) (by omega)) ?_)
              intro _ G1 r1
              obtain ⟨a3, ha3, ha3N⟩ := r1.cur
              have hg3 : Space.get G1 (BRef.heap ob) = some a3 := ha3
              refine Sat.bind (Sat.mono (sat_add hg3 (by omega) 1 (o + k + (i + 1)) (by simp; omega)
                (by omega)) ?_)
              rintro p G2 ⟨rfl, hG2⟩
              rw [hG2]
              refine Sat.bind (Sat.mono (sat_add hg3 (by omega) 1 (f + k + (i + 1)) (by simp; omega)
                (by omega)) ?_)
              rintro p G2 ⟨rfl, hG2⟩
              rw [hG2]
              exact Sat.pure ⟨⟨i + 1, rfl, by simp only [e1]; omega, r1⟩, by simp only [e1]; omega⟩
            · have hT : T.toNat = 0 := by
                have : T = 0 := by simpa using hc
                simp [this]
              exact ⟨by show B ob _ = B ob _; congr 1; omega, by show B ob _ = B ob _; congr 1; omega, rG⟩
          rintro ⟨out, fr, T⟩ G ⟨hx, hy, rG⟩
          simp only at hx hy
          subst hx hy
          refine Sat.pure ⟨⟨k + min (f - o) L.toNat, by simp [Nat.add_assoc], ?_, rG⟩, ?_⟩
          · show _ + (L - MIN nos L).toNat = _; omega
          · show (L - MIN nos L).toNat < L.toNat; omega
        have h4 : ∀ (x : BPtr × BPtr × UInt64) (G : Heap),
            CS H0 ob N lo hi (o + k) (f + k) (min (f - o) L.toNat) x G → x.2.2.toNat < 8 →
            Sat G (if x.2.snd ≥ 4 then do
                Ptr.memcpy x.fst x.2.fst 4
                let a ← x.fst.add 4
                let b ← x.2.fst.add 4
                let y ← pure (a, b, x.2.snd - 4)
                let z ← cwhile (fun x => pure (x.2.snd != 0, x.fst, x.2.fst, x.2.snd - 1))
                  (fun x => do
                    let v ← load8 x.2.fst
                    Ptr.store x.fst v
                    let p1 ← Ptr.add x.fst 1
                    let p2 ← Ptr.add x.2.fst 1
                    pure (p1, p2, x.2.snd))
                  (y.fst, y.2.fst, y.2.snd)
                pure (z.fst, z.2.fst, L - MIN nos L)
              else do
                let y ← pure (x.fst, x.2.fst, x.2.snd)
                let z ← cwhile (fun x => pure (x.2.snd != 0, x.fst, x.2.fst, x.2.snd - 1))
                  (fun x => do
                    let v ← load8 x.2.fst
                    Ptr.store x.fst v
                    let p1 ← Ptr.add x.fst 1
                    let p2 ← Ptr.add x.2.fst 1
                    pure (p1, p2, x.2.snd))
                  (y.fst, y.2.fst, y.2.snd)
                pure (z.fst, z.2.fst, L - MIN nos L))
              (fun s2 G2 => CS H0 ob N lo hi o f (MIN len safelen).toNat s2 G2 ∧ s2.2.2.toNat < L.toNat) := by
          rintro ⟨out, fr, T⟩ G ⟨j, hx, hj, rG⟩ hT8
          simp only [Prod.mk.injEq] at hx hj hT8
          obtain ⟨rfl, rfl, -⟩ := hx
          dsimp only
          split
          · rename_i hc
            have hT : 4 ≤ T.toNat := by rw [GE.ge, UInt64.le_iff_toNat_le] at hc; simpa using hc
            exact cs_step_kA rG 4 4 4 rfl rfl hj hT (by omega) (by omega) (by omega) (by omega) hN _ _
              fun y G hy _ => hbyte y G hy
          · exact Sat.bind (Sat.pure (hbyte _ G ⟨j, rfl, hj, rG⟩))
        split
        · rename_i hc
          have hT : 8 ≤ T.toNat := by rw [GE.ge, UInt64.le_iff_toNat_le] at hc; simpa using hc
          exact cs_step_kA rG 8 8 8 rfl rfl hj hT (by omega) (by omega) (by omega) (by omega) hN _ _
            fun y G hy hy8 => h4 y G hy (by omega)
        · rename_i hc
          have hT : T.toNat < 8 := by rw [GE.ge, UInt64.le_iff_toNat_le] at hc; simpa using hc
          first
            | exact h4 (B ob (o + k + j), B ob (f + k + j), T) G ⟨j, rfl, hj, rG⟩ hT
            | exact Sat.bind (Sat.pure (h4 (B ob (o + k + j), B ob (f + k + j), T) G ⟨j, rfl, hj, rG⟩ hT))
      · have hL : L.toNat = 0 := by
          have : L = 0 := by simpa using hc
          simp [this]
        exact ⟨by show B ob _ = B ob _; congr 1; omega, rG⟩
    rintro ⟨out, fr, L⟩ G ⟨hx, rG⟩
    simp only at hx
    exact Sat.pure ⟨by rw [hx, hm, hsl], rG⟩
  · have : decide (f < o + (MIN len safelen).toNat) = false := by simp; omega
    rw [this]
    simp only [Bool.not_false, ↓reduceIte]
    refine Sat.bind (Sat.mono (r.sat_memcpy (MIN len safelen).toNat (od := o) (os := f) h1 (by omega) (by omega) (by omega)
      (by omega)) ?_)
    intro _ G1 r1
    obtain ⟨a1, ha1, ha1N⟩ := r1.cur
    exact Sat.mono (sat_add (space_heap G1 ob ▸ ha1) (by omega) _ (o + (MIN len safelen).toNat) (by simp) (by omega))
      fun p G2 ⟨hp, hG⟩ => ⟨by rw [hp, hm, hsl], hG ▸ r1⟩

end ZlibNgF.Proof.ChunkcopySafe
