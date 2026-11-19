import ZlibNgF.Proof.«chunkset.mem»

/-!
# Chunk copies of `chunkset_tpl.h` (`ZlibNgF`)

Safety of `CHUNKCOPY` (`chunkcopy_c`), `CHUNKUNROLL`, `GET_CHUNK_MAG`, `CHUNKMEMSET` (`chunkmemset_c`),
`CHUNKMEMSET_SAFE` (`chunkmemset_safe_c`) and `CHUNKCOPY_SAFE` as instantiated by `arch/generic/chunkset_c.c`
(8-byte `chunk_t`). Every call site (`inflate_fast_c`, `inflate`'s `MATCH` state) passes an output pointer `out`
and a source `from = out - dist` with `dist ≥ 1` in the same object, the caller's output buffer, a heap block
`ob` of `N` bytes (`N < 2 ^ 63` where a difference other than `out - from` is computed); the lemmas are stated for that
case. Each lemma takes a run `ORun H0 H ob N lo hi` and
the fact that the bytes the routine may write lie in `[lo, hi)`, and returns the result pointer and the run
extended by the call, so that the lemmas compose.

Bytes written (`o` the offset of `out`, `len` the length, after `MIN` with the room where the routine clamps):
* `CHUNKCOPY`: `[o, o + max len 8)` (an 8-byte store even for a short copy); reads `[f, f + max len 8)`.
* `CHUNKUNROLL`: `[o, o + len + 6)` (8-byte stores at offsets below `o + len - 1`).
* `CHUNKMEMSET`: `[o, o + max len 8)`.
* `CHUNKMEMSET_SAFE`: `[o, o + left)`; with `left < 8` exactly `[o, o + MIN len left)`.
* `CHUNKCOPY_SAFE`: `[o, safe)`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.ChunkCopy
open C ZlibNg.Chunkset ZlibNg.Zbuild
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem

/-- `p` designates offset `k` of heap block `ob`. -/
abbrev B (ob k : Nat) : BPtr := Ptr.ref (BRef.heap ob) k

theorem align_toNat (len : UInt64) (h : 1 ≤ len.toNat) :
    (((len - 1) % CHUNK) + 1).toNat = (len.toNat - 1) % 8 + 1 := by
  have e1 : (len - 1).toNat = len.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using h)
  unfold CHUNK
  rw [UInt64.toNat_add, UInt64.toNat_mod, e1]
  simp only [UInt64.reduceToNat]
  omega

theorem cast_add (o k : Nat) : (o : Int) + Int.ofNat k = ((o + k : Nat) : Int) := by simp

/-! ## `CHUNKCOPY` -/

theorem sat_CHUNKCOPY {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {o f : Nat} (len : UInt64)
    (hlen : 1 ≤ len.toNat) (h1 : lo ≤ o) (h2 : o + max len.toNat 8 ≤ hi) (hN : o + max len.toNat 8 ≤ N)
    (hf : f + max len.toNat 8 ≤ N) :
    Sat H (CHUNKCOPY (B ob o) (B ob f) len) (fun p H' => p = B ob (o + len.toNat) ∧ ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have m1 := Nat.le_max_left len.toNat 8
  have m2 := Nat.le_max_right len.toNat 8
  have hal := align_toNat len hlen
  have hal8 : (len.toNat - 1) % 8 + 1 ≤ 8 := by omega
  have hall : (len.toNat - 1) % 8 + 1 ≤ len.toNat := by omega
  unfold CHUNKCOPY loadchunk storechunk
  refine Sat.bind (Sat.mono (sat_memread8 (space_heap H ob ▸ ha) (by omega)) ?_); rintro _ H1 rfl
  refine Sat.bind (Sat.mono (r.sat_memwrite8 _ h1 (by omega) (by omega)) ?_); intro _ H1 r1
  obtain ⟨a1, ha1, ha1N⟩ := r1.cur
  have hg1 : Space.get H1 (BRef.heap ob) = some a1 := ha1
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) _ (o + ((len.toNat - 1) % 8 + 1))
    (by rw [hal, cast_add]) (by omega)) ?_)
  rintro p H2 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) _ (f + ((len.toNat - 1) % 8 + 1))
    (by rw [hal, cast_add]) (by omega)) ?_)
  rintro p H2 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_cwhile
    (fun (s : BPtr × BPtr × UInt64) (G : Heap) => ∃ m, s.1 = B ob (o + len.toNat - m) ∧
      s.2.1 = B ob (f + len.toNat - m) ∧ s.2.2.toNat = m ∧ m % 8 = 0 ∧ m + ((len.toNat - 1) % 8 + 1) ≤ len.toNat ∧
      ORun H0 G ob N lo hi)
    (fun s => s.2.2.toNat)
    (fun s G => s.1 = B ob (o + len.toNat) ∧ ORun H0 G ob N lo hi) ?_ ?_ ?_) ?_)
  · rintro ⟨out, fr, l⟩ G ⟨m, rfl, rfl, hm, hm8, hml, rG⟩
    simp only at hm
    refine ⟨_, _, rfl, ?_, ?_⟩
    · intro hc
      have hc' : 0 < m := by
        have := UInt64.lt_iff_toNat_lt.mp (by simpa using hc); simp at this; omega
      obtain ⟨aG, haG, haGN⟩ := rG.cur
      have hgG : Space.get G (BRef.heap ob) = some aG := haG
      refine Sat.bind (Sat.mono (sat_memread8 hgG (by omega)) ?_); rintro _ G1 rfl
      refine Sat.bind (Sat.mono (rG.sat_memwrite8 _ (by omega) (by omega) (by omega)) ?_); intro _ G1 r2
      obtain ⟨a2, ha2, ha2N⟩ := r2.cur
      have hg2 : Space.get G1 (BRef.heap ob) = some a2 := ha2
      refine Sat.bind (Sat.mono (sat_add hg2 (by omega) 8 (o + len.toNat - m + 8) (by omega) (by omega)) ?_)
      rintro p G2 ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (sat_add hg2 (by omega) 8 (f + len.toNat - m + 8) (by omega) (by omega)) ?_)
      rintro p G2 ⟨rfl, rfl⟩
      refine Sat.pure ⟨⟨m - 8, ?_, ?_, ?_, by omega, by omega, r2⟩, ?_⟩
      · show B ob _ = B ob _; congr 1; omega
      · show B ob _ = B ob _; congr 1; omega
      · show (l - CHUNK).toNat = m - 8
        rw [UInt64.toNat_sub_of_le] <;> simp only [CHUNK, UInt64.le_iff_toNat_le] <;> simp <;> omega
      · show (l - CHUNK).toNat < l.toNat
        rw [UInt64.toNat_sub_of_le] <;> simp only [CHUNK, UInt64.le_iff_toNat_le] <;> simp <;> omega
    · intro hc
      have hc' : m = 0 := by
        have : ¬ 0 < l := by simpa using hc
        rw [UInt64.lt_iff_toNat_lt] at this; simp at this; omega
      subst hc'
      exact ⟨by simp, rG⟩
  · refine ⟨len.toNat - ((len.toNat - 1) % 8 + 1), ?_, ?_, ?_, ?_, ?_, r1⟩
    · show B ob _ = B ob _; congr 1; omega
    · show B ob _ = B ob _; congr 1; omega
    · rw [UInt64.toNat_sub_of_le, hal]; rw [UInt64.le_iff_toNat_le, hal]; omega
    · omega
    · omega
  · exact UInt64.toNat_lt _
  · rintro ⟨out, fr, l⟩ G ⟨rfl, rG⟩
    exact Sat.pure ⟨rfl, rG⟩

/-! ## `CHUNKUNROLL` -/

/-- `CHUNKUNROLL(out, &dist, &len)` with `from = out - dist` in the same block: 8-byte stores at offsets below
`o + len - 1`. It returns `(out', dist', len')` with `out' - dist' = out - dist`, `out' + len' = out + len`, and on exit
`dist' ≥ len'` or `dist' ≥ 8`. -/
theorem sat_CHUNKUNROLL {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {o : Nat} (dist len : UInt32)
    (hd1 : 1 ≤ dist.toNat) (hdo : dist.toNat ≤ o) (h1 : lo ≤ o)
    (h2 : dist.toNat < 8 → o + min (len.toNat + 6) 14 ≤ hi) (hN : hi ≤ N) (hoN : o + len.toNat ≤ N) :
    Sat H (CHUNKUNROLL (B ob o) dist len) (fun res H' =>
      ∃ L D : UInt32, res = (B ob (o + len.toNat - L.toNat), D, L) ∧ L.toNat ≤ len.toNat ∧
        D.toNat = dist.toNat + (len.toNat - L.toNat) ∧ (1 ≤ len.toNat → 1 ≤ L.toNat) ∧
        (L.toNat ≤ D.toNat ∨ 8 ≤ D.toNat) ∧ ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hg : Space.get H (BRef.heap ob) = some a := ha
  unfold CHUNKUNROLL loadchunk storechunk
  refine Sat.bind (Sat.mono (sat_add hg (by omega) _ (o - dist.toNat) (by simp; omega) (by omega)) ?_)
  rintro p H1 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_cwhile
    (fun (s : BPtr × UInt32 × UInt32) (G : Heap) => s.1 = B ob (o + len.toNat - s.2.2.toNat) ∧
      s.2.2.toNat ≤ len.toNat ∧ s.2.1.toNat = dist.toNat + (len.toNat - s.2.2.toNat) ∧
      (1 ≤ len.toNat → 1 ≤ s.2.2.toNat) ∧ ORun H0 G ob N lo hi)
    (fun s => s.2.2.toNat)
    (fun s G => ∃ L D : UInt32, s = (B ob (o + len.toNat - L.toNat), D, L) ∧ L.toNat ≤ len.toNat ∧
        D.toNat = dist.toNat + (len.toNat - L.toNat) ∧ (1 ≤ len.toNat → 1 ≤ L.toNat) ∧
        (L.toNat ≤ D.toNat ∨ 8 ≤ D.toNat) ∧ ORun H0 G ob N lo hi)
    ?_ ?_ ?_) ?_)
  · rintro ⟨out, D, L⟩ G ⟨hp, hL, hD, hL1, rG⟩
    simp only at hp hL hD hL1
    subst hp
    refine ⟨_, _, rfl, ?_, ?_⟩
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, CHUNK] at hc
      obtain ⟨hc1, hc2⟩ := hc
      rw [UInt32.lt_iff_toNat_lt] at hc1
      have hc2' : D.toNat < 8 := by
        have := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hc2); simpa using this
      have h2' := h2 (by omega)
      have := Nat.min_le_left (len.toNat + 6) 14
      have := Nat.min_le_right (len.toNat + 6) 14
      have hP : o + len.toNat - L.toNat + 8 ≤ o + min (len.toNat + 6) 14 := by
        rw [Nat.min_def]; split <;> omega
      obtain ⟨aG, haG, haGN⟩ := rG.cur
      have hgG : Space.get G (BRef.heap ob) = some aG := haG
      refine Sat.bind (Sat.mono (sat_memread8 hgG (by omega)) ?_); rintro _ G1 rfl
      refine Sat.bind (Sat.mono (rG.sat_memwrite8 _ (by omega) (by omega) (by omega)) ?_); intro _ G1 r2
      obtain ⟨a2, ha2, ha2N⟩ := r2.cur
      have hg2 : Space.get G1 (BRef.heap ob) = some a2 := ha2
      refine Sat.bind (Sat.mono (sat_add hg2 (by omega) _ (o + len.toNat - L.toNat + D.toNat)
        (by simp) (by omega)) ?_)
      rintro p G2 ⟨rfl, rfl⟩
      have e1 : (D + D).toNat = D.toNat + D.toNat := by
        rw [UInt32.toNat_add]; omega
      have e2 : (L - D).toNat = L.toNat - D.toNat :=
        UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
      refine Sat.pure ⟨⟨?_, ?_, ?_, ?_, r2⟩, ?_⟩
      · show B ob _ = B ob _; simp only [e2]; congr 1; omega
      · show (L - D).toNat ≤ _; omega
      · show (D + D).toNat = _ + (_ - (L - D).toNat); omega
      · show _ → 1 ≤ (L - D).toNat; omega
      · show (L - D).toNat < L.toNat; omega
    · intro hc
      refine ⟨L, D, rfl, hL, hD, hL1, ?_, rG⟩
      rcases Bool.and_eq_false_iff.mp hc with hc | hc
      · left; have := of_decide_eq_false hc; rw [UInt32.lt_iff_toNat_lt] at this; omega
      · right; have := of_decide_eq_false hc; simp only [CHUNK] at this
        rw [UInt64.lt_iff_toNat_lt] at this; simp at this; omega
  · refine ⟨?_, Nat.le_refl _, by simp, id, r⟩
    show B ob _ = B ob _; simp only; congr 1; omega
  · exact Nat.lt_of_lt_of_le (UInt32.toNat_lt _) (by unfold fuel; decide)
  · rintro ⟨out, D, L⟩ G hQ
    exact Sat.pure hQ

/-! ## `GET_CHUNK_MAG` -/

theorem sat_GET_CHUNK_MAG {H : Heap} {ob f : Nat} {a : Array UInt8} (hg : Space.get H (BRef.heap ob) = some a)
    (rem0 dist : UInt64) (hd1 : 1 ≤ dist.toNat) (hrem : rem0.toNat ≤ dist.toNat) (hf : f + dist.toNat ≤ a.size) :
    Sat H (GET_CHUNK_MAG (B ob f) rem0 dist) (fun res H' => H' = H ∧ res.2.toNat ≤ dist.toNat) := by
  unfold GET_CHUNK_MAG
  refine Sat.bind (Sat.mono (sat_cwhile
    (fun (s : UInt64 × UInt64 × UInt64 × UInt64) (G : Heap) => G = H ∧ s.2.2.2.toNat ≤ dist.toNat)
    (fun s => s.2.1.toNat)
    (fun s G => G = H ∧ s.2.2.2.toNat ≤ dist.toNat) ?_ ⟨rfl, hrem⟩ (UInt64.toNat_lt _)) ?_)
  · rintro ⟨c, br, cur, rem⟩ G ⟨hG, hr⟩
    rw [hG]
    refine ⟨_, _, rfl, ?_, ?_⟩
    · intro hc
      have hbr : br ≠ 0 := by simpa using hc
      have hbr' : br.toNat ≠ 0 := fun e => hbr (UInt64.toNat_inj.mp (by simpa using e))
      have hmin : (MIN dist br).toNat = min dist.toNat br.toNat := by
        unfold MIN; split
        · rename_i h; rw [GT.gt, UInt64.lt_iff_toNat_lt] at h; omega
        · rename_i h; rw [GT.gt, UInt64.lt_iff_toNat_lt] at h; omega
      refine Sat.bind (Sat.mono (sat_cwhile
        (fun (t : UInt64 × UInt64) (G : Heap) => G = H ∧ t.2.toNat ≤ (MIN dist br).toNat)
        (fun t => (MIN dist br).toNat - t.2.toNat)
        (fun _ G => G = H) ?_ ⟨rfl, by simp⟩ (by have := UInt64.toNat_lt (MIN dist br); unfold fuel; omega)) ?_)
      · rintro ⟨c', i⟩ G ⟨hG, hi⟩
        rw [hG]
        simp only at hi
        refine ⟨_, _, rfl, ?_, ?_⟩
        · intro hc'
          have hi' : i.toNat < (MIN dist br).toNat := by
            have := of_decide_eq_true hc'; rwa [UInt64.lt_iff_toNat_lt] at this
          refine Sat.bind (Sat.mono (sat_index8 hg i.toNat (by omega)) ?_)
          rintro _ G rfl
          refine Sat.pure ⟨⟨rfl, ?_⟩, ?_⟩
          · show (i + 1).toNat ≤ _; rw [UInt64.toNat_add]; simp; omega
          · show (MIN dist br).toNat - (i + 1).toNat < (MIN dist br).toNat - i.toNat
            have := UInt64.toNat_lt (MIN dist br)
            rw [UInt64.toNat_add]; simp; omega
        · intro _; rfl
      · rintro _ G hG
        refine Sat.pure ⟨⟨hG, ?_⟩, ?_⟩
        · show (MIN dist br).toNat ≤ _; omega
        · show (br - MIN dist br).toNat < br.toNat
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; omega
    · intro _; exact ⟨rfl, hr⟩
  · rintro ⟨c, br, cur, rem⟩ G ⟨hG, hr⟩
    exact Sat.pure ⟨hG, hr⟩

/-! ## The tail stores of `CHUNKMEMSET` -/

theorem sat_storeChunkBytes {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {p : Nat}
    (chunk start n : UInt64) (h1 : lo ≤ p) (h2 : p + n.toNat ≤ hi) (hN : hi ≤ N) :
    Sat H (storeChunkBytes (B ob p) chunk start n) (fun _ H' => ORun H0 H' ob N lo hi) := by
  unfold storeChunkBytes
  refine Sat.bind (Sat.mono (sat_cwhile
    (fun (i : UInt64) (G : Heap) => i.toNat ≤ n.toNat ∧ ORun H0 G ob N lo hi)
    (fun i => n.toNat - i.toNat)
    (fun _ G => ORun H0 G ob N lo hi) ?_ ⟨by simp, r⟩ (by have := UInt64.toNat_lt n; unfold fuel; omega)) ?_)
  · rintro i G ⟨hi', rG⟩
    refine ⟨_, _, rfl, ?_, ?_⟩
    · intro hc
      have hc' : i.toNat < n.toNat := by
        have := of_decide_eq_true hc; rwa [UInt64.lt_iff_toNat_lt] at this
      exact rG.sat_store_add _ (p + i.toNat) (by simp) (by omega) (by omega) (by omega) (by omega) _ _ _
        fun G1 r1 => Sat.pure ⟨⟨by show (i + 1).toNat ≤ _; rw [UInt64.toNat_add]; simp; omega, r1⟩, by
          show n.toNat - (i + 1).toNat < n.toNat - i.toNat
          have := UInt64.toNat_lt n
          rw [UInt64.toNat_add]; simp; omega⟩
    · intro _; exact rG
  · intro _ G rG; exact Sat.pure rG

/-! ## `CHUNKMEMSET` -/

theorem u64_beq (x y : UInt64) : (x == y) = decide (x.toNat = y.toNat) := by
  by_cases h : x = y
  · subst h; simp
  · have : x.toNat ≠ y.toNat := fun e => h (UInt64.toNat_inj.mp e)
    simp [h, this]

theorem u64_lt (x y : UInt64) : decide (x < y) = decide (x.toNat < y.toNat) := by
  simp [UInt64.lt_iff_toNat_lt]

theorem u64_le (x y : UInt64) : decide (x ≤ y) = decide (x.toNat ≤ y.toNat) := by
  simp [UInt64.le_iff_toNat_le]

theorem u64_sub (x y : UInt64) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact h)

/-- `Ptr.diff` inside one object when the difference is a `ptrdiff_t`. -/
theorem sat_diff_r {H : Heap} {r : BRef} {a : Array UInt8} {o1 o2 : Nat} (hb : Space.get H r = some a)
    (h1 : o1 ≤ a.size) (h2 : o2 ≤ a.size) (hr : -(2 ^ 63 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 2 ^ 63) :
    Sat H (Ptr.diff (.ref r o1) (.ref r o2)) (fun d H' => d = Int64.ofInt ((o1 : Int) - o2) ∧ H' = H) :=
  ⟨_, _, by simp only [Ptr.diff, hb, h1, h2, and_self, ↓reduceIte, hr], rfl, rfl⟩

theorem sat_CHUNKMEMSET {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {o f : Nat} (len : UInt64)
    (hfo : f < o) (hlen : 1 ≤ len.toNat) (h1 : lo ≤ o) (h2 : o + max len.toNat 8 ≤ hi) (hN : hi ≤ N)
    (hd63 : o - f < 2 ^ 63) :
    Sat H (CHUNKMEMSET (B ob o) (B ob f) len) (fun p H' => p = B ob (o + len.toNat) ∧ ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hg : Space.get H (BRef.heap ob) = some a := ha
  have m1 := Nat.le_max_left len.toNat 8
  have m2 := Nat.le_max_right len.toNat 8
  unfold CHUNKMEMSET
  refine Sat.bind (Sat.mono (sat_diff_r hg (o1 := o) (o2 := f) (by omega) (by omega) (by omega)) ?_)
  rintro d H1 ⟨rfl, rfl⟩
  have hdist := absI64 ((o : Int) - f) (by omega) (by omega)
  generalize (if Int64.ofInt ((o : Int) - f) < 0 then -Int64.ofInt ((o : Int) - f)
    else Int64.ofInt ((o : Int) - f)).toUInt64 = dist at hdist ⊢
  have hdn : dist.toNat = o - f := by omega
  refine Sat.bind (Sat.mono (sat_lt hg (o1 := o) (o2 := f) (by omega) (by omega)) ?_)
  rintro c H1 ⟨rfl, rfl⟩
  have hlt : decide (o < f) = false := by simp; omega
  simp (config := { zeta := false }) only [hlt, Bool.false_and, Bool.false_eq_true, ↓reduceIte, u64_beq, u64_lt,
    u64_le, GE.ge, GT.gt, Bool.or_eq_true, decide_eq_true_eq, hdn]
  by_cases e1 : o - f = 1
  · simp only [e1, UInt64.reduceToNat, ↓reduceIte]
    refine Sat.bind (Sat.mono (sat_load hg (k := f) (by omega)) ?_); rintro b H1 rfl
    refine Sat.bind (Sat.mono (r.sat_memset b len.toNat h1 (by omega) (by omega)) ?_); intro _ H1 r1
    obtain ⟨a1, ha1, ha1N⟩ := r1.cur
    exact Sat.mono (sat_add (space_heap H1 ob ▸ ha1) (by omega) _ (o + len.toNat) (by simp) (by omega))
      fun p G ⟨hp, hG⟩ => ⟨hp, hG ▸ r1⟩
  simp (config := { zeta := false }) only [e1, UInt64.reduceToNat, ↓reduceIte, CHUNK]
  by_cases e2 : len.toNat ≤ o - f ∨ 8 < o - f
  · simp only [e2, ↓reduceIte]
    exact sat_CHUNKCOPY r len hlen h1 (by omega) (by omega) (by omega)
  simp (config := { zeta := false }) only [e2, ↓reduceIte]
  have hd8 : o - f ≤ 8 := by omega
  have hdl : o - f < len.toNat := by omega
  lift_lets (config := {merge := false})
  extract_lets jp
  have hjp : ∀ (x : UInt64 × UInt64) (G : Heap), x.2.toNat ≤ 7 → ORun H0 G ob N lo hi →
      Sat G (jp x) (fun p H' => p = B ob (o + len.toNat) ∧ ORun H0 H' ob N lo hi) := by
    rintro ⟨cl, cm⟩ G hcm rG
    simp only [jp]
    simp only at hcm
    have hle8 : ∀ x : UInt64, (x ≤ 8) ↔ x.toNat ≤ 8 := fun x => by rw [UInt64.le_iff_toNat_le]; simp
    by_cases e3 : len.toNat ≤ 8
    · rw [ite_eq_left ((hle8 len).mpr e3)]
      refine Sat.bind (Sat.mono (rG.sat_memwrite8 _ h1 (by omega) (by omega)) ?_); intro _ G1 r1
      obtain ⟨a1, ha1, ha1N⟩ := r1.cur
      exact Sat.mono (sat_add (space_heap G1 ob ▸ ha1) (by omega) _ (o + len.toNat) (by simp) (by omega))
        fun p G2 ⟨hp, hG⟩ => ⟨hp, hG ▸ r1⟩
    rw [ite_eq_right (fun h => e3 ((hle8 len).mp h))]
    have hadv : (8 - cm).toNat = 8 - cm.toNat := u64_sub _ _ (by simp; omega)
    have h2adv : (2 * (8 - cm)).toNat = 2 * (8 - cm.toNat) := by
      rw [UInt64.toNat_mul, hadv]; simp; omega
    have h16 : ((2 : UInt64) * 8).toNat = 16 := rfl
    refine Sat.bind (Sat.mono (sat_cwhile
      (fun (s : BPtr × UInt64) (G : Heap) => ∃ P, s.1 = B ob P ∧ P + s.2.toNat = o + len.toNat ∧ o ≤ P ∧
        ORun H0 G ob N lo hi)
      (fun s => s.2.toNat)
      (fun s G => (∃ P, s.1 = B ob P ∧ P + s.2.toNat = o + len.toNat ∧ o ≤ P ∧ ORun H0 G ob N lo hi) ∧
        s.2.toNat < 16)
      ?_ ⟨o, rfl, rfl, Nat.le_refl _, rG⟩ (UInt64.toNat_lt _)) ?_)
    · rintro ⟨out, L⟩ G ⟨P, hp, hPL, hoP, rG⟩
      simp only at hp hPL; subst hp
      refine ⟨_, _, rfl, ?_, ?_⟩
      · intro hc
        have hc' : 16 ≤ L.toNat := by have := of_decide_eq_true hc; rwa [h16] at this
        refine Sat.bind (Sat.mono (rG.sat_memwrite8 _ (by omega) (by omega) (by omega)) ?_); intro _ G1 r1
        obtain ⟨a1, ha1, ha1N⟩ := r1.cur
        refine Sat.bind (Sat.mono (sat_add (space_heap G1 ob ▸ ha1) (by omega) _ (P + (8 - cm.toNat))
          (by rw [hadv]; simp) (by omega)) ?_)
        rintro q G2 ⟨rfl, rfl⟩
        refine Sat.bind (Sat.mono (r1.sat_memwrite8 _ (by omega) (by omega) (by omega)) ?_); intro _ G2 r2
        obtain ⟨a2, ha2, ha2N⟩ := r2.cur
        refine Sat.bind (Sat.mono (sat_add (space_heap G2 ob ▸ ha2) (by omega) _ (P + 2 * (8 - cm.toNat))
          (by rw [h2adv]; simp) (by omega)) ?_)
        rintro q G3 ⟨rfl, rfl⟩
        have hsub : (L - 2 * (8 - cm)).toNat = L.toNat - 2 * (8 - cm.toNat) := by
          rw [u64_sub _ _ (by rw [h2adv]; omega), h2adv]
        refine Sat.pure ⟨⟨P + 2 * (8 - cm.toNat), rfl, ?_, by omega, r2⟩, ?_⟩
        · show _ + (L - 2 * (8 - cm)).toNat = _; omega
        · show (L - 2 * (8 - cm)).toNat < L.toNat; omega
      · intro hc
        refine ⟨⟨P, rfl, hPL, hoP, rG⟩, ?_⟩
        have := of_decide_eq_false hc; rw [h16] at this; simpa using this
    rintro ⟨out1, L1⟩ G1 ⟨⟨P1, hp1, hPL1, hoP1, rG1⟩, hL16⟩
    simp only at hp1 hPL1 hL16; subst hp1
    refine Sat.bind (Sat.mono (sat_cwhile
      (fun (s : BPtr × UInt64) (G : Heap) => ∃ P, s.1 = B ob P ∧ P + s.2.toNat = o + len.toNat ∧ o ≤ P ∧
        ORun H0 G ob N lo hi)
      (fun s => s.2.toNat)
      (fun s G => (∃ P, s.1 = B ob P ∧ P + s.2.toNat = o + len.toNat ∧ o ≤ P ∧ ORun H0 G ob N lo hi) ∧
        s.2.toNat < 8)
      ?_ ⟨P1, rfl, hPL1, hoP1, rG1⟩ (UInt64.toNat_lt _)) ?_)
    · rintro ⟨out, L⟩ G ⟨P, hp, hPL, hoP, rG⟩
      simp only at hp hPL; subst hp
      refine ⟨_, _, rfl, ?_, ?_⟩
      · intro hc
        have hc' : 8 ≤ L.toNat := by have := of_decide_eq_true hc; simpa using this
        refine Sat.bind (Sat.mono (rG.sat_memwrite8 _ (by omega) (by omega) (by omega)) ?_); intro _ G1 r1
        obtain ⟨a1, ha1, ha1N⟩ := r1.cur
        refine Sat.bind (Sat.mono (sat_add (space_heap G1 ob ▸ ha1) (by omega) _ (P + (8 - cm.toNat))
          (by rw [hadv]; simp) (by omega)) ?_)
        rintro q G2 ⟨rfl, rfl⟩
        have hsub : (L - (8 - cm)).toNat = L.toNat - (8 - cm.toNat) := by
          rw [u64_sub _ _ (by rw [hadv]; omega), hadv]
        refine Sat.pure ⟨⟨P + (8 - cm.toNat), rfl, ?_, by omega, r1⟩, ?_⟩
        · show _ + (L - (8 - cm)).toNat = _; omega
        · show (L - (8 - cm)).toNat < L.toNat; omega
      · intro hc
        refine ⟨⟨P, rfl, hPL, hoP, rG⟩, ?_⟩
        have := of_decide_eq_false hc; simpa using this
    rintro ⟨out2, L2⟩ G2 ⟨⟨P2, hp2, hPL2, hoP2, rG2⟩, hL8⟩
    simp only at hp2 hPL2 hL8; subst hp2
    simp only
    have tail : ∀ (n : UInt64) (G : Heap), 1 ≤ n.toNat → n.toNat ≤ L2.toNat → ORun H0 G ob N lo hi →
        Sat G (do
          storeChunkBytes (B ob P2) cl 0 n
          let q ← Ptr.add (B ob P2) (Int.ofNat (L2 - n).toNat)
          storeChunkBytes q cl (L2 - n) n
          Ptr.add (B ob P2) (Int.ofNat L2.toNat))
          (fun p H' => p = B ob (o + len.toNat) ∧ ORun H0 H' ob N lo hi) := by
      intro n G hn1 hn rG
      have hs : (L2 - n).toNat = L2.toNat - n.toNat := u64_sub _ _ hn
      refine Sat.bind (Sat.mono (sat_storeChunkBytes rG cl 0 n (by omega) (by omega) hN) ?_); intro _ G1 r1
      obtain ⟨a1, ha1, ha1N⟩ := r1.cur
      refine Sat.bind (Sat.mono (sat_add (space_heap G1 ob ▸ ha1) (by omega) _ (P2 + (L2.toNat - n.toNat))
        (by rw [hs]; simp) (by omega)) ?_)
      rintro q G2 ⟨rfl, rfl⟩
      refine Sat.bind (Sat.mono (sat_storeChunkBytes r1 cl _ n (by omega) (by omega) hN) ?_); intro _ G3 r3
      obtain ⟨a3, ha3, ha3N⟩ := r3.cur
      exact Sat.mono (sat_add (space_heap G3 ob ▸ ha3) (by omega) _ (o + len.toNat) (by simp; omega) (by omega))
        fun p G4 ⟨hp, hG⟩ => ⟨hp, hG ▸ r3⟩
    by_cases eL : L2.toNat = 0
    · have : (L2 != 0) = false := by
        have : L2 = 0 := UInt64.toNat_inj.mp (by simpa using eL)
        simp [this]
      rw [this]
      exact Sat.pure ⟨by show B ob _ = B ob _; congr 1; omega, rG2⟩
    have : (L2 != 0) = true := by
      have : L2 ≠ 0 := fun e => eL (by simp [e])
      simpa using this
    rw [ite_eq_left this]
    have hn16 : ¬ (16 ≤ L2) := by rw [UInt64.le_iff_toNat_le]; simp; omega
    have hn8 : ¬ (8 ≤ L2) := by rw [UInt64.le_iff_toNat_le]; simp; omega
    rw [ite_eq_right hn16, ite_eq_right hn8]
    by_cases e4 : 4 ≤ L2.toNat
    · rw [ite_eq_left (by rw [UInt64.le_iff_toNat_le]; simpa using e4)]
      exact tail 4 G2 (by simp) (by simpa using e4) rG2
    rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simpa using e4)]
    by_cases e2' : 2 ≤ L2.toNat
    · rw [ite_eq_left (by rw [UInt64.le_iff_toNat_le]; simpa using e2')]
      exact tail 2 G2 (by simp) (by simpa using e2') rG2
    rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simpa using e2')]
    have hL1 : L2.toNat = 1 := by omega
    refine Sat.bind (Sat.mono (sat_storeChunkBytes rG2 cl 0 1 (by omega) (by simp; omega) hN) ?_); intro _ G3 r3
    obtain ⟨a3, ha3, ha3N⟩ := r3.cur
    exact Sat.mono (sat_add (space_heap G3 ob ▸ ha3) (by omega) _ (o + len.toNat) (by simp; omega) (by omega))
      fun p G4 ⟨hp, hG⟩ => ⟨hp, hG ▸ r3⟩
  clear_value jp
  have hgf : f + 8 ≤ a.size := by omega
  by_cases e4 : o - f = 4
  · simp only [e4, ↓reduceIte]
    refine Sat.bind (Sat.mono (Sat.bind (Sat.mono (sat_memread4 hg (k := f) (by omega))
      fun _ G hG => Sat.pure (Q := fun _ H' => H' = H1) hG)) ?_); rintro _ G rfl
    exact Sat.bind (Sat.pure (hjp _ _ (by simp) r))
  simp only [e4, ↓reduceIte]
  by_cases e8 : o - f = 8
  · simp only [e8, ↓reduceIte]
    refine Sat.bind (Sat.mono (sat_memread8 hg (by omega)) ?_); rintro _ G rfl
    exact Sat.bind (Sat.pure (hjp _ _ (by simp) r))
  simp only [e8, ↓reduceIte]
  refine Sat.bind (Sat.mono (sat_GET_CHUNK_MAG hg 0 dist (by omega) (by simp) (by omega)) ?_)
  rintro x G ⟨rfl, hx⟩
  exact hjp x _ (by omega) r

/-! ## The byte loops `*out++ = *from++` -/

/-- The invariant of a byte loop copying `n` bytes from `f` to `o`, after `k` bytes. -/
def BL (H0 : Heap) (ob N lo hi o f n : Nat) (s : BPtr × BPtr × UInt64) (G : Heap) : Prop :=
  ∃ k, s = (B ob (o + k), B ob (f + k), s.2.2) ∧ k + s.2.2.toNat = n ∧ ORun H0 G ob N lo hi

theorem bl_step {H0 G : Heap} {ob N lo hi o f n k : Nat} {L : UInt64} (rG : ORun H0 G ob N lo hi)
    (hk : k + L.toNat = n) (hL : 0 < L.toNat) (h1 : lo ≤ o) (h2 : o + n ≤ hi) (hN : hi ≤ N) (hf : f + n ≤ N) :
    Sat G (do
        Ptr.store (B ob (o + k)) (← load8 (B ob (f + k)))
        pure (← (B ob (o + k)).add 1, ← (B ob (f + k)).add 1, L - 1))
      (fun s2 G2 => BL H0 ob N lo hi o f n s2 G2 ∧ s2.2.2.toNat < L.toNat) := by
  obtain ⟨a, ha, haN⟩ := rG.cur
  have hg : Space.get G (BRef.heap ob) = some a := ha
  refine Sat.bind (Sat.mono (sat_load hg (k := f + k) (by omega)) ?_); rintro v G1 rfl
  refine Sat.bind (Sat.mono (rG.sat_store v (k := o + k) (by omega) (by omega) (by omega)) ?_); intro _ G1 r1
  obtain ⟨a1, ha1, ha1N⟩ := r1.cur
  have hg1 : Space.get G1 (BRef.heap ob) = some a1 := ha1
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) 1 (o + (k + 1)) (by simp; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_add hg1 (by omega) 1 (f + (k + 1)) (by simp; omega) (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  have e : (L - 1).toNat = L.toNat - 1 := u64_sub _ _ (by simp; omega)
  exact Sat.pure ⟨⟨k + 1, rfl, by simp only [e]; omega, r1⟩, by simp only [e]; omega⟩

/-! ## `CHUNKMEMSET_SAFE` (`chunkmemset_safe_c`) -/

theorem min_toNat (x y : UInt64) : (MIN x y).toNat = min x.toNat y.toNat := by
  unfold MIN; split
  · rename_i h; rw [GT.gt, UInt64.lt_iff_toNat_lt] at h; omega
  · rename_i h; rw [GT.gt, UInt64.lt_iff_toNat_lt] at h; omega

/-- `chunkmemset_safe_c(out, out - dist, len, left)` with `left` bytes of room at `out`: it writes only inside the
room and returns `out + MIN(len, left)`. -/
theorem sat_CHUNKMEMSET_SAFE {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {o f : Nat}
    (len left : UInt64) (hfo : f < o) (h1 : lo ≤ o) (h2 : o + left.toNat ≤ hi) (hN : hi ≤ N) (hd63 : o - f < 2 ^ 63) :
    Sat H (CHUNKMEMSET_SAFE (B ob o) (B ob f) len left)
      (fun p H' => p = B ob (o + min len.toNat left.toNat) ∧ ORun H0 H' ob N lo hi) := by
  unfold CHUNKMEMSET_SAFE
  have hm := min_toNat len left
  generalize MIN len left = len' at hm ⊢
  by_cases hl : left.toNat < 8
  · rw [ite_eq_left (show left < CHUNK by rw [UInt64.lt_iff_toNat_lt]; simpa [CHUNK] using hl)]
    refine Sat.bind (Sat.mono (sat_cwhile (BL H0 ob N lo hi o f len'.toNat) (fun s => s.2.2.toNat)
      (fun s G => ∃ k, s.1 = B ob (o + k) ∧ k = len'.toNat ∧ ORun H0 G ob N lo hi) ?_
      ⟨0, by simp, by simp, r⟩ (UInt64.toNat_lt _)) ?_)
    · rintro ⟨out, fr, L⟩ G ⟨k, hs, hk, rG⟩
      simp only [Prod.mk.injEq] at hs hk
      obtain ⟨rfl, rfl, -⟩ := hs
      refine ⟨_, _, rfl, fun hc => ?_, fun hc => ?_⟩
      · have hL : 0 < L.toNat := by
          have := of_decide_eq_true hc; rw [GT.gt, UInt64.lt_iff_toNat_lt] at this; simpa using this
        exact bl_step rG hk hL h1 (by omega) hN (by omega)
      · have hL : L.toNat = 0 := by
          have := of_decide_eq_false hc; rw [GT.gt, UInt64.lt_iff_toNat_lt] at this; simp at this; omega
        exact ⟨k, rfl, by omega, rG⟩
    · rintro ⟨out, fr, L⟩ G ⟨k, hp, hk, rG⟩
      simp only at hp
      exact Sat.pure ⟨by rw [hp, hk, hm], rG⟩
  rw [ite_eq_right (show ¬ left < CHUNK by rw [UInt64.lt_iff_toNat_lt]; simpa [CHUNK] using hl)]
  by_cases hz : len'.toNat = 0
  · have : (len' != 0) = false := by
      have : len' = 0 := UInt64.toNat_inj.mp (by simpa using hz)
      simp [this]
    rw [this]
    exact Sat.pure ⟨by rw [← hm, hz]; rfl, r⟩
  have : (len' != 0) = true := by
    have : len' ≠ 0 := fun e => hz (by simp [e])
    simpa using this
  rw [ite_eq_left this]
  have := Nat.le_max_left len'.toNat 8
  have := Nat.le_max_right len'.toNat 8
  exact Sat.mono (sat_CHUNKMEMSET r len' hfo (by omega) h1 (by omega) hN hd63)
    fun p G ⟨hp, rG⟩ => ⟨by rw [hp, hm], rG⟩

/-! ## `CHUNKCOPY_SAFE` -/

theorem beq_B (ob o f : Nat) (h : f ≠ o) : (B ob o == B ob f) = false := by
  simp [B]; omega

/-- `CHUNKCOPY_SAFE(out, out - dist, len, safe)` with `safe` in the same block: it writes only inside `[out, safe)`
and returns `out + MIN(len, safe - out)`. -/
theorem sat_CHUNKCOPY_SAFE {H0 H : Heap} {ob N lo hi : Nat} (r : ORun H0 H ob N lo hi) {o f s : Nat}
    (len : UInt64) (hfo : f < o) (hos : o ≤ s) (hlen : 1 ≤ len.toNat) (h1 : lo ≤ o) (h2 : s ≤ hi) (hN : hi ≤ N)
    (hN63 : N < 2 ^ 63) :
    Sat H (CHUNKCOPY_SAFE (B ob o) (B ob f) len (B ob s))
      (fun p H' => p = B ob (o + min len.toNat (s - o)) ∧ ORun H0 H' ob N lo hi) := by
  obtain ⟨a, ha, haN⟩ := r.cur
  have hg : Space.get H (BRef.heap ob) = some a := ha
  unfold CHUNKCOPY_SAFE
  rw [beq_B ob o f (by omega)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.mono (sat_diff hg (o1 := s) (o2 := o) (by omega) (by omega) (by omega)) ?_)
  rintro d G ⟨rfl, rfl⟩
  have hsl : (Int64.ofInt ((s : Int) - o)).toUInt64.toNat = s - o := by
    rw [toNat_ofInt_nonneg _ (by omega) (by omega)]; omega
  generalize (Int64.ofInt ((s : Int) - o)).toUInt64 = safelen at hsl ⊢
  have hm := min_toNat len safelen
  generalize MIN len safelen = len' at hm ⊢
  refine Sat.bind (Sat.mono (sat_diff hg (o1 := s) (o2 := f) (by omega) (by omega) (by omega)) ?_)
  rintro d G ⟨rfl, rfl⟩
  have hfd := absI64 ((s : Int) - f) (by omega) (by omega)
  generalize (if Int64.ofInt ((s : Int) - f) < 0 then -Int64.ofInt ((s : Int) - f)
    else Int64.ofInt ((s : Int) - f)).toUInt64 = from_dist at hfd ⊢
  split
  · rename_i hb
    simp only [CHUNK, Bool.or_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at hb
    refine Sat.bind (Sat.mono (sat_cwhile (BL H0 ob N lo hi o f len'.toNat) (fun s => s.2.2.toNat)
      (fun s G => ∃ k, s.1 = B ob (o + k) ∧ k = len'.toNat ∧ ORun H0 G ob N lo hi) ?_
      ⟨0, by simp, by simp, r⟩ (UInt64.toNat_lt _)) ?_)
    · rintro ⟨out, fr, L⟩ G ⟨k, hs, hk, rG⟩
      simp only [Prod.mk.injEq] at hs hk
      obtain ⟨rfl, rfl, -⟩ := hs
      refine ⟨_, _, rfl, fun hc => ?_, fun hc => ?_⟩
      · have hL : 0 < L.toNat := by
          have : L ≠ 0 := by simpa using hc
          have : L.toNat ≠ 0 := fun e => this (UInt64.toNat_inj.mp (by simpa using e))
          omega
        exact bl_step rG hk hL h1 (by omega) hN (by omega)
      · have hL : L.toNat = 0 := by
          have : L = 0 := by simpa using hc
          simp [this]
        exact ⟨k, rfl, by omega, rG⟩
    · rintro ⟨out, fr, L⟩ G ⟨k, hp, hk, rG⟩
      simp only at hp
      exact Sat.pure ⟨by rw [hp, hk, hm, hsl], rG⟩
  rename_i hb
  simp only [CHUNK, Bool.or_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at hb
  have := Nat.le_max_left len'.toNat 8
  have := Nat.le_max_right len'.toNat 8
  exact Sat.mono (sat_CHUNKMEMSET r len' hfo (by omega) h1 (by omega) hN (by omega))
    fun p G ⟨hp, rG⟩ => ⟨by rw [hp, hm, hsl], rG⟩

/-! ## Summary: each routine alone

`out = B ob o`, `from = B ob f` in heap block `ob` of `N < 2 ^ 63` bytes, `f < o`. Each routine terminates without
fault, returns the stated pointer, and changes nothing in the heap but the bytes `[o, hi)` of block `ob`. -/

theorem chunkcopy_c_safe {H : Heap} {ob N : Nat} {a : Array UInt8} (ha : H.bytes ob = some a) (hN : a.size = N)
    {o f : Nat} (len : UInt64) (hlen : 1 ≤ len.toNat) (ho : o + max len.toNat 8 ≤ N) (hf : f < o) :
    Sat H (CHUNKCOPY (B ob o) (B ob f) len)
      (fun p H' => p = B ob (o + len.toNat) ∧ ORun H H' ob N o (o + max len.toNat 8)) :=
  sat_CHUNKCOPY (ORun.refl ha hN _ _) len hlen (Nat.le_refl _) (Nat.le_refl _) ho (by omega)

theorem chunkunroll_c_safe {H : Heap} {ob N : Nat} {a : Array UInt8} (ha : H.bytes ob = some a)
    (hN : a.size = N) {o : Nat} (dist len : UInt32) (hd1 : 1 ≤ dist.toNat) (hdo : dist.toNat ≤ o)
    (ho : o + len.toNat + 6 ≤ N) :
    Sat H (CHUNKUNROLL (B ob o) dist len) (fun res H' =>
      ∃ L D : UInt32, res = (B ob (o + len.toNat - L.toNat), D, L) ∧ L.toNat ≤ len.toNat ∧
        D.toNat = dist.toNat + (len.toNat - L.toNat) ∧ (1 ≤ len.toNat → 1 ≤ L.toNat) ∧
        (L.toNat ≤ D.toNat ∨ 8 ≤ D.toNat) ∧ ORun H H' ob N o (o + min (len.toNat + 6) 14)) :=
  sat_CHUNKUNROLL (ORun.refl ha hN _ _) dist len hd1 hdo (Nat.le_refl _) (fun _ => Nat.le_refl _)
    (by have := Nat.min_le_left (len.toNat + 6) 14; omega) (by omega)

theorem chunkmemset_c_safe {H : Heap} {ob N : Nat} {a : Array UInt8} (ha : H.bytes ob = some a)
    (hN : a.size = N) {o f : Nat} (hd63 : o - f < 2 ^ 63) (len : UInt64) (hlen : 1 ≤ len.toNat)
    (ho : o + max len.toNat 8 ≤ N) (hf : f < o) :
    Sat H (CHUNKMEMSET (B ob o) (B ob f) len)
      (fun p H' => p = B ob (o + len.toNat) ∧ ORun H H' ob N o (o + max len.toNat 8)) :=
  sat_CHUNKMEMSET (ORun.refl ha hN _ _) len hf hlen (Nat.le_refl _) (Nat.le_refl _) ho hd63

theorem chunkmemset_safe_c_safe {H : Heap} {ob N : Nat} {a : Array UInt8} (ha : H.bytes ob = some a)
    (hN : a.size = N) {o f : Nat} (hd63 : o - f < 2 ^ 63) (len left : UInt64) (ho : o + left.toNat ≤ N) (hf : f < o) :
    Sat H (ZlibNg.ChunksetC.chunkmemset_safe_c (B ob o) (B ob f) len left)
      (fun p H' => p = B ob (o + min len.toNat left.toNat) ∧ ORun H H' ob N o (o + left.toNat)) :=
  sat_CHUNKMEMSET_SAFE (ORun.refl ha hN _ _) len left hf (Nat.le_refl _) (Nat.le_refl _) ho hd63

theorem chunkcopy_safe_tpl_safe {H : Heap} {ob N : Nat} {a : Array UInt8} (ha : H.bytes ob = some a)
    (hN : a.size = N) (hN63 : N < 2 ^ 63) {o f s : Nat} (len : UInt64) (hlen : 1 ≤ len.toNat) (hf : f < o)
    (hos : o ≤ s) (hs : s ≤ N) :
    Sat H (CHUNKCOPY_SAFE (B ob o) (B ob f) len (B ob s))
      (fun p H' => p = B ob (o + min len.toNat (s - o)) ∧ ORun H H' ob N o s) :=
  sat_CHUNKCOPY_SAFE (ORun.refl ha hN _ _) len hf hos hlen (Nat.le_refl _) (Nat.le_refl _) hs hN63

end ZlibNgF.Proof.ChunkCopy
