import ZlibNgF.Proof.«insert_string_p.h.sli»

/-!
# The hash chains under `insert_roll`, `insert_skip` and the tail insertions (`ZlibNgF`)

`insert_roll` (one insertion with the rolling hash) grows the chains by its position, as `insert_knuth`
(`insert_roll_G`).

`insert_skip(s, str, count)` (`count <= w_size`) zeroes the `prev` slots of the positions `str .. str + count - 1`
(two `memset`s of whole `Pos` slots, the second after the wrap of `prev`) and writes nothing else. No position joins the
chain set: (C1) and (C2) do not read `prev`, and a zeroed slot satisfies (C3) for every position of the set, since 0 is
allowed (`grow_zero`). So the chain set `I` is kept as it is (`insert_skip_G`, with the empty set of new positions).

`insert_knuth_batch_tail_static` / `insert_roll_batch_tail_static` (`tail <= count`): `insert_skip` of the first
`count - tail` positions, then the batch insertion of the last `tail` positions `str + count - tail .. str + count - 1`;
these are the positions that join the chain set.

The `sli_*` wrappers run them inside the strategy loop (`SLI`); the rolling forms change `ins_h`, which the loop
invariant does not read (`sli_insh`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InsertTail
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNg.InsertStringP ZlibNg.InsertString ZlibNgF.Proof.InsertSafe ZlibNgF.Proof.InsertChain
open ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop ZlibNgF.Proof.Strategy ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts (posAt)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.ChunkMem (fillFold fillFold_get fillFold_size mem_range'_bound)
open ZlibNgF.Proof.DeflateAlloc (fillFold_in)

/-! ## Zeroed `prev` slots -/

/-- Zeroing the `prev` slots `a .. a + n - 1` (the bytes `[po + 2 a, po + 2 (a + n))`) keeps the chain clauses with the
same set: no position joins. -/
theorem grow_zero {d : Array UInt8} {ho po w a n off : Nat} (S : Nat → Prop) (hw : 0 < w) (ho2 : off = po + 2 * a)
    (han : a + n ≤ w) (hph : po + 2 * w ≤ ho) (hd : ho + 131072 ≤ d.size) :
    Grow d (fillFold 0 off (List.range' 0 (n * 2)) d) ho po w S := by
  subst ho2
  intro ss lim I C _
  refine ⟨I, C.c1, fun k hk hne => ?_, fun p hp hin => ?_⟩
  · have e : posAt (fillFold 0 (po + 2 * a) (List.range' 0 (n * 2)) d) ho k = posAt d ho k := by
      unfold posAt
      rw [fillFold_get _ _ _ _ _ (fun j hj => mem_range'_bound hj (by omega)),
        fillFold_get _ _ _ _ _ (fun j hj => mem_range'_bound hj (by omega))]
    rw [e] at hne ⊢; exact C.c2 k hk hne
  · have hm := Nat.mod_lt p hw
    by_cases hk : a ≤ p % w ∧ p % w < a + n
    · left
      unfold posAt
      rw [fillFold_in 0 _ _ _ _ ⟨2 * (p % w - a), by rw [List.mem_range'_1]; omega, by omega⟩ (by omega),
        fillFold_in 0 _ _ _ _ ⟨2 * (p % w - a) + 1, by rw [List.mem_range'_1]; omega, by omega⟩ (by omega)]
      rfl
    · have e : posAt (fillFold 0 (po + 2 * a) (List.range' 0 (n * 2)) d) po (p % w) = posAt d po (p % w) := by
        unfold posAt
        rw [fillFold_get _ _ _ _ _ (fun j hj => mem_range'_bound hj (by omega)),
          fillFold_get _ _ _ _ _ (fun j hj => mem_range'_bound hj (by omega))]
      rw [e]; exact C.c3 p hp hin

theorem fill_wrin (od n : Nat) (d : Array UInt8) : WrIn d od (od + n) (fillFold 0 od (List.range' 0 n) d) :=
  ⟨fillFold_size .., fun _ hj => fillFold_get _ _ _ _ _ (fun _ hx => mem_range'_bound hx (by omega))⟩

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- `insert_skip(s, str, count)` with `count <= w_size`: the `prev` slots of `count` positions zeroed, nothing joins the
chain set. -/
theorem insert_skip_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str count : UInt32) (hc : count.toNat ≤ st.w_size.toNat) :
    Sat (SH H i z b st d) (insert_skip (some b) str count)
      (GPost H i z b st d ho po st.w_size.toNat (fun _ => False)) := by
  have hw := L.w1
  have hph := L.ph
  have hho := L.hd
  have hpw := L.pw
  unfold insert_skip
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  simp only [L.prev]
  have hm := wmask_mod hp str
  have hmw := Nat.mod_lt str.toNat (show 0 < st.w_size.toNat by omega)
  generalize str &&& W_MASK st = idx at hm
  have hwi : (st.w_size - idx).toNat = st.w_size.toNat - idx.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  generalize hf : (if count < st.w_size - idx then count else st.w_size - idx) = f
  have hf' : f.toNat = min count.toNat (st.w_size.toNat - idx.toNat) := by
    subst hf; split
    · rename_i h; have := UInt32.lt_iff_toNat_lt.mp h; omega
    · rename_i h; have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h); omega
  have hcf : (count - f).toNat = count.toNat - f.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  refine Sat.bind (Sat.pure ?_)
  have ea : Ptr.add (Ptr.ref (BRef.heap b) po) (2 * (idx.toNat : Int)) (SH H i z b st d) =
      .ok (.ref (.heap b) (po + 2 * idx.toNat), SH H i z b st d) := by
    rw [show 2 * (idx.toNat : Int) = ((2 * idx.toNat : Nat) : Int) by omega]
    exact addN_SH (2 * idx.toNat) (by omega)
  refine Sat.bind (Sat.of_eq ea ?_)
  refine Sat.bind (Sat.of_eq (memset_SH (by omega) 0) ?_)
  refine Sat.bind (Sat.pure ?_)
  refine Sat.of_eq (memset_SH (by rw [fillFold_size, hcf]; omega) 0) ?_
  refine ⟨_, rfl, ?_, ?_⟩
  · have w1 := fill_wrin (po + 2 * idx.toNat) (f.toNat * 2) d
    have w2 := fill_wrin po ((count - f).toNat * 2) (fillFold 0 (po + 2 * idx.toNat) (List.range' 0 (f.toNat * 2)) d)
    exact (w1.widen (lo' := po) (hi' := ho + 131072) (by omega) (by omega)).trans
      (w2.widen (lo' := po) (hi' := ho + 131072) (by omega) (by rw [hcf]; omega)) (Nat.le_refl _) (Nat.le_refl _)
  · refine (grow_zero (a := idx.toNat) (n := f.toNat) _ (by omega) rfl (by omega) hph hho).trans
      (grow_zero (a := 0) (n := (count - f).toNat) _ (by omega) (by omega) (by rw [hcf]; omega) hph
        (by rw [fillFold_size]; exact hho)) (fun _ h => h) (fun _ h => h)

/-- `insert_roll(s, window, str)`: the chains grow by `str`; `ins_h` changes. -/
theorem insert_roll_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str : UInt32) (hr : wo + str.toNat + 3 ≤ d.size) (hi : str.toNat < 65536) :
    Sat (SH H i z b st d) (insert_roll (some b) (.ref (.heap b) wo) str)
      (GPostH H i z b st d ho po st.w_size.toNat (· = str.toNat)) := by
  have hw := L.w1
  have hph := L.ph
  have hho := L.hd
  unfold insert_roll
  refine Sat.bind (Sat.of_eq (addN_SH str.toNat (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (addN_SH (STD_MIN_MATCH - 1).toNat (by simp [STD_MIN_MATCH]; omega)) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.ro (index8_SH 0 (by decide) (by simp [STD_MIN_MATCH]; omega)) (fun c => ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have L' := L.insh (UPDATE_HASH_ROLL st.ins_h c.toUInt32)
  have hm : ∀ x : UInt32, (x &&& W_MASK { st with ins_h := UPDATE_HASH_ROLL st.ins_h c.toUInt32 }).toNat =
      x.toNat % st.w_size.toNat := fun x => wmask_mod hp x
  have hh := roll_lt st.ins_h c.toUInt32
  have hsx : ∀ d', SH H i z b { st with ins_h := UPDATE_HASH_ROLL st.ins_h c.toUInt32 } d' =
      SH H i z b { st with ins_h := UPDATE_HASH_ROLL st.ins_h c.toUInt32 } d' := fun _ => rfl
  generalize hs1 : { st with ins_h := UPDATE_HASH_ROLL st.ins_h c.toUInt32 } = st1 at L' hm hsx ⊢
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L'.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (posLoad_eq _ (by omega)) ?_)
  split
  · have hmw := Nat.mod_lt str.toNat (show 0 < st.w_size.toNat by omega)
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    simp only [L'.prev]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq (str &&& W_MASK st1).toNat _
      (by rw [hm]; omega)) ?_)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [L'.head]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq _ _ (by rw [wr2_size]; omega)) ?_)
    obtain ⟨w1, g1⟩ := ins_bytes (d := d) (po := po) (ho := ho) str (str &&& W_MASK st1)
      (UPDATE_HASH_ROLL st.ins_h c.toUInt32) (show 0 < st.w_size.toNat by omega) (hm str) hi hh hho hph
    subst hs1
    exact Sat.pure ⟨_, _, rfl, w1, g1⟩
  · subst hs1
    exact Sat.pure ⟨d, _, rfl, WrIn.refl _ _ _, Grow.refl _ _ _ _ _⟩

/-- `insert_knuth_batch_tail_static(s, window, str, count, tail)` with `tail <= count`, `count - tail <= w_size`: the
chains grow by the last `tail` positions `[str + count - tail, str + count)`. -/
theorem insert_knuth_batch_tail_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str count tail : UInt32) (ht : tail.toNat ≤ count.toNat) (hc : count.toNat - tail.toNat ≤ st.w_size.toNat)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H i z b st d) (insert_knuth_batch_tail_static (some b) (.ref (.heap b) wo) str count tail)
      (GPost H i z b st d ho po st.w_size.toNat
        (fun q => str.toNat + count.toNat - tail.toNat ≤ q ∧ q < str.toNat + count.toNat)) := by
  unfold insert_knuth_batch_tail_static
  have hk : (count - tail).toNat = count.toNat - tail.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr ht)
  have hsk : (str + (count - tail)).toNat = str.toNat + (count.toNat - tail.toNat) := by
    rw [UInt32.toNat_add, hk]; omega
  refine Sat.bind (Sat.mono (insert_skip_G L hp str (count - tail) (by rw [hk]; exact hc)) ?_)
  rintro _ _ ⟨d1, rfl, w1, g1⟩
  have hs1 := w1.1
  have L1 : HLay b d1.size st wo po ho := ⟨L.win, L.prev, L.head, L.w1, by have := L.pw; omega, by have := L.hd; omega, L.ph⟩
  refine Sat.mono (insert_knuth_batch_G L1 hp _ tail (by rw [hsk]; omega) (by rw [hsk]; omega)) ?_
  rintro _ _ ⟨d2, rfl, w2, g2⟩
  exact ⟨d2, rfl, wtr w1 w2, g1.trans g2 (fun _ h => h.elim) (fun q hq => by rw [hsk] at hq; omega)⟩

/-- `insert_roll_batch_tail_static(s, window, str, count, tail)` with `tail <= count`, `count - tail <= w_size`: as the
Knuth form, with `ins_h` recomputed from the two bytes at `str + count - tail`. -/
theorem insert_roll_batch_tail_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str count tail : UInt32) (ht : tail.toNat ≤ count.toNat) (hc : count.toNat - tail.toNat ≤ st.w_size.toNat)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H i z b st d) (insert_roll_batch_tail_static (some b) (.ref (.heap b) wo) str count tail)
      (GPostH H i z b st d ho po st.w_size.toNat
        (fun q => str.toNat + count.toNat - tail.toNat ≤ q ∧ q < str.toNat + count.toNat)) := by
  unfold insert_roll_batch_tail_static
  have hk : (count - tail).toNat = count.toNat - tail.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr ht)
  have hsk : (str + (count - tail)).toNat = str.toNat + (count.toNat - tail.toNat) := by
    rw [UInt32.toNat_add, hk]; omega
  have hsk1 : (str + (count - tail) + 1).toNat = str.toNat + (count.toNat - tail.toNat) + 1 := by
    rw [UInt32.toNat_add, hsk]; simp; omega
  refine Sat.bind (Sat.mono (insert_skip_G L hp str (count - tail) (by rw [hk]; exact hc)) ?_)
  rintro _ _ ⟨d1, rfl, w1, g1⟩
  have hs1 := w1.1
  dsimp only
  refine Sat.ro (index8_SH _ (by omega) (by simp only [Int.toNat_natCast]; rw [hsk]; omega)) (fun x => ?_)
  refine Sat.ro (index8_SH _ (by omega) (by simp only [Int.toNat_natCast]; rw [hsk1]; omega)) (fun y => ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have L1 : HLay b d1.size { st with ins_h := update_hash_roll x.toUInt32 y.toUInt32 } wo po ho :=
    ⟨L.win, L.prev, L.head, L.w1, by show po + 2 * st.w_size.toNat ≤ d1.size; have := L.pw; omega, by have := L.hd; omega, L.ph⟩
  refine Sat.mono (insert_roll_batch_G L1 hp _ tail (by rw [hsk]; omega) (by rw [hsk]; omega)) ?_
  rintro _ _ ⟨d2, x2, rfl, w2, g2⟩
  exact ⟨d2, x2, rfl, wtr w1 w2, g1.trans g2 (fun _ h => h.elim) (fun q hq => by rw [hsk] at hq; omega)⟩

end

/-! ## Inside the strategy loop -/

/-- `SLI` survives a change of `ins_h`, which the invariant does not read. -/
theorem sli_insh {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d)) (x : UInt32) : SLI h i b la ss (SH H0 i z b { st with ins_h := x } d) := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  simp only [SH_dstate, SH_bytes] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  have e3 := congrArg (fun H => H.streams i) e
  simp only [SH_streams] at e3
  obtain rfl := Option.some.inj e3
  refine ⟨H1, z, { st with ins_h := x }, d, ?_, ?_⟩
  · rw [← SH_SH H0 i z z b st { st with ins_h := x } d d, e, SH_SH]
  · refine ⟨slf_SH C.1 (fun al _ c => DCore.of_heap (by rw [SH_bytes, SH_bytes]) c) rfl rfl rfl rfl
      (C.1.st _ (SH_dstate _ _ _ _ _ _)).2.2 (StratKeeps.refl _) (fun _ => Nat.le_refl _), fun st2 h2 => ?_⟩
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    obtain ⟨hp, hs⟩ := C.2 (FS st la ss) (SH_dstate _ _ _ _ _ _)
    exact ⟨hp, hs⟩

/-- An insertion function with the post `GPostH` (it may change `ins_h`) inside the strategy loop. -/
theorem sli_insH {α : Type} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} {m : M α} {S : Nat → Prop} (I : SLI h i b la ss (SH H0 i z b st d))
    (hm : ∀ wo po ho, HLay b d.size st wo po ho → (∃ k, st.w_size.toNat = 2 ^ k) →
      wo + st.window_size.toNat ≤ po → Sat (SH H0 i z b st d) m (GPostH H0 i z b st d ho po st.w_size.toNat S)) :
    Sat (SH H0 i z b st d) m (fun _ H' => ∃ d' x, H' = SH H0 i z b { st with ins_h := x } d' ∧ SLI h i b la ss H' ∧
      GrowSt b st d d' S) := by
  have I0 := I
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I0
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  simp only [SH_dstate, SH_bytes] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain ⟨wo, po, ho, L, hp, hwp⟩ := slf_hlay C.1
  have L' : HLay b d.size st wo po ho := ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩
  refine Sat.mono (hm wo po ho L' hp hwp) ?_
  rintro _ _ ⟨d', x, rfl, w, g⟩
  refine ⟨d', x, rfl, sli_insh (sli_bytes I fun ho' hh => ?_) x, fun ho' po' hh hpv => ?_⟩
  · rw [L'.head] at hh
    obtain rfl : ho = ho' := by injection hh with e; injection e
    exact w.widen (Nat.zero_le _) (Nat.le_refl _)
  · rw [L'.head] at hh; rw [L'.prev] at hpv
    obtain rfl : ho = ho' := by injection hh with e; injection e
    obtain rfl : po = po' := by injection hpv with e; injection e
    exact g

/-- `insert_roll(s, window, str)` inside the strategy loop, its byte read in the window. -/
theorem sli_insert_roll {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (str : UInt32) (hr : str.toNat + 3 ≤ st.window_size.toNat) (hs : str.toNat < 65536) :
    Sat (SH H0 i z b st d) (insert_roll (some b) (.ref (.heap b) wo) str)
      (fun _ H' => ∃ d' x, H' = SH H0 i z b { st with ins_h := x } d' ∧ SLI h i b la ss H' ∧
        GrowSt b st d d' (· = str.toNat)) :=
  sli_insH I fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_roll_G L hp str (by have := L.pw; omega) hs

/-- `insert_batch(s, window, str, count)` through the function pointer (not `insert_knuth_batch_head`) inside the
strategy loop. -/
theorem sli_call_insert_batch {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (f : InsertBatchFn) (hf : f ≠ .insert_knuth_batch_head) (str count : UInt32)
    (hr : str.toNat + count.toNat + 3 ≤ st.window_size.toNat) (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H0 i z b st d) (call_insert_batch f (some b) (.ref (.heap b) wo) str count)
      (fun _ H' => ∃ d' x, H' = SH H0 i z b { st with ins_h := x } d' ∧ SLI h i b la ss H' ∧
        GrowSt b st d d' (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) :=
  sli_insH I fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact call_insert_batch_G L hp f hf str count (by have := L.pw; omega) hs

/-- `insert_knuth_batch_tail_static(s, window, str, count, tail)` inside the strategy loop. -/
theorem sli_insert_knuth_tail {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (str count tail : UInt32) (ht : tail.toNat ≤ count.toNat) (hc : count.toNat - tail.toNat ≤ st.w_size.toNat)
    (hr : str.toNat + count.toNat + 3 ≤ st.window_size.toNat) (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H0 i z b st d) (insert_knuth_batch_tail_static (some b) (.ref (.heap b) wo) str count tail)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLI h i b la ss H' ∧
        GrowSt b st d d' (fun q => str.toNat + count.toNat - tail.toNat ≤ q ∧ q < str.toNat + count.toNat)) :=
  sli_ins I fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_knuth_batch_tail_G L hp str count tail ht hc (by have := L.pw; omega) hs

/-- `insert_roll_batch_tail_static(s, window, str, count, tail)` inside the strategy loop. -/
theorem sli_insert_roll_tail {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (str count tail : UInt32) (ht : tail.toNat ≤ count.toNat) (hc : count.toNat - tail.toNat ≤ st.w_size.toNat)
    (hr : str.toNat + count.toNat + 3 ≤ st.window_size.toNat) (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H0 i z b st d) (insert_roll_batch_tail_static (some b) (.ref (.heap b) wo) str count tail)
      (fun _ H' => ∃ d' x, H' = SH H0 i z b { st with ins_h := x } d' ∧ SLI h i b la ss H' ∧
        GrowSt b st d d' (fun q => str.toNat + count.toNat - tail.toNat ≤ q ∧ q < str.toNat + count.toNat)) :=
  sli_insH I fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_roll_batch_tail_G L hp str count tail ht hc (by have := L.pw; omega) hs

end ZlibNgF.Proof.InsertTail
