import ZlibNgF.Proof.«inftrees.c.geom»

/-!
# `zng_inflate_table`: which slots hold entries (`ZlibNgF`)

The coverage part `Cv` of the loop invariant across the three steps that change it: the replication of an entry
(`cov_fill`: the slots whose code interval starts in `[K, K + 2 ^ (16 - len))` are exactly the replicated ones), the
opening of a sub-table (`cov_link`: the previous sub-table is complete and the new one is empty), and the end of
the codes (`cov_final`: every slot of the used region is written).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount
open ZlibNgF.Proof.InfbackLoop (Lvl PosCB lvl_congr lvl_of_pos pos_of_slot)

theorem getElem!_of_some {C : Array Code} {k : Nat} {v : Code} (h : C[k]? = some v) : C[k]! = v := by
  simp [getElem!_def, h]

theorem getElem!_congr {C C' : Array Code} {k : Nat} (h : C'[k]? = C[k]?) : C'[k]! = C[k]! := by
  simp [getElem!_def, h]

theorem u32_ne0 {x : UInt32} : x ≠ 0 ↔ x.toNat ≠ 0 := by
  constructor
  · intro h e; exact h (UInt32.toNat_inj.mp (by rw [e]; rfl))
  · intro h e; rw [e] at h; exact h rfl

theorem St.K_lt {S : Setup} {t : TL} {C : Array Code} {K : Nat} {inb : Bool} (hS : S.OK)
    (hs : St S t C K inb) : K + 2 ^ (16 - t.len.toNat) ≤ 2 ^ 16 := by
  have h1 := wsum_le_of (cnt t.count) (k := t.len.toNat) (m := 15) hs.len_lo (by have := hs.len_hi; have := hS.mx15; omega)
  have h2 := hs.kraft
  have h3 := hS.kraft
  have h4 : 2 ^ (16 - t.len.toNat) ≤ cnt t.count t.len.toNat * 2 ^ (16 - t.len.toNat) :=
    Nat.le_mul_of_pos_left _ hs.cur_pos
  omega

/-- The block number of a code. -/
theorem blk_lt {K r : Nat} (hK : K < 2 ^ 16) (hr : r ≤ 16) : K / 2 ^ (16 - r) < 2 ^ r := by
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, show 16 - r + r = 16 by omega]
  exact hK

/-- The coverage at the start of the loop: nothing written, `K = 0`. -/
theorem cov_init {S : Setup} {t : TL} {C : Array Code} (hd : t.drop = 0) : Cv S t C 0 := by
  have h0 : ∀ i, Wr S t 0 i → False := by
    intro i hw
    rcases hw with ⟨-, h | ⟨h, -⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    all_goals exact absurd hd h
  exact ⟨fun i _ hw => (h0 i hw).elim, Or.inl ⟨hd, Nat.dvd_zero _⟩, fun i _ hw => (h0 i hw).elim⟩

/-- The block facts of the current table in both modes. -/
theorem St.blkP {S : Setup} (hS : S.OK) {t : TL} {C : Array Code} {K : Nat} (hst : St S t C K true) :
    (t.drop = 0 ∧ t.curr.toNat = S.root ∧ t.used.toNat = 2 ^ S.root ∧ t.len.toNat ≤ S.root ∧ K < 2 ^ 16) ∨
    (t.drop ≠ 0 ∧ t.drop.toNat = S.root ∧ S.root < t.len.toNat ∧ S.root + t.curr.toNat ≤ 15 ∧
      2 ^ S.root + 2 ^ t.curr.toNat ≤ t.used.toNat ∧ t.low.toNat < 2 ^ S.root ∧
      K / 2 ^ (16 - S.root) = rev S.root t.low.toNat) := by
  have hK := hst.K_lt hS
  have := Nat.two_pow_pos (16 - t.len.toNat)
  rcases hst.geo with ⟨h1, h2, -, h4, -, h6⟩ | ⟨h1, h2, h3, h4, nx, P, -, h6, h7, h8, h9, -, h11⟩
  · exact Or.inl ⟨h1, h2, h4, h6 rfl, by omega⟩
  · have hr1 := hS.root1
    refine Or.inr ⟨u32_ne0.2 (by omega), h1, h2, h4, by omega, by rw [h9]; exact rev_lt _ _, ?_⟩
    rw [h11 rfl, h9, rev_rev, Nat.mod_eq_of_lt h8]

/-- The entry made for a code of length `L` in a table that drops `d` bits: a sub-table entry with `L - d` code
bits, which are its `bits` in a code length table. -/
def HereOK (type : UInt32) (d L : Nat) (e : Code) : Prop :=
  SubOK type d e ∧ (CODE_BITS e).toNat = L - d ∧ (type = CODES → e.op.toNat &&& 16 = 0)

/-- The weight of the codes not yet entered, split at the current length `l`. -/
theorem wsum_tail {c g : Nat → Nat} {l : Nat} (hl1 : 1 ≤ l) (hb : ∀ L, 1 ≤ L → L < l → g L = 0)
    (ha : ∀ L, l < L → L ≤ 15 → g L = c L) (hle : g l ≤ c l) :
    ∀ n, l ≤ n → n ≤ 15 → wsum c n = wsum g n + wsum c (l - 1) + (c l - g l) * 2 ^ (16 - l) := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
    intro _
    have e1 : wsum c l = wsum c (l - 1) + c l * 2 ^ (16 - l) := by
      have := wsum_succ c (l - 1)
      rwa [show l - 1 + 1 = l by omega, show 15 - (l - 1) = 16 - l by omega] at this
    have e2 : wsum g l = g l * 2 ^ (16 - l) := by
      have := wsum_succ g (l - 1)
      rw [show l - 1 + 1 = l by omega, show 15 - (l - 1) = 16 - l by omega,
        wsum_eq_zero (fun L h1 h2 => hb L h1 (Nat.lt_of_le_of_lt h2 (Nat.sub_lt hl1 Nat.one_pos)))] at this
      omega
    have := Nat.mul_le_mul_right (2 ^ (16 - l)) hle
    simp only [Nat.add_zero]
    rw [e1, e2, Nat.sub_mul]
    omega
  | succ k ih =>
    intro h
    rw [← Nat.add_assoc, wsum_succ, wsum_succ g, ha (l + k + 1) (by omega) h, ih (by omega) (by omega)]
    omega

/-- The current code `K` lies in the interval of the codes of its length. -/
theorem St.kpos {S : Setup} {t : TL} {C : Array Code} {K : Nat} {inb : Bool} (hS : S.OK) (hst : St S t C K inb) :
    wsum S.c0 (t.len.toNat - 1) ≤ K ∧ K + 2 ^ (16 - t.len.toNat) ≤ wsum S.c0 t.len.toNat := by
  have hl1 := hst.len_lo
  have hl2 := hst.len_hi
  have hmx := hS.mx15
  have e := wsum_tail (c := S.c0) (g := cnt t.count) hl1 hst.below hst.above hst.cur_le 15 (by omega) (Nat.le_refl _)
  have hk := hst.kraft
  have e1 := wsum_succ S.c0 (t.len.toNat - 1)
  rw [show t.len.toNat - 1 + 1 = t.len.toNat by omega, show 15 - (t.len.toNat - 1) = 16 - t.len.toNat by omega] at e1
  have h1 := Nat.mul_le_mul_right (2 ^ (16 - t.len.toNat)) hst.cur_le
  have h2 := Nat.mul_le_mul_right (2 ^ (16 - t.len.toNat)) hst.cur_pos
  rw [Nat.sub_mul] at e
  rw [Nat.one_mul] at h2
  omega

/-- The prefix facts of a slot whose entry is kept, when the earlier sub-tables are kept. -/
theorem PreOK.keep {S : Setup} {drop curr used low : UInt32} {C C2 : Array Code} {i : Nat}
    (hp : PreOK S drop curr used low C i) (hi : C2[S.off + i]! = C[S.off + i]!)
    (hk : ∀ q, q < used.toNat - 2 ^ curr.toNat → C2[S.off + q]! = C[S.off + q]!) :
    PreOK S drop curr used low C2 i := by
  obtain ⟨p1, p2⟩ := hp
  refine ⟨fun hr => ?_, fun hd hge => by rw [hi]; exact p2 hd hge⟩
  obtain ⟨q1, q2, q3⟩ := p1 hr
  rw [hi]
  refine ⟨q1, fun hl => (q2 hl).imp id (fun ⟨a, b, c⟩ => ⟨a, b, lvl_congr (fun x hx => ?_) c⟩), q3⟩
  rw [Nat.add_assoc]
  exact hk _ (by omega)

/-- Replicating the entry of the current code `K` (length `len`) in the current table. -/
theorem cov_fill {S : Setup} (hS : S.OK) {t : TL} {C C2 : Array Code} {K : Nat} (hst : St S t C K true)
    (hp : CovPre S) {here : Code} (hhere : HereOK S.type t.drop.toNat t.len.toNat here) {nx : Nat}
    (hnx : nx + 2 ^ t.curr.toNat = t.used.toNat)
    (hF : Fill C C2 (S.off + nx + t.huff.toNat / 2 ^ t.drop.toNat) (2 ^ (t.len.toNat - t.drop.toNat)) 0
      (2 ^ (t.curr.toNat - (t.len.toNat - t.drop.toNat))) (unpackCode (packCode here))) :
    Cv S t C2 (K + 2 ^ (16 - t.len.toNat)) := by
  rw [unpack_pack] at hF
  have hcv := hst.cov hp
  have hK := hst.K_lt hS
  have hdvd := hst.dvd
  have hll := hst.len_le
  have hl1 := hst.len_lo
  have hmx := hS.mx15
  have hrmx := hS.rootmx
  have hr1 := hS.root1
  have hlmx := hst.len_hi
  have hhuff := hst.huff
  have hkp := hst.kpos hS
  have hB := Nat.two_pow_pos (16 - S.root)
  have hBL := Nat.two_pow_pos (16 - t.len.toNat)
  -- the filled slots
  have key : ∀ i, (∀ j, j < 2 ^ (t.curr.toNat - (t.len.toNat - t.drop.toNat)) →
      S.off + i ≠ S.off + nx + t.huff.toNat / 2 ^ t.drop.toNat + j * 2 ^ (t.len.toNat - t.drop.toNat)) →
      C2[S.off + i]! = C[S.off + i]! := fun i hi => getElem!_congr (hF.keep _ (fun j _ hj => hi j hj))
  have hkeep : ∀ q, q < t.used.toNat - 2 ^ t.curr.toNat → C2[S.off + q]! = C[S.off + q]! :=
    fun q hq => key q (fun j _ e => by
      generalize t.huff.toNat / 2 ^ t.drop.toNat = A at e
      generalize j * 2 ^ (t.len.toNat - t.drop.toNat) = B at e
      omega)
  rcases hst.blkP hS with ⟨hd, hc, hu, hlr, hK16⟩ | ⟨hd, hdr, hrl, hrc, hru, hlow, hKP⟩
  · -- the root table
    have hd0 : t.drop.toNat = 0 := by rw [hd]; rfl
    have hnx0 : nx = 0 := by rw [hc, hu] at hnx; omega
    subst hnx0
    rw [hd0] at key hF hhere
    simp only [Nat.pow_zero, Nat.div_one, Nat.sub_zero, Nat.add_zero] at key hF
    have hcase : ∀ i, i < t.used.toNat → Wr S t (K + 2 ^ (16 - t.len.toNat)) i →
        (∃ j, j < 2 ^ (t.curr.toNat - t.len.toNat) ∧ i = t.huff.toNat + j * 2 ^ t.len.toNat ∧
          C2[S.off + i]! = here) ∨ (C2[S.off + i]! = C[S.off + i]! ∧ Wr S t K i) := by
      intro i hi hw
      have hir : i < 2 ^ S.root := by omega
      by_cases hfill : ∃ j, j < 2 ^ (t.curr.toNat - t.len.toNat) ∧ i = t.huff.toNat + j * 2 ^ t.len.toNat
      · obtain ⟨j, hj, rfl⟩ := hfill
        have := hF.set j (Nat.zero_le _) hj
        refine Or.inl ⟨j, hj, rfl, ?_⟩
        rw [← Nat.add_assoc, getElem!_of_some this]
      · refine Or.inr ⟨key i (fun j hj e => hfill ⟨j, hj, by omega⟩), ?_⟩
        rcases hw with ⟨-, h | ⟨h, -⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · by_cases hlt : rev S.root i * 2 ^ (16 - S.root) < K
          · exact Or.inl ⟨hir, Or.inl hlt⟩
          · exfalso
            obtain ⟨j, hj, e⟩ := slot_of_pos (d := 0) (c := S.root) (L := t.len.toNat) (P := 0) (j0 := i)
              (by omega) (by omega) (by omega) hdvd (by rw [Nat.div_eq_of_lt hK16]) hir
              (by simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero]; omega)
              (by simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero]; exact h)
            rw [hc] at hfill
            simp only [Nat.pow_zero, Nat.div_one, Nat.sub_zero] at e
            exact hfill ⟨j, hj, by rw [e, hhuff]⟩
        all_goals exact absurd hd h
    refine ⟨fun i hi hw => ?_, Or.inl ⟨hd, ?_⟩, fun i hi hw => ?_⟩
    · have hir : i < 2 ^ S.root := by omega
      rcases hcase i hi hw with ⟨j, -, -, he⟩ | ⟨he, hw'⟩
      · rw [he]; exact ⟨fun _ => RootOK.of_sub hhere.1, fun h => by omega⟩
      · rw [he]; exact hcv.ok i hi hw'
    · rcases hcv.blk with ⟨-, h⟩ | ⟨h, -⟩
      · exact Nat.dvd_add h (Nat.pow_dvd_pow 2 (by omega))
      · exact absurd hd h
    · have hir : i < 2 ^ S.root := by omega
      rcases hcase i hi hw with ⟨j, hj, rfl, he⟩ | ⟨he, hw'⟩
      · refine ⟨fun _ => ⟨?_, fun hl => (by rw [he, hhere.1.nolink] at hl; cases hl),
          fun hc => (by rw [he]; exact hhere.2.2 hc)⟩, fun h => absurd hd h⟩
        have hpos := pos_of_slot (d := 0) (c := S.root) (L := t.len.toNat) (P := 0) (K := K) (j := j)
          (by omega) (by omega) (by omega) hdvd (by rw [Nat.div_eq_of_lt hK16])
        simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero, Nat.pow_zero, Nat.div_one] at hpos
        rw [← hhuff] at hpos
        rw [he, hhere.2.1]
        exact Or.inl ⟨t.len.toNat, hl1, by omega, by omega, by omega, by omega⟩
      · exact (hcv.pre i hi hw').keep he hkeep
  · -- a sub-table
    have hnxr : 2 ^ S.root ≤ nx := by omega
    rw [hdr] at key hF hhere
    have hKP' : K + 2 ^ (16 - t.len.toNat) ≤ (rev S.root t.low.toNat + 1) * 2 ^ (16 - S.root) := by
      apply dvd_add_le hdvd
      · exact Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega)) _
      · have := Nat.lt_div_mul_add (a := K) hB
        rw [hKP] at this
        rw [Nat.add_mul, Nat.one_mul]; exact this
    have hPK : rev S.root t.low.toNat * 2 ^ (16 - S.root) ≤ K := by
      rw [← hKP]; exact Nat.div_mul_le_self _ _
    have hcase : ∀ i, i < t.used.toNat → Wr S t (K + 2 ^ (16 - t.len.toNat)) i →
        (∃ j, j < 2 ^ (t.curr.toNat - (t.len.toNat - S.root)) ∧
          i = nx + t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root) ∧ C2[S.off + i]! = here) ∨
        (C2[S.off + i]! = C[S.off + i]! ∧ Wr S t K i) := by
      intro i hi hw
      by_cases hfill : ∃ j, j < 2 ^ (t.curr.toNat - (t.len.toNat - S.root)) ∧
          i = nx + t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root)
      · obtain ⟨j, hj, rfl⟩ := hfill
        have := hF.set j (Nat.zero_le _) hj
        refine Or.inl ⟨j, hj, rfl, ?_⟩
        rw [show S.off + (nx + t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root)) =
          S.off + nx + t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root) by omega]
        rw [getElem!_of_some this]
      · refine Or.inr ⟨key i (fun j hj e => hfill ⟨j, hj, by omega⟩), ?_⟩
        rcases hw with ⟨hir, h | h⟩ | h | ⟨-, hge, h⟩
        · by_cases hlt : rev S.root i * 2 ^ (16 - S.root) < K
          · exact Or.inl ⟨hir, Or.inl hlt⟩
          · -- the only root block met by the code is the current one, already linked
            refine Or.inl ⟨hir, Or.inr ⟨hd, ?_⟩⟩
            have h1 : rev S.root t.low.toNat ≤ rev S.root i :=
              Nat.le_of_mul_le_mul_right (by omega) hB
            have h2 : rev S.root i < rev S.root t.low.toNat + 1 :=
              Nat.lt_of_mul_lt_mul_right (a := 2 ^ (16 - S.root)) (by omega)
            exact rev_inj hir hlow (by omega)
        · exact Or.inl ⟨hir, Or.inr h⟩
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ⟨hd, hge, ?_⟩)
          apply Classical.byContradiction
          intro hlt
          have hnxe : t.used.toNat - 2 ^ t.curr.toNat = nx := by omega
          rw [hnxe] at hge h hlt
          obtain ⟨j, hj, e⟩ := slot_of_pos (d := S.root) (c := t.curr.toNat) (L := t.len.toNat)
            (P := rev S.root t.low.toNat) (j0 := i - nx) (by omega) (by omega) (by omega) hdvd hKP (by omega)
            (by omega) h
          rw [hhuff] at hfill
          exact hfill ⟨j, hj, by omega⟩
    refine ⟨fun i hi hw => ?_, Or.inr ⟨hd, by omega, hKP'⟩, fun i hi hw => ?_⟩
    · rcases hcase i hi hw with ⟨j, -, rfl, he⟩ | ⟨he, hw'⟩
      · rw [he]
        exact ⟨fun h => absurd h (Nat.not_lt.2 (Nat.le_trans hnxr (Nat.le_trans (Nat.le_add_right nx _)
          (Nat.le_add_right _ _)))), fun _ => hhere.1⟩
      · rw [he]; exact hcv.ok i hi hw'
    · rcases hcase i hi hw with ⟨j, hj, rfl, he⟩ | ⟨he, hw'⟩
      · refine ⟨fun h => absurd h (Nat.not_lt.2 (Nat.le_trans hnxr (Nat.le_trans (Nat.le_add_right nx _)
          (Nat.le_add_right _ _)))), fun _ _ => ?_⟩
        have hpos := pos_of_slot (d := S.root) (c := t.curr.toNat) (L := t.len.toNat) (P := rev S.root t.low.toNat)
          (K := K) (j := j) (by omega) (by omega) (by omega) hdvd hKP
        rw [← hhuff] at hpos
        rw [show nx + t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root) - (t.used.toNat - 2 ^ t.curr.toNat) =
          t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root) by omega, he, hhere.2.1]
        exact Or.inl ⟨t.len.toNat, hl1, by omega, by omega, by omega, by omega⟩
      · exact (hcv.pre i hi hw').keep he hkeep

/-- Opening the sub-table for the block of `K`: the root slot `low` is linked to it, the previous sub-table (if
any) is complete, and the new one is still empty. -/
theorem cov_link {S : Setup} (hS : S.OK) {t1 t2 : TL} {C C3 : Array Code} {K : Nat} {inb : Bool}
    (hst : St S t1 C K inb) (hp : CovPre S)
    (hd2 : t2.drop.toNat = S.root) (hcu1 : 1 ≤ t2.curr.toNat) (hcu : S.root + t2.curr.toNat ≤ 15)
    (hu2 : t2.used.toNat = t1.used.toNat + 2 ^ t2.curr.toNat)
    (hlow : t2.low.toNat = rev S.root (K / 2 ^ (16 - S.root))) (hne : t2.low ≠ t1.low)
    (hlr : S.root < t1.len.toNat)
    (hC : ∀ j, j ≠ S.off + t2.low.toNat → C3[j]! = C[j]!)
    (he : (C3[S.off + t2.low.toNat]!).op.toNat = t2.curr.toNat ∧ (C3[S.off + t2.low.toNat]!).bits.toNat = S.root ∧
      (C3[S.off + t2.low.toNat]!).val.toNat = t1.used.toNat) :
    Cv S t2 C3 K := by
  have hcv := hst.cov hp
  have hK := hst.K_lt hS
  have hmx := hS.mx15
  have hrmx := hS.rootmx
  have hr1 := hS.root1
  have hB := Nat.two_pow_pos (16 - S.root)
  have hKl : K < 2 ^ 16 := by have := Nat.two_pow_pos (16 - t1.len.toNat); omega
  have hP2 : K / 2 ^ (16 - S.root) < 2 ^ S.root := blk_lt hKl (by omega)
  have hl2 : t2.low.toNat < 2 ^ S.root := by rw [hlow]; exact rev_lt _ _
  have hrl2 : rev S.root t2.low.toNat = K / 2 ^ (16 - S.root) := by rw [hlow, rev_rev, Nat.mod_eq_of_lt hP2]
  have hd2' : t2.drop ≠ 0 := u32_ne0.2 (by omega)
  -- the old tables: `K` is at the start of its block, and every slot of the old region before `K` is written
  have hold : K / 2 ^ (16 - S.root) * 2 ^ (16 - S.root) = K ∧ 2 ^ S.root ≤ t1.used.toNat ∧
      ∀ i, i < t1.used.toNat → 2 ^ S.root ≤ i → Wr S t1 K i := by
    rcases hst.geo with ⟨h1, h2, -, h4, -⟩ | ⟨h1, -, -, h4, nx, P, -, h6, h7, h8, h9, -⟩
    · refine ⟨?_, by omega, fun i h1 h2 => by omega⟩
      rcases hcv.blk with ⟨-, hdv⟩ | ⟨h, -⟩
      · exact Nat.div_mul_cancel hdv
      · exact absurd h1 h
    · have hrP : rev S.root t1.low.toNat = P := by rw [h9, rev_rev, Nat.mod_eq_of_lt h8]
      rcases hcv.blk with ⟨h, -⟩ | ⟨hd1, hb1, hb2⟩
      · exfalso; rw [h] at h1; simp at h1; omega
      rw [hrP] at hb1 hb2
      have hKe : K = (P + 1) * 2 ^ (16 - S.root) := by
        apply Classical.byContradiction
        intro hlt
        have hlt' : K < (P + 1) * 2 ^ (16 - S.root) := by omega
        have hq : K / 2 ^ (16 - S.root) = P := by
          exact Nat.div_eq_of_lt_le hb1 hlt'
        apply hne
        apply UInt32.toNat_inj.mp
        rw [hlow, hq, h9]
      have := Nat.two_pow_pos t1.curr.toNat
      refine ⟨by rw [hKe, Nat.mul_div_cancel _ hB], by omega, fun i hi hri => ?_⟩
      by_cases hlt : i < t1.used.toNat - 2 ^ t1.curr.toNat
      · exact Or.inr (Or.inl ⟨hd1, hri, hlt⟩)
      · refine Or.inr (Or.inr ⟨hd1, by omega, ?_⟩)
        rw [hrP, hKe, Nat.add_mul, Nat.one_mul]
        have hr := rev_lt t1.curr.toNat (i - (t1.used.toNat - 2 ^ t1.curr.toNat))
        have hsplit : 2 ^ (16 - S.root) = 2 ^ t1.curr.toNat * 2 ^ (16 - S.root - t1.curr.toNat) := by
          rw [← Nat.pow_add]; congr 1; omega
        have : rev t1.curr.toNat (i - (t1.used.toNat - 2 ^ t1.curr.toNat)) * 2 ^ (16 - S.root - t1.curr.toNat) <
            2 ^ (16 - S.root) := by
          rw [hsplit]; exact Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
        omega
  obtain ⟨hKb, hur, hsub⟩ := hold
  have hw1 : ∀ i, i < t2.used.toNat → Wr S t2 K i → i ≠ t2.low.toNat → i < t1.used.toNat ∧ Wr S t1 K i := by
    intro i hi hw hil
    rcases hw with ⟨hir, h | ⟨-, h⟩⟩ | ⟨-, hri, h⟩ | ⟨-, hge, h⟩
    · exact ⟨by omega, Or.inl ⟨hir, Or.inl h⟩⟩
    · exact absurd h hil
    · rw [hu2, Nat.add_sub_cancel] at h; exact ⟨h, hsub i h hri⟩
    · exfalso
      rw [hrl2] at h
      have := Nat.div_mul_le_self K (2 ^ (16 - S.root))
      omega
  refine ⟨fun i hi hw => ?_, Or.inr ⟨hd2', by rw [hrl2]; exact Nat.le_of_eq hKb, by rw [hrl2, Nat.add_mul, Nat.one_mul]; omega⟩,
    fun i hi hw => ?_⟩
  · by_cases hil : i = t2.low.toNat
    · subst hil
      obtain ⟨e1, e2, e3⟩ := he
      have := Nat.two_pow_pos t2.curr.toNat
      exact ⟨fun _ => root_link e1 hcu1 (by omega) e2 hr1 (by omega) (by omega) (by omega), fun h => by omega⟩
    · rw [hC _ (by omega)]
      obtain ⟨h1, h2⟩ := hw1 i hi hw hil
      exact (hcv.ok i h1 h2).mono (by rw [hu2]; exact Nat.le_add_right _ _)
  · by_cases hil : i = t2.low.toNat
    · subst hil
      obtain ⟨e1, e2, e3⟩ := he
      have hkp := hst.kpos hS
      have hlh := hst.len_hi
      have hnc : S.type ≠ CODES := fun hc => by
        rcases hS.kind with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · omega
        · rw [hc] at h; exact absurd h (by decide)
        · rw [hc] at h; exact absurd h (by decide)
      refine ⟨fun _ => ⟨?_, fun _ => Or.inl ⟨hd2', rfl, e1, by rw [e3, hu2]⟩, fun hc => absurd hc hnc⟩,
        fun _ h => absurd h (by rw [hu2, Nat.add_sub_cancel]; exact Nat.not_le.2 (Nat.lt_of_lt_of_le hl2 hur))⟩
      have hcb : (CODE_BITS C3[S.off + t2.low.toNat]!).toNat = S.root := by
        rw [codeBits_of (by rw [e1]; exact (nat_bits_small _ (by omega)).1), e2]
      rw [hcb, hrl2, hKb]
      have := Nat.two_pow_pos (16 - t1.len.toNat)
      exact Or.inl ⟨t1.len.toNat, hst.len_lo, by omega, hkp.1, by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := hw1 i hi hw hil
      have hCi := hC (S.off + i) (by omega)
      have hk3 : ∀ q, 2 ^ S.root ≤ q → C3[S.off + q]! = C[S.off + q]! := fun q hq => hC _ (by omega)
      obtain ⟨p1, -⟩ := hcv.pre i h1 h2
      refine ⟨fun hir => ?_, fun _ h => absurd h (by rw [hu2, Nat.add_sub_cancel]; exact Nat.not_le.2 h1)⟩
      obtain ⟨q1, q2, q3⟩ := p1 hir
      rw [hCi]
      refine ⟨q1, fun hl => Or.inr ?_, q3⟩
      have hreg : ∀ (v k : Nat), 2 ^ S.root ≤ v → Lvl C (S.off + v) k → Lvl C3 (S.off + v) k :=
        fun v k hv hL => lvl_congr (fun x _ => by rw [Nat.add_assoc]; exact hk3 _ (by omega)) hL
      rcases q2 hl with ⟨hd1, hi1, eop, eval⟩ | ⟨g1, g2, g3⟩
      · -- the link of the previous sub-table, now complete
        rcases hst.geo with ⟨h0, -⟩ | ⟨hdr1, -, hcu1', hrc1, nx, P, -, hnxr, hnx, -, -, -, -⟩
        · exact absurd h0 hd1
        have hval : C[S.off + i]!.val.toNat = t1.used.toNat - 2 ^ t1.curr.toNat := by omega
        refine ⟨by omega, by rw [eop]; omega, hreg _ _ (by omega) ?_⟩
        rw [eop]
        refine lvl_of_pos (d := S.root) (Pb := rev S.root t1.low.toNat * 2 ^ (16 - S.root)) (c := S.c0) (by omega)
          (Nat.dvd_mul_left _ _) (fun m hm => ?_)
        have hq := (hcv.pre (C[S.off + i]!.val.toNat + m) (by omega)
          (hsub _ (by omega) (by omega))).2 hd1 (by omega)
        rw [show C[S.off + i]!.val.toNat + m - (t1.used.toNat - 2 ^ t1.curr.toNat) = m by omega,
          ← Nat.add_assoc] at hq
        exact hq
      · exact ⟨g1, by rw [hu2, Nat.add_sub_cancel]; exact Nat.le_trans g2 (Nat.sub_le _ _), hreg _ _ g1 g3⟩

/-- After the last code of a complete code (`K = 2 ^ 16`) every slot of the used region is written. -/
theorem wr_all {S : Setup} (hS : S.OK) {t : TL} {C : Array Code} {K : Nat} (hst : St S t C K true) :
    ∀ i, i < t.used.toNat → Wr S t (2 ^ 16) i := by
  intro i hi
  have hmx := hS.mx15
  have hrmx := hS.rootmx
  have hroot : ∀ j, j < 2 ^ S.root → rev S.root j * 2 ^ (16 - S.root) < 2 ^ 16 := by
    intro j _
    have := rev_lt S.root j
    have e : 2 ^ (16 : Nat) = 2 ^ S.root * 2 ^ (16 - S.root) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e]; exact Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
  rcases hst.blkP hS with ⟨hd, hc, hu, -, -⟩ | ⟨hd, hdr, hrl, hrc, hru, hlow, -⟩
  · exact Or.inl ⟨by omega, Or.inl (hroot i (by omega))⟩
  · by_cases h1 : i < 2 ^ S.root
    · exact Or.inl ⟨h1, Or.inl (hroot i h1)⟩
    by_cases h2 : i < t.used.toNat - 2 ^ t.curr.toNat
    · exact Or.inr (Or.inl ⟨hd, by omega, h2⟩)
    refine Or.inr (Or.inr ⟨hd, by omega, ?_⟩)
    have hr := rev_lt t.curr.toNat (i - (t.used.toNat - 2 ^ t.curr.toNat))
    have hP := rev_lt S.root t.low.toNat
    have hsplit : 2 ^ (16 - S.root) = 2 ^ t.curr.toNat * 2 ^ (16 - S.root - t.curr.toNat) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h3 : rev t.curr.toNat (i - (t.used.toNat - 2 ^ t.curr.toNat)) * 2 ^ (16 - S.root - t.curr.toNat) <
        2 ^ (16 - S.root) := by
      rw [hsplit]; exact Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
    have h4 : (rev S.root t.low.toNat + 1) * 2 ^ (16 - S.root) ≤ 2 ^ S.root * 2 ^ (16 - S.root) :=
      Nat.mul_le_mul_right _ hP
    have e : 2 ^ (16 : Nat) = 2 ^ S.root * 2 ^ (16 - S.root) := by rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.add_mul, Nat.one_mul] at h4
    omega

/-! ## The entry of the current code -/

/-- The code bits `len - drop` of the current entry. -/
theorem St.cbf {S : Setup} (hS : S.OK) {t : TL} {C : Array Code} {K : Nat} (hst : St S t C K true) :
    ((t.len - t.drop).toUInt8).toNat = t.len.toNat - t.drop.toNat ∧ t.drop.toNat < t.len.toNat ∧
      t.len.toNat ≤ 15 := by
  have hmx := hS.mx15
  have hl := hst.len_hi
  have hl1 := hst.len_lo
  have hdl : t.drop.toNat < t.len.toNat := by
    rcases hst.blkP hS with ⟨hd, -⟩ | ⟨-, hd, h, -⟩
    · rw [hd]; exact hl1
    · omega
  refine ⟨?_, hdl, by omega⟩
  rw [UInt32.toNat_toUInt8, u32_sub (by omega)]
  omega

theorem here_lit {type : UInt32} {d L : Nat} {cb : UInt8} {here : Code}
    (hcb : cb.toNat = L - d ∧ d < L ∧ L ≤ 15) (hop : here.op = 0) (hbits : here.bits = cb)
    (hd : dOf type = false) : HereOK type d L here :=
  ⟨sub_lit hop (by rw [hbits]; omega) (by rw [hbits]; omega) hd,
    by rw [codeBits_of (by rw [hop]; rfl), hbits]; exact hcb.1, fun _ => by rw [hop]; rfl⟩

theorem here_eob {type : UInt32} {d L : Nat} {cb : UInt8} {here : Code}
    (hcb : cb.toNat = L - d ∧ d < L ∧ L ≤ 15) (hop : here.op = 32 + 64) (hbits : here.bits = cb) :
    HereOK type d L here := by
  have h : here.op.toNat = 96 := by rw [hop]; rfl
  exact ⟨sub_inv (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [hbits]; omega)
    (by rw [hbits]; omega), by rw [codeBits_of (by rw [h]; decide), hbits]; exact hcb.1, fun _ => by rw [h]; decide⟩

theorem here_len {type : UInt32} {d L : Nat} {cb : UInt8} {here : Code} {ext base : UInt16}
    (hcb : cb.toNat = L - d ∧ d < L ∧ L ≤ 15) (hop : here.op = COMBINE_OP ext.toUInt32 cb)
    (hbits : here.bits = COMBINE_BITS cb ext.toUInt32) (hval : here.val = base)
    (he1 : 16 ≤ ext.toNat) (he2 : ext.toNat < 32) (hb : 1 ≤ base.toNat) (hsum : L + (ext.toNat - 16) ≤ mOf type)
    (hlen : dOf type = false → L + (ext.toNat - 16) ≤ 20 ∧ base.toNat + 2 ^ (ext.toNat - 16) ≤ 259)
    (hty : type ≠ CODES) : HereOK type d L here := by
  obtain ⟨c1, c2⟩ := comb_len ext.toUInt32 cb (by rw [UInt16.toNat_toUInt32]; exact he1)
    (by rw [UInt16.toNat_toUInt32]; exact he2) (by omega)
  rw [UInt16.toNat_toUInt32] at c2
  have hop' : here.op.toNat = 16 + (L - d) := by rw [hop, c1, hcb.1]
  obtain ⟨b16, b15, -⟩ := nat_bits_len (L - d) (by omega)
  refine ⟨sub_len (cb := L - d) (x := ext.toNat - 16) hop' (by omega) (by omega)
    (by rw [hbits, c2, hcb.1]) (by omega) (by rw [hval]; exact hb) (fun h => ?_),
    by rw [codeBits_len (by rw [hop', b16]; omega), hop', b15], fun h => absurd h hty⟩
  obtain ⟨h1, h2⟩ := hlen h
  exact ⟨by omega, by rw [hval]; exact h2⟩

theorem here_d64 {type : UInt32} {d L : Nat} {cb : UInt8} {here : Code} {ext : UInt16}
    (hcb : cb.toNat = L - d ∧ d < L ∧ L ≤ 15) (hop : here.op = COMBINE_OP ext.toUInt32 cb)
    (hbits : here.bits = COMBINE_BITS cb ext.toUInt32) (hext : ext = 64) : HereOK type d L here := by
  subst hext
  obtain ⟨c1, c2⟩ := comb_64 cb
  rw [show (64 : UInt16).toUInt32 = 64 from rfl] at hop hbits
  have h : here.op.toNat = 64 := by rw [hop]; exact congrArg UInt8.toNat c1
  exact ⟨sub_inv (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [hbits, c2]; omega)
    (by rw [hbits, c2]; omega), by rw [codeBits_of (by rw [h]; decide), hbits, c2]; exact hcb.1,
    fun _ => by rw [h]; decide⟩

/-! ## The finished table -/

/-- A region whose slots all satisfy `SlotOK` is a decoding table. -/
theorem codeTable_of {type : UInt32} {C : Array Code} {off u root : Nat} (hr1 : 1 ≤ root) (hr15 : root ≤ 15)
    (hru : 2 ^ root ≤ u) (hsz : off + u ≤ C.size)
    (hall : ∀ i, i < u → SlotOK type root u i C[off + i]!) :
    InflateTab.CodeTable C off (off + u) root (mOf type) (dOf type) := by
  have hall' : ∀ j, off ≤ j → j < off + u → SlotOK type root u (j - off) C[j]! := by
    intro j h1 h2
    have := hall (j - off) (by omega)
    rwa [show off + (j - off) = j by omega] at this
  refine ⟨hr1, hr15, by omega, hsz, fun j h1 h2 => ?_, fun hd j h1 h2 => ?_, fun j h1 h2 hl => ?_,
    fun j h1 h2 hl => ?_⟩
  · obtain ⟨hR, hS⟩ := hall' j h1 h2
    by_cases hi : j - off < 2 ^ root
    · exact (hR hi).ent
    · exact (hS (by omega)).ent
  · exact ((hall' j h1 (by omega)).1 (by omega)).len hd
  · obtain ⟨hR, hS⟩ := hall' j h1 h2
    have hi : j - off < 2 ^ root := by
      apply Classical.byContradiction
      intro hi
      rw [(hS (by omega)).nolink] at hl; cases hl
    obtain ⟨hb, hv, hvu⟩ := (hR hi).link hl
    refine ⟨by omega, fun k hk => ?_⟩
    have hsub := (hall' (off + C[j]!.val.toNat + k) (by omega) (by omega)).2 (by omega)
    exact ⟨by rw [hb]; exact hsub.sum, hsub.nolink, fun hd => by rw [hb]; exact hsub.len hd⟩
  · obtain ⟨hR, hS⟩ := hall' j h1 h2
    have hi : j - off < 2 ^ root := by
      apply Classical.byContradiction
      intro hi
      rw [(hS (by omega)).nolink] at hl; cases hl
    exact ((hR hi).link hl).1

/-- A finished table whose slots all have their prefix facts is a prefix code (`Rep`). -/
theorem rep_of_pre {S : Setup} (hS : S.OK) {drop curr used low : UInt32} {C : Array Code}
    (hru : 2 ^ S.root ≤ used.toNat)
    (hrc : drop ≠ 0 → S.root + curr.toNat ≤ 15 ∧ 2 ^ S.root + 2 ^ curr.toNat ≤ used.toNat)
    (hall : ∀ i, i < used.toNat → PreOK S drop curr used low C i) :
    InfbackLoop.Rep C S.off S.root (dOf S.type) := by
  have hr15 : S.root ≤ 15 := by have := hS.rootmx; have := hS.mx15; omega
  refine ⟨lvl_of_pos (d := 0) (Pb := 0) (c := S.c0) (by omega) (Nat.dvd_zero _) (fun x hx => ?_), fun j hj hl => ?_⟩
  · have := ((hall x (Nat.lt_of_lt_of_le hx hru)).1 hx).1
    simpa only [Nat.zero_add, Nat.sub_zero, Nat.add_zero] using this
  · rcases ((hall j (Nat.lt_of_lt_of_le hj hru)).1 hj).2.1 hl with ⟨hd, -, eop, eval⟩ | ⟨-, -, h3⟩
    · obtain ⟨hrc1, hrc2⟩ := hrc hd
      rw [eop]
      refine lvl_of_pos (d := S.root) (Pb := rev S.root low.toNat * 2 ^ (16 - S.root)) (c := S.c0) (by omega)
        (Nat.dvd_mul_left _ _) (fun m hm => ?_)
      have hq := (hall (C[S.off + j]!.val.toNat + m) (by omega)).2 hd (by omega)
      rw [show C[S.off + j]!.val.toNat + m - (used.toNat - 2 ^ curr.toNat) = m by omega, ← Nat.add_assoc] at hq
      exact hq
    · exact h3

/-- An invalid-code marker (`op = 64`, `val = 0`) of `bits` bits. -/
theorem marker_ok {type : UInt32} {d : Nat} {bits : UInt8} (h1 : 1 ≤ bits.toNat) (h2 : d + bits.toNat ≤ 20) :
    SubOK type d ⟨bits, 64, 0⟩ :=
  sub_inv (show (64 : UInt8).toNat &&& 16 = 0 by decide) (show (64 : UInt8).toNat &&& 64 ≠ 0 by decide)
    (show (64 : UInt8).toNat &&& 240 ≠ 0 by decide) h1 h2

/-- In a finished code length table (`CODES`) whose slots have their prefix facts, the root entries have
`op & 16` clear (their code bits are their `bits`). -/
theorem codes_op_of_pre {S : Setup} {drop curr used low : UInt32} {C : Array Code} (hc : S.type = CODES)
    (hru : 2 ^ S.root ≤ used.toNat) (hall : ∀ i, i < used.toNat → PreOK S drop curr used low C i) :
    ∀ j, j < 2 ^ S.root → C[S.off + j]!.op.toNat &&& 16 = 0 :=
  fun j hj => ((hall j (Nat.lt_of_lt_of_le hj hru)).1 hj).2.2 hc

/-- Two invalid-code markers of one bit (the table of an empty code) are a prefix code. -/
theorem rep_markers {C : Array Code} {off : Nat} {dist : Bool} (h : ∀ x, x < 2 → C[off + x]! = ⟨1, 64, 0⟩) :
    InfbackLoop.Rep C off 1 dist := by
  refine ⟨fun x x' hx hx' _ => ?_, fun j hj hl => ?_⟩
  · rw [h x hx, h x' hx']
    exact ⟨by decide, fun _ => rfl⟩
  · rw [h j hj, linkTest_false (by decide)] at hl
    cases hl

theorem set!_self {C : Array Code} {k : Nat} (h : k < C.size) (v : Code) : (C.set! k v)[k]? = some v := by
  simp [Array.set!_eq_setIfInBounds, h]

end ZlibNgF.Proof.Inftrees
