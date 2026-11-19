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
  refine ⟨fun i _ hw => ?_, Or.inl ⟨hd, Nat.dvd_zero _⟩⟩
  rcases hw with ⟨-, h | ⟨h, -⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · omega
  all_goals exact absurd hd h

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

/-- Replicating the entry of the current code `K` (length `len`) in the current table. -/
theorem cov_fill {S : Setup} (hS : S.OK) {t : TL} {C C2 : Array Code} {K : Nat} (hst : St S t C K true)
    (hp : CovPre S) {here : Code} (hhere : SubOK S.type t.drop.toNat here) {nx : Nat}
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
  have hB := Nat.two_pow_pos (16 - S.root)
  have hBL := Nat.two_pow_pos (16 - t.len.toNat)
  -- the filled slots
  have key : ∀ i, (∀ j, j < 2 ^ (t.curr.toNat - (t.len.toNat - t.drop.toNat)) →
      S.off + i ≠ S.off + nx + t.huff.toNat / 2 ^ t.drop.toNat + j * 2 ^ (t.len.toNat - t.drop.toNat)) →
      C2[S.off + i]! = C[S.off + i]! := fun i hi => getElem!_congr (hF.keep _ (fun j _ hj => hi j hj))
  rcases hst.blkP hS with ⟨hd, hc, hu, hlr, hK16⟩ | ⟨hd, hdr, hrl, hrc, hru, hlow, hKP⟩
  · -- the root table
    have hd0 : t.drop.toNat = 0 := by rw [hd]; rfl
    have hnx0 : nx = 0 := by rw [hc, hu] at hnx; omega
    subst hnx0
    rw [hd0] at key hF hhere
    simp only [Nat.pow_zero, Nat.div_one, Nat.sub_zero, Nat.add_zero] at key hF
    refine ⟨fun i hi hw => ?_, Or.inl ⟨hd, ?_⟩⟩
    · have hir : i < 2 ^ S.root := by omega
      by_cases hfill : ∃ j, j < 2 ^ (t.curr.toNat - t.len.toNat) ∧ i = t.huff.toNat + j * 2 ^ t.len.toNat
      · obtain ⟨j, hj, rfl⟩ := hfill
        have := hF.set j (Nat.zero_le _) hj
        rw [← Nat.add_assoc]
        rw [getElem!_of_some this]
        exact ⟨fun _ => RootOK.of_sub hhere, fun h => by omega⟩
      · rw [key i (fun j hj e => hfill ⟨j, hj, by omega⟩)]
        refine hcv.ok i hi ?_
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
    · rcases hcv.blk with ⟨-, h⟩ | ⟨h, -⟩
      · exact Nat.dvd_add h (Nat.pow_dvd_pow 2 (by omega))
      · exact absurd hd h
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
    refine ⟨fun i hi hw => ?_, Or.inr ⟨hd, by omega, hKP'⟩⟩
    by_cases hfill : ∃ j, j < 2 ^ (t.curr.toNat - (t.len.toNat - S.root)) ∧
        i = nx + t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root)
    · obtain ⟨j, hj, rfl⟩ := hfill
      have := hF.set j (Nat.zero_le _) hj
      rw [show S.off + (nx + t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root)) =
        S.off + nx + t.huff.toNat / 2 ^ S.root + j * 2 ^ (t.len.toNat - S.root) by omega]
      rw [getElem!_of_some this]
      exact ⟨fun h => absurd h (Nat.not_lt.2 (Nat.le_trans hnxr (Nat.le_trans (Nat.le_add_right nx _)
        (Nat.le_add_right _ _)))), fun _ => hhere⟩
    · rw [key i (fun j hj e => hfill ⟨j, hj, by omega⟩)]
      refine hcv.ok i hi ?_
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

/-- Opening the sub-table for the block of `K`: the root slot `low` is linked to it, the previous sub-table (if
any) is complete, and the new one is still empty. -/
theorem cov_link {S : Setup} (hS : S.OK) {t1 t2 : TL} {C C3 : Array Code} {K : Nat} {inb : Bool}
    (hst : St S t1 C K inb) (hp : CovPre S)
    (hd2 : t2.drop.toNat = S.root) (hcu1 : 1 ≤ t2.curr.toNat) (hcu : S.root + t2.curr.toNat ≤ 15)
    (hu2 : t2.used.toNat = t1.used.toNat + 2 ^ t2.curr.toNat)
    (hlow : t2.low.toNat = rev S.root (K / 2 ^ (16 - S.root))) (hne : t2.low ≠ t1.low)
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
  refine ⟨fun i hi hw => ?_, Or.inr ⟨hd2', by rw [hrl2]; exact Nat.le_of_eq hKb, by rw [hrl2, Nat.add_mul, Nat.one_mul]; omega⟩⟩
  by_cases hil : i = t2.low.toNat
  · subst hil
    obtain ⟨e1, e2, e3⟩ := he
    have := Nat.two_pow_pos t2.curr.toNat
    exact ⟨fun _ => root_link e1 hcu1 (by omega) e2 hr1 (by omega) (by omega) (by omega), fun h => by omega⟩
  · rw [hC _ (by omega)]
    have hw1 : i < t1.used.toNat ∧ Wr S t1 K i := by
      rcases hw with ⟨hir, h | ⟨-, h⟩⟩ | ⟨-, hri, h⟩ | ⟨-, hge, h⟩
      · exact ⟨by omega, Or.inl ⟨hir, Or.inl h⟩⟩
      · exact absurd h hil
      · rw [hu2, Nat.add_sub_cancel] at h; exact ⟨h, hsub i h hri⟩
      · exfalso
        rw [hrl2] at h
        have := Nat.div_mul_le_self K (2 ^ (16 - S.root))
        omega
    exact (hcv.ok i hw1.1 hw1.2).mono (by rw [hu2]; exact Nat.le_add_right _ _)

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
    (hd : dOf type = false) : SubOK type d here :=
  sub_lit hop (by rw [hbits]; omega) (by rw [hbits]; omega) hd

theorem here_eob {type : UInt32} {d L : Nat} {cb : UInt8} {here : Code}
    (hcb : cb.toNat = L - d ∧ d < L ∧ L ≤ 15) (hop : here.op = 32 + 64) (hbits : here.bits = cb) :
    SubOK type d here := by
  have h : here.op.toNat = 96 := by rw [hop]; rfl
  exact sub_inv (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [hbits]; omega)
    (by rw [hbits]; omega)

theorem here_len {type : UInt32} {d L : Nat} {cb : UInt8} {here : Code} {ext base : UInt16}
    (hcb : cb.toNat = L - d ∧ d < L ∧ L ≤ 15) (hop : here.op = COMBINE_OP ext.toUInt32 cb)
    (hbits : here.bits = COMBINE_BITS cb ext.toUInt32) (hval : here.val = base)
    (he1 : 16 ≤ ext.toNat) (he2 : ext.toNat < 32) (hb : 1 ≤ base.toNat) (hsum : L + (ext.toNat - 16) ≤ mOf type)
    (hlen : dOf type = false → L + (ext.toNat - 16) ≤ 20 ∧ base.toNat + 2 ^ (ext.toNat - 16) ≤ 259) :
    SubOK type d here := by
  obtain ⟨c1, c2⟩ := comb_len ext.toUInt32 cb (by rw [UInt16.toNat_toUInt32]; exact he1)
    (by rw [UInt16.toNat_toUInt32]; exact he2) (by omega)
  rw [UInt16.toNat_toUInt32] at c2
  refine sub_len (cb := L - d) (x := ext.toNat - 16) (by rw [hop, c1, hcb.1]) (by omega) (by omega)
    (by rw [hbits, c2, hcb.1]) (by omega) (by rw [hval]; exact hb) (fun h => ?_)
  obtain ⟨h1, h2⟩ := hlen h
  exact ⟨by omega, by rw [hval]; exact h2⟩

theorem here_d64 {type : UInt32} {d L : Nat} {cb : UInt8} {here : Code} {ext : UInt16}
    (hcb : cb.toNat = L - d ∧ d < L ∧ L ≤ 15) (hop : here.op = COMBINE_OP ext.toUInt32 cb)
    (hbits : here.bits = COMBINE_BITS cb ext.toUInt32) (hext : ext = 64) : SubOK type d here := by
  subst hext
  obtain ⟨c1, c2⟩ := comb_64 cb
  rw [show (64 : UInt16).toUInt32 = 64 from rfl] at hop hbits
  have h : here.op.toNat = 64 := by rw [hop]; exact congrArg UInt8.toNat c1
  exact sub_inv (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [hbits, c2]; omega)
    (by rw [hbits, c2]; omega)

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
  refine ⟨hr1, hr15, by omega, hsz, fun j h1 h2 => ?_, fun hd j h1 h2 => ?_, fun j h1 h2 hl => ?_⟩
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

/-- An invalid-code marker (`op = 64`, `val = 0`) of `bits` bits. -/
theorem marker_ok {type : UInt32} {d : Nat} {bits : UInt8} (h1 : 1 ≤ bits.toNat) (h2 : d + bits.toNat ≤ 20) :
    SubOK type d ⟨bits, 64, 0⟩ :=
  sub_inv (show (64 : UInt8).toNat &&& 16 = 0 by decide) (show (64 : UInt8).toNat &&& 64 ≠ 0 by decide)
    (show (64 : UInt8).toNat &&& 240 ≠ 0 by decide) h1 h2

theorem set!_self {C : Array Code} {k : Nat} (h : k < C.size) (v : Code) : (C.set! k v)[k]? = some v := by
  simp [Array.set!_eq_setIfInBounds, h]

end ZlibNgF.Proof.Inftrees
