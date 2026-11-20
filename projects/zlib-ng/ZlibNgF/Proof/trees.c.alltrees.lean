import ZlibNgF.Proof.«trees.c.blt»

/-!
# `send_all_trees` (`ZlibNgF`)

On `SH` heaps: `send_all_trees(s, lcodes, dcodes, blcodes)` sends `5 + 5 + 4` bits of counts, `3` bits per
bit-length code length in `bl_order`, then the two trees with `send_tree`: exactly
`14 + 3 * blcodes + (bits of treeTokens of the literal/length tree) + (bits of treeTokens of the distance tree)` bits,
every 8-byte store below `pbo + Lim` when that many bits and one store fit.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesAllTrees
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesHeader ZlibNgF.Proof.TreesSendTree ZlibNgF.Proof.TreesEmitP ZlibNgF.Proof.TreesBlt
open ZlibNgF.Math.Huff ZlibNgF.Proof.DeflateBits
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- Bits sent after a first part that left `np` pending bytes and `bv` bits. -/
theorem SendPost.cat {pbo e1 e2 : Nat} {np : UInt32} {bb : UInt64} {bv : UInt32} {d' : Array UInt8} {H2 : Heap}
    (w : WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d') (hle : st.pending.toNat ≤ np.toNat)
    (hacc : 8 * np.toNat + bv.toNat = 8 * st.pending.toNat + st.bi_valid.toInt.toNat + e1) (hbv : bv.toNat < 64)
    (q : SendPost H i z b { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 } d' pbo e2 H2) :
    SendPost H i z b st d pbo (e1 + e2) H2 := by
  obtain ⟨np2, bb2, bv2, d2, rfl, w2, hle2, hacc2, hbv2⟩ := q
  dsimp only at w2 hle2 hacc2
  have hv := toInt32_toInt bv hbv
  rw [hv] at hacc2
  refine ⟨np2, bb2, bv2, d2, rfl, ?_, by omega, by simp only [Int.toNat_natCast] at hacc2; omega, hbv2⟩
  exact (w.widen (Nat.le_refl _) (by omega)).trans (w2.widen (by omega) (Nat.le_refl _)) (Nat.le_refl _) (Nat.le_refl _)

/-- What `send_all_trees` needs of the state: literal/length and distance trees with guards, `bl_tree` lengths at
most 7. -/
structure SatPre (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo Lim mL mD nb : Nat) : Prop where
  hpb : st.pending_buf = .val (.ref (.heap b) pbo)
  hLim : pbo + Lim ≤ d.size
  hL32 : Lim < 2 ^ 31
  hbl : 19 ≤ st.bl_tree.size
  h7 : ∀ t, t < 19 → (st.bl_tree[t]!).dl.toNat ≤ 7
  mL1 : 1 ≤ mL
  mL2 : mL ≤ 286
  mD1 : 1 ≤ mD
  mD2 : mD ≤ 30
  nb1 : 4 ≤ nb
  nb2 : nb ≤ 19
  lsize : mL < st.dyn_ltree.size
  dsize : mD < st.dyn_dtree.size
  lg : (st.dyn_ltree[mL]!).dl = 0xffff
  dg : (st.dyn_dtree[mD]!).dl = 0xffff
  l15 : ∀ n, n < mL → lenOf st.dyn_ltree n ≤ 15
  d15 : ∀ n, n < mD → lenOf st.dyn_dtree n ≤ 15
  v0 : 0 ≤ st.bi_valid.toInt
  v64 : st.bi_valid.toInt < 64

/-- The bits of `send_all_trees`. -/
noncomputable def satBits (st : DeflateState) (mL mD nb : Nat) : Nat :=
  14 + 3 * nb + tokBits st.bl_tree (treeTokens (lenOf st.dyn_ltree) mL) +
    tokBits st.bl_tree (treeTokens (lenOf st.dyn_dtree) mD)

theorem send_all_trees_SH {pbo Lim mL mD nb : Nat} (P : SatPre b st d pbo Lim mL mD nb)
    (lc dc bc : Int32) (hlc : lc.toInt = mL) (hdc : dc.toInt = mD) (hbc : bc.toInt = nb)
    (hroom : 8 * st.pending.toNat + st.bi_valid.toInt.toNat + satBits st mL mD nb + 64 ≤ 8 * Lim) :
    Sat (SH H i z b st d) (send_all_trees (some b) lc dc bc)
      (fun _ H' => SendPost H i z b st d pbo (satBits st mL mD nb) H') := by
  have hpb := P.hpb; have hLim := P.hLim; have hL32 := P.hL32
  have := P.nb1; have := P.nb2; have := P.mL1; have := P.mL2; have := P.mD1; have := P.mD2
  unfold satBits at hroom
  unfold send_all_trees
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  have hv := toU32 _ P.v0
  have h64 := P.v64
  have A0 : BAcc H i z b st d pbo st.bi_valid.toInt.toNat 0 st.bi_valid.toUInt32 (SH H i z b st d) :=
    ⟨st.pending, d, rfl, WrIn.refl _ _ _, Nat.le_refl _, by rw [hv]; omega, by rw [hv]; omega⟩
  dsimp only
  rw [chk_small _ (by omega) (by omega), pure_bind_M]
  refine Sat.bind (Sat.mono (bacc_send_bits hpb hLim hL32 A0 _ 5 _ (by decide) (by rw [show (5 : UInt32).toNat = 5 from rfl]; omega)) ?_)
  rintro ⟨bb1, bv1⟩ H1 A1
  rw [show (5 : UInt32).toNat = 5 from rfl] at A1
  dsimp only
  rw [chk_small _ (by omega) (by omega), pure_bind_M]
  refine Sat.bind (Sat.mono (bacc_send_bits hpb hLim hL32 A1 _ 5 _ (by decide) (by rw [show (5 : UInt32).toNat = 5 from rfl]; omega)) ?_)
  rintro ⟨bb2, bv2⟩ H2 A2
  rw [show (5 : UInt32).toNat = 5 from rfl] at A2
  dsimp only
  rw [chk_small _ (by omega) (by omega), pure_bind_M]
  refine Sat.bind (Sat.mono (bacc_send_bits hpb hLim hL32 A2 _ 4 _ (by decide) (by rw [show (4 : UInt32).toNat = 4 from rfl]; omega)) ?_)
  rintro ⟨bb3, bv3⟩ H3 A3
  rw [show (4 : UInt32).toNat = 4 from rfl] at A3
  dsimp only
  have e3 : ∀ x : UInt32, x = 3 → x.toNat = 3 := fun x h => by subst h; rfl
  refine Sat.bind (Sat.mono (sat_cwhile (fun (x : Int32 × UInt64 × UInt32) H' => ∃ r : Nat, x.1.toInt = r ∧ r ≤ nb ∧
      BAcc H i z b st d pbo st.bi_valid.toInt.toNat (14 + 3 * r) x.2.2 H')
    (fun x => nb - x.1.toInt.toNat)
    (fun x H' => BAcc H i z b st d pbo st.bi_valid.toInt.toNat (14 + 3 * nb) x.2.2 H') ?_
    ⟨0, rfl, by omega, by simpa using A3⟩ (by simp [fuel]; omega)) ?_)
  · rintro ⟨rk, bb, bv⟩ H4 ⟨r, hr, hrn, A4⟩
    dsimp only at hr A4
    refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
    · have hc' : rk < bc := by simpa using hc
      have hlt : r < nb := by have := Int32.lt_iff_toInt_lt.mp hc'; omega
      have e1 : rk.toInt.toNat = r := by omega
      dsimp only
      simp only [e1]
      have ho := bl_order_lt ⟨r, by omega⟩
      refine Sat.bind (Sat.of_eq (tblGet_ok _ _ (by rw [bl_order_size]; omega) _) ?_)
      simp only [blTreeP, pure_bind_M]
      obtain ⟨np, d', rfl, hrest⟩ := A4
      refine Sat.bind (Sat.of_eq (ctDl_T (H := H) (i := i) (z := z) (b := b) (d := d') .bl_desc
        { st with pending := np } _ (by show _ < st.bl_tree.size; dsimp only at ho; have := P.hbl; omega)) ?_)
      refine Sat.bind (Sat.mono (bacc_send_bits hpb hLim hL32 ⟨np, d', rfl, hrest⟩ _ 3 bb (by decide)
        (by rw [show (3 : UInt32).toNat = 3 from rfl]; omega)) ?_)
      rintro ⟨bb5, bv5⟩ H5 A5
      rw [show (3 : UInt32).toNat = 3 from rfl] at A5
      have hs : (rk + 1).toInt = ((r + 1 : Nat) : Int) := by
        rw [TreesInit.i32_succ rk (by omega) (by omega)]; omega
      refine Sat.pure ⟨⟨r + 1, hs, by omega, by simpa [Nat.mul_succ, Nat.add_assoc] using A5⟩, ?_⟩
      dsimp only; rw [hs]; omega
    · have hge : nb ≤ r := by
        have hc' : ¬ rk < bc := by simpa using hc
        have := mt Int32.lt_iff_toInt_lt.mpr hc'; omega
      obtain rfl : r = nb := by omega
      exact A4
  rintro ⟨rk, bb6, bv6⟩ H6 A6
  dsimp only at A6 ⊢
  obtain ⟨np6, d6, rfl, w6, hle6, hacc6, hbv6⟩ := A6
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hsz6 : d6.size = d.size := w6.1
  have hv6 := toInt32_toInt bv6 hbv6
  simp only [dynLtreeP, dynDtreeP, pure_bind_M]
  rw [chk_small _ (by omega) (by omega), pure_bind_M]
  have hmc1 : (Int32.ofInt (lc.toInt - 1)).toInt + 1 = mL := by rw [ofInt_small _ (by omega) (by omega)]; omega
  refine Sat.bind (Sat.mono (send_tree_SH (st := { st with pending := np6, bi_buf := bb6, bi_valid := bv6.toInt32 })
    (d := d6) hpb (by rw [hsz6]; exact hLim) hL32 P.hbl P.h7 .l_desc mL _ hmc1 P.mL1 P.lsize (by omega) P.lg P.l15
    (by rw [hv6]; omega) (by rw [hv6]; omega) (by
      show 8 * np6.toNat + (bv6.toInt32).toInt.toNat +
        tokBits st.bl_tree (treeTokens (lenOf st.dyn_ltree) mL) + 64 ≤ 8 * Lim
      rw [hv6, Int.toNat_natCast]; omega)) ?_)
  rintro _ H7 q7
  have q7' : SendPost H i z b st d pbo (14 + 3 * nb + tokBits st.bl_tree (treeTokens (lenOf st.dyn_ltree) mL)) H7 :=
    SendPost.cat w6 hle6 (by rw [hacc6]) hbv6 q7
  obtain ⟨np7, bb7, bv7, d7, rfl, w7, hle7, hacc7, hbv7⟩ := q7'
  have hsz7 : d7.size = d.size := w7.1
  have hv7 := toInt32_toInt bv7 hbv7
  have hmc2 : (Int32.ofInt (dc.toInt - 1)).toInt + 1 = mD := by rw [ofInt_small _ (by omega) (by omega)]; omega
  refine Sat.mono (send_tree_SH (st := { st with pending := np7, bi_buf := bb7, bi_valid := bv7.toInt32 })
    (d := d7) hpb (by rw [hsz7]; exact hLim) hL32 P.hbl P.h7 .d_desc mD _ hmc2 P.mD1 P.dsize (by omega) P.dg P.d15
    (by rw [hv7]; omega) (by rw [hv7]; omega) (by
      show 8 * np7.toNat + (bv7.toInt32).toInt.toNat +
        tokBits st.bl_tree (treeTokens (lenOf st.dyn_dtree) mD) + 64 ≤ 8 * Lim
      rw [hv7, Int.toNat_natCast]; omega)) ?_
  rintro _ H8 q8
  exact SendPost.cat w7 hle7 hacc7 hbv7 q8

end

end ZlibNgF.Proof.TreesAllTrees
