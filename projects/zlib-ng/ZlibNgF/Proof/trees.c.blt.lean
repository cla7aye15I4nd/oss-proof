import ZlibNgF.Proof.«trees.c.sendtree»
import ZlibNgF.Proof.«trees.c.buildspec»

/-!
# `build_bl_tree` (`ZlibNgF`)

On `SH` heaps, given `BuildTreeSpec` (the statement of `build_tree`, proved elsewhere): `build_bl_tree` scans the
literal/length and distance trees (`scan_tree`, guards stored), builds the bit-length tree from the frequencies of
the model's `allTokens` (`treeLengths 19 7 (blFreq toks)`), finds `max_blindex` (`blMaxC`: the C loop, which agrees with
the model's `blMaxIndex` as soon as some length at `bl_order[3 ..]` is not zero), and adds to `opt_len` the bits of the
bit-length symbols and `3 * (max_blindex + 1) + 5 + 5 + 4`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesBlt
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesHeader ZlibNgF.Proof.TreesSendTree ZlibNgF.Proof.TreesBuildSpec ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Math.Huff
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.TreesScan (frq)

/-- `bl_order[k]` is the model's `blOrder`. -/
theorem bl_order_eq : ∀ k : Fin 19, (bl_order[k.val]!).toNat = blOrder.getD k.val 0 := by decide +kernel

theorem bl_order_size : bl_order.size = 19 := by decide +kernel

theorem bl_order_lt : ∀ k : Fin 19, (bl_order[k.val]!).toNat < 19 := by decide +kernel

/-- The bit-length symbols of both trees of `s`. -/
noncomputable def toksOf (s : DeflateState) (mL mD : Nat) : List Nat :=
  allTokens (lenOf s.dyn_ltree) mL (lenOf s.dyn_dtree) mD

/-- The bit-length code lengths `build_bl_tree` assigns. -/
noncomputable def blLenOf (s : DeflateState) (mL mD : Nat) : Nat → Nat := treeLengths 19 7 (blFreq (toksOf s mL mD))

/-- What `build_bl_tree` needs of the state. -/
structure BlPre (b : Nat) (s : DeflateState) (mL mD : Nat) : Prop where
  hmL : s.l_desc.max_code.toInt + 1 = mL
  mL1 : 1 ≤ mL
  mL2 : mL ≤ 286
  hmD : s.d_desc.max_code.toInt + 1 = mD
  mD1 : 1 ≤ mD
  mD2 : mD ≤ 30
  lsize : s.dyn_ltree.size = HEAP_SIZE
  dsize : s.dyn_dtree.size = 2 * 30 + 1
  bsize : s.bl_tree.size = 2 * 19 + 1
  l15 : ∀ n, n < mL → lenOf s.dyn_ltree n ≤ 15
  d15 : ∀ n, n < mD → lenOf s.dyn_dtree n ≤ 15
  b0 : ∀ c, c < 19 → (s.bl_tree[c]!).fc = 0
  bdyn : s.bl_desc.dyn_tree = .val (.ref (.bl_tree b) 0)
  bstat : s.bl_desc.stat_desc = .val .static_bl_desc
  pql : s.pq_leaves.size = 287
  pqs : s.pq_scratch.size = 287
  blc : s.bl_count.size = 16

/-- What `build_bl_tree` leaves (result `r = max_blindex`). -/
structure BlPost (s : DeflateState) (mL mD : Nat) (r : Int32) (s' : DeflateState) : Prop where
  keeps : EmitKeeps s s'
  pending : s'.pending = s.pending
  bi_buf : s'.bi_buf = s.bi_buf
  bi_valid : s'.bi_valid = s.bi_valid
  sym_next : s'.sym_next = s.sym_next
  ltree : s'.dyn_ltree = guard s.dyn_ltree mL
  dtree : s'.dyn_dtree = guard s.dyn_dtree mD
  bsize : s'.bl_tree.size = 2 * 19 + 1
  blen : ∀ k, k < 19 → lenOf s'.bl_tree k = blLenOf s mL mD k
  blmax : r.toInt = blMaxC (blLenOf s mL mD) 18
  opt_len : s'.opt_len = s.opt_len + (((toksOf s mL mD).map fun t => blLenOf s mL mD t + blExtra t).sum).toUInt32 +
    (3 * (r.toUInt32 + 1) + 5 + 5 + 4)
  static_len : s'.static_len = s.static_len
  l_desc : s'.l_desc = s.l_desc
  d_desc : s'.d_desc = s.d_desc
  bi_used : s'.bi_used = s.bi_used
  pql : s'.pq_leaves.size = s.pq_leaves.size
  pqs : s'.pq_scratch.size = s.pq_scratch.size
  blc : s'.bl_count.size = s.bl_count.size
  bl_dyn : s'.bl_desc.dyn_tree = s.bl_desc.dyn_tree
  bl_stat : s'.bl_desc.stat_desc = s.bl_desc.stat_desc

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- The `max_blindex` loop of `build_bl_tree`. -/
theorem blmax_loop (S : DeflateState) (hS : S.bl_tree.size = 2 * 19 + 1) :
    Sat (SH H i z b S d) (cwhile
      (fun ((mb, done) : Int32 × Bool) => pure (!done && mb >= 3, (mb, done)))
      (fun ((mb, _) : Int32 × Bool) => do
        let o ← tblGet bl_order mb.toInt.toNat
        if (← ctDl (← blTreeP (some b)) o.toNat) != 0 then pure (mb, true)
        else pure (mb - 1, false))
      (BL_CODES.toInt32 - 1, false))
      (fun x H' => H' = SH H i z b S d ∧ x.1.toInt = blMaxC (lenOf S.bl_tree) 18) := by
  refine sat_cwhile (fun (x : Int32 × Bool) H' => H' = SH H i z b S d ∧ ∃ k : Nat, x.1.toInt = k ∧ k ≤ 18 ∧
      (x.2 = false → 2 ≤ k ∧ blMaxC (lenOf S.bl_tree) 18 = blMaxC (lenOf S.bl_tree) k) ∧
      (x.2 = true → blMaxC (lenOf S.bl_tree) 18 = k))
    (fun x => if x.2 then 0 else x.1.toInt.toNat + 1) _ ?_ ⟨rfl, 18, by decide, by omega, fun _ => ⟨by omega, rfl⟩,
      fun h => by simp at h⟩ (by simp [fuel]; decide)
  rintro ⟨mb, dn⟩ _ ⟨rfl, k, hk, hk18, hf, ht⟩
  dsimp only at hk hf ht
  refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨rfl, ?_⟩⟩
  · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨rfl, hc⟩ := hc
    have hk3 : 3 ≤ k := by have := Int32.le_iff_toInt_le.mp hc; simp at this; omega
    have e1 : mb.toInt.toNat = k := by omega
    simp only [e1]
    have ho := bl_order_lt ⟨k, by omega⟩
    refine Sat.bind (Sat.of_eq (TreesEmitP.tblGet_ok _ _ (by rw [bl_order_size]; omega) _) ?_)
    simp only [blTreeP, pure_bind_M]
    refine Sat.bind (Sat.of_eq (ctDl_T .bl_desc S _ (by show _ < S.bl_tree.size; dsimp only at ho; omega)) ?_)
    have eo := bl_order_eq ⟨k, by omega⟩
    dsimp only at eo
    have hstep : blMaxC (lenOf S.bl_tree) k = if lenOf S.bl_tree (blOrder.getD k 0) ≠ 0 then k
        else blMaxC (lenOf S.bl_tree) (k - 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [blMaxC, show ¬ j + 1 < 3 by omega, ↓reduceIte, Nat.add_sub_cancel]
    have hfk := (hf rfl).2
    split
    · rename_i hne
      have hne' : lenOf S.bl_tree (blOrder.getD k 0) ≠ 0 := by
        rw [← eo]; unfold lenOf; intro h0; apply bne_iff_ne.mp hne
        exact UInt16.toNat_inj.mp h0
      refine Sat.pure ⟨⟨rfl, k, hk, hk18, fun h => by simp at h, fun _ => ?_⟩, by simp⟩
      rw [hfk, hstep, ite_t hne']
    · rename_i hne
      have hne' : ¬ lenOf S.bl_tree (blOrder.getD k 0) ≠ 0 := by
        intro h0; apply hne; rw [bne_iff_ne]; intro h1; apply h0; rw [← eo]; unfold lenOf
        have := congrArg UInt16.toNat h1
        exact this
      have hs : (mb - 1).toInt = k - 1 := by
        rw [Int32.toInt_sub, Int32.toInt_one, hk]; exact Int.bmod_eq_of_le (by omega) (by omega)
      refine Sat.pure ⟨⟨rfl, k - 1, by rw [hs]; omega, by omega, fun _ => ⟨by omega, ?_⟩, fun h => by simp at h⟩, ?_⟩
      · rw [hfk, hstep, ite_f hne']
      · simp only [Bool.false_eq_true, ↓reduceIte, hs]; omega
  · cases dn
    · have h1 : ¬ mb ≥ 3 := by simpa using hc
      have h2 := Int32.lt_iff_toInt_lt.mp (Int32.not_le.mp h1)
      simp at h2
      obtain ⟨hk2, hfk⟩ := hf rfl
      obtain rfl : k = 2 := by omega
      rw [hk, hfk]; rfl
    · rw [hk, ht rfl]

theorem build_bl_tree_SH (hbt : BuildTreeSpec) (s : DeflateState) (mL mD : Nat) (P : BlPre b s mL mD) :
    Sat (SH H i z b s d) (build_bl_tree (some b))
      (fun r H' => ∃ s', H' = SH H i z b s' d ∧ BlPost s mL mD r s') := by
  have := P.mL1; have := P.mL2; have := P.mD1; have := P.mD2
  have hLs := P.lsize; have hDs := P.dsize; have hBs := P.bsize
  simp only [HEAP_SIZE, L_CODES] at hLs
  unfold build_bl_tree
  simp only [dynLtreeP, dynDtreeP, pure_bind_M]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.mono (scan_tree_SH (H := H) (i := i) (z := z) (b := b) (d := d) .l_desc (by decide) s mL _ P.hmL
    P.mL1 (by show mL < s.dyn_ltree.size; omega) (by omega) P.l15 (by omega)
    (fun c hc => by rw [P.b0 c hc]; simp; omega)) ?_)
  rintro _ _ ⟨C1, rfl, hC1s, hC1⟩
  have tl := treeTokens_length (lenOf (tArr DescSel.l_desc s)) mL
  have td := treeTokens_length (lenOf (tArr DescSel.d_desc s)) mD
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.mono (scan_tree_SH (H := H) (i := i) (z := z) (b := b) (d := d) .d_desc (by decide)
    (tPut .bl_desc (tPut .l_desc s (guard (tArr .l_desc s) mL)) C1) mD _ P.hmD P.mD1
    (by show mD < s.dyn_dtree.size; omega) (by omega) P.d15 (by show 19 ≤ C1.size; omega)
    (fun c hc => by
      show (C1[c]!).fc.toNat + mD < 65536
      have h1 := hC1 c hc
      have := List.count_le_length (a := c) (l := treeTokens (lenOf (tArr DescSel.l_desc s)) mL)
      rw [P.b0 c hc] at h1; simp at h1; omega)) ?_)
  rintro _ _ ⟨C2, rfl, hC2s, hC2⟩
  -- the bit-length frequencies are those of the model
  have hfrq : ∀ c, c < 19 → frq C2 c = blFreq (toksOf s mL mD) c := fun c hc => by
    have a := hC2 c hc
    have b1 := hC1 c hc
    have z0 := P.b0 c hc
    unfold frq blFreq toksOf allTokens
    rw [List.count_append]
    change (C2[c]!).fc.toNat = (C1[c]!).fc.toNat + _ at a
    rw [z0] at b1
    simp only [UInt16.toNat_zero, Nat.zero_add] at b1
    rw [a, b1]; rfl
  have e2 : tPut .bl_desc (tPut .d_desc (tPut .bl_desc (tPut .l_desc s (guard (tArr .l_desc s) mL)) C1)
      (guard (tArr .d_desc (tPut .bl_desc (tPut .l_desc s (guard (tArr .l_desc s) mL)) C1)) mD)) C2 =
      { s with dyn_ltree := guard s.dyn_ltree mL, dyn_dtree := guard s.dyn_dtree mD, bl_tree := C2 } := rfl
  rw [e2]
  have hC2s' : C2.size = 2 * 19 + 1 := by rw [hC2s]; show C1.size = _; omega
  have hlen : (toksOf s mL mD).length ≤ mL + mD := by
    unfold toksOf allTokens; rw [List.length_append]; exact Nat.add_le_add tl td
  have hlt : ∀ x ∈ toksOf s mL mD, x < 19 := by
    unfold toksOf allTokens; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact treeTokens_lt _ _ P.l15 x hx
    · exact treeTokens_lt _ _ P.d15 x hx
  have hmass : ZlibNgF.Math.HuffSymbols.mass (frq C2) 19 < 65534 := by
    rw [ZlibNgF.Math.HuffSymbols.mass_congr hfrq]
    have := mass_count_le 19 (toksOf s mL mD)
    unfold blFreq; omega
  refine Sat.bind (Sat.mono (hbt .bl_desc H i z b _ d ⟨P.bdyn, P.bstat, hC2s', P.pql, P.pqs, P.blc, hmass⟩) ?_)
  rintro _ _ ⟨s3, rfl, Q⟩
  obtain ⟨A, blc, lv, sc, mc, rfl, hAs, hblc, hlv, hsc, hmc, hdl, hfc⟩ := Q.shape
  have hblen : ∀ k, k < 19 → lenOf A k = blLenOf s mL mD k := fun k hk => by
    unfold lenOf blLenOf; rw [hdl k hk]
    exact congrFun (treeLengths_congr 19 7 (frq C2) _ hfrq) k
  refine Sat.bind (Sat.mono (blmax_loop _ (by show A.size = _; rw [hAs]; exact hC2s')) ?_)
  rintro ⟨mb, dn⟩ _ ⟨rfl, hmb⟩
  have hmb' : mb.toInt = blMaxC (lenOf A) 18 := hmb
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hopt : optAdd .bl_desc C2 = ((toksOf s mL mD).map fun t => blLenOf s mL mD t + blExtra t).sum := by
    unfold optAdd
    rw [ZlibNgF.Math.HuffSymbols.mass_congr (g := fun k => (toksOf s mL mD).count k * (blLenOf s mL mD k + blExtra k))
      (fun k hk => by
        rw [hfrq k hk]
        have := congrFun (treeLengths_congr 19 7 (frq C2) _ hfrq) k
        show blFreq _ k * (treeLengths 19 7 (frq C2) k + blExtra k) = _
        rw [this]; rfl)]
    exact mass_count_mul _ 19 _ hlt
  refine Sat.pure ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, hlv, hsc, hblc, rfl, rfl⟩⟩
  · show A.size = _; rw [hAs]; exact hC2s'
  · exact hblen
  · rw [hmb', blMaxC_congr _ _ hblen 18]
  · show s.opt_len + (optAdd .bl_desc C2).toUInt32 + _ = _
    rw [hopt]
  · show s.static_len + (statAdd .bl_desc C2).toUInt32 = _
    simp [statAdd]

end

end ZlibNgF.Proof.TreesBlt
