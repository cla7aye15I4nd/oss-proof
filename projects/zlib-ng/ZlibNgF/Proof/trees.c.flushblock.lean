import ZlibNgF.Proof.«trees.c.flush»
import ZlibNgF.Math.OverlayTinyBudget
import ZlibNgF.Proof.«trees.c.blt»
import ZlibNgF.Proof.«trees.c.alltrees»
import ZlibNgF.Proof.«trees.c.dyn»
import ZlibNgF.Proof.«trees.c.buildspec»
import ZlibNgF.Math.TreesHdrCost

/-!
# The trees of a dynamic block (`ZlibNgF`)

What `build_tree(s, &s->l_desc)`, `build_tree(s, &s->d_desc)` and `build_bl_tree(s)` leave in `zng_tr_flush_block`,
from a state between blocks (`opt_len = static_len = 0`, `bl_tree` frequencies 0, `SymOk`), in terms of the model of
the tallied symbols `xs = symsOf d sbo n` (`TPost`): `opt_len = optLen xs` and `static_len = staticLen xs` (exact,
no wrap), `max_code + 1` of both trees the model's, the code lengths of both trees the model's below `max_code + 1`
and the `scan_tree` guard at `max_code + 1`, the bit-length code lengths at most 7, the header bits of
`send_all_trees(s, lcodes, dcodes, max_blindex + 1)` the model's `blockHeader xs`, and the code lengths that
`compress_block` reads at most 15 with the symbol costs the model's `blockCosts xs`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesFlushBlock
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.TreesPrims ZlibNgF.Proof.TreesHeader ZlibNgF.Proof.TreesSendTree ZlibNgF.Proof.TreesBlt
open ZlibNgF.Proof.TreesAllTrees ZlibNgF.Proof.TreesBuildSpec ZlibNgF.Proof.TreesDyn ZlibNgF.Proof.TreesCompress
open ZlibNgF.Math.Huff ZlibNgF.Math.HuffSymbols ZlibNgF.Math.OverlayDynamic
open ZlibNgF.Proof.TreesScan (frq)
open ZlibNgF.Proof.DeflateFacts (EmitKeeps)
open ZlibNgF.Proof.TreesForce (sdl)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-! ## The overlay budget of a dynamic block -/

open ZlibNgF.Math.HuffSymbols (Symbol)
open ZlibNgF.Math.TreesOverlay (Budget)
open ZlibNgF.Math.OverlayDynamic (blockHeader blockCosts Chosen dynamic_budget)

/-- **The dynamic-block budget.** For every `lit_bufsize` `B` that `deflateInit2` can set (`1 << (memLevel + 6)`,
`DCore.lpow`), at most 7 bits waiting before the block (`FlushBlockPre`), and every block of at most `B - 1` valid
symbols that `zng_tr_flush_block` sends with dynamic trees (`Chosen xs`: `opt_lenb < static_lenb`, with `opt_len` and
`static_len` the model sums `optLen xs` / `staticLen xs`), the bits before the first symbol (the waiting bits, the 3
block-type bits and the tree header `blockHeader xs`) and the excess of the symbol costs fit the `sym_buf` overlay. -/
def DynBudget : Prop :=
  ∀ (B b0 : Nat) (xs : List Symbol), (∃ k, 7 ≤ k ∧ k ≤ 15 ∧ B = 2 ^ k) → b0 ≤ 7 → xs.length + 1 ≤ B →
    (∀ s ∈ xs, s.Valid) → Chosen xs → Budget B (b0 + 3 + blockHeader xs) (blockCosts xs)

/-- `DynBudget` holds: `dynamic_budget` (`Math/OverlayTinyBudget.lean`) for each power of two. -/
theorem dynBudget : DynBudget := by
  intro B b0 xs ⟨k, h7, h15, hB⟩ hb0 hn hv hc
  refine dynamic_budget xs ?_ hb0 hn hv hc
  subst hB
  by_cases a7 : k = 7
  · subst a7; left; rfl
  by_cases a8 : k = 8
  · subst a8; right; left; rfl
  by_cases a9 : k = 9
  · subst a9; right; right; left; rfl
  right; right; right
  refine ⟨?_, ?_⟩
  · have : 2 ^ 10 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    exact this
  · have : 2 ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) h15
    exact this


/-! ## The frequencies as the model's -/

/-- The entry state of the tree construction: between blocks, `n` tallied symbols. -/
structure TCtx (b : Nat) (st : DeflateState) (d : Array UInt8) (sbo n : Nat) : Prop where
  sym : SymOk d sbo st.sym_next st.dyn_ltree st.dyn_dtree
  hsn : st.sym_next.toNat = 3 * n
  hn : n < 32768
  lsize : st.dyn_ltree.size = HEAP_SIZE
  dsize : st.dyn_dtree.size = 2 * 30 + 1
  bsize : st.bl_tree.size = 2 * 19 + 1
  pql : st.pq_leaves.size = 287
  pqs : st.pq_scratch.size = 287
  blc : st.bl_count.size = 16
  opt0 : st.opt_len = 0
  stat0 : st.static_len = 0
  bl0 : ∀ c, c < 19 → (st.bl_tree[c]!).fc = 0
  ldyn : st.l_desc.dyn_tree = .val (.ref (.dyn_ltree b) 0)
  lstat : st.l_desc.stat_desc = .val .static_l_desc
  ddyn : st.d_desc.dyn_tree = .val (.ref (.dyn_dtree b) 0)
  dstat : st.d_desc.stat_desc = .val .static_d_desc
  bldyn : st.bl_desc.dyn_tree = .val (.ref (.bl_tree b) 0)
  blstat : st.bl_desc.stat_desc = .val .static_bl_desc

section
variable {b : Nat} {st : DeflateState} {d : Array UInt8} {sbo n : Nat}

theorem TCtx.n3 (T : TCtx b st d sbo n) : st.sym_next.toNat / 3 = n := by rw [T.hsn]; omega

theorem TCtx.valid (T : TCtx b st d sbo n) : ∀ s ∈ symsOf d sbo n, s.Valid :=
  symsOf_valid fun j hj => T.sym.dist j (by rw [T.n3]; exact hj)

theorem TCtx.flit (T : TCtx b st d sbo n) (k : Nat) (hk : k < 286) : frq st.dyn_ltree k = litFreq (symsOf d sbo n) k := by
  unfold frq; rw [T.sym.lfreq k hk, litFreq_eq, T.n3]

theorem TCtx.fdist (T : TCtx b st d sbo n) (k : Nat) (hk : k < 30) : frq st.dyn_dtree k = distFreq (symsOf d sbo n) k := by
  unfold frq; rw [T.sym.dfreq k hk, distFreq_eq (fun j hj => T.sym.dist j (by rw [T.n3]; exact hj)), T.n3]

theorem TCtx.bl (T : TCtx b st d sbo n) : buildTree 286 (frq st.dyn_ltree) = buildTree 286 (litFreq (symsOf d sbo n)) :=
  buildTree_congr _ _ _ T.flit

theorem TCtx.bd (T : TCtx b st d sbo n) : buildTree 30 (frq st.dyn_dtree) = buildTree 30 (distFreq (symsOf d sbo n)) :=
  buildTree_congr _ _ _ T.fdist

theorem TCtx.ll (T : TCtx b st d sbo n) : tLen .l_desc st.dyn_ltree = litLens (symsOf d sbo n) :=
  treeLengths_congr _ _ _ _ T.flit

theorem TCtx.dl (T : TCtx b st d sbo n) : tLen .d_desc st.dyn_dtree = distLens (symsOf d sbo n) :=
  treeLengths_congr _ _ _ _ T.fdist

theorem mass_distFreq_le (xs : List Symbol) : mass (distFreq xs) 30 ≤ xs.length := by
  have distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey distanceCode = some k → k < 30 := by
    intro s _ k hk
    unfold Symbol.distanceKey at hk
    split at hk
    · simp at hk
    · simp only [Option.some.injEq] at hk; rw [← hk]; exact distanceCode_lt _
  have e := weighted_optional_key (Symbol.distanceKey distanceCode) (xs := xs) 30 (fun _ => 1) distanceKeys
  have e2 : mass (fun k => countKey (Symbol.distanceKey distanceCode) xs k * 1) 30 = mass (distFreq xs) 30 :=
    mass_congr fun k _ => by simp [distFreq, distanceFrequency]
  rw [e2] at e
  rw [e]
  refine Nat.le_trans (sum_le_mul 1 _ fun c hc => ?_) (by simp)
  simp only [List.mem_map] at hc
  obtain ⟨x, -, rfl⟩ := hc
  split <;> simp

theorem TCtx.lkeys (T : TCtx b st d sbo n) : ∀ s ∈ symsOf d sbo n, s.literalKey lengthCode < 286 := by
  intro s hs
  have := (T.valid s hs).2
  have := lengthCode_lt s.value
  unfold Symbol.literalKey; split <;> omega

theorem TCtx.massL (T : TCtx b st d sbo n) : mass (frq st.dyn_ltree) 286 = n + 1 := by
  rw [mass_congr T.flit]
  unfold litFreq
  rw [literal_frequency_mass _ T.lkeys, symsOf_length]

theorem TCtx.massD (T : TCtx b st d sbo n) : mass (frq st.dyn_dtree) 30 ≤ n := by
  rw [mass_congr T.fdist]
  have := mass_distFreq_le (symsOf d sbo n)
  rwa [symsOf_length] at this

theorem TCtx.optL (T : TCtx b st d sbo n) :
    optAdd .l_desc st.dyn_ltree = mass (fun k => litFreq (symsOf d sbo n) k * (litLens (symsOf d sbo n) k + xbL k)) 286 := by
  unfold optAdd
  refine mass_congr fun k hk => ?_
  show frq st.dyn_ltree k * (tLen .l_desc st.dyn_ltree k + xb .l_desc k) = _
  rw [T.flit k hk, T.ll]; rfl

theorem TCtx.optD (T : TCtx b st d sbo n) :
    optAdd .d_desc st.dyn_dtree =
      mass (fun k => distFreq (symsOf d sbo n) k * (distLens (symsOf d sbo n) k + distanceExtra k)) 30 := by
  unfold optAdd
  refine mass_congr fun k hk => ?_
  show frq st.dyn_dtree k * (tLen .d_desc st.dyn_dtree k + xb .d_desc k) = _
  rw [T.fdist k hk, T.dl]; rfl

theorem TCtx.statL (T : TCtx b st d sbo n) :
    statAdd .l_desc st.dyn_ltree = mass (fun k => litFreq (symsOf d sbo n) k * (staticLitLen k + xbL k)) 286 := by
  unfold statAdd
  refine mass_congr fun k hk => ?_
  show frq st.dyn_ltree k * ((sdl .l_desc k).toNat + xb .l_desc k) = _
  have hk' : k < 286 := hk
  rw [T.flit k hk']
  have := sl_eq ⟨k, by omega⟩
  simp only [sdl, UInt16.toNat_toUInt32] at this ⊢
  rw [this]; rfl

theorem TCtx.statD (T : TCtx b st d sbo n) :
    statAdd .d_desc st.dyn_dtree = mass (fun k => distFreq (symsOf d sbo n) k * (5 + distanceExtra k)) 30 := by
  unfold statAdd
  refine mass_congr fun k hk => ?_
  show frq st.dyn_dtree k * ((sdl .d_desc k).toNat + xb .d_desc k) = _
  rw [T.fdist k hk]
  have := sd_eq ⟨k, hk⟩
  simp only [sdl, UInt16.toNat_toUInt32] at this ⊢
  rw [this]; rfl

/-- The tallied symbol `j` has a nonzero literal/length frequency. -/
theorem lused (j : Nat) (hj : j < n) : litFreq (symsOf d sbo n) (symLCode d sbo j) ≠ 0 := by
  rw [litFreq_eq]
  have : 0 < lCount d sbo n (symLCode d sbo j) :=
    List.countP_pos_iff.mpr ⟨j, List.mem_range.mpr hj, by simp⟩
  omega

theorem TCtx.dused (T : TCtx b st d sbo n) (j : Nat) (hj : j < n) (h0 : symDist d sbo j ≠ 0) :
    distFreq (symsOf d sbo n) (dCodeOf (symDist d sbo j - 1)) ≠ 0 := by
  rw [distFreq_eq (fun j hj => T.sym.dist j (by rw [T.n3]; exact hj))]
  have : 0 < dCount d sbo n (dCodeOf (symDist d sbo j - 1)) :=
    List.countP_pos_iff.mpr ⟨j, List.mem_range.mpr hj, by simp [h0]⟩
  omega

end


/-! ## What the tree construction leaves -/

/-- `max_code + 1` of the literal/length tree of the tallied symbols. -/
noncomputable def mcL (d : Array UInt8) (sbo n : Nat) : Nat := (buildTree 286 (litFreq (symsOf d sbo n))).maxCode1

/-- `max_code + 1` of the distance tree of the tallied symbols. -/
noncomputable def mcD (d : Array UInt8) (sbo n : Nat) : Nat := (buildTree 30 (distFreq (symsOf d sbo n))).maxCode1

theorem mcL_le (d : Array UInt8) (sbo n : Nat) : 1 ≤ mcL d sbo n ∧ mcL d sbo n ≤ 286 :=
  ⟨built_pos _ _, built_maxCode1_le _ (by omega)⟩

theorem mcD_le (d : Array UInt8) (sbo n : Nat) : 1 ≤ mcD d sbo n ∧ mcD d sbo n ≤ 30 :=
  ⟨built_pos _ _, built_maxCode1_le _ (by omega)⟩

/-- The state after `build_tree` (both data trees) and `build_bl_tree` (result `r = max_blindex`). -/
structure TPost (st : DeflateState) (d : Array UInt8) (sbo n : Nat) (r : Int32) (s3 : DeflateState) : Prop where
  keeps : EmitKeeps st s3
  pending : s3.pending = st.pending
  bi_buf : s3.bi_buf = st.bi_buf
  bi_valid : s3.bi_valid = st.bi_valid
  bi_used : s3.bi_used = st.bi_used
  sym_next : s3.sym_next = st.sym_next
  opt : s3.opt_len.toNat = optLen (symsOf d sbo n)
  stat : s3.static_len.toNat = staticLen (symsOf d sbo n)
  mL : s3.l_desc.max_code.toInt + 1 = mcL d sbo n
  mD : s3.d_desc.max_code.toInt + 1 = mcD d sbo n
  lsize : s3.dyn_ltree.size = HEAP_SIZE
  dsize : s3.dyn_dtree.size = 2 * 30 + 1
  bsize : s3.bl_tree.size = 2 * 19 + 1
  pql : s3.pq_leaves.size = 287
  pqs : s3.pq_scratch.size = 287
  blc : s3.bl_count.size = 16
  lg : (s3.dyn_ltree[mcL d sbo n]!).dl = 0xffff
  dg : (s3.dyn_dtree[mcD d sbo n]!).dl = 0xffff
  l15 : ∀ k, k < mcL d sbo n → lenOf s3.dyn_ltree k ≤ 15
  d15 : ∀ k, k < mcD d sbo n → lenOf s3.dyn_dtree k ≤ 15
  bl7 : ∀ t, t < 19 → (s3.bl_tree[t]!).dl.toNat ≤ 7
  r3 : 3 ≤ r.toInt
  r18 : r.toInt ≤ 18
  hdr : satBits s3 (mcL d sbo n) (mcD d sbo n) (r.toInt.toNat + 1) = blockHeader (symsOf d sbo n)
  used : UsedLe15 s3.dyn_ltree s3.dyn_dtree d sbo n
  costs : TreesCompress.blockCosts s3.dyn_ltree s3.dyn_dtree d sbo n = blockCosts (symsOf d sbo n)
  ldyn : s3.l_desc.dyn_tree = st.l_desc.dyn_tree
  lstat : s3.l_desc.stat_desc = st.l_desc.stat_desc
  ddyn : s3.d_desc.dyn_tree = st.d_desc.dyn_tree
  dstat : s3.d_desc.stat_desc = st.d_desc.stat_desc
  bldyn : s3.bl_desc.dyn_tree = st.bl_desc.dyn_tree
  blstat : s3.bl_desc.stat_desc = st.bl_desc.stat_desc

section
variable {b : Nat} {st : DeflateState} {d : Array UInt8} {sbo n : Nat}

theorem TCtx.preL (T : TCtx b st d sbo n) : BuildPre .l_desc b st :=
  ⟨T.ldyn, T.lstat, T.lsize, T.pql, T.pqs, T.blc, by show mass (frq st.dyn_ltree) 286 < 65534; rw [T.massL]; have := T.hn; omega⟩

theorem u32n (x : Nat) : x.toUInt32.toNat = x % 2 ^ 32 := by
  simp [Nat.toUInt32]

/-- The tree construction from a state between blocks ends in `TPost`. -/
theorem tpost_of (T : TCtx b st d sbo n) {s1 s2 s3 : DeflateState} {r : Int32} (p1 : BuildPost .l_desc st s1)
    (p2 : BuildPost .d_desc s1 s2) (p3 : BlPost s2 (mcL d sbo n) (mcD d sbo n) r s3) : TPost st d sbo n r s3 := by
  obtain ⟨⟨A, blc1, lv1, sc1, mc1, rfl, hAs, hblc1, hlv1, hsc1, hmc1, hAl, -⟩⟩ := p1
  obtain ⟨⟨B, blc2, lv2, sc2, mc2, rfl, hBs, hblc2, hlv2, hsc2, hmc2, hBl, -⟩⟩ := p2
  simp only [DescSel.set, DescSel.get, tPut, tArr] at *
  have ⟨mL1, mL2⟩ := mcL_le d sbo n
  have ⟨mD1, mD2⟩ := mcD_le d sbo n
  have hn := T.hn
  simp only [show tElems DescSel.l_desc = 286 from rfl, show tElems DescSel.d_desc = 30 from rfl] at hmc1 hAl hmc2 hBl
  rw [T.bl] at hmc1; rw [T.bd] at hmc2
  rw [T.ll] at hAl; rw [T.dl] at hBl
  have hL : ∀ k, k < mcL d sbo n → lenOf A k = litLens (symsOf d sbo n) k := fun k hk => hAl k (by omega)
  have hD : ∀ k, k < mcD d sbo n → lenOf B k = distLens (symsOf d sbo n) k := fun k hk => hBl k (by omega)
  have hLs : A.size = HEAP_SIZE := by rw [hAs, T.lsize]
  have hBs' : B.size = 2 * 30 + 1 := by rw [hBs, T.dsize]
  generalize hS2 : ({ st with
      opt_len := st.opt_len + (optAdd DescSel.l_desc st.dyn_ltree).toUInt32 + (optAdd DescSel.d_desc st.dyn_dtree).toUInt32
      static_len := st.static_len + (statAdd DescSel.l_desc st.dyn_ltree).toUInt32 +
        (statAdd DescSel.d_desc st.dyn_dtree).toUInt32
      l_desc := { st.l_desc with max_code := mc1 }
      d_desc := { st.d_desc with max_code := mc2 }
      bl_count := blc2
      pq_leaves := lv2
      pq_scratch := sc2
      dyn_ltree := A
      dyn_dtree := B } : DeflateState) = S2 at p3
  have e1 : S2.dyn_ltree = A := by rw [← hS2]
  have e2 : S2.dyn_dtree = B := by rw [← hS2]
  -- the bit-length symbols
  have toksE : toksOf S2 (mcL d sbo n) (mcD d sbo n) =
      allTokens (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n)) (mcD d sbo n) := by
    unfold toksOf allTokens
    rw [e1, e2, treeTokens_congr _ _ _ mL1 hL, treeTokens_congr _ _ _ mD1 hD]
  have blE : blLenOf S2 (mcL d sbo n) (mcD d sbo n) =
      treeLengths 19 7 (blFreq (allTokens (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n))
        (mcD d sbo n))) := by
    unfold blLenOf; rw [toksE]
  have f256 : litFreq (symsOf d sbo n) 256 ≠ 0 := by simp [litFreq, literalFrequency]
  have l256 : 256 < mcL d sbo n := built_gt 286 _ 256 (by omega) f256
  have hl15 : ∀ i, i < mcL d sbo n → litLens (symsOf d sbo n) i ≤ 15 := fun i _ => litLens_le _ _
  have hd15 : ∀ i, i < mcD d sbo n → distLens (symsOf d sbo n) i ≤ 15 := fun i _ => distLens_le _ _
  obtain ⟨t, ht, ht15⟩ := treeTokens_small _ _ hl15 256 l256
    (treeLengths_pos 286 15 _ 256 (by omega) (by omega) (by omega) f256)
  have hmax := blMaxC_of_tok (allTokens (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n))
    (mcD d sbo n)) t (List.mem_append.mpr (Or.inl ht)) ht15
  have hr : r.toInt = blMaxIndex (treeLengths 19 7 (blFreq (allTokens (litLens (symsOf d sbo n)) (mcL d sbo n)
      (distLens (symsOf d sbo n)) (mcD d sbo n)))) 18 := by
    rw [p3.blmax, blE, hmax]
  have r3 := blMaxIndex_ge (treeLengths 19 7 (blFreq (allTokens (litLens (symsOf d sbo n)) (mcL d sbo n)
      (distLens (symsOf d sbo n)) (mcD d sbo n)))) 18
  have r18 := blMaxIndex_le (treeLengths 19 7 (blFreq (allTokens (litLens (symsOf d sbo n)) (mcL d sbo n)
      (distLens (symsOf d sbo n)) (mcD d sbo n)))) 18
  simp only [show max 18 3 = 18 from rfl] at r18
  have hrN : r.toInt.toNat = blMaxIndex (treeLengths 19 7 (blFreq (allTokens (litLens (symsOf d sbo n))
      (mcL d sbo n) (distLens (symsOf d sbo n)) (mcD d sbo n)))) 18 := by omega
  have hR : r.toUInt32.toNat = r.toInt.toNat := ZlibNgF.Proof.TreesEmitP.toU32 r (by omega)
  have hdist : ∀ j, j < n → symDist d sbo j ≤ 32768 := fun j hj => T.sym.dist j (by rw [T.n3]; exact hj)
  -- the guarded trees
  have gL : ∀ k, k < mcL d sbo n → (guard A (mcL d sbo n))[k]! = A[k]! := fun k hk => guard_lt _ _ _ hk
  have gD : ∀ k, k < mcD d sbo n → (guard B (mcD d sbo n))[k]! = B[k]! := fun k hk => guard_lt _ _ _ hk
  have uL : ∀ c, c < 286 → litFreq (symsOf d sbo n) c ≠ 0 → ((guard A (mcL d sbo n))[c]!).dl.toNat ≤ 15 := by
    intro c hc hf
    rw [gL c (built_gt 286 _ c hc hf), hAl c hc]; exact litLens_le _ _
  have uD : ∀ c, c < 30 → distFreq (symsOf d sbo n) c ≠ 0 → ((guard B (mcD d sbo n))[c]!).dl.toNat ≤ 15 := by
    intro c hc hf
    rw [gD c (built_gt 30 _ c hc hf), hBl c hc]; exact distLens_le _ _
  -- the bit-length symbols and their bits
  have hlt : ∀ x ∈ allTokens (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n)) (mcD d sbo n),
      x < 19 := by
    unfold allTokens; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact treeTokens_lt _ _ hl15 x hx
    · exact treeTokens_lt _ _ hd15 x hx
  have hbl : ∀ x, x < 19 → (s3.bl_tree[x]!).dl.toNat = treeLengths 19 7 (blFreq (allTokens (litLens (symsOf d sbo n))
      (mcL d sbo n) (distLens (symsOf d sbo n)) (mcD d sbo n))) x := fun x hx => by
    have := p3.blen x hx; unfold lenOf at this; rw [this, blE]
  have hH : blockHeader (symsOf d sbo n) = 5 + 5 + 4 + 3 * (blMaxIndex (treeLengths 19 7 (blFreq (allTokens
      (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n)) (mcD d sbo n)))) 18 + 1) +
      ((allTokens (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n)) (mcD d sbo n)).map fun t =>
        treeLengths 19 7 (blFreq (allTokens (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n))
          (mcD d sbo n))) t + blExtra t).sum := rfl
  have hHb := header_bound (symsOf d sbo n)
  have hO := opt_codes _ T.valid
  rw [← T.optL, ← T.optD] at hO
  have hBC := blockCosts_sum_le (symsOf d sbo n)
  rw [symsOf_length] at hBC
  have h256 := litLens_le (symsOf d sbo n) 256
  have hS := static_codes _ T.valid
  rw [← T.statL, ← T.statD] at hS
  have hSl := staticLen_le (symsOf d sbo n)
  rw [symsOf_length] at hSl
  refine {
    keeps := ?_
    pending := ?_
    bi_buf := ?_
    bi_valid := ?_
    bi_used := ?_
    sym_next := ?_
    opt := ?_
    stat := ?_
    mL := ?_
    mD := ?_
    lsize := ?_
    dsize := ?_
    bsize := p3.bsize
    pql := ?_
    pqs := ?_
    blc := ?_
    lg := ?_
    dg := ?_
    l15 := ?_
    d15 := ?_
    bl7 := ?_
    r3 := by omega
    r18 := by omega
    hdr := ?_
    used := ?_
    costs := ?_
    ldyn := ?_
    lstat := ?_
    ddyn := ?_
    dstat := ?_
    bldyn := ?_
    blstat := ?_ }
  · have k := p3.keeps; rw [← hS2] at k; exact k.trans rfl
  · rw [p3.pending, ← hS2]
  · rw [p3.bi_buf, ← hS2]
  · rw [p3.bi_valid, ← hS2]
  · rw [p3.bi_used, ← hS2]
  · rw [p3.sym_next, ← hS2]
  · rw [p3.opt_len, toksE, blE, ← hS2]
    show (st.opt_len + _ + _ + _ + _).toNat = _
    rw [T.opt0]
    unfold optLen
    rw [hH, ← hrN]
    simp only [UInt32.toNat_add, UInt32.toNat_mul, u32n, hR, UInt32.toNat_zero]
    simp only [UInt32.reduceToNat]
    omega
  · rw [p3.static_len, ← hS2]
    show (st.static_len + _ + _).toNat = _
    rw [T.stat0]
    simp only [UInt32.toNat_add, u32n, UInt32.toNat_zero]
    omega
  · rw [p3.l_desc, ← hS2]; exact hmc1
  · rw [p3.d_desc, ← hS2]; exact hmc2
  · rw [p3.ltree, guard_size, e1, hLs]
  · rw [p3.dtree, guard_size, e2, hBs']
  · rw [p3.pql, ← hS2]; show lv2.size = _; rw [hlv2, hlv1, T.pql]
  · rw [p3.pqs, ← hS2]; show sc2.size = _; rw [hsc2, hsc1, T.pqs]
  · rw [p3.blc, ← hS2]; show blc2.size = _; rw [hblc2, hblc1, T.blc]
  · rw [p3.ltree, e1]; exact guard_m A _ (by rw [hLs]; simp only [HEAP_SIZE, L_CODES]; omega)
  · rw [p3.dtree, e2]; exact guard_m B _ (by rw [hBs']; omega)
  · intro k hk; unfold lenOf; rw [p3.ltree, e1, gL k hk]; have := hL k hk; unfold lenOf at this; rw [this]; exact litLens_le _ _
  · intro k hk; unfold lenOf; rw [p3.dtree, e2, gD k hk]; have := hD k hk; unfold lenOf at this; rw [this]; exact distLens_le _ _
  · intro t ht; rw [hbl t ht]; exact genBitlen_le _ _ _
  · unfold satBits
    have q1 : treeTokens (lenOf s3.dyn_ltree) (mcL d sbo n) = treeTokens (litLens (symsOf d sbo n)) (mcL d sbo n) :=
      treeTokens_congr _ _ _ mL1 fun k hk => by unfold lenOf; rw [p3.ltree, e1, gL k hk]; exact hL k hk
    have q2 : treeTokens (lenOf s3.dyn_dtree) (mcD d sbo n) = treeTokens (distLens (symsOf d sbo n)) (mcD d sbo n) :=
      treeTokens_congr _ _ _ mD1 fun k hk => by unfold lenOf; rw [p3.dtree, e2, gD k hk]; exact hD k hk
    rw [q1, q2, Nat.add_assoc, ← tokBits_append, hH, ← hrN]
    have : tokBits s3.bl_tree (treeTokens (litLens (symsOf d sbo n)) (mcL d sbo n) ++
        treeTokens (distLens (symsOf d sbo n)) (mcD d sbo n)) =
        ((allTokens (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n)) (mcD d sbo n)).map fun t =>
          treeLengths 19 7 (blFreq (allTokens (litLens (symsOf d sbo n)) (mcL d sbo n) (distLens (symsOf d sbo n))
            (mcD d sbo n))) t + blExtra t).sum := by
      unfold tokBits
      exact congrArg List.sum (List.map_congr_left fun x hx => by unfold tokCost; rw [hbl x (hlt x hx)])
    rw [this]
  · rw [p3.ltree, p3.dtree, e1, e2]
    refine ⟨uL 256 (by omega) f256, fun j hj => ⟨uL _ (symLCode_lt d sbo j) (lused j hj), fun h0 => ?_⟩⟩
    exact uD _ (dCodeOf_lt _ (by have := hdist j hj; omega)) (T.dused j hj h0)
  · rw [p3.ltree, p3.dtree, e1, e2]
    rw [← blockCosts_model A B d sbo n hdist (fun k hk => hAl k hk) (fun k hk => hBl k hk)]
    unfold TreesCompress.blockCosts
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    rw [symCost_eq, symCost_eq, gL _ (built_gt 286 _ _ (symLCode_lt d sbo j) (lused j hj'))]
    by_cases h0 : symDist d sbo j = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      rw [gD _ (built_gt 30 _ _ (dCodeOf_lt _ (by have := hdist j hj'; omega)) (T.dused j hj' h0))]
  · rw [p3.l_desc, ← hS2]
  · rw [p3.l_desc, ← hS2]
  · rw [p3.d_desc, ← hS2]
  · rw [p3.d_desc, ← hS2]
  · rw [p3.bl_dyn, ← hS2]
  · rw [p3.bl_stat, ← hS2]

theorem TCtx.preD (T : TCtx b st d sbo n) {s1 : DeflateState} (p1 : BuildPost .l_desc st s1) :
    BuildPre .d_desc b s1 := by
  obtain ⟨⟨A, blc1, lv1, sc1, mc1, hs1, hAs, hblc1, hlv1, hsc1, -, -, -⟩⟩ := p1
  simp only [DescSel.set, DescSel.get, tPut, tArr] at hs1
  have e1 : s1.d_desc = st.d_desc := by rw [hs1]
  have e2 : s1.dyn_dtree = st.dyn_dtree := by rw [hs1]
  have e3 : s1.pq_leaves = lv1 := by rw [hs1]
  have e4 : s1.pq_scratch = sc1 := by rw [hs1]
  have e5 : s1.bl_count = blc1 := by rw [hs1]
  have := T.massD; have := T.hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s1.d_desc.dyn_tree = _; rw [e1]; exact T.ddyn
  · show s1.d_desc.stat_desc = _; rw [e1]; exact T.dstat
  · show s1.dyn_dtree.size = 2 * 30 + 1; rw [e2]; exact T.dsize
  · rw [e3, hlv1, T.pql]
  · rw [e4, hsc1, T.pqs]
  · rw [e5, hblc1, T.blc]
  · show mass (frq s1.dyn_dtree) 30 < 65534; rw [e2]; omega

theorem TCtx.blpre (T : TCtx b st d sbo n) {s1 s2 : DeflateState} (p1 : BuildPost .l_desc st s1)
    (p2 : BuildPost .d_desc s1 s2) : BlPre b s2 (mcL d sbo n) (mcD d sbo n) := by
  obtain ⟨⟨A, blc1, lv1, sc1, mc1, hs1, hAs, hblc1, hlv1, hsc1, hmc1, hAl, -⟩⟩ := p1
  obtain ⟨⟨B, blc2, lv2, sc2, mc2, hs2, hBs, hblc2, hlv2, hsc2, hmc2, hBl, -⟩⟩ := p2
  simp only [DescSel.set, DescSel.get, tPut, tArr] at hs1 hs2 hmc1 hAl hmc2 hBl hBs hlv2 hsc2 hblc2
  simp only [show tElems DescSel.l_desc = 286 from rfl, show tElems DescSel.d_desc = 30 from rfl] at hmc1 hAl hmc2 hBl
  have f1 : s1.dyn_dtree = st.dyn_dtree := by rw [hs1]
  have f2 : s1.pq_leaves = lv1 := by rw [hs1]
  have f3 : s1.pq_scratch = sc1 := by rw [hs1]
  have f4 : s1.bl_count = blc1 := by rw [hs1]
  have f5 : s1.l_desc = { st.l_desc with max_code := mc1 } := by rw [hs1]
  have f6 : s1.d_desc = st.d_desc := by rw [hs1]
  have f7 : s1.bl_tree = st.bl_tree := by rw [hs1]
  have f8 : s1.bl_desc = st.bl_desc := by rw [hs1]
  have f9 : s1.dyn_ltree = A := by rw [hs1]
  have g1 : s2.l_desc = s1.l_desc := by rw [hs2]
  have g2 : s2.d_desc = { s1.d_desc with max_code := mc2 } := by rw [hs2]
  have g3 : s2.dyn_ltree = s1.dyn_ltree := by rw [hs2]
  have g4 : s2.dyn_dtree = B := by rw [hs2]
  have g5 : s2.bl_tree = s1.bl_tree := by rw [hs2]
  have g6 : s2.bl_desc = s1.bl_desc := by rw [hs2]
  have g7 : s2.pq_leaves = lv2 := by rw [hs2]
  have g8 : s2.pq_scratch = sc2 := by rw [hs2]
  have g9 : s2.bl_count = blc2 := by rw [hs2]
  have hmc1' : mc1.toInt + 1 = (mcL d sbo n : Int) := by unfold mcL; rw [← T.bl]; exact hmc1
  have hmc2' : mc2.toInt + 1 = (mcD d sbo n : Int) := by
    unfold mcD; rw [← T.bd, ← f1]; exact hmc2
  have hAl' : ∀ k, k < 286 → lenOf A k ≤ 15 := fun k hk => by
    have h1 := hAl k hk
    have h2 : tLen .l_desc st.dyn_ltree k ≤ 15 := by unfold tLen treeLengths; exact genBitlen_le _ _ _
    unfold lenOf; omega
  have hBl' : ∀ k, k < 30 → lenOf B k ≤ 15 := fun k hk => by
    have h1 := hBl k hk
    have h2 : tLen .d_desc s1.dyn_dtree k ≤ 15 := by unfold tLen treeLengths; exact genBitlen_le _ _ _
    unfold lenOf; omega
  have ⟨mL1, mL2⟩ := mcL_le d sbo n
  have ⟨mD1, mD2⟩ := mcD_le d sbo n
  exact {
    hmL := by rw [g1, f5]; exact hmc1'
    mL1 := mL1
    mL2 := mL2
    hmD := by rw [g2]; exact hmc2'
    mD1 := mD1
    mD2 := mD2
    lsize := by rw [g3, f9, hAs]; exact T.lsize
    dsize := by rw [g4, hBs, f1, T.dsize]
    bsize := by rw [g5, f7, T.bsize]
    l15 := fun k hk => by rw [g3, f9]; exact hAl' k (by omega)
    d15 := fun k hk => by rw [g4]; exact hBl' k (by omega)
    b0 := by rw [g5, f7]; exact T.bl0
    bdyn := by rw [g6, f8]; exact T.bldyn
    bstat := by rw [g6, f8]; exact T.blstat
    pql := by rw [g7, hlv2, f2, hlv1, T.pql]
    pqs := by rw [g8, hsc2, f3, hsc1, T.pqs]
    blc := by rw [g9, hblc2, f4, hblc1, T.blc] }

section
variable {H : Heap} {i : Nat} {z : ZStream}

/-- `build_tree` of both data trees and `build_bl_tree`, followed by `k max_blindex`. -/
theorem trees_then (hbt : BuildTreeSpec) (T : TCtx b st d sbo n) {β : Type} (k : Int32 → M β) (Q : β → Heap → Prop)
    (hk : ∀ r s3, TPost st d sbo n r s3 → Sat (SH H i z b s3 d) (k r) Q) :
    Sat (SH H i z b st d) (do
      build_tree (some b) .l_desc
      build_tree (some b) .d_desc
      let r ← build_bl_tree (some b)
      k r) Q := by
  refine Sat.bind (Sat.mono (hbt .l_desc H i z b st d T.preL) ?_)
  rintro _ _ ⟨s1, rfl, p1⟩
  refine Sat.bind (Sat.mono (hbt .d_desc H i z b s1 d (T.preD p1)) ?_)
  rintro _ _ ⟨s2, rfl, p2⟩
  refine Sat.bind (Sat.mono (build_bl_tree_SH hbt s2 _ _ (T.blpre p1 p2)) ?_)
  rintro r _ ⟨s3, rfl, p3⟩
  exact hk r s3 (tpost_of T p1 p2 p3)

end

end

/-! ## The dynamic branch -/

theorem syms_congr {d d' : Array UInt8} {sbo : Nat} (h : ∀ m, sbo ≤ m → d'[m]! = d[m]!) (j : Nat) :
    symDist d' sbo j = symDist d sbo j ∧ symLCode d' sbo j = symLCode d sbo j ∧
      d'[sbo + 3 * j + 2]! = d[sbo + 3 * j + 2]! := by
  have e0 := h (sbo + 3 * j) (by omega)
  have e1 := h (sbo + 3 * j + 1) (by omega)
  have e2 := h (sbo + 3 * j + 2) (by omega)
  have hd : symDist d' sbo j = symDist d sbo j := by unfold symDist; rw [e0, e1]
  exact ⟨hd, by unfold symLCode; rw [hd, e2], e2⟩

theorem used_congr {LT DT : Array Ct} {d d' : Array UInt8} {sbo n : Nat} (h : ∀ m, sbo ≤ m → d'[m]! = d[m]!)
    (u : UsedLe15 LT DT d sbo n) : UsedLe15 LT DT d' sbo n :=
  ⟨u.1, fun j hj => by
    obtain ⟨a, c, -⟩ := syms_congr h j
    rw [a, c]; exact u.2 j hj⟩

theorem costs_congr (LT DT : Array Ct) {d d' : Array UInt8} {sbo : Nat} (h : ∀ m, sbo ≤ m → d'[m]! = d[m]!)
    (n : Nat) : TreesCompress.blockCosts LT DT d' sbo n = TreesCompress.blockCosts LT DT d sbo n := by
  unfold TreesCompress.blockCosts
  refine List.map_congr_left fun j _ => ?_
  obtain ⟨a, -, c⟩ := syms_congr h j
  unfold symCost; rw [a, c]

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

theorem ctGet_dd (s : DeflateState) (k : Nat) (hk : k < s.dyn_dtree.size) :
    ctGet (.ref (CtRef.dyn_dtree b) 0) (k : Int) (SH H i z b s d) = .ok (s.dyn_dtree[k]!, SH H i z b s d) := by
  have e1 : Ptr.add (Ptr.ref (CtRef.dyn_dtree b) 0) (k : Int) (SH H i z b s d) =
      .ok (Ptr.ref (CtRef.dyn_dtree b) k, SH H i z b s d) := by
    simp only [Ptr.add, ctd_get]
    rw [ZlibNgF.Proof.DeflateAlloc.ite_t (by omega)]
    congr 3; omega
  simp [ctGet, Ptr.index, bind_app, e1, Ptr.load, ctd_get, hk]

theorem treeRd_l (st : DeflateState) (h : 286 ≤ st.dyn_ltree.size) :
    TreeRd (Fam H i z b st) (.ref (CtRef.dyn_ltree b) 0) st.dyn_ltree 286 := by
  rintro _ ⟨st', d', rfl, hl, -⟩ k hk
  rw [← hl] at h ⊢
  exact TreesInit.ctGet_dl st' k (by omega)

theorem treeRd_d (st : DeflateState) (h : 30 ≤ st.dyn_dtree.size) :
    TreeRd (Fam H i z b st) (.ref (CtRef.dyn_dtree b) 0) st.dyn_dtree 30 := by
  rintro _ ⟨st', d', rfl, -, hd⟩ k hk
  rw [← hd] at h ⊢
  exact ctGet_dd st' k (by omega)

end

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8} {st0 s : DeflateState}
open ZlibNgF.Proof.TreesEmitP ZlibNgF.Proof.TreesFlush ZlibNgF.Proof.DeflateAlloc
open ZlibNgF.Math.TreesOverlay (Budget room_header)

/-- The dynamic branch of `zng_tr_flush_block` (the 3 block-type bits, `send_all_trees`, `compress_block` with the
dynamic trees, the read of `opt_len`), followed by `k`, from the state that the tree construction leaves, with no
pending bytes, fewer than 8 bits waiting, and the block choice `Chosen` of the model. -/
theorem dyn_then {pbo sbo n : Nat} {r : Int32} (TP : TPost st0 d sbo n r s)
    (hpb : s.pending_buf = .val (.ref (.heap b) pbo)) (hsb : s.sym_buf = .val (.ref (.heap b) sbo))
    (hsn : s.sym_next.toNat = 3 * n) (hsbo : sbo = pbo + s.lit_bufsize.toNat + 8)
    (hend : pbo + 4 * s.lit_bufsize.toNat + 64 ≤ d.size) (hn : n + 1 ≤ s.lit_bufsize.toNat)
    (hpow : ∃ k, 7 ≤ k ∧ k ≤ 15 ∧ s.lit_bufsize.toNat = 2 ^ k)
    (hdist : ∀ j, j < n → symDist d sbo j ≤ 32768) (v0 : 0 ≤ s.bi_valid.toInt) (v8 : s.bi_valid.toInt < 8)
    (hp0 : s.pending.toNat = 0) (last : Int32) (hl0 : 0 ≤ last.toInt) (hl1 : last.toInt ≤ 1)
    (hch : ZlibNgF.Math.OverlayDynamic.Chosen (symsOf d sbo n)) {β : Type} (k : M β) (Q : β → Heap → Prop)
    (hk : ∀ H', BlkPost H i z b s d pbo H' → Sat H' k Q) :
    Sat (SH H i z b s d) (do
      ZlibNg.TreesEmit.zng_tr_emit_tree (some b) DYN_TREES last
      let __do_lift ← rdD (some b) fun x => x.l_desc.max_code
      let lc ← chkI32 (__do_lift.toInt + 1)
      let __do_lift ← rdD (some b) fun x => x.d_desc.max_code
      let dc ← chkI32 (__do_lift.toInt + 1)
      let bc ← chkI32 (r.toInt + 1)
      send_all_trees (some b) lc dc bc
      let __do_lift ← dynLtreeP (some b)
      let __do_lift_1 ← dynDtreeP (some b)
      compress_block (some b) __do_lift __do_lift_1
      let _ ← rdD (some b) fun x => x.opt_len
      k) Q := by
  obtain ⟨kp, hk7, hk15, hB⟩ := hpow
  have hB128 : 128 ≤ s.lit_bufsize.toNat := by
    rw [hB]; exact Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk7)
  have hB32 : s.lit_bufsize.toNat ≤ 32768 := by
    rw [hB]; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hk15) (by decide)
  have hbud := dynBudget s.lit_bufsize.toNat s.bi_valid.toInt.toNat (symsOf d sbo n) ⟨kp, hk7, hk15, hB⟩
    (by omega) (by rw [symsOf_length]; exact hn) (symsOf_valid hdist) hch
  have hHb := header_bound (symsOf d sbo n)
  have ⟨mL1, mL2⟩ := mcL_le d sbo n
  have ⟨mD1, mD2⟩ := mcD_le d sbo n
  have r3 := TP.r3; have r18 := TP.r18
  -- the block-type bits
  refine Sat.bind (Sat.mono (emit_tree_SH hpb v0 (by omega) (by omega) (by omega) _ last (by decide) (by decide)
    (by show 2 * (2 : Int32).toInt + last.toInt < _; simp; omega)) ?_)
  rintro _ _ ⟨np1, bb1, bv1, d1, rfl, w1, hacc1, hbv1, hle1, hge1⟩
  have e1 := toInt32_toInt bv1 hbv1
  have hsz1 : d1.size = d.size := w1.1
  -- the counts
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  rw [show (({ s with pending := np1, bi_buf := bb1, bi_valid := bv1.toInt32 } : DeflateState).l_desc.max_code.toInt + 1)
    = mcL d sbo n from TP.mL]
  rw [chk_small _ (by omega) (by omega), pure_bind_M]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  rw [show (({ s with pending := np1, bi_buf := bb1, bi_valid := bv1.toInt32 } : DeflateState).d_desc.max_code.toInt + 1)
    = mcD d sbo n from TP.mD]
  rw [chk_small _ (by omega) (by omega), pure_bind_M]
  rw [chk_small _ (by omega) (by omega), pure_bind_M]
  -- the tree header
  have hroom : 8 * np1.toNat + bv1.toInt32.toInt.toNat +
      satBits { s with pending := np1, bi_buf := bb1, bi_valid := bv1.toInt32 } (mcL d sbo n) (mcD d sbo n)
        (r.toInt.toNat + 1) ≤ 8 * s.lit_bufsize.toNat + 7 := by
    have h := TP.hdr
    unfold satBits at h ⊢
    unfold Budget at hbud
    rw [e1]; simp only [Int.toNat_natCast]; omega
  refine Sat.bind (Sat.mono (send_all_trees_SH (st := { s with pending := np1, bi_buf := bb1, bi_valid := bv1.toInt32 })
    (d := d1) (pbo := pbo) (Lim := s.lit_bufsize.toNat) (mL := mcL d sbo n) (mD := mcD d sbo n)
    (nb := r.toInt.toNat + 1) ⟨hpb, by omega, by omega, by show 19 ≤ s.bl_tree.size; rw [TP.bsize]; omega,
      fun t ht => TP.bl7 t ht, mL1, mL2, mD1, mD2, by omega, by omega,
      by show _ < s.dyn_ltree.size; rw [TP.lsize]; simp only [HEAP_SIZE, L_CODES]; omega,
      by show _ < s.dyn_dtree.size; rw [TP.dsize]; omega, TP.lg, TP.dg, TP.l15, TP.d15,
      by rw [e1]; omega, by rw [e1]; omega⟩
    _ _ _ (ofInt_small _ (by omega) (by omega)) (ofInt_small _ (by omega) (by omega))
    (by rw [ofInt_small _ (by omega) (by omega)]; omega) hroom) ?_)
  rintro _ _ ⟨np2, bb2, bv2, d2, rfl, w2, hle2, hacc2, hbv2⟩
  dsimp only at w2 hle2 hacc2
  have hsz2 : d2.size = d.size := by rw [w2.1, hsz1]
  -- the symbols are untouched
  have hsat : satBits s (mcL d sbo n) (mcD d sbo n) (r.toInt.toNat + 1) = blockHeader (symsOf d sbo n) := TP.hdr
  have hnp2 : np2.toNat + 8 ≤ s.lit_bufsize.toNat + 8 := by
    refine room_header hbud np2.toNat ?_
    rw [e1] at hacc2; simp only [Int.toNat_natCast] at hacc2
    have : satBits { s with pending := np1, bi_buf := bb1, bi_valid := bv1.toInt32 } (mcL d sbo n) (mcD d sbo n)
        (r.toInt.toNat + 1) = blockHeader (symsOf d sbo n) := hsat
    omega
  have hby : ∀ m, sbo ≤ m → d2[m]! = d[m]! := fun m hm =>
    (w2.2 m (Or.inr (by omega))).trans (w1.2 m (Or.inr (by omega)))
  simp only [dynLtreeP, dynDtreeP, pure_bind_M]
  have e2 := toInt32_toInt bv2 hbv2
  refine Sat.bind (Sat.mono (compress_SH (H := H) (i := i) (z := z) (b := b)
    (st := { s with pending := np2, bi_buf := bb2, bi_valid := bv2.toInt32 }) (d := d2)
    (LT := s.dyn_ltree) (DT := s.dyn_dtree) (pbo := pbo) (sbo := sbo) (n := n)
    ⟨hpb, hsb, hsn, hsbo, by show pbo + 4 * s.lit_bufsize.toNat + 9 ≤ d2.size; omega, hn, hB32, treeRd_l _ (by rw [TP.lsize]; simp only [HEAP_SIZE, L_CODES]; omega),
      treeRd_d _ (by rw [TP.dsize]; omega), used_congr hby TP.used,
      fun j hj => by rw [(syms_congr hby j).1]; exact hdist j hj, by show 0 ≤ bv2.toInt32.toInt; rw [e2]; omega,
      by show bv2.toInt32.toInt < 64; rw [e2]; omega, ?_⟩) ?_)
  · show Budget s.lit_bufsize.toNat (8 * np2.toNat + bv2.toInt32.toInt.toNat)
      (TreesCompress.blockCosts s.dyn_ltree s.dyn_dtree d2 sbo n)
    rw [costs_congr _ _ hby, TP.costs, e2]
    rw [e1] at hacc2; simp only [Int.toNat_natCast] at hacc2 ⊢
    have : satBits { s with pending := np1, bi_buf := bb1, bi_valid := bv1.toInt32 } (mcL d sbo n) (mcD d sbo n)
        (r.toInt.toNat + 1) = blockHeader (symsOf d sbo n) := hsat
    have h3 : 8 * np2.toNat + bv2.toNat = s.bi_valid.toInt.toNat + 3 + blockHeader (symsOf d sbo n) := by omega
    rw [h3]; exact hbud
  rintro _ _ ⟨np3, bb3, bv3, d3, rfl, w3, -, hbv3, hle3, hge3⟩
  dsimp only at w3 hle3 hge3
  refine Sat.bind (Sat.of_eq (rdD_SH _) (hk _ ⟨np3, bb3, bv3, d3, rfl, ?_, hbv3, by omega, hge3⟩))
  exact WrIn.cat (WrIn.cat w1 w2 (by omega) (by omega)) w3 (by omega) (by omega)

end

end ZlibNgF.Proof.TreesFlushBlock
