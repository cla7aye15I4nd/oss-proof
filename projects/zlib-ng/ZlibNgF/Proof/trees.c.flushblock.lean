import ZlibNgF.Proof.«trees.c.flush»
import ZlibNgF.Math.OverlayTinyBudget
import ZlibNgF.Proof.«trees.c.blt»
import ZlibNgF.Proof.«trees.c.alltrees»
import ZlibNgF.Proof.«trees.c.dyn»
import ZlibNgF.Proof.«trees.c.buildspec»
import ZlibNgF.Math.TreesHdrCost

/-!
# `zng_tr_flush_block` on `SH` heaps (`ZlibNgF`)

`flush_SH`: from a state between blocks (`FCtx`: the tallied symbols counted by the frequencies, no pending bytes,
fewer than 8 bits waiting, a level above 0, the block's bytes in the window below `pending_buf` or `NULL`),
`zng_tr_flush_block` does not fault and ends in `FinPost`: only `data_type` of the stream, the state's emitter fields
and `pending_buf` changed, no symbols, `opt_len = static_len = 0`, the frequencies of `init_block`, the pending bytes
and the bits within `pending_buf`. Given `BuildTreeSpec` (the statement of `build_tree`).

The trees of a dynamic block:

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

/-! ## The whole of `zng_tr_flush_block` -/

open ZlibNgF.Proof.TreesEmitP ZlibNgF.Proof.TreesFlush ZlibNgF.Proof.TreesInit ZlibNgF.Proof.DeflateBits
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## The block and its tail -/

theorem EmitKeeps.trans' {a b c : DeflateState} (h1 : EmitKeeps a b) (h2 : EmitKeeps b c) : EmitKeeps a c := by
  unfold EmitKeeps at *
  conv => lhs; rw [h2]
  conv => lhs; rw [h1]

/-- The fields of the invariant that a block keeps: the descriptors and the sizes of the scratch and tree arrays. -/
structure Rel (st0 s : DeflateState) : Prop where
  keeps : EmitKeeps st0 s
  lsize : s.dyn_ltree.size = HEAP_SIZE
  dsize : s.dyn_dtree.size = 2 * 30 + 1
  bsize : s.bl_tree.size = 2 * 19 + 1
  pql : s.pq_leaves.size = 287
  pqs : s.pq_scratch.size = 287
  blc : s.bl_count.size = 16
  ldyn : s.l_desc.dyn_tree = st0.l_desc.dyn_tree
  lstat : s.l_desc.stat_desc = st0.l_desc.stat_desc
  ddyn : s.d_desc.dyn_tree = st0.d_desc.dyn_tree
  dstat : s.d_desc.stat_desc = st0.d_desc.stat_desc
  bldyn : s.bl_desc.dyn_tree = st0.bl_desc.dyn_tree
  blstat : s.bl_desc.stat_desc = st0.bl_desc.stat_desc

theorem Rel.step {st0 s s' : DeflateState} (R : Rel st0 s) (hk : EmitKeeps s s')
    (h1 : s'.dyn_ltree.size = HEAP_SIZE) (h2 : s'.dyn_dtree.size = 2 * 30 + 1) (h3 : s'.bl_tree.size = 2 * 19 + 1)
    (h4 : s'.pq_leaves = s.pq_leaves) (h5 : s'.pq_scratch = s.pq_scratch) (h6 : s'.bl_count = s.bl_count)
    (h7 : s'.l_desc = s.l_desc) (h8 : s'.d_desc = s.d_desc) (h9 : s'.bl_desc = s.bl_desc) : Rel st0 s' :=
  ⟨EmitKeeps.trans' R.keeps hk, h1, h2, h3, by rw [h4, R.pql], by rw [h5, R.pqs], by rw [h6, R.blc],
    by rw [h7, R.ldyn], by rw [h7, R.lstat], by rw [h8, R.ddyn], by rw [h8, R.dstat], by rw [h9, R.bldyn],
    by rw [h9, R.blstat]⟩

/-- What a block body leaves (any of the three kinds): new pending count, bit buffer and `bi_used`, the bytes
changed only in `pending_buf`, room for one more 8-byte store, fewer than 64 bits waiting. -/
def BrPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (s : DeflateState) (d : Array UInt8) (pbo : Nat)
    (H' : Heap) : Prop :=
  ∃ (np : UInt32) (bu : Int32) (bb : UInt64) (bv : UInt32) (d' : Array UInt8),
    H' = SH H i z b { s with pending := np, bi_used := bu, bi_buf := bb, bi_valid := bv.toInt32 } d' ∧
    WrIn d pbo (pbo + 4 * s.lit_bufsize.toNat + 9) d' ∧ bv.toNat < 64 ∧ np.toNat + 8 ≤ 4 * s.lit_bufsize.toNat + 9

/-- What `zng_tr_flush_block` leaves (from state `st0`, bytes `d`, stream `z0`). -/
def FinPost (H : Heap) (i : Nat) (z0 : ZStream) (b : Nat) (st0 : DeflateState) (d : Array UInt8) (pbo : Nat)
    (H' : Heap) : Prop :=
  ∃ (dt : Int32) (st' : DeflateState) (d' : Array UInt8), H' = SH H i { z0 with data_type := dt } b st' d' ∧
    WrIn d pbo (pbo + 4 * st0.lit_bufsize.toNat + 9) d' ∧ Rel st0 st' ∧ st'.sym_next = 0 ∧ st'.opt_len = 0 ∧
    st'.static_len = 0 ∧ IbFreq st'.dyn_ltree st'.dyn_dtree st'.bl_tree ∧
    st'.pending.toNat * 8 + st'.bi_valid.toInt.toNat ≤ 8 * (4 * st0.lit_bufsize.toNat + 9) ∧
    0 ≤ st'.bi_valid.toInt ∧ st'.bi_valid.toInt < 64

section
variable {H : Heap} {i : Nat} {b : Nat} {d : Array UInt8}

/-- `init_block` and, for the last block, `zng_tr_emit_align`. -/
theorem tail_SH {z0 z : ZStream} {st0 s : DeflateState} {pbo : Nat} (hz : z = { z0 with data_type := z.data_type })
    (R : Rel st0 s) (hpb : s.pending_buf = .val (.ref (.heap b) pbo))
    (hend : pbo + 4 * s.lit_bufsize.toNat + 64 ≤ d.size) (hB : s.lit_bufsize.toNat ≤ 32768)
    (hlb : s.lit_bufsize = st0.lit_bufsize) (last : Int32)
    {H' : Heap} (q : BrPost H i z b s d pbo H') :
    Sat H' (do
      init_block (some b)
      if (last != 0) = true then ZlibNg.TreesEmit.zng_tr_emit_align (some b) else pure ())
      (fun _ H'' => FinPost H i z0 b st0 d pbo H'') := by
  obtain ⟨np, bu, bb, bv, d', rfl, w, hbv, hnp⟩ := q
  have e := toInt32_toInt bv hbv
  have hsz : d'.size = d.size := w.1
  refine Sat.bind (Sat.mono (init_block_SH (H := H) (i := i) (z := z) (b := b) (d := d')
    { s with pending := np, bi_used := bu, bi_buf := bb, bi_valid := bv.toInt32 } R.lsize R.dsize R.bsize) ?_)
  rintro _ _ ⟨A, B, C, rfl, hI⟩
  have R1 : Rel st0 (ibS { s with pending := np, bi_used := bu, bi_buf := bb, bi_valid := bv.toInt32 } A B C) :=
    R.step rfl hI.1 hI.2.1 hI.2.2.1 rfl rfl rfl rfl rfl rfl
  have ez : ∀ (st' : DeflateState) (d' : Array UInt8),
      SH H i z b st' d' = SH H i { z0 with data_type := z.data_type } b st' d' := fun _ _ => by rw [← hz]
  split
  · refine Sat.mono (windup_SH (st := ibS { s with pending := np, bi_used := bu, bi_buf := bb, bi_valid := bv.toInt32 } A B C)
      (pbo := pbo) hpb (by show 0 ≤ bv.toInt32.toInt; rw [e]; omega) (by show bv.toInt32.toInt < 64; rw [e]; omega)
      (by show pbo + np.toNat + 8 ≤ d'.size; omega) (by show np.toNat + 8 < _; omega)) ?_
    rintro _ _ ⟨np', bu', d'', rfl, w', h1, h2⟩
    have hK : (((ibS { s with pending := np, bi_used := bu, bi_buf := bb, bi_valid := bv.toInt32 } A B C).bi_valid.toInt
        + 7).toNat / 8) ≤ 8 := by show (bv.toInt32.toInt + 7).toNat / 8 ≤ 8; rw [e]; omega
    refine ⟨z.data_type, _, d'', ez _ _, ?_, R1.step rfl hI.1 hI.2.1 hI.2.2.1 rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl, hI,
      ?_, show 0 ≤ (0 : Int32).toInt by decide, show (0 : Int32).toInt < 64 by decide⟩
    · rw [← hlb]
      exact w.trans (w'.widen (by omega) (by simp only [ibS] at h1 h2 ⊢; omega)) (Nat.le_refl _) (Nat.le_refl _)
    · show np'.toNat * 8 + (0 : Int32).toInt.toNat ≤ _
      rw [← hlb]; simp only [ibS] at h1 h2; simp only [show (0 : Int32).toInt.toNat = 0 from rfl]; omega
  · refine Sat.pure ⟨z.data_type, _, d', ez _ _, by rw [← hlb]; exact w, R1, rfl, rfl, rfl, hI, ?_, ?_, ?_⟩
    · show np.toNat * 8 + bv.toInt32.toInt.toNat ≤ _
      rw [e, ← hlb]; simp only [Int.toNat_natCast]; omega
    · show 0 ≤ bv.toInt32.toInt; rw [e]; omega
    · show bv.toInt32.toInt < 64; rw [e]; omega

end
/-- The tail of `zng_tr_flush_block` after the block choice inputs (copied; `flush_eq`). -/
def outerJp (st : StatePtr) (buf : BPtr) (stored_len : UInt32) (last : Int32) (opt_lenb static_lenb : UInt32)
    (max_blindex : Int32) : M Unit := do
  let bufNonNull : Bool := match buf with | .null => false | _ => true
  if stored_len + 4 <= opt_lenb && bufNonNull then
    zng_tr_stored_block st buf stored_len last
  else if static_lenb == opt_lenb then
    ZlibNg.TreesEmit.zng_tr_emit_tree st STATIC_TREES last
    compress_block st (.ref .static_ltree 0) (.ref .static_dtree 0)
    let _ ← rdD st (·.static_len)
  else
    ZlibNg.TreesEmit.zng_tr_emit_tree st DYN_TREES last
    let lc ← chkI32 ((← rdD st (·.l_desc.max_code)).toInt + 1)
    let dc ← chkI32 ((← rdD st (·.d_desc.max_code)).toInt + 1)
    let bc ← chkI32 (max_blindex.toInt + 1)
    send_all_trees st lc dc bc
    compress_block st (← dynLtreeP st) (← dynDtreeP st)
    let _ ← rdD st (·.opt_len)
  init_block st
  if last != 0 then
    ZlibNg.TreesEmit.zng_tr_emit_align st

/-- The trees and the block choice of `zng_tr_flush_block` (copied; `flush_eq`). -/
def innerJp (st : StatePtr) (buf : BPtr) (stored_len : UInt32) (last : Int32) : M Unit := do
  build_tree st .l_desc
  build_tree st .d_desc
  let max_blindex ← build_bl_tree st
  let opt_lenb : UInt32 := ((← rdD st (·.opt_len)) + 3 + 7) >>> 3
  let static_lenb : UInt32 := ((← rdD st (·.static_len)) + 3 + 7) >>> 3
  if static_lenb <= opt_lenb || (← rdD st (·.strategy)) == Z_FIXED then
    outerJp st buf stored_len last static_lenb static_lenb max_blindex
  else
    outerJp st buf stored_len last opt_lenb static_lenb max_blindex

theorem flush_eq (st : StatePtr) (buf : BPtr) (stored_len : UInt32) (last : Int32) :
    zng_tr_flush_block st buf stored_len last = (do
      if (← rdD st (·.sym_next)) == 0 then
        wrD st fun s => { s with static_len := 7 }
        outerJp st buf stored_len last 0 0 0
      else if (← rdD st (·.level)) > 0 then
        let strm ← (← rdD st (·.strm)).get
        if (← rdZ strm (·.data_type)) == Z_UNKNOWN then
          let dt ← detect_data_type st
          let strm ← (← rdD st (·.strm)).get
          wrZ strm fun z => { z with data_type := dt }
        innerJp st buf stored_len last
      else
        outerJp st buf stored_len last (stored_len + 5) (stored_len + 5) 0) := by
  rfl

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8} {st : DeflateState}

/-- The static branch of `zng_tr_flush_block` followed by `k` (as `static_branch_SH`). -/
theorem static_then {pbo sbo n : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hsb : st.sym_buf = .val (.ref (.heap b) sbo)) (hsn : st.sym_next.toNat = 3 * n)
    (hsbo : sbo = pbo + st.lit_bufsize.toNat + 8) (hend : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size)
    (hn : n + 1 ≤ st.lit_bufsize.toNat) (hB : 128 ≤ st.lit_bufsize.toNat) (hlb : st.lit_bufsize.toNat ≤ 32768)
    (hdist : ∀ j, j < n → symDist d sbo j ≤ 32768) (v0 : 0 ≤ st.bi_valid.toInt) (v8 : st.bi_valid.toInt < 8)
    (hp0 : st.pending.toNat = 0) (last : Int32) (hl0 : 0 ≤ last.toInt) (hl1 : last.toInt ≤ 1) {β : Type} (k : M β)
    (Q : β → Heap → Prop) (hk : ∀ H', BlkPost H i z b st d pbo H' → Sat H' k Q) :
    Sat (SH H i z b st d) (do
      ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STATIC_TREES last
      ZlibNg.Trees.compress_block (some b) (.ref .static_ltree 0) (.ref .static_dtree 0)
      let _ ← rdD (some b) (·.static_len)
      k) Q := by
  refine Sat.bind (Sat.mono (emit_tree_SH hpb v0 (by omega) (by omega) (by omega) _ last (by decide) (by decide)
    (by show 2 * (1 : Int32).toInt + last.toInt < _; simp; omega)) ?_)
  rintro _ _ ⟨np, bb, bv, d1, rfl, w1, hacc1, hbv1, hle1, hge1⟩
  have e1 := toInt32_toInt bv hbv1
  have hsz1 : d1.size = d.size := w1.1
  have hdist1 : ∀ j, j < n → symDist d1 sbo j ≤ 32768 := fun j hj => by
    have a0 := w1.2 (sbo + 3 * j) (Or.inr (by omega))
    have a1 := w1.2 (sbo + 3 * j + 1) (Or.inr (by omega))
    unfold symDist; rw [a0, a1]; exact hdist j hj
  refine Sat.bind (Sat.mono (compress_static_SH (st := { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 })
    (d := d1) (n := n) hpb hsb hsn hsbo (by dsimp only; omega) hn (by dsimp only; omega) hlb hdist1
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)) ?_)
  rintro _ _ ⟨np2, bb2, bv2, d2, rfl, w2, -, hbv2, hle2, hge2⟩
  dsimp only at w2 hle2 hge2
  refine Sat.bind (Sat.of_eq (rdD_SH _) (hk _ ⟨np2, bb2, bv2, d2, rfl, ?_, hbv2, by omega, hge2⟩))
  exact WrIn.cat w1 w2 (by omega) (by omega)

theorem blk_br {pbo : Nat} {H' : Heap} (hp0 : st.pending.toNat = 0) (q : BlkPost H i z b st d pbo H') :
    BrPost H i z b st d pbo H' := by
  obtain ⟨np, bb, bv, d', rfl, w, hbv, -, hge⟩ := q
  exact ⟨np, st.bi_used, bb, bv, d', rfl, w.widen (by omega) (Nat.le_refl _), hbv, hge⟩

/-- `zng_tr_stored_block` followed by `k`, with room for the block in `pending_buf`. -/
theorem stored_then {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hend : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size) (v0 : 0 ≤ st.bi_valid.toInt) (v8 : st.bi_valid.toInt < 8)
    (hp0 : st.pending.toNat = 0) (buf : BPtr) (len : UInt32) (os : Nat) (hbuf : buf = .ref (.heap b) os)
    (hos : os + len.toNat ≤ pbo) (hlen : len.toNat + 6 ≤ 4 * st.lit_bufsize.toNat) (hlb : st.lit_bufsize.toNat ≤ 32768)
    (last : Int32) {β : Type}
    (k : M β) (Q : β → Heap → Prop) (hk : ∀ H', BrPost H i z b st d pbo H' → Sat H' k Q) :
    Sat (SH H i z b st d) (do
      ZlibNg.Trees.zng_tr_stored_block (some b) buf len last
      k) Q := by
  refine Sat.bind (Sat.mono (stored_block_X_SH hpb v0 (by omega) buf len (Or.inr ⟨os, hbuf, hos⟩) (by omega)
    (by omega) last) ?_)
  rintro _ _ ⟨np2, pend, bu, d', rfl, hpe, hle, hb2, w⟩
  exact hk _ ⟨pend, bu, 0, 0, d', rfl, w.widen (by omega) (by omega), by decide, by omega⟩

end

section
variable {H : Heap} {i : Nat} {b : Nat} {d : Array UInt8}

theorem u32_add4 (len : UInt32) (h : len.toNat ≤ 65536) : (len + 4).toNat = len.toNat + 4 := by
  rw [UInt32.toNat_add]; simp; omega

/-- The block choice and the tail of `zng_tr_flush_block` (`outerJp`): from a state `s` that keeps the fields of the
invariant of `st0`, with the inputs `opt_lenb` / `static_lenb` / `max_blindex`; the stored block fits when it is
chosen, and the dynamic block has the trees of `TPost` and the model's choice. -/
theorem outer_SH {z0 z : ZStream} {st0 s : DeflateState} {pbo sbo n : Nat}
    (hz : z = { z0 with data_type := z.data_type }) (R : Rel st0 s) (hlb : s.lit_bufsize = st0.lit_bufsize)
    (hpb : s.pending_buf = .val (.ref (.heap b) pbo)) (hsb : s.sym_buf = .val (.ref (.heap b) sbo))
    (hsn : s.sym_next.toNat = 3 * n) (hsbo : sbo = pbo + s.lit_bufsize.toNat + 8)
    (hend : pbo + 4 * s.lit_bufsize.toNat + 64 ≤ d.size) (hn : n + 1 ≤ s.lit_bufsize.toNat)
    (hpow : ∃ k, 7 ≤ k ∧ k ≤ 15 ∧ s.lit_bufsize.toNat = 2 ^ k)
    (hdist : ∀ j, j < n → symDist d sbo j ≤ 32768) (v0 : 0 ≤ s.bi_valid.toInt) (v8 : s.bi_valid.toInt < 8)
    (hp0 : s.pending.toNat = 0) (buf : BPtr) (len : UInt32)
    (hbuf : buf = .null ∨ ((∃ os, buf = .ref (.heap b) os ∧ os + len.toNat ≤ pbo) ∧ len.toNat ≤ 65536))
    (last : Int32) (hl0 : 0 ≤ last.toInt) (hl1 : last.toInt ≤ 1) (ol sl : UInt32) (mb : Int32)
    (hroom : len.toNat + 4 ≤ ol.toNat → len.toNat + 6 ≤ 4 * s.lit_bufsize.toNat)
    (hdyn : ol ≠ sl → TPost st0 d sbo n mb s ∧ Chosen (symsOf d sbo n)) :
    Sat (SH H i z b s d) (outerJp (some b) buf len last ol sl mb) (fun _ H' => FinPost H i z0 b st0 d pbo H') := by
  obtain ⟨kp, hk7, hk15, hB⟩ := hpow
  have hB128 : 128 ≤ s.lit_bufsize.toNat := by
    rw [hB]; exact Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk7)
  have hB32 : s.lit_bufsize.toNat ≤ 32768 := by
    rw [hB]; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hk15) (by decide)
  have tail := fun H' (q : BrPost H i z b s d pbo H') => tail_SH (H := H) hz R hpb hend hB32 hlb last q
  unfold outerJp
  try simp only []
  split
  · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    split
    · exact static_then hpb hsb hsn hsbo hend hn hB128 hB32 hdist v0 v8 hp0 last hl0 hl1 _ _
        fun H' q => tail H' (blk_br hp0 q)
    · rename_i hne
      have hne' : ol ≠ sl := fun e => hne (by rw [e]; simp)
      obtain ⟨TP, hch⟩ := hdyn hne'
      exact dyn_then TP hpb hsb hsn hsbo hend hn ⟨kp, hk7, hk15, hB⟩ hdist v0 v8 hp0 last hl0 hl1 hch _ _
        fun H' q => tail H' (blk_br hp0 q)
  · rename_i hnn
    rcases hbuf with rfl | ⟨⟨os, rfl, hos⟩, h64⟩
    · exact absurd rfl hnn
    by_cases h4 : len + 4 ≤ ol
    · simp only [h4, decide_true, Bool.and_self, ↓reduceIte]
      have h4' := UInt32.le_iff_toNat_le.mp h4
      rw [u32_add4 len h64] at h4'
      exact stored_then hpb hend v0 v8 hp0 _ len os rfl hos (hroom h4') hB32 last _ _ tail
    · simp only [h4, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split
      · exact static_then hpb hsb hsn hsbo hend hn hB128 hB32 hdist v0 v8 hp0 last hl0 hl1 _ _
          fun H' q => tail H' (blk_br hp0 q)
      · rename_i hne
        have hne' : ol ≠ sl := fun e => hne (by rw [e]; simp)
        obtain ⟨TP, hch⟩ := hdyn hne'
        exact dyn_then TP hpb hsb hsn hsbo hend hn ⟨kp, hk7, hk15, hB⟩ hdist v0 v8 hp0 last hl0 hl1 hch _ _
          fun H' q => tail H' (blk_br hp0 q)
end

/-- What `zng_tr_flush_block` needs of its state (from `DWork` and `FlushBlockPre`). -/
structure FCtx (i b : Nat) (st : DeflateState) (d : Array UInt8) (pbo sbo n : Nat) (buf : BPtr) (len : UInt32) :
    Prop where
  T : TCtx b st d sbo n
  hpb : st.pending_buf = .val (.ref (.heap b) pbo)
  hsb : st.sym_buf = .val (.ref (.heap b) sbo)
  hsbo : sbo = pbo + st.lit_bufsize.toNat + 8
  hend : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size
  hn : n + 1 ≤ st.lit_bufsize.toNat
  hpow : ∃ k, 7 ≤ k ∧ k ≤ 15 ∧ st.lit_bufsize.toNat = 2 ^ k
  hp0 : st.pending.toNat = 0
  v0 : 0 ≤ st.bi_valid.toInt
  v8 : st.bi_valid.toInt < 8
  hlev : 0 < st.level
  hbuf : buf = .null ∨ ((∃ os, buf = .ref (.heap b) os ∧ os + len.toNat ≤ pbo) ∧ len.toNat ≤ 65536)
  hstrm : st.strm = .val (some i)

theorem lenb (x : UInt32) (h : x.toNat + 10 < 2 ^ 32) : ((x + 3 + 7) >>> 3).toNat = (x.toNat + 10) / 8 := by
  rw [UInt32.toNat_shiftRight, UInt32.toNat_add, UInt32.toNat_add]
  simp only [Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reducePow, Nat.reduceMod]
  omega

section
variable {H : Heap} {i : Nat} {b : Nat} {d : Array UInt8} {st : DeflateState} {pbo sbo n : Nat} {buf : BPtr}
  {len : UInt32}

theorem FCtx.rel (F : FCtx i b st d pbo sbo n buf len) : Rel st st :=
  ⟨rfl, F.T.lsize, F.T.dsize, F.T.bsize, F.T.pql, F.T.pqs, F.T.blc, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The trees, the block choice and the tail (`innerJp`), on any stream record `z` that differs from `z0` at most in
`data_type`. -/
theorem inner_SH (hbt : BuildTreeSpec) (F : FCtx i b st d pbo sbo n buf len) {z0 z : ZStream}
    (hz : z = { z0 with data_type := z.data_type }) (last : Int32) (hl0 : 0 ≤ last.toInt) (hl1 : last.toInt ≤ 1) :
    Sat (SH H i z b st d) (innerJp (some b) buf len last) (fun _ H' => FinPost H i z0 b st d pbo H') := by
  unfold innerJp
  refine trees_then hbt F.T _ _ ?_
  intro r s3 TP
  have R : Rel st s3 := ⟨TP.keeps, TP.lsize, TP.dsize, TP.bsize, TP.pql, TP.pqs, TP.blc, TP.ldyn, TP.lstat, TP.ddyn,
    TP.dstat, TP.bldyn, TP.blstat⟩
  have k := TP.keeps
  have hlb : s3.lit_bufsize = st.lit_bufsize := by rw [k]
  have hpb : s3.pending_buf = st.pending_buf := by rw [k]
  have hsb : s3.sym_buf = st.sym_buf := by rw [k]
  have hn := F.T.hn
  have hn1 := F.hn
  have hBC := blockCosts_sum_le (symsOf d sbo n)
  rw [symsOf_length] at hBC
  have h256 := litLens_le (symsOf d sbo n) 256
  have hHb := header_bound (symsOf d sbo n)
  have hSl := staticLen_le (symsOf d sbo n)
  rw [symsOf_length] at hSl
  have hol := lenb s3.opt_len (by rw [TP.opt]; unfold optLen; omega)
  have hsl := lenb s3.static_len (by rw [TP.stat]; omega)
  rw [TP.opt] at hol
  rw [TP.stat] at hsl
  have hdist : ∀ j, j < n → symDist d sbo j ≤ 32768 := fun j hj => F.T.sym.dist j (by rw [F.T.n3]; exact hj)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  try simp only []
  have common := fun (ol : UInt32) (hol' : ol.toNat ≤ (staticLen (symsOf d sbo n) + 10) / 8)
      (hdyn : ol ≠ (s3.static_len + 3 + 7) >>> 3 → TPost st d sbo n r s3 ∧ Chosen (symsOf d sbo n)) =>
    outer_SH (H := H) (i := i) (d := d) (n := n) hz R hlb (by rw [hpb]; exact F.hpb)
      (by rw [hsb]; exact F.hsb) (by rw [TP.sym_next]; exact F.T.hsn) (by rw [hlb]; exact F.hsbo)
      (by rw [hlb]; exact F.hend) (by rw [hlb]; exact F.hn) (by rw [hlb]; exact F.hpow) hdist
      (by rw [TP.bi_valid]; exact F.v0) (by rw [TP.bi_valid]; exact F.v8) (by rw [TP.pending]; exact F.hp0) buf len F.hbuf last
      hl0 hl1 ol ((s3.static_len + 3 + 7) >>> 3) r (fun h4 => by rw [hlb]; omega) hdyn
  split
  · exact common _ (by rw [hsl]; exact Nat.le_refl _) (fun h => absurd rfl h)
  · rename_i hc
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
    have hlt := hc.1
    rw [UInt32.le_iff_toNat_le, hol, hsl] at hlt
    exact common _ (by rw [hol]; omega) (fun _ => ⟨TP, by unfold Chosen; omega⟩)

/-- **`zng_tr_flush_block`** on `SH` heaps, from a state between blocks with no pending bytes and fewer than 8 bits
waiting, at a level above 0, for `last` 0 or 1: no fault, `FinPost`. -/
theorem flush_SH (hbt : BuildTreeSpec) (F : FCtx i b st d pbo sbo n buf len) {z : ZStream} (last : Int32)
    (hl0 : 0 ≤ last.toInt) (hl1 : last.toInt ≤ 1) :
    Sat (SH H i z b st d) (zng_tr_flush_block (some b) buf len last) (fun _ H' => FinPost H i z b st d pbo H') := by
  rw [flush_eq]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  try simp only []
  split
  · rename_i h0
    have hs0 : st.sym_next.toNat = 0 := by rw [beq_iff_eq.mp h0]; rfl
    have n0 : n = 0 := by have := F.T.hsn; omega
    subst n0
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    exact outer_SH (st0 := st) (s := { st with static_len := 7 }) (z := z) rfl ⟨rfl, F.T.lsize, F.T.dsize, F.T.bsize, F.T.pql, F.T.pqs, F.T.blc, rfl, rfl,
      rfl, rfl, rfl, rfl⟩ rfl F.hpb F.hsb F.T.hsn F.hsbo F.hend F.hn F.hpow (fun j hj => absurd hj (by omega))
      F.v0 F.v8 F.hp0 buf len F.hbuf last hl0 hl1 0 0 0 (fun h => by simp at h) (fun h => absurd rfl h)
  · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    try simp only []
    split
    · refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.bind (Sat.of_eq (ival_get F.hstrm _) ?_)))
      refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
      try simp only []
      split
      · refine Sat.bind (Sat.mono (TreesInit.detect_SH st (by rw [F.T.lsize]; simp only [HEAP_SIZE, L_CODES]; omega)) ?_)
        rintro dt _ rfl
        refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.bind (Sat.of_eq (ival_get F.hstrm _) ?_)))
        refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
        exact inner_SH hbt F (z0 := z) rfl last hl0 hl1
      · exact inner_SH hbt F (z0 := z) rfl last hl0 hl1
    · rename_i hl
      exact absurd F.hlev hl

end

end ZlibNgF.Proof.TreesFlushBlock
