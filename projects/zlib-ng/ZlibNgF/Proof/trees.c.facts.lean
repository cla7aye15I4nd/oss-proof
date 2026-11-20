import ZlibNgF.Proof.«trees.c.flushblock»

/-!
# `TreesFacts` from the statement of `build_tree` (`ZlibNgF`)

Every field of `TreesFacts` (`Proof/deflate.c.facts.lean`) except `flush_block` and `flush_block_clears` is proved
in `Proof/trees_emit.h.static.lean`; `treesFacts_of_flush` assembles the structure from proofs of those two.
`flush_block_ok` / `flush_block_clears_ok` lift `flush_SH` (`Proof/trees.c.flushblock.lean`) from `SH` heaps to the
working state of `deflate` (`DWork`, `FlushBlockPre`), so `treesFacts_of : BuildTreeSpec → TreesFacts`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesFactsP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.TreesEmitP

/-- `TreesFacts`, given its `flush_block` and `flush_block_clears` fields. -/
theorem treesFacts_of_flush
    (hf : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32), 0 ≤ last → last ≤ 1 →
      EmitOk s b (FlushBlockPre b buf len) (fun _ => 0) (fun st => 4 * st.lit_bufsize.toNat + 9)
        (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last))
    (hc : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32), 0 ≤ last → last ≤ 1 →
      EmitClears s b (FlushBlockPre b buf len) (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last)) :
    TreesFacts where
  flush_block := hf
  flush_block_clears := hc
  stored_block := stored_block_ok
  align := align_ok
  emit_lit := emit_lit_ok
  emit_dist := emit_dist_ok
  emit_tree := emit_tree_ok
  emit_end_block := emit_end_block_ok
  emit_align := emit_align_ok

/-! ## `flush_block` and `flush_block_clears` from `flush_SH` -/

section
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesFlushBlock
open ZlibNgF.Proof.TreesBuildSpec (BuildTreeSpec)
open ZlibNgF.Proof.InflateSync (Sat)

/-- The run of `zng_tr_flush_block` from the working state of `FLUSH_BLOCK_ONLY`: `FinPost`. -/
theorem flush_run (hbt : BuildTreeSpec) {s : StreamPtr} {b : Nat} {buf : BPtr} {len : UInt32} {last : Int32}
    (h0 : 0 ≤ last) (h1 : last ≤ 1) {h : Heap} {st : DeflateState} (hw : DWork h s) (hs : DStateIs h s b st)
    (hpre : FlushBlockPre b buf len st) :
    ∃ i z d pbo al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
      h.bytes b = some d ∧ h.dallocsOf b = some al ∧ DCore h s z b (dview { st with bi_valid := 0 }) al ∧
      st.pending_buf = .val (.ref (.heap b) pbo) ∧
      ∃ h', C.run (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last) h = .ok ((), h') ∧
        FinPost h i z b st d pbo h' := by
  obtain ⟨i, z, b', st0, al, rfl, hz, hb, hst, hal, b0, b64, c, -, -⟩ := hw
  obtain ⟨i1, z1, e1, hz1, hb1, hst1⟩ := hs
  obtain rfl := Option.some.inj e1
  rw [hz] at hz1; obtain rfl := Option.some.inj hz1
  rw [hb] at hb1; obtain rfl := (Option.some.inj hb1).symm
  rw [hst] at hst1; obtain rfl := (Option.some.inj hst1).symm
  obtain ⟨hp0, hlev, hv8, hbuf⟩ := hpre
  obtain ⟨-, -, -, hB1, hB2, -, hse⟩ := c.sizes
  obtain ⟨d, wo, po, ho, pbo, hd, hw, hp, hh, hpb, l1, l2, l3, l4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  simp only [dview] at hB1 hB2 hse hw hp hh hpb l1 l2 l3 l4 hsb hpo hpoo hpe
  obtain ⟨d0, sbo, hd0, hs0, hsym⟩ := c.symv
  obtain rfl : d = d0 := Option.some.inj (hd.symm.trans hd0)
  simp only [dview] at hs0 hsym
  rw [hsb] at hs0
  obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hs0 with e1; injection e1
  have hsyms := c.syms
  simp only [dview] at hsyms
  have hn3 := hsyms.2
  have hnle := UInt32.le_iff_toNat_le.mp hsyms.1
  have hl := c.look
  have hst65 := (strstart_toInt32 c).2
  obtain ⟨tl, td, tb⟩ := c.trees
  obtain ⟨sl, ss, sc⟩ := c.scratch
  obtain ⟨bo, bs, bz⟩ := c.blk
  obtain ⟨ld, ls, dd, ds, bld, bls⟩ := c.descs
  simp only [dview] at hl hst65 tl td tb sl ss sc bo bs bz ld ls dd ds bld bls
  have hpow := c.lpow
  simp only [dview] at hpow
  have hstrm := c.strm
  simp only [dview] at hstrm
  have hlev' : 0 < st.level := hlev
  have hv0 : 0 ≤ st.bi_valid.toInt := by have := Int32.le_iff_toInt_le.mp b0; simpa using this
  have hv8' : st.bi_valid.toInt < 8 := by have := Int32.lt_iff_toInt_lt.mp hv8; simpa using this
  have hst' : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  have F : FCtx i b st d pbo (pbo + st.lit_bufsize.toNat + 8) (st.sym_next.toNat / 3) buf len := {
    T := {
      sym := hsym
      hsn := by omega
      hn := by omega
      lsize := tl
      dsize := td
      bsize := tb
      pql := sl
      pqs := ss
      blc := sc
      opt0 := bo
      stat0 := bs
      bl0 := bz
      ldyn := ld
      lstat := ls
      ddyn := dd
      dstat := ds
      bldyn := bld
      blstat := bls }
    hpb := hpb
    hsb := hsb
    hsbo := rfl
    hend := l4
    hn := by omega
    hpow := hpow
    hp0 := by rw [hp0]; rfl
    v0 := hv0
    v8 := hv8'
    hlev := hlev'
    hbuf := by
      rcases hbuf with h | ⟨h, -⟩ | ⟨wo1, k, hwo1, rfl, hk⟩
      · exact Or.inl h
      · exact Or.inl h
      · rw [hw] at hwo1
        injection hwo1 with e; injection e with _ e; subst e
        have : po ≤ pbo := by omega
        exact Or.inr ⟨⟨wo + k, rfl, by omega⟩, by omega⟩
    hstrm := hstrm }
  have S := flush_SH (H := h) (z := z) hbt F last (by have := Int32.le_iff_toInt_le.mp h0; simpa using this)
    (by have := Int32.le_iff_toInt_le.mp h1; simpa using this)
  rw [DeflateReset.SH_self hz hst' hd] at S
  obtain ⟨r, h', e, q⟩ := S
  exact ⟨i, z, d, pbo, al, rfl, hz, hb, hst, hd, hal, c, hpb, h', e, q⟩


/-- **`flush_block`** of `TreesFacts`, from `BuildTreeSpec`. -/
theorem flush_block_ok (hbt : BuildTreeSpec) (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32)
    (h0 : 0 ≤ last) (h1 : last ≤ 1) :
    EmitOk s b (FlushBlockPre b buf len) (fun _ => 0) (fun st => 4 * st.lit_bufsize.toNat + 9)
      (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last) := by
  intro h st hw hs hpre _ _
  obtain ⟨i, z, d, pbo, al, rfl, hz, hb, hst, hd, hal, c, hpb0, h', e, q⟩ := flush_run hbt h0 h1 hw hs hpre
  obtain ⟨dt, st', d', rfl, w, R, hsn, hopt, hstat, hI, hacc, bv0, bv64⟩ := q
  have hsz : d'.size = d.size := w.1
  have k := R.keeps
  have hlb : st'.lit_bufsize = st.lit_bufsize := by rw [k]
  have hpb' : st'.pending_buf = st.pending_buf := by rw [k]
  have hpo' : st'.pending_out = st.pending_out := by rw [k]
  have hsc := c.scratch
  simp only [dview] at hsc
  obtain ⟨sl, ss, sc⟩ := hsc
  have hv : dview { st' with bi_valid := 0 } = dview { st with
      bi_valid := 0
      pending := st'.pending
      sym_next := 0
      opt_len := 0
      static_len := 0
      dyn_ltree := st'.dyn_ltree
      dyn_dtree := st'.dyn_dtree
      bl_tree := st'.bl_tree } := by
    conv => lhs; rw [k]
    simp only [dview, R.ldyn, R.lstat, R.ddyn, R.dstat, R.bldyn, R.blstat, hsn, hopt, hstat, R.pql, R.pqs, R.blc, sl,
      ss, sc]
  have hpo0 : st.pending_out = st.pending_buf := by
    have := c.pout (by simp only [dview]; exact hpre.1)
    simpa [dview] using this
  obtain ⟨d0, wo, po, ho, pbo1, hd0, hw, hp, hh, hpb, l1, l2, l3, l4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  simp only [dview] at hw hp hh hpb l1 l2 l3 l4 hsb hpo hpoo hpe
  have ed : d = d0 := Option.some.inj (hd.symm.trans hd0)
  subst d0
  have epb := TreesEmitP.pend_inj hpb0 hpb
  subst pbo1
  rw [hpo0, hpb] at hpo
  have epo : poo = pbo := by injection hpo with e; injection e with _ e; exact e.symm
  subst poo
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  have hst' : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  have hbv : st'.bi_valid.toInt.toNat / 8 + st'.pending.toNat ≤ 4 * st.lit_bufsize.toNat + 9 := by omega
  refine ⟨_, e, ⟨i, { z with data_type := dt }, b, st', al, rfl, SH_streams _ _ _ _ _ _, hb,
    SH_dstate _ _ _ _ _ _, by simp [Heap.dallocsOf, SH, hda], Int32.le_iff_toInt_le.mpr (by simpa using bv0),
    Int32.lt_iff_toInt_lt.mpr (by simpa using bv64), ?_,
    ⟨pbo, pbo, by rw [hpb', hpb], by rw [hpo', hpo0, hpb], by rw [hlb]; omega⟩,
    fun hn => absurd hsn hn⟩, DeflateReset.dframe_SH h i _ b st' d',
    ⟨i, z, { z with data_type := dt }, rfl, hz, SH_streams _ _ _ _ _ _, by cases z; rfl⟩,
    fun pbo2 hpb2 => ?_, ?_⟩
  · rw [hv]
    have hsym : SymOk d' (pbo + st.lit_bufsize.toNat + 8) 0 st'.dyn_ltree st'.dyn_dtree := by
      refine ⟨fun j hj => by simp at hj, fun c hc => ?_, fun c hc => ?_⟩
      · rw [hI.2.2.2.1 c hc]; simp [lCount]
      · rw [hI.2.2.2.2.1 c hc]; simp [dCount]
    have tl := hI.1
    have td := hI.2.1
    have tb := hI.2.2.1
    exact {
      zalloc := c.zalloc
      zfree := c.zfree
      strm := c.strm
      alloc_bufs := c.alloc_bufs
      al_state := c.al_state
      al_zfree := c.al_zfree
      al_buf := c.al_buf
      status_lo := c.status_lo
      status_hi := c.status_hi
      wrap := c.wrap
      gzhead := c.gzhead
      w_size := c.w_size
      pbuf := c.pbuf
      head := ⟨ho, d', by simp [SH], hh, by rw [hsz]; omega⟩
      level := c.level
      trees := ⟨tl, td, tb⟩
      sizes := c.sizes
      lay := ⟨d', wo, po, ho, pbo, by simp [SH], hw, hp, hh, hpb, l1, l2, l3, by rw [hsz]; exact l4, hsb, pbo,
        by simp only [dview]; rw [hpo0, hpb], Nat.le_refl _, by simp only [dview]; omega⟩
      pout := fun _ => by simp only [dview]; exact hpo0
      syms := ⟨UInt32.le_iff_toNat_le.mpr (Nat.zero_le _), rfl⟩
      bits := ⟨Int32.le_refl _, show (0 : Int32) < 8 by decide⟩
      look := c.look
      strategy := c.strategy
      fns := c.fns
      symv := ⟨d', pbo + st.lit_bufsize.toNat + 8, by simp [SH], hsb, hsym⟩
      psym := fun hn => absurd rfl hn
      hdr := fun _ _ => rfl
      bstart := c.bstart
      ins := c.ins
      wpow := c.wpow
      fe_mod := c.fe_mod
      fe_hi := c.fe_hi
      bs_lo := c.bs_lo
      lmod := c.lmod
      lpow := c.lpow
      scratch := c.scratch
      blk := ⟨rfl, rfl, fun c hc => by
        show (st'.bl_tree[c]!).fc = 0
        have := hI.2.2.2.2.2 c hc
        exact UInt16.toNat_inj.mp (by rw [this]; rfl)⟩
      descs := c.descs }
  · obtain rfl := TreesEmitP.pend_inj hpb hpb2
    exact ⟨d, d', hd, SH_bytes _ _ _ _ _ _, hsz, fun j hj => w.2 j (by omega)⟩
  · refine ⟨?_, ?_⟩
    · rintro st'' ⟨i2, z2, e2, hz2, hb2, hst2⟩
      obtain rfl := Option.some.inj e2
      rw [SH_dstate] at hst2; obtain rfl := Option.some.inj hst2
      exact ⟨k, by rw [hpre.1]; simp; omega, by rw [hsn]; exact UInt32.le_iff_toNat_le.mpr (Nat.zero_le _)⟩
    · intro i2 z2 e2 hz2
      obtain rfl := Option.some.inj e2
      rw [hz] at hz2; obtain rfl := Option.some.inj hz2
      exact ⟨dt, st', d', rfl⟩

/-- **`flush_block_clears`** of `TreesFacts`, from `BuildTreeSpec`. -/
theorem flush_block_clears_ok (hbt : BuildTreeSpec) (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32)
    (last : Int32) (h0 : 0 ≤ last) (h1 : last ≤ 1) :
    EmitClears s b (FlushBlockPre b buf len) (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last) := by
  intro h h'' st hw hs hpre er st'' hs''
  obtain ⟨i, z, d, pbo, al, rfl, hz, hb, hst, hd, hal, c, hpb0, h', e, q⟩ := flush_run hbt h0 h1 hw hs hpre
  rw [e] at er
  obtain rfl : h' = h'' := (Prod.mk.inj (Except.ok.inj er)).2
  obtain ⟨dt, st', d', rfl, w, R, hsn, -⟩ := q
  obtain ⟨i2, z2, e2, hz2, hb2, hst2⟩ := hs''
  obtain rfl := Option.some.inj e2
  rw [SH_dstate] at hst2; obtain rfl := Option.some.inj hst2
  exact hsn

/-- **`TreesFacts`** from the statement of `build_tree`. -/
theorem treesFacts_of (hbt : BuildTreeSpec) : TreesFacts :=
  treesFacts_of_flush (flush_block_ok hbt) (flush_block_clears_ok hbt)


end

end ZlibNgF.Proof.TreesFactsP
