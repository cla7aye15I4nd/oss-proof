import ZlibNgF.Proof.«deflate.c.fill_window.safety»

/-!
# The window facts of `deflate` (`ZlibNgF`)

`windowFacts : WindowFacts`: `fill_window` and the `insert_batch` functions on an invariant stream, lifted from the
`SH`-level lemmas `fill_window_SH` and `call_insert_batch_SH`. The window clauses `WCore` and the layout `HLay` are
read off the invariant (`wcore_of`, `hlay_of`); the invariant after (`dcore_fw`) holds because only the fields of
`fill_window` change (`FWS`), the window clauses hold after, and the bytes of the block change below the end of
`head` only, so the symbols in `sym_buf` stay.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FillFacts
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNgF.Proof.InsertSafe ZlibNgF.Proof.WinInv ZlibNgF.Proof.FillSlide ZlibNgF.Proof.ReadBuf
open ZlibNgF.Proof.FillWindow ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.InflateSync (Sat)
open ZlibNgF.Proof.DeflateBits (WrIn)

section
variable {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}

/-- The window clauses of an invariant state. -/
theorem wcore_of (c : DCore h s z b (dview st) al) : WCore st :=
  ⟨c.wpow, c.fe_mod, c.fe_hi, UInt32.le_iff_toNat_le.mp c.ins, c.bstart, c.bs_lo⟩

/-- The hash-table layout of an invariant state, with the window before `prev`. -/
theorem hlay_of {d : Array UInt8} (c : DCore h s z b (dview st) al) (hd : h.bytes b = some d) :
    ∃ wo po ho pbo, HLay b d.size st wo po ho ∧ wo + st.window_size.toNat ≤ po ∧
      st.pending_buf = .val (.ref (.heap b) pbo) ∧ ho + 131072 ≤ pbo ∧
      st.sym_buf = .val (.ref (.heap b) (pbo + st.lit_bufsize.toNat + 8)) := by
  obtain ⟨w1, -, -, -, -, -, -⟩ := c.sizes
  obtain ⟨d0, wo, po, ho, pbo, hd0, hw, hp, hh, hpb, h1, h2, h3, h4, hsb, -⟩ := c.lay
  simp only [dview] at w1 hw hp hh hpb h1 h2 h3 h4 hsb
  obtain rfl : d = d0 := Option.some.inj (hd.symm.trans hd0)
  exact ⟨wo, po, ho, pbo, ⟨hw, hp, hh, by omega, by omega, by omega, h2⟩, h1, hpb, h3, hsb⟩

end

/-- The invariant's clauses after a change of `fill_window`'s fields (`FWS`) with the window clauses, the data
within the window, the same allocator in the stream record, and the block's bytes changed below the end of `head`
only. -/
theorem dcore_fw {h H : Heap} {i : Nat} {z z' : ZStream} {b : Nat} {st st' : DeflateState} {al : DeflateAllocs}
    {d d' : Array UInt8} (c : DCore h (some i) z b (dview st) al) (hd : h.bytes b = some d)
    (hza : z'.zalloc = z.zalloc) (hzf : z'.zfree = z.zfree) (F : FWS st st') (C : WCore st')
    (lk : st'.strstart.toNat + st'.lookahead.toNat ≤ st'.window_size.toNat)
    (hw : ∀ ho, st.head = .val (.ref (.heap b) ho) → WrIn d 0 (ho + 131072) d') :
    DCore (SH H i z' b st' d') (some i) z' b (dview st') al := by
  obtain ⟨fe, ms, pl, ss, bs, ins, sl, la, ih, hwv, rfl⟩ := F
  obtain ⟨ho, d0, hd0, hh, hho⟩ := c.head
  obtain rfl : d = d0 := Option.some.inj (hd.symm.trans hd0)
  have W := hw ho hh
  obtain ⟨d1, wo, po, ho1, pbo, hd1, hwo, hp, hh1, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  obtain rfl : d = d1 := Option.some.inj (hd.symm.trans hd1)
  simp only [dview] at hh hh1 hsb hpb hwo hp h1 h2 h3 h4 hpo hpoo hpe
  rw [hh] at hh1
  obtain rfl : ho = ho1 := by injection hh1 with e; injection e
  obtain ⟨d2, sbo, hd2, hsb2, hsym⟩ := c.symv
  obtain rfl : d = d2 := Option.some.inj (hd.symm.trans hd2)
  simp only [dview] at hsb2 hsym
  rw [hsb] at hsb2
  obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hsb2 with e; injection e
  have hW := W.1
  exact {
    zalloc := by rw [hza]; exact c.zalloc
    zfree := by rw [hzf]; exact c.zfree
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
    head := ⟨ho, d', SH_bytes _ _ _ _ _ _, hh, by rw [hW]; exact hho⟩
    level := c.level
    trees := c.trees
    sizes := c.sizes
    lay := ⟨d', wo, po, ho, pbo, SH_bytes _ _ _ _ _ _, hwo, hp, hh, hpb, h1, h2, h3, by rw [hW]; exact h4, hsb,
      poo, hpo, hpoo, hpe⟩
    pout := c.pout
    syms := c.syms
    bits := c.bits
    look := lk
    strategy := c.strategy
    fns := c.fns
    symv := ⟨d', pbo + st.lit_bufsize.toNat + 8, SH_bytes _ _ _ _ _ _, hsb, fun j hj => by
      rw [W.2 _ (Or.inr (by omega)), W.2 _ (Or.inr (by omega))]; exact hsym j hj⟩
    psym := c.psym
    hdr := c.hdr
    bstart := C.bs_hi
    ins := UInt32.le_iff_toNat_le.mpr C.ins
    wpow := C.wpow
    fe_mod := C.fe_mod
    fe_hi := C.fe_hi
    bs_lo := C.bs_lo }

/-- The input of `DInput` as `fill_window_SH` takes it: empty, or outside the block. -/
theorem insrc_of {h : Heap} {b : Nat} {z : ZStream} (hr : NullOrRead h z.next_in z.avail_in.toNat)
    (hnb : NotInBlock b z.next_in) (hnn : z.avail_in ≠ 0 → z.next_in ≠ .null) : z.avail_in = 0 ∨ InSrc h b z := by
  rcases hr with hn | ⟨r, off, data, hp, hg, hle⟩
  · exact Or.inl (Classical.byContradiction fun h0 => hnn h0 hn)
  · refine Or.inr ⟨r, off, data, hp, fun e => hnb off (by rw [hp, e]), hg, hle⟩

/-- `fill_window` on an invariant stream (`WindowFacts.fill_window`). -/
theorem fill_window_ok (h : Heap) (s : StreamPtr) (b : Nat) (st : DeflateState) (hv : DInv h s)
    (hs : DStateIs h s b st) (hin : DInput h s) (hc : st.wrap = 2 → CrcGlobals h) (hla : st.lookahead.toNat < 262) :
    ∃ h', C.run (ZlibNg.Deflate.fill_window (some b)) h = .ok ((), h') ∧ FillPost h h' s := by
  obtain ⟨i, z, b0, st0, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨i1, z1, e1, hz1, hb1, hst1⟩ := hs
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (L.hz.symm.trans hz1)
  obtain rfl : b = b0 := Option.some.inj (hb1.symm.trans L.hb)
  obtain rfl : st = st0 := Option.some.inj (hst1.symm.trans L.dstate)
  obtain ⟨z2, b2, ⟨i2, e2, hz2⟩, hb2, hnr, hnb, hnn⟩ := hin
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (L.hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (L.hb.symm.trans hb2)
  obtain ⟨d, hd⟩ := L.hd
  obtain ⟨wo, po, ho, pbo, HL, hwo, -, -, -⟩ := hlay_of c hd
  obtain ⟨-, w2, wsz, -, -, -, -⟩ := c.sizes
  obtain ⟨f, hf⟩ := c.fns.2
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  have S := fill_window_SH (H := h) (i := i) (z := z) (b := b) (d := d) f L.hb c.strm hf HL wsz hwo w2 (wcore_of c)
    c.look hla (insrc_of hnr hnb hnn) (fun e => (hc e).1)
  rw [ZlibNgF.Proof.DeflateReset.SH_self L.hz L.hst hd] at S
  obtain ⟨_, h', e, z', st', d', rfl, W, zr, inz, F, C, lk, hend, sum⟩ := S
  have hst := ZR.state zr
  obtain ⟨hle, ni, ai, ti, ad, rfl⟩ := zr
  refine ⟨_, e, ⟨i, _, b, st', al, rfl, SH_streams _ _ _ _ _ _, hst.trans L.hb, SH_dstate _ _ _ _ _ _,
    by simp [Heap.dallocsOf, SH, hda], dcore_fw c hd rfl rfl F C lk (fun ho' hh' => ?_)⟩, ?_, ?_, ?_⟩
  · rw [HL.head] at hh'
    obtain rfl : ho = ho' := by injection hh' with e; injection e
    exact W
  · refine ⟨_, b, ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, hst.trans L.hb, ?_, ?_, ?_⟩
    · rcases inz with ⟨e0, h0⟩ | ⟨r, os, src, hp, hr, hg, hle'⟩
      · rw [e0]
        rcases hnr with hn | ⟨r, off, data, hp, hg, hle'⟩
        · exact Or.inl hn
        · have hr : r ≠ .heap b := fun e => hnb off (by rw [hp, e])
          exact Or.inr ⟨r, off, data, hp, by rw [get_SH_ne hr]; exact hg, hle'⟩
      · exact Or.inr ⟨r, os, src, hp, by rw [get_SH_ne hr]; exact hg, hle'⟩
    · rcases inz with ⟨e0, -⟩ | ⟨r, os, src, hp, hr, -, -⟩
      · rw [e0]; exact hnb
      · intro off e; rw [hp] at e; injection e with e1; exact hr e1
    · rcases inz with ⟨e0, -⟩ | ⟨r, os, src, hp, -, -, -⟩
      · rw [e0]; exact hnn
      · intro _; rw [hp]; exact fun e => by cases e
  · have : stateIds h (some i) = [b] := by simp [stateIds, L.hz, L.hb]
    rw [this]
    exact ZlibNgF.Proof.DeflateReset.dframe_SH h i _ b st' d'
  · obtain ⟨fe, ms, pl, ss, bs, ins, sl, la, ih, hw', rfl⟩ := F
    refine ⟨i, z, _, b, st, _, rfl, L.hz, SH_streams _ _ _ _ _ _, L.hb, L.dstate, SH_dstate _ _ _ _ _ _, rfl, hle,
      fun hne => ?_, hend, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hne' : la ≠ st.lookahead := hne
    have sum' : ai.toNat + la.toNat = z.avail_in.toNat + st.lookahead.toNat := sum
    have : ¬ la.toNat = st.lookahead.toNat := fun e' => hne' (UInt32.toNat_inj.mp e')
    have hle' : ai.toNat ≤ z.avail_in.toNat := hle
    show ai.toNat < z.avail_in.toNat
    omega

/-- `insert_batch` through the function pointer on an invariant stream (`WindowFacts.insert_batch`). -/
theorem insert_batch_ok (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8)
    (f : InsertBatchFn) (wo : Nat) (str n : UInt32) (hv : DInv h (some i)) (hz : h.streams i = some z)
    (hb : z.state = some b) (hst : h.dstate b = some st) (hd : h.bytes b = some d)
    (hw : st.window = .val (.ref (.heap b) wo)) (_hn : 1 ≤ n.toNat)
    (hr : str.toNat + n.toNat + 2 ≤ st.strstart.toNat + st.lookahead.toNat) :
    ∃ st' d', C.run (ZlibNg.InsertString.call_insert_batch f (some b) (.ref (.heap b) wo) str n) h =
        .ok ((), SH h i z b st' d') ∧
      DInv (SH h i z b st' d') (some i) ∧ st' = { st with ins_h := st'.ins_h } ∧ d'.size = d.size := by
  obtain ⟨i0, z0, b0, st0, al, e0, L, hal, c⟩ := live hv
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans L.hz)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans L.hb)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans L.dstate)
  obtain ⟨wo1, po, ho, pbo, HL, hwo, -, hpb, -⟩ := hlay_of c hd
  rw [HL.win] at hw
  obtain rfl : wo1 = wo := by injection hw with e; injection e
  have hlk := c.look
  have hph := HL.ph
  have hhd := HL.hd
  simp only [dview] at hlk
  have S := call_insert_batch_SH (H := h) (i := i) (z := z) (d := d) HL f str n (by omega)
  rw [ZlibNgF.Proof.DeflateReset.SH_self L.hz L.hst hd] at S
  obtain ⟨_, h', e, d', x, rfl, W⟩ := S
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  refine ⟨_, d', e, ⟨i, z, b, _, al, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _,
    by simp [Heap.dallocsOf, SH, hda], dcore_fw c hd rfl rfl ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ ?_ hlk
      (fun ho' hh' => ?_)⟩, rfl, W.1⟩
  · have C := wcore_of c
    exact ⟨C.wpow, C.fe_mod, C.fe_hi, C.ins, C.bs_hi, C.bs_lo⟩
  · rw [HL.head] at hh'
    obtain rfl : ho = ho' := by injection hh' with e; injection e
    exact W

/-- The window facts. -/
theorem windowFacts : WindowFacts := ⟨fill_window_ok, insert_batch_ok⟩

end ZlibNgF.Proof.FillFacts
