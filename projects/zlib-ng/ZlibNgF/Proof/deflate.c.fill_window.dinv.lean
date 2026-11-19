import ZlibNgF.Proof.«deflate.c.fill_window.safety»

/-!
# `fill_window` on an invariant stream (`ZlibNgF`)

`fill_window_dinv`: on a stream with the structural invariant `DInv` and the window invariant `WInv`, with
`lookahead < MIN_LOOKAHEAD` and input that is empty or lies outside the stream's block, `fill_window` does not fault,
keeps `DInv` and `WInv`, changes only the stream record and the stream's block, and leaves at least
`MIN_LOOKAHEAD` bytes of lookahead or no input.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FillWindowInv
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.InsertSafe ZlibNgF.Proof.WinInv ZlibNgF.Proof.FillWindow
open ZlibNgF.Proof.DeflateReset (SH_self dframe_SH)

/-- `fill_window` on an invariant stream `s` (state block `b`). -/
theorem fill_window_dinv {h : Heap} {s : StreamPtr} (hv : DInv h s) (hw : WInv h s) (hc : CrcGlobals h)
    (hla : ∀ b st, DStateIs h s b st → st.lookahead.toNat < 262)
    (hin : ∀ b z, StateBlock h s b → StreamAt h s z → z.avail_in = 0 ∨ InSrc h b z) :
    ∃ i b, s = some i ∧ StateBlock h s b ∧ ∃ h', C.run (fill_window (some b)) h = .ok ((), h') ∧
      DInv h' s ∧ WInv h' s ∧ DFrame h h' [i] [b] [] [] ∧
      ∀ b' st z, DStateIs h' s b' st → StreamAt h' s z → 262 ≤ st.lookahead.toNat ∨ z.avail_in = 0 := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨b1, st1, ⟨i1, z1, hi1, hz1, hzb1, hst1⟩, C⟩ := hw
  obtain rfl := Option.some.inj hi1
  rw [L.hz] at hz1; obtain rfl := Option.some.inj hz1
  rw [L.hb] at hzb1; obtain rfl := Option.some.inj hzb1
  rw [L.dstate] at hst1; obtain rfl := Option.some.inj hst1
  obtain ⟨w1, w2, wsz, -, -, -, -⟩ := c.sizes
  obtain ⟨d, wo, po, ho, pbo, hd, hwin, hprev, hhead, -, h1, h2, h3, h4, -, -⟩ := c.lay
  simp only [dview] at w1 w2 wsz hwin hprev hhead h1 h2 h3 h4
  have Lh : HLay b d.size st wo po ho := ⟨hwin, hprev, hhead, by omega, by omega, by omega⟩
  obtain ⟨f, hf⟩ := c.fns.2
  have hzb : z.state = some b := L.hb
  have hsb : StateBlock h (some i) b := ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩
  obtain ⟨_, H', e, z', st', d', rfl, hd', zr, hin', F, C', lk, hend⟩ :=
    fill_window_SH (H := h) (d := d) f hzb c.strm hf Lh wsz h1 w2 C c.look (hla b st ⟨i, z, rfl, L.hz, L.hb, L.dstate⟩)
      (hin b z hsb ⟨i, rfl, L.hz⟩) hc.1
  rw [SH_self L.hz L.hst hd] at e
  have hzb' : z'.state = some b := by rw [ZR.state zr]; exact hzb
  obtain ⟨-, ni, ai, ti, ad, rfl⟩ := zr
  obtain ⟨fe, ms, pl, ss, bs, ins, sl, la, ih, hw, rfl⟩ := F
  have hal' : ∀ zz ss dd, (SH h i zz b ss dd).dallocsOf b = some al := fun zz ss dd => by
    simpa [Heap.dallocsOf, SH, hd] using hal
  refine ⟨i, b, rfl, hsb, _, e, ⟨i, _, b, _, al, rfl, SH_streams .., hzb', SH_dstate .., hal' _ _ _, ?_⟩,
    ⟨b, _, ⟨i, _, rfl, SH_streams .., hzb', SH_dstate ..⟩, C'⟩, ?_, ?_⟩
  · obtain ⟨ho', d0, hd0, hho, hho'⟩ := c.head
    rw [hd] at hd0; obtain rfl := Option.some.inj hd0
    obtain ⟨d1, wo1, po1, ho1, pbo1, hd1, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := c.lay
    rw [hd] at hd1; obtain rfl := Option.some.inj hd1
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
      head := ⟨ho', d', SH_bytes .., hho, by omega⟩
      level := c.level
      trees := c.trees
      sizes := c.sizes
      lay := ⟨d', wo1, po1, ho1, pbo1, SH_bytes .., l1, l2, l3, l4, l5, l6, l7, by rw [hd']; exact l8, l9, l10⟩
      pout := c.pout
      syms := c.syms
      bits := c.bits
      look := lk
      strategy := c.strategy
      fns := c.fns }
  · exact dframe_SH h i _ b _ d'
  · rintro b' st0 z0 ⟨i0, z1, hi0, hz0, hzb0, hst0⟩ ⟨i2, hi2, hz2⟩
    obtain rfl := Option.some.inj hi0
    obtain rfl := Option.some.inj hi2
    rw [SH_streams] at hz0 hz2
    obtain rfl := Option.some.inj hz0
    obtain rfl := Option.some.inj hz2
    rw [hzb'] at hzb0; obtain rfl := Option.some.inj hzb0
    rw [SH_dstate] at hst0; obtain rfl := Option.some.inj hst0
    exact hend

end ZlibNgF.Proof.FillWindowInv
