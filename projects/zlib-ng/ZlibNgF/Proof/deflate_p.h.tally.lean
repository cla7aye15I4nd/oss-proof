import ZlibNgF.Proof.«deflate.c.fill_window.facts»

/-!
# `zng_tr_tally_lit` / `zng_tr_tally_dist` (`ZlibNgF`)

Runs on `SH` heaps. A tally stores the symbol with one 4-byte `zng_memwrite_4` at `sym_buf + sym_next` (`W4`; the
fourth byte is overwritten by the next symbol), adds 3 to `sym_next`, and increments one frequency of `dyn_ltree`
(the literal, or `zng_length_code[len] + LITERALS + 1`) and, for a match, one of `dyn_dtree` (`d_code(dist - 1)`).
The table indices are in range for `len <= 255` and `1 <= dist <= 32768` (`length_code_lt`, `d_code_lt`). The first
two bytes of the stored symbol are the distance (`lit_bytes`, `dist_bytes`), which the invariant's `symv` clause
reads.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Tally
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateBits (WrIn st1 st1e wr_seq)
open ZlibNg.DeflateP

/-- The bytes `d` after `zng_memwrite_4(d + off, v)`. -/
def W4 (d : Array UInt8) (off : Nat) (v : UInt32) : Array UInt8 :=
  (((d.set! off v.toUInt8).set! (off + 1) (v >>> 8).toUInt8).set! (off + 2) (v >>> 16).toUInt8).set! (off + 3)
    (v >>> 24).toUInt8

theorem W4_wr (d : Array UInt8) (off : Nat) (v : UInt32) : WrIn d off (off + 4) (W4 d off v) :=
  wr_seq 3 _ (by omega) (wr_seq 2 _ (by omega) (wr_seq 1 _ (by omega) (wr_seq 0 _ (by omega) (WrIn.refl _ _ _))))

theorem get_set_ne (a : Array UInt8) (j k : Nat) (v : UInt8) (h : j ≠ k) : (a.set! j v)[k]! = a[k]! := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [h]

theorem get_set_eq (a : Array UInt8) (j : Nat) (v : UInt8) (h : j < a.size) : (a.set! j v)[j]! = v := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [h]

theorem W4_get0 (d : Array UInt8) (off : Nat) (v : UInt32) (h : off + 4 ≤ d.size) :
    (W4 d off v)[off]! = v.toUInt8 := by
  unfold W4
  rw [get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega),
    get_set_eq _ _ _ (by omega)]

theorem W4_get1 (d : Array UInt8) (off : Nat) (v : UInt32) (h : off + 4 ≤ d.size) :
    (W4 d off v)[off + 1]! = (v >>> 8).toUInt8 := by
  unfold W4
  rw [get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega), get_set_eq _ _ _ (by simp; omega)]

/-- The distance bytes of a match symbol `dist | (len << 16)`. -/
theorem dist_bytes (dist len : UInt32) (h : dist.toNat < 65536) :
    (dist ||| (len <<< 16)).toUInt8.toNat + 256 * ((dist ||| (len <<< 16)) >>> 8).toUInt8.toNat = dist.toNat := by
  have e : (dist ||| (len <<< 16)).toNat % 65536 = dist.toNat := by
    rw [UInt32.toNat_or, show (65536 : Nat) = 2 ^ 16 from rfl, Nat.or_mod_two_pow, UInt32.toNat_shiftLeft]
    have : len.toNat <<< ((16 : UInt32).toNat % 32) % 2 ^ 32 % 2 ^ 16 = 0 := by
      rw [Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide)]
      exact Nat.mul_mod_left _ _
    rw [this, Nat.or_zero]; exact Nat.mod_eq_of_lt h
  generalize dist ||| (len <<< 16) = v at e
  rw [UInt32.toNat_toUInt8, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  simp only [Nat.shiftRight_eq_div_pow]
  have : (8 : UInt32).toNat % 32 = 8 := rfl
  rw [this]
  omega

/-- The distance bytes of a literal symbol `c << 16` are zero. -/
theorem lit_bytes (c : UInt8) :
    (c.toUInt32 <<< 16).toUInt8.toNat + 256 * ((c.toUInt32 <<< 16) >>> 8).toUInt8.toNat = 0 := by
  have := dist_bytes 0 c.toUInt32 (by decide)
  rwa [UInt32.zero_or] at this

set_option maxRecDepth 100000 in
theorem length_code_all : ∀ k (h : k < zng_length_code.size), (zng_length_code[k]'h).toNat < 29 := by
  decide

set_option maxRecDepth 100000 in
theorem dist_code_all : ∀ k (h : k < zng_dist_code.size), (zng_dist_code[k]'h).toNat < 30 := by
  decide

set_option maxRecDepth 100000 in
theorem length_code_lt (k : Nat) (hk : k < 256) :
    ∃ h : k < zng_length_code.size, (zng_length_code[k]'h).toNat < 29 := by
  have e : zng_length_code.size = 256 := rfl
  exact ⟨by omega, length_code_all k _⟩

set_option maxRecDepth 100000 in
theorem dist_code_lt (k : Nat) (hk : k < 512) :
    ∃ h : k < zng_dist_code.size, (zng_dist_code[k]'h).toNat < 30 := by
  have e : zng_dist_code.size = 512 := rfl
  exact ⟨by omega, dist_code_all k _⟩

theorem d_code_lt (dist : UInt32) (hd : dist.toNat < 32768) :
    ∃ v, d_code dist = (pure v : M UInt8) ∧ v.toNat < 30 := by
  unfold d_code
  split
  · rename_i h
    have h' : dist.toNat < 256 := by simpa [UInt32.lt_iff_toNat_lt] using h
    obtain ⟨hs, hv⟩ := dist_code_lt dist.toNat (by omega)
    exact ⟨_, by simp only [tblGet, hs, ↓reduceDIte], hv⟩
  · have e : (dist >>> 7).toNat = dist.toNat / 128 := by
      rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
    obtain ⟨hs, hv⟩ := dist_code_lt (256 + (dist >>> 7).toNat) (by omega)
    exact ⟨_, by simp only [tblGet, hs, ↓reduceDIte], hv⟩

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem memwrite4_W4 {off : Nat} (v : UInt32) (h : off + 4 ≤ d.size) :
    Sat (SH H i z b st d) (memwrite4 (.ref (.heap b) off) v) (fun _ H' => H' = SH H i z b st (W4 d off v)) := by
  unfold memwrite4
  refine st1 0 (by decide) _ (by simp; omega) ?_
  refine st1 1 (by decide) _ (by simp; omega) ?_
  refine st1 2 (by decide) _ (by simp; omega) ?_
  exact st1e 3 (by decide) _ (by simp; omega) rfl

theorem ctFc_l (s : DeflateState) (k : Nat) (hk : k < s.dyn_ltree.size) :
    ctFc (.ref (CtRef.dyn_ltree b) 0) (k : Int) (SH H i z b s d) = .ok ((s.dyn_ltree[k]'hk).fc, SH H i z b s d) := by
  have e1 : Ptr.add (Ptr.ref (CtRef.dyn_ltree b) 0) (k : Int) (SH H i z b s d) =
      .ok (Ptr.ref (CtRef.dyn_ltree b) k, SH H i z b s d) := by
    simp only [Ptr.add, ctl_get]
    rw [ZlibNgF.Proof.DeflateAlloc.ite_t (by omega)]
    congr 3; omega
  simp only [ctFc, ctGet, Ptr.index, bind_app, e1, Ptr.load, ctl_get, hk, ↓reduceDIte]
  rfl

theorem ctFc_d (s : DeflateState) (k : Nat) (hk : k < s.dyn_dtree.size) :
    ctFc (.ref (CtRef.dyn_dtree b) 0) (k : Int) (SH H i z b s d) = .ok ((s.dyn_dtree[k]'hk).fc, SH H i z b s d) := by
  have e1 : Ptr.add (Ptr.ref (CtRef.dyn_dtree b) 0) (k : Int) (SH H i z b s d) =
      .ok (Ptr.ref (CtRef.dyn_dtree b) k, SH H i z b s d) := by
    simp only [Ptr.add, ctd_get]
    rw [ZlibNgF.Proof.DeflateAlloc.ite_t (by omega)]
    congr 3; omega
  simp only [ctFc, ctGet, Ptr.index, bind_app, e1, Ptr.load, ctd_get, hk, ↓reduceDIte]
  rfl

theorem ctSetFc_d (s : DeflateState) (k : Nat) (v : UInt16) (hk : k < s.dyn_dtree.size) :
    ctSetFc (.ref (CtRef.dyn_dtree b) 0) (k : Int) v (SH H i z b s d) =
      .ok ((), SH H i z b { s with dyn_dtree := s.dyn_dtree.set! k { (s.dyn_dtree[k]'hk) with fc := v } } d) := by
  have e1 : Ptr.add (Ptr.ref (CtRef.dyn_dtree b) 0) (k : Int) (SH H i z b s d) =
      .ok (Ptr.ref (CtRef.dyn_dtree b) k, SH H i z b s d) := by
    simp only [Ptr.add, ctd_get]
    rw [ZlibNgF.Proof.DeflateAlloc.ite_t (by omega)]
    congr 3; omega
  simp only [ctSetFc, ctGet, ctSet, Ptr.index, bind_app, e1, Ptr.load, ctd_get, hk, ↓reduceDIte,
    Ptr.store, ↓reduceIte, ctd_mod]
  rfl

/-- `zng_tr_tally_lit(s, c)`: the symbol at `sym_buf + sym_next`, `sym_next + 3`, one frequency of `dyn_ltree`
incremented; the result is `sym_next + 3 == sym_end`. -/
theorem tally_lit_SH (c : UInt8) {sbo : Nat} (hsb : st.sym_buf = .val (.ref (.heap b) sbo))
    (hk : sbo + st.sym_next.toNat + 4 ≤ d.size) (hl : st.dyn_ltree.size = HEAP_SIZE) :
    Sat (SH H i z b st d) (zng_tr_tally_lit (some b) c) (fun r H' => ∃ s' : DeflateState,
      H' = SH H i z b s' (W4 d (sbo + st.sym_next.toNat) (c.toUInt32 <<< 16)) ∧
      s' = { st with sym_next := st.sym_next + 3, dyn_ltree := s'.dyn_ltree } ∧
      s'.dyn_ltree.size = st.dyn_ltree.size ∧ r = (st.sym_next + 3 == st.sym_end)) := by
  unfold zng_tr_tally_lit
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have eg : st.sym_buf.get = (pure (.ref (.heap b) sbo) : M BPtr) := by rw [hsb]; rfl
  rw [eg]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (addN_SH _ (by omega)) ?_)
  refine Sat.bind (Sat.mono (memwrite4_W4 _ hk) ?_)
  rintro _ _ rfl
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.pure ?_)
  have hc : c.toNat < ({ st with sym_next := st.sym_next + 3 } : DeflateState).dyn_ltree.size := by
    show c.toNat < st.dyn_ltree.size
    rw [hl]; have := c.toNat_lt; simp [HEAP_SIZE, L_CODES]; omega
  refine Sat.bind (Sat.of_eq (ctFc_l _ _ hc) ?_)
  refine Sat.bind (Sat.of_eq (ctSetFc_l _ _ _ hc) ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  exact Sat.pure ⟨_, rfl, rfl, by simp, rfl⟩

/-- `zng_tr_tally_dist(s, dist, len)` with `len <= 255` and `1 <= dist <= 32768`. -/
theorem tally_dist_SH (dist len : UInt32) (hlen : len.toNat < 256) (hd1 : 1 ≤ dist.toNat)
    (hd2 : dist.toNat ≤ 32768) {sbo : Nat} (hsb : st.sym_buf = .val (.ref (.heap b) sbo))
    (hk : sbo + st.sym_next.toNat + 4 ≤ d.size) (hl : st.dyn_ltree.size = HEAP_SIZE)
    (hdt : st.dyn_dtree.size = 2 * 30 + 1) :
    Sat (SH H i z b st d) (zng_tr_tally_dist (some b) dist len) (fun r H' => ∃ s' : DeflateState,
      H' = SH H i z b s' (W4 d (sbo + st.sym_next.toNat) (dist ||| (len <<< 16))) ∧
      s' = { st with sym_next := st.sym_next + 3, dyn_ltree := s'.dyn_ltree, dyn_dtree := s'.dyn_dtree } ∧
      s'.dyn_ltree.size = st.dyn_ltree.size ∧ s'.dyn_dtree.size = st.dyn_dtree.size ∧
      r = (st.sym_next + 3 == st.sym_end)) := by
  unfold zng_tr_tally_dist
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have eg : st.sym_buf.get = (pure (.ref (.heap b) sbo) : M BPtr) := by rw [hsb]; rfl
  rw [eg]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (addN_SH _ (by omega)) ?_)
  refine Sat.bind (Sat.mono (memwrite4_W4 _ hk) ?_)
  rintro _ _ rfl
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.pure ?_)
  obtain ⟨hs, hv⟩ := length_code_lt len.toNat hlen
  have et : tblGet zng_length_code len.toNat = (pure (zng_length_code[len.toNat]'hs) : M UInt8) := by
    simp [tblGet, hs]
  rw [et]
  refine Sat.bind (Sat.pure ?_)
  have hc : (zng_length_code[len.toNat]'hs).toNat + LITERALS + 1 <
      ({ st with sym_next := st.sym_next + 3 } : DeflateState).dyn_ltree.size := by
    show _ < st.dyn_ltree.size
    rw [hl]; simp [HEAP_SIZE, L_CODES, LITERALS]; omega
  refine Sat.bind (Sat.of_eq (ctFc_l _ _ hc) ?_)
  refine Sat.bind (Sat.of_eq (ctSetFc_l _ _ _ hc) ?_)
  refine Sat.bind (Sat.pure ?_)
  have hdm : (dist - 1).toNat < 32768 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hd1)]; simp; omega
  obtain ⟨v, ev, hv30⟩ := d_code_lt (dist - 1) hdm
  rw [ev]
  refine Sat.bind (Sat.pure ?_)
  have hj : v.toNat < ({ { st with sym_next := st.sym_next + 3 } with
      dyn_ltree := ({ st with sym_next := st.sym_next + 3 } : DeflateState).dyn_ltree.set!
        ((zng_length_code[len.toNat]'hs).toNat + LITERALS + 1)
        { (({ st with sym_next := st.sym_next + 3 } : DeflateState).dyn_ltree[
          (zng_length_code[len.toNat]'hs).toNat + LITERALS + 1]'hc) with
          fc := (({ st with sym_next := st.sym_next + 3 } : DeflateState).dyn_ltree[
            (zng_length_code[len.toNat]'hs).toNat + LITERALS + 1]'hc).fc + 1 } } : DeflateState).dyn_dtree.size := by
    show _ < st.dyn_dtree.size
    rw [hdt]; omega
  refine Sat.bind (Sat.of_eq (ctFc_d _ _ hj) ?_)
  refine Sat.bind (Sat.of_eq (ctSetFc_d _ _ _ hj) ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  exact Sat.pure ⟨_, rfl, rfl, by simp, by simp, rfl⟩

end

open ZlibNgF.Proof.DeflateInv in
/-- The invariant's clauses after a tally: the view changes in `sym_next` only (`+ 3`, from below `sym_end`), the
symbol's distance bytes are at most 32768, the pending bytes end before `sym_buf`, and the stream is past its header
(`BUSY_STATE` or `FINISH_STATE`). -/
theorem dcore_tally {h H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState} {al : DeflateAllocs}
    {d : Array UInt8} {sbo : Nat} (v : UInt32) (c : DCore h (some i) z b (dview st) al) (hd : h.bytes b = some d)
    (hsb : st.sym_buf = .val (.ref (.heap b) sbo))
    (hv : dview st' = { dview st with sym_next := st.sym_next + 3 }) (hlt : st.sym_next < st.sym_end)
    (hval : (v.toUInt8.toNat + 256 * (v >>> 8).toUInt8.toNat) ≤ 32768)
    (hroom : ∃ pbo poo, st.pending_buf = .val (.ref (.heap b) pbo) ∧ st.pending_out = .val (.ref (.heap b) poo) ∧
      poo - pbo + st.pending.toNat ≤ st.lit_bufsize.toNat + 8)
    (hstat : st.status = ZlibNg.Deflate.BUSY_STATE ∨ st.status = ZlibNg.Deflate.FINISH_STATE) :
    DCore (SH H i z b st' (W4 d (sbo + st.sym_next.toNat) v)) (some i) z b (dview st') al := by
  rw [hv]
  obtain ⟨d1, wo, po, ho, pbo, hd1, hwo, hp, hh, hpb, h1, h2, h3, h4, hsb1, poo, hpo, hpoo, hpe⟩ := c.lay
  obtain rfl : d = d1 := Option.some.inj (hd.symm.trans hd1)
  simp only [dview] at hsb1 hpb h4
  rw [hsb] at hsb1
  obtain rfl : sbo = pbo + st.lit_bufsize.toNat + 8 := by injection hsb1 with e; injection e
  obtain ⟨hsn, hsm⟩ := c.syms
  simp only [dview] at hsn hsm
  obtain ⟨-, -, -, -, hl2, -, hse⟩ := c.sizes
  simp only [dview] at hse hl2
  have hlt' : st.sym_next.toNat < st.sym_end.toNat := UInt32.lt_iff_toNat_lt.mp hlt
  have hsn3 : (st.sym_next + 3).toNat = st.sym_next.toNat + 3 := by rw [UInt32.toNat_add]; simp; omega
  have hk : pbo + st.lit_bufsize.toNat + 8 + st.sym_next.toNat + 4 ≤ d.size := by omega
  have hW := W4_wr d (pbo + st.lit_bufsize.toNat + 8 + st.sym_next.toNat) v
  have hWs : (W4 d (pbo + st.lit_bufsize.toNat + 8 + st.sym_next.toNat) v).size = d.size := hW.1
  obtain ⟨d2, sbo2, hd2, hsb2, hsym⟩ := c.symv
  obtain rfl : d = d2 := Option.some.inj (hd.symm.trans hd2)
  simp only [dview] at hsb2 hsym
  rw [hsb] at hsb2
  obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo2 := by injection hsb2 with e; injection e
  obtain ⟨ho', d3, hd3, hh', hho'⟩ := c.head
  obtain rfl : d = d3 := Option.some.inj (hd.symm.trans hd3)
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
    head := ⟨ho', _, SH_bytes _ _ _ _ _ _, hh', by rw [hWs]; exact hho'⟩
    level := c.level
    trees := c.trees
    sizes := c.sizes
    lay := ⟨_, wo, po, ho, pbo, SH_bytes _ _ _ _ _ _, hwo, hp, hh, hpb, h1, h2, h3, by rw [hWs]; exact h4,
      by simp only [dview]; rw [hsb], poo, hpo, hpoo, hpe⟩
    pout := c.pout
    syms := ⟨UInt32.le_iff_toNat_le.mpr (show (st.sym_next + 3).toNat ≤ st.sym_end.toNat by rw [hsn3]; omega),
      show (st.sym_next + 3).toNat % 3 = 0 by rw [hsn3]; omega⟩
    bits := c.bits
    look := c.look
    strategy := c.strategy
    fns := c.fns
    symv := ⟨_, pbo + st.lit_bufsize.toNat + 8, SH_bytes _ _ _ _ _ _, by simp only [dview]; rw [hsb], fun j hj => by
      simp only [] at hj
      rw [hsn3] at hj
      by_cases hj' : 3 * j < st.sym_next.toNat
      · rw [hW.2 _ (Or.inl (by omega)), hW.2 _ (Or.inl (by omega))]; exact hsym j hj'
      · have e : 3 * j = st.sym_next.toNat := by omega
        rw [show pbo + st.lit_bufsize.toNat + 8 + 3 * j = pbo + st.lit_bufsize.toNat + 8 + st.sym_next.toNat by
          omega, W4_get0 _ _ _ hk, W4_get1 _ _ _ hk]
        exact hval⟩
    psym := fun _ => hroom
    hdr := fun h1 h2 => by
      rcases hstat with e | e
      · exact absurd e h1
      · exact absurd e h2
    bstart := c.bstart
    ins := c.ins
    wpow := c.wpow
    fe_mod := c.fe_mod
    fe_hi := c.fe_hi
    bs_lo := c.bs_lo }

open ZlibNgF.Proof.DeflateInv in
/-- `block_start = strstart` (the store of `FLUSH_BLOCK_ONLY` after `zng_tr_flush_block`) keeps the invariant's
clauses. -/
theorem dcore_bs {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs} (x : Int32)
    (c : DCore h s z b v al) (hx : x.toInt = v.strstart.toNat) :
    DCore h s z b { v with block_start := x } al :=
  { c with
    bstart := by simp only []; omega
    bs_lo := by simp only []; omega }

end ZlibNgF.Proof.Tally
