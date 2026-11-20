import ZlibNgF.Proof.«deflate.c.body.run»

/-!
# `deflate`: header segments (`ZlibNgF`)

Between two flushes, the header code of `deflate` changes only the stream's `adler`, the state's `pending`, `status`,
`gzindex`, and the bytes of `pending_buf` after the pending bytes (`Seg`). With no tallied symbols and `pending_out`
at `pending_buf` (as in the header states), such a change keeps the invariant (`dcore_hdr`) and, with the header facts
of the new state, `Run` (`seg_run`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateBits (WrIn)

theorem SH_SH (H : Heap) (i : Nat) (z z' : ZStream) (b : Nat) (st st' : DeflateState) (d d' : Array UInt8) :
    SH (SH H i z b st d) i z' b st' d' = SH H i z' b st' d' := by
  simp [SH, ZlibNgF.Proof.InflateInv.upd_upd]

/-- The invariant's record and block for stream `i` of an `SH` heap. -/
theorem inv_SH {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (hv : DInv (SH H0 i z b st d) (some i)) (hb : z.state = some b) :
    ∃ al, (SH H0 i z b st d).dallocsOf b = some al ∧ DCore (SH H0 i z b st d) (some i) z b (dview st) al := by
  obtain ⟨i', z', b', st', al, e, hz, hb', hst, hal, c⟩ := hv
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : st = st' := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
  exact ⟨al, hal, c⟩

/-- The invariant after a header store: the status, the pending count and the bytes after `pending_buf`'s head
part changed, with no symbols and `pending_out` at `pending_buf`. -/
theorem dcore_hdr {H H' : Heap} {i : Nat} {z z' : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    {d d' : Array UInt8} (c : DCore H (some i) z b v al) (hd : H.bytes b = some d) (hd' : H'.bytes b = some d')
    (hsz : d'.size = d.size) (h0 : v.sym_next = 0) (hpo : v.pending_out = v.pending_buf) (st : Int32) (pd : UInt32)
    (hp : pd.toNat + v.bi_valid.toInt.toNat / 8 ≤ 4 * v.lit_bufsize.toNat + 9) (hs1 : INIT_STATE ≤ st)
    (hs2 : st ≤ MAX_STATE) (hza : z'.zalloc = z.zalloc) (hzf : z'.zfree = z.zfree) :
    DCore H' (some i) z' b { v with status := st, pending := pd } al := by
  obtain ⟨d0, wo, po, ho, pbo, hd0, hw, hpp, hh, hpb, l1, l2, l3, l4, hsb, poo, hpoo, hpo1, hpe⟩ := c.lay
  obtain rfl := Option.some.inj (hd.symm.trans hd0)
  rw [hpo, hpb] at hpoo
  obtain rfl : poo = pbo := by injection hpoo with e; injection e with _ e; exact e.symm
  obtain ⟨ho1, d1, hd1, hh1, hho⟩ := c.head
  obtain rfl := Option.some.inj (hd.symm.trans hd1)
  exact {
    zalloc := hza.trans c.zalloc
    zfree := hzf.trans c.zfree
    strm := c.strm
    alloc_bufs := c.alloc_bufs
    al_state := c.al_state
    al_zfree := c.al_zfree
    al_buf := c.al_buf
    status_lo := hs1
    status_hi := hs2
    wrap := c.wrap
    gzhead := c.gzhead
    w_size := c.w_size
    pbuf := c.pbuf
    head := ⟨ho1, d', hd', hh1, by rw [hsz]; exact hho⟩
    level := c.level
    trees := c.trees
    sizes := c.sizes
    lay := ⟨d', wo, po, ho, poo, hd', hw, hpp, hh, hpb, l1, l2, l3, by rw [hsz]; exact l4, hsb, poo,
      by rw [hpo, hpb], Nat.le_refl _, by simp only []; omega⟩
    pout := fun _ => hpo
    syms := c.syms
    bits := c.bits
    look := c.look
    strategy := c.strategy
    fns := c.fns
    symv := by
      obtain ⟨d2, sbo2, hd2', hsb2', hv⟩ := c.symv
      obtain rfl := Option.some.inj (hd.symm.trans hd2')
      exact ⟨d', sbo2, hd', hsb2', hv.of_eq fun k hk => by rw [h0] at hk; exact absurd hk (Nat.not_lt_zero _)⟩
    psym := fun hn => absurd h0 hn
    hdr := fun _ _ => h0
    bstart := c.bstart
    ins := c.ins
    wpow := c.wpow
    fe_mod := c.fe_mod
    fe_hi := c.fe_hi
    bs_lo := c.bs_lo
    descs := c.descs
    lmod := c.lmod
    lpow := c.lpow
    scratch := c.scratch
    blk := c.blk }

/-- A header segment from `SH H0 i z0 b st0 d0` (no symbols, `pending_out` at `pending_buf`) keeps `Run`, given the
header facts of the new state and a status other than `FINISH_STATE`. -/
theorem seg_run {h H0 : Heap} {i b : Nat} {z0 : ZStream} {st0 : DeflateState} {d0 d : Array UInt8} {pbo : Nat}
    (R : Run h i b (SH H0 i z0 b st0 d0)) (hpb : st0.pending_buf = .val (.ref (.heap b) pbo))
    (h0 : st0.sym_next = 0) (hpo : st0.pending_out = st0.pending_buf) (a : UInt64) (p : UInt32) (s : Int32)
    (g : UInt32) (hsz : d.size = d0.size) (hlo : ∀ j, j < pbo → d[j]! = d0[j]!)
    (hp : p.toNat ≤ 4 * st0.lit_bufsize.toNat) (hs1 : INIT_STATE ≤ s) (hs2 : s ≤ MAX_STATE)
    (hfin : s ≠ FINISH_STATE)
    (hdr : HdrOk (SH H0 i { z0 with adler := a } b { st0 with pending := p, status := s, gzindex := g } d) b
      { st0 with pending := p, status := s, gzindex := g }) :
    Run h i b (SH H0 i { z0 with adler := a } b { st0 with pending := p, status := s, gzindex := g } d) := by
  have hv := R.inv
  obtain ⟨z1, hz1, hb⟩ := R.blk
  obtain rfl : z0 = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain ⟨al, hal, c⟩ := inv_SH hv hb
  have hb8 := c.bits
  simp only [dview] at hb8
  have hb8' : st0.bi_valid.toInt.toNat / 8 ≤ 7 := by
    have a1 : st0.bi_valid.toInt < 64 := Int32.lt_iff_toInt_lt.mp hb8.2
    omega
  have c' := dcore_hdr (H' := SH H0 i { z0 with adler := a } b { st0 with pending := p, status := s, gzindex := g } d)
    (z' := { z0 with adler := a }) c (SH_bytes _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _) hsz h0 hpo s p (by simp only [dview]; omega) hs1 hs2 rfl rfl
  have R' := run_SH (z' := { z0 with adler := a }) (st' := { st0 with pending := p, status := s, gzindex := g })
    (d' := d) R (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) hal
    (by rw [SH_SH]; exact c') rfl rfl rfl rfl rfl rfl ?_
  · rwa [SH_SH] at R'
  · rw [SH_SH]
    obtain ⟨S1, -, -, S4, S5⟩ := R.side st0 (SH_dstate _ _ _ _ _ _)
    refine ⟨S1, fun e => absurd e hfin, hdr, S4, fun d' hd' => ?_⟩
    rw [SH_bytes] at hd'; obtain rfl := Option.some.inj hd'
    exact chain_keep c (SH_bytes _ _ _ _ _ _) (S5 d0 (SH_bytes _ _ _ _ _ _)) (fun pbo' hpb' j hj => by
      rw [hpb] at hpb'
      obtain rfl : pbo = pbo' := by injection hpb' with e; injection e with _ e
      exact hlo j hj) rfl rfl rfl rfl rfl rfl rfl

/-- A segment from `SH H0 i z0 b st0 d0` (no symbols, `pending_out` at `pending_buf`) keeps `Run`, given the header
facts of the new state, and no lookahead in `FINISH_STATE`. -/
theorem seg_run' {h H0 : Heap} {i b : Nat} {z0 : ZStream} {st0 : DeflateState} {d0 d : Array UInt8} {pbo : Nat}
    (R : Run h i b (SH H0 i z0 b st0 d0)) (hpb : st0.pending_buf = .val (.ref (.heap b) pbo))
    (h0 : st0.sym_next = 0) (hpo : st0.pending_out = st0.pending_buf) (a : UInt64) (p : UInt32) (s : Int32)
    (g : UInt32) (hsz : d.size = d0.size) (hlo : ∀ j, j < pbo → d[j]! = d0[j]!)
    (hp : p.toNat ≤ 4 * st0.lit_bufsize.toNat) (hs1 : INIT_STATE ≤ s) (hs2 : s ≤ MAX_STATE)
    (hfin : s = FINISH_STATE → st0.sym_next = 0 ∧ st0.lookahead = 0)
    (hdr : HdrOk (SH H0 i { z0 with adler := a } b { st0 with pending := p, status := s, gzindex := g } d) b
      { st0 with pending := p, status := s, gzindex := g }) :
    Run h i b (SH H0 i { z0 with adler := a } b { st0 with pending := p, status := s, gzindex := g } d) := by
  have hv := R.inv
  obtain ⟨z1, hz1, hb⟩ := R.blk
  obtain rfl : z0 = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain ⟨al, hal, c⟩ := inv_SH hv hb
  have hb8 := c.bits
  simp only [dview] at hb8
  have hb8' : st0.bi_valid.toInt.toNat / 8 ≤ 7 := by
    have a1 : st0.bi_valid.toInt < 64 := Int32.lt_iff_toInt_lt.mp hb8.2
    omega
  have c' := dcore_hdr (H' := SH H0 i { z0 with adler := a } b { st0 with pending := p, status := s, gzindex := g } d)
    (z' := { z0 with adler := a }) c (SH_bytes _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _) hsz h0 hpo s p (by simp only [dview]; omega) hs1 hs2 rfl rfl
  have R' := run_SH (z' := { z0 with adler := a }) (st' := { st0 with pending := p, status := s, gzindex := g })
    (d' := d) R (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) hal
    (by rw [SH_SH]; exact c') rfl rfl rfl rfl rfl rfl ?_
  · rwa [SH_SH] at R'
  · rw [SH_SH]
    obtain ⟨S1, -, -, S4, S5⟩ := R.side st0 (SH_dstate _ _ _ _ _ _)
    refine ⟨S1, hfin, hdr, S4, fun d' hd' => ?_⟩
    rw [SH_bytes] at hd'; obtain rfl := Option.some.inj hd'
    exact chain_keep c (SH_bytes _ _ _ _ _ _) (S5 d0 (SH_bytes _ _ _ _ _ _)) (fun pbo' hpb' j hj => by
      rw [hpb] at hpb'
      obtain rfl : pbo = pbo' := by injection hpb' with e; injection e with _ e
      exact hlo j hj) rfl rfl rfl rfl rfl rfl rfl

end ZlibNgF.Proof.DeflateBody
