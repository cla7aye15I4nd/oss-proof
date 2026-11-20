import ZlibNgF.Proof.«deflate_stored.c.window»

/-!
# The stored block through `pending_buf` (`ZlibNgF`)

`blk_ok`: `zng_tr_stored_block(s, window + block_start, len, last)` with `len` window bytes below `strstart` and room in
`pending_buf` (`len <= pending_buf_size - header bytes`), `block_start += len`, and `flush_pending` keep `SF`
(`deflate_stored.c:174-178`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.StoredBlk
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateFlush ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.StoredIO ZlibNgF.Proof.StoredF ZlibNgF.Proof.StoredTrip ZlibNgF.Proof.StoredWin
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNg.DeflateStored

section parts
open ZlibNg.DeflateP ZlibNg.Trees

/-- The stored block through `pending_buf` (`deflate_stored.c:176-178`), followed by `k`. -/
def blk_part {α : Type} (st : StatePtr) (window : BPtr) (len : UInt32) (last : Int32) (k : M α) : M α := do
  zng_tr_stored_block st (← window.add (← rdD st (·.block_start)).toInt) len last
  let bs ← chkI32 ((← rdD st (·.block_start)).toInt + len.toInt32.toInt)
  wrD st fun s => { s with block_start := bs }
  flush_pending (← strmOf st)
  k

end parts

/-- The clauses of `DCore` after a change of the pending bytes, the bit buffer and `block_start`. -/
theorem dcore_pend {H : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st st' : DeflateState}
    {al : DeflateAllocs} (c : DCore H s z b (dview st) al)
    (he : st' = { st with
      pending := st'.pending
      pending_out := st'.pending_out
      bi_buf := st'.bi_buf
      bi_valid := st'.bi_valid
      bi_used := st'.bi_used
      block_start := st'.block_start })
    {pbo poo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hpo : st'.pending_out = .val (.ref (.heap b) poo)) (hle : pbo ≤ poo)
    (hroom : poo - pbo + st'.pending.toNat ≤ 4 * st.lit_bufsize.toNat + 9)
    (hpz : st'.pending = 0 → st'.pending_out = st.pending_buf) (h0 : 0 ≤ st'.bi_valid) (h8 : st'.bi_valid < 8)
    (hbs : st'.block_start.toInt ≤ st.strstart.toNat)
    (hlo : -(2 ^ 30 + 2 ^ 16) ≤ st'.block_start.toInt) (hsym : st.sym_next = 0) :
    DCore H s z b (dview st') al := by
  have hz : st'.bi_valid.toInt.toNat / 8 = 0 := by
    have a := Int32.le_iff_toInt_le.mp h0
    have a' := Int32.lt_iff_toInt_lt.mp h8
    rw [show (0 : Int32).toInt = 0 from rfl] at a
    rw [show (8 : Int32).toInt = 8 from rfl] at a'
    omega
  have h64 : st'.bi_valid < 64 := Int32.lt_iff_toInt_lt.mpr (by
    have a' := Int32.lt_iff_toInt_lt.mp h8
    rw [show (8 : Int32).toInt = 8 from rfl] at a'
    rw [show (64 : Int32).toInt = 64 from rfl]
    omega)
  obtain ⟨d, wo, po, ho, pbo', hd, hwo, hp, hh, hpb', h1, h2, h3, h4, hsb, -⟩ := c.lay
  simp only [dview] at hpb'
  rw [hpb] at hpb'
  obtain rfl : pbo = pbo' := by injection hpb' with e1; injection e1 with e1
  rw [he]
  exact { c with
    lay := ⟨d, wo, po, ho, pbo, hd, hwo, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hle, by
      simp only [dview]; omega⟩
    pout := hpz
    bits := ⟨h0, h64⟩
    psym := fun hn => absurd hsym hn
    bstart := hbs
    bs_lo := hlo }

/-- The stored block of `len` window bytes from `block_start` through `pending_buf`, then `block_start += len` and
`flush_pending`: `SF` after. -/
theorem blk_ok {h H : Heap} {i b wo : Nat} (F : SF h i b H) (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (len : UInt32) (last : Int32)
    (hl : ∀ st, H.dstate b = some st → (len.toNat : Int) ≤ st.strstart.toNat - st.block_start.toInt ∧
      len.toNat + (st.bi_valid.toInt.toNat + 42) / 8 ≤ st.pending_buf_size.toNat)
    {α : Type} (k : M α) (Q : α → Heap → Prop) (hk : ∀ H', SF h i b H' → Sat H' k Q) :
    Sat H (blk_part (some b) (.ref (.heap b) wo) len last k) Q := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by
    rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  have hp := hp0 st S.hst
  obtain ⟨hl1, hl2⟩ := hl st S.hst
  have hoo := S.hoo
  obtain ⟨hv0, hv8⟩ := S.bits
  obtain ⟨hw1, hw2⟩ := S.lay
  obtain ⟨lb1, lb2, lb3⟩ := S.lb
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  have hws := S.ws.1
  have hp' : st.pending.toNat = 0 := by rw [hp]; rfl
  have hpo : st.pending_out = .val (.ref (.heap b) pbo) := (S.pout hp).trans S.hpb
  rw [← e0]
  unfold blk_part
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  rw [show st.block_start.toInt = ((st.block_start.toInt.toNat : Nat) : Int) by omega]
  refine Sat.bind (Sat.of_eq (add_SH (st.block_start.toInt.toNat) (by omega)) ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.TreesEmitP.stored_block_X_SH S.hpb hv0 (by omega) _ len
    (.inr ⟨_, rfl, by omega⟩) (by omega) (by omega) last) ?_)
  rintro _ H1 ⟨np2, pend, bu, d1, rfl, hpe, -, hb2, w1⟩
  have hd1 : d1.size = d.size := w1.1
  clear w1
  refine sat_gen (fun st3 => st3 = { st with
      pending := st3.pending
      bi_used := st3.bi_used
      bi_buf := st3.bi_buf
      bi_valid := st3.bi_valid } ∧ st3.pending = pend ∧ st3.bi_valid = 0) ⟨rfl, rfl, rfl⟩ ?_
  rintro st3 ⟨he3, hp3, hbv3⟩
  have hbs3 : st3.block_start = st.block_start := by rw [he3]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  have hli : len.toInt32.toInt = len.toNat := DeflateAlloc.u32_toInt32_toInt _ (by omega)
  simp only [chkI32, hbs3, hli]
  rw [ite_t (by omega), pure_bind_M]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (strmOf_SH (by rw [he3]; exact S.strm)) ?_)
  have hnb : (Int32.ofInt (st.block_start.toInt + ↑len.toNat)).toInt = st.block_start.toInt + len.toNat :=
    Int32.toInt_ofInt_of_le (by omega) (by omega)
  refine Sat.bind (Sat.mono (flush_SH (lb := st.lit_bufsize.toNat) (pbo := pbo) (poo := pbo) (ad := X) (oo := oo)
    (ob := ob) S.hb S.hob (by simp [setB]) S.hno hoo ?_ ?_ (Nat.le_refl _) ?_ ?_ lb2 ?_ ?_ ?_) ?_)
  · show st3.pending_buf = _; rw [he3]; exact S.hpb
  · show st3.pending_out = _; rw [he3]; exact hpo
  · show pbo - pbo + st3.pending.toNat + st3.bi_valid.toInt.toNat / 8 ≤ _
    rw [hp3, hbv3]; simp; omega
  · omega
  · show 0 ≤ st3.bi_valid.toInt; rw [hbv3]; decide
  · show st3.bi_valid.toInt < 64; rw [hbv3]; decide
  · intro _; show st3.pending_out = st3.pending_buf; rw [he3]; exact hpo.trans S.hpb.symm
  rintro _ H4 ⟨np, bb, bv, d4, L, z', st', rfl, w4, hbv0, hbv8, hnp, hL, hst', hpn, hpz, hpnz, hz', hno', hav'⟩
  have hnp' : np.toNat = pend.toNat := by
    rw [hnp]; show st3.pending.toNat + st3.bi_valid.toInt.toNat / 8 = _; rw [hp3, hbv3]; rfl
  clear hnp
  rw [OH_eq S.hob, setB_setB]
  obtain ⟨no, ao, tt, rfl⟩ : ∃ no ao tt, z' = { z with next_out := no, avail_out := ao, total_out := tt } :=
    ⟨_, _, _, hz'⟩
  have he : st' = { st with
      pending := st'.pending
      pending_out := st'.pending_out
      bi_buf := st'.bi_buf
      bi_valid := st'.bi_valid
      bi_used := st'.bi_used
      block_start := st'.block_start } := by rw [hst']; rw [he3]
  have hbv : st'.bi_valid = bv := by rw [hst']
  have hbs' : st'.block_start = Int32.ofInt (st.block_start.toInt + ↑len.toNat) := by rw [hst']
  have hpz' : st'.pending = 0 → st'.pending_out = st.pending_buf := fun e => by
    rw [hpz e]; show st3.pending_buf = _; rw [he3]
  have hpnz' : st'.pending ≠ 0 → st'.pending_out = .val (.ref (.heap b) (pbo + L)) := hpnz
  clear hst' hpz hpnz
  have hpend : st'.pending.toNat + L = pend.toNat := by omega
  obtain ⟨poo, hpo', hle', hroom'⟩ : ∃ poo, st'.pending_out = .val (.ref (.heap b) poo) ∧ pbo ≤ poo ∧
      poo - pbo + st'.pending.toNat ≤ 4 * st.lit_bufsize.toNat + 9 := by
    by_cases h0 : st'.pending = 0
    · refine ⟨pbo, (hpz' h0).trans S.hpb, Nat.le_refl _, ?_⟩
      rw [h0]; simp
    · exact ⟨pbo + L, hpnz' h0, by omega, by omega⟩
  have hX4 := copyFold_size d4 oo pbo (List.range' 0 L) X
  have hXo := copyFold_out d4 X oo pbo L
  have hsy : (dview st').sym_next = 0 := by show st'.sym_next = 0; rw [he]; exact S.sym
  have hb0' : 0 ≤ st'.bi_valid := Int32.le_iff_toInt_le.mpr (by rw [hbv, show (0 : Int32).toInt = 0 from rfl]; exact hbv0)
  have hb8' : st'.bi_valid < 8 := Int32.lt_iff_toInt_lt.mpr (by rw [hbv, show (8 : Int32).toInt = 8 from rfl]; exact hbv8)
  have hd4 : d4.size = d.size := by rw [w4.1, hd1]
  have hbs1 : st'.block_start.toInt ≤ st.strstart.toNat := by rw [hbs', hnb]; omega
  have hbs2 : -(2 ^ 30 + 2 ^ 16) ≤ st'.block_start.toInt := by rw [hbs', hnb]; omega
  have hLA : L ≤ z.avail_out.toNat := by omega
  refine hk _ (sf_next F S.hz S.hst S.hno S.hX (L := L) hX4 hXo hLA rfl (Or.inl ⟨rfl, rfl⟩) (Nat.le_refl _) hno' hav'
    (fun al _ c => dcore_mv (dcore_pend c he S.hpb hpo' hle' hroom' hpz' hb0' hb8' hbs1 hbs2 S.sym)
      S.hd (SH_bytes _ _ _ _ _ _) hd4 hsy rfl rfl) ?_ ?_)
  · rw [he]; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  · refine ⟨Int32.le_iff_toInt_le.mpr (by rw [hbs', hnb]; show (0 : Int) ≤ _; omega), ?_, hb8'⟩
    rw [he]; exact S.sym

end ZlibNgF.Proof.StoredBlk
