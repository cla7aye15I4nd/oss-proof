import ZlibNgF.Proof.«deflate_fast.c.frame»
import ZlibNgF.Proof.«deflate_fast.c.chain»
import ZlibNgF.Proof.«deflate_medium.c.step»

/-!
# Steps of `deflate_fast` (`ZlibNgF`)

The hash chains across one trip of `deflate_fast`. At level 2 the chain clauses (`ChainOk`) hold with the limit
`strstart`, so the insertion of `strstart` itself breaks them until `strstart` moves past it. The trip records the
growth from its start instead (`CG`: the bytes grew the chains of the trip-start bytes by a set `S` of positions,
the chain fields of the state kept), and `ck_of_cg` gives `ChainOk` back once `strstart` is above every position of
`S`. A tally writes `sym_buf`, after `head`, and keeps the chain fields (`tally_dist_K`, `tally_lit_K`), so the growth
survives it (`cg_tally`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FastSteps
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop ZlibNgF.Proof.InsertLoopW ZlibNgF.Proof.InsertChain
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNg.DeflateP

/-- `ChainOk` of the state and bytes of block `b` in `H`. -/
def CK (b : Nat) (H : Heap) : Prop :=
  ∀ st d, H.dstate b = some st → H.bytes b = some d → ChainOk b d st

/-- The chain fields of the state kept from `st` to `st'`. -/
def CF (st st' : DeflateState) : Prop :=
  st'.level = st.level ∧ st'.strategy = st.strategy ∧ st'.head = st.head ∧ st'.prev = st.prev ∧
    st'.w_size = st.w_size

theorem CF.refl (st : DeflateState) : CF st st := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem CF.trans {a b c : DeflateState} (h1 : CF a b) (h2 : CF b c) : CF a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

/-- The growth of the chains since the trip-start state `st0` and bytes `d0`, by the positions `S`. -/
def CG (b : Nat) (st0 : DeflateState) (d0 : Array UInt8) (S : Nat → Prop) (H : Heap) : Prop :=
  ∃ st d, H.dstate b = some st ∧ H.bytes b = some d ∧ GrowSt b st0 d0 d S ∧ CF st0 st

theorem cg_start {b : Nat} {H0 : Heap} {i : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (S : Nat → Prop) : CG b st d S (SH H0 i z b st d) :=
  ⟨st, d, SH_dstate _ _ _ _ _ _, SH_bytes _ _ _ _ _ _, GrowSt.refl _ _ _ _, CF.refl _⟩

theorem cg_mono {b : Nat} {st0 : DeflateState} {d0 : Array UInt8} {S T : Nat → Prop} {H : Heap}
    (G : CG b st0 d0 S H) (hST : ∀ q, S q → T q) : CG b st0 d0 T H := by
  obtain ⟨st, d, h1, h2, g, c⟩ := G
  exact ⟨st, d, h1, h2, fun ho po hh hp => (g ho po hh hp).mono hST, c⟩

/-- An insertion (bytes only, growth `S'`) after growth `S`. -/
theorem cg_ins {b : Nat} {st0 : DeflateState} {d0 : Array UInt8} {S S' : Nat → Prop} {H0 : Heap} {i : Nat}
    {z : ZStream} {st : DeflateState} {d d' : Array UInt8} (G : CG b st0 d0 S (SH H0 i z b st d))
    (g : GrowSt b st d d' S') : CG b st0 d0 (fun q => S q ∨ S' q) (SH H0 i z b st d') := by
  obtain ⟨st1, d1, h1, h2, g0, c⟩ := G
  obtain rfl : st1 = st := Option.some.inj (h1.symm.trans (SH_dstate _ _ _ _ _ _))
  obtain rfl : d1 = d := Option.some.inj (h2.symm.trans (SH_bytes _ _ _ _ _ _))
  refine ⟨st1, d', SH_dstate _ _ _ _ _ _, SH_bytes _ _ _ _ _ _, fun ho po hh hp => ?_, c⟩
  have g1 := g ho po (by rw [c.2.2.1]; exact hh) (by rw [c.2.2.2.1]; exact hp)
  rw [c.2.2.2.2] at g1
  exact (g0 ho po hh hp).trans g1 (fun q h => Or.inl h) (fun q h => Or.inr h)

/-- A change of the state that keeps its chain fields. -/
theorem cg_st {b : Nat} {st0 : DeflateState} {d0 : Array UInt8} {S : Nat → Prop} {H0 : Heap} {i : Nat}
    {z : ZStream} {st st' : DeflateState} {d : Array UInt8} (G : CG b st0 d0 S (SH H0 i z b st d))
    (c : CF st st') : CG b st0 d0 S (SH H0 i z b st' d) := by
  obtain ⟨st1, d1, h1, h2, g0, c0⟩ := G
  obtain rfl : st1 = st := Option.some.inj (h1.symm.trans (SH_dstate _ _ _ _ _ _))
  obtain rfl : d1 = d := Option.some.inj (h2.symm.trans (SH_bytes _ _ _ _ _ _))
  exact ⟨st', d1, SH_dstate _ _ _ _ _ _, SH_bytes _ _ _ _ _ _, g0, c0.trans c⟩

/-- A store at or after `ho + 131072` (`head` at `ho`) with the chain fields kept. -/
theorem cg_wr {b : Nat} {st0 : DeflateState} {d0 : Array UInt8} {S : Nat → Prop} {H0 : Heap} {i : Nat}
    {z : ZStream} {st st' : DeflateState} {d d' : Array UInt8} {lo hi : Nat} (G : CG b st0 d0 S (SH H0 i z b st d))
    (c : CF st st') (W : WrIn d lo hi d')
    (hl : ∀ ho po, st.head = .val (.ref (.heap b) ho) → st.prev = .val (.ref (.heap b) po) →
      ho + 131072 ≤ lo ∧ po + 2 * st.w_size.toNat ≤ ho ∧ 0 < st.w_size.toNat) :
    CG b st0 d0 S (SH H0 i z b st' d') := by
  obtain ⟨st1, d1, h1, h2, g0, c0⟩ := G
  obtain rfl : st1 = st := Option.some.inj (h1.symm.trans (SH_dstate _ _ _ _ _ _))
  obtain rfl : d1 = d := Option.some.inj (h2.symm.trans (SH_bytes _ _ _ _ _ _))
  refine ⟨st', d', SH_dstate _ _ _ _ _ _, SH_bytes _ _ _ _ _ _, fun ho po hh hp => ?_, c0.trans c⟩
  obtain ⟨a1, a2, a3⟩ := hl ho po (by rw [c0.2.2.1]; exact hh) (by rw [c0.2.2.2.1]; exact hp)
  rw [c0.2.2.2.2] at a2 a3
  exact (g0 ho po hh hp).trans (grow_wrin S W a1 a2 a3) (fun q h => h) (fun q h => h)

/-- `chainLim` at level 2 is `strstart`. -/
theorem chainLim_2 {st : DeflateState} (hl : st.level = 2) : chainLim st = st.strstart.toNat := by
  simp only [chainLim, hl]; simp [show ¬ ((3 : Int32) ≤ 2) by decide]

/-- `ChainOk` at the end of a trip from the growth since its start, with `strstart` above every grown position. -/
theorem ck_of_cg {b : Nat} {st0 : DeflateState} {d0 : Array UInt8} {S : Nat → Prop} {H : Heap}
    (C0 : ChainOk b d0 st0) (G : CG b st0 d0 S H) (hl : st0.level = 2)
    (hs : ∀ st, H.dstate b = some st → st0.strstart.toNat ≤ st.strstart.toNat ∧
      ∀ q, S q → q ≠ 0 → q < st.strstart.toNat) : CK b H := by
  intro st d h1 h2
  obtain ⟨st1, d1, h3, h4, g, c⟩ := G
  obtain rfl : st1 = st := Option.some.inj (h3.symm.trans h1)
  obtain rfl : d1 = d := Option.some.inj (h4.symm.trans h2)
  obtain ⟨e1, e2, e3, e4, e5⟩ := c
  obtain ⟨hss, hq⟩ := hs st1 h1
  have hl' : st1.level = 2 := e1.trans hl
  exact ChainOk.grow C0 g e1 e2 e3 e4 e5 hss (by rw [chainLim_2 hl, chainLim_2 hl']; exact hss)
    (fun q hS hq0 => by rw [chainLim_2 hl']; exact hq q hS hq0)

/-- The tallies' state keeps the chain fields, `strstart`, `lookahead`, `match_start` and `window`. -/
def TK (st st' : DeflateState) : Prop :=
  CF st st' ∧ st'.strstart = st.strstart ∧ st'.lookahead = st.lookahead ∧ st'.match_start = st.match_start ∧
    st'.window = st.window

/-- `SLI` gives `SLW` with the same locals. -/
theorem sli_slw {h H : Heap} {i b : Nat} {la ss : UInt32} (I : SLI h i b la ss H) : SLW h i b la ss H := by
  obtain ⟨H0, z, st, d, rfl, C⟩ := I
  exact ⟨H0, z, st, d, rfl, C.1, (C.2 _ (SH_dstate _ _ _ _ _ _)).1⟩

open ZlibNgF.Proof.Tally (tally_dist_SH W4_wr) in
/-- `zng_tr_tally_dist(s, dist, len)` under `SLW` with `sym_next <= sym_end`: an `SH` heap over the same base and
record, the state's other fields kept (`TK`), the bytes changed inside `sym_buf` only, after `head`. -/
theorem tally_dist_K {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (W : SLW h i b la ss (SH H0 i z b st d)) (hle : st.sym_next ≤ st.sym_end) (dist len : UInt32)
    (hlen : len.toNat < 256) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) :
    Sat (SH H0 i z b st d) (zng_tr_tally_dist (some b) dist len) (fun _ H' => ∃ st' d' lo hi,
      H' = SH H0 i z b st' d' ∧ TK st st' ∧ WrIn d lo hi d' ∧
      ∀ ho, st.head = .val (.ref (.heap b) ho) → ho + 131072 ≤ lo) := by
  have W0 := W
  obtain ⟨H1, z1, st1, d1, e, F, -⟩ := W0
  obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
  obtain ⟨sbo, hsb, hk, hlt, hdt⟩ := slf_sym F hle
  obtain ⟨wo, po, ho, L, -, -, -, -, -, -, -, hsy⟩ := slw_lay W
  refine Sat.mono (tally_dist_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d) dist len hlen hd1 hd2
    hsb hk hlt hdt) ?_
  rintro r H' ⟨rfl, -⟩
  refine ⟨_, _, sbo, sbo + st.sym_next.toNat + 4, rfl, ⟨CF.refl _, rfl, rfl, rfl, rfl⟩,
    (W4_wr _ _ _).widen (by omega) (by omega), fun ho' hh => ?_⟩
  rw [L.head] at hh; obtain rfl : ho = ho' := by injection hh with e; injection e
  exact hsy sbo hsb

open ZlibNgF.Proof.Tally (tally_lit_SH W4_wr) in
/-- `zng_tr_tally_lit(s, c)` under `SLW` with `sym_next <= sym_end`: as `tally_dist_K`. -/
theorem tally_lit_K {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (W : SLW h i b la ss (SH H0 i z b st d)) (hle : st.sym_next ≤ st.sym_end) (c : UInt8) :
    Sat (SH H0 i z b st d) (zng_tr_tally_lit (some b) c) (fun _ H' => ∃ st' d' lo hi,
      H' = SH H0 i z b st' d' ∧ TK st st' ∧ WrIn d lo hi d' ∧
      ∀ ho, st.head = .val (.ref (.heap b) ho) → ho + 131072 ≤ lo) := by
  have W0 := W
  obtain ⟨H1, z1, st1, d1, e, F, -⟩ := W0
  obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
  obtain ⟨sbo, hsb, hk, hlt, -⟩ := slf_sym F hle
  obtain ⟨wo, po, ho, L, -, -, -, -, -, -, -, hsy⟩ := slw_lay W
  refine Sat.mono (tally_lit_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d) c hsb hk hlt) ?_
  rintro r H' ⟨rfl, -⟩
  refine ⟨_, _, sbo, sbo + st.sym_next.toNat + 4, rfl, ⟨CF.refl _, rfl, rfl, rfl, rfl⟩,
    (W4_wr _ _ _).widen (by omega) (by omega), fun ho' hh => ?_⟩
  rw [L.head] at hh; obtain rfl : ho = ho' := by injection hh with e; injection e
  exact hsy sbo hsb

/-- The growth across a tally (`tally_dist_K` / `tally_lit_K`). -/
theorem cg_tally {b : Nat} {st0 : DeflateState} {d0 : Array UInt8} {S : Nat → Prop} {h H0 : Heap} {i : Nat}
    {z : ZStream} {st st' : DeflateState} {d d' : Array UInt8} {lo hi : Nat} {la ss : UInt32}
    (W : SLW h i b la ss (SH H0 i z b st d)) (G : CG b st0 d0 S (SH H0 i z b st d)) (K : TK st st')
    (Wr : WrIn d lo hi d') (hl : ∀ ho, st.head = .val (.ref (.heap b) ho) → ho + 131072 ≤ lo) :
    CG b st0 d0 S (SH H0 i z b st' d') := by
  obtain ⟨wo, po, ho, L, -, w1, -⟩ := slw_lay W
  refine cg_wr G K.1 Wr fun ho' po' hh hp => ?_
  rw [L.head] at hh; rw [L.prev] at hp
  obtain rfl : ho = ho' := by injection hh with e; injection e
  obtain rfl : po = po' := by injection hp with e; injection e
  exact ⟨hl ho L.head, L.ph, by omega⟩

/-- The input that `fill_window` reads, under `SLF`. -/
theorem dinput_of {h H : Heap} {i b : Nat} (F : SLF h i b H) : DInput H (some i) := by
  obtain ⟨z, hz, hb⟩ := F.blk
  obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, hin0, -, -, hdj⟩ := F.io
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb.symm.trans hb2)
  obtain ⟨z3, ⟨i3, e3, hz3⟩, -, hni⟩ := F.set
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  exact ⟨z, b, ⟨i, rfl, hz⟩, hb, hin0, (hdj _ (.inl rfl)).2, hni⟩

end ZlibNgF.Proof.FastSteps
