import ZlibNgF.Proof.«insert_string_p.h.grow»
import ZlibNgF.Proof.«deflate_strategy.common»

/-!
# Insertions inside the strategy loop (`ZlibNgF`)

An insertion function changes the bytes of the stream's block below the end of `head` only (`GPost`), so the loop
frame of a strategy (`SLF`, `SLC`, `SLI` of `Proof/deflate_strategy.common.lean`) survives it: the invariant reads
the block's bytes through the sizes, the layout and the symbols in `sym_buf`, which lie after `head`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InsertLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.Strategy ZlibNgF.Proof.InsertGrow
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-- The invariant's clauses on bytes changed below the end of `head` only. -/
theorem dcore_bytes {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    {d d' : Array UInt8} (c : DCore (SH H0 i z b st d) (some i) z b (dview st) al)
    (hw : ∀ ho, st.head = .val (.ref (.heap b) ho) → WrIn d 0 (ho + 131072) d') :
    DCore (SH H0 i z b st d') (some i) z b (dview st) al := by
  obtain ⟨ho, d0, hd0, hh, hho⟩ := c.head
  obtain rfl : d = d0 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd0)
  have W := hw ho hh
  obtain ⟨d1, wo, po, ho1, pbo, hd1, hwo, hp, hh1, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  obtain rfl : d = d1 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd1)
  simp only [dview] at hh hh1
  rw [hh] at hh1
  obtain rfl : ho = ho1 := by injection hh1 with e; injection e
  obtain ⟨d2, sbo, hd2, hsb2, hsym⟩ := c.symv
  obtain rfl : d = d2 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd2)
  simp only [dview] at hsb2 hsb
  rw [hsb] at hsb2
  obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hsb2 with e; injection e
  exact { c with
    head := ⟨ho, d', SH_bytes _ _ _ _ _ _, hh, by rw [W.1]; exact hho⟩
    lay := ⟨d', wo, po, ho, pbo, SH_bytes _ _ _ _ _ _, hwo, hp, by simp only [dview]; exact hh, hpb, h1, h2, h3,
      by rw [W.1]; exact h4, hsb, poo, hpo, hpoo, hpe⟩
    symv := ⟨d', _, SH_bytes _ _ _ _ _ _, hsb, hsym.of_eq fun k _ => W.2 _ (Or.inr (by omega))⟩ }

/-- `SLF` on bytes changed below the end of `head` only. -/
theorem slf_bytes {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d))
    (hw : ∀ ho, st.head = .val (.ref (.heap b) ho) → WrIn d 0 (ho + 131072) d') : SLF h i b (SH H0 i z b st d') :=
  slf_SH F (fun _ _ c => dcore_bytes c hw) rfl rfl rfl rfl (F.st st (SH_dstate _ _ _ _ _ _)).2.2 (StratKeeps.refl _)

/-- `SLC` on bytes changed below the end of `head` only. -/
theorem slc_bytes {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8}
    (C : SLC h i b (SH H0 i z b st d))
    (hw : ∀ ho, st.head = .val (.ref (.heap b) ho) → WrIn d 0 (ho + 131072) d') : SLC h i b (SH H0 i z b st d') :=
  ⟨slf_bytes C.1 hw, fun st2 h2 => by
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    exact C.2 st (SH_dstate _ _ _ _ _ _)⟩

/-- `SLI` on bytes changed below the end of `head` only (the state's `head` is that of `FS st la ss`). -/
theorem sli_bytes {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d))
    (hw : ∀ ho, st.head = .val (.ref (.heap b) ho) → WrIn d 0 (ho + 131072) d') :
    SLI h i b la ss (SH H0 i z b st d') := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  simp only [SH_dstate, SH_bytes] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  refine ⟨H1, z1, st, d', ?_, slc_bytes C hw⟩
  have e3 := congrArg (fun H => H.streams i) e
  simp only [SH_streams] at e3
  obtain rfl := Option.some.inj e3
  rw [← SH_SH H0 i z z b st st d d', e, SH_SH]

/-- The hash-table layout (`HLay`) of the state of an `SLF` heap, `w_size` a power of two, the window before `prev`. -/
theorem slf_hlay {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) :
    ∃ wo po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho ∧ (∃ k, st.w_size.toNat = 2 ^ k) ∧
      wo + st.window_size.toNat ≤ po := by
  obtain ⟨z1, st1, al, hz1, hb, hst1, -, c⟩ := F.live
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  obtain ⟨d1, wo, po, ho, pbo, hd1, hwo, hp, hh, -, h1, h2, h3, h4, -⟩ := c.lay
  obtain rfl : d = d1 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd1)
  obtain ⟨k, -, -, hk⟩ := c.wpow
  obtain ⟨w1, -⟩ := c.sizes
  simp only [dview] at hwo hp hh h1 h2 hk w1
  exact ⟨wo, po, ho, ⟨hwo, hp, hh, by omega, by omega, by omega, h2⟩, ⟨k, hk⟩, h1⟩

/-- The chains of state `st` (block `b`) grow by `S` from bytes `d` to `d'` (the premise of `ChainOk.grow`). -/
def GrowSt (b : Nat) (st : DeflateState) (d d' : Array UInt8) (S : Nat → Prop) : Prop :=
  ∀ ho po, st.head = .val (.ref (.heap b) ho) → st.prev = .val (.ref (.heap b) po) → Grow d d' ho po st.w_size.toNat S

theorem GrowSt.refl (b : Nat) (st : DeflateState) (d : Array UInt8) (S : Nat → Prop) : GrowSt b st d d S :=
  fun ho po _ _ => Grow.refl d ho po _ S

theorem GrowSt.trans {b : Nat} {st : DeflateState} {d1 d2 d3 : Array UInt8} {S1 S2 S : Nat → Prop}
    (a : GrowSt b st d1 d2 S1) (c : GrowSt b st d2 d3 S2) (h1 : ∀ q, S1 q → S q) (h2 : ∀ q, S2 q → S q) :
    GrowSt b st d1 d3 S :=
  fun ho po hh hp => (a ho po hh hp).trans (c ho po hh hp) h1 h2

/-- An insertion function (any `m` with the post `GPost` under the layout) inside the strategy loop: `SLI` again on
the new bytes, and the chains grown. -/
theorem sli_ins {α : Type} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} {m : M α} {S : Nat → Prop} (I : SLI h i b la ss (SH H0 i z b st d))
    (hm : ∀ wo po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho → (∃ k, st.w_size.toNat = 2 ^ k) →
      wo + st.window_size.toNat ≤ po → Sat (SH H0 i z b st d) m (GPost H0 i z b st d ho po st.w_size.toNat S)) :
    Sat (SH H0 i z b st d) m (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLI h i b la ss H' ∧ GrowSt b st d d' S) := by
  have I0 := I
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I0
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  simp only [SH_dstate, SH_bytes] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain ⟨wo, po, ho, L, hp, hwp⟩ := slf_hlay C.1
  have L' : ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho := ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩
  refine Sat.mono (hm wo po ho L' hp hwp) ?_
  rintro _ _ ⟨d', rfl, w, g⟩
  refine ⟨d', rfl, sli_bytes I fun ho' hh => ?_, fun ho' po' hh hpv => ?_⟩
  · rw [L'.head] at hh
    obtain rfl : ho = ho' := by injection hh with e; injection e
    exact w.widen (Nat.zero_le _) (Nat.le_refl _)
  · rw [L'.head] at hh; rw [L'.prev] at hpv
    obtain rfl : ho = ho' := by injection hh with e; injection e
    obtain rfl : po = po' := by injection hpv with e; injection e
    exact g

/-- `insert_knuth(s, window, str)` inside the strategy loop, its 4-byte read in the window. -/
theorem sli_insert_knuth {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (str : UInt32) (hr : str.toNat + 4 ≤ st.window_size.toNat) (hs : str.toNat < 65536) :
    Sat (SH H0 i z b st d) (ZlibNg.InsertStringP.insert_knuth (some b) (.ref (.heap b) wo) str)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLI h i b la ss H' ∧ GrowSt b st d d' (· = str.toNat)) :=
  sli_ins I fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_knuth_G L hp str (by have := L.pw; omega) hs

/-- `insert_match(s, window, m, max_insert_count)` inside the strategy loop (as `insert_match_G`). -/
theorem sli_insert_match {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (m : ZlibNg.DeflateMedium.Match) (mic : UInt32) (hm2 : 2 ≤ mic.toNat) (hm3 : mic.toNat ≤ 258)
    (hl : 2 ≤ m.match_length.toNat) (ho2 : m.orgstart.toNat ≤ m.strstart.toNat + m.match_length.toNat)
    (hs : m.strstart.toNat + m.match_length.toNat ≤ 65536)
    (hr : m.strstart.toNat + m.match_length.toNat + 3 ≤ st.window_size.toNat) :
    Sat (SH H0 i z b st d) (ZlibNg.DeflateMedium.insert_match (some b) (.ref (.heap b) wo) m mic)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLI h i b la ss H' ∧
        GrowSt b st d d' (fun q => m.strstart.toNat < q ∧ q < m.strstart.toNat + m.match_length.toNat)) :=
  sli_ins I fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_match_G L hp m mic hm2 hm3 hl ho2 hs (by have := L.pw; omega)

/-- `insert_knuth_val(s, str, val)` inside the strategy loop. -/
theorem sli_insert_knuth_val {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (str val : UInt32) (hs : str.toNat < 65536) :
    Sat (SH H0 i z b st d) (ZlibNg.InsertStringP.insert_knuth_val (some b) str val)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLI h i b la ss H' ∧ GrowSt b st d d' (· = str.toNat)) :=
  sli_ins I fun _ _ _ L hp _ => insert_knuth_val_G L hp str val hs

/-- `insert_knuth_spread_static(s, window, str, count, max_inserts)` inside the strategy loop (`count >= 2`,
`max_inserts >= 2`). -/
theorem sli_insert_spread {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (hw : st.window = .val (.ref (.heap b) wo))
    (str count mi : UInt32) (hc : 2 ≤ count.toNat) (hm : 2 ≤ mi.toNat) (hs : str.toNat + count.toNat ≤ 65536)
    (hr : str.toNat + count.toNat + 3 ≤ st.window_size.toNat) :
    Sat (SH H0 i z b st d) (ZlibNg.InsertStringP.insert_knuth_spread_static (some b) (.ref (.heap b) wo) str count mi)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧ SLI h i b la ss H' ∧
        GrowSt b st d d' (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) :=
  sli_ins I fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_knuth_spread_G L hp str count mi hc hm hs (by have := L.pw; omega)

end ZlibNgF.Proof.InsertLoop
