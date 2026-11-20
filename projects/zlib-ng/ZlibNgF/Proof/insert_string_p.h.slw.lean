import ZlibNgF.Proof.«insert_string_p.h.sli»

/-!
# Insertions after a tally that filled the symbol buffer (`ZlibNgF`)

`deflate_fast` and `deflate_medium` insert the positions of a match after its tally, which may have filled the symbol
buffer: the loop state is then `SLW` (`Proof/deflate_strategy.common.lean`), not `SLI`. An insertion changes the bytes
of the stream's block below the end of `head` only, so `SLW` survives it (`slw_bytes`), as `SLI` does (`sli_bytes`).

* `slf_lay`: the layout facts of a state under `SLF` (as `MediumStep.sli_lay`);
* `sl_ins`: an insertion function (`GPost`) keeps `SLW` and `SLI` with any locals and grows the chains (`GrowSt`);
* `sl_insert_knuth`, `sl_insert_spread`: the 4-byte reads may run up to 256 bytes past `window_size` (the window is
  followed by `prev`);
* `slw_wr`, `sli_wr`: a store of `lookahead` or `strstart` into the state keeps `SLW` / `SLI` with the same locals;
* `grow_wrin`: a store at or after the end of `head` grows the chains by nothing.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InsertLoopW
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.Strategy ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop ZlibNgF.Proof.InsertChain
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.DeflateFacts (posAt)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-- Two `SH` heaps over one stream and block are equal only with the same record, state and bytes. -/
theorem SH_inj {H0 H1 : Heap} {i b : Nat} {z z1 : ZStream} {st st1 : DeflateState} {d d1 : Array UInt8}
    (e : SH H0 i z b st d = SH H1 i z1 b st1 d1) : z1 = z ∧ st1 = st ∧ d1 = d := by
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  have e3 := congrArg (fun H => H.streams i) e
  simp only [SH_dstate, SH_bytes, SH_streams] at e1 e2 e3
  exact ⟨(Option.some.inj e3).symm, (Option.some.inj e1).symm, (Option.some.inj e2).symm⟩

/-- A change of the state and bytes of an `SH` heap equal to another `SH` heap. -/
theorem SH_re {H0 H1 : Heap} {i b : Nat} {z : ZStream} {st st' : DeflateState} {d d' : Array UInt8}
    (e : SH H0 i z b st d = SH H1 i z b st d) : SH H0 i z b st' d' = SH H1 i z b st' d' := by
  rw [← SH_SH H0 i z z b st st' d d', e, SH_SH]

/-- `SLW` on bytes changed below the end of `head` only. -/
theorem slw_bytes {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8} {la ss : UInt32}
    (W : SLW h i b la ss (SH H0 i z b st d))
    (hw : ∀ ho, st.head = .val (.ref (.heap b) ho) → WrIn d 0 (ho + 131072) d') :
    SLW h i b la ss (SH H0 i z b st d') := by
  obtain ⟨H1, z1, st1, d1, e, F, hp⟩ := W
  obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
  exact ⟨H1, z, st, d', SH_re e, slf_bytes F hw, hp⟩

/-- The layout facts of a state under `SLF`: the hash layout, the sizes, and the room of `longest_match_c`. -/
theorem slf_lay {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) :
    ∃ wo po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho ∧ (∃ k, st.w_size.toNat = 2 ^ k) ∧
      512 ≤ st.w_size.toNat ∧ st.w_size.toNat ≤ 32768 ∧
      st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat ∧ st.window_size.toNat ≤ 65536 ∧
      wo + st.window_size.toNat ≤ po ∧ wo + 131400 ≤ d.size ∧
      (∀ sbo, st.sym_buf = .val (.ref (.heap b) sbo) → ho + 131072 ≤ sbo) := by
  obtain ⟨z2, st2, al, hz2, hb2, hst2, -, c⟩ := F.live
  obtain rfl : st = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
  obtain ⟨wo, po, ho, pbo, L, hwp, hpb, hhp, hsb⟩ := ZlibNgF.Proof.FillFacts.hlay_of c (SH_bytes _ _ _ _ _ _)
  obtain ⟨k, -, -, hk⟩ := c.wpow
  obtain ⟨w1, w2, hws, -⟩ := c.sizes
  have hlook : st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat := c.look
  have hws' : st.window_size = W_BUF_SIZE st.w_size := hws
  have w1' : 512 ≤ st.w_size.toNat := w1
  have w2' : st.w_size.toNat ≤ 32768 := w2
  have h65 : st.window_size.toNat ≤ 65536 := by
    rw [hws', DeflateInit.wbuf_toNat _ w2']; unfold DeflateAlloc.dWS; split <;> omega
  have h1k : 1024 ≤ st.window_size.toNat := by
    rw [hws', DeflateInit.wbuf_toNat _ w2']; unfold DeflateAlloc.dWS; split <;> omega
  have hL := L.ph
  have hLd := L.hd
  refine ⟨wo, po, ho, L, ⟨k, hk⟩, w1', w2', hlook, h65, hwp, by omega, fun s hs => ?_⟩
  rw [hsb] at hs; obtain rfl : pbo + st.lit_bufsize.toNat + 8 = s := by injection hs with e; injection e
  omega

/-- The layout facts under `SLW` with the locals `la` / `ss`. -/
theorem slw_lay {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (W : SLW h i b la ss (SH H0 i z b st d)) :
    ∃ wo po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho ∧ (∃ k, st.w_size.toNat = 2 ^ k) ∧
      512 ≤ st.w_size.toNat ∧ st.w_size.toNat ≤ 32768 ∧ ss.toNat + la.toNat ≤ st.window_size.toNat ∧
      st.window_size.toNat ≤ 65536 ∧ wo + st.window_size.toNat ≤ po ∧ wo + 131400 ≤ d.size ∧
      (∀ sbo, st.sym_buf = .val (.ref (.heap b) sbo) → ho + 131072 ≤ sbo) := by
  obtain ⟨H1, z1, st1, d1, e, F, -⟩ := W
  obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
  obtain ⟨wo, po, ho, L, hp, a1, a2, a3, a4, a5, a6, a7⟩ := slf_lay F
  exact ⟨wo, po, ho, ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩, hp, a1, a2, a3, a4, a5, a6, a7⟩

/-- An insertion function (any `m` with the post `GPost` under the layout) keeps `SLW` and `SLI` with any locals and
grows the chains by `S`. -/
theorem sl_ins {α : Type} {h H0 : Heap} {i b wo po ho : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {m : M α} {S : Nat → Prop} (L : ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho)
    (hm : Sat (SH H0 i z b st d) m (GPost H0 i z b st d ho po st.w_size.toNat S)) :
    Sat (SH H0 i z b st d) m (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧
      (∀ la ss, SLW h i b la ss (SH H0 i z b st d) → SLW h i b la ss H') ∧
      (∀ la ss, SLI h i b la ss (SH H0 i z b st d) → SLI h i b la ss H') ∧ GrowSt b st d d' S) := by
  refine Sat.mono hm ?_
  rintro _ _ ⟨d', rfl, w, g⟩
  have hw : ∀ ho', st.head = .val (.ref (.heap b) ho') → WrIn d 0 (ho' + 131072) d' := fun ho' hh => by
    rw [L.head] at hh
    obtain rfl : ho = ho' := by injection hh with e; injection e
    exact w.widen (Nat.zero_le _) (Nat.le_refl _)
  refine ⟨d', rfl, fun la ss W => slw_bytes W hw, fun la ss I => sli_bytes I hw, fun ho' po' hh hpv => ?_⟩
  rw [L.head] at hh; rw [L.prev] at hpv
  obtain rfl : ho = ho' := by injection hh with e; injection e
  obtain rfl : po = po' := by injection hpv with e; injection e
  exact g

/-- `insert_knuth(s, window, str)` with its 4-byte read below `window_size + 256` (the window is followed by
`prev`). -/
theorem sl_insert_knuth {h H0 : Heap} {i b wo po ho : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (L : ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (hwp : wo + st.window_size.toNat ≤ po) (hws : 512 ≤ st.w_size.toNat)
    (str : UInt32) (hr : str.toNat + 4 ≤ st.window_size.toNat + 256) (hs : str.toNat < 65536) :
    Sat (SH H0 i z b st d) (ZlibNg.InsertStringP.insert_knuth (some b) (.ref (.heap b) wo) str)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧
      (∀ la ss, SLW h i b la ss (SH H0 i z b st d) → SLW h i b la ss H') ∧
      (∀ la ss, SLI h i b la ss (SH H0 i z b st d) → SLI h i b la ss H') ∧ GrowSt b st d d' (· = str.toNat)) :=
  sl_ins L (insert_knuth_G L hp str (by have := L.pw; omega) hs)

/-- `insert_knuth_spread_static(s, window, str, count, max_inserts)` (`count >= 2`, `max_inserts >= 2`) with its
reads below `window_size + 256`. -/
theorem sl_insert_spread {h H0 : Heap} {i b wo po ho : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (L : ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (hwp : wo + st.window_size.toNat ≤ po) (hws : 512 ≤ st.w_size.toNat)
    (str count mi : UInt32) (hc : 2 ≤ count.toNat) (hm : 2 ≤ mi.toNat) (hs : str.toNat + count.toNat ≤ 65536)
    (hr : str.toNat + count.toNat + 3 ≤ st.window_size.toNat + 256) :
    Sat (SH H0 i z b st d) (ZlibNg.InsertStringP.insert_knuth_spread_static (some b) (.ref (.heap b) wo) str count mi)
      (fun _ H' => ∃ d', H' = SH H0 i z b st d' ∧
      (∀ la ss, SLW h i b la ss (SH H0 i z b st d) → SLW h i b la ss H') ∧
      (∀ la ss, SLI h i b la ss (SH H0 i z b st d) → SLI h i b la ss H') ∧
      GrowSt b st d d' (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) :=
  sl_ins L (insert_knuth_spread_G L hp str count mi hc hm hs (by have := L.pw; omega))

/-- A change of the state that keeps it up to `lookahead` / `strstart` keeps `SLW` with the same locals. -/
theorem slw_wr {h H0 : Heap} {i b : Nat} {z : ZStream} {st st' : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (W : SLW h i b la ss (SH H0 i z b st d)) (hf : FS st' la ss = FS st la ss) :
    SLW h i b la ss (SH H0 i z b st' d) := by
  obtain ⟨H1, z1, st1, d1, e, F, hp⟩ := W
  obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
  refine ⟨H1, z, st', d, SH_re e, by rw [hf]; exact F, ?_⟩
  have := congrArg DeflateState.pending hf
  simp only [] at this
  rw [this]; exact hp

/-- A change of the state that keeps it up to `lookahead` / `strstart` keeps `SLI` with the same locals. -/
theorem sli_wr {h H0 : Heap} {i b : Nat} {z : ZStream} {st st' : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d)) (hf : FS st' la ss = FS st la ss) :
    SLI h i b la ss (SH H0 i z b st' d) := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
  exact ⟨H1, z, st', d, SH_re e, by rw [hf]; exact C⟩

/-- `SLW` with the state's own `lookahead` / `strstart`: `SLF` with no pending bytes. -/
theorem slw_self {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (W : SLW h i b st.lookahead st.strstart (SH H0 i z b st d)) : SLF h i b (SH H0 i z b st d) ∧ st.pending = 0 := by
  obtain ⟨H1, z1, st1, d1, e, F, hp⟩ := W
  obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
  rw [FS_self, ← e] at F
  exact ⟨F, hp⟩

/-- A store at or after the end of `head` grows the chains by nothing. -/
theorem grow_wrin {d d' : Array UInt8} {ho po w lo hi : Nat} (S : Nat → Prop) (W : WrIn d lo hi d')
    (hl : ho + 131072 ≤ lo) (hph : po + 2 * w ≤ ho) (hw : 0 < w) : Grow d d' ho po w S := by
  intro ss lim I C _
  have hp : ∀ o k, o + 2 * k + 1 < lo → posAt d' o k = posAt d o k := fun o k hk => by
    unfold posAt; rw [W.2 _ (Or.inl (by omega)), W.2 _ (Or.inl (by omega))]
  refine ⟨I, C.c1, fun k hk hne => ?_, fun p hp' hin => ?_⟩
  · rw [hp ho k (by omega)] at hne ⊢; exact C.c2 k hk hne
  · have hm := Nat.mod_lt p hw
    rw [hp po (p % w) (by omega)]; exact C.c3 p hp' hin

end ZlibNgF.Proof.InsertLoopW
