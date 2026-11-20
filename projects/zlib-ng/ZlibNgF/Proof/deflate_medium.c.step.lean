import ZlibNgF.Proof.«insert_string_p.h.sli»
import ZlibNgF.Proof.«deflate_medium_tpl.h.fizzle»
import ZlibNgF.Proof.«deflate_quick.c.match»
import ZlibNgF.Proof.«deflate.c.side»

/-!
# Steps of `deflate_medium` inside the strategy loop (`ZlibNgF`)

`deflate_medium` keeps `lookahead` and `strstart` in the state (no locals), so its loop state is `SLI h i b la ss H`
with `la` / `ss` the state's own fields, except while a match is emitted (`s->lookahead -= len`, the tally,
`s->strstart += len`) and while `deflate_medium_fizzle` looks one match ahead (`strstart` moved by the current
match length, `lookahead` not). The steps here hold for any `la` / `ss`:

* `Sat.and`: two `Sat` facts about one run combine (a run is a function of the heap);
* `insert_knuth_res`: the hash-chain head that `insert_knuth` returns is a `Pos` (below 65536);
* `sli_match_start`: a change of `match_start` (`longest_match_c`) keeps `SLI`;
* `sli_find`: `find_best_match` inside the loop, from the layout of the state (the `LN` of `longest_match_c`, with
  the slack of 512 above `strstart + lookahead` that the fizzle look-ahead uses): `SLI` again, only `match_start`
  changed, and `FindOk`;
* `chain_W4`: the tally's store into `sym_buf`, after `head`, keeps `ChainOk`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumStep
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertSafe
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.InsertStringP

/-- Two `Sat` facts about one run of `m` from `H` hold together. -/
theorem Sat.and {α : Type} {H : Heap} {m : M α} {P Q : α → Heap → Prop} (a : Sat H m P) (c : Sat H m Q) :
    Sat H m (fun r H' => P r H' ∧ Q r H') := by
  obtain ⟨r, H', e, p⟩ := a
  obtain ⟨r2, H2, e2, q⟩ := c
  rw [e] at e2
  injection e2 with e3
  injection e3 with e4 e5
  subst e4 e5
  exact ⟨r, H', e, p, q⟩

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem pv_lt (d : Array UInt8) (o k : Nat) : (pv d o k).toUInt32.toNat < 65536 := by
  have := (pv d o k).toNat_lt
  simpa using this

/-- `insert_knuth(s, window, str)` returns a `Pos`. -/
theorem insert_knuth_res {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str : UInt32)
    (hr : wo + str.toNat + 4 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth (some b) (.ref (.heap b) wo) str) (fun r _ => r.toNat < 65536) := by
  have hw := L.w1
  have hph := L.ph
  have hho := L.hd
  unfold insert_knuth
  refine winRead4 str.toNat hr (fun v => ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (posLoad_eq _ (by have := ZlibNgF.Proof.WinBase.knuth_lt v; omega)) ?_)
  split
  · have hmw := Nat.mod_lt str.toNat (show 0 < st.w_size.toNat by omega)
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    simp only [L.prev]
    refine Sat.bind (Sat.pure ?_)
    have hm : (str &&& W_MASK st).toNat < st.w_size.toNat := by
      have := ZlibNgF.Proof.WinBase.mask_lt str st.w_size hw; unfold W_MASK; omega
    refine Sat.bind (Sat.of_eq (posStore_eq (str &&& W_MASK st).toNat _ (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [L.head]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq _ _ (by rw [wr2_size]; have := ZlibNgF.Proof.WinBase.knuth_lt v; omega)) ?_)
    exact Sat.pure (pv_lt _ _ _)
  · exact Sat.pure (pv_lt _ _ _)

end

/-- A change of `match_start` keeps `SLI` (the invariant does not read it). -/
theorem sli_match_start {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (I : SLI h i b la ss (SH H0 i z b st d)) (ms : UInt32) :
    SLI h i b la ss (SH H0 i z b { st with match_start := ms } d) := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  have e3 := congrArg (fun H => H.streams i) e
  simp only [SH_dstate, SH_bytes, SH_streams] at e1 e2 e3
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj e3
  refine ⟨H1, z, { st with match_start := ms }, d, ?_, ?_⟩
  · rw [← SH_SH H0 i z z b st { st with match_start := ms } d d, e, SH_SH]
  obtain ⟨F, hC⟩ := C
  refine ⟨slf_SH F (fun al _ c => DCore.of_heap (by rw [SH_bytes, SH_bytes]) c) rfl rfl rfl rfl
    (F.st _ (SH_dstate _ _ _ _ _ _)).2.2 (StratKeeps.refl _), fun st2 h2 => ?_⟩
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
  obtain ⟨hp, hs⟩ := hC _ (SH_dstate _ _ _ _ _ _)
  exact ⟨hp, hs⟩

/-- The layout facts of a state under `SLI`: the hash layout, the sizes, and the room of `longest_match_c`. -/
theorem sli_lay {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d)) :
    ∃ wo po ho, HLay b d.size st wo po ho ∧ (∃ k, st.w_size.toNat = 2 ^ k) ∧ 512 ≤ st.w_size.toNat ∧
      st.w_size.toNat ≤ 32768 ∧ ss.toNat + la.toNat ≤ st.window_size.toNat ∧ st.window_size.toNat ≤ 65536 ∧
      wo + st.window_size.toNat ≤ po ∧ wo + 131400 ≤ d.size ∧
      (∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) → ho + 131072 ≤ pbo) ∧
      (∀ sbo, st.sym_buf = .val (.ref (.heap b) sbo) → ho + 131072 ≤ sbo) := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  simp only [SH_dstate, SH_bytes] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain ⟨z2, st2, al, hz2, hb2, hst2, -, c⟩ := C.1.live
  obtain rfl : FS st la ss = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
  obtain ⟨wo, po, ho, pbo, L, hwp, hpb, hhp, hsb⟩ := ZlibNgF.Proof.FillFacts.hlay_of c (SH_bytes _ _ _ _ _ _)
  obtain ⟨k, -, -, hk⟩ := c.wpow
  obtain ⟨w1, w2, hws, -⟩ := c.sizes
  have hlook : ss.toNat + la.toNat ≤ st.window_size.toNat := c.look
  have hws' : st.window_size = W_BUF_SIZE st.w_size := hws
  have w1' : 512 ≤ st.w_size.toNat := w1
  have w2' : st.w_size.toNat ≤ 32768 := w2
  have h65 : st.window_size.toNat ≤ 65536 := by
    rw [hws', DeflateInit.wbuf_toNat _ w2']; unfold DeflateAlloc.dWS; split <;> omega
  have h1k : 1024 ≤ st.window_size.toNat := by
    rw [hws', DeflateInit.wbuf_toNat _ w2']; unfold DeflateAlloc.dWS; split <;> omega
  obtain ⟨d3, -, -, -, pbo3, hd3, -, -, -, hpb3, -, -, -, h4, -⟩ := c.lay
  obtain rfl : d = d3 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd3)
  simp only [dview] at hpb3 h4
  have hpbF : (FS st la ss).pending_buf = .val (.ref (.heap b) pbo) := hpb
  have hpb3' : (FS st la ss).pending_buf = .val (.ref (.heap b) pbo3) := hpb3
  rw [hpbF] at hpb3'
  obtain rfl : pbo = pbo3 := by injection hpb3' with e; injection e
  have h4' : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size := h4
  have hL := L.ph
  have e5 : (FS st la ss).window_size.toNat = st.window_size.toNat := rfl
  have e6 : (FS st la ss).w_size.toNat = st.w_size.toNat := rfl
  have hLw := L.pw
  refine ⟨wo, po, ho, ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩, ⟨k, hk⟩, w1', w2', hlook, h65, hwp,
    by omega, fun p hp => ?_, fun s hs => ?_⟩
  · have hpb' : (FS st la ss).pending_buf = .val (.ref (.heap b) pbo) := hpb
    rw [hpb'] at hp; obtain rfl : pbo = p := by injection hp with e; injection e
    exact hhp
  · have hsb' : (FS st la ss).sym_buf = .val (.ref (.heap b) (pbo + st.lit_bufsize.toNat + 8)) := hsb
    rw [hsb'] at hs; obtain rfl : pbo + st.lit_bufsize.toNat + 8 = s := by injection hs with e; injection e
    omega

open ZlibNgF.Proof.MediumFind in
/-- `find_best_match(s, hash_head, max_dist)` inside the loop (`SLI` with any locals), with `strstart + lookahead`
of the state at most 512 above 65536 and `max_dist = MAX_DIST(s)`: `SLI` again with only `match_start` changed, and
`FindOk`. -/
theorem sli_find {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d)) (hh : UInt32) (md : Int32) (hh6 : hh.toNat < 65536)
    (hmd : md.toInt = (MAX_DIST st).toNat) (hs1 : st.strstart.toNat ≤ 65536) (hl1 : st.lookahead.toNat ≤ 65536)
    (hsl : st.strstart.toNat + st.lookahead.toNat ≤ 65536 + 512) :
    Sat (SH H0 i z b st d) (ZlibNg.DeflateMedium.find_best_match (some b) hh md) (fun m H' => ∃ ms,
      H' = SH H0 i z b { st with match_start := ms } d ∧ SLI h i b la ss H' ∧
      FindOk st.strstart.toNat st.lookahead.toNat (MAX_DIST st).toNat m) := by
  obtain ⟨wo, po, ho, L, -, w1, w2, -, -, -, hbig, -, -⟩ := sli_lay I
  have N : ZlibNgF.Proof.LongestMatch.LN d wo po ho st :=
    ⟨w1, w2, hs1, hl1, hsl, hbig, L.pw, L.hd⟩
  refine Sat.mono (find_best_match_ok L.win L.prev N hh6 hmd) ?_
  rintro m _ ⟨ms, rfl, hf⟩
  exact ⟨ms, rfl, sli_match_start I ms, hf⟩

/-- A store into block `b` at or after the end of `head` keeps `ChainOk`. -/
theorem chain_wr {b : Nat} {d d' : Array UInt8} {st : DeflateState} {lo hi : Nat} (C : ChainOk b d st)
    (hw : 0 < st.w_size.toNat)
    (hl : ∀ ho po, st.head = .val (.ref (.heap b) ho) → st.prev = .val (.ref (.heap b) po) →
      ho + 131072 ≤ lo ∧ po + 2 * st.w_size.toNat ≤ ho)
    (W : ZlibNgF.Proof.DeflateBits.WrIn d lo hi d') : ChainOk b d' st :=
  ZlibNgF.Proof.DeflateSide.ChainOk.of_bytes C hw fun ho po hh hp => by
    obtain ⟨h1, h2⟩ := hl ho po hh hp
    exact ⟨fun j _ hj => W.2 j (Or.inl (by omega)), fun j _ hj => W.2 j (Or.inl (by omega))⟩

end ZlibNgF.Proof.MediumStep
