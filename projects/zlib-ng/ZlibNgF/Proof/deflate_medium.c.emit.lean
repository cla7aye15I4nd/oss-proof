import ZlibNgF.Proof.«deflate_medium.c.base»

/-!
# The emission of a match in `deflate_medium` (`ZlibNgF`)

A match of length `L` (1 is a literal) is emitted by `s->lookahead -= L`, the tally, `s->strstart += L`
(`deflate_medium_tpl.h:269-276`, and `:303-308` in the continuation loop). Between the tally and `FLUSH_BLOCK` the
state is `PF bf` (the frame with no pending bytes, the chains, and room for one more symbol unless `bf`, the
accumulated `bflush`), and `PE bf` adds `sym_next ≤ sym_end` (one more tally may follow: the first continuation of
a match of length `STD_MAX_MATCH`). `A` bounds `2 * avail_in + lookahead`.

* `pe_tally_lit` / `pe_tally_dist`: the tally after `s->lookahead -= L`, with the state after `s->strstart += L`;
* `pf_flush`: `FLUSH_BLOCK(s, window, 0)` from `PF`;
* `pe_ins`: an insertion that grows the chains below `strstart + lookahead` keeps `PE`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.StrategyChain
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP

/-- The state between a tally and `FLUSH_BLOCK` (see the module comment). -/
def PF (h : Heap) (i b : Nat) (W : UInt32) (A : Nat) (bf : Bool) (H : Heap) : Prop :=
  ∃ H0 z st d, H = SH H0 i z b st d ∧ SLF h i b H ∧ st.pending = 0 ∧ ChainOk b d st ∧
    (bf = false → st.sym_next < st.sym_end) ∧ 2 * avIn H i + st.lookahead.toNat ≤ A ∧ st.w_size = W

/-- `PF` with room for one more tally. -/
def PE (h : Heap) (i b : Nat) (W : UInt32) (A : Nat) (bf : Bool) (H : Heap) : Prop := PF h i b W A bf H ∧ SymLe b H

/-- The levels of `deflate_medium*`. -/
def MedLv (h : Heap) (b : Nat) : Prop := ∀ st0, h.dstate b = some st0 → 3 ≤ st0.level ∧ st0.level ≤ 6

theorem slf_lv {h H : Heap} {i b : Nat} (F : SLF h i b H) (hl : MedLv h b) {st : DeflateState}
    (hst : H.dstate b = some st) : chainLim st = st.strstart.toNat + st.lookahead.toNat := by
  obtain ⟨st0, h0, hk⟩ := F.keeps
  obtain ⟨-, -, -, -, e, -⟩ := hk st hst
  have := hl st0 h0
  unfold chainLim; rw [e]; simp only [this.1, this.2, and_self, ite_true]

/-- `StratPost` from `SLF` and the exit facts at the levels of `deflate_medium*` (any strategy, `Z_FIXED`
included: the level is not 1, and `LazyOk` is kept by `StratKeeps` outside the levels of `deflate_slow`). -/
theorem slf_postM {h H : Heap} {i b : Nat} (F : SLF h i b H) (flush : Int32) (bs : BlockState) (hl : MedLv h b)
    (hs : ∀ st, H.dstate b = some st → ExitOk flush bs st) : StratPost h (some i) flush bs H := by
  refine slf_postL F flush bs (fun st0 h0 e1 => absurd (e1 ▸ (hl st0 h0).1 : (3 : Int32) ≤ 1) (by decide))
    (fun st0 h0 L st hst => ?_) hs
  obtain ⟨st1, h1, hk⟩ := F.keeps
  obtain rfl : st0 = st1 := Option.some.inj (h0.symm.trans h1)
  have hT : ¬ TableAt 7 9 st0 := fun ht => absurd (Int32.le_trans ht.1 (hl st0 h0).2) (by decide)
  obtain ⟨L', hm⟩ := (hk st hst).lazy L hT
  exact ⟨L', fun _ => hm⟩

/-- `PE` from the loop state. -/
theorem pe_of_mg {h H : Heap} {i b : Nat} (G : MG h i b H) {st : DeflateState} (hst : H.dstate b = some st) :
    PE h i b st.w_size (2 * avIn H i + st.lookahead.toNat) false H := by
  obtain ⟨C, Ch⟩ := G
  obtain ⟨z, st1, -, hz, -, hst1, -, -⟩ := C.1.live
  obtain rfl := Option.some.inj (hst1.symm.trans hst)
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  have e := ZlibNgF.Proof.DeflateReset.SH_self hz (dstates_of_dstate hst hd) hd
  obtain ⟨hp, hs⟩ := C.2 st1 hst
  refine ⟨⟨H, z, st1, d, e.symm, C.1, hp, Ch st1 d hst hd, fun _ => hs, Nat.le_refl _, rfl⟩, fun st2 h2 => ?_⟩
  obtain rfl := Option.some.inj (hst.symm.trans h2)
  exact UInt32.le_of_lt hs

/-- The loop state from `PE false`. -/
theorem mg_of_pf {h H : Heap} {i b A : Nat} {W : UInt32} (P : PF h i b W A false H) : MG h i b H := by
  obtain ⟨H0, z, st, d, rfl, F, hp, Ch, hs, -, -⟩ := P
  exact ⟨⟨F, fun st2 h2 => by
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); exact ⟨hp, hs rfl⟩⟩,
    chainAll_SH.mpr Ch⟩

theorem pf_mono {h H : Heap} {i b A A' : Nat} {W : UInt32} {bf : Bool} (P : PF h i b W A bf H) (hA : A ≤ A') : PF h i b W A' bf H := by
  obtain ⟨H0, z, st, d, e, F, hp, Ch, hs, ha, hw⟩ := P
  exact ⟨H0, z, st, d, e, F, hp, Ch, hs, by omega, hw⟩

/-- The state of a `PE` heap. -/
theorem pe_st {h H0 : Heap} {i b A : Nat} {W : UInt32} {z : ZStream} {st : DeflateState} {d : Array UInt8} {bf : Bool}
    (P : PE h i b W A bf (SH H0 i z b st d)) :
    SLF h i b (SH H0 i z b st d) ∧ st.pending = 0 ∧ st.sym_next ≤ st.sym_end ∧ ChainOk b d st ∧
      (bf = false → st.sym_next < st.sym_end) ∧ 2 * z.avail_in.toNat + st.lookahead.toNat ≤ A ∧ st.w_size = W := by
  obtain ⟨⟨H1, z1, st1, d1, e1, F, hp, Ch, hs, hA, hW⟩, hSL⟩ := P
  have e2 := congrArg (fun H => H.dstate b) e1
  have e3 := congrArg (fun H => H.bytes b) e1
  simp only [SH_dstate, SH_bytes] at e2 e3
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj e3
  rw [avIn_SH] at hA
  exact ⟨F, hp, hSL _ (SH_dstate _ _ _ _ _ _), Ch, hs, hA, hW⟩

open ZlibNgF.Proof.MediumStep in
/-- The state after a tally and `s->strstart += L`, for a record `st2` that differs from `st` in `lookahead`
(lowered by `L`), the symbols, the trees and the bytes. -/
theorem pe_post {h H0 : Heap} {i b A : Nat} {W : UInt32} {z : ZStream} {st st2 : DeflateState} {d d' : Array UInt8}
    {bf r : Bool} (P : PE h i b W A bf (SH H0 i z b st d)) (hl : MedLv h b) (L : UInt32)
    (hLa : L.toNat ≤ st.lookahead.toNat)
    (hla2 : st2.lookahead = st.lookahead - L) (hss2 : st2.strstart = st.strstart)
    (hk : st2.level = st.level ∧ st2.strategy = st.strategy ∧ st2.head = st.head ∧ st2.prev = st.prev ∧
      st2.w_size = st.w_size ∧ st2.sym_buf = st.sym_buf)
    (Wl : SLW h i b (st.lookahead - L) (st.strstart + L) (SH H0 i z b st2 d'))
    (Wr : SymWr b (SH H0 i z b { st with lookahead := st.lookahead - L } d) (SH H0 i z b st2 d'))
    (hle : st.sym_next < st.sym_end → SymLe b (SH H0 i z b st2 d'))
    (hsli : st.sym_next < st.sym_end → r = false →
      SLI h i b (st.lookahead - L) (st.strstart + L) (SH H0 i z b st2 d')) :
    PF h i b W (A - L.toNat) (bf || r) (SH H0 i z b { st2 with strstart := st2.strstart + L } d') ∧
      (bf = false → SymLe b (SH H0 i z b { st2 with strstart := st2.strstart + L } d')) := by
  obtain ⟨F, hp, -, Ch, hs, hA, hW⟩ := pe_st P
  obtain ⟨wo, po, ho, Ly, -, w1, w2, hlook, h65, -, -, -, hsb⟩ := slf_lay F
  have hcl := slf_lv F hl (SH_dstate _ _ _ _ _ _)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk
  have hLa' : (st.lookahead - L).toNat = st.lookahead.toNat - L.toNat := UInt32.toNat_sub_of_le _ _
    (UInt32.le_iff_toNat_le.mpr hLa)
  have hss' : (st.strstart + L).toNat = st.strstart.toNat + L.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have W3 : SLW h i b st2.lookahead (st2.strstart + L) (SH H0 i z b { st2 with strstart := st2.strstart + L } d') :=
    (fun la ss (e1 : la = st2.lookahead) (e2 : ss = st2.strstart + L) (w : SLW h i b la ss _) => by
      subst e1 e2; exact w) _ _ hla2.symm (by rw [hss2]) (slw_congr (st' := { st2 with strstart := st2.strstart + L }) Wl rfl)
  obtain ⟨F3, hp3⟩ := slw_slf (st := { st2 with strstart := st2.strstart + L }) W3
  refine ⟨⟨H0, z, _, d', rfl, F3, hp3, ?_, ?_, ?_, k5.trans hW⟩, ?_⟩
  · obtain ⟨sbo, hi, da, db, hda, hdb, hsbo, Wi⟩ := Wr
    have e1 : d = da := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hda)
    have e2 : d' = db := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hdb)
    subst e1 e2
    have hsbo' : st.sym_buf = .val (.ref (.heap b) sbo) := hsbo { st with lookahead := st.lookahead - L } (SH_dstate _ _ _ _ _ _)
    have C1 : ChainOk b d' st := chain_wr Ch (by omega) (fun ho' po' hh hp' => by
      rw [Ly.head] at hh; rw [Ly.prev] at hp'
      obtain rfl : ho = ho' := by injection hh with e; injection e
      obtain rfl : po = po' := by injection hp' with e; injection e
      exact ⟨hsb sbo hsbo', Ly.ph⟩) Wi
    refine chain_adv C1 k1 k2 k3 k4 k5 (by show _ ≤ (st2.strstart + L).toNat; rw [hss2]; omega) ?_
    rw [hcl]
    obtain ⟨st0, h0, hk⟩ := F.keeps
    obtain ⟨-, -, -, -, ev, -⟩ := hk st (SH_dstate _ _ _ _ _ _)
    have hlv3 : 3 ≤ st2.level ∧ st2.level ≤ 6 := by rw [k1, ev]; exact hl st0 h0
    show _ ≤ (st2.strstart + L).toNat + if 3 ≤ st2.level ∧ st2.level ≤ 6 then st2.lookahead.toNat else 0
    simp only [hlv3.1, hlv3.2, and_self, ite_true]; rw [hla2, hss2]
    omega
  · intro e
    simp only [Bool.or_eq_false_iff] at e
    obtain ⟨rfl, rfl⟩ := e
    have I := hsli (hs rfl) rfl
    have I3 : SLI h i b st2.lookahead (st2.strstart + L) (SH H0 i z b { st2 with strstart := st2.strstart + L } d') :=
      (fun la ss (e1 : la = st2.lookahead) (e2 : ss = st2.strstart + L) (w : SLI h i b la ss _) => by
        subst e1 e2; exact w) _ _ hla2.symm (by rw [hss2]) (sli_congr (st' := { st2 with strstart := st2.strstart + L }) I rfl)
    exact ((sli_slc (st := { st2 with strstart := st2.strstart + L }) I3).2 _ (SH_dstate _ _ _ _ _ _)).2
  · rw [avIn_SH]
    show 2 * z.avail_in.toNat + st2.lookahead.toNat ≤ A - L.toNat
    rw [hla2, hLa']; omega
  · intro e
    subst e
    have := hle (hs rfl)
    intro st3 h3
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h3)
    exact this st2 (SH_dstate _ _ _ _ _ _)

/-- The tally after `s->lookahead -= L`, with the facts of `slf_tally_*` (`T1`) and the shape of the heap after
(`T2`): the state after `s->strstart += L` is `PF (bf || r)` with `A - L`, and `SymLe` when `bf` is false. -/
theorem pe_tally_core {h H0 : Heap} {i b A : Nat} {W : UInt32} {z : ZStream} {st : DeflateState} {d : Array UInt8} {bf : Bool}
    (P : PE h i b W A bf (SH H0 i z b st d)) (hl : MedLv h b) (L : UInt32)
    (hLa : L.toNat ≤ st.lookahead.toNat) (t : M Bool)
    (T1 : Sat (SH H0 i z b { st with lookahead := st.lookahead - L } d) t (fun r H' =>
      avIn H' i = avIn (SH H0 i z b { st with lookahead := st.lookahead - L } d) i ∧
      SLW h i b (st.lookahead - L) (st.strstart + L) H' ∧
      SymWr b (SH H0 i z b { st with lookahead := st.lookahead - L } d) H' ∧
      (st.sym_next < st.sym_end → SymLe b H') ∧
      (st.sym_next < st.sym_end → r = false → SLI h i b (st.lookahead - L) (st.strstart + L) H')))
    (T2 : Sat (SH H0 i z b { st with lookahead := st.lookahead - L } d) t (fun _ H' => ∃ sn lt dt d',
      H' = SH H0 i z b { st with lookahead := st.lookahead - L, sym_next := sn, dyn_ltree := lt, dyn_dtree := dt } d')) :
    Sat (SH H0 i z b { st with lookahead := st.lookahead - L } d) t (fun r H2 => ∃ st2 d2,
      H2 = SH H0 i z b st2 d2 ∧ st2.lookahead = st.lookahead - L ∧ st2.strstart = st.strstart ∧
      PF h i b W (A - L.toNat) (bf || r) (SH H0 i z b { st2 with strstart := st2.strstart + L } d2) ∧
      (bf = false → SymLe b (SH H0 i z b { st2 with strstart := st2.strstart + L } d2))) := by
  refine Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and T1 T2) ?_
  rintro r H' ⟨⟨-, Wl, Wr, hle, hsli⟩, sn, lt, dt, d', rfl⟩
  exact ⟨_, d', rfl, rfl, rfl, pe_post P hl L hLa rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ Wl Wr hle hsli⟩

open ZlibNgF.Proof.Tally (W4) in
/-- `zng_tr_tally_lit(s, c)` after `s->lookahead -= 1`. -/
theorem pe_tally_lit {h H0 : Heap} {i b A : Nat} {W : UInt32} {z : ZStream} {st : DeflateState} {d : Array UInt8} {bf : Bool}
    (P : PE h i b W A bf (SH H0 i z b st d)) (hl : MedLv h b) (hL : 1 ≤ st.lookahead.toNat) (c : UInt8) :
    Sat (SH H0 i z b { st with lookahead := st.lookahead - 1 } d) (zng_tr_tally_lit (some b) c) (fun r H2 => ∃ st2 d2,
      H2 = SH H0 i z b st2 d2 ∧ st2.lookahead = st.lookahead - 1 ∧ st2.strstart = st.strstart ∧
      PF h i b W (A - (1 : UInt32).toNat) (bf || r) (SH H0 i z b { st2 with strstart := st2.strstart + 1 } d2) ∧
      (bf = false → SymLe b (SH H0 i z b { st2 with strstart := st2.strstart + 1 } d2))) := by
  obtain ⟨F, hp, hle, -⟩ := pe_st P
  have F' : SLF h i b (SH H0 i z b (FS { st with lookahead := st.lookahead - 1 } st.lookahead st.strstart) d) := F
  refine pe_tally_core P hl 1 hL _ ?_ ?_
  · exact Sat.mono (slf_tally_lit F' hp hle hL c) fun _ _ q => ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2⟩
  · exact Sat.mono (tally_lit_shape F' hle c) fun _ _ ⟨sn, lt, d', e⟩ => ⟨sn, lt, st.dyn_dtree, d', e⟩

/-- `zng_tr_tally_dist(s, dist, L - STD_MIN_MATCH)` after `s->lookahead -= L`. -/
theorem pe_tally_dist {h H0 : Heap} {i b A : Nat} {W : UInt32} {z : ZStream} {st : DeflateState} {d : Array UInt8} {bf : Bool}
    (P : PE h i b W A bf (SH H0 i z b st d)) (hl : MedLv h b) (dist len L : UInt32) (hlen : len.toNat < 256)
    (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) (hn1 : 1 ≤ L.toNat) (hn : L.toNat ≤ 258)
    (hL : L.toNat ≤ st.lookahead.toNat) :
    Sat (SH H0 i z b { st with lookahead := st.lookahead - L } d) (zng_tr_tally_dist (some b) dist len)
      (fun r H2 => ∃ st2 d2,
      H2 = SH H0 i z b st2 d2 ∧ st2.lookahead = st.lookahead - L ∧ st2.strstart = st.strstart ∧
      PF h i b W (A - L.toNat) (bf || r) (SH H0 i z b { st2 with strstart := st2.strstart + L } d2) ∧
      (bf = false → SymLe b (SH H0 i z b { st2 with strstart := st2.strstart + L } d2))) := by
  obtain ⟨F, hp, hle, -⟩ := pe_st P
  have F' : SLF h i b (SH H0 i z b (FS { st with lookahead := st.lookahead - L } st.lookahead st.strstart) d) := F
  refine pe_tally_core P hl L hL _ ?_ ?_
  · exact Sat.mono (slf_tally_dist F' hp hle dist len L hlen hd1 hd2 hn1 hn hL) fun _ _ q =>
      ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2⟩
  · exact Sat.mono (tally_dist_shape F' hle dist len hlen hd1 hd2) fun _ _ ⟨sn, lt, dt, d', e⟩ => ⟨sn, lt, dt, d', e⟩

/-- An `SLF` heap is an `SH` heap of its own record and bytes. -/
theorem slf_sh {h H : Heap} {i b : Nat} (F : SLF h i b H) :
    ∃ z st d, H = SH H i z b st d ∧ H.dstate b = some st := by
  obtain ⟨z, st, -, hz, -, hst, -, -⟩ := F.live
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  exact ⟨z, st, d, (ZlibNgF.Proof.DeflateReset.SH_self hz (dstates_of_dstate hst hd) hd).symm, hst⟩

/-- `FLUSH_BLOCK(s, window, 0)` from `PF`: `PE false` with `lookahead` and `strstart` kept, or the return of
`need_more` with `StratPost` and the chains. -/
theorem pf_flush (T : TreesFacts) {h H : Heap} {i b A wo : Nat} {W : UInt32} {bf : Bool} (P : PF h i b W A bf H) (flush : Int32)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (hl : MedLv h b) :
    Sat H (FLUSH_BLOCK (some b) (.ref (.heap b) wo) 0) (fun r H2 =>
      (r = none → PE h i b W A false H2 ∧ ∀ st2, H2.dstate b = some st2 → ∃ st, H.dstate b = some st ∧
        st2.lookahead = st.lookahead ∧ st2.strstart = st.strstart) ∧
      (∀ r', r = some r' → r' = .need_more ∧ StratPost h (some i) flush .need_more H2 ∧ ChainAll b H2)) := by
  obtain ⟨H0, z, st, d, rfl, F, hp, Ch, -, hA, hW⟩ := P
  obtain ⟨st0, h0, hw⟩ := F.win
  refine Sat.mono (slf_flush_mg T 0 (by decide) (by decide) F (fun st' h' => ?_) (chainAll_SH.mpr Ch)) ?_
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h')
    exact ⟨hp, (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)⟩
  rintro r H2 ⟨a1, F2, Ch2, KW, hs, hnone, hsome⟩
  refine ⟨fun hr => ?_, fun r' hr => ?_⟩
  · obtain ⟨z2, st2, d2, e2, hst2⟩ := slf_sh F2
    obtain ⟨hs0, hs1, st1, h1, hl1, hs2, -⟩ := hs st2 hst2
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h1)
    refine ⟨⟨⟨H2, z2, st2, d2, e2, F2, hnone hr st2 hst2, ?_, fun _ => hs1, ?_,
      (KW _ _ (SH_dstate _ _ _ _ _ _) hst2).trans hW⟩, fun st3 h3 => ?_⟩,
      fun st3 h3 => ?_⟩
    · exact Ch2 st2 d2 hst2 (by rw [e2]; exact SH_bytes _ _ _ _ _ _)
    · rw [a1, hl1]; exact hA
    · obtain rfl := Option.some.inj (hst2.symm.trans h3); rw [hs0]; exact UInt32.zero_le
    · obtain rfl := Option.some.inj (hst2.symm.trans h3); exact ⟨st, SH_dstate _ _ _ _ _ _, hl1, hs2⟩
  · have e := hsome (by rw [hr]; simp)
    rw [hr] at e
    have e' : r' = .need_more := by simpa using e
    subst e'
    refine ⟨rfl, slf_postM F2 flush _ hl fun st2 h2 => ?_, Ch2⟩
    obtain ⟨hs0, hs1, -⟩ := hs st2 h2
    refine ⟨hs1, fun e => ?_, fun _ => hs0, fun e => ?_, fun e => ?_⟩
    · rcases e with e | e <;> cases e
    · rcases e with e | e <;> cases e
    · cases e

open ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop in
/-- An insertion that keeps the state record and grows the chains by positions below `strstart + lookahead` keeps
`PE`. -/
theorem pe_ins {h H0 : Heap} {i b A : Nat} {W : UInt32} {z : ZStream} {st : DeflateState} {d d' : Array UInt8} {bf : Bool}
    (P : PE h i b W A bf (SH H0 i z b st d)) (hl : MedLv h b) (F' : SLF h i b (SH H0 i z b st d'))
    {S : Nat → Prop} (g : GrowSt b st d d' S)
    (hS : ∀ q, S q → q ≠ 0 → q < st.strstart.toNat + st.lookahead.toNat) : PE h i b W A bf (SH H0 i z b st d') := by
  obtain ⟨F, hp, hle, Ch, hs, hA, hW⟩ := pe_st P
  have hcl := slf_lv F' hl (SH_dstate _ _ _ _ _ _)
  refine ⟨⟨H0, z, st, d', rfl, F', hp, ChainOk.grow Ch g rfl rfl rfl rfl rfl (Nat.le_refl _) (Nat.le_refl _)
    (by rw [hcl]; exact hS), hs, by rw [avIn_SH]; exact hA, hW⟩, fun st2 h2 => ?_⟩
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
  exact hle

end ZlibNgF.Proof.MediumLoop
