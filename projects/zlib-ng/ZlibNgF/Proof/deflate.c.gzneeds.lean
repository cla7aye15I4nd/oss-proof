import ZlibNgF.Proof.«deflate.c.gz.io»
import ZlibNgF.Proof.«deflate.c.gz»

/-!
# The deflate side of the gz write layer, proved (`ZlibNgF`)

`deflateGz`: the obligations of the deflate side that the write side uses (`GzWriteNeeds.DeflateGz`), with the
potential `ψ = DeflatePsi.psi` and `G = DeflateBody.G2 = 2^21`:

* `deflateInit2_`, `deflateReset`: `init2_part`, `reset_part` (`Proof/deflate.c.gz.lean`);
* the bound `psi f st ≤ 2^48`: `DeflatePsi.psi_le`;
* `deflate`: `CallOk (psi flush) G2 5` from `DeflateBody.deflate_okP` (`EndOk`: the marker owed when the output is
  full is `markK flush ≤ 5`), `DKeep` (`deflate_keep`), and all input consumed or the output full (`full_part`);
* `deflateParams`: `CallOk (psi Z_BLOCK) G2 0` (its `deflate(strm, Z_BLOCK)` call owes no marker, and the stores of
  the level fields after it do not change what `psi` reads: `tail_psi`), and `DKeep` (`params_keep`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateGz
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateBody ZlibNgF.Proof.DeflateParams ZlibNgF.Proof.DeflatePsi
open ZlibNgF.Proof.DeflateSide (DSide)
open ZlibNgF.Proof.GzWriteNeeds (Adv BufAdv CallOk DKeep)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-- The tail of `deflateParams` (the level fields) keeps the stream record and `psi`. -/
theorem tail_psi {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {level strategy : Int32}
    (hv : DInv h (some i)) (hz : h.streams i = some z) (hb : z.state = some b)
    (hst : h.dstate b = some st) (l0 : 0 ≤ level) (l9 : level ≤ 9) :
    ∃ h', paramsTail (some b) level strategy h = .ok (Z_OK, h') ∧ h'.streams i = h.streams i ∧
      ∀ st', h'.dstate b = some st' → ∀ f, psi f st' = psi f st := by
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, hal, c⟩ := hv
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨d, hd, e⟩ := DeflateSetDict.sh_of hz hst
  obtain ⟨ho, d1, hd1, hh, hho⟩ := c.head
  obtain rfl := Option.some.inj (hd.symm.trans hd1)
  simp only [dview] at hh
  obtain ⟨r, H', run, rfl, st', d', rfl, T⟩ := tail_SH (H := h) (i := i) (z := z) (b := b) (st := st) (d := d)
    level strategy hh hho l0 l9
  rw [e] at run
  refine ⟨_, run, by rw [SH_streams, hz], fun st2 h2 f => ?_⟩
  rw [SH_dstate] at h2
  obtain rfl := Option.some.inj h2
  obtain ⟨x1, x2, a1, a2, a4, a3, lm, ib, rfl, -⟩ := T
  rfl

/-- `EndOk` moves to a heap with the same stream record and, for the state, the same `psi f`. -/
theorem endOk_psi {f : Int32} {P : Nat} {h H H' : Heap} {i b : Nat} (E : EndOk f P h i b H)
    (ez : H'.streams i = H.streams i) (hs : ∃ st, H.dstate b = some st)
    (ep : ∀ st st', H.dstate b = some st → H'.dstate b = some st' → psi f st' = psi f st) :
    EndOk f P h i b H' := fun st' h' => by
  obtain ⟨st, hst⟩ := hs
  rw [aIn_congr ez, aOut_congr ez, ep st st' hst h']
  exact E st hst

/-- **`deflateParams` with the potential at `Z_BLOCK`**: with no `gz_header` registered, `psi Z_BLOCK` of the state at
entry pays for the call (no marker: `markK Z_BLOCK = 0`). -/
theorem params_end (SF : StrategyFacts) {h : Heap} {i : Nat} {level strategy : Int32} (hv : DInv h (some i))
    (hs : DSide h (some i)) (hcg : CrcGlobals h) (hio : DStreamIO h (some i)) :
    Sat h (deflateParams (some i) level strategy) (fun _ h' => ∀ b st0,
      (∃ z, h.streams i = some z ∧ z.state = some b) → h.dstate b = some st0 → st0.gzhead = .val none →
        EndOk Z_BLOCK (psi Z_BLOCK st0) h i b h') := by
  obtain ⟨i', z0, b, st, al, e', L, hal, c⟩ := live hv
  obtain rfl := Option.some.inj e'
  -- the post at a heap with the state's `psi` and counts unchanged from a heap where it holds
  have red : ∀ H, (∀ b' st0, (∃ z, h.streams i = some z ∧ z.state = some b') → h.dstate b' = some st0 →
      st0.gzhead = .val none → EndOk Z_BLOCK (psi Z_BLOCK st0) h i b' H) →
      ∀ H', H'.streams i = H.streams i → (∃ st1, H.dstate b = some st1) →
      (∀ st1 st2, H.dstate b = some st1 → H'.dstate b = some st2 → psi Z_BLOCK st2 = psi Z_BLOCK st1) →
      ∀ b' st0, (∃ z, h.streams i = some z ∧ z.state = some b') → h.dstate b' = some st0 →
        st0.gzhead = .val none → EndOk Z_BLOCK (psi Z_BLOCK st0) h i b' H' := by
    intro H E H' ez hs1 ep b' st0 ⟨z', hz', hb'⟩ h0 hg
    obtain rfl := Option.some.inj (L.hz.symm.trans hz')
    obtain rfl := Option.some.inj (L.hb.symm.trans hb')
    exact endOk_psi (E b st0 ⟨z0, L.hz, L.hb⟩ h0 hg) ez hs1 ep
  have E0 : ∀ b' st0, (∃ z, h.streams i = some z ∧ z.state = some b') → h.dstate b' = some st0 →
      st0.gzhead = .val none → EndOk Z_BLOCK (psi Z_BLOCK st0) h i b' h := by
    intro b' st0 ⟨z', hz', hb'⟩ h0 _
    obtain rfl := Option.some.inj (L.hz.symm.trans hz')
    obtain rfl := Option.some.inj (L.hb.symm.trans hb')
    exact endOk_same h0 rfl rfl
  unfold deflateParams
  rw [params_eq]
  refine Sat.bind (Sat.of_eq L.check ?_)
  refine Sat.bind (Sat.of_eq L.stateOf ?_)
  generalize (if (level == Z_DEFAULT_COMPRESSION) = true then 6 else level) = lv
  by_cases hr : (decide (lv < 0) || decide (lv > 9) || decide (strategy < 0) || decide (strategy > Z_FIXED)) = true
  · rw [ite_t hr]
    exact Sat.pure E0
  rw [ite_f hr]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hr
  obtain ⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩ := hr
  have l0 : 0 ≤ lv := Int32.not_lt.mp hr1
  have l9 : lv ≤ 9 := Int32.not_lt.mp hr2
  have o := c.level
  simp only [dview] at o
  refine Sat.bind (Sat.of_eq (ldDState_app L.dstate) ?_)
  rw [config_eq _ o.1 o.2]
  refine Sat.bind (Sat.pure ?_)
  rw [config_eq _ l0 l9]
  refine Sat.bind (Sat.pure ?_)
  dsimp only
  by_cases hc : ((strategy != st.strategy ||
      configuration_table[st.level.toNatClampNeg]!.func != configuration_table[lv.toNatClampNeg]!.func) &&
      st.last_flush != -2 ||
      Z_NO_FLUSH != Z_NO_FLUSH) = true
  · rw [ite_t hc]
    refine Sat.bind (Sat.of_eq (rank0 _) ?_)
    refine Sat.bind (Sat.of_eq (rank5 _) ?_)
    rw [ite_f (by decide : ¬ ((0 : Int32) > 1))]
    refine Sat.bind (Sat.mono (deflate_okP SF (flush := Z_BLOCK) hv hs hcg hio) ?_)
    rintro r1 h1 ⟨⟨⟨-, si1, hv1, hs1⟩, -⟩, E1⟩
    by_cases he : (r1 == Z_STREAM_ERROR) = true
    · rw [ite_t he]; exact Sat.pure E1
    rw [ite_f he]
    obtain ⟨i1, z1, b1, st1, al1, e', L1, hal1, c1⟩ := live hv1
    obtain rfl : i = i1 := Option.some.inj e'
    have hsi : stateIds h (some i) = [b] := by simp [stateIds, L.hz, L.hb]
    obtain rfl : b = b1 := by
      have : stateIds h1 (some i) = [b1] := by simp [stateIds, L1.hz, L1.hb]
      rw [si1, hsi] at this; exact List.cons.inj this |>.1
    refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.InflateInv.ldStream_app L1.hz) ?_)
    refine Sat.bind (Sat.of_eq (ldDState_app L1.dstate) ?_)
    by_cases ha : (z1.avail_in != 0) = true
    · rw [ite_t ha]; exact Sat.pure E1
    rw [ite_f ha]
    by_cases hbo : (st1.block_open != 0) = true
    · rw [ite_t hbo]; exact Sat.pure E1
    rw [ite_f hbo]
    have ss := DeflateFacts.strstart_toInt32 c1
    have hb1 := c1.bstart
    have hb2 := c1.bs_lo
    have hl1 := c1.look
    obtain ⟨-, w2, wsz, -⟩ := c1.sizes
    simp only [dview] at ss hb1 hb2 hl1 w2 wsz
    have hws : st1.window_size.toNat ≤ 65536 := by
      rw [wsz, DeflateInit.wbuf_toNat _ w2]; unfold DeflateAlloc.dWS; split <;> omega
    rw [ss.1, DeflatePrime.chk_ok _ (by omega) (by omega)]
    refine Sat.bind (Sat.pure ?_)
    by_cases hz : ((Int32.ofInt ((st1.strstart.toNat : Int) - st1.block_start.toInt)).toUInt32 + st1.lookahead
        != 0) = true
    · rw [ite_t hz]; exact Sat.pure E1
    rw [ite_f hz]
    obtain ⟨h', e2, es, ep⟩ := tail_psi (strategy := strategy) hv1 L1.hz L1.hb L1.dstate l0 l9
    exact Sat.of_eq e2 (red h1 E1 h' es ⟨st1, L1.dstate⟩ fun s1 s2 g1 g2 => by
      obtain rfl := Option.some.inj (L1.dstate.symm.trans g1); exact ep s2 g2 Z_BLOCK)
  · rw [ite_f hc]
    obtain ⟨h', e2, es, ep⟩ := tail_psi (strategy := strategy) hv L.hz L.hb L.dstate l0 l9
    exact Sat.of_eq e2 (red h E0 h' es ⟨st, L.dstate⟩ fun s1 s2 g1 g2 => by
      obtain rfl := Option.some.inj (L.dstate.symm.trans g1); exact ep s2 g2 Z_BLOCK)

/-- `CallOk` from `BufAdv` and `EndOk` at the same final heap. -/
theorem callOk_of {f : Int32} {K : Nat} {h h' : Heap} {s : StreamPtr}
    (hK : markK f ≤ K)
    (BA : ∀ z, StreamAt h s z → ∃ z', StreamAt h' s z' ∧ BufAdv z z')
    (E : ∀ i b st0, s = some i → (∃ z, h.streams i = some z ∧ z.state = some b) → h.dstate b = some st0 →
      st0.gzhead = .val none → EndOk f (psi f st0) h i b h')
    (hreg : DRegisteredHeader h s none) : CallOk (psi f) G2 K h h' s := by
  intro z hz
  obtain ⟨z', hz', ba⟩ := BA z hz
  refine ⟨z', hz', ba, fun b st st' ⟨⟨zb, ⟨i, e, hzb⟩, hb⟩, hst⟩ ⟨_, hst'⟩ => ?_⟩
  subst e
  obtain ⟨i1, e1, hz1⟩ := hz
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj (hz1.symm.trans hzb)
  obtain ⟨i2, e2, hz2⟩ := hz'
  obtain rfl := Option.some.inj e2
  obtain ⟨b0, st0, ⟨⟨zb0, ⟨i0, e0, hz0⟩, hb0⟩, hst0⟩, hg⟩ := hreg
  obtain rfl := Option.some.inj e0
  obtain rfl := Option.some.inj (hz1.symm.trans hz0)
  obtain rfl := Option.some.inj (hb.symm.trans hb0)
  obtain rfl := Option.some.inj (hst.symm.trans hst0)
  have q := E i b st rfl ⟨z, hz1, hb⟩ hst hg st' hst'
  rw [aOut_of hz1, aOut_of hz2, aIn_of hz1, aIn_of hz2] at q
  have hk : (if z'.avail_out.toNat = 0 then markK f else 0) ≤ (if z'.avail_out = 0 then K else 0) := by
    by_cases h0 : z'.avail_out = 0
    · have h0' : z'.avail_out.toNat = 0 := by rw [h0]; rfl
      rw [ite_eq_left h0', ite_eq_left h0]; exact hK
    · have h0' : z'.avail_out.toNat ≠ 0 := fun x => h0 (UInt32.toNat_inj.mp (by rw [x]; rfl))
      rw [ite_eq_right h0', ite_eq_right h0]; exact Nat.le_refl _
  omega

/-- **The obligations of the deflate side of the gz write layer** (`GzWriteNeeds.DeflateGz`). -/
theorem deflateGz : GzWriteNeeds.DeflateGz := by
  refine ⟨init2_part, reset_part, fun f st => psi f st, G2, G2_le,
    fun h s b st f hv _ hs => psi_le f hv hs, ?_, ?_⟩
  · intro h h' s flush r hv hs hcg hio hreg e
    refine ⟨callOk_of (markK_le flush) (bufadv_part DeflatePublic.strategyFacts h h' s flush r hv hs hcg hio e)
      ?_ hreg, deflate_keep h h' s flush r e, full_part DeflatePublic.strategyFacts h h' s flush r hv hs hcg hio e⟩
    intro i b st0 rfl hb h0 hg
    obtain ⟨r', h'', e', -, q⟩ := deflate_okP DeflatePublic.strategyFacts (flush := flush) hv hs hcg hio
    have e2 : deflate (some i) flush h = .ok (r, h') := e
    rw [e2] at e'
    injection e' with e3
    injection e3 with e4 e5
    subst e4; subst e5
    exact q b st0 hb h0 hg
  · intro h h' s level strategy r hv hs hcg hreg hio e
    refine ⟨callOk_of (by decide : markK Z_BLOCK ≤ 0)
      (params_bufadv DeflatePublic.strategyFacts h h' s level strategy r hv hs hcg hio e) ?_ hreg,
      params_keep h h' s level strategy r e⟩
    intro i b st0 rfl hb h0 hg
    obtain ⟨r', h'', e', q⟩ := params_end DeflatePublic.strategyFacts (level := level) (strategy := strategy)
      hv hs hcg hio
    have e2 : deflateParams (some i) level strategy h = .ok (r, h') := e
    rw [e2] at e'
    injection e' with e3
    injection e3 with e4 e5
    subst e4; subst e5
    exact q b st0 hb h0 hg

end ZlibNgF.Proof.DeflateGz
