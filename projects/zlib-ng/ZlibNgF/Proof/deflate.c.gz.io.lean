import ZlibNgF.Proof.«public-deflate»
import ZlibNgF.Proof.«deflate.c.gz.keep»

/-!
# `deflate` and `deflateParams` move the buffer fields by what they consume and produce (`ZlibNgF`)

The facts of the gz write side (`GzWriteNeeds.DeflateGz`) and of `compress` (`Compress.DeflateProgress`) about the
buffer fields of a `deflate` call, from `DeflateBody.deflate_okX`:

* `bufadv_part`: `deflate` moves `next_in` / `next_out` by the bytes it consumes and produces and keeps the `state`
  field (`BufAdv`): a call that runs has the input and the output of its stream as tails of those at entry (`Run`); an
  argument check returns with the buffer fields unchanged.
* `full_part`: with a flush other than `Z_FINISH`, a call that does not return `Z_STREAM_ERROR` consumed all its
  input or filled the output (`DIO`).
* `deflate_progress`: the statement of `Compress.DeflateProgress` (a call that returns `Z_OK` under `Z_FINISH`, or
  under `Z_NO_FLUSH` with input, consumed input or produced output; `deflate` returns `Z_BUF_ERROR` on a full
  output at entry, and keeps the registered header).
* `params_bufadv`: `BufAdv` for `deflateParams` (its `deflate(Z_BLOCK)` call, then writes of the state only).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateGz
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateBody ZlibNgF.Proof.DeflateParams
open ZlibNgF.Proof.DeflateSide (DSide)
open ZlibNgF.Proof.GzWriteNeeds (Adv BufAdv)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.DeflateKeep (DR)

/-- The buffer fields of stream `i` move from `h` to `h'` (`BufAdv`). -/
def BA (h h' : Heap) (i : Nat) : Prop := ∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ BufAdv z z'

theorem bufAdv_refl (z : ZStream) : BufAdv z z := by
  refine ⟨UInt32.le_refl _, UInt32.le_refl _, ?_, ?_, rfl⟩
  · cases z.next_in <;> simp [Adv]
  · cases z.next_out <;> simp [Adv]

theorem ba_same {h h' : Heap} {i : Nat} (S : SameBuf h h' i) : BA h h' i := fun z hz => by
  obtain ⟨z', hz', e1, e2, e3, e4, e5⟩ := S z hz
  refine ⟨z', hz', ?_⟩
  have q := bufAdv_refl z
  unfold BufAdv at q ⊢
  rw [e1, e2, e3, e4, e5]; exact q

theorem ba_congr {h h1 h2 : Heap} {i : Nat} (q : BA h h1 i) (e : h2.streams i = h1.streams i) : BA h h2 i :=
  fun z hz => by obtain ⟨z', hz', a⟩ := q z hz; exact ⟨z', by rw [e]; exact hz', a⟩

theorem ba_run {h h' : Heap} {i b : Nat} (R : Run h i b h') : BA h h' i := by
  intro z hz
  obtain ⟨z0, z1, ob, oo, k, h0, h1, e0, e1, ek⟩ := R.out
  obtain rfl := Option.some.inj (hz.symm.trans h0)
  obtain ⟨z0', z2, k', h0', h2, ek', m⟩ := R.inp
  obtain rfl := Option.some.inj (hz.symm.trans h0')
  obtain rfl := Option.some.inj (h1.symm.trans h2)
  obtain ⟨zb, hzb, hb⟩ := R.blk
  obtain ⟨zb0, hzb0, hb0⟩ := R.blk0
  obtain rfl := Option.some.inj (h1.symm.trans hzb)
  obtain rfl := Option.some.inj (hz.symm.trans hzb0)
  refine ⟨z1, h1, UInt32.le_iff_toNat_le.mpr (by omega), UInt32.le_iff_toNat_le.mpr (by omega), ?_, ?_,
    hb.trans hb0.symm⟩
  · have hk : z.avail_in.toNat - z1.avail_in.toNat = k' := by omega
    rw [hk]
    revert m
    cases z.next_in with
    | null => intro m; exact m
    | ref r o => intro m; exact m
  · have hk : z.avail_out.toNat - z1.avail_out.toNat = k := by omega
    rw [e0, hk]; exact e1

/-- The facts of a `deflate` call on its stream: `BufAdv`; with a flush other than `Z_FINISH` and a result other
than `Z_STREAM_ERROR`, all input consumed or the output full; with `Z_OK` under `Z_FINISH`, or under `Z_NO_FLUSH`
with input at entry, input consumed or output produced. -/
theorem deflate_io (SF : StrategyFacts) {h h' : Heap} {s : StreamPtr} {flush r : Int32} (hv : DInv h s)
    (hs : DSide h s) (hcg : CrcGlobals h) (hio : DStreamIO h s) (e : C.run (deflate s flush) h = .ok (r, h')) :
    ∀ z, StreamAt h s z → ∃ z', StreamAt h' s z' ∧ BufAdv z z' ∧
      (flush ≠ Z_FINISH → r ≠ Z_STREAM_ERROR → z'.avail_in = 0 ∨ z'.avail_out = 0) ∧
      (r = Z_OK → (flush = Z_FINISH ∨ (flush = Z_NO_FLUSH ∧ 0 < z.avail_in)) →
        z'.avail_in < z.avail_in ∨ z'.avail_out < z.avail_out) := by
  obtain ⟨i, z0, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨r', h'', e', -, q⟩ := deflate_okX SF (flush := flush) hv hs hcg hio
  have e2 : deflate (some i) flush h = .ok (r, h') := e
  rw [e2] at e'
  injection e' with e3
  injection e3 with e4 e5
  subst e4; subst e5
  rintro z ⟨i', ei, hz⟩
  obtain rfl := Option.some.inj ei
  have u0 : ∀ x : UInt32, x.toNat = 0 → x = 0 := fun x hx => UInt32.toNat_inj.mp (by rw [hx]; rfl)
  rcases q with ⟨b', R, D, hao⟩ | ⟨S, hr⟩
  · obtain ⟨z', hz', ba⟩ := ba_run R z hz
    refine ⟨z', ⟨i, rfl, hz'⟩, ba, fun hf hr => ?_, fun er ef => ?_⟩
    · rcases D.1 hf hr with x | x
      · rw [aIn_of hz'] at x; exact .inl (u0 _ x)
      · rw [aOut_of hz'] at x; exact .inr (u0 _ x)
    · have ef' : flush = Z_FINISH ∨ (flush = Z_NO_FLUSH ∧ aIn h i ≠ 0) := by
        rcases ef with x | ⟨x, y⟩
        · exact .inl x
        · refine .inr ⟨x, ?_⟩
          rw [aIn_of hz]; have := UInt32.lt_iff_toNat_lt.mp y; simp at this; omega
      rcases D.2 er ef' hao with x | x
      · rw [aIn_of hz', aIn_of hz] at x; exact .inl (UInt32.lt_iff_toNat_lt.mpr x)
      · rw [aOut_of hz', aOut_of hz] at x; exact .inr (UInt32.lt_iff_toNat_lt.mpr x)
  · obtain ⟨z', hz', a1, a2, a3, a4, a5⟩ := S z hz
    obtain ⟨-, ba⟩ := ba_same S z hz
    obtain ⟨z'', hz'', ba'⟩ := ba_same S z hz
    obtain rfl := Option.some.inj (hz'.symm.trans hz'')
    refine ⟨z', ⟨i, rfl, hz'⟩, ba', fun hf hr' => ?_, fun er => ?_⟩
    · rcases hr with x | ⟨-, x⟩
      · exact absurd x hr'
      · rw [aOut_of hz] at x; exact .inr (by rw [a4]; exact u0 _ x)
    · rcases hr with x | ⟨x, -⟩ <;> rw [er] at x <;> exact absurd x (by decide)

/-- **`deflate` moves the buffer fields** by the bytes it consumes and produces, and keeps the `state` field
(`BufAdv`; the `io` part of the `deflate` field of `GzWriteNeeds.DeflateGz`), given the strategies. -/
theorem bufadv_part (SF : StrategyFacts) :
    ∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DInv h s → DSide h s → CrcGlobals h → DStreamIO h s →
      C.run (deflate s flush) h = .ok (r, h') → ∀ z, StreamAt h s z → ∃ z', StreamAt h' s z' ∧ BufAdv z z' :=
  fun _ _ _ _ _ hv hs hcg hio e z hz => by
    obtain ⟨z', h1, h2, -⟩ := deflate_io SF hv hs hcg hio e z hz
    exact ⟨z', h1, h2⟩

/-- **`deflate` consumes all input or fills the output** with a flush other than `Z_FINISH`, unless it returns
`Z_STREAM_ERROR` (the `done` part of the `deflate` field of `GzWriteNeeds.DeflateGz`), given the strategies. -/
theorem full_part (SF : StrategyFacts) :
    ∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DInv h s → DSide h s → CrcGlobals h → DStreamIO h s →
      C.run (deflate s flush) h = .ok (r, h') → flush ≠ Z_FINISH → r ≠ Z_STREAM_ERROR →
      ∀ z', StreamAt h' s z' → z'.avail_in = 0 ∨ z'.avail_out = 0 := by
  intro h h' s flush r hv hs hcg hio e hf hr z' hz'
  obtain ⟨i, z0, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨z1, ⟨i1, e1, h1⟩, -, x, -⟩ := deflate_io SF hv hs hcg hio e z0 ⟨i, rfl, L.hz⟩
  obtain ⟨i2, e2, h2⟩ := hz'
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj (h1.symm.trans h2)
  exact x hf hr

/-- **`deflate` moves the buffer fields, keeps "no registered header", and makes progress when it returns `Z_OK`**
under `Z_FINISH` or under `Z_NO_FLUSH` with input: the statement of `Compress.DeflateProgress`. -/
theorem deflate_progress :
    ∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DInv h s → DSide h s → CrcGlobals h → DStreamIO h s →
      C.run (deflate s flush) h = .ok (r, h') → ∀ z, StreamAt h s z →
      ∃ z', StreamAt h' s z' ∧ BufAdv z z' ∧ (DRegisteredHeader h s none → DRegisteredHeader h' s none) ∧
        (r = Z_OK → (flush = Z_FINISH ∨ (flush = Z_NO_FLUSH ∧ 0 < z.avail_in)) →
          z'.avail_in < z.avail_in ∨ z'.avail_out < z.avail_out) := by
  intro h h' s flush r hv hs hcg hio e z hz
  obtain ⟨z', h1, h2, -, h4⟩ := deflate_io DeflatePublic.strategyFacts hv hs hcg hio e z hz
  refine ⟨z', h1, h2, fun hreg => ?_, h4⟩
  have k : DR h h' := (DeflateKeep.K.ZlibNg.Deflate.deflate s flush).run h r h' e
  obtain ⟨b, st, ⟨⟨zb, hzb, hb⟩, hst⟩, hg⟩ := hreg
  obtain ⟨i, rfl, hzi⟩ := hzb
  obtain ⟨i1, ei1, hz1⟩ := h1
  obtain rfl := Option.some.inj ei1
  have hzs := k.zs i
  rw [hz1, hzi] at hzs
  have hb' : z'.state = some b := by
    have : z'.state = zb.state := by simpa using hzs
    rw [this, hb]
  obtain ⟨r2, h3, e3, -, -, hv', -⟩ := DeflateBody.deflate_ok DeflatePublic.strategyFacts h (some i) flush hv hs hcg hio
  have e4 : deflate (some i) flush h = .ok (r, h') := e
  have e5 : deflate (some i) flush h = .ok (r2, h3) := e3
  rw [e4] at e5
  injection e5 with e6
  injection e6 with e7 e8
  subst e7; subst e8
  obtain ⟨i3, z3, b3, st3, al3, e9, L3, -, -⟩ := live hv'
  obtain rfl := Option.some.inj e9
  obtain rfl := Option.some.inj (hz1.symm.trans L3.hz)
  obtain rfl := Option.some.inj (hb'.symm.trans L3.hb)
  obtain ⟨st0, hst0, hg0⟩ := dstate_of_dr k L3.dstate
  obtain rfl := Option.some.inj (hst.symm.trans hst0)
  exact ⟨b, st3, ⟨⟨z', ⟨i, rfl, hz1⟩, hb'⟩, L3.dstate⟩, hg0.symm.trans hg⟩

/-- `BA` for a `deflate` call. -/
theorem deflate_ba (SF : StrategyFacts) {h : Heap} {i : Nat} {flush : Int32} (hv : DInv h (some i))
    (hs : DSide h (some i)) (hcg : CrcGlobals h) (hio : DStreamIO h (some i)) :
    Sat h (deflate (some i) flush) (fun _ h' => DPost h h' i ∧ BA h h' i) :=
  Sat.mono (deflate_okX SF hv hs hcg hio) fun _ _ ⟨p, q⟩ => ⟨p, by
    rcases q with ⟨b, R, -, -⟩ | ⟨S, -⟩
    · exact ba_run R
    · exact ba_same S⟩

/-- **`deflateParams` moves the buffer fields** by the bytes it consumes and produces, and keeps the `state` field
(`BufAdv`; the `io` part of the `deflateParams` field of `GzWriteNeeds.DeflateGz`), given the strategies: its
`deflate(Z_BLOCK)` call, then writes of the state only. -/
theorem params_bufadv (SF : StrategyFacts) :
    ∀ (h h' : Heap) (s : StreamPtr) (level strategy r : Int32), DInv h s → DSide h s → CrcGlobals h →
      DStreamIO h s → C.run (deflateParams s level strategy) h = .ok (r, h') →
      ∀ z, StreamAt h s z → ∃ z', StreamAt h' s z' ∧ BufAdv z z' := by
  intro h h' s level strategy r hv hs hcg hio e z hz
  obtain ⟨i, z0, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨i', ei, hzi⟩ := hz
  obtain rfl := Option.some.inj ei
  suffices q : Sat h (deflateParams (some i) level strategy) (fun _ h' => BA h h' i) by
    obtain ⟨r', h'', e', q⟩ := q
    have e2 : deflateParams (some i) level strategy h = .ok (r, h') := e
    rw [e2] at e'
    injection e' with e3
    injection e3 with e4 e5
    subst e4; subst e5
    obtain ⟨z', hz', a⟩ := q z hzi
    exact ⟨z', ⟨i, rfl, hz'⟩, a⟩
  have ba0 : BA h h i := fun z hz => ⟨z, hz, bufAdv_refl z⟩
  unfold deflateParams
  rw [params_eq]
  refine Sat.bind (Sat.of_eq L.check ?_)
  refine Sat.bind (Sat.of_eq L.stateOf ?_)
  generalize (if (level == Z_DEFAULT_COMPRESSION) = true then 6 else level) = lv
  have S := hs b st ⟨i, z0, rfl, L.hz, L.hb, L.dstate⟩
  by_cases hr : (decide (lv < 0) || decide (lv > 9) || decide (strategy < 0) || decide (strategy > Z_FIXED)) = true
  · rw [ite_t hr]
    exact Sat.pure ba0
  rw [ite_f hr]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hr
  obtain ⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩ := hr
  have l0 : 0 ≤ lv := Int32.not_lt.mp hr1
  have l9 : lv ≤ 9 := Int32.not_lt.mp hr2
  have s0 : 0 ≤ strategy := Int32.not_lt.mp hr3
  have s4 : strategy ≤ 4 := Int32.not_lt.mp hr4
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
    refine Sat.bind (Sat.mono (deflate_ba SF (flush := Z_BLOCK) hv hs hcg hio) ?_)
    rintro r1 h1 ⟨⟨-, si1, hv1, hs1⟩, ba1⟩
    by_cases he : (r1 == Z_STREAM_ERROR) = true
    · rw [ite_t he]; exact Sat.pure ba1
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
    · rw [ite_t ha]; exact Sat.pure ba1
    rw [ite_f ha]
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
    · rw [ite_t hz]; exact Sat.pure ba1
    rw [ite_f hz]
    have hz' : (Int32.ofInt ((st1.strstart.toNat : Int) - st1.block_start.toInt)).toUInt32 + st1.lookahead = 0 := by
      simpa using hz
    obtain ⟨q1, q2⟩ := sum_zero _ (by omega) (by omega) _ (by omega) hz'
    obtain ⟨h', e2, -, -, -, es⟩ := tail_ok hv1 hs1 L1.hz L1.hb L1.dstate l0 l9 s0 s4 (Or.inr ⟨q2, by omega⟩)
    exact Sat.of_eq e2 (ba_congr ba1 es)
  · rw [ite_f hc]
    have sw : SwitchOk st lv strategy := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, not_or, not_and, Classical.not_not] at hc
      obtain ⟨hc1, -⟩ := hc
      by_cases hl : st.last_flush = -2
      · obtain ⟨-, -, hf⟩ := S.2.2.2.2.1
        obtain ⟨e1, e2⟩ := hf hl
        exact Or.inr ⟨e2, e1⟩
      · have := fun x => hl (hc1 x)
        refine Or.inl ⟨?_, ?_⟩
        · exact Classical.byContradiction fun hn => this (Or.inl (Ne.symm hn))
        · exact Classical.byContradiction fun hn => this (Or.inr hn)
    obtain ⟨h', e2, -, -, -, es⟩ := tail_ok hv hs L.hz L.hb L.dstate l0 l9 s0 s4 sw
    exact Sat.of_eq e2 (ba_congr ba0 es)

end ZlibNgF.Proof.DeflateGz
