import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Proof.«deflate.c.prime»

/-!
# The bit writer and the static-tree emitters of `trees_emit.h` (`ZlibNgF`)

`send_bits` on `SH` heaps: at most one 8-byte store at `pending_buf + pending`, with the bits counted
(`pending * 8 + bi_valid` grows by the length sent). On top of it the emitters of `deflate_quick` with the static
trees (`zng_tr_emit_lit`, `zng_tr_emit_dist`, `zng_tr_emit_end_block`), `zng_tr_emit_tree`, `zng_tr_emit_align`
(`bi_windup`), and from `trees.c` `zng_tr_align` and `zng_tr_stored_block`.

Each emitter is first proved on `SH` heaps (`EPost`: the bytes change only after the pending bytes, the bits are
counted, the state changes only in the fields of `EmitKeeps`), then lifted to `EmitOk` by `emit_of`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesEmitP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateBits ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## The emitter contract -/

/-- What the emitters use of a working state. -/
structure WCtx (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo : Nat) :
    Prop where
  hpb : st.pending_buf = .val (.ref (.heap b) pbo)
  pad : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size
  lb : st.lit_bufsize.toNat ≤ 32768
  v0 : 0 ≤ st.bi_valid.toInt
  v64 : st.bi_valid.toInt < 64
  /-- the window positions below `strstart` lie before `pending_buf` -/
  win : ∀ wo, st.window = .val (.ref (.heap b) wo) → wo + st.strstart.toNat ≤ pbo

/-- What an emitter leaves on an `SH` heap: a new state that differs from `st` in the view only in `pending` (and
`bi_valid`) and otherwise only in the fields of `EmitKeeps`, the bytes changed only in `[pbo + pending, pbo +
pending')`, the pending bytes and the bits left at most `grow` bytes more, at most 63 bits. -/
def EPost (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo grow : Nat)
    (H' : Heap) : Prop :=
  ∃ st' d', H' = SH h i z b st' d' ∧ WrIn d (pbo + st.pending.toNat) (pbo + st'.pending.toNat) d' ∧
    dview { st' with bi_valid := 0 } = dview { st with bi_valid := 0, pending := st'.pending } ∧
    EmitKeeps st st' ∧ st.pending.toNat ≤ st'.pending.toNat ∧
    st'.pending.toNat * 8 + st'.bi_valid.toInt.toNat ≤ st.pending.toNat * 8 + 8 * grow ∧
    0 ≤ st'.bi_valid.toInt ∧ st'.bi_valid.toInt < 64

theorem pend_inj {b pbo pbo1 : Nat} {p : Ival BPtr} (h1 : p = .val (.ref (.heap b) pbo))
    (h2 : p = .val (.ref (.heap b) pbo1)) : pbo = pbo1 := by
  rw [h1] at h2; injection h2 with e; injection e

/-- The heap that an emitter `m` leaves on stream `s` (block `b`) from the working state: the same heap with only the
state record and the bytes of block `b` replaced (`SH`), the stream record unchanged. -/
def EmitShape (s : StreamPtr) (b : Nat) (pre : DeflateState → Prop) (room : DeflateState → Nat) (m : M Unit) :
    Prop :=
  ∀ (h : Heap) (st : DeflateState), DWork h s → DStateIs h s b st → pre st →
    PendRoom b st (room st) (4 * st.lit_bufsize.toNat + 9) →
    (st.sym_next ≠ 0 → PendRoom b st (room st) (st.lit_bufsize.toNat + 8)) →
    ∀ h', C.run m h = .ok ((), h') → ∃ i z st' d', s = some i ∧ h.streams i = some z ∧ h' = SH h i z b st' d'

/-- An emitter proved on `SH` heaps (the hypothesis of `emit_of`) leaves an `SH` heap. -/
theorem shape_of {s : StreamPtr} {b : Nat} {pre : DeflateState → Prop} {room grow : DeflateState → Nat} {m : M Unit}
    (H : ∀ h i z st d pbo, WCtx h i z b st d pbo → pre st →
      st.pending.toNat + room st ≤ 4 * st.lit_bufsize.toNat + 9 →
      Sat (SH h i z b st d) m (fun _ H' => EPost h i z b st d pbo (grow st) H')) :
    EmitShape s b pre room m := by
  intro h st hw hs hpre hr1 hr2 h' hrun
  obtain ⟨i, z, b', st0, al, rfl, hz, hb, hst, hal, b0, b64, c, -, -⟩ := hw
  obtain ⟨i1, z1, e1, hz1, hb1, hst1⟩ := hs
  obtain rfl := Option.some.inj e1
  rw [hz] at hz1; obtain rfl := Option.some.inj hz1
  rw [hb] at hb1; obtain rfl := (Option.some.inj hb1).symm
  rw [hst] at hst1; obtain rfl := (Option.some.inj hst1).symm
  obtain ⟨pbo1, poo1, hpb1, hpo1, hroom⟩ := hr1
  obtain ⟨-, -, -, -, l2, -, -⟩ := c.sizes
  obtain ⟨d, wo, po, ho, pbo, hd, hw, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  simp only [dview] at l2 hw hp hh hpb h1 h2 h3 h4 hsb hpo hpoo hpe
  obtain rfl := pend_inj hpb hpb1
  obtain rfl := pend_inj hpo hpo1
  have hst' : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  have v0 : 0 ≤ st.bi_valid.toInt := by have := Int32.le_iff_toInt_le.mp b0; simpa using this
  have v64 : st.bi_valid.toInt < 64 := by have := Int32.lt_iff_toInt_lt.mp b64; simpa using this
  have hwin : ∀ wo1, st.window = .val (.ref (.heap b) wo1) → wo1 + st.strstart.toNat ≤ pbo := by
    intro wo1 hw1
    rw [hw] at hw1; injection hw1 with e; injection e with _ e; subst e
    have := c.look; simp only [dview] at this; omega
  have S := H h i z st d pbo ⟨hpb, h4, l2, v0, v64, hwin⟩ hpre (by omega)
  rw [DeflateReset.SH_self hz hst' hd] at S
  obtain ⟨r, h'', e, st', d', rfl, -⟩ := S
  have e2 : C.run m h = .ok (r, SH h i z b st' d') := e
  rw [e2] at hrun
  cases hrun
  exact ⟨i, z, st', d', rfl, hz, rfl⟩

/-- An emitter proved on `SH` heaps is `EmitOk`. -/
theorem emit_of {s : StreamPtr} {b : Nat} {pre : DeflateState → Prop} {room grow : DeflateState → Nat} {m : M Unit}
    (hg : ∀ st, grow st ≤ room st)
    (H : ∀ h i z st d pbo, WCtx h i z b st d pbo → pre st →
      st.pending.toNat + room st ≤ 4 * st.lit_bufsize.toNat + 9 →
      Sat (SH h i z b st d) m (fun _ H' => EPost h i z b st d pbo (grow st) H')) :
    EmitOk s b pre room grow m := by
  intro h st hw hs hpre hr1 hr2
  obtain ⟨i, z, b', st0, al, rfl, hz, hb, hst, hal, b0, b64, c, -, -⟩ := hw
  obtain ⟨i1, z1, e1, hz1, hb1, hst1⟩ := hs
  obtain rfl := Option.some.inj e1
  rw [hz] at hz1; obtain rfl := Option.some.inj hz1
  rw [hb] at hb1; obtain rfl := (Option.some.inj hb1).symm
  rw [hst] at hst1; obtain rfl := (Option.some.inj hst1).symm
  obtain ⟨pbo1, poo1, hpb1, hpo1, hroom⟩ := hr1
  obtain ⟨-, -, -, -, l2, -, -⟩ := c.sizes
  obtain ⟨d, wo, po, ho, pbo, hd, hw, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  simp only [dview] at l2 hw hp hh hpb h1 h2 h3 h4 hsb hpo hpoo hpe
  obtain rfl := pend_inj hpb hpb1
  obtain rfl := pend_inj hpo hpo1
  have hst' : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  have v0 : 0 ≤ st.bi_valid.toInt := by have := Int32.le_iff_toInt_le.mp b0; simpa using this
  have v64 : st.bi_valid.toInt < 64 := by have := Int32.lt_iff_toInt_lt.mp b64; simpa using this
  have hwin : ∀ wo1, st.window = .val (.ref (.heap b) wo1) → wo1 + st.strstart.toNat ≤ pbo := by
    intro wo1 hw1
    rw [hw] at hw1; injection hw1 with e; injection e with _ e; subst e
    have := c.look; simp only [dview] at this; omega
  have S := H h i z st d pbo ⟨hpb, h4, l2, v0, v64, hwin⟩ hpre (by omega)
  rw [DeflateReset.SH_self hz hst' hd] at S
  obtain ⟨r, h', e, st', d', rfl, w, hv, hk, hle, hacc, v0', v64'⟩ := S
  have hg' := hg st
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  have hlb : st'.lit_bufsize = st.lit_bufsize := congrArg DView.lit_bufsize hv
  have hpb' : st'.pending_buf = st.pending_buf := congrArg DView.pending_buf hv
  have hpo' : st'.pending_out = st.pending_out := congrArg DView.pending_out hv
  have hsn : st'.sym_next = st.sym_next := congrArg DView.sym_next hv
  have hsz := w.1
  refine ⟨_, e, ⟨i, z, b, st', al, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _,
    by simp [Heap.dallocsOf, SH, hda], Int32.le_iff_toInt_le.mpr (by simpa using v0'),
    Int32.lt_iff_toInt_lt.mpr (by simpa using v64'), ?_,
    ⟨pbo, poo, by rw [hpb', hpb], by rw [hpo', hpo], by rw [hlb]; omega⟩,
    fun hn => ?_⟩, ?_, ⟨i, z, z, rfl, hz, SH_streams _ _ _ _ _ _, by cases z; rfl⟩,
    fun pbo2 hpb2 => ?_, ?_⟩
  · rw [hv]
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
      head := ⟨ho, d', by simp [SH], hh, by rw [hsz]; omega⟩
      level := c.level
      trees := c.trees
      sizes := c.sizes
      lay := ⟨d', wo, po, ho, pbo, by simp [SH], hw, hp, hh, hpb, h1, h2, h3, by rw [hsz]; exact h4, hsb, poo, hpo,
        hpoo, by simp only [dview]; omega⟩
      pout := fun hz0 => by
        simp only [dview] at hz0 ⊢
        have : st'.pending.toNat = 0 := by rw [hz0]; rfl
        have h0 : st.pending = 0 := UInt32.toNat_inj.mp (by rw [UInt32.toNat_zero]; omega)
        have := c.pout (by simp only [dview]; exact h0)
        simpa [dview] using this
      syms := c.syms
      bits := ⟨Int32.le_refl _, show (0 : Int32) < 8 by decide⟩
      look := c.look
      strategy := c.strategy
      fns := c.fns
      symv := by
        obtain ⟨d0, sbo, hd0, hs0, hv0⟩ := c.symv
        obtain rfl : d0 = d := Option.some.inj (hd0.symm.trans hd)
        simp only [dview] at hs0 hv0
        rw [hsb] at hs0
        obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hs0 with e1; injection e1
        refine ⟨d', _, by simp [SH], hsb, hv0.of_eq fun j hj => ?_⟩
        have hn : st.sym_next ≠ 0 := fun e => by simp [e] at hj
        obtain ⟨pbo3, poo3, hp3, ho3, hq⟩ := hr2 hn
        obtain rfl := pend_inj hpb hp3
        obtain rfl := pend_inj hpo ho3
        exact w.2 _ (Or.inr (by omega))
      psym := fun hn => by
        simp only [dview] at hn ⊢
        obtain ⟨pbo3, poo3, hp3, ho3, hq⟩ := hr2 hn
        obtain rfl := pend_inj hpb hp3
        obtain rfl := pend_inj hpo ho3
        exact ⟨pbo, poo, hpb, hpo, by omega⟩
      hdr := c.hdr
      bstart := c.bstart
      ins := c.ins
      wpow := c.wpow
      fe_mod := c.fe_mod
      fe_hi := c.fe_hi
      bs_lo := c.bs_lo
      descs := c.descs }
  · rw [hsn] at hn
    obtain ⟨pbo3, poo3, hp3, ho3, hq⟩ := hr2 hn
    obtain rfl := pend_inj hpb hp3
    obtain rfl := pend_inj hpo ho3
    exact ⟨pbo, poo, by rw [hpb', hpb], by rw [hpo', hpo], by rw [hlb]; omega⟩
  · exact DeflateReset.dframe_SH h i z b st' d'
  · obtain rfl := pend_inj hpb hpb2
    exact ⟨d, d', hd, SH_bytes _ _ _ _ _ _, hsz, fun j hj => w.2 j (by omega)⟩
  · rintro st'' ⟨i2, z2, e2, hz2, hb2, hst2⟩
    obtain rfl := Option.some.inj e2
    rw [SH_streams] at hz2; obtain rfl := Option.some.inj hz2
    rw [SH_dstate] at hst2; obtain rfl := Option.some.inj hst2
    exact ⟨hk, by omega⟩


/-! ## The static tables -/

theorem sl_size : static_ltree.size = 288 := by decide +kernel
theorem sd_size : static_dtree.size = 30 := by decide +kernel
theorem sl_len : ∀ k : Fin 288, (static_ltree[k.val]!).dl ≤ 9 := by decide +kernel
theorem dc_lt : ∀ k : Fin 512, (zng_dist_code[k.val]!) < 30 := by decide +kernel
theorem lc_lt : ∀ k : Fin 256, (zng_length_code[k.val]!) < 29 := by decide +kernel
theorem lm_ext : ∀ k : Fin 29, (lmask_extra[k.val]!.toUInt32 >>> 8).toNat ≤ 5 := by decide +kernel
theorem dm_ext : ∀ k : Fin 30, (dmask_extra[k.val]! >>> 16).toNat ≤ 13 ∧ (static_dtree[k.val]!).dl ≤ 5 := by
  decide +kernel
theorem dc_size : zng_dist_code.size = 512 := by decide +kernel
theorem lc_size : zng_length_code.size = 256 := by decide +kernel
theorem lm_size : lmask_extra.size = 29 := by decide +kernel
theorem dm_size : dmask_extra.size = 30 := by decide +kernel

theorem tblGet_ok {α : Type} [Inhabited α] (t : Array α) (k : Nat) (h : k < t.size) (H : Heap) :
    tblGet t k H = .ok (t[k]!, H) := by
  simp [tblGet, h]

theorem ctGet_sl (H : Heap) (k : Nat) (hk : k < 288) :
    ctGet (.ref .static_ltree 0) (k : Int) H = .ok (static_ltree[k]!, H) := by
  have hs := sl_size
  have hk' : (k : Int) ≤ 288 := by omega
  simp [ctGet, Ptr.index, Ptr.add, Ptr.load, bind_app, Space.get, Heap.getCts, hs, hk, hk']

theorem ctGet_sd (H : Heap) (k : Nat) (hk : k < 30) :
    ctGet (.ref .static_dtree 0) (k : Int) H = .ok (static_dtree[k]!, H) := by
  have hs := sd_size
  have hk' : (k : Int) ≤ 30 := by omega
  simp [ctGet, Ptr.index, Ptr.add, Ptr.load, bind_app, Space.get, Heap.getCts, hs, hk, hk']


/-! ## `send_bits` -/

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- What `send_bits` leaves: at most 8 more pending bytes, all the bits counted, fewer than 64 bits left. -/
def SBPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo n : Nat)
    (r : UInt64 × UInt32) (H' : Heap) : Prop :=
  ∃ np d', H' = SH H i z b { st with pending := np } d' ∧ WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' ∧
    np.toNat * 8 + r.2.toNat = st.pending.toNat * 8 + n ∧ r.2.toNat < 64 ∧ st.pending.toNat ≤ np.toNat ∧
    np.toNat ≤ st.pending.toNat + 8

theorem send_bits_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (val : UInt64) (len : UInt32)
    (bb : UInt64) (bv : UInt32) (hbv : bv.toNat < 64) (hlen : len.toNat ≤ 64)
    (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.send_bits (some b) val len bb bv)
      (SBPost H i z b st d pbo (bv.toNat + len.toNat)) := by
  have hbv' : bv < 64 := UInt32.lt_iff_toNat_lt.mpr hbv
  have ht : (bv + len).toNat = bv.toNat + len.toNat := by rw [UInt32.toNat_add]; omega
  unfold ZlibNg.TreesEmit.send_bits
  simp only [shl64, hbv', ↓reduceIte, pure_bind_M]
  by_cases c : bv + len ≥ 64
  · rw [ite_t c]
    have c' : 64 ≤ bv.toNat + len.toNat := by rw [← ht]; exact UInt32.le_iff_toNat_le.mp c
    refine Sat.bind (Sat.mono (put_uint64_SH hpb _ hroom) ?_)
    rintro _ _ ⟨d1, rfl, w1⟩
    have hm : (~~~bv &&& 63) < 64 := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_and]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    simp only [shr64, hm, ↓reduceIte, pure_bind_M]
    have hp8 : (st.pending + 8).toNat = st.pending.toNat + 8 := add_toNat _ 8 (by decide) (by omega)
    have hs : (bv + len - 64).toNat = bv.toNat + len.toNat - 64 := by
      rw [UInt32.toNat_sub_of_le _ _ c, ht]; rfl
    refine Sat.pure ⟨st.pending + 8, d1, rfl, by rw [hp8]; exact w1, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hp8, hs] <;> omega
  · rw [ite_f c]
    have c' : bv.toNat + len.toNat < 64 := by
      rw [← ht]; exact UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp c)
    refine Sat.pure ⟨st.pending, d, rfl, WrIn.refl _ _ _, ?_, ?_, ?_, ?_⟩ <;> (try simp only [ht]) <;> omega

theorem ctFc_sl (H : Heap) (k : Nat) (hk : k < 288) :
    ctFc (.ref .static_ltree 0) (k : Int) H = .ok ((static_ltree[k]!).fc, H) := by
  simp [ctFc, bind_app, ctGet_sl H k hk]
theorem ctDl_sl (H : Heap) (k : Nat) (hk : k < 288) :
    ctDl (.ref .static_ltree 0) (k : Int) H = .ok ((static_ltree[k]!).dl, H) := by
  simp [ctDl, bind_app, ctGet_sl H k hk]
theorem ctFc_sd (H : Heap) (k : Nat) (hk : k < 30) :
    ctFc (.ref .static_dtree 0) (k : Int) H = .ok ((static_dtree[k]!).fc, H) := by
  simp [ctFc, bind_app, ctGet_sd H k hk]
theorem ctDl_sd (H : Heap) (k : Nat) (hk : k < 30) :
    ctDl (.ref .static_dtree 0) (k : Int) H = .ok ((static_dtree[k]!).dl, H) := by
  simp [ctDl, bind_app, ctGet_sd H k hk]

/-! ## The emitters -/

theorem toU32 (x : Int32) (h0 : 0 ≤ x.toInt) : x.toUInt32.toNat = x.toInt.toNat :=
  DeflatePrime.toUInt32_toNat x h0

/-- The state an emitter leaves when it ends with `s->bi_buf = bi_buf; s->bi_valid = bi_valid;`. -/
theorem epost_mk {pbo grow : Nat} (np : UInt32) (d' : Array UInt8) (bb : UInt64) (bv : UInt32)
    (w : WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d')
    (hle : st.pending.toNat ≤ np.toNat) (hacc : np.toNat * 8 + bv.toNat ≤ st.pending.toNat * 8 + 8 * grow)
    (hbv : bv.toNat < 64) :
    EPost H i z b st d pbo grow (SH H i z b { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 } d') := by
  have e := DeflateAlloc.u32_toInt32_toInt bv (by omega)
  exact ⟨_, d', rfl, w, rfl, rfl, hle, by dsimp only; rw [e]; omega, by rw [e]; omega, by rw [e]; omega⟩

theorem emit_lit_SH {pbo : Nat} (W : WCtx H i z b st d pbo) (hroom : st.pending.toNat + 8 ≤ 4 * st.lit_bufsize.toNat + 9)
    (c : UInt32) (hc : c.toNat < 256) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_lit (some b) ZlibNg.DeflateQuick.static_ltree_p c)
      (fun _ H' => EPost H i z b st d pbo 16 H') := by
  have := W.pad; have := W.lb
  unfold ZlibNg.TreesEmit.zng_tr_emit_lit ZlibNg.TreesEmit.zng_emit_lit ZlibNg.TreesEmit.send_code
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  have hv := toU32 _ W.v0
  have hl : (static_ltree[c.toNat]!).dl.toNat ≤ 9 := UInt16.le_iff_toNat_le.mp (sl_len ⟨c.toNat, by omega⟩)
  refine Sat.bind (Sat.bind (Sat.of_eq (ctFc_sl _ _ (by omega)) (Sat.bind (Sat.of_eq (ctDl_sl _ _ (by omega)) ?_))))
  refine Sat.mono (send_bits_SH W.hpb _ _ _ _ (by have := W.v64; omega) (by simp only [UInt16.toNat_toUInt32]; omega) (by omega)
    (by omega)) ?_
  rintro ⟨r1, r2⟩ _ ⟨np, d1, rfl, w, hacc, hr, hle, hge⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (ctDl_sl _ _ (by omega)) ?_)
  exact Sat.pure (epost_mk np d1 r1 r2 w hle (by simp only [UInt16.toNat_toUInt32] at hacc; rw [hv] at hacc; have := W.v64; omega) hr)

theorem EPost.mono {pbo grow grow' : Nat} {H' : Heap} (q : EPost H i z b st d pbo grow H') (hg : grow ≤ grow') :
    EPost H i z b st d pbo grow' H' := by
  obtain ⟨st', d', e, hsz, hv, hk, hle, hge, h0, h1⟩ := q
  exact ⟨st', d', e, hsz, hv, hk, hle, by omega, h0, h1⟩

end

/-! ## `bi_windup` -/

/-- The last statements of `bi_windup`. -/
def wdTail (st : StatePtr) : M Unit := do
  let v ← chkI32 ((← rdD st (·.bi_valid)).toInt - 1)
  let bi_used := (v &&& 7) + 1
  wrD st fun s => { s with bi_used := bi_used, bi_buf := 0, bi_valid := 0 }

/-- `if (s->bi_valid > 0) put_byte(...)` and the tail. -/
def wd0 (st : StatePtr) : M Unit := do
  if (← rdD st (·.bi_valid)) > 0 then
    put_byte st (← rdD st (·.bi_buf)).toUInt8
  let v ← chkI32 ((← rdD st (·.bi_valid)).toInt - 1)
  let bi_used := (v &&& 7) + 1
  wrD st fun s => { s with bi_used := bi_used, bi_buf := 0, bi_valid := 0 }

/-- `if (s->bi_valid > 8) { put_short(...); ... }` and the rest. -/
def wd8 (st : StatePtr) : M Unit := do
  if (← rdD st (·.bi_valid)) > 8 then
    put_short st (← rdD st (·.bi_buf)).toUInt16
    wrD st fun s => { s with bi_buf := s.bi_buf >>> 16 }
    wrD st fun s => { s with bi_valid := s.bi_valid - 16 }
  if (← rdD st (·.bi_valid)) > 0 then
    put_byte st (← rdD st (·.bi_buf)).toUInt8
  let v ← chkI32 ((← rdD st (·.bi_valid)).toInt - 1)
  let bi_used := (v &&& 7) + 1
  wrD st fun s => { s with bi_used := bi_used, bi_buf := 0, bi_valid := 0 }

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- What `bi_windup` (or a tail of it) leaves: at most `K` more pending bytes, the bit buffer empty. -/
def WDPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo K : Nat)
    (H' : Heap) : Prop :=
  ∃ np bu d', H' = SH H i z b { st with pending := np, bi_used := bu, bi_buf := 0, bi_valid := 0 } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' ∧ st.pending.toNat ≤ np.toNat ∧
    np.toNat ≤ st.pending.toNat + K

theorem WDPost.step {pbo k K : Nat} {st1 : DeflateState} {d1 : Array UInt8} {H' : Heap}
    (hs : st1 = { st with pending := st1.pending, bi_buf := st1.bi_buf, bi_valid := st1.bi_valid })
    (w : WrIn d (pbo + st.pending.toNat) (pbo + st.pending.toNat + k) d1)
    (hp : st1.pending.toNat = st.pending.toNat + k) (q : WDPost H i z b st1 d1 pbo K H') :
    WDPost H i z b st d pbo (k + K) H' := by
  obtain ⟨np, bu, d', rfl, w', h1, h2⟩ := q
  refine ⟨np, bu, d', by rw [hs], ?_, by omega, by omega⟩
  rw [hp] at w'
  exact (w.widen (Nat.le_refl _) (by omega : pbo + st.pending.toNat + k ≤ pbo + np.toNat)).trans
    (w'.widen (by omega) (Nat.le_refl _)) (Nat.le_refl _) (Nat.le_refl _)

/-- `x - k` on `int32_t` for small `x` and `k`. -/
theorem subI (x : Int32) (k : Nat) (h1 : -1000 ≤ x.toInt) (h2 : x.toInt ≤ 1000) (hk : k ≤ 1000 := by omega) :
    (x - Int32.ofNat k).toInt = x.toInt - k := by
  rw [Int32.toInt_sub, Int32.toInt_ofNat_of_lt (by omega)]
  rw [Int.bmod_eq_of_le] <;> omega

theorem WDPost.mono_K {pbo K K' : Nat} {H' : Heap} (q : WDPost H i z b st d pbo K H') (hK : K ≤ K') :
    WDPost H i z b st d pbo K' H' := by
  obtain ⟨np, bu, d', e, w, h1, h2⟩ := q
  exact ⟨np, bu, d', e, w, h1, by omega⟩

theorem wdTail_SH {pbo : Nat} (h0 : -8 < st.bi_valid.toInt) :
    Sat (SH H i z b st d) (wdTail (some b)) (fun _ H' => WDPost H i z b st d pbo 0 H') := by
  unfold wdTail
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  have := st.bi_valid.toInt_lt
  rw [DeflatePrime.chk_ok _ (by omega) (by omega), pure_bind_M]
  exact Sat.of_eq (wrD_SH _) ⟨st.pending, _, d, rfl, WrIn.refl _ _ _, Nat.le_refl _, by omega⟩

theorem wd0_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : -8 < st.bi_valid.toInt)
    (_h8 : st.bi_valid.toInt ≤ 8) (hroom : pbo + st.pending.toNat + 1 ≤ d.size) (hp : st.pending.toNat + 1 < 2 ^ 32) :
    Sat (SH H i z b st d) (wd0 (some b)) (fun _ H' => WDPost H i z b st d pbo ((st.bi_valid.toInt + 7).toNat / 8) H') := by
  unfold wd0
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  by_cases c : st.bi_valid > 0
  · rw [ite_t c]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (put_byte_SH hpb _ hroom) ?_)
    rintro _ _ ⟨d1, rfl, w1⟩
    have hp1 : (st.pending + 1).toNat = st.pending.toNat + 1 := add_toNat _ 1 (by decide) (by omega)
    exact Sat.mono (wdTail_SH (pbo := pbo) (by exact h0)) fun _ _ q =>
      (WDPost.step rfl w1 hp1 q).mono_K (by have := Int32.lt_iff_toInt_lt.mp c; simp at this; omega)
  · rw [ite_f c]
    exact Sat.mono (wdTail_SH (pbo := pbo) h0) fun _ _ q =>
      (WDPost.step (k := 0) rfl (WrIn.refl _ _ _) rfl q).mono_K (by omega)

theorem wd8_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : -8 < st.bi_valid.toInt)
    (h24 : st.bi_valid.toInt ≤ 24) (hroom : pbo + st.pending.toNat + 3 ≤ d.size) (hp : st.pending.toNat + 3 < 2 ^ 32) :
    Sat (SH H i z b st d) (wd8 (some b)) (fun _ H' => WDPost H i z b st d pbo ((st.bi_valid.toInt + 7).toNat / 8) H') := by
  unfold wd8
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  by_cases c : st.bi_valid > 8
  · rw [ite_t c]
    have c' := Int32.lt_iff_toInt_lt.mp c
    have e8 : (8 : Int32).toInt = 8 := rfl
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (put_short_SH hpb _ (by omega)) ?_)
    rintro _ _ ⟨d1, rfl, w1⟩
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    have hp2 : (st.pending + 2).toNat = st.pending.toNat + 2 := add_toNat _ 2 (by decide) (by omega)
    have hv : (st.bi_valid - 16).toInt = st.bi_valid.toInt - 16 := subI _ 16 (by omega) (by omega)
    exact Sat.mono (wd0_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; rw [hp2, w1.1]; omega) (by dsimp only; rw [hp2]; omega))
      fun _ _ q => (WDPost.step (k := 2) rfl w1 hp2 q).mono_K (by dsimp only; rw [hv]; omega)
  · rw [ite_f c]
    have c' : ¬ (8 : Int32).toInt < st.bi_valid.toInt := fun h => c (Int32.lt_iff_toInt_lt.mpr h)
    have e8 : (8 : Int32).toInt = 8 := rfl
    exact Sat.mono (wd0_SH hpb h0 (by omega) (by omega) (by omega))
      fun _ _ q => (WDPost.step (k := 0) rfl (WrIn.refl _ _ _) rfl q).mono_K (by omega)

/-- `bi_windup` with at most 63 bits: at most 8 bytes. -/
theorem windup_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.bi_windup (some b)) (fun _ H' => WDPost H i z b st d pbo ((st.bi_valid.toInt + 7).toNat / 8) H') := by
  unfold ZlibNg.TreesEmit.bi_windup
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  by_cases c : st.bi_valid > 56
  · rw [ite_t c]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (put_uint64_SH hpb _ hroom) ?_)
    rintro _ _ ⟨d1, rfl, w1⟩
    have hp8 : (st.pending + 8).toNat = st.pending.toNat + 8 := add_toNat _ 8 (by decide) (by omega)
    exact Sat.mono (wdTail_SH (pbo := pbo) (by dsimp only; omega)) fun _ _ q =>
      (WDPost.step (k := 8) rfl w1 hp8 q).mono_K (by have := Int32.lt_iff_toInt_lt.mp c; simp at this; omega)
  · rw [ite_f c]
    have c' : ¬ (56 : Int32).toInt < st.bi_valid.toInt := fun h => c (Int32.lt_iff_toInt_lt.mpr h)
    have e56 : (56 : Int32).toInt = 56 := rfl
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    by_cases c2 : st.bi_valid > 24
    · rw [ite_t c2]
      have c2' := Int32.lt_iff_toInt_lt.mp c2
      have e24 : (24 : Int32).toInt = 24 := rfl
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
      refine Sat.bind (Sat.mono (put_uint32_SH hpb _ (by omega)) ?_)
      rintro _ _ ⟨d1, rfl, w1⟩
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
      have hp4 : (st.pending + 4).toNat = st.pending.toNat + 4 := add_toNat _ 4 (by decide) (by omega)
      have hv : (st.bi_valid - 32).toInt = st.bi_valid.toInt - 32 := subI _ 32 (by omega) (by omega)
      exact Sat.mono (wd8_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; rw [hp4, w1.1]; omega) (by dsimp only; rw [hp4]; omega))
        fun _ _ q => (WDPost.step (k := 4) rfl w1 hp4 q).mono_K (by dsimp only; rw [hv]; omega)
    · rw [ite_f c2]
      have c2' : ¬ (24 : Int32).toInt < st.bi_valid.toInt := fun h => c2 (Int32.lt_iff_toInt_lt.mpr h)
      have e24 : (24 : Int32).toInt = 24 := rfl
      exact Sat.mono (wd8_SH hpb (by omega) (by omega) (by omega) (by omega))
        fun _ _ q => (WDPost.step (k := 0) rfl (WrIn.refl _ _ _) rfl q).mono_K (by omega)

/-! ## Emitters that end with `s->bi_buf = bi_buf; s->bi_valid = bi_valid;` -/

/-- What such an emitter leaves: `n` more bits counted, at most `K` more pending bytes, fewer than 64 bits. -/
def APost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (pbo n K : Nat)
    (H' : Heap) : Prop :=
  ∃ np bb, ∃ bv : UInt32, ∃ d', H' = SH H i z b { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' ∧
    np.toNat * 8 + bv.toNat = st.pending.toNat * 8 + st.bi_valid.toInt.toNat + n ∧ bv.toNat < 64 ∧
    st.pending.toNat ≤ np.toNat ∧ np.toNat ≤ st.pending.toNat + K

theorem APost.epost {pbo n K grow : Nat} {H' : Heap} (q : APost H i z b st d pbo n K H')
    (hn : st.bi_valid.toInt.toNat + n ≤ 8 * grow) :
    EPost H i z b st d pbo grow H' := by
  obtain ⟨np, bb, bv, d', rfl, w, hacc, hbv, hle, hge⟩ := q
  exact epost_mk np d' bb bv w hle (by omega) hbv

theorem toInt32_toInt (bv : UInt32) (h : bv.toNat < 64) : bv.toInt32.toInt = bv.toNat :=
  DeflateAlloc.u32_toInt32_toInt bv (by omega)

theorem toInt32_toUInt32 (bv : UInt32) : bv.toInt32.toUInt32 = bv := by
  simp

/-- `send_bits` of `n` bits from the state's bit buffer, stored back. -/
theorem sbw {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (val : UInt64) (len : UInt32)
    (h0 : 0 ≤ st.bi_valid.toInt) (h64 : st.bi_valid.toInt < 64) (hlen : len.toNat ≤ 64)
    (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32) {β : Type} {Q : β → Heap → Prop}
    (f : UInt64 × UInt32 → M β)
    (hf : ∀ (r : UInt64 × UInt32) np d', WrIn d (pbo + st.pending.toNat) (pbo + np.toNat) d' →
      np.toNat * 8 + r.2.toNat = st.pending.toNat * 8 + st.bi_valid.toInt.toNat + len.toNat → r.2.toNat < 64 →
      st.pending.toNat ≤ np.toNat → np.toNat ≤ st.pending.toNat + 8 →
      Sat (SH H i z b { st with pending := np } d') (f r) Q) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.send_bits (some b) val len st.bi_buf st.bi_valid.toUInt32 >>= f) Q := by
  have hv := toU32 _ h0
  refine Sat.bind (Sat.mono (send_bits_SH hpb _ _ _ _ (by omega) hlen hroom hp) ?_)
  rintro r _ ⟨np, d1, rfl, w, hacc, hr, hle, hge⟩
  exact hf r np d1 w (by rw [hv] at hacc; omega) hr hle hge

theorem emit_tree_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 8 ≤ d.size) (hp : st.pending.toNat + 8 < 2 ^ 32)
    (type last : Int32) (ht0 : 0 ≤ type.toInt) (ht2 : type.toInt ≤ 2) (hl : 2 * type.toInt + last.toInt < 2147483648) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_tree (some b) type last)
      (fun _ H' => APost H i z b st d pbo 3 8 H') := by
  unfold ZlibNg.TreesEmit.zng_tr_emit_tree
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  have hn : ¬ type < 0 := fun h => by have := Int32.lt_iff_toInt_lt.mp h; simp at this; omega
  have := last.le_toInt
  simp only [hn, ↓reduceIte]
  rw [DeflatePrime.chk_ok _ (by omega) (by omega), pure_bind_M]
  rw [DeflatePrime.chk_ok _ (by rw [DeflatePrime.ofInt_toInt _ (by omega) (by omega)]; omega)
    (by rw [DeflatePrime.ofInt_toInt _ (by omega) (by omega)]; omega), pure_bind_M]
  refine sbw hpb _ _ h0 h64 (by decide) hroom hp _ ?_
  rintro ⟨r1, r2⟩ np d' w hacc hr hle hge
  exact Sat.of_eq (wrD_SH _) ⟨np, r1, r2, d', rfl, w, hacc, hr, hle, hge⟩

/-- `bi_windup` after an emitter: the view is kept, at most `grow` more bytes in all. -/
theorem WDPost.epost {pbo K grow : Nat} {st1 : DeflateState} {d1 : Array UInt8} {H' : Heap}
    (hs : st1 = { st with pending := st1.pending, bi_buf := st1.bi_buf, bi_valid := st1.bi_valid })
    (w1 : WrIn d (pbo + st.pending.toNat) (pbo + st1.pending.toNat) d1) (hle : st.pending.toNat ≤ st1.pending.toNat)
    (hge : st1.pending.toNat + K ≤ st.pending.toNat + grow) (q : WDPost H i z b st1 d1 pbo K H') :
    EPost H i z b st d pbo grow H' := by
  obtain ⟨np, bu, d', rfl, w, h1, h2⟩ := q
  refine ⟨_, d', rfl, (w1.widen (Nat.le_refl _) (by dsimp only; omega)).trans (w.widen (by omega) (Nat.le_refl _))
    (Nat.le_refl _) (Nat.le_refl _), ?_, ?_, by dsimp only; omega,
    by dsimp only; rw [show (0 : Int32).toInt.toNat = 0 from rfl]; omega,
    show 0 ≤ (0 : Int32).toInt by decide, show (0 : Int32).toInt < 64 by decide⟩
  · rw [hs]; rfl
  · rw [hs]; rfl

theorem end_block_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (h0 : 0 ≤ st.bi_valid.toInt)
    (h64 : st.bi_valid.toInt < 64) (hroom : pbo + st.pending.toNat + 16 ≤ d.size) (hp : st.pending.toNat + 16 < 2 ^ 32)
    (last : Int32) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) (.ref .static_ltree 0) last)
      (fun _ H' => (last = 0 → APost H i z b st d pbo 7 8 H') ∧ EPost H i z b st d pbo 16 H') := by
  unfold ZlibNg.TreesEmit.zng_tr_emit_end_block ZlibNg.TreesEmit.zng_emit_end_block ZlibNg.TreesEmit.send_code
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  have hl : (static_ltree[256]!).dl.toNat = 7 := by decide +kernel
  have hv := toU32 _ h0
  refine Sat.bind (Sat.bind (Sat.of_eq (ctFc_sl _ 256 (by decide)) (Sat.bind (Sat.of_eq (ctDl_sl _ 256 (by decide))
    ?_))))
  refine Sat.mono (send_bits_SH hpb _ _ _ _ (by omega) (by simp only [UInt16.toNat_toUInt32]; omega) (by omega)
    (by omega)) ?_
  rintro ⟨r1, r2⟩ _ ⟨np, d1, rfl, w, hacc, hr, hle, hge⟩
  simp only [UInt16.toNat_toUInt32, hl, hv] at hacc
  dsimp only at hr
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  have ea : APost H i z b st d pbo 7 8 (SH H i z b { st with pending := np, bi_buf := r1, bi_valid := r2.toInt32 } d1) :=
    ⟨np, r1, r2, d1, rfl, w, by omega, hr, hle, hge⟩
  by_cases c : last = 0
  · subst c
    exact Sat.pure ⟨fun _ => ea, ea.epost (by have := h64; omega)⟩
  · have c' : (last != 0) = true := by simpa using c
    rw [ite_t c']
    have e := toInt32_toInt r2 hr
    unfold ZlibNg.TreesEmit.zng_tr_emit_align
    refine Sat.mono (windup_SH (pbo := pbo) (by exact hpb) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; rw [w.1]; omega) (by dsimp only; omega)) ?_
    intro _ _ q
    exact ⟨fun h => absurd h c, WDPost.epost rfl w hle (by dsimp only; omega) q⟩

end

/-! ## `zng_tr_emit_dist` with the static trees -/

theorem shl_ok (x : UInt64) (n : UInt32) (h : n.toNat < 64) (H : Heap) : shl64 x n H = .ok (x <<< n.toUInt64, H) := by
  have h' : n < 64 := UInt32.lt_iff_toNat_lt.mpr (by rw [show (64 : UInt32).toNat = 64 from rfl]; exact h)
  simp only [shl64, h', ↓reduceIte]; rfl

theorem d_code_ok (H : Heap) (x : UInt32) (hx : x.toNat < 32768) :
    ∃ c, d_code x H = .ok (c, H) ∧ c.toNat < 30 := by
  unfold d_code
  by_cases c : x < 256
  · rw [ite_t c]
    have c' := UInt32.lt_iff_toNat_lt.mp c
    simp only [show (256 : UInt32).toNat = 256 from rfl] at c'
    exact ⟨_, tblGet_ok _ _ (by rw [dc_size]; omega) H, UInt8.lt_iff_toNat_lt.mp (dc_lt ⟨x.toNat, by omega⟩)⟩
  · rw [ite_f c]
    have hs : (x >>> 7).toNat = x.toNat / 128 := by
      rw [UInt32.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
    exact ⟨_, tblGet_ok _ _ (by rw [dc_size, hs]; omega) H,
      UInt8.lt_iff_toNat_lt.mp (dc_lt ⟨256 + (x >>> 7).toNat, by rw [hs]; omega⟩)⟩

/-- `zng_assemble_dist` on the static trees, for a length code `lc <= 255` and a distance `1..32768`: no fault, at
most 32 bits. -/
theorem assemble_static (H : Heap) (lc dist : UInt32) (hlc : lc.toNat < 256) (hd1 : 1 ≤ dist.toNat)
    (hd2 : dist.toNat ≤ 32768) :
    Sat H (ZlibNg.TreesEmit.zng_assemble_dist (.ref .static_ltree 0) (.ref .static_dtree 0) lc dist)
      (fun r H' => H' = H ∧ r.2.toNat ≤ 32) := by
  unfold ZlibNg.TreesEmit.zng_assemble_dist
  refine Sat.bind (Sat.of_eq (tblGet_ok _ _ (by rw [lc_size]; exact hlc) H) ?_)
  have hcode : (zng_length_code[lc.toNat]!).toNat < 29 := UInt8.lt_iff_toNat_lt.mp (lc_lt ⟨_, hlc⟩)
  generalize zng_length_code[lc.toNat]! = code at hcode ⊢
  have hc : (code.toUInt32 + LITERALS.toUInt32 + 1).toNat = code.toNat + 257 := by
    simp only [UInt32.toNat_add, UInt8.toNat_toUInt32, LITERALS]; simp; omega
  try dsimp only
  rw [hc]
  have hl1 : (static_ltree[code.toNat + 257]!).dl.toNat ≤ 9 := UInt16.le_iff_toNat_le.mp (sl_len ⟨_, by omega⟩)
  have hx1 := lm_ext ⟨_, hcode⟩
  obtain ⟨e1, he1⟩ : ∃ e, static_ltree[code.toNat + 257]! = e := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ e, lmask_extra[code.toNat]! = e := ⟨_, rfl⟩
  rw [he1] at hl1; rw [hm1] at hx1
  refine Sat.bind (Sat.of_eq ((ctFc_sl H _ (by omega)).trans (by rw [he1])) ?_)
  refine Sat.bind (Sat.of_eq ((ctDl_sl H _ (by omega)).trans (by rw [he1])) ?_)
  refine Sat.bind (Sat.of_eq ((tblGet_ok _ _ (by rw [lm_size]; exact hcode) H).trans (by rw [hm1])) ?_)
  refine Sat.bind (Sat.of_eq (shl_ok _ _ (by simp only [UInt16.toNat_toUInt32]; omega) H) ?_)
  have hd1' : (1 : UInt32) ≤ dist := UInt32.le_iff_toNat_le.mpr (by simpa using hd1)
  have hdm : (dist - 1).toNat = dist.toNat - 1 := by rw [UInt32.toNat_sub_of_le _ _ hd1']; rfl
  obtain ⟨c2, hd, hc2⟩ := d_code_ok H (dist - 1) (by rw [hdm]; omega)
  refine Sat.bind (Sat.of_eq hd ?_)
  have hd2' := dm_ext ⟨_, hc2⟩
  obtain ⟨e2, he2⟩ : ∃ e, static_dtree[c2.toNat]! = e := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ e, dmask_extra[c2.toNat]! = e := ⟨_, rfl⟩
  rw [he2, hm2] at hd2'
  obtain ⟨hx2, hl2⟩ := hd2'
  have hl2' : e2.dl.toNat ≤ 5 := UInt16.le_iff_toNat_le.mp hl2
  have hs1 : (e1.dl.toUInt32 + m1.toUInt32 >>> 8).toNat = e1.dl.toNat + (m1.toUInt32 >>> 8).toNat := by
    rw [UInt32.toNat_add, UInt16.toNat_toUInt32]; omega
  refine Sat.bind (Sat.of_eq ((ctFc_sd H _ hc2).trans (by rw [he2])) ?_)
  refine Sat.bind (Sat.of_eq (shl_ok _ _ (by rw [hs1]; omega) H) ?_)
  refine Sat.bind (Sat.of_eq ((ctDl_sd H _ hc2).trans (by rw [he2])) ?_)
  refine Sat.bind (Sat.of_eq ((tblGet_ok _ _ (by rw [dm_size]; exact hc2) H).trans (by rw [hm2])) ?_)
  have hs2 : (e1.dl.toUInt32 + m1.toUInt32 >>> 8 + e2.dl.toUInt32).toNat =
      e1.dl.toNat + (m1.toUInt32 >>> 8).toNat + e2.dl.toNat := by
    rw [UInt32.toNat_add, hs1, UInt16.toNat_toUInt32]; omega
  refine Sat.bind (Sat.of_eq (shl_ok _ _ (by rw [hs2]; omega) H) ?_)
  refine Sat.pure ⟨rfl, ?_⟩
  show (e1.dl.toUInt32 + m1.toUInt32 >>> 8 + e2.dl.toUInt32 + m2 >>> 16).toNat ≤ 32
  rw [UInt32.toNat_add, hs2]; omega

end ZlibNgF.Proof.TreesEmitP
