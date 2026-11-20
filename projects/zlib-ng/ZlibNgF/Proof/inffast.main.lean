import ZlibNgF.Proof.«inffast.loop»
import ZlibNgF.Proof.«inflate.c.invariant»

/-!
# `inflate_fast_c` / `inflate_fast_safe_c`: the whole call (`ZlibNgF`)

`inflate_fast_post`: from the entry state that `LEN` of `inflate` guarantees (fewer than 8 bits held, at least 15 input
bytes, at least 260 / 3 output bytes, the window and the decoding tables of the state), `INFLATE_FAST` runs without
fault and ends in `FastPost`: the exact stream and state records it leaves, the exit modes, `bits < 8`, the progress
inequality, and the frame (only the output bytes `[next_out, next_out + avail_out)`, the stream record and the state
change). The entry code establishes `EnvOK`; the main loop is `loop_step`; the epilogue moves `in` back by
`bits >> 3` bytes, which stays inside the input because `bits ≤ 8 * (in - next_in) + bits0` and `bits0 < 8`
(patch 0010).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastMain
open C ZlibNg.Inffast ZlibNg.InflateP ZlibNg.Chunkset
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem
open ZlibNgF.Proof.ChunkCopy (B sat_diff_r)
open ZlibNgF.Proof.InffastBase
open ZlibNgF.Proof.InffastInv
open ZlibNgF.Proof.InffastSteps
open ZlibNgF.Proof.InffastLoop

theorem sat_bind_eq {α β : Type} {H H' : Heap} {m : M α} {f : α → M β} {a : α} {Q : β → Heap → Prop}
    (e : m H = .ok (a, H')) (k : Sat H' (f a) Q) : Sat H (m >>= f) Q :=
  Sat.bind ⟨a, H', e, k⟩

theorem u8_of_lt8 (x : UInt32) (h : x < 8) : x.toUInt8.toNat = x.toNat := by
  rw [UInt32.lt_iff_toNat_lt] at h
  simp only [UInt32.toNat_toUInt8]; simp at h; omega

theorem shr3 : ∀ x : UInt8, (x.toUInt32 >>> 3).toNat = x.toNat / 8 := by decide
theorem md8 : ∀ x : UInt8, (x - ((x.toUInt32 >>> 3) <<< 3).toUInt8).toNat = x.toNat % 8 := by decide

open ZlibNgF.Spec in
/-- The frame of a run that changed the output bytes `[o0, o0 + n)` of block `ob`, the stream record `i` and the state
`b`. -/
theorem frame_run {h G1 : Heap} {ob N o0 n i b : Nat} (r : ORun h G1 ob N o0 (o0 + n)) (hb : b ≠ ob)
    (X : Tbl (Option ZStream)) (Y : Tbl (Option InflateState)) (hX : ∀ j, j ≠ i → X j = G1.streams j)
    (hY : ∀ j, j ≠ b → Y j = G1.istates j) :
    Frame h { G1 with streams := X, istates := Y } [i] [b] [] [(.ref (.heap ob) o0, n)] := by
  have eq := r.eq
  obtain ⟨a0, a, e0, e1, s0, s1, hp⟩ := r.blk
  refine ⟨fun j hj => ?_, fun k _ => by rw [eq], fun b' _ hb' => ?_, fun b' _ _ data hd => ?_,
    fun b' _ _ hn => ?_, by rw [eq], by rw [eq], by rw [eq], by rw [eq], by rw [eq]; exact Nat.le_refl _⟩
  · show X j = _; rw [hX j (by simpa using hj), eq]
  · refine ⟨?_, by show G1.iallocs b' = _; rw [eq]⟩
    show Y b' = _; rw [hY b' (by simpa using hb'), eq]
  · by_cases hbo : b' = ob
    · subst hbo
      rw [e0] at hd; cases hd
      refine ⟨a, e1, by omega, fun j _ hw => (hp j ?_)⟩
      have := hw _ (List.mem_singleton_self _) o0 rfl
      omega
    · exact ⟨data, by show G1.bytes b' = _; rw [r.bytes_ne hbo]; exact hd, rfl, fun _ _ _ => rfl⟩
  · by_cases hbo : b' = ob
    · subst hbo; rw [e0] at hn; cases hn
    · show G1.bytes b' = _; rw [r.bytes_ne hbo]; exact hn

open ZlibNgF.Spec in
/-- What `inflate_fast_c` / `inflate_fast_safe_c` guarantee on return (the conclusion of `InflateFacts.FastFacts`). -/
def FastPost (safe : Bool) (h : Heap) (i b : Nat) (z : ZStream) (st : InflateState) (start : UInt32) (ri : BRef)
    (oi bo oo : Nat) (h' : Heap) : Prop :=
  ∃ (ai ao : UInt32) (m : UInt32) (hold : UInt64) (bits : UInt32) (len was off : UInt32) (msg : BPtr),
    8 * ai.toNat + bits.toNat + 1 ≤ 8 * z.avail_in.toNat + st.bits.toNat ∧ ai ≤ z.avail_in ∧ ao ≤ z.avail_out ∧
    h'.streams i = some { z with
      next_in := .ref ri (oi + (z.avail_in - ai).toNat)
      avail_in := ai
      next_out := .ref (.heap bo) (oo + (start - ao).toNat)
      avail_out := ao
      msg := msg } ∧
    h'.istates b = some { st with
      mode := m
      hold := hold
      bits := bits
      length := len
      was := was
      offset := off } ∧
    (m = ZlibNg.Inflate.LEN ∨ m = ZlibNg.Inflate.TYPE ∨ m = ZlibNg.Inflate.BAD ∨
      (safe = true ∧ m = ZlibNg.Inflate.MATCH ∧ 1 ≤ off.toNat)) ∧ bits < 8 ∧
    8 * ai.toNat + bits.toNat + ao.toNat + (if m = ZlibNg.Inflate.BAD then 0 else 1) ≤
      8 * z.avail_in.toNat + st.bits.toNat + z.avail_out.toNat ∧
    h'.bytes b = h.bytes b ∧ h'.iallocs b = h.iallocs b ∧ (∀ c, c ≠ bo → h'.bytes c = h.bytes c) ∧
    (∀ d, h.bytes bo = some d → ∃ d', h'.bytes bo = some d' ∧ d'.size = d.size) ∧
    Frame h h' [i] [b] [] [(z.next_out, z.avail_out.toNat)]

/-- **`INFLATE_FAST` (both variants), the window in block `wb`**: another block than the output (`LEN` of
`inflate`), or the output itself with `beg == window`, the safe variant, `start == wsize` and `wnext == 0` (`LEN` of
`inflateBack`). It allocates nothing. -/
theorem inflate_fast_post_w (safe : Bool) (h : Heap) (i b : Nat) (z : ZStream) (st : InflateState) (start : UInt32)
    (ri : BRef) (oi bo oo : Nat) (A D : Array UInt8) (hmode : st.mode = ZlibNg.Inflate.LEN)
    (hz : h.streams i = some z) (hzs : z.state = some b) (hst : h.istate b = some st)
    (hbits : st.bits < 8) (hbo : bo ≠ b) (bd : Array UInt8) (hbd : h.bytes b = some bd) (wb woff : Nat)
    (wd : Array UInt8)
    (hW : wb ≠ bo ∨ (wb = bo ∧ woff = oo ∧ safe = true ∧ start = st.wsize ∧ st.wnext = 0))
    (hwv : st.window = .val (B wb woff)) (hwd : h.bytes wb = some wd) (hws : woff + st.wsize.toNat ≤ wd.size)
    (hwh : st.whave ≤ st.wsize) (hwn : st.wnext ≤ st.whave)
    (lc dc : CodePtr) (hlc : st.lencode = .val lc) (hdc : st.distcode = .val dc)
    (htab : FastTableOK h lc st.lenbits dc st.distbits)
    (hlnb : ∀ r o b', lc = .ref r o → r = .codes b' → b' ≠ bo) (hdnb : ∀ r o b', dc = .ref r o → r = .codes b' → b' ≠ bo)
    (hin15 : 15 ≤ z.avail_in) (hstart : z.avail_out ≤ start)
    (hroom : if safe then 3 ≤ z.avail_out else 260 ≤ z.avail_out)
    (hni : z.next_in = .ref ri oi) (hA : Space.get h ri = some A) (hAs : oi + z.avail_in.toNat ≤ A.size)
    (hno : z.next_out = .ref (.heap bo) (oo + (start - z.avail_out).toNat)) (hD : h.bytes bo = some D)
    (hDs : oo + start.toNat ≤ D.size) :
    Sat h (INFLATE_FAST safe (some i) start)
      (fun _ h' => FastPost safe h i b z st start ri oi bo oo h' ∧ h'.nextBlk = h.nextBlk) := by
  have hi15 : 15 ≤ z.avail_in.toNat := by rw [UInt32.le_iff_toNat_le] at hin15; simpa using hin15
  have hso : z.avail_out.toNat ≤ start.toNat := UInt32.le_iff_toNat_le.mp hstart
  have hsub : (start - z.avail_out).toNat = start.toNat - z.avail_out.toNat := UInt32.toNat_sub_of_le _ _ hstart
  have hav : (z.avail_in - (INFLATE_FAST_MIN_HAVE - 1)).toNat = z.avail_in.toNat - 14 :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp [INFLATE_FAST_MIN_HAVE]; omega)
  have hD' : Space.get h (BRef.heap bo) = some D := hD
  unfold INFLATE_FAST
  refine sat_bind_eq (ZlibNgF.Proof.InflateInv.ldStream_app hz) ?_
  rw [hzs, hni, hno]
  refine Sat.bind (Sat.mono (sat_add_g hA (by omega) _ (oi + (z.avail_in.toNat - 14)) (by rw [hav]; simp) (by omega)) ?_)
  rintro last H1 ⟨rfl, hH⟩
  rw [hH]
  refine Sat.bind (Sat.mono (sat_add_g hD' (by omega) _ oo (by rw [hsub]; simp; omega) (by omega)) ?_)
  rintro beg H1 ⟨rfl, hH⟩
  rw [hH]
  refine Sat.bind (Sat.mono (sat_add_g hD' (by omega) _ (oo + start.toNat) (by rw [hsub]; simp; omega) (by omega)) ?_)
  rintro sf H1 ⟨rfl, hH⟩
  rw [hH]
  extract_lets jp
  have hjp : Sat h (jp (B bo (if safe then oo + start.toNat - 2 else oo + start.toNat - 259)))
      (fun _ h' => FastPost safe h i b z st start ri oi bo oo h' ∧ h'.nextBlk = h.nextBlk) := by
    simp only [jp]
    refine sat_bind_eq (ZlibNgF.Proof.InflateInv.ldState_app hst) ?_
    refine sat_bind_eq (a := B wb woff) (H' := h) (by rw [hwv]; rfl) ?_
    refine sat_bind_eq (a := lc) (H' := h) (by rw [hlc]; rfl) ?_
    refine sat_bind_eq (a := dc) (H' := h) (by rw [hdc]; rfl) ?_
    obtain ⟨hlb, hdb, ⟨rl, ol, Tl, hlr, hlg, hlt⟩, ⟨rd, od, Td, hdr, hdg, hdt⟩⟩ := htab
    have hlb' : st.lenbits < 32 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hlb
    have hdb' : st.distbits < 32 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hdb
    refine sat_bind_eq (a := 1 <<< st.lenbits) (H' := h) (by simp [shl32, hlb']) ?_
    refine sat_bind_eq (a := 1 <<< st.distbits) (H' := h) (by simp [shl32, hdb']) ?_
    refine sat_bind_eq (a := h.garbage (2 ^ 42 + 1)) (H' := h) rfl ?_
    have hb8' : st.bits.toNat < 8 := by rw [UInt32.lt_iff_toNat_lt] at hbits; simpa using hbits
    have hb8 : st.bits.toUInt8.toNat = st.bits.toNat := u8_of_lt8 _ hbits
    have hS : start.toNat < 2 ^ 32 := start.toNat_lt
    let e : FE := ⟨bo, D.size, oo + (start.toNat - z.avail_out.toNat), oo + start.toNat, oo, ri, oi,
      oi + z.avail_in.toNat, st.bits.toNat, wb, woff, i, b, st, z, rl, ol, Tl, st.lenbits.toNat, rd, od, Td,
      st.distbits.toNat⟩
    let c : FC := ⟨some i, some b, Ptr.ref ri (oi + (z.avail_in.toNat - 14)), Ptr.ref (BRef.heap bo) oo,
      B bo (if safe = true then oo + start.toNat - 2 else oo + start.toNat - 259), Ptr.ref (BRef.heap bo) (oo + start.toNat),
      B wb woff, st.wsize, st.whave, st.wnext, lc, dc, 1 <<< st.lenbits - 1, 1 <<< st.distbits - 1, safe⟩
    have EV : EnvOK h c e := by
      refine ⟨rfl, rfl, hz, hst, hbo.symm, ⟨D, hD, rfl⟩, rfl, rfl, by dsimp only [e]; omega, by dsimp only [e]; omega,
        by dsimp only [e]; omega, by dsimp only [e]; omega, rfl, ?_, ?_,
        ⟨A, hA, by dsimp only [e]; omega⟩, by dsimp only [e]; omega, hb8', rfl, ⟨wd, hwd, hws⟩, ?_, hwh, hwn, hlr, hlg, hlt,
        fun x => and_mask_lt x _ hlb, fun b' hb' => hlnb rl ol b' hlr hb', hdr, hdg, hdt,
        fun x => and_mask_lt x _ hdb, fun b' hb' => hdnb rd od b' hdr hb'⟩
      · dsimp only [e, c]
        cases safe <;> simp at hroom ⊢ <;> rw [UInt32.le_iff_toNat_le] at hroom <;> simp at hroom <;> omega
      · show Ptr.ref ri _ = Ptr.ref ri (oi + z.avail_in.toNat - 14); congr 1; omega
      · rcases hW with hW | ⟨h1, h2, h3, h4, h5⟩
        · exact Or.inl hW
        · exact Or.inr ⟨h1, h2, h3, by dsimp only [e, c]; rw [h4], h5⟩
    refine Sat.bind (Sat.mono (sat_REFILL hA _ rfl (p := oi) (by omega) (by simp only; omega)) ?_)
    rintro l0 H1 ⟨hH, hd, hl0⟩
    rw [hH]
    refine Sat.bind (Sat.mono (sat_cdoWhile (LoopI h _ e) (loopM e) (LoopQ h safe e) (loop_step EV) ?_ ?_) ?_)
    · subst hl0
      have e56 := or56 st.bits.toUInt8 (by omega)
      refine ⟨rfl, e.o0, ⟨?_, by dsimp only [e]; omega, ?_⟩, ORun.refl hD rfl _ _, oi + (7 - st.bits.toUInt8.toNat / 8), rfl,
        by dsimp only [e]; omega, ?_, ?_, ?_⟩
      · show B bo _ = B bo _; congr 1; dsimp only [e]; rw [hsub]; omega
      · dsimp only [e, c]
        cases safe <;> simp at hroom ⊢ <;> rw [UInt32.le_iff_toNat_le] at hroom <;> simp at hroom <;> omega
      · dsimp only [e]; rw [e56]; omega
      · dsimp only; rw [e56]; omega
      · dsimp only [e]; rw [e56]; omega
    · subst hl0
      show e.s - offOf (B bo _) < fuel
      simp only [offOf, fuel]; dsimp only [e]; omega
    rintro ⟨lf, brk⟩ G ⟨po, hpo, hpo0, hpos, ⟨p, hp, hp0, hpE, hb64, hacc⟩, hcase⟩
    have hsi : h.istates b = some st := by
      have := hst; simp only [Heap.istate, hbd] at this; exact this
    obtain ⟨G1, st', z', r1, hG, hst', hzz, hprog⟩ : ∃ G1 st' z', RH h e G1 ∧
        G = { G1 with istates := upd G1.istates b (some st'), streams := upd G1.streams i (some z') } ∧
        (st' = st ∨ st' = { st with mode := BAD } ∨ st' = { st with mode := TYPE } ∨
          ∃ len dist : UInt32, safe = true ∧ 1 ≤ dist.toNat ∧
            st' = { st with mode := MATCH, length := len, was := len, offset := dist }) ∧
        (z' = z ∨ ∃ q, z' = { z with msg := q }) ∧
        lf.bits.toNat + 1 ≤ 8 * (p - oi) + st.bits.toNat := by
      rcases hcase with ⟨-, hlt, ⟨q, hq, hqs⟩, r⟩ | ⟨-, ⟨q, hq, hqs⟩, G1, st', z', r1, hG, hst', hzz⟩
      · have hqp : q = p := by rw [hp] at hq; cases hq; rfl
        subst hqp
        refine ⟨G, st, z, r, ?_, Or.inl rfl, Or.inl rfl, hqs⟩
        have e1 : upd G.istates b (some st) = G.istates := by
          rw [r.eq]; exact upd_self _ _ _ hsi
        have e2 : upd G.streams i (some z) = G.streams := by
          rw [r.eq]; exact upd_self _ _ _ hz
        rw [e1, e2]
      · have hqp : q = p := by rw [hp] at hq; cases hq; rfl
        subst hqp
        refine ⟨G1, st', z', r1, hG, ?_, hzz, hqs⟩
        rcases hst' with h1 | h1 | ⟨len, dist, hsf, hd1, h1⟩
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inr ⟨len, dist, hsf, hd1, h1⟩))
    subst hG
    dsimp only at hp hpo ⊢
    dsimp only [e] at hacc hpE hp0 hprog hpo0 hpos
    obtain ⟨A', hA', hsz⟩ := in_get r1 hA
    have hAG : Space.get { G1 with istates := upd G1.istates b (some st'), streams := upd G1.streams i (some z') } ri
        = some A' := by cases ri <;> exact hA'
    have hβ := shr3 lf.bits
    have hm8 := md8 lf.bits
    have hβ8 : lf.bits.toNat / 8 ≤ p - oi := by omega
    rw [hp]
    refine Sat.bind (Sat.mono (sat_add_g hAG (off := p) (by omega) _ (p - lf.bits.toNat / 8)
      (by rw [hβ]; simp; omega) (by omega)) ?_)
    rintro q H2 ⟨rfl, hH2⟩
    rw [hH2]
    have h64 : (lf.bits - ((lf.bits.toUInt32 >>> 3) <<< 3).toUInt8).toUInt32 < 64 := by
      rw [UInt32.lt_iff_toNat_lt]; simp only [UInt8.toNat_toUInt32, hm8]; simp; omega
    refine sat_bind_eq (a := (1 : UInt64) <<< (lf.bits - ((lf.bits.toUInt32 >>> 3) <<< 3).toUInt8).toUInt32.toUInt64)
      (by simp only [shl64, h64, ↓reduceIte]; rfl) ?_
    refine sat_bind_eq (ZlibNgF.Proof.InflateInv.ldStream_app (z := z') (by simp)) ?_
    have hE : p ≤ oi + z.avail_in.toNat := by omega
    refine Sat.bind (Sat.mono (sat_lt hAG (o1 := p - lf.bits.toNat / 8) (o2 := oi + (z.avail_in.toNat - 14))
      (by omega) (by omega)) ?_)
    rintro cb H3 ⟨rfl, hH3⟩
    rw [hH3]
    have hav32 : z.avail_in.toNat < 2 ^ 32 := z.avail_in.toNat_lt
    by_cases hlt : p - lf.bits.toNat / 8 < oi + (z.avail_in.toNat - 14)
    have hc : decide (p - lf.bits.toNat / 8 < oi + (z.avail_in.toNat - 14)) = true := by simpa using hlt
    rw [hc]; simp only [↓reduceIte]
    refine Sat.bind (Sat.mono (sat_diff_r hAG (o1 := oi + (z.avail_in.toNat - 14)) (o2 := p - lf.bits.toNat / 8)
      (by omega) (by omega) (by omega)) ?_)
    rintro d H4 ⟨rfl, hH4⟩
    rw [hH4]
    have hai : ((INFLATE_FAST_MIN_HAVE - 1).toUInt64 + (Int64.ofInt (((oi + (z.avail_in.toNat - 14) : Nat) : Int) -
        ((p - lf.bits.toNat / 8 : Nat) : Int))).toUInt64).toUInt32.toNat = oi + z.avail_in.toNat - (p - lf.bits.toNat / 8) := by
      rw [UInt64.toNat_toUInt32, UInt64.toNat_add, toNat_ofInt_nonneg _ (by omega) (by omega)]
      simp [INFLATE_FAST_MIN_HAVE]; omega
    generalize ((INFLATE_FAST_MIN_HAVE - 1).toUInt64 + (Int64.ofInt (((oi + (z.avail_in.toNat - 14) : Nat) : Int) -
        ((p - lf.bits.toNat / 8 : Nat) : Int))).toUInt64).toUInt32 = ai at hai ⊢
    refine sat_bind_eq (a := ai) rfl ?_
    rotate_left
    have hc : decide (p - lf.bits.toNat / 8 < oi + (z.avail_in.toNat - 14)) = false := by simpa using hlt
    rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.mono (sat_diff_r hAG (o1 := p - lf.bits.toNat / 8) (o2 := oi + (z.avail_in.toNat - 14))
      (by omega) (by omega) (by omega)) ?_)
    rintro d H4 ⟨rfl, hH4⟩
    rw [hH4]
    have hd14 : (Int64.ofInt (((p - lf.bits.toNat / 8 : Nat) : Int) -
        ((oi + (z.avail_in.toNat - 14) : Nat) : Int))).toUInt64.toNat = p - lf.bits.toNat / 8 - (oi + (z.avail_in.toNat - 14)) := by
      rw [toNat_ofInt_nonneg _ (by omega) (by omega)]; omega
    have hai : ((INFLATE_FAST_MIN_HAVE - 1).toUInt64 - (Int64.ofInt (((p - lf.bits.toNat / 8 : Nat) : Int) -
        ((oi + (z.avail_in.toNat - 14) : Nat) : Int))).toUInt64).toUInt32.toNat = oi + z.avail_in.toNat - (p - lf.bits.toNat / 8) := by
      rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hd14]; simp [INFLATE_FAST_MIN_HAVE]; omega), hd14]
      simp [INFLATE_FAST_MIN_HAVE]; omega
    generalize ((INFLATE_FAST_MIN_HAVE - 1).toUInt64 - (Int64.ofInt (((p - lf.bits.toNat / 8 : Nat) : Int) -
        ((oi + (z.avail_in.toNat - 14) : Nat) : Int))).toUInt64).toUInt32 = ai at hai ⊢
    refine sat_bind_eq (a := ai) rfl ?_
    all_goals
      obtain ⟨aG, haG, haGN⟩ := r1.cur
      have hGo : Space.get { G1 with istates := upd G1.istates b (some st'), streams := upd G1.streams i (some z') }
          (BRef.heap bo) = some aG := haG
      have haGN' : aG.size = D.size := haGN
      rw [hpo]
      refine Sat.bind (Sat.mono (sat_diff_r hGo (o1 := oo + start.toNat) (o2 := po) (by omega) (by omega)
        (by omega)) ?_)
      rintro d H5 ⟨rfl, hH5⟩
      rw [hH5]
      have hao : (Int64.ofInt (((oo + start.toNat : Nat) : Int) - (po : Int))).toUInt64.toUInt32.toNat =
          oo + start.toNat - po := by
        rw [UInt64.toNat_toUInt32, toNat_ofInt_nonneg _ (by omega) (by omega)]; omega
      generalize (Int64.ofInt (((oo + start.toNat : Nat) : Int) - (po : Int))).toUInt64.toUInt32 = ao at hao ⊢
      refine sat_bind_eq (by simp only [stStream, upd_same]; rfl) ?_
      have hbb : G1.bytes b = h.bytes b := r1.bytes_ne hbo.symm
      refine sat_bind_eq (by simp only [ldState, Heap.istate, hbb, hbd, upd_same]; rfl) ?_
      refine ⟨(), _, by simp only [stState, Heap.istate, hbb, hbd, upd_same]; rfl, ?_, ?_⟩
      have hbf : (lf.bits - ((lf.bits.toUInt32 >>> 3) <<< 3).toUInt8).toUInt32.toNat = lf.bits.toNat % 8 := by
        simp only [UInt8.toNat_toUInt32, hm8]
      have hao' : z.avail_out.toNat ≤ start.toNat := hso
      refine ⟨ai, ao, st'.mode,
        (lf.hold &&& (1 : UInt64) <<< (lf.bits - ((lf.bits.toUInt32 >>> 3) <<< 3).toUInt8).toUInt32.toUInt64 - 1).toUInt32.toUInt64,
        (lf.bits - ((lf.bits.toUInt32 >>> 3) <<< 3).toUInt8).toUInt32, st'.length, st'.was, st'.offset, z'.msg,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hbf, hai]; omega
      · rw [UInt32.le_iff_toNat_le]; omega
      · rw [UInt32.le_iff_toNat_le]; omega
      · show (upd (upd G1.streams i (some z')) i (some _)) i = some _
        rw [upd_same]
        have h1 : oi + (z.avail_in - ai).toNat = p - lf.bits.toNat / 8 := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]; omega
        have h2 : oo + (start - ao).toNat = po := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]; omega
        rw [h1, h2]
        rcases hzz with rfl | ⟨q, rfl⟩ <;> rfl
      · show (upd (upd G1.istates b (some st')) b (some _)) b = some _
        rw [upd_same]
        rcases hst' with rfl | rfl | rfl | ⟨len, dist, -, -, rfl⟩ <;> rfl
      · rcases hst' with rfl | rfl | rfl | ⟨len, dist, hsf, hd1, rfl⟩
        · exact Or.inl hmode
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr ⟨hsf, rfl, hd1⟩))
      · rw [UInt32.lt_iff_toNat_lt, hbf]; simp; omega
      · rw [hbf, hai, hao]
        split <;> omega
      · exact hbb
      · show G1.iallocs b = _; rw [r1.eq]
      · intro c hc; exact r1.bytes_ne hc
      · intro d hd
        obtain ⟨a0, a, h0, h1, s0, s1, -⟩ := r1.blk
        have : a0 = d := by
          have h0' : h.bytes bo = some a0 := h0
          rw [hd] at h0'; exact (Option.some.inj h0').symm
        subst this
        exact ⟨a, h1, by rw [s1, s0]⟩
      · rw [hno]
        refine frame_run (r1.mono (lo' := oo + (start - z.avail_out).toNat)
          (hi' := oo + (start - z.avail_out).toNat + z.avail_out.toNat) (by dsimp only [e]; omega)
          (by dsimp only [e]; omega)) hbo.symm _ _ ?_ ?_
        · intro j hj; simp only [upd_ne _ _ _ _ hj]
        · intro j hj; simp only [upd_ne _ _ _ _ hj]
      · show G1.nextBlk = h.nextBlk
        rw [r1.eq]
  cases safe
  · simp only [Bool.false_eq_true, ↓reduceIte] at hroom hjp
    have : 260 ≤ z.avail_out.toNat := by rw [UInt32.le_iff_toNat_le] at hroom; simpa using hroom
    refine Sat.bind (Sat.mono (sat_add_g hD' (by omega) _ (oo + start.toNat - 260) (by simp [INFLATE_FAST_MIN_LEFT]; omega) (by omega)) ?_)
    rintro p H1 ⟨rfl, hH⟩
    rw [hH]
    refine Sat.bind (Sat.mono (sat_add_g hD' (by omega) _ (oo + start.toNat - 259) (by omega) (by omega)) ?_)
    rintro p H1 ⟨rfl, hH⟩
    rw [hH]
    exact hjp
  · simp only [↓reduceIte] at hroom hjp
    have : 3 ≤ z.avail_out.toNat := by rw [UInt32.le_iff_toNat_le] at hroom; simpa using hroom
    refine Sat.bind (Sat.mono (sat_add_g hD' (by omega) _ (oo + start.toNat - 3) (by simp [INFLATE_FAST_MIN_SAFE]; omega) (by omega)) ?_)
    rintro p H1 ⟨rfl, hH⟩
    rw [hH]
    refine Sat.bind (Sat.mono (sat_add_g hD' (by omega) _ (oo + start.toNat - 2) (by omega) (by omega)) ?_)
    rintro p H1 ⟨rfl, hH⟩
    rw [hH]
    exact hjp

/-- **`INFLATE_FAST` (both variants) as `LEN` of `inflate` calls it**: the window in the state block. -/
theorem inflate_fast_post (safe : Bool) (h : Heap) (i b : Nat) (z : ZStream) (st : InflateState) (start : UInt32)
    (ri : BRef) (oi bo oo : Nat) (A D : Array UInt8) (hmode : st.mode = ZlibNg.Inflate.LEN)
    (hz : h.streams i = some z) (hzs : z.state = some b) (hst : h.istate b = some st)
    (hbits : st.bits < 8) (hbo : bo ≠ b) (woff : Nat) (wd : Array UInt8)
    (hwv : st.window = .val (B b woff)) (hwd : h.bytes b = some wd) (hws : woff + st.wsize.toNat ≤ wd.size)
    (hwh : st.whave ≤ st.wsize) (hwn : st.wnext ≤ st.whave)
    (lc dc : CodePtr) (hlc : st.lencode = .val lc) (hdc : st.distcode = .val dc)
    (htab : FastTableOK h lc st.lenbits dc st.distbits)
    (hlnb : ∀ r o b', lc = .ref r o → r = .codes b' → b' ≠ bo) (hdnb : ∀ r o b', dc = .ref r o → r = .codes b' → b' ≠ bo)
    (hin15 : 15 ≤ z.avail_in) (hstart : z.avail_out ≤ start)
    (hroom : if safe then 3 ≤ z.avail_out else 260 ≤ z.avail_out)
    (hni : z.next_in = .ref ri oi) (hA : Space.get h ri = some A) (hAs : oi + z.avail_in.toNat ≤ A.size)
    (hno : z.next_out = .ref (.heap bo) (oo + (start - z.avail_out).toNat)) (hD : h.bytes bo = some D)
    (hDs : oo + start.toNat ≤ D.size) :
    Sat h (INFLATE_FAST safe (some i) start) (fun _ h' => FastPost safe h i b z st start ri oi bo oo h') :=
  Sat.mono (inflate_fast_post_w safe h i b z st start ri oi bo oo A D hmode hz hzs hst hbits hbo wd hwd b woff wd
    (Or.inl hbo.symm) hwv hwd hws hwh hwn lc dc hlc hdc htab hlnb hdnb hin15 hstart hroom hni hA hAs hno hD hDs)
    (fun _ _ p => p.1)

end ZlibNgF.Proof.InffastMain
