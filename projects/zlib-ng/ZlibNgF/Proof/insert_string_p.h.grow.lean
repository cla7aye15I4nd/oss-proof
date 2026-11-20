import ZlibNgF.Proof.«insert_string_p.h.chain»
import ZlibNgF.Proof.«deflate_medium_tpl.h.insert»

/-!
# The hash chains under the insertion functions (`ZlibNgF`)

The byte-level instance of `chain_step` (`Proof/insert_string_p.h.chain.lean`) for the insertion functions that the
levels 2..8 run: `insert_knuth`, `insert_knuth_val`, `insert_knuth_one`, `insert_knuth_batch`,
`insert_knuth_stepped`, `insert_knuth_spread_static` and `insert_match`. Each runs on an `SH` heap with the layout
`HLay` and leaves bytes `d'` with `Grow d d' ho po w S`: every bound `lim` above the nonzero positions of `S` (the
positions the function inserts) turns the chain clauses `ChainSet d ... lim I` into `ChainSet d' ... lim J` for some
`J`.

The pieces: a `Pos` store `posStore p k v` writes the two bytes of `v` (little endian) at `p + 2 k` and nothing else
(`posStore_eq`); a `Pos` load returns `posAt` (`posLoad_eq`, `pv_toNat`); `prev` ends before `head` (`HLay.ph`);
`idx & W_MASK = idx % w_size` for the power of two `w_size` (`wmask_mod`); an inserted position below 65536 survives
`(Pos)idx`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InsertGrow
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNg.InsertStringP ZlibNg.InsertString ZlibNgF.Proof.InsertSafe ZlibNgF.Proof.InsertChain
open ZlibNgF.Proof.DeflateFacts (posAt)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateBits (WrIn addI_SH store_SH)
open ZlibNgF.Proof.DeflatePrime (lt_SH)

/-! ## Bytes -/

theorem get_set (d : Array UInt8) (o j : Nat) (v : UInt8) (h : o < d.size) :
    (d.set! o v)[j]! = if o = j then v else d[j]! := by
  by_cases e : o = j
  · subst e; simp [h]
  · simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, e, ite_false]

/-- The two bytes of `v` at `off` (little endian), as `zng_memwrite_2` stores them. -/
def wr2 (d : Array UInt8) (off : Nat) (v : UInt16) : Array UInt8 :=
  (d.set! off v.toUInt8).set! (off + 1) (v >>> 8).toUInt8

theorem wr2_size (d : Array UInt8) (off : Nat) (v : UInt16) : (wr2 d off v).size = d.size := by simp [wr2]

theorem wr2_get {d : Array UInt8} {off : Nat} (v : UInt16) (h : off + 1 < d.size) (j : Nat) :
    (wr2 d off v)[j]! =
      if j = off + 1 then (v >>> 8).toUInt8 else if j = off then v.toUInt8 else d[j]! := by
  unfold wr2
  rw [get_set _ _ _ _ (by simp; omega), get_set _ _ _ _ (by omega)]
  by_cases e1 : j = off + 1
  · simp [e1]
  · by_cases e2 : j = off
    · subst e2; simp
    · simp [Ne.symm e1, Ne.symm e2, e1, e2]

theorem wr2_wrin {d : Array UInt8} {off : Nat} (v : UInt16) (h : off + 1 < d.size) : WrIn d off (off + 2) (wr2 d off v) :=
  ⟨wr2_size _ _ _, fun j hj => by
    rw [wr2_get v h j, ite_eq_right (by omega), ite_eq_right (by omega)]⟩

theorem u16_bytes (v : UInt16) : v.toUInt8.toNat + 256 * (v >>> 8).toUInt8.toNat = v.toNat := by
  have := v.toNat_lt
  simp [UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem posAt_wr2_same {d : Array UInt8} {o k : Nat} (v : UInt16) (h : o + 2 * k + 1 < d.size) :
    posAt (wr2 d (o + 2 * k) v) o k = v.toNat := by
  unfold posAt
  rw [wr2_get v h, wr2_get v h, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl]
  exact u16_bytes v

theorem posAt_wr2_other {d : Array UInt8} {o k off : Nat} (v : UInt16) (h : off + 1 < d.size)
    (hd : o + 2 * k + 1 < off ∨ off + 1 < o + 2 * k) : posAt (wr2 d off v) o k = posAt d o k := by
  unfold posAt
  rw [wr2_get v h, wr2_get v h, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The value `memread2` reads at `o + 2 k`. -/
def pv (d : Array UInt8) (o k : Nat) : UInt16 := d[o + 2 * k]!.toUInt16 ||| (d[o + 2 * k + 1]!.toUInt16 <<< 8)

theorem pv_toNat (d : Array UInt8) (o k : Nat) : (pv d o k).toNat = posAt d o k := by
  unfold pv posAt
  generalize d[o + 2 * k]! = a
  generalize d[o + 2 * k + 1]! = c
  rw [UInt16.toNat_or, UInt16.toNat_shiftLeft]
  have ha := a.toNat_lt
  have hc := c.toNat_lt
  simp
  rw [Nat.mod_eq_of_lt (by omega), Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by simpa using ha),
    Nat.shiftLeft_eq]
  omega

theorem posAt_lt (d : Array UInt8) (o k : Nat) : posAt d o k < 65536 := by
  rw [← pv_toNat]; exact (pv d o k).toNat_lt

/-- `idx & W_MASK(s)` is `idx % w_size` for a power of two `w_size`. -/
theorem wmask_mod {st : DeflateState} (hp : ∃ k, st.w_size.toNat = 2 ^ k) (x : UInt32) :
    (x &&& W_MASK st).toNat = x.toNat % st.w_size.toNat := by
  obtain ⟨k, hk⟩ := hp
  unfold W_MASK
  rw [UInt32.toNat_and, UInt32.toNat_sub_of_le _ _ (by
    rw [UInt32.le_iff_toNat_le, hk]; simp; exact Nat.one_le_two_pow), hk]
  simp only [UInt32.toNat_one]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem memwrite2_eq {off : Nat} (v : UInt16) (h : off + 2 ≤ d.size) :
    memwrite2 (.ref (.heap b) off) v (SH H i z b st d) = .ok ((), SH H i z b st (wr2 d off v)) := by
  unfold memwrite2
  simp only [bind_app]
  rw [addI_SH 0 (by decide) (by omega)]
  simp only [Int.add_zero, Int.toNat_natCast]
  rw [store_SH _ (by omega)]
  simp only []
  rw [addI_SH 1 (by decide) (by simp; omega)]
  simp only [show ((off : Int) + 1).toNat = off + 1 by omega]
  rw [store_SH _ (by simp; omega)]
  rfl

theorem posStore_eq {po : Nat} (k : Nat) (v : UInt16) (hk : po + 2 * k + 2 ≤ d.size) :
    posStore (Ptr.ref (BRef.heap b) po) (k : Int) v (SH H i z b st d) =
      .ok ((), SH H i z b st (wr2 d (po + 2 * k) v)) := by
  have ea : Ptr.add (Ptr.ref (BRef.heap b) po) (2 * (k : Int)) (SH H i z b st d) =
      .ok (.ref (.heap b) (po + 2 * k), SH H i z b st d) := by
    rw [show 2 * (k : Int) = ((2 * k : Nat) : Int) by omega]
    exact addN_SH (2 * k) (by omega)
  simp only [posStore, bind_app, ea]
  exact memwrite2_eq v hk

theorem load_eq {off : Nat} (hk : off < d.size) :
    Ptr.load (R := BRef) (T := UInt8) (Ptr.ref (BRef.heap b) off) (SH H i z b st d) = .ok (d[off]!, SH H i z b st d) := by
  simp only [Ptr.load, ZlibNgF.Proof.InflateAlloc.space_get_heap, SH_bytes, hk, ↓reduceDIte, getElem!_pos d off hk]

theorem index8_eq {off : Nat} (k : Nat) (hk : off + k < d.size) :
    index8 (Ptr.ref (BRef.heap b) off) (k : Int) (SH H i z b st d) = .ok (d[off + k]!, SH H i z b st d) := by
  simp only [index8, Ptr.index, bind_app, addI_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off)
    (k : Int) (by omega) (by omega)]
  rw [show ((off : Int) + (k : Int)).toNat = off + k by omega]
  exact load_eq hk

theorem posLoad_eq {po : Nat} (k : Nat) (hk : po + 2 * k + 2 ≤ d.size) :
    posLoad (Ptr.ref (BRef.heap b) po) (k : Int) (SH H i z b st d) = .ok (pv d po k, SH H i z b st d) := by
  have ea : Ptr.add (Ptr.ref (BRef.heap b) po) (2 * (k : Int)) (SH H i z b st d) =
      .ok (.ref (.heap b) (po + 2 * k), SH H i z b st d) := by
    rw [show 2 * (k : Int) = ((2 * k : Nat) : Int) by omega]
    exact addN_SH (2 * k) (by omega)
  simp only [posLoad, bind_app, ea, memread2]
  have e0 : index8 (Ptr.ref (BRef.heap b) (po + 2 * k)) 0 (SH H i z b st d) =
      .ok (d[po + 2 * k + 0]!, SH H i z b st d) := index8_eq 0 (by omega)
  have e1 : index8 (Ptr.ref (BRef.heap b) (po + 2 * k)) 1 (SH H i z b st d) =
      .ok (d[po + 2 * k + 1]!, SH H i z b st d) := index8_eq 1 (by omega)
  rw [e0]; simp only []
  rw [e1]; rfl

end

/-- Two changes inside `[lo, hi)`. -/
theorem wtr {d d' d'' : Array UInt8} {lo hi : Nat} (a : WrIn d lo hi d') (c : WrIn d' lo hi d'') : WrIn d lo hi d'' :=
  a.trans c (Nat.le_refl _) (Nat.le_refl _)

/-! ## Growth of the chains -/

/-- From bytes `d` to `d'`, the chain clauses hold again for every bound above the nonzero positions of `S`. -/
def Grow (d d' : Array UInt8) (ho po w : Nat) (S : Nat → Prop) : Prop :=
  ∀ ss lim I, ChainSet d ho po w ss lim I → (∀ q, S q → q ≠ 0 → q < lim) → ∃ J, ChainSet d' ho po w ss lim J

theorem Grow.refl (d : Array UInt8) (ho po w : Nat) (S : Nat → Prop) : Grow d d ho po w S :=
  fun _ _ I C _ => ⟨I, C⟩

theorem Grow.trans {d1 d2 d3 : Array UInt8} {ho po w : Nat} {S1 S2 S : Nat → Prop} (a : Grow d1 d2 ho po w S1)
    (c : Grow d2 d3 ho po w S2) (h1 : ∀ q, S1 q → S q) (h2 : ∀ q, S2 q → S q) : Grow d1 d3 ho po w S := by
  intro ss lim I C hl
  obtain ⟨J, C'⟩ := a ss lim I C (fun q hq => hl q (h1 q hq))
  exact c ss lim J C' (fun q hq => hl q (h2 q hq))

theorem Grow.mono {d d' : Array UInt8} {ho po w : Nat} {S T : Nat → Prop} (a : Grow d d' ho po w S)
    (h : ∀ q, S q → T q) : Grow d d' ho po w T :=
  fun ss lim I C hl => a ss lim I C (fun q hq => hl q (h q hq))

/-- One insertion of `p` with hash `h`: `prev[p % w] = head[h]` (the two bytes `X`), then `head[h] = p` (`Y`). -/
theorem grow_ins {d : Array UInt8} {ho po w h p : Nat} {X Y : UInt16} (hw : 0 < w) (hph : po + 2 * w ≤ ho)
    (hd : ho + 131072 ≤ d.size) (hh : h < 65536) (hX : X.toNat = posAt d ho h) (hY : Y.toNat = p) :
    Grow d (wr2 (wr2 d (po + 2 * (p % w)) X) (ho + 2 * h) Y) ho po w (· = p) := by
  intro ss lim I C hl
  have hm := Nat.mod_lt p hw
  have hs1 : po + 2 * (p % w) + 1 < d.size := by omega
  have hs2 : ho + 2 * h + 1 < (wr2 d (po + 2 * (p % w)) X).size := by rw [wr2_size]; omega
  refine ⟨_, chain_step hw hh C ⟨?_, fun k hk hne => ?_, ?_, fun k hk hne => ?_⟩ (fun hp => hl p rfl hp)⟩
  · rw [posAt_wr2_same Y hs2, hY]
  · rw [posAt_wr2_other Y hs2 (by omega), posAt_wr2_other X hs1 (by omega)]
  · rw [posAt_wr2_other Y hs2 (by omega), posAt_wr2_same X hs1, hX]
  · rw [posAt_wr2_other Y hs2 (by omega), posAt_wr2_other X hs1 (by omega)]

/-- The step of an insertion function: bytes `d'` reached from `d` by stores below `U`, growing the chains by `S`. -/
def GPost {α : Type} (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8)
    (ho po w : Nat) (S : Nat → Prop) : α → Heap → Prop :=
  fun _ H' => ∃ d', H' = SH H i z b st d' ∧ WrIn d po (ho + 131072) d' ∧ Grow d d' ho po w S

/-- The bytes after the two stores of one insertion of `idx` with hash `h`. -/
theorem ins_bytes {d : Array UInt8} {po ho w : Nat} (idx m h : UInt32) (hw : 0 < w) (hm : m.toNat = idx.toNat % w)
    (hi : idx.toNat < 65536) (hh : h.toNat < 65536) (hho : ho + 131072 ≤ d.size) (hph : po + 2 * w ≤ ho) :
    WrIn d po (ho + 131072) (wr2 (wr2 d (po + 2 * m.toNat) (pv d ho h.toNat).toUInt32.toUInt16) (ho + 2 * h.toNat)
      idx.toUInt16) ∧
    Grow d (wr2 (wr2 d (po + 2 * m.toNat) (pv d ho h.toNat).toUInt32.toUInt16) (ho + 2 * h.toNat) idx.toUInt16)
      ho po w (· = idx.toNat) := by
  have hmw := Nat.mod_lt idx.toNat hw
  refine ⟨?_, ?_⟩
  · have a := wr2_wrin (d := d) (off := po + 2 * m.toNat) (pv d ho h.toNat).toUInt32.toUInt16 (by omega)
    have c := wr2_wrin (d := wr2 d (po + 2 * m.toNat) (pv d ho h.toNat).toUInt32.toUInt16)
      (off := ho + 2 * h.toNat) idx.toUInt16 (by rw [wr2_size]; omega)
    exact (a.widen (lo' := po) (hi' := ho + 131072) (by omega) (by omega)).trans
      (c.widen (lo' := po) (hi' := ho + 131072) (by omega) (by omega)) (Nat.le_refl _) (Nat.le_refl _)
  · rw [hm]
    exact grow_ins hw hph hho hh (by simp [pv_toNat]) (by simp; omega)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem ins_post {α : Type} {po ho w : Nat} (a : α) (idx m h : UInt32) (hw : 0 < w) (hm : m.toNat = idx.toNat % w)
    (hi : idx.toNat < 65536) (hh : h.toNat < 65536) (hho : ho + 131072 ≤ d.size) (hph : po + 2 * w ≤ ho) :
    GPost H i z b st d ho po w (· = idx.toNat) a (SH H i z b st (wr2 (wr2 d (po + 2 * m.toNat)
      (pv d ho h.toNat).toUInt32.toUInt16) (ho + 2 * h.toNat) idx.toUInt16)) :=
  ⟨_, rfl, (ins_bytes idx m h hw hm hi hh hho hph).1, (ins_bytes idx m h hw hm hi hh hho hph).2⟩

theorem skip_post {α : Type} {ho po w : Nat} (S : Nat → Prop) (a : α) : GPost H i z b st d ho po w S a (SH H i z b st d) :=
  ⟨d, rfl, WrIn.refl _ _ _, Grow.refl _ _ _ _ _⟩

/-- The conditional stores of one insertion of `idx` with hash `h`, after `head[h]` was read. -/
theorem ins_frag {po ho w : Nat} (idx m h : UInt32) (hw : 0 < w) (hm : m.toNat = idx.toNat % w)
    (hi : idx.toNat < 65536) (hh : h.toNat < 65536) (hho : ho + 131072 ≤ d.size) (hph : po + 2 * w ≤ ho) :
    Sat (SH H i z b st d) (if ((pv d ho h.toNat).toUInt32 != idx) = true then do
        posStore (Ptr.ref (BRef.heap b) po) (m.toNat : Int) (pv d ho h.toNat).toUInt32.toUInt16
        posStore (Ptr.ref (BRef.heap b) ho) (h.toNat : Int) idx.toUInt16
      else pure ()) (GPost H i z b st d ho po w (· = idx.toNat)) := by
  split
  · have hmw := Nat.mod_lt idx.toNat hw
    refine Sat.bind (Sat.of_eq (posStore_eq m.toNat _ (by omega)) ?_)
    exact Sat.of_eq (posStore_eq h.toNat _ (by rw [wr2_size]; omega)) (ins_post _ idx m h hw hm hi hh hho hph)
  · exact Sat.pure (skip_post _ _)

theorem insert_knuth_one_G {wo po ho w : Nat} (w_mask idx : UInt32) (hw : 0 < w)
    (hm : ∀ x : UInt32, (x &&& w_mask).toNat = x.toNat % w) (hho : ho + 131072 ≤ d.size)
    (hph : po + 2 * w ≤ ho) (hr : wo + idx.toNat + 4 ≤ d.size) (hi : idx.toNat < 65536) :
    Sat (SH H i z b st d) (insert_knuth_one (.ref (.heap b) ho) (.ref (.heap b) po) w_mask (.ref (.heap b) wo) idx)
      (GPost H i z b st d ho po w (· = idx.toNat)) := by
  unfold insert_knuth_one
  refine winRead4 idx.toNat hr (fun v => ?_)
  refine Sat.bind (Sat.of_eq (posLoad_eq _ (by have := knuth_lt v; omega)) ?_)
  exact ins_frag idx _ _ hw (hm idx) hi (knuth_lt v) hho hph

theorem insert_knuth_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str : UInt32) (hr : wo + str.toNat + 4 ≤ d.size) (hi : str.toNat < 65536) :
    Sat (SH H i z b st d) (insert_knuth (some b) (.ref (.heap b) wo) str)
      (GPost H i z b st d ho po st.w_size.toNat (· = str.toNat)) := by
  have hw := L.w1
  have hph := L.ph
  have hho := L.hd
  unfold insert_knuth
  refine winRead4 str.toNat hr (fun v => ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (posLoad_eq _ (by have := knuth_lt v; omega)) ?_)
  split
  · have hmw := Nat.mod_lt str.toNat hw
    have hm := wmask_mod hp str
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    simp only [L.prev]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq (str &&& W_MASK st).toNat _ (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [L.head]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq _ _ (by rw [wr2_size]; have := knuth_lt v; omega)) ?_)
    exact Sat.pure (ins_post _ str _ _ hw hm hi (knuth_lt v) hho hph)
  · exact Sat.pure (skip_post _ _)

theorem insert_knuth_val_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str val : UInt32) (hi : str.toNat < 65536) :
    Sat (SH H i z b st d) (insert_knuth_val (some b) str val)
      (GPost H i z b st d ho po st.w_size.toNat (· = str.toNat)) := by
  have hw := L.w1
  have hph := L.ph
  have hho := L.hd
  unfold insert_knuth_val
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (posLoad_eq _ (by have := knuth_lt val; omega)) ?_)
  split
  · have hmw := Nat.mod_lt str.toNat hw
    have hm := wmask_mod hp str
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    simp only [L.prev]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq (str &&& W_MASK st).toNat _ (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [L.head]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.of_eq (posStore_eq _ _ (by rw [wr2_size]; have := knuth_lt val; omega)) ?_)
    exact Sat.pure (ins_post _ str _ _ hw hm hi (knuth_lt val) hho hph)
  · exact Sat.pure (skip_post _ _)

/-- Loop invariant of the growing batch loop: the cursor at `base + k`, `idx = str + k`, the chains grown by
`[str, str + k)`. -/
def GI (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (ho po w base str count : Nat)
    (s : UInt32 × BPtr) (H' : Heap) : Prop :=
  ∃ k, k ≤ count ∧ s.2 = .ref (.heap b) (base + k) ∧ s.1.toNat = str + k ∧ ∃ d0 : Array UInt8,
    H' = SH H i z b st d0 ∧ WrIn d po (ho + 131072) d0 ∧ Grow d d0 ho po w (fun q => str ≤ q ∧ q < str + k)

theorem insert_knuth_batch_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str count : UInt32) (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H i z b st d) (insert_knuth_batch_static (some b) (.ref (.heap b) wo) str count)
      (GPost H i z b st d ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) := by
  unfold insert_knuth_batch_static
  refine Sat.bind (Sat.of_eq (addN_SH str.toNat (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (addN_SH count.toNat (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.prev]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have hpw := L.pw
  have hhd := L.hd
  have hw1 := L.w1
  have hph := L.ph
  refine Sat.bind (Sat.mono (sat_cwhile (s := (str, Ptr.ref (BRef.heap b) (wo + str.toNat)))
    (GI H i z b st d ho po st.w_size.toNat (wo + str.toNat) str.toNat count.toNat)
    (fun x => wo + str.toNat + count.toNat - poff x.2)
    (fun _ H' => GPost H i z b st d ho po st.w_size.toNat
      (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat) () H') ?_
    ⟨0, by omega, by simp, by simp, d, rfl, WrIn.refl _ _ _, Grow.refl _ _ _ _ _⟩ ?_) ?_)
  · rintro ⟨idx, p⟩ H1 ⟨k, hk, hp', hidx, d0, rfl, hs0, hg⟩
    have hs0' := hs0.1
    simp only at hp' hidx; subst hp'
    refine Sat.bind (Sat.of_eq (lt_SH (by omega) (by omega)) (Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩))
    · have hk' : k < count.toNat := by simpa using hc
      refine Sat.ro (memread4_SH (by omega)) (fun v => ?_)
      refine Sat.bind (Sat.of_eq (posLoad_eq (UPDATE_HASH_KNUTH v).toNat (by have := knuth_lt v; omega)) ?_)
      have hi1 : (idx + 1).toNat = str.toNat + (k + 1) := by rw [UInt32.toNat_add]; simp; omega
      split
      · have hm := wmask_mod hp idx
        have hmw := Nat.mod_lt idx.toNat (show 0 < st.w_size.toNat by omega)
        refine Sat.bind (Sat.of_eq (posStore_eq (idx &&& W_MASK st).toNat _ (by omega)) ?_)
        refine Sat.bind (Sat.of_eq (posStore_eq _ _ (by rw [wr2_size]; have := knuth_lt v; omega)) ?_)
        obtain ⟨w1, g1⟩ := ins_bytes (d := d0) (po := po) (ho := ho) idx (idx &&& W_MASK st) (UPDATE_HASH_KNUTH v)
          (show 0 < st.w_size.toNat by omega) hm (by omega) (knuth_lt v) (by omega) hph
        refine Sat.bind (Sat.of_eq (addN_SH 1 (by rw [wr2_size, wr2_size]; omega))
          (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], hi1, _, rfl, wtr hs0 w1,
            hg.trans g1 (fun q hq => ⟨hq.1, by omega⟩) (fun q hq => ⟨by omega, by omega⟩)⟩, ?_⟩))
        simp only [poff]; omega
      · refine Sat.bind (Sat.of_eq (addN_SH 1 (by omega)) (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], hi1,
          d0, rfl, hs0, hg.mono (fun q hq => ⟨hq.1, by omega⟩)⟩, ?_⟩))
        simp only [poff]; omega
    · have hk' : k = count.toNat := by simp at hc; omega
      subst hk'
      exact ⟨d0, rfl, hs0, hg⟩
  · simp only [poff, fuel]; have := count.toNat_lt; omega
  · rintro _ _ ⟨d', rfl, hs, hg⟩; exact Sat.pure ⟨d', rfl, hs, hg⟩

theorem stepped_lo (s j inc : Nat) : s ≤ (s * 65536 + j * inc) / 65536 :=
  (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)

theorem insert_knuth_stepped_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str count mi : UInt32) (hc : 2 ≤ count.toNat) (hm : 2 ≤ mi.toNat) (hs : str.toNat + count.toNat ≤ 65536)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth_stepped_static (some b) (.ref (.heap b) wo) str count mi)
      (GPost H i z b st d ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) := by
  unfold insert_knuth_stepped_static
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.prev]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have hpw := L.pw
  have hhd := L.hd
  have hw1 := L.w1
  have hph := L.ph
  generalize hI : (if count < mi then count else mi) = ins
  have hins : ins.toNat = min count.toNat mi.toNat := by
    subst hI; split
    · rename_i h; have := UInt32.lt_iff_toNat_lt.mp h; omega
    · rename_i h; have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h); omega
  have hiv : (ins - 1).toNat = ins.toNat - 1 := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
  have hne : ((ins - 1) == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; have := congrArg UInt32.toNat e; simp at this; omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  have hc1 : (count - 1).toNat = count.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
  have hsh : ((count - 1) <<< 16).toNat = (count.toNat - 1) * 65536 := by
    rw [UInt32.toNat_shiftLeft, hc1]; simp; omega
  have hiv1 : (ins - 1 - 1).toNat = ins.toNat - 2 := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hiv]; simp; omega)), hiv]; simp; omega
  have hnum : ((count - 1) <<< 16 + (ins - 1 - 1)).toNat = (count.toNat - 1) * 65536 + (ins.toNat - 2) := by
    rw [UInt32.toNat_add, hsh, hiv1]; omega
  generalize hF : ((count - 1) <<< 16 + (ins - 1 - 1)) / (ins - 1) = inc
  have hinc : inc.toNat = ((count.toNat - 1) * 65536 + (ins.toNat - 1 - 1)) / (ins.toNat - 1) := by
    rw [← hF, UInt32.toNat_div, hnum, hiv, Nat.sub_sub]
  have hs16 : (str <<< 16).toNat = str.toNat * 65536 := by
    rw [UInt32.toNat_shiftLeft]; simp
    have : str.toNat < 65536 := by omega
    omega
  refine Sat.bind (Sat.mono (sat_cwhile (s := ((0 : UInt32), str <<< 16))
    (fun (x : UInt32 × UInt32) H' => x.1.toNat ≤ ins.toNat ∧
      (x.1.toNat < ins.toNat → x.2.toNat = str.toNat * 65536 + x.1.toNat * inc.toNat) ∧
      ∃ d0 : Array UInt8, H' = SH H i z b st d0 ∧ WrIn d po (ho + 131072) d0 ∧
        Grow d d0 ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat))
    (fun x => ins.toNat - x.1.toNat) (fun _ H' => GPost H i z b st d ho po st.w_size.toNat
      (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat) () H') ?_
    ⟨by simp, fun _ => by simp [hs16], d, rfl, WrIn.refl _ _ _, Grow.refl _ _ _ _ _⟩ ?_) ?_)
  · rintro ⟨j, fp⟩ H1 ⟨hj, hfp, d0, rfl, hw, hg⟩
    have hd0 := hw.1
    refine Sat.pure ⟨fun hlt => ?_, fun _ => ⟨d0, rfl, hw, hg⟩⟩
    simp only [decide_eq_true_eq] at hlt
    have hlt' : j.toNat < ins.toNat := UInt32.lt_iff_toNat_lt.mp hlt
    have hfp' := hfp hlt'
    dsimp only at hfp' ⊢
    obtain ⟨hb1, hb2⟩ := ZlibNgF.Proof.MediumInsert.stepped_idx str.toNat count.toNat (ins.toNat - 1) j.toNat
      inc.toNat (by omega) (by omega) (by omega) (by rw [hinc]) (by omega)
    have hb0 := stepped_lo str.toNat j.toNat inc.toNat
    have hidx : (fp >>> 16).toNat = (str.toNat * 65536 + j.toNat * inc.toNat) / 65536 := by
      rw [UInt32.toNat_shiftRight, hfp']; simp [Nat.shiftRight_eq_div_pow]
    refine Sat.bind (Sat.of_eq (addN_SH (d := d0) (fp >>> 16).toNat (by omega)) ?_)
    refine Sat.ro (memread4_SH (by omega)) (fun v => ?_)
    refine Sat.bind (Sat.of_eq (posLoad_eq (UPDATE_HASH_KNUTH v).toNat (by have := knuth_lt v; omega)) ?_)
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    have hnext : j.toNat + 1 < ins.toNat → (fp + inc).toNat = str.toNat * 65536 + (j.toNat + 1) * inc.toNat := by
      intro h
      obtain ⟨hb3, -⟩ := ZlibNgF.Proof.MediumInsert.stepped_idx str.toNat count.toNat (ins.toNat - 1) (j.toNat + 1)
        inc.toNat (by omega) (by omega) (by omega) (by rw [hinc]) (by omega)
      rw [UInt32.toNat_add, hfp', Nat.succ_mul]
      rw [Nat.succ_mul] at hb3
      omega
    split
    · have hm := wmask_mod hp (fp >>> 16)
      have hmw := Nat.mod_lt (fp >>> 16).toNat (show 0 < st.w_size.toNat by omega)
      refine Sat.bind (Sat.of_eq (posStore_eq ((fp >>> 16) &&& W_MASK st).toNat _ (by omega)) ?_)
      refine Sat.bind (Sat.of_eq (posStore_eq _ _ (by rw [wr2_size]; have := knuth_lt v; omega)) ?_)
      obtain ⟨w1, g1⟩ := ins_bytes (d := d0) (po := po) (ho := ho) (fp >>> 16) ((fp >>> 16) &&& W_MASK st)
        (UPDATE_HASH_KNUTH v) (show 0 < st.w_size.toNat by omega) hm (by omega) (knuth_lt v) (by omega) hph
      exact Sat.pure ⟨⟨by rw [hj1]; omega, fun h => by rw [hj1] at h ⊢; exact hnext h, _, rfl,
        wtr hw w1, hg.trans g1 (fun q hq => hq) (fun q hq => ⟨by omega, by omega⟩)⟩, by rw [hj1]; omega⟩
    · exact Sat.pure ⟨⟨by rw [hj1]; omega, fun h => by rw [hj1] at h ⊢; exact hnext h, d0, rfl, hw, hg⟩,
        by rw [hj1]; omega⟩
  · simp only [fuel]; have := ins.toNat_lt; omega
  · rintro _ _ ⟨d', rfl, hs, hg⟩; exact Sat.pure ⟨d', rfl, hs, hg⟩

/-- `insert_knuth_spread_static(s, window, str, count, max_inserts)` with `count >= 2`, `max_inserts >= 2`: the
stepped insertion, or the positions `str`, `str + (count - 1) / 2` (when `max_inserts == 3`) and `str + count - 1`. -/
theorem insert_knuth_spread_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str count mi : UInt32) (hc : 2 ≤ count.toNat) (hm : 2 ≤ mi.toNat) (hs : str.toNat + count.toNat ≤ 65536)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth_spread_static (some b) (.ref (.heap b) wo) str count mi)
      (GPost H i z b st d ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) := by
  unfold insert_knuth_spread_static
  have hpw := L.pw
  have hhd := L.hd
  have hw1 := L.w1
  have hph := L.ph
  have hw0 : 0 < st.w_size.toNat := by omega
  by_cases h3 : mi > 3
  · rw [ite_eq_left h3]
    refine Sat.bind (Sat.mono (insert_knuth_stepped_G L hp str count mi hc hm hs hr) ?_)
    rintro _ _ q; exact Sat.pure q
  rw [ite_eq_right h3]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.prev]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have hmk := wmask_mod hp
  -- one insertion inside `[str, str + count)`, then the rest
  have one : ∀ (d0 : Array UInt8) (x : UInt32) {β : Type} {f : Unit → M β} {Q : β → Heap → Prop},
      d0.size = d.size → str.toNat ≤ x.toNat → x.toNat < str.toNat + count.toNat →
      (∀ d1, d1.size = d.size → WrIn d0 po (ho + 131072) d1 →
        Grow d0 d1 ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat) →
        Sat (SH H i z b st d1) (f ()) Q) →
      Sat (SH H i z b st d0) (insert_knuth_one (.ref (.heap b) ho) (.ref (.heap b) po) (W_MASK st)
        (.ref (.heap b) wo) x >>= f) Q := by
    intro d0 x β f Q hd0 hx1 hx2 k
    refine Sat.bind (Sat.mono (insert_knuth_one_G (d := d0) (wo := wo) (W_MASK st) x hw0 hmk (by omega) hph
      (by omega) (by omega)) ?_)
    rintro _ _ ⟨d1, rfl, w1, g1⟩
    exact k d1 (by rw [w1.1, hd0]) w1 (g1.mono (fun q hq => ⟨by omega, by omega⟩))
  have hcm1 : (count - 1).toNat = count.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
  have hlast : (str + count - 1).toNat = str.toNat + count.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [UInt32.toNat_add]; simp; omega)),
      UInt32.toNat_add]; simp; omega
  have hmid : (str + ((count - 1) >>> 1)).toNat = str.toNat + (count.toNat - 1) / 2 := by
    rw [UInt32.toNat_add, UInt32.toNat_shiftRight, hcm1]; simp [Nat.shiftRight_eq_div_pow]; omega
  have last : ∀ d2 : Array UInt8, d2.size = d.size → WrIn d po (ho + 131072) d2 →
      Grow d d2 ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat) →
      Sat (SH H i z b st d2) (insert_knuth_one (.ref (.heap b) ho) (.ref (.heap b) po) (W_MASK st)
        (.ref (.heap b) wo) (str + count - 1))
        (GPost H i z b st d ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) := by
    intro d2 hd2 w2 g2
    refine Sat.mono (insert_knuth_one_G (d := d2) (wo := wo) (W_MASK st) _ hw0 hmk (by omega) hph
      (by rw [hlast]; omega) (by rw [hlast]; omega)) ?_
    rintro _ _ ⟨d3, rfl, w3, g3⟩
    exact ⟨d3, rfl, wtr w2 w3, g2.trans g3 (fun q hq => hq) (fun q hq => by rw [hq, hlast]; omega)⟩
  refine one d str rfl (Nat.le_refl _) (by omega) (fun d1 hd1 w1 g1 => ?_)
  split
  · refine one d1 _ hd1 (by rw [hmid]; omega) (by rw [hmid]; omega) (fun d2 hd2 w2 g2 => ?_)
    exact last d2 hd2 (wtr w1 w2) (g1.trans g2 (fun q hq => hq) (fun q hq => hq))
  · exact last d1 hd1 w1 g1

/-- `insert_match(s, window, m, max_insert_count)` (as `MediumInsert.insert_match_SH`): the chains grow by
positions in `(m.strstart, m.strstart + m.match_length)`. -/
theorem insert_match_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (m : ZlibNg.DeflateMedium.Match)
    (mic : UInt32) (hm2 : 2 ≤ mic.toNat) (hm3 : mic.toNat ≤ 258) (hl : 2 ≤ m.match_length.toNat)
    (ho2 : m.orgstart.toNat ≤ m.strstart.toNat + m.match_length.toNat)
    (hs : m.strstart.toNat + m.match_length.toNat ≤ 65536)
    (hr : wo + m.strstart.toNat + m.match_length.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (ZlibNg.DeflateMedium.insert_match (some b) (.ref (.heap b) wo) m mic)
      (GPost H i z b st d ho po st.w_size.toNat
        (fun q => m.strstart.toNat < q ∧ q < m.strstart.toNat + m.match_length.toNat)) := by
  unfold ZlibNg.DeflateMedium.insert_match
  have hs1 : (m.strstart + 1).toNat = m.strstart.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  have hl1 : (m.match_length - 1).toNat = m.match_length.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
  have hmx : (2 * mic).toNat = 2 * mic.toNat := by rw [UInt32.toNat_mul]; simp; omega
  have tail : ∀ str cnt : UInt32, str.toNat + cnt.toNat = m.strstart.toNat + m.match_length.toNat →
      m.strstart.toNat < str.toNat →
      Sat (SH H i z b st d) (if cnt ≤ 2 * mic then do
          insert_knuth_batch (some b) (.ref (.heap b) wo) str cnt
          return ()
        else insert_knuth_stepped (some b) (.ref (.heap b) wo) str cnt mic)
        (GPost H i z b st d ho po st.w_size.toNat
          (fun q => m.strstart.toNat < q ∧ q < m.strstart.toNat + m.match_length.toNat)) := by
    intro str cnt he hlo
    split
    · refine Sat.bind (Sat.mono (insert_knuth_batch_G L hp str cnt (by omega) (by omega)) ?_)
      rintro _ _ ⟨d', rfl, hw, hg⟩
      exact Sat.pure ⟨d', rfl, hw, hg.mono (fun q hq => ⟨by omega, by omega⟩)⟩
    · rename_i hc
      have hc' : 2 * mic.toNat < cnt.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hc); omega
      refine Sat.mono (insert_knuth_stepped_G L hp str cnt mic (by omega) hm2 (by omega) (by omega)) ?_
      rintro _ _ ⟨d', rfl, hw, hg⟩
      exact ⟨d', rfl, hw, hg.mono (fun q hq => ⟨by omega, by omega⟩)⟩
  dsimp only
  split
  · rename_i hlt
    have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
    rw [hs1] at hlt'
    have he : (m.strstart + 1 + (m.match_length - 1)).toNat = m.strstart.toNat + m.match_length.toNat := by
      rw [UInt32.toNat_add, hs1, hl1]; omega
    have hd : (m.strstart + 1 + (m.match_length - 1) - m.orgstart).toNat =
        m.strstart.toNat + m.match_length.toNat - m.orgstart.toNat :=
      by rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), he]
    split
    · rename_i h0
      have h0' : m.strstart.toNat + m.match_length.toNat - m.orgstart.toNat = 0 := by
        rw [← hd]; have := congrArg UInt32.toNat (beq_iff_eq.mp h0); simpa using this
      have hm1 : (m.strstart + 1 + (m.match_length - 1) - 1).toNat = m.strstart.toNat + m.match_length.toNat - 1 :=
        by rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), he]; simp
      refine Sat.bind (Sat.mono (insert_knuth_G L hp _ (by rw [hm1]; omega) (by rw [hm1]; omega)) ?_)
      rintro _ _ ⟨d', rfl, hw, hg⟩
      exact Sat.pure ⟨d', rfl, hw, hg.mono (fun q hq => by rw [hq, hm1]; omega)⟩
    · exact tail _ _ (by rw [hd]; omega) (by omega)
  · exact tail _ _ (by rw [hs1, hl1]; omega) (by rw [hs1]; omega)

/-- `GPost` with any `ins_h` (the rolling hash). -/
def GPostH {α : Type} (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8)
    (ho po w : Nat) (S : Nat → Prop) : α → Heap → Prop :=
  fun _ H' => ∃ d' x, H' = SH H i z b { st with ins_h := x } d' ∧ WrIn d po (ho + 131072) d' ∧ Grow d d' ho po w S

theorem insert_roll_batch_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (str count : UInt32) (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H i z b st d) (insert_roll_batch_static (some b) (.ref (.heap b) wo) str count)
      (GPostH H i z b st d ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) := by
  unfold insert_roll_batch_static
  refine Sat.bind (Sat.of_eq (addN_SH str.toNat (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (addN_SH (STD_MIN_MATCH - 1).toNat (by simp [STD_MIN_MATCH]; omega)) ?_)
  have e2 : (STD_MIN_MATCH - 1).toNat = 2 := by decide
  rw [e2]
  refine Sat.bind (Sat.of_eq (addN_SH count.toNat (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.prev]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have hpw := L.pw
  have hhd := L.hd
  have hw1 := L.w1
  have hph := L.ph
  refine Sat.bind (Sat.mono (sat_cwhile (s := (str, Ptr.ref (BRef.heap b) (wo + str.toNat + 2), st.ins_h))
    (fun (x : UInt32 × BPtr × UInt32) H' => ∃ k, k ≤ count.toNat ∧ x.2.1 = .ref (.heap b) (wo + str.toNat + 2 + k) ∧
      x.1.toNat = str.toNat + k ∧ ∃ d0 : Array UInt8, H' = SH H i z b st d0 ∧ WrIn d po (ho + 131072) d0 ∧
      Grow d d0 ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + k))
    (fun x => wo + str.toNat + 2 + count.toNat - poff x.2.1)
    (fun _ H' => GPost H i z b st d ho po st.w_size.toNat
      (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat) () H') ?_
    ⟨0, by omega, by simp, by simp, d, rfl, WrIn.refl _ _ _, Grow.refl _ _ _ _ _⟩ ?_) ?_)
  · rintro ⟨idx, p, hh⟩ H1 ⟨k, hk, hp', hidx, d0, rfl, hs0, hg⟩
    have hs0' := hs0.1
    simp only at hp' hidx; subst hp'
    refine Sat.bind (Sat.of_eq (lt_SH (by omega) (by omega)) (Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩))
    · have hk' : k < count.toNat := by simpa using hc
      dsimp only
      refine Sat.ro (index8_SH 0 (by decide) (by simp; omega)) (fun c => ?_)
      refine Sat.bind (Sat.of_eq (posLoad_eq (UPDATE_HASH_ROLL hh c.toUInt32).toNat
        (by have := roll_lt hh c.toUInt32; omega)) ?_)
      have hi1 : (idx + 1).toNat = str.toNat + (k + 1) := by rw [UInt32.toNat_add]; simp; omega
      split
      · have hm := wmask_mod hp idx
        have hmw := Nat.mod_lt idx.toNat (show 0 < st.w_size.toNat by omega)
        refine Sat.bind (Sat.of_eq (posStore_eq (idx &&& W_MASK st).toNat _ (by omega)) ?_)
        refine Sat.bind (Sat.of_eq (posStore_eq _ _ (by rw [wr2_size]; have := roll_lt hh c.toUInt32; omega)) ?_)
        obtain ⟨w1, g1⟩ := ins_bytes (d := d0) (po := po) (ho := ho) idx (idx &&& W_MASK st)
          (UPDATE_HASH_ROLL hh c.toUInt32) (show 0 < st.w_size.toNat by omega) hm (by omega) (roll_lt _ _)
          (by omega) hph
        refine Sat.bind (Sat.of_eq (addN_SH 1 (by rw [wr2_size, wr2_size]; omega))
          (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], hi1, _, rfl, wtr hs0 w1,
            hg.trans g1 (fun q hq => ⟨hq.1, by omega⟩) (fun q hq => ⟨by omega, by omega⟩)⟩, ?_⟩))
        simp only [poff]; omega
      · refine Sat.bind (Sat.of_eq (addN_SH 1 (by omega)) (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], hi1,
          d0, rfl, hs0, hg.mono (fun q hq => ⟨hq.1, by omega⟩)⟩, ?_⟩))
        simp only [poff]; omega
    · have hk' : k = count.toNat := by simp at hc; omega
      subst hk'
      exact ⟨d0, rfl, hs0, hg⟩
  · simp only [poff, fuel]; have := count.toNat_lt; omega
  · rintro ⟨_, _, hh⟩ _ ⟨d', rfl, hs, hg⟩
    exact Sat.of_eq (wrD_SH _) ⟨d', hh, rfl, hs, hg⟩

/-- `insert_batch(s, window, str, count)` through the function pointer, for the two values that levels 2..9 set
(`insert_knuth_batch`, `insert_roll_batch`). -/
theorem call_insert_batch_G {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hp : ∃ k, st.w_size.toNat = 2 ^ k)
    (f : InsertBatchFn) (hf : f ≠ .insert_knuth_batch_head) (str count : UInt32)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H i z b st d) (call_insert_batch f (some b) (.ref (.heap b) wo) str count)
      (GPostH H i z b st d ho po st.w_size.toNat (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) := by
  cases f
  · exact Sat.mono (insert_knuth_batch_G L hp str count hr hs) (fun _ _ ⟨d', e, w, g⟩ => ⟨d', st.ins_h, e, w, g⟩)
  · exact absurd rfl hf
  · exact insert_roll_batch_G L hp str count hr hs

end

/-! ## `ChainOk` -/

/-- `ChainOk` survives growth of the chains by `S`, with a state that keeps `level`, `strategy`, `head`, `prev`,
`w_size`, does not move `strstart` back, does not lower `chainLim`, and has every nonzero position of `S` below its
`chainLim`. -/
theorem ChainOk.grow {b : Nat} {d d' : Array UInt8} {st st' : DeflateState} {S : Nat → Prop}
    (C : ZlibNgF.Proof.DeflateFacts.ChainOk b d st)
    (g : ∀ ho po, st.head = .val (.ref (.heap b) ho) → st.prev = .val (.ref (.heap b) po) →
      Grow d d' ho po st.w_size.toNat S)
    (e1 : st'.level = st.level) (e2 : st'.strategy = st.strategy) (e3 : st'.head = st.head)
    (e4 : st'.prev = st.prev) (e5 : st'.w_size = st.w_size) (hss : st.strstart.toNat ≤ st'.strstart.toNat)
    (hl : ZlibNgF.Proof.DeflateFacts.chainLim st ≤ ZlibNgF.Proof.DeflateFacts.chainLim st')
    (hS : ∀ q, S q → q ≠ 0 → q < ZlibNgF.Proof.DeflateFacts.chainLim st') :
    ZlibNgF.Proof.DeflateFacts.ChainOk b d' st' := by
  intro h1 h2
  rw [e1] at h1; rw [e1, e2] at h2
  obtain ⟨I, ho, po, hh, hp, c1, c2, c3⟩ := C h1 h2
  have CS : ChainSet d ho po st.w_size.toNat st.strstart.toNat (ZlibNgF.Proof.DeflateFacts.chainLim st) I :=
    ⟨c1, c2, c3⟩
  obtain ⟨J, CJ⟩ := g ho po hh hp _ _ _ (chain_mono CS hss hl) hS
  refine ⟨J, ho, po, by rw [e3]; exact hh, by rw [e4]; exact hp, CJ.c1, CJ.c2, fun p hp' hs => ?_⟩
  rw [e5]; exact CJ.c3 p hp' (by rw [← e5]; exact hs)

end ZlibNgF.Proof.InsertGrow
