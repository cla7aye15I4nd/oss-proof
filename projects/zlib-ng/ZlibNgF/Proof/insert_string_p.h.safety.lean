import ZlibNgF.Proof.«insert_string_p.h.base»
import ZlibNgF.Proof.«deflate.c.prime»

/-!
# Safety of the hash insertion functions (`ZlibNgF`)

Runs on `SH` heaps. With the layout of `alloc_deflate` (`HLay`: window, `prev` with `w_size` entries, `head` with
`HASH_SIZE` entries in block `b`), every insertion function of `insert_string_p.h` / `insert_string.c` that the
window layer calls (`insert_knuth`, `insert_knuth_head`, `insert_roll`, `insert_knuth_val`, `insert_knuth_val_head`,
`insert_knuth_one`, the batches `insert_knuth_batch`, `insert_knuth_batch_head`, `insert_roll_batch` and the call
through `s->insert_batch`) does not fault when its window reads `[str, str + count + 3)` lie in the block: the hash
index is below `HASH_SIZE` (`knuth_lt`, `roll_lt`) and the `prev` index is masked by `W_MASK` (`mask_lt`). Each
changes only the block's bytes below the end of `head` (keeping their size) and, for the rolling hash, `ins_h`
(`IKeep`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InsertSafe
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNg.InsertStringP ZlibNg.InsertString
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflatePrime (lt_SH)
open ZlibNgF.Proof.DeflateBits (WrIn)

/-- The hash tables of the state `st` in block `b`, whose bytes have size `D`. -/
structure HLay (b D : Nat) (st : DeflateState) (wo po ho : Nat) : Prop where
  win : st.window = .val (.ref (.heap b) wo)
  prev : st.prev = .val (.ref (.heap b) po)
  head : st.head = .val (.ref (.heap b) ho)
  w1 : 1 ≤ st.w_size.toNat
  pw : po + 2 * st.w_size.toNat ≤ D
  hd : ho + 131072 ≤ D
  ph : po + 2 * st.w_size.toNat ≤ ho

/-- A step that changes block `b`'s bytes below `U` (keeping their size) and `ins_h` only. -/
def IKeep {α : Type} (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (U : Nat) :
    α → Heap → Prop :=
  fun _ H' => ∃ d' x, H' = SH H i z b { st with ins_h := x } d' ∧ WrIn d 0 U d'

theorem st_insh (st : DeflateState) : { st with ins_h := st.ins_h } = st := rfl

theorem BKeep.ikeep {α : Type} {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    {U : Nat} {a : α} {H' : Heap} (k : BKeep H i z b st d U a H') : IKeep H i z b st d U a H' := by
  obtain ⟨d', rfl, hs⟩ := k; exact ⟨d', st.ins_h, rfl, hs⟩

def poff : BPtr → Nat
  | .ref _ o => o
  | .null => 0

/-- Loop invariant of the batch loops: the cursor at `base + k`, `k ≤ count`, the bytes of `d` changed below `U`. -/
def BI {σ : Type} (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (U base count : Nat)
    (cur : σ → BPtr) (s : σ) (H' : Heap) : Prop :=
  ∃ k, k ≤ count ∧ cur s = .ref (.heap b) (base + k) ∧ ∃ d0 : Array UInt8, H' = SH H i z b st d0 ∧ WrIn d 0 U d0

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- The conditional `prev` / `head` stores of an insertion. -/
theorem ins_if {po ho : Nat} (c : Bool) (m h : UInt32) (v1 v2 : UInt16) (W : Nat) (hm : m.toNat < W)
    (hh : h.toNat < 65536) (hpw : po + 2 * W ≤ d.size) (hho : ho + 131072 ≤ d.size) (hph : po + 2 * W ≤ ho) :
    Sat (SH H i z b st d) (if c = true then do
        posStore (Ptr.ref (BRef.heap b) po) (m.toNat : Int) v1
        posStore (Ptr.ref (BRef.heap b) ho) (h.toNat : Int) v2
      else pure ()) (BKeep H i z b st d (ho + 131072)) := by
  split
  · refine BKeep.bind (Sat.mono (posStore_SH (U := ho + 131072) m.toNat v1 (by omega) (by omega)) ?_)
    rintro _ _ ⟨d', rfl, hs⟩
    exact ⟨d', rfl, hs, fun d0 hd0 => posStore_SH (U := ho + 131072) h.toNat v2 (by have := hd0.1; omega) (by omega)⟩
  · exact Sat.pure ⟨d, rfl, WrIn.refl _ _ _⟩

/-- A read of a `Pos` of `head` followed by the rest `f`. -/
theorem headLoad {α : Type} {ho : Nat} (h : UInt32) (hh : h.toNat < 65536) (hho : ho + 131072 ≤ d.size)
    {f : UInt16 → M α} {Q : α → Heap → Prop} (k : ∀ v, Sat (SH H i z b st d) (f v) Q) :
    Sat (SH H i z b st d) (posLoad (Ptr.ref (BRef.heap b) ho) (h.toNat : Int) >>= f) Q :=
  Sat.ro (posLoad_SH h.toNat (by omega)) k

theorem winRead4 {α : Type} {wo : Nat} (n : Nat) (hn : wo + n + 4 ≤ d.size)
    {f : UInt32 → M α} {Q : α → Heap → Prop} (k : ∀ v, Sat (SH H i z b st d) (f v) Q) :
    Sat (SH H i z b st d) ((Ptr.ref (BRef.heap b) wo).add (n : Int) >>= fun p => memread4 p >>= f) Q := by
  refine Sat.bind (Sat.of_eq (addN_SH n (by omega)) ?_)
  exact Sat.ro (memread4_SH (by omega)) k

theorem insert_knuth_one_SH {wo po ho : Nat} (w_mask idx : UInt32) (W : Nat)
    (hm : ∀ x : UInt32, (x &&& w_mask).toNat < W) (hpw : po + 2 * W ≤ d.size) (hho : ho + 131072 ≤ d.size)
    (hph : po + 2 * W ≤ ho) (hr : wo + idx.toNat + 4 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth_one (.ref (.heap b) ho) (.ref (.heap b) po) w_mask (.ref (.heap b) wo) idx)
      (BKeep H i z b st d (ho + 131072)) := by
  unfold insert_knuth_one
  refine winRead4 idx.toNat hr (fun v => ?_)
  refine headLoad _ (knuth_lt v) hho (fun hv => ?_)
  exact ins_if _ _ _ _ _ W (hm idx) (knuth_lt v) hpw hho hph

theorem insert_knuth_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str : UInt32)
    (hr : wo + str.toNat + 4 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth (some b) (.ref (.heap b) wo) str) (BKeep H i z b st d (ho + 131072)) := by
  unfold insert_knuth
  refine winRead4 str.toNat hr (fun v => ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine headLoad _ (knuth_lt v) L.hd (fun hv => ?_)
  split
  · refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    simp only [L.prev]
    refine Sat.bind (Sat.pure ?_)
    refine BKeep.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d) (po := po) (str &&& W_MASK st).toNat _ (by have := mask_lt str st.w_size L.w1; have := L.pw; unfold W_MASK; omega) (by have := mask_lt str st.w_size L.w1; have := L.ph; unfold W_MASK; omega)) ?_)
    rintro _ _ ⟨d', rfl, hs⟩
    refine ⟨d', rfl, hs, fun d0 hd0 => ?_⟩
    have hd0s := hd0.1
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [L.head]
    refine Sat.bind (Sat.pure ?_)
    refine BKeep.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d0) (po := ho) (UPDATE_HASH_KNUTH v).toNat _ (by have := knuth_lt v; have := L.hd; omega) (by have := knuth_lt v; omega)) ?_)
    rintro _ _ ⟨d'', rfl, hs'⟩
    exact ⟨d'', rfl, hs', fun d1 _ => Sat.pure ⟨d1, rfl, WrIn.refl _ _ _⟩⟩
  · exact Sat.pure ⟨d, rfl, WrIn.refl _ _ _⟩

theorem insert_knuth_batch_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str count : UInt32)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth_batch_static (some b) (.ref (.heap b) wo) str count) (BKeep H i z b st d (ho + 131072)) := by
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
  refine Sat.bind (Sat.mono (sat_cwhile (s := (str, Ptr.ref (BRef.heap b) (wo + str.toNat))) (BI H i z b st d (ho + 131072) (wo + str.toNat) count.toNat (fun x : UInt32 × BPtr => x.2))
    (fun x => wo + str.toNat + count.toNat - poff x.2) (fun _ H' => BKeep H i z b st d (ho + 131072) () H') ?_ ⟨0, by omega, by simp, d, rfl, WrIn.refl _ _ _⟩ ?_) ?_)
  · rintro ⟨idx, p⟩ H1 ⟨k, hk, hp, d0, rfl, hs⟩
    have hs0 := hs.1
    simp only at hp; subst hp
    refine Sat.bind (Sat.of_eq (lt_SH (by omega) (by omega)) (Sat.pure ⟨fun hc => ?_, fun _ => ⟨d0, rfl, hs⟩⟩))
    have hk' : k < count.toNat := by simpa using hc
    refine Sat.ro (memread4_SH (by omega)) (fun v => ?_)
    refine Sat.ro (posLoad_SH (UPDATE_HASH_KNUTH v).toNat (by have := knuth_lt v; omega)) (fun hv => ?_)
    split
    · refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d0) (po := po) (idx &&& W_MASK st).toNat _ (by have := mask_lt idx st.w_size hw1; unfold W_MASK; omega) (by have := mask_lt idx st.w_size hw1; have := L.ph; unfold W_MASK; omega)) ?_)
      rintro _ _ ⟨d1, rfl, hs1⟩
      have hs1' := hs1.1
      refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d1) (po := ho) (UPDATE_HASH_KNUTH v).toNat _ (by have := knuth_lt v; omega) (by have := knuth_lt v; omega)) ?_)
      rintro _ _ ⟨d2, rfl, hs2⟩
      have hs2' := hs2.1
      refine Sat.bind (Sat.of_eq (addN_SH 1 (by omega)) (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], d2, rfl, wr_tr hs (wr_tr hs1 hs2)⟩, ?_⟩))
      simp only [poff]; omega
    · refine Sat.bind (Sat.of_eq (addN_SH 1 (by omega)) (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], d0, rfl, hs⟩, ?_⟩))
      simp only [poff]; omega
  · simp only [poff, fuel]; have := count.toNat_lt; omega
  · rintro _ _ ⟨d', rfl, hs⟩; exact Sat.pure ⟨d', rfl, hs⟩

theorem insert_knuth_head_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str : UInt32)
    (hr : wo + str.toNat + 4 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth_head (some b) (.ref (.heap b) wo) str) (BKeep H i z b st d (ho + 131072)) := by
  unfold insert_knuth_head
  refine winRead4 str.toNat hr (fun v => ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine headLoad _ (knuth_lt v) L.hd (fun hv => ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d) (po := ho) (UPDATE_HASH_KNUTH v).toNat _
    (by have := knuth_lt v; have := L.hd; omega) (by have := knuth_lt v; omega)) ?_)
  rintro _ _ ⟨d', rfl, hs⟩
  exact Sat.pure ⟨d', rfl, hs⟩

theorem insert_knuth_val_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str val : UInt32) :
    Sat (SH H i z b st d) (insert_knuth_val (some b) str val) (BKeep H i z b st d (ho + 131072)) := by
  unfold insert_knuth_val
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine headLoad _ (knuth_lt val) L.hd (fun hv => ?_)
  split
  · refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    simp only [L.prev]
    refine Sat.bind (Sat.pure ?_)
    refine BKeep.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d) (po := po) (str &&& W_MASK st).toNat _
      (by have := mask_lt str st.w_size L.w1; have := L.pw; unfold W_MASK; omega) (by have := mask_lt str st.w_size L.w1; have := L.ph; unfold W_MASK; omega)) ?_)
    rintro _ _ ⟨d', rfl, hs⟩
    refine ⟨d', rfl, hs, fun d0 hd0 => ?_⟩
    have hd0s := hd0.1
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [L.head]
    refine Sat.bind (Sat.pure ?_)
    refine BKeep.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d0) (po := ho) (UPDATE_HASH_KNUTH val).toNat _
      (by have := knuth_lt val; have := L.hd; omega) (by have := knuth_lt val; omega)) ?_)
    rintro _ _ ⟨d'', rfl, hs'⟩
    exact ⟨d'', rfl, hs', fun d1 _ => Sat.pure ⟨d1, rfl, WrIn.refl _ _ _⟩⟩
  · exact Sat.pure ⟨d, rfl, WrIn.refl _ _ _⟩

theorem insert_knuth_val_head_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str val : UInt32) :
    Sat (SH H i z b st d) (insert_knuth_val_head (some b) str val) (BKeep H i z b st d (ho + 131072)) := by
  unfold insert_knuth_val_head
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine headLoad _ (knuth_lt val) L.hd (fun hv => ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d) (po := ho) (UPDATE_HASH_KNUTH val).toNat _
    (by have := knuth_lt val; have := L.hd; omega) (by have := knuth_lt val; omega)) ?_)
  rintro _ _ ⟨d', rfl, hs⟩
  exact Sat.pure ⟨d', rfl, hs⟩

theorem insert_knuth_batch_head_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str count : UInt32)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth_batch_head_static (some b) (.ref (.heap b) wo) str count)
      (BKeep H i z b st d (ho + 131072)) := by
  unfold insert_knuth_batch_head_static
  refine Sat.bind (Sat.of_eq (addN_SH str.toNat (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (addN_SH count.toNat (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  have hhd := L.hd
  refine Sat.bind (Sat.mono (sat_cwhile (s := (str, Ptr.ref (BRef.heap b) (wo + str.toNat)))
    (BI H i z b st d (ho + 131072) (wo + str.toNat) count.toNat (fun x : UInt32 × BPtr => x.2))
    (fun x => wo + str.toNat + count.toNat - poff x.2) (fun _ H' => BKeep H i z b st d (ho + 131072) () H') ?_
    ⟨0, by omega, by simp, d, rfl, WrIn.refl _ _ _⟩ ?_) ?_)
  · rintro ⟨idx, p⟩ H1 ⟨k, hk, hp, d0, rfl, hs⟩
    have hs0 := hs.1
    simp only at hp; subst hp
    refine Sat.bind (Sat.of_eq (lt_SH (by omega) (by omega)) (Sat.pure ⟨fun hc => ?_, fun _ => ⟨d0, rfl, hs⟩⟩))
    have hk' : k < count.toNat := by simpa using hc
    refine Sat.ro (memread4_SH (by omega)) (fun v => ?_)
    refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d0) (po := ho) (UPDATE_HASH_KNUTH v).toNat _
      (by have := knuth_lt v; omega) (by have := knuth_lt v; omega)) ?_)
    rintro _ _ ⟨d2, rfl, hs2⟩
    have hs2' := hs2.1
    refine Sat.bind (Sat.of_eq (addN_SH 1 (by omega)) (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], d2, rfl,
      wr_tr hs hs2⟩, ?_⟩))
    simp only [poff]; omega
  · simp only [poff, fuel]; have := count.toNat_lt; omega
  · rintro _ _ ⟨d', rfl, hs⟩; exact Sat.pure ⟨d', rfl, hs⟩


theorem HLay.insh {wo po ho D : Nat} (L : HLay b D st wo po ho) (x : UInt32) :
    HLay b D { st with ins_h := x } wo po ho := ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩

theorem insert_roll_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str : UInt32)
    (hr : wo + str.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (insert_roll (some b) (.ref (.heap b) wo) str) (IKeep H i z b st d (ho + 131072)) := by
  unfold insert_roll
  refine Sat.bind (Sat.of_eq (addN_SH str.toNat (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (addN_SH (STD_MIN_MATCH - 1).toNat (by simp [STD_MIN_MATCH]; omega)) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.ro (index8_SH 0 (by decide) (by simp [STD_MIN_MATCH]; omega)) (fun c => ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have L' := L.insh (UPDATE_HASH_ROLL st.ins_h c.toUInt32)
  generalize hs1 : { st with ins_h := UPDATE_HASH_ROLL st.ins_h c.toUInt32 } = st1 at L' ⊢
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L'.head]
  refine headLoad _ (roll_lt _ _) L'.hd (fun hv => ?_)
  split
  · refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    simp only [L'.prev]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d) (po := po) (str &&& W_MASK st1).toNat _
      (by have := mask_lt str st1.w_size L'.w1; have := L'.pw; unfold W_MASK; omega) (by have := mask_lt str st1.w_size L'.w1; have := L'.ph; unfold W_MASK; omega)) ?_)
    rintro _ _ ⟨d', rfl, hs⟩
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    simp only [L'.head]
    refine Sat.bind (Sat.pure ?_)
    refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d') (po := ho) (UPDATE_HASH_ROLL st.ins_h c.toUInt32).toNat _
      (by have := roll_lt st.ins_h c.toUInt32; have := L'.hd; have := hs.1; omega)
      (by have := roll_lt st.ins_h c.toUInt32; omega)) ?_)
    rintro _ _ ⟨d'', rfl, hs'⟩
    subst hs1
    exact Sat.pure ⟨d'', _, rfl, wr_tr hs hs'⟩
  · subst hs1
    exact Sat.pure ⟨d, _, rfl, WrIn.refl _ _ _⟩

/-- Loop invariant of `insert_roll_batch`: as `BI`, with any `ins_h`. -/
def RI (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (U base count : Nat)
    (s : UInt32 × BPtr × UInt32) (H' : Heap) : Prop :=
  ∃ k, k ≤ count ∧ s.2.1 = .ref (.heap b) (base + k) ∧ ∃ d0 : Array UInt8, H' = SH H i z b st d0 ∧ WrIn d 0 U d0

theorem insert_roll_batch_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str count : UInt32)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (insert_roll_batch_static (some b) (.ref (.heap b) wo) str count)
      (IKeep H i z b st d (ho + 131072)) := by
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
  refine Sat.bind (Sat.mono (sat_cwhile (s := (str, Ptr.ref (BRef.heap b) (wo + str.toNat + 2), st.ins_h))
    (RI H i z b st d (ho + 131072) (wo + str.toNat + 2) count.toNat)
    (fun x => wo + str.toNat + 2 + count.toNat - poff x.2.1)
    (fun x H' => BKeep H i z b st d (ho + 131072) () H') ?_ ⟨0, by omega, by simp, d, rfl, WrIn.refl _ _ _⟩ ?_) ?_)
  · rintro ⟨idx, p, hh⟩ H1 ⟨k, hk, hp, d0, rfl, hs⟩
    have hs0 := hs.1
    simp only at hp; subst hp
    refine Sat.bind (Sat.of_eq (lt_SH (by omega) (by omega)) (Sat.pure ⟨fun hc => ?_, fun _ => ⟨d0, rfl, hs⟩⟩))
    have hk' : k < count.toNat := by simpa using hc
    refine Sat.ro (index8_SH 0 (by decide) (by simp; omega)) (fun c => ?_)
    refine Sat.ro (posLoad_SH (UPDATE_HASH_ROLL hh c.toUInt32).toNat
      (by have := roll_lt hh c.toUInt32; omega)) (fun hv => ?_)
    split
    · refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d0) (po := po) (idx &&& W_MASK st).toNat _
        (by have := mask_lt idx st.w_size hw1; unfold W_MASK; omega) (by have := mask_lt idx st.w_size hw1; have := L.ph; unfold W_MASK; omega)) ?_)
      rintro _ _ ⟨d1, rfl, hs1⟩
      have hs1' := hs1.1
      refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d1) (po := ho) (UPDATE_HASH_ROLL hh c.toUInt32).toNat _
        (by have := roll_lt hh c.toUInt32; omega) (by have := roll_lt hh c.toUInt32; omega)) ?_)
      rintro _ _ ⟨d2, rfl, hs2⟩
      have hs2' := hs2.1
      refine Sat.bind (Sat.of_eq (addN_SH 1 (by omega)) (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], d2,
        rfl, wr_tr hs (wr_tr hs1 hs2)⟩, ?_⟩))
      simp only [poff]; omega
    · refine Sat.bind (Sat.of_eq (addN_SH 1 (by omega)) (Sat.pure ⟨⟨k + 1, by omega, by simp [Nat.add_assoc], d0,
        rfl, hs⟩, ?_⟩))
      simp only [poff]; omega
  · simp only [poff, fuel]; have := count.toNat_lt; omega
  · rintro ⟨_, _, hh⟩ _ ⟨d', rfl, hs⟩
    exact Sat.of_eq (wrD_SH _) ⟨d', hh, rfl, hs⟩

/-- `insert_batch(s, window, str, count)` through the function pointer, for each of its three values. -/
theorem call_insert_batch_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (f : InsertBatchFn) (str count : UInt32)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (call_insert_batch f (some b) (.ref (.heap b) wo) str count) (IKeep H i z b st d (ho + 131072)) := by
  cases f
  · exact Sat.mono (insert_knuth_batch_SH L str count hr) (fun _ _ k => BKeep.ikeep k)
  · exact Sat.mono (insert_knuth_batch_head_SH L str count hr) (fun _ _ k => BKeep.ikeep k)
  · exact insert_roll_batch_SH L str count hr

end

end ZlibNgF.Proof.InsertSafe
