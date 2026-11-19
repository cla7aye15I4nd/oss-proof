import ZlibNgF.Proof.«trees_emit.h.bits»
import ZlibNgF.Proof.«deflate.c.reset»
import ZlibNgF.ZlibNg.«deflate.c.fill_window»

/-!
# Byte and `Pos` accesses of the window layer (`ZlibNgF`)

Runs on `SH` heaps (`Proof/deflate.c.init.lean`): reads of window bytes (`index8`, `zng_memread_2/4/8`), the
two-byte `Pos` accesses of `prev` / `head` (`posLoad`, `posStore`), and the index bounds of the hash functions
(`UPDATE_HASH_KNUTH` and `UPDATE_HASH_ROLL` stay below `HASH_SIZE`, `idx & W_MASK` below `w_size`). A store keeps the
size of the block's bytes and the bytes from an upper bound `U` on (`BKeep`): every store of the window layer is to the
window, `prev` or `head`, so `U` is the end of `head` and the bytes of `pending_buf` (the symbols in `sym_buf`) stay.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.WinBase
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)
open ZlibNgF.Proof.DeflateBits (addI_SH memwrite2_SH WrIn)

/-- A step that leaves the stream record and the state `st` and changes block `b`'s bytes below `U` only, keeping
their size. -/
def BKeep {α : Type} (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (U : Nat) :
    α → Heap → Prop :=
  fun _ H' => ∃ d', H' = SH H i z b st d' ∧ WrIn d 0 U d'

/-- Two changes below `U`. -/
theorem wr_tr {d d' d'' : Array UInt8} {U : Nat} (a : WrIn d 0 U d') (c : WrIn d' 0 U d'') : WrIn d 0 U d'' :=
  a.trans c (Nat.le_refl _) (Nat.le_refl _)

/-- A change within `[lo, hi)` is a change below `U` when `hi ≤ U`. -/
theorem wr_below {d d' : Array UInt8} {lo hi U : Nat} (a : WrIn d lo hi d') (h : hi ≤ U) : WrIn d 0 U d' :=
  a.widen (Nat.zero_le _) h

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- A read that leaves the heap. -/
theorem Sat.ro {α β : Type} {H0 : Heap} {m : M α} {f : α → M β} {Q : β → Heap → Prop}
    (hm : ∃ v, m H0 = .ok (v, H0)) (k : ∀ v, Sat H0 (f v) Q) : Sat H0 (m >>= f) Q := by
  obtain ⟨v, e⟩ := hm; exact Sat.bind (Sat.of_eq e (k v))

theorem addN_SH {off : Nat} (k : Nat) (hk : off + k ≤ d.size) :
    Ptr.add (Ptr.ref (BRef.heap b) off) (k : Int) (SH H i z b st d) =
      .ok (.ref (.heap b) (off + k), SH H i z b st d) := by
  rw [addI_SH (k : Int) (by omega) (by omega)]
  simp only [Except.ok.injEq, Prod.mk.injEq, Ptr.ref.injEq, and_true, true_and]
  omega

theorem load_SH {off : Nat} (hk : off < d.size) :
    ∃ v, Ptr.load (R := BRef) (T := UInt8) (Ptr.ref (BRef.heap b) off) (SH H i z b st d) = .ok (v, SH H i z b st d) := by
  simp only [Ptr.load, space_get_heap, SH_bytes, hk, ↓reduceDIte]
  exact ⟨_, rfl⟩

theorem index8_SH {off : Nat} (k : Int) (h0 : 0 ≤ k) (hk : off + k.toNat < d.size) :
    ∃ v, index8 (Ptr.ref (BRef.heap b) off) k (SH H i z b st d) = .ok (v, SH H i z b st d) := by
  simp only [index8, Ptr.index, bind_app, addI_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off)
    k h0 (by omega)]
  exact load_SH (by omega)

theorem memread2_SH {off : Nat} (hk : off + 2 ≤ d.size) :
    ∃ v, memread2 (Ptr.ref (BRef.heap b) off) (SH H i z b st d) = .ok (v, SH H i z b st d) := by
  obtain ⟨v0, e0⟩ := index8_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off) 0 (by decide) (by simp; omega)
  obtain ⟨v1, e1⟩ := index8_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off) 1 (by decide) (by simp; omega)
  simp only [memread2, bind_app, e0, e1]
  exact ⟨_, rfl⟩

theorem memread4_SH {off : Nat} (hk : off + 4 ≤ d.size) :
    ∃ v, memread4 (Ptr.ref (BRef.heap b) off) (SH H i z b st d) = .ok (v, SH H i z b st d) := by
  obtain ⟨v0, e0⟩ := index8_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off) 0 (by decide) (by simp; omega)
  obtain ⟨v1, e1⟩ := index8_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off) 1 (by decide) (by simp; omega)
  obtain ⟨v2, e2⟩ := index8_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off) 2 (by decide) (by simp; omega)
  obtain ⟨v3, e3⟩ := index8_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off) 3 (by decide) (by simp; omega)
  simp only [memread4, bind_app, e0, e1, e2, e3]
  exact ⟨_, rfl⟩

theorem memread8_SH {off : Nat} (hk : off + 8 ≤ d.size) :
    ∃ v, memread8 (Ptr.ref (BRef.heap b) off) (SH H i z b st d) = .ok (v, SH H i z b st d) := by
  obtain ⟨v0, e0⟩ := memread4_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off) (by omega)
  obtain ⟨v1, e1⟩ := memread4_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off + 4) (by omega)
  have ea := addN_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := off) 4 (by omega)
  simp only [memread8, bind_app]
  rw [e0]; simp only []
  rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, ea]; simp only []
  rw [e1]
  exact ⟨_, rfl⟩

theorem posLoad_SH {po : Nat} (k : Nat) (hk : po + 2 * k + 2 ≤ d.size) :
    ∃ v, posLoad (Ptr.ref (BRef.heap b) po) (k : Int) (SH H i z b st d) = .ok (v, SH H i z b st d) := by
  have ea : Ptr.add (Ptr.ref (BRef.heap b) po) (2 * (k : Int)) (SH H i z b st d) =
      .ok (.ref (.heap b) (po + 2 * k), SH H i z b st d) := by
    rw [show 2 * (k : Int) = ((2 * k : Nat) : Int) by omega]
    exact addN_SH (2 * k) (by omega)
  simp only [posLoad, bind_app, ea]
  exact memread2_SH hk

theorem posStore_SH {po U : Nat} (k : Nat) (v : UInt16) (hk : po + 2 * k + 2 ≤ d.size) (hu : po + 2 * k + 2 ≤ U) :
    Sat (SH H i z b st d) (posStore (Ptr.ref (BRef.heap b) po) (k : Int) v) (BKeep H i z b st d U) := by
  have ea : Ptr.add (Ptr.ref (BRef.heap b) po) (2 * (k : Int)) (SH H i z b st d) =
      .ok (.ref (.heap b) (po + 2 * k), SH H i z b st d) := by
    rw [show 2 * (k : Int) = ((2 * k : Nat) : Int) by omega]
    exact addN_SH (2 * k) (by omega)
  unfold posStore
  refine Sat.bind (Sat.of_eq ea ?_)
  exact Sat.mono (memwrite2_SH v hk) (fun _ _ ⟨d', e, w⟩ => ⟨d', e, wr_below w hu⟩)

end

/-- A chain of steps each changing the bytes below `U` only. -/
theorem BKeep.bind {α β : Type} {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    {U : Nat} {m : M α} {f : α → M β}
    (hm : Sat (SH H i z b st d) m (fun a H' => ∃ d', H' = SH H i z b st d' ∧ WrIn d 0 U d' ∧
      ∀ d0 : Array UInt8, WrIn d 0 U d0 → Sat (SH H i z b st d0) (f a) (BKeep H i z b st d0 U))) :
    Sat (SH H i z b st d) (m >>= f) (BKeep H i z b st d U) := by
  refine Sat.bind (Sat.mono hm ?_)
  rintro a _ ⟨d', rfl, hs, k⟩
  exact Sat.mono (k d' hs) (fun _ _ ⟨d'', e, hs'⟩ => ⟨d'', e, wr_tr hs hs'⟩)

/-! ## Index bounds -/

theorem knuth_lt (v : UInt32) : (ZlibNg.InsertStringP.UPDATE_HASH_KNUTH v).toNat < 65536 := by
  unfold ZlibNg.InsertStringP.UPDATE_HASH_KNUTH ZlibNg.InsertStringP.KNUTH_SHIFT
  have hx := (v * 2654435761).toNat_lt
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have e : (2 : Nat) ^ ((32 - HASH_BITS : UInt32).toNat % 32) = 65536 := by decide
  rw [e]; omega

theorem roll_lt (h v : UInt32) : (ZlibNg.InsertStringP.UPDATE_HASH_ROLL h v).toNat < 65536 := by
  unfold ZlibNg.InsertStringP.UPDATE_HASH_ROLL ZlibNg.InsertStringP.ROLL_MASK
  rw [UInt32.toNat_and]
  have := Nat.and_le_right (n := ((h <<< 5) ^^^ v.toUInt8.toUInt32).toNat) (m := (HASH_SIZE / 2 - 1 : UInt32).toNat)
  have e : (HASH_SIZE / 2 - 1 : UInt32).toNat = 32767 := by decide
  omega

theorem mask_lt (idx w : UInt32) (hw : 1 ≤ w.toNat) : (idx &&& (w - 1)).toNat < w.toNat := by
  rw [UInt32.toNat_and]
  have := Nat.and_le_right (n := idx.toNat) (m := (w - 1).toNat)
  have e : (w - 1).toNat = w.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by simpa [UInt32.le_iff_toNat_le] using hw)]; rfl
  omega

end ZlibNgF.Proof.WinBase
