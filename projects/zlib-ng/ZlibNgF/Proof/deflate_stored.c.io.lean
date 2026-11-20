import ZlibNgF.Proof.«deflate_strategy.common»
import ZlibNgF.Proof.«deflate_p.h.readbuf»
import ZlibNgF.ZlibNg.«deflate_stored.c»

/-!
# The heap steps of `deflate_stored` (`ZlibNgF`)

`deflate_stored` writes the caller's output block directly (the window bytes and `read_buf` from `next_in`), so its
heaps have the form `SH (setB h ob X) i z b st d`: the entry heap `h` with the output block `ob` holding `X`, and the
stream record, the state and the library's block replaced. This file gives the steps on that form: the `memcpy` from
the window into the output, `read_buf` into the output (the input may lie in the output's object, in a disjoint
range), `memmove` / `memcpy` within the library's block, `flush_pending`, and the header of the empty stored block
`zng_tr_stored_block(s, NULL, 0, last)` with its exact byte count (`deflate_stored` then patches the last four of
them, so it needs at least four).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.StoredIO
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get memcpy_heap)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## Tables -/

theorem tbl_size_set {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) :
    (t.set k v).arr.size = max t.arr.size (k + 1) := by
  unfold Tbl.set; split
  · simp; omega
  · simp; omega

theorem tbl_ext {α : Type} [Inhabited α] (t u : Tbl α) (hs : t.arr.size = u.arr.size)
    (hg : ∀ x, t.get x = u.get x) : t = u := by
  cases t with | mk a => cases u with | mk c =>
  simp only [Tbl.mk.injEq]
  apply Array.ext hs
  intro x h1 h2
  have := hg x
  simp only [Tbl.get_eq] at this
  rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at this
  simpa using this

/-- Two stores at different keys commute. -/
theorem upd_comm {α : Type} [Inhabited α] (t : Tbl α) {a c : Nat} (hac : a ≠ c) (x y : α) :
    upd (upd t a x) c y = upd (upd t c y) a x := by
  apply tbl_ext
  · simp only [upd, tbl_size_set]; omega
  · intro k
    show (upd (upd t a x) c y) k = (upd (upd t c y) a x) k
    by_cases h1 : k = c
    · subst h1; simp [upd_ne _ _ _ _ (Ne.symm hac)]
    · by_cases h2 : k = a
      · subst h2; simp [upd_ne _ _ _ _ hac]
      · simp [upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2]

/-! ## The output block -/

/-- `H` with block `c` holding `X`. -/
def setB (H : Heap) (c : Nat) (X : Array UInt8) : Heap := { H with bytes := upd H.bytes c (some X) }

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {ob : Nat}
  {X : Array UInt8}

theorem setB_setB (Y : Array UInt8) : setB (setB H ob X) ob Y = setB H ob Y := by
  simp [setB, upd_upd]

theorem setB_self (hX : H.bytes ob = some X) : setB H ob X = H := by
  simp [setB, ZlibNgF.Proof.DeflateReset.upd_self _ _ _ hX]

theorem SH_setB_ob (hob : ob ≠ b) : (SH (setB H ob X) i z b st d).bytes ob = some X := by
  simp [SH, setB, upd_ne _ _ _ _ hob]

theorem get_SH_setB (hob : ob ≠ b) (r : BRef) (hr : r ≠ .heap b) :
    Space.get (SH (setB H ob X) i z b st d) r = if r = .heap ob then some X else Space.get H r := by
  cases r with
  | heap c =>
    have hcb : c ≠ b := fun e => hr (e ▸ rfl)
    show upd (upd H.bytes ob (some X)) b (some d) c = _
    rw [upd_ne _ _ _ _ hcb]
    by_cases e : c = ob
    · subst e; simp
    · simp only [BRef.heap.injEq, e, ↓reduceIte]; exact upd_ne _ _ _ _ e
  | const _ => rfl
  | str _ => rfl

/-- The heap that `flush_pending` leaves (`OH`) in the `setB` form. -/
theorem OH_setB (hob : ob ≠ b) (H0 : Heap) (Y : Array UInt8) :
    ZlibNgF.Proof.DeflateFlush.OH (setB H0 ob X) i z b st d ob Y = SH (setB H0 ob Y) i z b st d := by
  simp only [ZlibNgF.Proof.DeflateFlush.OH, SH, setB]
  rw [upd_comm _ (Ne.symm hob), upd_upd]

/-- `memcpy(next_out, window + k, n)`: from block `b` into the output block. -/
theorem memcpy_out (hob : ob ≠ b) {oo k n : Nat} (h1 : oo + n ≤ X.size) (h2 : k + n ≤ d.size) :
    Ptr.memcpy (Ptr.ref (BRef.heap ob) oo) (Ptr.ref (BRef.heap b) k) n (SH (setB H ob X) i z b st d) =
      .ok ((), SH (setB H ob (copyFold d oo k (List.range' 0 n) X)) i z b st d) := by
  rw [memcpy_heap (SH_setB_ob hob) (by rw [space_get_heap]; exact SH_bytes ..)
    (fun e => hob (by injection e with e; exact e.symm)) h1 h2]
  simp only [SH, setB]
  rw [upd_comm _ (Ne.symm hob), upd_upd]

/-- The input pointer advanced over the bytes taken. -/
theorem add_in_SH {r : BRef} {src : Array UInt8} {os k : Nat} (hg : Space.get (SH H i z b st d) r = some src)
    (hk : os + k ≤ src.size) :
    Ptr.add (Ptr.ref r os) (k : Int) (SH H i z b st d) = .ok (.ref r (os + k), SH H i z b st d) := by
  have c1 : os ≤ src.size := by omega
  simp only [Ptr.add, hg, c1, show (0 : Int) ≤ (os : Int) + (k : Int) by omega,
    show (os : Int) + (k : Int) ≤ src.size by omega, and_self, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq,
    Ptr.ref.injEq, true_and, and_true]
  omega

/-- The output pointer advanced over the bytes written. -/
theorem add_out_SH (hob : ob ≠ b) {oo k : Nat} (hk : oo + k ≤ X.size) :
    Ptr.add (Ptr.ref (BRef.heap ob) oo) (k : Int) (SH (setB H ob X) i z b st d) =
      .ok (.ref (.heap ob) (oo + k), SH (setB H ob X) i z b st d) :=
  add_in_SH (by rw [space_get_heap]; exact SH_setB_ob hob) hk

/-- `memmove` within block `b`. -/
theorem memmove_SH {od os n : Nat} (h1 : od + n ≤ d.size) (h2 : os + n ≤ d.size) :
    Ptr.memmove (Ptr.ref (BRef.heap b) od) (Ptr.ref (BRef.heap b) os) n (SH H i z b st d) =
      .ok ((), SH H i z b st (copyFold d od os (List.range' 0 n) d)) := by
  simp only [Ptr.memmove, space_get_heap, SH_bytes, h1, h2, and_self, ↓reduceIte]
  simp only [Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, Space.modify, Heap.modifyBytes,
    Tbl.modify_opt _ b _ d (SH_bytes H i z b st d)]
  rw [ZlibNgF.Proof.InflateDict.memcpy_loop]
  simp [SH, upd_upd]

/-- `memcpy` into the output block from any object (the output's own object in a range that does not overlap). -/
theorem memcpy_into_out (hob : ob ≠ b) {r : BRef} {src : Array UInt8} {oo os n : Nat}
    (hs : Space.get (SH (setB H ob X) i z b st d) r = some src)
    (hov : r = .heap ob → oo + n ≤ os ∨ os + n ≤ oo) (h1 : oo + n ≤ X.size) (h2 : os + n ≤ src.size) :
    Ptr.memcpy (Ptr.ref (BRef.heap ob) oo) (Ptr.ref r os) n (SH (setB H ob X) i z b st d) =
      .ok ((), SH (setB H ob (copyFold src oo os (List.range' 0 n) X)) i z b st d) := by
  have hno : ¬ (BRef.heap ob = r ∧ n > 0 ∧ ¬ (oo + n ≤ os ∨ os + n ≤ oo)) := by
    rintro ⟨e, -, hc⟩; exact hc (hov e.symm)
  have hd := SH_setB_ob (H := H) (i := i) (z := z) (st := st) (d := d) (X := X) hob
  simp only [Ptr.memcpy, space_get_heap, hd, hs, h1, h2, and_self, hno, ↓reduceIte]
  simp only [Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, Space.modify, Heap.modifyBytes,
    Tbl.modify_opt _ ob _ X hd]
  rw [ZlibNgF.Proof.InflateDict.memcpy_loop]
  simp only [SH, setB, Except.ok.injEq, Prod.mk.injEq, true_and]
  rw [upd_comm _ (Ne.symm hob), upd_upd]

open ZlibNgF.Proof.ReadBuf (RBZ get_SH_ne dstateOf_SH) in
/-- `read_buf(strm, next_out, size)`: `n = min(avail_in, size)` input bytes copied into the output block at `off`
(the input may lie in the output's object, in a range that does not overlap), the input fields advanced by `n`; the
output block changes within `[off, off + size)` only. -/
theorem read_buf_out (hob : ob ≠ b) (hzb : z.state = some b) {r : BRef} {os : Nat} {src : Array UInt8}
    (hni : z.next_in = .ref r os) (hr : r ≠ .heap b) (hg : Space.get (setB H ob X) r = some src)
    (hin : os + z.avail_in.toNat ≤ src.size) (hc : st.wrap = 2 → H.crcTable = ZlibNg.Crc32Tbl.crc_table)
    {off : Nat} (size : UInt32) (hbuf : off + size.toNat ≤ X.size)
    (hov : r = .heap ob → off + size.toNat ≤ os ∨ os + z.avail_in.toNat ≤ off) :
    Sat (SH (setB H ob X) i z b st d) (ZlibNg.DeflateP.read_buf (some i) (.ref (.heap ob) off) size)
      (fun n H' => n.toNat = min z.avail_in.toNat size.toNat ∧
        ∃ X' a, H' = SH (setB H ob X') i (RBZ z n r os a) b st d ∧ X'.size = X.size ∧
          ∀ j, (j < off ∨ off + size.toNat ≤ j) → X'[j]! = X[j]!) := by
  unfold ZlibNg.DeflateP.read_buf
  refine Sat.bind (Sat.of_eq (dstateOf_SH hzb) ?_)
  refine Sat.bind (Sat.of_eq ldStream_SH ?_)
  obtain ⟨len, hlen⟩ : ∃ len : UInt32, len = (if z.avail_in > size then size else z.avail_in) := ⟨_, rfl⟩
  have hlm : len.toNat = min z.avail_in.toNat size.toNat := by
    rw [hlen]; split
    · rename_i h; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at h; omega
    · rename_i h; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at h; omega
  rw [← hlen]
  show Sat _ (if (len == 0) = true then _ else _) _
  have hg0 : Space.get (SH (setB H ob X) i z b st d) r = some src := by rw [get_SH_ne hr]; exact hg
  split
  · rename_i h0
    have : len = 0 := by simpa using h0
    subst this
    have e : RBZ z 0 r os z.adler = z := by
      cases z; simp only [RBZ] at *; subst hni; simp
    exact Sat.pure ⟨by rw [← hlm], X, z.adler, by rw [e], rfl, fun _ _ => rfl⟩
  rename_i h0
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have hl64 : os + len.toUInt64.toNat ≤ src.size := by rw [UInt32.toNat_toUInt64]; omega
  have hm := memcpy_into_out (H := H) (i := i) (z := z) (st := st) (d := d) (X := X) hob hg0
    (oo := off) (os := os) (n := len.toNat) (fun e => by have := hov e; omega) (by omega) (by omega)
  have hX := copyFold_size src off os (List.range' 0 len.toNat) X
  extract_lets jp
  have hjp : ∀ (a : UInt64) (X' : Array UInt8), X'.size = X.size →
      (∀ j, (j < off ∨ off + size.toNat ≤ j) → X'[j]! = X[j]!) →
      Sat (SH (setB H ob X') i { z with adler := a } b st d) (jp ())
        (fun n H' => n.toNat = min z.avail_in.toNat size.toNat ∧
          ∃ X' a, H' = SH (setB H ob X') i (RBZ z n r os a) b st d ∧ X'.size = X.size ∧
            ∀ j, (j < off ∨ off + size.toNat ≤ j) → X'[j]! = X[j]!) := by
    intro a X' hs' ho'
    simp only [jp]
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
    simp only [hni]
    have hg2 : ∀ zz : ZStream, ∃ s2, Space.get (SH (setB H ob X') i zz b st d) r = some s2 ∧
        s2.size = src.size := by
      intro zz
      rw [get_SH_setB hob r hr]
      have hg' := hg
      rw [show setB H ob X = setB H ob X from rfl] at hg'
      unfold setB at hg'
      by_cases e : r = .heap ob
      · subst e
        simp only [↓reduceIte]
        have : src = X := by simpa [space_get_heap] using hg'.symm
        exact ⟨X', rfl, by rw [hs', this]⟩
      · simp only [e, ↓reduceIte]
        refine ⟨src, ?_, rfl⟩
        cases r with
        | heap c =>
          have hc' : c ≠ ob := fun e' => e (e' ▸ rfl)
          simpa [space_get_heap, upd_ne _ _ _ _ hc'] using hg'
        | const _ => exact hg'
        | str _ => exact hg'
    refine Sat.bind (Sat.of_eq (by
      obtain ⟨s2, h2, h2s⟩ := hg2 { z with adler := a, avail_in := z.avail_in - len }
      exact add_in_SH h2 (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    exact Sat.pure ⟨hlm, X', a, rfl, hs', ho'⟩
  clear_value jp
  have hout : ∀ j, (j < off ∨ off + size.toNat ≤ j) →
      (copyFold src off os (List.range' 0 len.toNat) X)[j]! = X[j]! := fun j hj =>
    copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'_1] at hx; omega)
  split
  · rename_i hw2
    have hc' := hc (by simpa using hw2)
    refine Sat.bind (Sat.of_eq ldStream_SH ?_)
    rw [hni]
    obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Crc32.crc32_braid_ok
      (show (SH (setB H ob X) i z b st d).crcTable = _ from hc') hg0 z.adler.toUInt32 os len.toUInt64 hl64
    refine Sat.bind ?_
    refine ⟨v, SH (setB H ob (copyFold src off os (List.range' 0 len.toNat) X)) i z b st d, ?_, ?_⟩
    · show (ZlibNg.Crc32Braid.crc32_copy_braid _ _ _ _) _ = _
      simp only [ZlibNg.Crc32Braid.crc32_copy_braid, bind_app]
      rw [show (ZlibNg.Crc32Braid.crc32_braid z.adler.toUInt32 (Ptr.ref r os) len.toUInt64)
        (SH (setB H ob X) i z b st d) = .ok (v, SH (setB H ob X) i z b st d) from e]
      simp only []
      rw [UInt32.toNat_toUInt64, hm]; rfl
    · refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
      exact hjp _ _ hX hout
  · split
    · refine Sat.bind (Sat.of_eq ldStream_SH ?_)
      rw [hni]
      obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Adler32Safe.adler32_c_safe hg0 z.adler.toUInt32 os len.toUInt64 hl64
      refine Sat.bind ?_
      refine ⟨v, SH (setB H ob (copyFold src off os (List.range' 0 len.toNat) X)) i z b st d, ?_, ?_⟩
      · show (ZlibNg.Adler32C.adler32_copy_c _ _ _ _) _ = _
        simp only [ZlibNg.Adler32C.adler32_copy_c, bind_app]
        rw [show (ZlibNg.Adler32C.adler32_c z.adler.toUInt32 (Ptr.ref r os) len.toUInt64)
          (SH (setB H ob X) i z b st d) = .ok (v, SH (setB H ob X) i z b st d) from e]
        simp only []
        rw [UInt32.toNat_toUInt64, hm]; rfl
      · refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
        exact hjp _ _ hX hout
    · refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
      rw [hni]
      refine Sat.bind (Sat.of_eq hm ?_)
      have e : SH (setB H ob (copyFold src off os (List.range' 0 len.toNat) X)) i z b st d =
          SH (setB H ob (copyFold src off os (List.range' 0 len.toNat) X)) i { z with adler := z.adler } b st d := rfl
      rw [e]
      exact hjp z.adler _ hX hout

/-- `zng_tr_emit_tree(s, STORED_BLOCK, last)` with `last` 0 or 1 and fewer than 8 bits waiting: three more bits in
`bi_buf`, nothing stored. -/
theorem emit_tree_stored {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (last : Int32) (hl : last = 0 ∨ last = 1) (v : Int32) (hv : st.bi_valid = v)
    (hv8 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STORED_BLOCK last)
      (fun _ H' => ∃ bb, H' = SH H i z b { st with bi_valid := v + 3, bi_buf := bb } d) := by
  unfold ZlibNg.TreesEmit.zng_tr_emit_tree ZlibNg.TreesEmit.send_bits
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  rw [hv]
  rcases hl with rfl | rfl <;> rcases hv8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) [ZlibNg.Trees.STORED_BLOCK, chkI32, shl64, bind_app, Sat, wrD_SH]
    exact ⟨_, rfl⟩

end

end ZlibNgF.Proof.StoredIO
