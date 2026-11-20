import ZlibNgF.Proof.«slide_hash_c.c.safety»
import ZlibNgF.Proof.«public-crc32»
import ZlibNgF.Proof.«adler32_c.c.safety»

/-!
# Safety of `read_buf` (`ZlibNgF`)

`read_buf(strm, buf, size)` with `buf` in the window of block `b` (`size` bytes there) and `next_in` in another
object with `avail_in` readable bytes: the check value (`crc32_copy_braid` for gzip, `adler32_copy_c` for zlib)
or plain `memcpy` copies `len = min(avail_in, size)` input bytes into the block, and the input fields advance by
`len` (`RBZ`). Nothing else changes: the block's bytes change within `[buf, buf + size)` only.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.ReadBuf
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get memcpy_heap)
open ZlibNgF.Proof.DeflateBits (WrIn)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)

/-- The stream record after `read_buf` consumed `n` input bytes from `next_in = r + os`. -/
def RBZ (z : ZStream) (n : UInt32) (r : BRef) (os : Nat) (a : UInt64) : ZStream :=
  { z with adler := a, avail_in := z.avail_in - n, next_in := .ref r (os + n.toNat),
           total_in := z.total_in + n.toUInt64 }

/-- A copy of `n` bytes to offset `od` changes `[od, od + n)` only. -/
theorem copyFold_wr (src : Array UInt8) (od os n : Nat) (a : Array UInt8) :
    WrIn a od (od + n) (copyFold src od os (List.range' 0 n) a) :=
  ⟨copyFold_size .., fun _ hj => copyFold_get _ _ _ _ _ _ (fun x hx => by
    simp only [List.mem_range'_1] at hx; omega)⟩

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem get_SH_ne {r : BRef} (hr : r ≠ .heap b) : Space.get (SH H i z b st d) r = Space.get H r := by
  cases r with
  | heap c =>
    have : c ≠ b := fun e => hr (e ▸ rfl)
    show upd H.bytes b (some d) c = H.bytes c
    exact upd_ne _ _ _ _ this
  | const _ => rfl
  | str _ => rfl

theorem memcpy_SH {r : BRef} {src : Array UInt8} (hr : r ≠ .heap b) (hg : Space.get H r = some src)
    {od os n : Nat} (h1 : od + n ≤ d.size) (h2 : os + n ≤ src.size) :
    Ptr.memcpy (.ref (.heap b) od) (.ref r os) n (SH H i z b st d) =
      .ok ((), SH H i z b st (copyFold src od os (List.range' 0 n) d)) := by
  rw [memcpy_heap (SH_bytes H i z b st d) (by rw [get_SH_ne hr]; exact hg) hr h1 h2]
  simp [SH, upd_upd]

theorem dstateOf_SH (hzb : z.state = some b) :
    dstateOf (some i) (SH H i z b st d) = .ok (some b, SH H i z b st d) := by
  simp [dstateOf, rdZ_SH, hzb]

theorem read_buf_SH (hzb : z.state = some b) {r : BRef} {os : Nat} {src : Array UInt8}
    (hni : z.next_in = .ref r os) (hr : r ≠ .heap b) (hg : Space.get H r = some src)
    (hin : os + z.avail_in.toNat ≤ src.size) (hc : st.wrap = 2 → H.crcTable = ZlibNg.Crc32Tbl.crc_table)
    {off : Nat} (size : UInt32) (hbuf : off + size.toNat ≤ d.size) :
    Sat (SH H i z b st d) (ZlibNg.DeflateP.read_buf (some i) (.ref (.heap b) off) size)
      (fun n H' => n.toNat ≤ size.toNat ∧ n.toNat ≤ z.avail_in.toNat ∧ (n = 0 → H' = SH H i z b st d ∧ (z.avail_in = 0 ∨ size = 0)) ∧
        ∃ d' a, H' = SH H i (RBZ z n r os a) b st d' ∧ WrIn d off (off + size.toNat) d') := by
  unfold ZlibNg.DeflateP.read_buf
  refine Sat.bind (Sat.of_eq (dstateOf_SH hzb) ?_)
  refine Sat.bind (Sat.of_eq ldStream_SH ?_)
  obtain ⟨len, hlen⟩ : ∃ len : UInt32, len = (if z.avail_in > size then size else z.avail_in) := ⟨_, rfl⟩
  have hl1 : len.toNat ≤ size.toNat := by
    rw [hlen]; split
    · omega
    · rename_i h; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at h; omega
  have hl2 : len.toNat ≤ z.avail_in.toNat := by
    rw [hlen]; split
    · rename_i h; simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at h; omega
    · omega
  rw [← hlen]
  show Sat _ (if (len == 0) = true then _ else _) _
  split
  · rename_i h0
    have : len = 0 := by simpa using h0
    subst this
    have e : RBZ z 0 r os z.adler = z := by
      cases z; simp only [RBZ] at *; subst hni; simp
    have h0' : z.avail_in = 0 ∨ size = 0 := by
      split at hlen
      · exact Or.inr hlen.symm
      · exact Or.inl hlen.symm
    exact Sat.pure ⟨by simp, by simp, fun _ => ⟨rfl, h0'⟩, d, z.adler, by rw [e], WrIn.refl _ _ _⟩
  rename_i h0
  have hlen0 : len ≠ 0 := by simpa using h0
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have hl64 : os + len.toUInt64.toNat ≤ src.size := by rw [UInt32.toNat_toUInt64]; omega
  have hg' : Space.get (SH H i z b st d) r = some src := by rw [get_SH_ne hr]; exact hg
  have hm := memcpy_SH (H := H) (i := i) (z := z) (st := st) (d := d) hr hg (od := off) (os := os) (n := len.toNat)
    (by omega) (by omega)
  extract_lets jp
  have hjp : ∀ (a : UInt64) (d' : Array UInt8), WrIn d off (off + size.toNat) d' →
      Sat (SH H i { z with adler := a } b st d') (jp ())
        (fun n H' => n.toNat ≤ size.toNat ∧ n.toNat ≤ z.avail_in.toNat ∧ (n = 0 → H' = SH H i z b st d ∧ (z.avail_in = 0 ∨ size = 0)) ∧
          ∃ d' a, H' = SH H i (RBZ z n r os a) b st d' ∧ WrIn d off (off + size.toNat) d') := by
    intro a d' hd'
    simp only [jp]
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
    simp only [hni]
    have hadd : ∀ zz : ZStream, Ptr.add (Ptr.ref r os) (len.toNat : Int) (SH H i zz b st d') =
        .ok (.ref r (os + len.toNat), SH H i zz b st d') := by
      intro zz
      have hg2 : Space.get (SH H i zz b st d') r = some src := by rw [get_SH_ne hr]; exact hg
      have c1 : os ≤ src.size := by omega
      have c2 : 0 ≤ (os : Int) + (len.toNat : Int) := by omega
      have c3 : (os : Int) + (len.toNat : Int) ≤ src.size := by omega
      simp only [Ptr.add, hg2, c1, c2, c3, and_self, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, Ptr.ref.injEq,
        true_and, and_true]
      omega
    refine Sat.bind (Sat.of_eq (hadd _) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    exact Sat.pure ⟨hl1, hl2, fun h => absurd h hlen0, d', a, rfl, hd'⟩
  clear_value jp
  split
  · rename_i hw2
    have hc' := hc (by simpa using hw2)
    refine Sat.bind (Sat.of_eq ldStream_SH ?_)
    rw [hni]
    obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Crc32.crc32_braid_ok (show (SH H i z b st d).crcTable = _ from hc') hg'
      z.adler.toUInt32 os len.toUInt64 hl64
    refine Sat.bind ?_
    refine ⟨v, SH H i z b st (copyFold src off os (List.range' 0 len.toNat) d), ?_, ?_⟩
    · show (ZlibNg.Crc32Braid.crc32_copy_braid _ _ _ _) _ = _
      simp only [ZlibNg.Crc32Braid.crc32_copy_braid, bind_app]
      rw [show (ZlibNg.Crc32Braid.crc32_braid z.adler.toUInt32 (Ptr.ref r os) len.toUInt64) (SH H i z b st d) =
        .ok (v, SH H i z b st d) from e]
      simp only []
      rw [UInt32.toNat_toUInt64, hm]; rfl
    · refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
      exact hjp _ _ ((copyFold_wr ..).widen (Nat.le_refl _) (by omega))
  · split
    · refine Sat.bind (Sat.of_eq ldStream_SH ?_)
      rw [hni]
      obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Adler32Safe.adler32_c_safe hg' z.adler.toUInt32 os len.toUInt64 hl64
      refine Sat.bind ?_
      refine ⟨v, SH H i z b st (copyFold src off os (List.range' 0 len.toNat) d), ?_, ?_⟩
      · show (ZlibNg.Adler32C.adler32_copy_c _ _ _ _) _ = _
        simp only [ZlibNg.Adler32C.adler32_copy_c, bind_app]
        rw [show (ZlibNg.Adler32C.adler32_c z.adler.toUInt32 (Ptr.ref r os) len.toUInt64) (SH H i z b st d) =
          .ok (v, SH H i z b st d) from e]
        simp only []
        rw [UInt32.toNat_toUInt64, hm]; rfl
      · refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
        exact hjp _ _ ((copyFold_wr ..).widen (Nat.le_refl _) (by omega))
    · refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
      rw [hni]
      refine Sat.bind (Sat.of_eq hm ?_)
      exact hjp z.adler _ ((copyFold_wr ..).widen (Nat.le_refl _) (by omega))

end

end ZlibNgF.Proof.ReadBuf
