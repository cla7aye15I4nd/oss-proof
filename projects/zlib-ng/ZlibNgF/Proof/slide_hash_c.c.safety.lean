import ZlibNgF.Proof.«insert_string_p.h.safety»

/-!
# Safety of `slide_hash_c` / `slide_hash_head_c` (`ZlibNgF`)

`slide_hash_c_chain(table, entries, wsize)` reads and writes the `entries` two-byte entries from `table`; on the
`head` table (`HASH_SIZE` entries) and the `prev` table (`w_size` entries) of `HLay` they lie in block `b`. The
calls change only the block's bytes, keeping their size.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.SlideSafe
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNgF.Proof.InsertSafe
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateBits (memwrite2_SH)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem chain_SH {base : Nat} (entries : UInt32) (wsize : UInt16) (he : entries.toNat ≤ 65536)
    (hr : base + 2 * entries.toNat ≤ d.size) :
    Sat (SH H i z b st d) (ZlibNg.SlideHash.slide_hash_c_chain (.ref (.heap b) base) entries wsize)
      (BKeep H i z b st d) := by
  unfold ZlibNg.SlideHash.slide_hash_c_chain
  refine Sat.bind (Sat.mono (sat_cwhile (s := ((0 : UInt32), Ptr.ref (BRef.heap b) base))
    (fun (x : UInt32 × BPtr) H' => ∃ k, k ≤ entries.toNat ∧ x.1.toNat = k ∧ x.2 = .ref (.heap b) (base + 2 * k) ∧
      ∃ d0 : Array UInt8, H' = SH H i z b st d0 ∧ d0.size = d.size)
    (fun x => entries.toNat - x.1.toNat) (fun _ H' => BKeep H i z b st d () H') ?_
    ⟨0, by omega, rfl, by simp, d, rfl, rfl⟩ ?_) ?_)
  · rintro ⟨idx, q⟩ H1 ⟨k, hk, hi, hq, d0, rfl, hs⟩
    simp only at hi hq; subst hq
    refine Sat.pure ⟨fun hc => ?_, fun _ => ⟨d0, rfl, hs⟩⟩
    have hk' : k < entries.toNat := by
      have : idx < entries := by simpa using hc
      rw [UInt32.lt_iff_toNat_lt] at this; omega
    refine Sat.ro (memread2_SH (by omega)) (fun m => ?_)
    refine Sat.bind (Sat.mono (memwrite2_SH (d := d0) _ (by omega)) ?_)
    rintro _ _ ⟨d1, rfl, w⟩
    have h1 := w.1
    refine Sat.bind (Sat.of_eq (addN_SH 2 (by omega)) (Sat.pure ⟨⟨k + 1, by omega, ?_, by simp; omega, d1, rfl,
      w.1.trans hs⟩, ?_⟩))
    · rw [UInt32.toNat_add, hi]; simp; omega
    · simp only; rw [UInt32.toNat_add, hi]; simp; omega
  · simp only [fuel]; have := entries.toNat_lt; omega
  · rintro _ _ ⟨d', rfl, hs⟩; exact Sat.pure ⟨d', rfl, hs⟩

theorem slide_hash_c_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (hw : st.w_size.toNat ≤ 32768) :
    Sat (SH H i z b st d) (ZlibNg.SlideHash.slide_hash_c (some b)) (BKeep H i z b st d) := by
  unfold ZlibNg.SlideHash.slide_hash_c
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  have hhd := L.hd
  have hpw := L.pw
  refine BKeep.bind (Sat.mono (chain_SH HASH_SIZE _ (by decide) (by simp [HASH_SIZE]; omega)) ?_)
  rintro _ _ ⟨d', rfl, hs⟩
  refine ⟨d', rfl, hs, fun d0 hd0 => ?_⟩
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  simp only [L.prev]
  refine Sat.bind (Sat.pure ?_)
  exact chain_SH _ _ (by omega) (by omega)

theorem slide_hash_head_c_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) :
    Sat (SH H i z b st d) (ZlibNg.SlideHash.slide_hash_head_c (some b)) (BKeep H i z b st d) := by
  unfold ZlibNg.SlideHash.slide_hash_head_c
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  simp only [L.head]
  refine Sat.bind (Sat.pure ?_)
  have hhd := L.hd
  exact chain_SH HASH_SIZE _ (by decide) (by simp [HASH_SIZE]; omega)

end

end ZlibNgF.Proof.SlideSafe
