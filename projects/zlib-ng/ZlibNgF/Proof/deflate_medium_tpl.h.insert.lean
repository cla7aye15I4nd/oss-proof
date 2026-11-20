import ZlibNgF.Proof.«insert_string_p.h.safety»
import ZlibNgF.Proof.«deflate_medium_tpl.h.find»

/-!
# The insertions of `deflate_medium` (`ZlibNgF`)

`insert_knuth_stepped` (`insert_string_p.h:169-209`) with `count >= 2` and `max_inserts >= 2` (so `intervals =
MIN(count, max_inserts) - 1` is not zero) and `str + count <= 65536`: the fixed-point cursor `idx_fp = str << 16 + j *
inc_fp` does not wrap for `j < inserts`, and every inserted position `idx_fp >> 16` is at most `str + count - 1`, so
its 4-byte read stays in `[str, str + count + 3)`. `insert_match` (`deflate_medium_tpl.h:16-41`) then inserts
`[match.strstart + 1, match.strstart + match_length)` (or the part from `orgstart`) with `insert_knuth`,
`insert_knuth_batch` or `insert_knuth_stepped`, whose `count > 2 * max_insert_count >= 4` (patch 0013 keeps
`max_insert_count` in `2..STD_MAX_MATCH`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumInsert
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.WinBase
open ZlibNg.InsertStringP ZlibNg.InsertString ZlibNgF.Proof.InsertSafe
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateBits (WrIn)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- The arithmetic of the stepped cursor. -/
theorem stepped_idx (s c n j inc : Nat) (hn : 1 ≤ n) (hnc : n + 1 ≤ c) (hc6 : c ≤ 65536)
    (hinc : inc = ((c - 1) * 65536 + (n - 1)) / n) (hj : j ≤ n) :
    j * inc ≤ (c - 1) * 65536 + (n - 1) ∧ (s * 65536 + j * inc) / 65536 ≤ s + c - 1 := by
  have h1 : n * inc ≤ (c - 1) * 65536 + (n - 1) := by subst hinc; exact Nat.mul_div_le _ _
  have h2 : j * inc ≤ n * inc := Nat.mul_le_mul_right _ hj
  refine ⟨by omega, ?_⟩
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  have : n - 1 < 65536 * 1 + 0 := by omega
  rw [Nat.succ_eq_add_one, Nat.add_mul]
  have e : (s + c - 1) * 65536 = s * 65536 + (c - 1) * 65536 := by
    rw [show s + c - 1 = s + (c - 1) by omega, Nat.add_mul]
  omega

theorem insert_knuth_stepped_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (str count mi : UInt32)
    (hc : 2 ≤ count.toNat) (hm : 2 ≤ mi.toNat) (hs : str.toNat + count.toNat ≤ 65536)
    (hr : wo + str.toNat + count.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (insert_knuth_stepped_static (some b) (.ref (.heap b) wo) str count mi)
      (BKeep H i z b st d (ho + 131072)) := by
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
      ∃ d0 : Array UInt8, H' = SH H i z b st d0 ∧ WrIn d 0 (ho + 131072) d0)
    (fun x => ins.toNat - x.1.toNat) (fun _ H' => BKeep H i z b st d (ho + 131072) () H') ?_
    ⟨by simp, fun _ => by simp [hs16], d, rfl, WrIn.refl _ _ _⟩ ?_) ?_)
  · rintro ⟨j, fp⟩ H1 ⟨hj, hfp, d0, rfl, hw⟩
    have hd0 := hw.1
    refine Sat.pure ⟨fun hlt => ?_, fun _ => ⟨d0, rfl, hw⟩⟩
    simp only [decide_eq_true_eq] at hlt
    have hlt' : j.toNat < ins.toNat := UInt32.lt_iff_toNat_lt.mp hlt
    have hfp' := hfp hlt'
    dsimp only at hfp' ⊢
    obtain ⟨hb1, hb2⟩ := stepped_idx str.toNat count.toNat (ins.toNat - 1) j.toNat inc.toNat (by omega) (by omega) (by omega)
      (by rw [hinc]) (by omega)
    have hidx : (fp >>> 16).toNat = (str.toNat * 65536 + j.toNat * inc.toNat) / 65536 := by
      rw [UInt32.toNat_shiftRight, hfp']; simp [Nat.shiftRight_eq_div_pow]
    refine Sat.bind (Sat.of_eq (addN_SH (d := d0) (fp >>> 16).toNat (by omega)) ?_)
    refine Sat.ro (memread4_SH (by omega)) (fun v => ?_)
    refine Sat.ro (posLoad_SH (UPDATE_HASH_KNUTH v).toNat (by have := knuth_lt v; omega)) (fun hv => ?_)
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    have hnext : j.toNat + 1 < ins.toNat → (fp + inc).toNat = str.toNat * 65536 + (j.toNat + 1) * inc.toNat := by
      intro h
      obtain ⟨hb3, -⟩ := stepped_idx str.toNat count.toNat (ins.toNat - 1) (j.toNat + 1) inc.toNat (by omega)
        (by omega) (by omega) (by rw [hinc]) (by omega)
      rw [UInt32.toNat_add, hfp', Nat.succ_mul]
      rw [Nat.succ_mul] at hb3
      omega
    split
    · refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d0) (po := po) ((fp >>> 16) &&& W_MASK st).toNat _
        (by have := mask_lt (fp >>> 16) st.w_size hw1; unfold W_MASK; omega)
        (by have := mask_lt (fp >>> 16) st.w_size hw1; have := L.ph; unfold W_MASK; omega)) ?_)
      rintro _ _ ⟨d1, rfl, hs1⟩
      have hs1' := hs1.1
      refine Sat.bind (Sat.mono (posStore_SH (U := ho + 131072) (d := d1) (po := ho) (UPDATE_HASH_KNUTH v).toNat _
        (by have := knuth_lt v; omega) (by have := knuth_lt v; omega)) ?_)
      rintro _ _ ⟨d2, rfl, hs2⟩
      exact Sat.pure ⟨⟨by rw [hj1]; omega, fun h => by rw [hj1] at h ⊢; exact hnext h, d2, rfl,
        wr_tr hw (wr_tr hs1 hs2)⟩, by rw [hj1]; omega⟩
    · exact Sat.pure ⟨⟨by rw [hj1]; omega, fun h => by rw [hj1] at h ⊢; exact hnext h, d0, rfl, hw⟩,
        by rw [hj1]; omega⟩
  · simp only [fuel]; have := ins.toNat_lt; omega
  · rintro _ _ ⟨d', rfl, hs⟩; exact Sat.pure ⟨d', rfl, hs⟩

/-- `insert_match(s, window, m, max_insert_count)` with `2 <= max_insert_count <= STD_MAX_MATCH`, a match of length
`len >= 2` at `m.strstart = s` with `orgstart <= s + len`, whose last insertion reads stay in the block
(`window + s + len + 3`) and `s + len <= 65536`: no fault, only the bytes of `prev` / `head` change. -/
theorem insert_match_SH {wo po ho : Nat} (L : HLay b d.size st wo po ho) (m : ZlibNg.DeflateMedium.Match)
    (mic : UInt32) (hm2 : 2 ≤ mic.toNat) (hm3 : mic.toNat ≤ 258) (hl : 2 ≤ m.match_length.toNat)
    (ho2 : m.orgstart.toNat ≤ m.strstart.toNat + m.match_length.toNat)
    (hs : m.strstart.toNat + m.match_length.toNat ≤ 65536)
    (hr : wo + m.strstart.toNat + m.match_length.toNat + 3 ≤ d.size) :
    Sat (SH H i z b st d) (ZlibNg.DeflateMedium.insert_match (some b) (.ref (.heap b) wo) m mic)
      (BKeep H i z b st d (ho + 131072)) := by
  unfold ZlibNg.DeflateMedium.insert_match
  have hs1 : (m.strstart + 1).toNat = m.strstart.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  have hl1 : (m.match_length - 1).toNat = m.match_length.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
  have hmx : (2 * mic).toNat = 2 * mic.toNat := by rw [UInt32.toNat_mul]; simp; omega
  -- the common tail: `count` positions from `str`, `str + count = s + len`
  have tail : ∀ str cnt : UInt32, str.toNat + cnt.toNat = m.strstart.toNat + m.match_length.toNat →
      Sat (SH H i z b st d) (if cnt ≤ 2 * mic then do
          insert_knuth_batch (some b) (.ref (.heap b) wo) str cnt
          return ()
        else insert_knuth_stepped (some b) (.ref (.heap b) wo) str cnt mic) (BKeep H i z b st d (ho + 131072)) := by
    intro str cnt he
    split
    · refine Sat.bind (Sat.mono (insert_knuth_batch_SH L str cnt (by omega)) ?_)
      rintro _ _ ⟨d', rfl, hw⟩; exact Sat.pure ⟨d', rfl, hw⟩
    · rename_i hc
      have hc' : 2 * mic.toNat < cnt.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hc); omega
      exact insert_knuth_stepped_SH L str cnt mic (by omega) hm2 (by omega) (by omega)
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
      refine Sat.bind (Sat.mono (insert_knuth_SH L _ (by rw [hm1]; omega)) ?_)
      rintro _ _ ⟨d', rfl, hw⟩; exact Sat.pure ⟨d', rfl, hw⟩
    · exact tail _ _ (by rw [hd]; omega)
  · exact tail _ _ (by rw [hs1, hl1]; omega)

end

end ZlibNgF.Proof.MediumInsert
