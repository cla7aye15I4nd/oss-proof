import ZlibNgF.Proof.«inflate.c.check-modes»

/-!
# The `inf_leave` epilogue of `inflate` (`ZlibNgF`)

`RESTORE()`, `updatewindow` with or without a check value (`inf_chksum` / `inf_chksum_cpy`: `crc32_braid` or
`adler32_c`, then the copy into the window, `crc32_copy_braid` / `adler32_copy_c`), the totals, `data_type` and the
`Z_BUF_ERROR` rule (with the check of the output when there is no window). `G3`: the heap with block `b`'s bytes, its
state record and the stream record replaced, the shape every step of `updatewindow` keeps. `leave_ok`: from the loop
invariant, the epilogue returns with the structural invariant and the frame of the call.
-/

set_option autoImplicit false
namespace ZlibNgF.Proof.InflateLeave
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core view upd_upd ldState_app ldStream_app)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size memcpy_heap add_heap space_get_heap)
open ZlibNgF.Proof.InflateWindow (WinOk uwTail uw_split add_neg)
open ZlibNgF.Proof.ChunkMem (upd_self)
open ZlibNgF.Proof.InflateLoop (LI Env EnvOK SizeKeep Frame.trans Frame.mono HdrOK)
open ZlibNgF.Proof.InflateX

/-- A heap whose byte block `b`, state record of block `b` and stream record `i` are replaced. -/
def G3 (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream) : Heap :=
  { H with bytes := upd H.bytes b (some d), istates := upd H.istates b (some st), streams := upd H.streams i (some zz) }

theorem G3_G3 (H : Heap) (i b : Nat) (d d' : Array UInt8) (st st' : InflateState) (zz zz' : ZStream) :
    G3 (G3 H i b d st zz) i b d' st' zz' = G3 H i b d' st' zz' := by
  simp only [G3, upd_upd]

theorem G3_self {H : Heap} {i b : Nat} {d : Array UInt8} {st : InflateState} {zz : ZStream}
    (hd : H.bytes b = some d) (hs : H.istates b = some st) (hz : H.streams i = some zz) : G3 H i b d st zz = H := by
  simp only [G3, upd_self _ _ _ hd, upd_self _ _ _ hs, upd_self _ _ _ hz]

theorem G3_istate (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream) :
    (G3 H i b d st zz).istate b = some st := by
  simp [G3, Heap.istate]

theorem G3_get (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream) {r : BRef}
    (hr : r ≠ .heap b) : Space.get (G3 H i b d st zz) r = Space.get H r := by
  cases r with
  | heap c =>
    have : c ≠ b := fun e => hr (e ▸ rfl)
    show upd H.bytes b (some d) c = H.bytes c
    exact upd_ne _ _ _ _ this
  | const _ => rfl
  | str _ => rfl

theorem G3_ldState (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream) :
    ldState (some b) (G3 H i b d st zz) = .ok (st, G3 H i b d st zz) := ldState_app (G3_istate ..)

theorem G3_stateOf (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream)
    (hzb : zz.state = some b) : ZlibNg.Inflate.stateOf (some i) (G3 H i b d st zz) = .ok (some b, G3 H i b d st zz) := by
  simp [ZlibNg.Inflate.stateOf, rdZ, bind_app, ldStream, G3, hzb]

theorem G3_wrS (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream)
    (f : InflateState → InflateState) :
    ZlibNg.Inflate.wrS (some b) f (G3 H i b d st zz) = .ok ((), G3 H i b d (f st) zz) := by
  rw [ZlibNgF.Proof.InflateLoop.wrS_app (G3_istate ..)]
  simp only [ZlibNgF.Proof.InflateLoop.withS, G3, upd_upd]

theorem G3_wrZ (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream)
    (f : ZStream → ZStream) :
    ZlibNg.Inflate.wrZ (some i) f (G3 H i b d st zz) = .ok ((), G3 H i b d st (f zz)) := by
  simp [ZlibNg.Inflate.wrZ, bind_app, ldStream, stStream, G3, upd_upd]

theorem G3_rdS {α : Type} (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream)
    (g : InflateState → α) : ZlibNg.Inflate.rdS (some b) g (G3 H i b d st zz) = .ok (g st, G3 H i b d st zz) := by
  simp [ZlibNg.Inflate.rdS, bind_app, G3_ldState]

/-- `memcpy` into block `b` from another object. -/
theorem G3_memcpy (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream) {r : BRef}
    {sd : Array UInt8} (hr : r ≠ .heap b) (hg : Space.get H r = some sd) {od os n : Nat} (h1 : od + n ≤ d.size)
    (h2 : os + n ≤ sd.size) :
    Ptr.memcpy (.ref (.heap b) od) (.ref r os) n (G3 H i b d st zz) =
      .ok ((), G3 H i b (copyFold sd od os (List.range' 0 n) d) st zz) := by
  have hd : (G3 H i b d st zz).bytes b = some d := by simp [G3]
  have hg' : Space.get (G3 H i b d st zz) r = some sd := by rw [G3_get _ _ _ _ _ _ hr]; exact hg
  rw [memcpy_heap hd hg' hr h1 h2]
  simp only [G3, upd_upd]

/-- `inf_chksum(strm, src, len)` over `len` readable bytes of another object. -/
theorem G3_chksum {H : Heap} {i b : Nat} {d : Array UInt8} {st : InflateState} {zz : ZStream}
    (hc : H.crcTable = ZlibNg.Crc32Tbl.crc_table) (hzb : zz.state = some b) {r : BRef} {sd : Array UInt8}
    (hr : r ≠ .heap b) (hg : Space.get H r = some sd) {os : Nat} (len : UInt32) (hle : os + len.toNat ≤ sd.size) :
    Sat (G3 H i b d st zz) (inf_chksum (some i) (.ref r os) len)
      (fun _ H' => ∃ v : UInt64, H' = G3 H i b d { st with check := v } { zz with adler := v }) := by
  unfold inf_chksum
  refine Sat.bind (Sat.of_eq (G3_stateOf _ _ _ _ _ _ hzb) ?_)
  refine Sat.bind (Sat.of_eq (G3_ldState ..) ?_)
  have hg' : Space.get (G3 H i b d st zz) r = some sd := by rw [G3_get _ _ _ _ _ _ hr]; exact hg
  have hlen : os + len.toUInt64.toNat ≤ sd.size := by rw [UInt32.toNat_toUInt64]; exact hle
  extract_lets jp
  have hjp : ∀ v : UInt32, Sat (G3 H i b d st zz) (jp v)
      (fun _ H' => ∃ v : UInt64, H' = G3 H i b d { st with check := v } { zz with adler := v }) := by
    intro v
    simp only [jp]
    refine Sat.bind (Sat.of_eq (G3_wrS ..) ?_)
    exact Sat.of_eq (G3_wrZ ..) ⟨v.toUInt64, rfl⟩
  clear_value jp
  split
  · obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Crc32.crc32_braid_ok (show (G3 H i b d st zz).crcTable = _ from hc) hg' st.check.toUInt32 os len.toUInt64 hlen
    exact Sat.bind (Sat.of_eq e (hjp v))
  · obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Adler32Safe.adler32_c_safe hg' st.check.toUInt32 os len.toUInt64 hlen
    exact Sat.bind (Sat.of_eq e (hjp v))

/-- `inf_chksum_cpy(strm, window + od, src, copy)` from another object into block `b`. -/
theorem G3_chksumCpy {H : Heap} {i b : Nat} {d : Array UInt8} {st : InflateState} {zz : ZStream}
    (hc : H.crcTable = ZlibNg.Crc32Tbl.crc_table) (hzb : zz.state = some b) {r : BRef} {sd : Array UInt8}
    (hr : r ≠ .heap b) (hg : Space.get H r = some sd) {od os : Nat} (copy : UInt32) (h1 : od + copy.toNat ≤ d.size)
    (h2 : os + copy.toNat ≤ sd.size) :
    Sat (G3 H i b d st zz) (inf_chksum_cpy (some i) (.ref (.heap b) od) (.ref r os) copy)
      (fun _ H' => ∃ ck ad : UInt64, H' = G3 H i b (copyFold sd od os (List.range' 0 copy.toNat) d)
        { st with check := ck } { zz with adler := ad }) := by
  unfold inf_chksum_cpy
  split
  · rename_i h0
    have h0' : copy = 0 := by simpa using h0
    subst h0'
    exact Sat.pure ⟨st.check, zz.adler, rfl⟩
  refine Sat.bind (Sat.of_eq (G3_stateOf _ _ _ _ _ _ hzb) ?_)
  refine Sat.bind (Sat.of_eq (G3_ldState ..) ?_)
  have hg' : Space.get (G3 H i b d st zz) r = some sd := by rw [G3_get _ _ _ _ _ _ hr]; exact hg
  have hlen : os + copy.toUInt64.toNat ≤ sd.size := by rw [UInt32.toNat_toUInt64]; exact h2
  have hm := G3_memcpy H i b d st zz hr hg h1 h2
  extract_lets jp
  have hjp : ∀ v : UInt32, Sat (G3 H i b (copyFold sd od os (List.range' 0 copy.toNat) d) st zz) (jp v)
      (fun _ H' => ∃ ck ad : UInt64, H' = G3 H i b (copyFold sd od os (List.range' 0 copy.toNat) d)
        { st with check := ck } { zz with adler := ad }) := by
    intro v
    simp only [jp]
    refine Sat.bind (Sat.of_eq (G3_wrS ..) ?_)
    exact Sat.of_eq (G3_wrZ ..) ⟨v.toUInt64, v.toUInt64, rfl⟩
  clear_value jp
  split
  · obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Crc32.crc32_braid_ok (show (G3 H i b d st zz).crcTable = _ from hc) hg' st.check.toUInt32 os copy.toUInt64 hlen
    refine Sat.bind (Sat.bind (Sat.of_eq e (Sat.bind (Sat.of_eq (by rw [UInt32.toNat_toUInt64]; exact hm)
      (Sat.pure ?_)))))
    exact hjp v
  · obtain ⟨v, e, -⟩ := ZlibNgF.Proof.Adler32Safe.adler32_c_safe hg' st.check.toUInt32 os copy.toUInt64 hlen
    refine Sat.bind (Sat.bind (Sat.of_eq e (Sat.bind (Sat.of_eq (by rw [UInt32.toNat_toUInt64]; exact hm)
      (Sat.pure ?_)))))
    exact hjp v

macro "u32_omega" : tactic => `(tactic| (simp only [UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, ← UInt32.toNat_inj,
  UInt32.toNat_add, UInt32.toNat_sub, UInt32.toNat_ofNat, UInt32.toNat_zero, ne_eq] at *; omega))

/-- What `updatewindow` leaves: new window bytes of the same size, window fields with their clauses, a check value. -/
def UWPost (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream) (_ : Unit) (H' : Heap) : Prop :=
  ∃ (d' : Array UInt8) (wh wn : UInt32) (ck ad : UInt64), d'.size = d.size ∧ WinOk st.wsize wh wn ∧
    H' = G3 H i b d' { st with wnext := wn, whave := wh, check := ck } { zz with adler := ad }

theorem uwTailG_ok {H : Heap} {i b woff os : Nat} {d sd : Array UInt8} {st : InflateState} {zz : ZStream}
    {r : BRef} {len : UInt32} (cksum : Int32) (hc : H.crcTable = ZlibNg.Crc32Tbl.crc_table)
    (hzb : zz.state = some b) (hwin : st.window = .val (.ref (.heap b) woff)) (hsz : woff + 32832 ≤ d.size)
    (hws : st.wsize.toNat ≤ 32768) (W : WinOk st.wsize st.whave st.wnext) (hr : r ≠ .heap b)
    (hsd : Space.get H r = some sd) (hos : os + len.toNat ≤ sd.size) :
    Sat (G3 H i b d st zz) (uwTail (some i) (some b) (.ref r (os + len.toNat)) len cksum)
      (UWPost H i b d st zz) := by
  have hwh := W.whave
  have hwl := W.le
  have hwe := W.eq
  have hwn := W.wnext
  have hsd' : Space.get (G3 H i b d st zz) r = some sd := by rw [G3_get _ _ _ _ _ _ hr]; exact hsd
  have hdb : (G3 H i b d st zz).bytes b = some d := by simp [G3]
  unfold uwTail
  refine Sat.bind (Sat.of_eq (G3_ldState ..) ?_)
  rw [hwin]
  refine Sat.bind (Sat.of_eq (a := (.ref (.heap b) woff : BPtr)) rfl ?_)
  split
  · rename_i hA
    have hA' : st.wsize.toNat ≤ len.toNat := hA
    extract_lets jp jp1
    have hjp : ∀ (u : Unit) (d1 : Array UInt8) (ck ad : UInt64), d1.size = d.size →
        Sat (G3 H i b d1 { st with check := ck } { zz with adler := ad }) (jp u) (UWPost H i b d st zz) := by
      intro u d1 ck ad hd1
      simp only [jp]
      refine Sat.bind (Sat.of_eq (G3_wrS ..) ?_)
      refine Sat.of_eq (G3_wrS ..) ⟨d1, st.wsize, 0, ck, ad, hd1, ⟨UInt32.le_refl _, Or.inl rfl, by u32_omega,
        fun h => absurd h (UInt32.lt_irrefl _)⟩, rfl⟩
    have hjp1 : ∀ (u : Unit) (ck ad : UInt64),
        Sat (G3 H i b d { st with check := ck } { zz with adler := ad }) (jp1 u) (UWPost H i b d st zz) := by
      intro u ck ad
      simp only [jp1]
      have hg1 : Space.get (G3 H i b d { st with check := ck } { zz with adler := ad }) r = some sd := by
        rw [G3_get _ _ _ _ _ _ hr]; exact hsd
      refine Sat.bind (Sat.of_eq (add_neg (k := st.wsize.toNat) hg1 (by omega) hos) ?_)
      refine Sat.bind (Sat.mono (G3_chksumCpy (d := d) (st := { st with check := ck }) (zz := { zz with adler := ad })
        (od := woff) (os := os + len.toNat - st.wsize.toNat) hc hzb hr hsd st.wsize (by omega) (by omega)) ?_)
      rintro u2 H2 ⟨ck', ad', rfl⟩
      exact hjp u2 _ ck' ad' (copyFold_size ..)
    clear_value jp jp1
    split
    · split
      · rename_i _ hB
        have hB' : st.wsize.toNat < len.toNat := hB
        refine Sat.bind (Sat.of_eq (add_neg (k := len.toNat) hsd' (by omega) hos) ?_)
        refine Sat.bind (Sat.mono (G3_chksum hc hzb hr hsd (os := os + len.toNat - len.toNat) (len - st.wsize)
          (by rw [UInt32.toNat_sub_of_le _ _ hA]; omega)) ?_)
        rintro u2 H2 ⟨v, rfl⟩
        exact hjp1 u2 v v
      · exact hjp1 () st.check zz.adler
    · refine Sat.bind (Sat.of_eq (add_neg (k := st.wsize.toNat) hsd' (by omega) hos) ?_)
      refine Sat.bind (Sat.of_eq (G3_memcpy H i b d st zz (od := woff) (os := os + len.toNat - st.wsize.toNat)
        (n := st.wsize.toNat) hr hsd (by omega) (by omega)) ?_)
      exact hjp () _ st.check zz.adler (copyFold_size ..)
  · rename_i hA
    have hB : len < st.wsize := UInt32.not_le.mp hA
    have hB' : len.toNat < st.wsize.toNat := hB
    have hn' : st.wnext.toNat ≤ st.whave.toNat := hwl
    have hh' : st.whave.toNat ≤ st.wsize.toNat := hwh
    extract_lets dist0 D L1 jp2 jp3 jp
    have hD : D = (if st.wsize - st.wnext > len then len else st.wsize - st.wnext) := rfl
    have hL1 : L1 = len - D := rfl
    clear_value L1
    subst hL1
    clear_value D
    have hDn : D.toNat ≤ len.toNat ∧ st.wnext.toNat + D.toNat ≤ st.wsize.toNat ∧
        (D.toNat < len.toNat → D.toNat = st.wsize.toNat - st.wnext.toNat) := by
      have hsub : (st.wsize - st.wnext).toNat = st.wsize.toNat - st.wnext.toNat :=
        UInt32.toNat_sub_of_le _ _ (by u32_omega)
      by_cases hc : st.wsize - st.wnext > len
      · simp only [hD, hc, ↓reduceIte]; have : len.toNat < (st.wsize - st.wnext).toNat := hc; omega
      · simp only [hD, hc, ↓reduceIte]; have : ¬ len.toNat < (st.wsize - st.wnext).toNat := hc; omega
    have hlen : (len - D).toNat = len.toNat - D.toNat := UInt32.toNat_sub_of_le _ _ (by u32_omega)
    have hjp2 : ∀ (u : Unit) (d2 : Array UInt8) (ck ad : UInt64), d2.size = d.size → len - D ≠ 0 →
        Sat (G3 H i b d2 { st with check := ck } { zz with adler := ad }) (jp2 u) (UWPost H i b d st zz) := by
      intro u d2 ck ad hd2 hL
      have hL' : len.toNat - D.toNat ≠ 0 := by
        intro h0; apply hL; rw [← UInt32.toNat_inj, hlen, h0]; rfl
      have hDw : D.toNat = st.wsize.toNat - st.wnext.toNat := hDn.2.2 (by omega)
      simp only [jp2]
      refine Sat.bind (Sat.of_eq (G3_wrS ..) ?_)
      exact Sat.of_eq (G3_wrS ..) ⟨d2, st.wsize, len - D, ck, ad, hd2, ⟨UInt32.le_refl _, Or.inr (by u32_omega),
        by u32_omega, fun h => absurd h (UInt32.lt_irrefl _)⟩, rfl⟩
    have hjp3 : ∀ (u : Unit) (d1 : Array UInt8) (ck ad : UInt64) (wn : UInt32), d1.size = d.size →
        len - D = 0 → ((wn = st.wnext + D ∧ st.wnext + D ≠ st.wsize) ∨ (wn = 0 ∧ st.wnext + D = st.wsize)) →
        Sat (G3 H i b d1 { st with check := ck, wnext := wn } { zz with adler := ad }) (jp3 u)
          (UWPost H i b d st zz) := by
      intro u d1 ck ad wn hd1 hL0 hwn'
      have hDl : D.toNat = len.toNat := by
        have : (len - D).toNat = 0 := by rw [hL0]; rfl
        omega
      have hw1 := st.wsize.toNat_lt
      obtain ⟨hD1, hD2, -⟩ := hDn
      have hsum : (st.wnext + D).toNat = st.wnext.toNat + D.toNat := by
        rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hsum2 : (st.whave + D).toNat = st.whave.toNat + D.toNat := by
        rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      simp only [jp3]
      refine Sat.bind (Sat.of_eq (G3_rdS ..) ?_)
      refine Sat.bind (Sat.of_eq (G3_rdS ..) ?_)
      dsimp only
      have hE := hwe
      split
      · rename_i hy
        refine Sat.of_eq (G3_wrS ..) ⟨d1, st.whave + D, wn, ck, ad, hd1, ?_, rfl⟩
        have hE' : st.wnext.toNat = st.whave.toNat := congrArg UInt32.toNat (hE hy)
        have hy' : st.whave.toNat < st.wsize.toNat := hy
        rcases hwn' with ⟨e, e'⟩ | ⟨e, e'⟩ <;> subst e
        · have e'' : st.wnext.toNat + D.toNat ≠ st.wsize.toNat := fun h => e' (UInt32.toNat_inj.mp (by rw [hsum]; exact h))
          refine ⟨?_, Or.inr ?_, ?_, fun _ => ?_⟩
          · rw [UInt32.le_iff_toNat_le, hsum2]; omega
          · rw [UInt32.lt_iff_toNat_lt, hsum]; omega
          · rw [UInt32.le_iff_toNat_le, hsum2, hsum]; omega
          · rw [← UInt32.toNat_inj, hsum2, hsum]; omega
        · have e'' : st.wnext.toNat + D.toNat = st.wsize.toNat := by rw [← hsum, e']
          refine ⟨?_, Or.inl rfl, ?_, fun h => ?_⟩
          · rw [UInt32.le_iff_toNat_le, hsum2]; omega
          · exact UInt32.zero_le
          · rw [UInt32.lt_iff_toNat_lt, hsum2] at h; omega
      · rename_i hy
        refine Sat.pure ⟨d1, st.whave, wn, ck, ad, hd1, ?_, rfl⟩
        have hy' : st.wsize.toNat ≤ st.whave.toNat := by have := UInt32.not_lt.mp hy; exact this
        have hwe' : st.whave.toNat = st.wsize.toNat := by omega
        rcases hwn' with ⟨e, e'⟩ | ⟨e, e'⟩ <;> subst e
        · have e'' : st.wnext.toNat + D.toNat ≠ st.wsize.toNat := fun h => e' (UInt32.toNat_inj.mp (by rw [hsum]; exact h))
          refine ⟨hwh, Or.inr ?_, ?_, fun h => absurd h (UInt32.not_lt.mpr (UInt32.le_iff_toNat_le.mpr hy'))⟩
          · rw [UInt32.lt_iff_toNat_lt, hsum]; omega
          · rw [UInt32.le_iff_toNat_le, hsum]; omega
        · exact ⟨hwh, Or.inl rfl, UInt32.zero_le, fun h => absurd h (UInt32.not_lt.mpr (UInt32.le_iff_toNat_le.mpr hy'))⟩
    have hjp : ∀ (u : Unit) (d1 : Array UInt8) (ck ad : UInt64), d1.size = d.size →
        Sat (G3 H i b d1 { st with check := ck } { zz with adler := ad }) (jp u) (UWPost H i b d st zz) := by
      intro u d1 ck ad hd1
      simp only [jp]
      have hg1 : Space.get (G3 H i b d1 { st with check := ck } { zz with adler := ad }) r = some sd := by
        rw [G3_get _ _ _ _ _ _ hr]; exact hsd
      split
      · rename_i hL
        have hL' : len - D ≠ 0 := by simpa using hL
        have hL'' : len.toNat - D.toNat ≠ 0 := by
          intro h0; apply hL'; rw [← UInt32.toNat_inj, hlen, h0]; rfl
        split
        · refine Sat.bind (Sat.of_eq (add_neg (k := (len - D).toNat) hg1 (by omega) hos) ?_)
          refine Sat.bind (Sat.mono (G3_chksumCpy (d := d1) (st := { st with check := ck })
            (zz := { zz with adler := ad }) (od := woff) (os := os + len.toNat - (len - D).toNat) hc hzb hr hsd
            (len - D) (by have := hDn.2.2 (by omega); omega) (by omega)) ?_)
          rintro u2 H2 ⟨ck', ad', rfl⟩
          exact hjp2 u2 _ ck' ad' (by rw [copyFold_size, hd1]) hL'
        · refine Sat.bind (Sat.of_eq (add_neg (k := (len - D).toNat) hg1 (by omega) hos) ?_)
          refine Sat.bind (Sat.of_eq (G3_memcpy H i b d1 _ _ (od := woff) (os := os + len.toNat - (len - D).toNat)
            (n := (len - D).toNat) hr hsd (by have := hDn.2.2 (by omega); omega) (by omega)) ?_)
          exact hjp2 () _ ck ad (by rw [copyFold_size, hd1]) hL'
      · rename_i hL
        have hL0 : len - D = 0 := by simpa using hL
        refine Sat.bind (Sat.of_eq (G3_wrS ..) ?_)
        refine Sat.bind (Sat.of_eq (G3_rdS ..) ?_)
        refine Sat.bind (Sat.of_eq (G3_rdS ..) ?_)
        dsimp only
        split
        · rename_i hx
          refine Sat.bind (Sat.of_eq (G3_wrS ..) ?_)
          exact hjp3 () d1 ck ad 0 hd1 hL0 (Or.inr ⟨rfl, by simpa using hx⟩)
        · rename_i hx
          exact hjp3 () d1 ck ad (st.wnext + D) hd1 hL0 (Or.inl ⟨rfl, by simpa using hx⟩)
    clear_value jp jp2 jp3
    have hdb' := add_heap (off := woff) (k := st.wnext.toNat) hdb (by omega)
    split
    · refine Sat.bind (Sat.of_eq hdb' ?_)
      refine Sat.bind (Sat.of_eq (add_neg (k := len.toNat) hsd' (by omega) hos) ?_)
      rw [Nat.add_sub_cancel]
      refine Sat.bind (Sat.mono (G3_chksumCpy (od := woff + st.wnext.toNat) (os := os) hc hzb hr hsd D
        (by omega) (by omega)) ?_)
      rintro u2 H2 ⟨ck', ad', rfl⟩
      exact hjp u2 _ ck' ad' (copyFold_size ..)
    · refine Sat.bind (Sat.of_eq hdb' ?_)
      refine Sat.bind (Sat.of_eq (add_neg (k := len.toNat) hsd' (by omega) hos) ?_)
      rw [Nat.add_sub_cancel]
      refine Sat.bind (Sat.of_eq (G3_memcpy H i b d st zz (od := woff + st.wnext.toNat) (os := os)
        (n := D.toNat) hr hsd (by omega) (by omega)) ?_)
      exact hjp () _ st.check zz.adler (copyFold_size ..)

/-- `updatewindow(strm, end, len, cksum)` on an invariant stream, from `len` bytes of another object ending at
`end`: the window bytes, the window fields and the check value of the state and `adler` of the stream change. -/
theorem updatewindowG_ok {H : Heap} {i b : Nat} {z : ZStream} {st : InflateState} {al : InflateAllocs}
    (c : Core H (some i) z b (view st) al) (hz : H.streams i = some z) (hzb : z.state = some b)
    (hs : H.istates b = some st) (hcrc : H.crcTable = ZlibNg.Crc32Tbl.crc_table) {r : BRef} {os : Nat}
    {sd : Array UInt8} {len : UInt32} (cksum : Int32) (hr : r ≠ .heap b) (hsd : Space.get H r = some sd)
    (hos : os + len.toNat ≤ sd.size) :
    Sat H (updatewindow (some i) (.ref r (os + len.toNat)) len cksum) (fun _ H' =>
      ∃ (data d' : Array UInt8) (ws wh wn : UInt32) (ck ad : UInt64), H.bytes b = some data ∧ d'.size = data.size ∧
        ws ≤ 32768 ∧ WinOk ws wh wn ∧
        H' = G3 H i b d' { st with wsize := ws, wnext := wn, whave := wh, check := ck } { z with adler := ad }) := by
  obtain ⟨woff, data, hwin, hdata, hwsz, hws, hwh, hwn⟩ := ZlibNgF.Proof.InflateDict.window_nat c
  have hself := G3_self hdata hs hz
  have key : Sat (G3 H i b data st z) (updatewindow (some i) (.ref r (os + len.toNat)) len cksum) (fun _ H' =>
      ∃ (data d' : Array UInt8) (ws wh wn : UInt32) (ck ad : UInt64), H.bytes b = some data ∧ d'.size = data.size ∧
        ws ≤ 32768 ∧ WinOk ws wh wn ∧
        H' = G3 H i b d' { st with wsize := ws, wnext := wn, whave := wh, check := ck } { z with adler := ad }) := by
    rw [uw_split]
    refine Sat.bind (Sat.of_eq (G3_stateOf _ _ _ _ _ _ hzb) ?_)
    refine Sat.bind (Sat.of_eq (G3_rdS ..) ?_)
    dsimp only
    split
    · rename_i h0
      have h0' : st.wsize = 0 := by simpa using h0
      have hwb : st.wbits ≤ 15 := c.wbits
      have hwb' : st.wbits.toNat ≤ 15 := hwb
      have hlt : st.wbits < 32 := by rw [UInt32.lt_iff_toNat_lt]; show _ < 32; omega
      refine Sat.bind (Sat.of_eq (G3_rdS ..) ?_)
      refine Sat.bind (Sat.of_eq (a := (1 : UInt32) <<< st.wbits) (H' := G3 H i b data st z) (by simp [shl32, hlt]) ?_)
      refine Sat.bind (Sat.of_eq (G3_wrS ..) ?_)
      have hwh0 : st.whave = 0 := by have : st.whave ≤ st.wsize := c.whave; rw [h0'] at this; u32_omega
      have hwn0 : st.wnext = 0 := by have : st.wnext ≤ st.whave := c.wnext_le; rw [hwh0] at this; u32_omega
      have hws1 : ((1 : UInt32) <<< st.wbits).toNat ≤ 32768 := by
        rw [InflateWindow.shl_toNat _ hwb]
        have : 2 ^ st.wbits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hwb'
        omega
      have W1 : WinOk ((1 : UInt32) <<< st.wbits) st.whave st.wnext := by
        refine ⟨?_, Or.inl hwn0, ?_, fun _ => hwn0.trans hwh0.symm⟩
        · rw [hwh0]; u32_omega
        · rw [hwn0, hwh0]; exact UInt32.le_refl _
      refine Sat.mono (uwTailG_ok (st := { st with wsize := (1 : UInt32) <<< st.wbits }) cksum hcrc hzb hwin hwsz
        hws1 W1 hr hsd hos) ?_
      rintro _ H' ⟨d', wh, wn, ck, ad, hd', W, rfl⟩
      exact ⟨data, d', _, wh, wn, ck, ad, hdata, hd', InflateInv.shl_le _ hwb, W, rfl⟩
    · refine Sat.mono (uwTailG_ok cksum hcrc hzb hwin hwsz hws ⟨c.whave, c.wnext, c.wnext_le, c.wnext_eq⟩ hr hsd
        hos) ?_
      rintro _ H' ⟨d', wh, wn, ck, ad, hd', W, rfl⟩
      exact ⟨data, d', st.wsize, wh, wn, ck, ad, hdata, hd', c.wsize, W, rfl⟩
  rwa [hself] at key

/-- `G3` changes only stream `i` and block `b`. -/
theorem G3_frame (H : Heap) (i b : Nat) (d : Array UInt8) (st : InflateState) (zz : ZStream) :
    Frame H (G3 H i b d st zz) [i] [b] [] [] := by
  refine ⟨fun j hj => ?_, fun _ _ => rfl, fun c _ hc => ?_, fun c _ hc data hd => ?_, fun c _ hc hd => ?_,
    rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  · have : j ≠ i := fun e => hj (e ▸ List.mem_singleton_self _)
    exact upd_ne _ _ _ _ this
  · have : c ≠ b := fun e => hc (e ▸ List.mem_singleton_self _)
    exact ⟨upd_ne _ _ _ _ this, rfl⟩
  · have : c ≠ b := fun e => hc (e ▸ List.mem_singleton_self _)
    exact ⟨data, by show upd H.bytes b (some d) c = _; rw [upd_ne _ _ _ _ this]; exact hd, rfl, fun _ _ _ => rfl⟩
  · have : c ≠ b := fun e => hc (e ▸ List.mem_singleton_self _)
    show upd H.bytes b (some d) c = _; rw [upd_ne _ _ _ _ this]; exact hd

/-- The loop invariant after `updatewindow`. -/
theorem LI.afterUW {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S)
    {data d' : Array UInt8} (hd : H.bytes E.b = some data) (hsz : d'.size = data.size) (ws wh wn : UInt32)
    (hws : ws ≤ 32768) (W : WinOk ws wh wn) (ck ad : UInt64) :
    LI E l (G3 H E.i E.b d' { S with wsize := ws, wnext := wn, whave := wh, check := ck } { z with adler := ad })
      { z with adler := ad } { S with wsize := ws, wnext := wn, whave := wh, check := ck } := by
  obtain ⟨al, hal, c⟩ := li.core
  refine ⟨⟨E.i, { z with adler := ad }, E.b, _, al, rfl, by simp [G3], li.hb, G3_istate .., ?_,
    { InflateWindow.core_win (h := H) (d' := d')
      (h' := G3 H E.i E.b d' { S with wsize := ws, wnext := wn, whave := wh, check := ck } { z with adler := ad })
      c (by simp [G3]) (fun d0 hd0 => by rw [hd] at hd0; cases hd0; exact hsz)
      rfl ws wh wn hws W with }⟩,
    Frame.trans li.frame (Frame.mono (G3_frame ..) (fun _ m => m) (fun _ m => m) (fun _ m => nomatch m)
      (fun _ m => nomatch m)), ?_, by simp [G3], li.hb, G3_istate .., li.head, ?_, li.inAt, li.outAt, li.bits⟩
  · simp only [Heap.iallocsOf, G3, upd_same]
    simpa [Heap.iallocsOf, hd] using hal
  · refine li.sz.trans ⟨fun c hc d0 hd0 => ⟨d0, ?_, rfl⟩, rfl⟩
    show upd H.bytes E.b (some d') c = _
    rw [upd_ne _ _ _ _ hc]; exact hd0
  · exact li.hdr

open ZlibNgF.Proof.InflateLoop in
theorem leave_ok (E : Env) (eo : EnvOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) :
    SatX H l (infLeave E.c) (fun r _ H' => (∃ v, r = .ok v) ∧ Fin E H') := by
  unfold infLeave
  refine SatX.bind (SatX.mono li.restoreX ?_)
  rintro r l1 H2 ⟨hr, hl1, li2⟩
  subst hr
  rw [hl1]
  dsimp (config := { zeta := false }) only
  refine SatX.bind (SatX.lift_eq li2.ldStream ?_)
  refine SatX.bind (SatX.get ?_)
  refine SatX.bind (SatX.lift_eq li2.ldState ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp (config := { zeta := false }) only
  extract_lets jpr jpb jp
  have hjpr : ∀ (u : Unit) (l' : IL) (H' : Heap), Fin E H' → SatX H' l' (jpr u)
      (fun r _ H' => (∃ v, r = .ok v) ∧ Fin E H') := by
    intro u l' H' hf
    simp only [jpr]
    exact SatX.bind (SatX.get (SatX.pure ⟨⟨_, rfl⟩, hf⟩))
  have hjpb : ∀ (u : Unit) (l' : IL) (H' : Heap), Fin E H' → SatX H' l' (jpb u)
      (fun r _ H' => (∃ v, r = .ok v) ∧ Fin E H') := by
    intro u l' H' hf
    simp only [jpb]
    exact SatX.bind (SatX.modify (hjpr () _ _ hf))
  obtain ⟨hlo, ob, hob1, hob2, hput⟩ := li2.outAt
  have hlo' : l.left.toNat ≤ l.out.toNat := hlo
  have hsubo : (l.out - l.left).toNat = l.out.toNat - l.left.toNat := UInt32.toNat_sub_of_le _ _ hlo
  have hjp : ∀ (u : Unit) (H' : Heap) (z' : ZStream) (S' : InflateState), LI E l H' z' S' →
      SatX H' l (jp u) (fun r _ H' => (∃ v, r = .ok v) ∧ Fin E H') := by
    intro u H' z' S' li'
    simp only [jp]
    refine SatX.bind (SatX.lift_eq li'.ldStream ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.get ?_)
    refine SatX.bind (SatX.lift (Sat.mono (li'.wrZ (fun z => { z with total_in := z.total_in +
      (l.in_ - z'.avail_in).toUInt64 }) rfl rfl rfl) ?_))
    intro _ H4 li4
    refine SatX.bind (SatX.lift (Sat.mono (li4.wrZ (fun z => { z with total_out := z.total_out +
      (l.out - z'.avail_out).toUInt64 }) rfl rfl rfl) ?_))
    intro _ H5 li5
    refine SatX.bind (SatX.lift (Sat.mono (li5.wrS (fun s => { s with total := s.total +
      (l.out - z'.avail_out).toUInt64 }) (fun _ _ c => c) rfl) ?_))
    intro _ H6 li6
    refine SatX.bind (SatX.lift_eq li6.ldState ?_)
    dsimp (config := { zeta := false }) only
    refine SatX.bind (SatX.lift (Sat.mono (li6.wrZ _ rfl rfl rfl) ?_))
    intro _ H7 li7
    refine SatX.ite (fun _ => ?_) (fun _ => ?_)
    · refine SatX.bind (SatX.lift_eq li7.ldState ?_)
      dsimp (config := { zeta := false }) only
      split
      · obtain ⟨p, hp, hp1, hp2⟩ := li7.outPos
        obtain ⟨dout, hdo, hdos⟩ := li7.outBytes eo
        rw [hput] at hp
        injection hp with _ hp
        refine SatX.bind (SatX.lift_eq (show Ptr.add l.put (-Int.ofNat (l.out - l.left).toNat) H7 = _ by
          rw [hput]; exact add_neg (r := .heap E.bo) hdo (by omega) (by omega)) ?_)
        refine SatX.bind (SatX.lift (Sat.mono (li7.chksum eo hdo _ (by omega)) ?_))
        rintro u2 H8 ⟨v, li8⟩
        exact hjpb u2 _ _ ⟨li8.inv, li8.frame⟩
      · exact hjpb () _ _ ⟨li7.inv, li7.frame⟩
    · exact hjpr () _ _ ⟨li7.inv, li7.frame⟩
  clear_value jp jpb jpr
  split
  · obtain ⟨al, -, c⟩ := li2.core
    obtain ⟨dout, hdo, hdos⟩ := li2.outBytes eo
    obtain ⟨-, -, -, hbne, -, -⟩ := eo.outW
    have hcrc : H2.crcTable = ZlibNg.Crc32Tbl.crc_table := li2.frame.2.2.2.2.2.2.1.trans eo.crc
    have hne : BRef.heap E.bo ≠ BRef.heap E.b := fun e => hbne (by injection e)
    rw [hput]
    refine SatX.bind (SatX.lift (Sat.mono (updatewindowG_ok c li2.hz li2.hb
      (ZlibNgF.Proof.InflateLoop.istates_of li2.hs) hcrc (r := .heap E.bo) (os := ob) (sd := dout) _ hne hdo
      (by omega)) ?_))
    rintro u H3 ⟨data, d', ws, wh, wn, ck, ad, hdata, hd', hws, W, rfl⟩
    exact hjp u _ _ _ (LI.afterUW li2 hdata hd' ws wh wn hws W ck ad)
  · exact hjp () _ _ _ li2

end ZlibNgF.Proof.InflateLeave
