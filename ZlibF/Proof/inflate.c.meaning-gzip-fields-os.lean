import ZlibF.Proof.«inflate.c.meaning-gzip-fields-exlen»

/-!
# inflate.c: `OS` and `TIME` keep the format meaning

`TIME` waits for the four bytes of `MTIME` (`NEEDBITS(32)`) and adds them to the header CRC
through `hbuf` (`CRC4`) when `FHCRC` is set; `OS` does the same with the two bytes `XFL`, `OS`
(`CRC2`). Both fall through: `TIME` into `OS`, `OS` into `EXLEN`. A short input leaves inside the
ten fixed bytes, which no complete header ends in (`gzipShort_of_length`).
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

/-! ## `CRC4` -/

/-- `hbuf` after `CRC4(check, word)`: the low four bytes of `word`. -/
def crc4Bytes (a : Array UInt8) (word : UInt64) : Array UInt8 :=
  ((((a.set! 0 word.toUInt8).set! 1 (word >>> 8).toUInt8).set! 2 (word >>> 16).toUInt8).set! 3
    (word >>> 24).toUInt8)

/-- The check value after `CRC4(check, word)`. -/
def crc4Value (check word : UInt64) : UInt64 :=
  (ZlibF.Spec.crc32Update check.toUInt32
    [word.toUInt8, (word >>> 8).toUInt8, (word >>> 16).toUInt8, (word >>> 24).toUInt8]).toUInt64

theorem crc4Bytes_size (a : Array UInt8) (word : UInt64) : (crc4Bytes a word).size = a.size := by
  simp [crc4Bytes]

theorem CRC4_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) {b : Nat} {a : Array UInt8}
    (hbufAt : c.hbuf = .ref (.blk b) 0) (bytes : h.bytes b = some a) (size : a.size = 4)
    (writable : h.ro b = false) (statics : Zlib.Crc32.Proofs.StaticsOK h) :
    runX (CRC4 c) l h = .ok ((.ok (), l),
      Zlib.Inflate.Spec.setI (Space.put h (BRef.blk b) (crc4Bytes a l.hold)) zs
        { s with check := crc4Value s.check l.hold }) := by
  let a1 := a.set! 0 l.hold.toUInt8
  let a2 := a1.set! 1 (l.hold >>> 8).toUInt8
  let a3 := a2.set! 2 (l.hold >>> 16).toUInt8
  let a4 := a3.set! 3 (l.hold >>> 24).toUInt8
  let h1 := Space.put h (BRef.blk b) a1
  let h2 := Space.put h (BRef.blk b) a2
  let h3 := Space.put h (BRef.blk b) a3
  let h4 := Space.put h (BRef.blk b) a4
  have size1 : a1.size = 4 := by simp [a1, size]
  have size2 : a2.size = 4 := by simp [a2, size1]
  have size3 : a3.size = 4 := by simp [a3, size2]
  have get1 : Space.get h1 (BRef.blk b) = some a1 := by simp only [h1, Space.get, Space.put, upd_same]
  have get2 : Space.get h2 (BRef.blk b) = some a2 := by simp only [h2, Space.get, Space.put, upd_same]
  have get3 : Space.get h3 (BRef.blk b) = some a3 := by simp only [h3, Space.get, Space.put, upd_same]
  have store1 : store8 c.hbuf l.hold.toUInt8 h = .ok ((), h1) := by
    rw [hbufAt]
    exact Ptr.store_ok (R := BRef) bytes writable (by omega)
  have add1 : (Ptr.ref (BRef.blk b) 0 : BPtr).add 1 h1 = .ok (.ref (.blk b) 1, h1) :=
    Ptr.add_ok (R := BRef) (T := UInt8) (h := h1) (off := 0) (k := 1) get1 (by omega) (by rw [size1]; omega)
  have store2 : store8 (.ref (.blk b) 1) (l.hold >>> 8).toUInt8 h1 = .ok ((), h2) := by
    have := Ptr.store_ok (R := BRef) (h := h1) (off := 1) (v := (l.hold >>> 8).toUInt8) get1 writable
      (by rw [size1]; omega)
    have same : Space.put h1 (BRef.blk b) (a1.set! 1 (l.hold >>> 8).toUInt8) = h2 := by
      simp only [h2, h1, Space.put, upd_upd, a2]
    rw [same] at this
    exact this
  have add2 : (Ptr.ref (BRef.blk b) 0 : BPtr).add 2 h2 = .ok (.ref (.blk b) 2, h2) :=
    Ptr.add_ok (R := BRef) (T := UInt8) (h := h2) (off := 0) (k := 2) get2 (by omega) (by rw [size2]; omega)
  have store3 : store8 (.ref (.blk b) 2) (l.hold >>> 16).toUInt8 h2 = .ok ((), h3) := by
    have := Ptr.store_ok (R := BRef) (h := h2) (off := 2) (v := (l.hold >>> 16).toUInt8) get2 writable
      (by rw [size2]; omega)
    have same : Space.put h2 (BRef.blk b) (a2.set! 2 (l.hold >>> 16).toUInt8) = h3 := by
      simp only [h3, h2, Space.put, upd_upd, a3]
    rw [same] at this
    exact this
  have add3 : (Ptr.ref (BRef.blk b) 0 : BPtr).add 3 h3 = .ok (.ref (.blk b) 3, h3) :=
    Ptr.add_ok (R := BRef) (T := UInt8) (h := h3) (off := 0) (k := 3) get3 (by omega) (by rw [size3]; omega)
  have store4 : store8 (.ref (.blk b) 3) (l.hold >>> 24).toUInt8 h3 = .ok ((), h4) := by
    have := Ptr.store_ok (R := BRef) (h := h3) (off := 3) (v := (l.hold >>> 24).toUInt8) get3 writable
      (by rw [size3]; omega)
    have same : Space.put h3 (BRef.blk b) (a3.set! 3 (l.hold >>> 24).toUInt8) = h4 := by
      simp only [h4, h3, Space.put, upd_upd, a4]
    rw [same] at this
    exact this
  have env4 : Env c h4 r zs z s := ⟨E.strm, E.st, by cases r <;> exact E.hz, E.hs⟩
  have bytes4 : h4.bytes b = some (crc4Bytes a l.hold) := by
    simp only [h4, Space.put, upd_same]
    rfl
  have crc := Zlib.Crc32.Proofs.crc32_correct h4 statics s.check b 0 (crc4Bytes a l.hold) bytes4 4
    (by rw [crc4Bytes_size, size]; decide)
  have list : ((crc4Bytes a l.hold).toList.drop 0).take (4 : UInt32).toNat =
      [l.hold.toUInt8, (l.hold >>> 8).toUInt8, (l.hold >>> 16).toUInt8, (l.hold >>> 24).toUInt8] := by
    apply List.ext_getElem
    · simp [crc4Bytes_size, size]
    · intro n one two
      simp only [List.length_take, List.length_drop, Array.length_toList, crc4Bytes_size] at one
      have small : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by simp at one; omega
      rcases small with rfl | rfl | rfl | rfl <;>
        simp [crc4Bytes, Array.set!, Array.setIfInBounds, size]
  rw [list] at crc
  have crc' : Zlib.Crc32.crc32 s.check (.ref (.blk b) 0) 4 h4 = .ok (crc4Value s.check l.hold, h4) := crc
  unfold CRC4
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok store1]
  simp only []
  rw [hbufAt]
  rw [runX_bind, runX_lift_ok add1]
  simp only []
  rw [runX_bind, runX_lift_ok store2]
  simp only []
  rw [runX_bind, runX_lift_ok add2]
  simp only []
  rw [runX_bind, runX_lift_ok store3]
  simp only []
  rw [runX_bind, runX_lift_ok add3]
  simp only []
  rw [runX_bind, runX_lift_ok store4]
  simp only []
  rw [runX_bind, runX_rdS env4]
  simp only []
  rw [runX_bind, runX_lift_ok crc']
  simp only []
  rw [runX_wrS env4]
  rfl

#print axioms CRC4_run

theorem crc4Value_of {check : UInt64} {bytes : List UInt8} {hold : UInt64} {p q u v : UInt8}
    (cf : check = (crc32 bytes).toUInt64) (val : hold.toNat = leValue [p, q, u, v]) :
    crc4Value check hold = (crc32 (bytes ++ [p, q, u, v])).toUInt64 := by
  obtain ⟨e0, e1, e2, e3⟩ := hold_four val
  unfold crc4Value
  rw [e0, e1, e2, e3, cf, toUInt32_of_crc, MeaningChecksum.crc_continue]

theorem env_crc {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (b : Nat) (a : Array UInt8) (s2 : InflateState) :
    Env c (Zlib.Inflate.Spec.setI (Space.put h (BRef.blk b) a) zs s2) r zs z s2 :=
  ⟨E.strm, E.st, by rw [ZStreamRef.get_setI, byte_view_put_stream]; exact E.hz, setI_istates_same _ _ _⟩

theorem keep_crc0 {c : Ctx} {h : Heap} {b : Nat} {a a' : Array UInt8} {l : IL} (hb : Hbuf c h b a)
    (apart : HbufInputApart c l) (size : a'.size = 4) (zs : Nat) (s2 s3 : InflateState) :
    InputKept h (Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI (Space.put h (BRef.blk b) a') zs s2) zs s3) l :=
  ((InputKept.hbuf apart hb.at_ hb.bytes hb.ro (by rw [size, hb.size])).trans (InputKept.setI _ zs s2 l)).trans
    (InputKept.setI _ zs s3 l)

/-! ## `OS` -/

set_option maxHeartbeats 4000000 in
theorem os_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {zs : Nat} {s : InflateState} {bytes rest : List UInt8} (E : Env c h r zs z s)
    (g : GzAt c f h l zs s bytes rest) (mode : s.mode = OS)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) {b : Nat} {a : Array UInt8} (hb : Hbuf c h b a)
    (apart : HbufInputApart c l) :
    ∃ result l' h', runX (inflate_OS c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have lo : TIME ≤ s.mode := by rw [mode]; decide
  have hi : s.mode ≤ HCRC := by rw [mode]; decide
  obtain ⟨gzb, len4, flagsInt, crcF, _, posAll⟩ := g.hm.2.2.2.2.1 lo hi
  obtain ⟨bitsLe, four, fourLen, bytesEq⟩ := posAll.2.1 mode
  have head := g.head
  have w4 := g.wrap4
  have method : bytes.getD 2 0 = 8 := by rw [bytesEq]; simp
  have flagsEq : s.flags = flagsWord (bytes.getD 3 0) := flagsWord_eq flagsInt method
  have small : (bytes.getD 3 0).toNat < 32 := by
    have v := g.viable
    rw [bytesEq] at v
    exact small_of_viable v
  have short0 : GzipShort bytes := gzipShort_of_length (by rw [bytesEq]; simp [fourLen])
  unfold inflate_OS
  obtain ⟨result, l', j, run, shape, next, count, bitsCount, enough, leaveFacts, kinds, bitsMax,
    loopAt⟩ := g.needbits range short0 16 (by decide) (ok := fun b => b ≤ 16)
      (fun m => by rw [mode] at m; exact absurd m (by decide))
      (fun hold bits b' okb _ _ _ p => gzpos_os mode ⟨okb, (p.2.1 mode).2⟩)
  have n16 : (16 : UInt32).toNat = 16 := rfl
  rw [runX_bind, run]
  rcases kinds with rfl | rfl
  · have atLeast := enough rfl
    rw [n16] at atLeast bitsMax
    have aligned := g.bits
    have bits16 : l'.bits.toNat = 16 := by
      have := bitsLe
      change l.bits.toNat ≤ 16 at this
      omega
    have inEq : l'.in_ = l.in_ := by rw [shape]
    have g' := g.pulled (loopAt (by omega)) range inEq count bitsCount
    have restLen : (rest ++ (f.inp.drop (loopRead l)).take j).length = 2 := by
      have := g'.bits
      omega
    obtain ⟨x, y, xy⟩ : ∃ x y, rest ++ (f.inp.drop (loopRead l)).take j = [x, y] := by
      generalize rest ++ (f.inp.drop (loopRead l)).take j = w at restLen
      match w, restLen with
      | [x, y], _ => exact ⟨x, y, rfl⟩
    rw [xy] at g'
    have holdVal : l'.hold.toNat = x.toNat + 256 * y.toNat := by
      rw [g'.hold]
      simp [leValue]
    have apart' : HbufInputApart c l' := apart.advance next count
    simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_ldS E]
    simp only [head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [runX_bind, runX_lift_ok (hcrcOn_env E)]
    simp only []
    rw [show (s.flags &&& 0x0200 != 0 && s.wrap &&& 4 != 0) =
      decide ((bytes.getD 3 0).toNat / 2 % 2 = 1) by rw [flagsEq, flagsWord_hcrc, w4, Bool.and_true]]
    obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := [x, y]) bytesEq
    have sixLen : (four ++ [x, y]).length = 6 := by simp [fourLen]
    have form : bytes ++ [x, y] = [31, 139, 8, bytes.getD 3 0] ++ (four ++ [x, y]) := by
      rw [bytesEq]; simp
    have viable : GzipViable (bytes ++ [x, y]) := by
      rw [form]; exact gzipViable_fixed small _ sixLen
    have position : ∀ s' : InflateState, s'.mode = EXLEN →
        GzipPosition (loopState s' { l' with hold := 0, bits := 0 }) ((bytes ++ [x, y]).getD 3 0)
          (bytes ++ [x, y]) := by
      intro s' m'
      rw [getSame]
      exact gzpos_exlen m' ⟨by show (0 : UInt32).toNat ≤ 16; decide, fun _ => rfl, four ++ [x, y], sixLen, form⟩
    by_cases fh : (bytes.getD 3 0).toNat / 2 % 2 = 1
    · simp only [fh, decide_true, ↓reduceIte]
      rw [runX_bind, CRC2_run E l' hb.at_ hb.bytes hb.size hb.ro statics]
      simp only []
      let s2 : InflateState := { s with check := crc2Value s.check l'.hold }
      have E2 := env_crc E b (crc2Bytes a l'.hold) s2
      rw [runX_bind, runX_INITBITS]
      simp only []
      rw [runX_bind, runX_setMode E2]
      simp only []
      let s3 : InflateState := { s2 with mode := EXLEN }
      have size' : (crc2Bytes a l'.hold).size = 4 := by rw [crc2Bytes_size, hb.size]
      have g3 : GzAt c f (Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI (Space.put h (BRef.blk b)
          (crc2Bytes a l'.hold)) zs s2) zs s3) { l' with hold := 0, bits := 0 } zs s3
          (bytes ++ [x, y]) [] := by
        refine g'.step range (by simp) (keep_crc0 hb apart' size' zs s2 s3)
          0 (Nat.zero_le _) (inputAdvance_zero l'.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
          (by simp) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by show EXLEN ≠ SYNC; decide)
          viable (by show TIME ≤ EXLEN; decide) (by show EXLEN ≤ HCRC; decide) start
          (by show s.flags = _; rw [getSame, flagsEq])
          (fun _ => by
            show crc2Value s.check l'.hold = _
            exact crc2Value_of (crcF fh) holdVal) (position s3 rfl)
      exact exlen_step (envSetI E2 s3) g3 rfl statics (((hb.put _ size').setI zs s2).setI zs s3) apart'
    · simp only [fh, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, runX_INITBITS]
      simp only []
      rw [runX_bind, runX_setMode E]
      simp only []
      let s3 : InflateState := { s with mode := EXLEN }
      have g3 : GzAt c f (Zlib.Inflate.Spec.setI h zs s3) { l' with hold := 0, bits := 0 } zs s3
          (bytes ++ [x, y]) [] := by
        refine g'.step range (by simp) (InputKept.setI _ _ _ l')
          0 (Nat.zero_le _) (inputAdvance_zero l'.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
          (by simp) (Kept.mode s EXLEN) (by show EXLEN ≠ SYNC; decide)
          viable (by show TIME ≤ EXLEN; decide) (by show EXLEN ≤ HCRC; decide) start
          (by show s.flags = _; rw [getSame, flagsEq])
          (fun fh' => absurd (by rw [getSame] at fh'; exact fh') fh) (position s3 rfl)
      exact exlen_step (envSetI E s3) g3 rfl statics (hb.setI zs s3) apart'
  · have below := (leaveFacts rfl).2
    rw [n16] at below
    exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (loopAt (by omega))⟩⟩

#print axioms os_step

/-! ## `TIME` -/

set_option maxHeartbeats 4000000 in
theorem time_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {zs : Nat} {s : InflateState} {bytes rest : List UInt8} (E : Env c h r zs z s)
    (g : GzAt c f h l zs s bytes rest) (mode : s.mode = TIME)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) {b : Nat} {a : Array UInt8} (hb : Hbuf c h b a)
    (apart : HbufInputApart c l) :
    ∃ result l' h', runX (inflate_TIME c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have lo : TIME ≤ s.mode := by rw [mode]; decide
  have hi : s.mode ≤ HCRC := by rw [mode]; decide
  obtain ⟨gzb, len4, flagsInt, crcF, _, posAll⟩ := g.hm.2.2.2.2.1 lo hi
  obtain ⟨bytesEq, bitsLe⟩ := posAll.1 mode
  have head := g.head
  have w4 := g.wrap4
  have method : bytes.getD 2 0 = 8 := by rw [bytesEq]; simp
  have flagsEq : s.flags = flagsWord (bytes.getD 3 0) := flagsWord_eq flagsInt method
  have bytesEq' : bytes = [31, 139, 8, bytes.getD 3 0] ++ [] := by
    rw [List.append_nil]; exact bytesEq
  have small : (bytes.getD 3 0).toNat < 32 := by
    have v := g.viable
    rw [bytesEq'] at v
    exact small_of_viable v
  have short0 : GzipShort bytes := gzipShort_of_length (by rw [bytesEq]; simp)
  unfold inflate_TIME
  obtain ⟨result, l', j, run, shape, next, count, bitsCount, enough, leaveFacts, kinds, bitsMax,
    loopAt⟩ := g.needbits range short0 32 (by decide) (ok := fun b => b ≤ 32)
      (fun m => by rw [mode] at m; exact absurd m (by decide))
      (fun hold bits b' okb _ _ _ p => gzpos_time mode ⟨(p.1 mode).1, okb⟩)
  have n32 : (32 : UInt32).toNat = 32 := rfl
  rw [runX_bind, run]
  rcases kinds with rfl | rfl
  · have atLeast := enough rfl
    rw [n32] at atLeast bitsMax
    have aligned := g.bits
    have bits32 : l'.bits.toNat = 32 := by
      have := bitsLe
      change l.bits.toNat ≤ 32 at this
      omega
    have inEq : l'.in_ = l.in_ := by rw [shape]
    have g' := g.pulled (loopAt (by omega)) range inEq count bitsCount
    have restLen : (rest ++ (f.inp.drop (loopRead l)).take j).length = 4 := by
      have := g'.bits
      omega
    obtain ⟨p, q, u, v, pq⟩ : ∃ p q u v, rest ++ (f.inp.drop (loopRead l)).take j = [p, q, u, v] := by
      generalize rest ++ (f.inp.drop (loopRead l)).take j = w at restLen
      match w, restLen with
      | [p, q, u, v], _ => exact ⟨p, q, u, v, rfl⟩
    rw [pq] at g'
    have holdVal : l'.hold.toNat = leValue [p, q, u, v] := g'.hold
    have apart' : HbufInputApart c l' := apart.advance next count
    simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_ldS E]
    simp only [head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [runX_bind, runX_lift_ok (hcrcOn_env E)]
    simp only []
    rw [show (s.flags &&& 0x0200 != 0 && s.wrap &&& 4 != 0) =
      decide ((bytes.getD 3 0).toNat / 2 % 2 = 1) by rw [flagsEq, flagsWord_hcrc, w4, Bool.and_true]]
    obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := [p, q, u, v]) bytesEq'
    have form : bytes ++ [p, q, u, v] = [31, 139, 8, bytes.getD 3 0] ++ [p, q, u, v] := by
      conv => lhs; rw [bytesEq]
    have viable : GzipViable (bytes ++ [p, q, u, v]) := by
      rw [form]
      exact (gzipViable_fixed small ([p, q, u, v] ++ [0, 0]) rfl).of_prefix ⟨[0, 0], by simp⟩
    have position : ∀ s' : InflateState, s'.mode = OS →
        GzipPosition (loopState s' { l' with hold := 0, bits := 0 }) ((bytes ++ [p, q, u, v]).getD 3 0)
          (bytes ++ [p, q, u, v]) := by
      intro s' m'
      rw [getSame]
      exact gzpos_os m' ⟨by show (0 : UInt32).toNat ≤ 16; decide, [p, q, u, v], rfl, form⟩
    by_cases fh : (bytes.getD 3 0).toNat / 2 % 2 = 1
    · simp only [fh, decide_true, ↓reduceIte]
      rw [runX_bind, CRC4_run E l' hb.at_ hb.bytes hb.size hb.ro statics]
      simp only []
      let s2 : InflateState := { s with check := crc4Value s.check l'.hold }
      have E2 := env_crc E b (crc4Bytes a l'.hold) s2
      rw [runX_bind, runX_INITBITS]
      simp only []
      rw [runX_bind, runX_setMode E2]
      simp only []
      let s3 : InflateState := { s2 with mode := OS }
      have size' : (crc4Bytes a l'.hold).size = 4 := by rw [crc4Bytes_size, hb.size]
      have g3 : GzAt c f (Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI (Space.put h (BRef.blk b)
          (crc4Bytes a l'.hold)) zs s2) zs s3) { l' with hold := 0, bits := 0 } zs s3
          (bytes ++ [p, q, u, v]) [] := by
        refine g'.step range (by simp) (keep_crc0 hb apart' size' zs s2 s3)
          0 (Nat.zero_le _) (inputAdvance_zero l'.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
          (by simp) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by show OS ≠ SYNC; decide)
          viable (by show TIME ≤ OS; decide) (by show OS ≤ HCRC; decide) start
          (by show s.flags = _; rw [getSame, flagsEq])
          (fun _ => by
            show crc4Value s.check l'.hold = _
            exact crc4Value_of (crcF fh) holdVal) (position s3 rfl)
      exact os_step (envSetI E2 s3) g3 rfl statics (((hb.put _ size').setI zs s2).setI zs s3) apart'
    · simp only [fh, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, runX_INITBITS]
      simp only []
      rw [runX_bind, runX_setMode E]
      simp only []
      let s3 : InflateState := { s with mode := OS }
      have g3 : GzAt c f (Zlib.Inflate.Spec.setI h zs s3) { l' with hold := 0, bits := 0 } zs s3
          (bytes ++ [p, q, u, v]) [] := by
        refine g'.step range (by simp) (InputKept.setI _ _ _ l')
          0 (Nat.zero_le _) (inputAdvance_zero l'.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
          (by simp) (Kept.mode s OS) (by show OS ≠ SYNC; decide)
          viable (by show TIME ≤ OS; decide) (by show OS ≤ HCRC; decide) start
          (by show s.flags = _; rw [getSame, flagsEq])
          (fun fh' => absurd (by rw [getSame] at fh'; exact fh') fh) (position s3 rfl)
      exact os_step (envSetI E s3) g3 rfl statics (hb.setI zs s3) apart'
  · have below := (leaveFacts rfl).2
    rw [n32] at below
    exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (loopAt (by omega))⟩⟩

#print axioms time_step

end Zlib.Inflate.Proofs.MeaningGzipFields
