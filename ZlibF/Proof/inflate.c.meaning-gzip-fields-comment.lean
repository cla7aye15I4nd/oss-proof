import ZlibF.Proof.«inflate.c.meaning-gzip-fields-string»

/-!
# inflate.c: `COMMENT` and `NAME` keep the format meaning

With the flag set, the mode reads the unread input through the first zero byte. Without a zero,
it leaves: the field so far is longer, and the header still needs its zero (`gzipShort_*`). With
the zero, the field is complete and the mode falls through to the next one (`COMMENT` into
`HCRC`, `NAME` into `COMMENT`). Without the flag it falls through at once.
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

/-! ## Helpers -/

theorem statics_setI {h : Heap} (statics : Zlib.Crc32.Proofs.StaticsOK h) (zs : Nat) (s : InflateState) :
    Zlib.Crc32.Proofs.StaticsOK (Zlib.Inflate.Spec.setI h zs s) := statics

theorem Kept.refl (s : InflateState) : Kept s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Kept.trans {a b c : InflateState} (x : Kept a b) (y : Kept b c) : Kept a c := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11⟩ := x
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11⟩ := y
  exact ⟨y1.trans x1, y2.trans x2, y3.trans x3, y4.trans x4, y5.trans x5, y6.trans x6, y7.trans x7,
    y8.trans x8, y9.trans x9, y10.trans x10, y11.trans x11⟩

theorem Kept.mode (s : InflateState) (m : UInt32) : Kept s { s with mode := m } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Kept.lengthMode (s : InflateState) (len : UInt32) (m : UInt32) :
    Kept s { s with length := len, mode := m } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem strState_facts (s : InflateState) (on : Bool) (bs : List UInt8) :
    Kept s (strState s on bs) ∧ (strState s on bs).flags = s.flags ∧ (strState s on bs).mode = s.mode ∧
      (on = true → (strState s on bs).check =
        (ZlibF.Spec.crc32Update s.check.toUInt32 (bs.take (firstStop bs))).toUInt64) := by
  cases on
  · exact ⟨Kept.refl s, rfl, rfl, fun e => by cases e⟩
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, fun _ => rfl⟩

/-- The heap after the header CRC of a string field. -/
theorem str_heap {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (statics : Zlib.Crc32.Proofs.StaticsOK h) (on : Bool) (bs : List UInt8) :
    Env c (if on = true then Zlib.Inflate.Spec.setI h zs (strState s true bs) else h) r zs z
        (strState s on bs) ∧
      (∀ l, InputKept h (if on = true then Zlib.Inflate.Spec.setI h zs (strState s true bs) else h) l) ∧
      Zlib.Crc32.Proofs.StaticsOK (if on = true then Zlib.Inflate.Spec.setI h zs (strState s true bs) else h) := by
  cases on
  · exact ⟨E, fun l => InputKept.refl h l, statics⟩
  · exact ⟨envSetI E _, fun l => InputKept.setI h zs _ l, statics⟩

theorem toUInt32_of_crc (x : UInt32) : x.toUInt64.toUInt32 = x := by
  apply UInt32.toNat_inj.mp
  simp

theorem strRegs_next {l : IL} {ref : BRef} {off : Nat} {bs : List UInt8} (next : l.next = .ref ref off) :
    (strRegs l ref off bs).next = inputAdvance l.next (firstStop bs) := by
  rw [next]; rfl

theorem strRegs_count {l : IL} {ref : BRef} {off : Nat} {bs : List UInt8}
    (le : firstStop bs ≤ l.have_.toNat) :
    (strRegs l ref off bs).have_.toNat + firstStop bs = l.have_.toNat := by
  have small := l.have_.toNat_lt
  have k : (UInt32.ofNat (firstStop bs)).toNat = firstStop bs := by
    simp only [UInt32.toNat_ofNat']
    omega
  show (l.have_ - UInt32.ofNat (firstStop bs)).toNat + firstStop bs = l.have_.toNat
  rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [k]; exact le)), k]
  omega

theorem strCopyK_empty {c : Ctx} {sel : GzHeader → BPtr} {cap : GzHeader → UInt32} {k : X Unit} {l : IL}
    {h : Heap} (zero : l.have_ = 0) : runX (strCopyK c sel cap k) l h = .ok ((.error Ex.leave, l), h) := by
  unfold strCopyK
  rw [runX_bind, runX_get]
  simp only [zero, beq_self_eq_true, ↓reduceIte]
  rw [runX_bind, runX_throw]

/-- The unread input as a byte view. -/
theorem GzAt.view {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes rest : List UInt8} (g : GzAt c f h l zs s bytes rest) (pos : 0 < l.have_.toNat) :
    ∃ ref off A, l.next = .ref ref off ∧ Space.get h ref = some A ∧ off + l.have_.toNat ≤ A.size ∧
      f.inp.drop (loopRead l) = (A.toList.drop off).take l.have_.toNat := by
  have count := g.binv.have_eq
  rcases g.binv.next with empty | ⟨ref, A, off, ptr, get, fit, content⟩
  · rw [empty] at count
    simp at count
    omega
  · refine ⟨ref, off, A, ptr, get, by rw [count]; exact fit, by rw [count]; exact content⟩

theorem start_append {bytes u : List UInt8} {t : List UInt8}
    (e : bytes = [31, 139, 8, bytes.getD 3 0] ++ t) :
    (bytes ++ u).getD 3 0 = bytes.getD 3 0 ∧
      ∃ t', bytes ++ u = [31, 139, 8, (bytes ++ u).getD 3 0] ++ t' := by
  have len : 4 ≤ bytes.length := by rw [e]; simp
  have same : (bytes ++ u).getD 3 0 = bytes.getD 3 0 := getD_append (by omega)
  refine ⟨same, t ++ u, ?_⟩
  rw [same]
  conv => lhs; rw [e]
  simp

theorem small_of_viable {flg : UInt8} {t : List UInt8} (v : GzipViable ([31, 139, 8, flg] ++ t)) :
    flg.toNat < 32 :=
  (gzipViable_reject v).2

theorem six_split {six : List UInt8} (len : six.length = 6) :
    ∃ mt xfl os, mt.length = 4 ∧ six = mt ++ [xfl, os] := by
  match six, len with
  | [a, b, c, d, e, f], _ => exact ⟨[a, b, c, d], e, f, rfl, rfl⟩

/-! ## `COMMENT` -/

set_option maxHeartbeats 2000000 in
theorem comment_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {zs : Nat} {s : InflateState} {bytes rest : List UInt8} (E : Env c h r zs z s)
    (g : GzAt c f h l zs s bytes rest) (mode : s.mode = COMMENT)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) :
    ∃ result l' h', runX (inflate_COMMENT c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have lo : TIME ≤ s.mode := by rw [mode]; decide
  have hi : s.mode ≤ HCRC := by rw [mode]; decide
  obtain ⟨gzb, len4, flagsInt, crcF, _, posAll⟩ := g.hm.2.2.2.2.1 lo hi
  obtain ⟨bits0, six, ex, nm, part, sixLen, exLimit, nmOk, partOk, noFc, bytesEq⟩ :=
    posAll.2.2.2.2.2.1 mode
  have method : bytes.getD 2 0 = 8 := by rw [bytesEq]; simp
  have flagsEq : s.flags = flagsWord (bytes.getD 3 0) := flagsWord_eq flagsInt method
  have head := g.head
  have w4 := g.wrap4
  have l0 : l.bits = 0 := bits0
  have restNil : rest = [] := by
    have := g.bits
    rw [l0] at this
    have z : rest.length = 0 := by simp at this; omega
    exact List.eq_nil_of_length_eq_zero z
  subst restNil
  have hold0 : l.hold = 0 := by
    apply UInt64.toNat_inj.mp
    rw [g.hold]
    rfl
  have small : (bytes.getD 3 0).toNat < 32 := by
    have v := g.viable
    rw [bytesEq] at v
    exact small_of_viable (by simpa only [List.append_assoc] using v)
  obtain ⟨mt, xfl, os, mtLen, sixEq⟩ := six_split sixLen
  unfold inflate_COMMENT
  rw [runX_bind, runX_rdS E]
  simp only [flagsEq, flagsWord_comment]
  by_cases fc : (bytes.getD 3 0).toNat / 16 % 2 = 1
  · simp only [fc, decide_true, ↓reduceIte]
    show ∃ result l' h', runX (strCopyK c (fun g => g.comment) (fun g => g.comm_max)
      (do (monadLift (setMode c.st HCRC) : X Unit); inflate_HCRC c)) l h = .ok ((result, l'), h') ∧
        TripOutcome c f result h' l'
    have short0 : GzipShort bytes := by
      rw [bytesEq]; exact gzipShort_comment sixLen exLimit nmOk fc partOk
    by_cases hz : l.have_ = 0
    · rw [strCopyK_empty hz]
      exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (g.loop short0)⟩⟩
    have pos : 0 < l.have_.toNat := by
      have : l.have_.toNat ≠ 0 := fun e => hz (UInt32.toNat_inj.mp (by simpa using e))
      omega
    obtain ⟨ref, off, A, next, get, fit, inpEq⟩ := g.view pos
    rw [strCopyK_run E head statics next get fit pos, ← inpEq]
    generalize bsDef : f.inp.drop (loopRead l) = bs
    have bsLen : bs.length = l.have_.toNat := by
      rw [← bsDef]; have := g.binv.have_eq; omega
    have ne : bs ≠ [] := by intro e; rw [e] at bsLen; simp at bsLen; omega
    have kle : firstStop bs ≤ l.have_.toNat := by have := firstStop_le bs; omega
    have kpos := firstStop_pos bs ne
    generalize onDef : ((flagsWord (bytes.getD 3 0) &&& 0x0200) != 0 && (s.wrap &&& 4) != 0) = on
    obtain ⟨E2, keep2, statics2⟩ := str_heap E statics on bs
    obtain ⟨kept2, flags2, mode2, check2⟩ := strState_facts s on bs
    have onEq : on = decide ((bytes.getD 3 0).toNat / 2 % 2 = 1) := by
      rw [← onDef, flagsWord_hcrc, w4, Bool.and_true]
    have crc2 : (bytes.getD 3 0).toNat / 2 % 2 = 1 →
        (strState s on bs).check = (crc32 (bytes ++ bs.take (firstStop bs))).toUInt64 := by
      intro fh
      have onT : on = true := by rw [onEq]; exact decide_eq_true fh
      have cf : s.check = (crc32 bytes).toUInt64 := crcF fh
      rw [check2 onT, cf, toUInt32_of_crc, MeaningChecksum.crc_continue]
    rw [show (s.flags &&& 0x0200 != 0 && s.wrap &&& 4 != 0) = on by rw [flagsEq]; exact onDef]
    have regs : (strRegs l ref off bs).ret = l.ret ∧ (strRegs l ref off bs).in_ = l.in_ ∧
        (strRegs l ref off bs).out_ = l.out_ ∧ (strRegs l ref off bs).left = l.left ∧
        (strRegs l ref off bs).put = l.put := ⟨rfl, rfl, rfl, rfl, rfl⟩
    split
    · -- the terminating zero: on to `HCRC`
      rename_i zero
      have takeEq := firstStop_zero ne zero
      have noZero := firstStop_take_nonzero bs
      rw [runX_bind, runX_setMode E2]
      simp only []
      let s3 : InflateState := { strState s on bs with mode := HCRC }
      have g3 : GzAt c f (Zlib.Inflate.Spec.setI
          (if on = true then Zlib.Inflate.Spec.setI h zs (strState s true bs) else h) zs s3)
          (strRegs l ref off bs) zs s3
          (bytes ++ bs.take (firstStop bs)) [] := by
        obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := bs.take (firstStop bs)) (by
          rw [bytesEq]; simp only [List.append_assoc]; rfl)
        have hdr : bytes ++ bs.take (firstStop bs) =
            Gzip.header (bytes.getD 3 0) mt xfl os ex nm (part ++ bs.take (firstStop bs - 1)) := by
          rw [gzip_header_parts, takeEq]
          conv => lhs; rw [bytesEq]
          rw [sixEq]
          simp only [gzipCommentPart, fc, ↓reduceIte, List.append_assoc]
        have fields : GzipFields (bytes.getD 3 0) mt ex nm (part ++ bs.take (firstStop bs - 1)) :=
          ⟨small, mtLen, exLimit, nmOk, by simp [partOk, noZero]⟩
        refine g.step range (by simp) ((keep2 l).trans (InputKept.setI _ _ _ l)) (firstStop bs) kle
          (strRegs_next next) (strRegs_count kle) regs hold0 l0
          (by rw [bsDef, List.append_nil]) (kept2.trans (Kept.mode _ HCRC)) (by show HCRC ≠ SYNC; decide)
          (by rw [hdr]; exact gzipViable_core fields) (by show TIME ≤ HCRC; decide)
          (by show HCRC ≤ HCRC; decide) start
          (by show (strState s on bs).flags = _; rw [flags2, getSame, flagsEq])
          (fun fh => by
            show (strState s on bs).check = _
            rw [getSame] at fh
            exact crc2 fh) ?_
        rw [getSame]
        exact gzpos_hcrc rfl ⟨by show l.bits.toNat ≤ 16; rw [l0]; decide, fun _ => l0,
          mt, xfl, os, ex, nm, part ++ bs.take (firstStop bs - 1), fields, hdr⟩
      exact hcrc_step (envSetI E2 s3) g3 rfl
    · -- no zero: leave inside the comment
      rename_i nonzero
      obtain ⟨all, noZero⟩ := firstStop_all ne nonzero
      have takeAll : bs.take (firstStop bs) = bs := by rw [all, List.take_length]
      have partOk' : (0 : UInt8) ∉ part ++ bs := by simp [partOk, noZero]
      obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := bs.take (firstStop bs)) (by
        rw [bytesEq]; simp only [List.append_assoc]; rfl)
      have form : bytes ++ bs.take (firstStop bs) = [31, 139, 8, bytes.getD 3 0] ++ six ++
          gzipExtraPart (bytes.getD 3 0) ex ++ gzipNamePart (bytes.getD 3 0) nm ++ (part ++ bs) := by
        rw [takeAll]
        conv => lhs; rw [bytesEq]
        simp only [List.append_assoc]
      have g4 : GzAt c f (if on = true then Zlib.Inflate.Spec.setI h zs (strState s true bs) else h)
          (strRegs l ref off bs) zs (strState s on bs)
          (bytes ++ bs.take (firstStop bs)) [] := by
        refine g.step range E2.hs (keep2 l) (firstStop bs) kle
          (strRegs_next next) (strRegs_count kle) regs hold0 l0
          (by rw [bsDef, List.append_nil]) kept2 (by rw [mode2, mode]; decide)
          (by
            rw [form]
            simpa using gzipViable_comment small fc sixLen exLimit nmOk partOk' [] (Or.inl rfl))
          (by rw [mode2, mode]; decide) (by rw [mode2, mode]; decide) start
          (by rw [flags2, getSame, flagsEq])
          (fun fh => by rw [getSame] at fh; exact crc2 fh) ?_
        rw [getSame]
        exact gzpos_comment (mode2.trans mode) ⟨l0, six, ex, nm, part ++ bs, sixLen, exLimit, nmOk,
          partOk', fun nf => absurd fc (by omega), form⟩
      have short4 : GzipShort (bytes ++ bs.take (firstStop bs)) := by
        rw [form]; exact gzipShort_comment sixLen exLimit nmOk fc partOk'
      exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (g4.loop short4)⟩⟩
  · simp only [fc, decide_false, Bool.false_eq_true, ↓reduceIte]
    have partNil : part = [] := noFc (by omega)
    subst partNil
    rw [runX_bind, runX_ldS E]
    simp only [head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [runX_bind, runX_setMode E]
    simp only []
    let s3 : InflateState := { s with mode := HCRC }
    have hdr : bytes ++ [] = Gzip.header (bytes.getD 3 0) mt xfl os ex nm [] := by
      rw [gzip_header_parts, List.append_nil]
      conv => lhs; rw [bytesEq]
      rw [sixEq]
      simp only [gzipCommentPart, fc, ↓reduceIte, List.append_assoc, List.append_nil]
    have fields : GzipFields (bytes.getD 3 0) mt ex nm [] := ⟨small, mtLen, exLimit, nmOk, by simp⟩
    obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := []) (by
      rw [bytesEq]; simp only [List.append_assoc]; rfl)
    have g3 : GzAt c f (Zlib.Inflate.Spec.setI h zs s3) l zs s3 (bytes ++ []) [] := by
      refine g.step range (by simp) (InputKept.setI _ _ _ l) 0 (Nat.zero_le _)
        (inputAdvance_zero l.next).symm (by omega) ⟨rfl, rfl, rfl, rfl, rfl⟩ hold0 l0
        (by simp) (Kept.mode s HCRC) (by show HCRC ≠ SYNC; decide) (by rw [hdr]; exact gzipViable_core fields)
        (by show TIME ≤ HCRC; decide) (by show HCRC ≤ HCRC; decide) start (by show s.flags = _; rw [getSame, flagsEq])
        (fun fh => by
          show s.check = _
          rw [getSame] at fh
          have cf : s.check = (crc32 bytes).toUInt64 := crcF fh
          rw [cf, List.append_nil]) ?_
      rw [getSame]
      exact gzpos_hcrc rfl ⟨by show l.bits.toNat ≤ 16; rw [l0]; decide, fun _ => l0,
        mt, xfl, os, ex, nm, [], fields, hdr⟩
    exact hcrc_step (envSetI E s3) g3 rfl

#print axioms comment_step

end Zlib.Inflate.Proofs.MeaningGzipFields
