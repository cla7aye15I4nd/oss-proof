import ZlibF.Proof.«inflate.c.meaning-gzip-fields-comment»

/-!
# inflate.c: `NAME` keeps the format meaning

As `COMMENT` (`inflate.c.meaning-gzip-fields-comment`): with `FNAME` the name is read through
its zero byte, or the mode leaves inside it; then `length = 0` and on to `COMMENT`.
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

set_option maxHeartbeats 2000000 in
theorem name_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {zs : Nat} {s : InflateState} {bytes rest : List UInt8} (E : Env c h r zs z s)
    (g : GzAt c f h l zs s bytes rest) (mode : s.mode = NAME)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) :
    ∃ result l' h', runX (inflate_NAME c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have lo : TIME ≤ s.mode := by rw [mode]; decide
  have hi : s.mode ≤ HCRC := by rw [mode]; decide
  obtain ⟨gzb, len4, flagsInt, crcF, _, posAll⟩ := g.hm.2.2.2.2.1 lo hi
  obtain ⟨bits0, six, ex, part, sixLen, exLimit, partOk, noFn, bytesEq⟩ :=
    posAll.2.2.2.2.1 mode
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
  unfold inflate_NAME
  rw [runX_bind, runX_rdS E]
  simp only [flagsEq, flagsWord_name]
  by_cases fn : (bytes.getD 3 0).toNat / 8 % 2 = 1
  · simp only [fn, decide_true, ↓reduceIte]
    show ∃ result l' h', runX (strCopyK c (fun g => g.name) (fun g => g.name_max)
      ((monadLift (wrS c.st fun s => { s with length := 0, mode := COMMENT }) : X Unit) >>= fun _ =>
        inflate_COMMENT c)) l h = .ok ((result, l'), h') ∧ TripOutcome c f result h' l'
    have short0 : GzipShort bytes := by
      rw [bytesEq]; exact gzipShort_name sixLen exLimit fn partOk
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
    · -- the terminating zero: on to `COMMENT`
      rename_i zero
      have takeEq := firstStop_zero ne zero
      have noZero := firstStop_take_nonzero bs
      rw [runX_bind, runX_wrS E2]
      simp only []
      let s3 : InflateState := { strState s on bs with length := 0, mode := COMMENT }
      have nmOk : (0 : UInt8) ∉ part ++ bs.take (firstStop bs - 1) := by simp [partOk, noZero]
      obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := bs.take (firstStop bs)) (by
        rw [bytesEq]; simp only [List.append_assoc]; rfl)
      have form : bytes ++ bs.take (firstStop bs) = [31, 139, 8, bytes.getD 3 0] ++ six ++
          gzipExtraPart (bytes.getD 3 0) ex ++
          gzipNamePart (bytes.getD 3 0) (part ++ bs.take (firstStop bs - 1)) ++ [] := by
        rw [takeEq]
        conv => lhs; rw [bytesEq]
        simp only [gzipNamePart, fn, ↓reduceIte, List.append_assoc, List.append_nil]
      have g3 : GzAt c f (Zlib.Inflate.Spec.setI
          (if on = true then Zlib.Inflate.Spec.setI h zs (strState s true bs) else h) zs s3)
          (strRegs l ref off bs) zs s3 (bytes ++ bs.take (firstStop bs)) [] := by
        refine g.step range (by simp) ((keep2 l).trans (InputKept.setI _ _ _ l)) (firstStop bs) kle
          (strRegs_next next) (strRegs_count kle) regs hold0 l0
          (by rw [bsDef, List.append_nil]) (kept2.trans (Kept.lengthMode _ 0 COMMENT))
          (by show COMMENT ≠ SYNC; decide)
          (by
            rw [takeEq]
            conv => arg 1; rw [bytesEq]
            simpa only [List.append_assoc] using
              gzipViable_name small fn sixLen exLimit nmOk [0] (Or.inr rfl))
          (by show TIME ≤ COMMENT; decide) (by show COMMENT ≤ HCRC; decide) start
          (by show (strState s on bs).flags = _; rw [flags2, getSame, flagsEq])
          (fun fh => by
            show (strState s on bs).check = _
            rw [getSame] at fh
            exact crc2 fh) ?_
        rw [getSame]
        exact gzpos_comment rfl ⟨l0, six, ex, part ++ bs.take (firstStop bs - 1), [], sixLen,
          exLimit, nmOk, by simp, fun _ => rfl, form⟩
      exact comment_step (envSetI E2 s3) g3 rfl (statics_setI statics2 zs s3)
    · -- no zero: leave inside the name
      rename_i nonzero
      obtain ⟨all, noZero⟩ := firstStop_all ne nonzero
      have takeAll : bs.take (firstStop bs) = bs := by rw [all, List.take_length]
      have partOk' : (0 : UInt8) ∉ part ++ bs := by simp [partOk, noZero]
      obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := bs.take (firstStop bs)) (by
        rw [bytesEq]; simp only [List.append_assoc]; rfl)
      have form : bytes ++ bs.take (firstStop bs) = [31, 139, 8, bytes.getD 3 0] ++ six ++
          gzipExtraPart (bytes.getD 3 0) ex ++ (part ++ bs) := by
        rw [takeAll]
        conv => lhs; rw [bytesEq]
        simp only [List.append_assoc]
      have g4 : GzAt c f (if on = true then Zlib.Inflate.Spec.setI h zs (strState s true bs) else h)
          (strRegs l ref off bs) zs (strState s on bs) (bytes ++ bs.take (firstStop bs)) [] := by
        refine g.step range E2.hs (keep2 l) (firstStop bs) kle
          (strRegs_next next) (strRegs_count kle) regs hold0 l0
          (by rw [bsDef, List.append_nil]) kept2 (by rw [mode2, mode]; decide)
          (by
            rw [form]
            simpa using gzipViable_name small fn sixLen exLimit partOk' [] (Or.inl rfl))
          (by rw [mode2, mode]; decide) (by rw [mode2, mode]; decide) start
          (by rw [flags2, getSame, flagsEq])
          (fun fh => by rw [getSame] at fh; exact crc2 fh) ?_
        rw [getSame]
        exact gzpos_name (mode2.trans mode) ⟨l0, six, ex, part ++ bs, sixLen, exLimit,
          partOk', fun nf => absurd fn (by omega), form⟩
      have short4 : GzipShort (bytes ++ bs.take (firstStop bs)) := by
        rw [form]; exact gzipShort_name sixLen exLimit fn partOk'
      exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (g4.loop short4)⟩⟩
  · simp only [fn, decide_false, Bool.false_eq_true, ↓reduceIte]
    have partNil : part = [] := noFn (by omega)
    subst partNil
    rw [runX_bind, runX_ldS E]
    simp only [head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [runX_bind, runX_wrS E]
    simp only []
    let s3 : InflateState := { s with length := 0, mode := COMMENT }
    obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := []) (by
      rw [bytesEq]; simp only [List.append_assoc]; rfl)
    have form : bytes ++ [] = [31, 139, 8, bytes.getD 3 0] ++ six ++
        gzipExtraPart (bytes.getD 3 0) ex ++ gzipNamePart (bytes.getD 3 0) [] ++ [] := by
      conv => lhs; rw [bytesEq]
      simp only [gzipNamePart, fn, ↓reduceIte, List.append_assoc, List.append_nil]
    have g3 : GzAt c f (Zlib.Inflate.Spec.setI h zs s3) l zs s3 (bytes ++ []) [] := by
      refine g.step range (by simp) (InputKept.setI _ _ _ l) 0 (Nat.zero_le _)
        (inputAdvance_zero l.next).symm (by omega) ⟨rfl, rfl, rfl, rfl, rfl⟩ hold0 l0
        (by simp) (Kept.lengthMode s 0 COMMENT) (by show COMMENT ≠ SYNC; decide)
        (by rw [List.append_nil]; exact g.viable)
        (by show TIME ≤ COMMENT; decide) (by show COMMENT ≤ HCRC; decide) start
        (by show s.flags = _; rw [getSame, flagsEq])
        (fun fh => by
          show s.check = _
          rw [getSame] at fh
          have cf : s.check = (crc32 bytes).toUInt64 := crcF fh
          rw [cf, List.append_nil]) ?_
      rw [getSame]
      exact gzpos_comment rfl ⟨l0, six, ex, [], [], sixLen, exLimit, by simp, by simp,
        fun _ => rfl, form⟩
    exact comment_step (envSetI E s3) g3 rfl (statics_setI statics zs s3)

#print axioms name_step

end Zlib.Inflate.Proofs.MeaningGzipFields
