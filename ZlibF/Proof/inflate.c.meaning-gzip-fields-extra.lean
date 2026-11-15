import ZlibF.Proof.«inflate.c.meaning-gzip-fields-name»

/-!
# inflate.c: `EXTRA` keeps the format meaning

With `FEXTRA`, `EXTRA` copies `copy = min(length, have)` bytes of the extra field (no header
record: nothing is stored), updates the header CRC over them when `FHCRC` is set, and leaves
while `length != 0`. When the field is complete it sets `length = 0` and falls through to
`NAME`. Without `FEXTRA` it falls through at once.
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

theorem gzipExtraPart_of {flg : UInt8} {e : List UInt8} (fe : flg.toNat / 4 % 2 = 1) :
    gzipExtraPart flg e = le16 e.length ++ e := by
  simp [gzipExtraPart, fe]

/-- The end of an `EXTRA` copy of `m > 0` bytes: leave inside the field, or on to `NAME`. -/
theorem extra_after {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {bytes : List UInt8} (g : GzAt c f h l zs s bytes []) (mode : s.mode = EXTRA)
    {six e : List UInt8} (sixLen : six.length = 6) (fe : (bytes.getD 3 0).toNat / 4 % 2 = 1)
    (lim : e.length + s.length.toNat < 2 ^ 16)
    (bytesEq : bytes = [31, 139, 8, bytes.getD 3 0] ++ six ++ le16 (e.length + s.length.toNat) ++ e)
    (small : (bytes.getD 3 0).toNat < 32) (hold0 : l.hold = 0) (l0 : l.bits = 0)
    (flagsEq : s.flags = flagsWord (bytes.getD 3 0))
    {m : Nat} (mle : m ≤ l.have_.toNat) (mlen : m ≤ s.length.toNat)
    {h1 : Heap} {s1 : InflateState} (hs1 : h1.istates zs = some s1) (keep : InputKept h h1 l)
    (kept : Kept s s1) (flags1 : s1.flags = s.flags) (mode1 : s1.mode = s.mode)
    (len1 : s1.length.toNat = s.length.toNat - m)
    (crc1 : (bytes.getD 3 0).toNat / 2 % 2 = 1 →
      s1.check = (crc32 (bytes ++ (f.inp.drop (loopRead l)).take m)).toUInt64)
    {l1 : IL} (next1 : l1.next = inputAdvance l.next m) (count1 : l1.have_.toNat + m = l.have_.toNat)
    (regs1 : l1.ret = l.ret ∧ l1.in_ = l.in_ ∧ l1.out_ = l.out_ ∧ l1.left = l.left ∧ l1.put = l.put)
    (hold1 : l1.hold = 0) (bits1 : l1.bits = 0) :
    (s1.length ≠ 0 → LoopMatches c f h1 l1) ∧
    (s1.length = 0 → GzAt c f (Zlib.Inflate.Spec.setI h1 zs { s1 with length := 0, mode := NAME }) l1 zs
      { s1 with length := 0, mode := NAME } (bytes ++ (f.inp.drop (loopRead l)).take m) []) := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have chunkLen : ((f.inp.drop (loopRead l)).take m).length = m := by
    have := g.binv.have_eq
    simp only [List.length_take, List.length_drop] at this ⊢
    omega
  generalize chunkDef : (f.inp.drop (loopRead l)).take m = chunk at chunkLen crc1 ⊢
  have nEq : (e ++ chunk).length + s1.length.toNat = e.length + s.length.toNat := by
    rw [List.length_append, chunkLen, len1]
    omega
  have form : bytes ++ chunk = [31, 139, 8, bytes.getD 3 0] ++ six ++
      le16 (e.length + s.length.toNat) ++ (e ++ chunk) := by
    conv => lhs; rw [bytesEq]
    simp only [List.append_assoc]
  obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := chunk) (by
    rw [bytesEq]; simp only [List.append_assoc]; rfl)
  have viable : GzipViable (bytes ++ chunk) := by
    rw [form]
    exact gzipViable_extra small fe sixLen (by rw [← nEq]; omega) lim
  constructor
  · intro nz
    have g1 : GzAt c f h1 l1 zs s1 (bytes ++ chunk) [] := by
      refine g.step range hs1 keep m mle next1 count1 regs1 hold1 bits1
        (by rw [← chunkDef, List.append_nil]) kept (by rw [mode1, mode]; decide) viable
        (by rw [mode1, mode]; decide) (by rw [mode1, mode]; decide) start
        (by rw [flags1, getSame, flagsEq]) (fun fh => by rw [getSame] at fh; exact crc1 fh) ?_
      rw [getSame]
      exact gzpos_extra (mode1.trans mode) ⟨bits1, six, sixLen,
        fun _ => ⟨e ++ chunk, by show (e ++ chunk).length + s1.length.toNat < _; rw [nEq]; exact lim,
          by show _ = _ ++ le16 ((e ++ chunk).length + s1.length.toNat) ++ _; rw [nEq, form]⟩,
        fun nf => absurd fe (by omega)⟩
    have short : GzipShort (bytes ++ chunk) := by
      rw [form]
      refine gzipShort_extra sixLen fe lim ?_
      have : s1.length.toNat ≠ 0 := fun z0 => nz (UInt32.toNat_inj.mp (by simpa using z0))
      omega
    exact g1.loop short
  · intro z0
    have len0 : s1.length.toNat = 0 := by rw [z0]; rfl
    have exLen : (e ++ chunk).length = e.length + s.length.toNat := by omega
    have formN : bytes ++ chunk = [31, 139, 8, bytes.getD 3 0] ++ six ++
        gzipExtraPart (bytes.getD 3 0) (e ++ chunk) ++ [] := by
      rw [form, gzipExtraPart_of fe, exLen]
      simp only [List.append_assoc, List.append_nil]
    refine g.step range (by simp) (keep.trans (InputKept.setI _ _ _ l)) m mle next1 count1 regs1
      hold1 bits1 (by rw [← chunkDef, List.append_nil]) (kept.trans (Kept.lengthMode _ 0 NAME))
      (by show NAME ≠ SYNC; decide) viable (by show TIME ≤ NAME; decide)
      (by show NAME ≤ HCRC; decide) start
      (by show s1.flags = _; rw [flags1, getSame, flagsEq])
      (fun fh => by show s1.check = _; rw [getSame] at fh; exact crc1 fh) ?_
    rw [getSame]
    exact gzpos_name rfl ⟨bits1, six, e ++ chunk, [], sixLen, by rw [exLen]; exact lim, by simp,
      fun _ => rfl, formN⟩

#print axioms extra_after

theorem take_view {A : Array UInt8} {off n m : Nat} (le : m ≤ n) :
    (A.toList.drop off).take m = ((A.toList.drop off).take n).take m := by
  rw [List.take_take, Nat.min_eq_left le]

set_option maxHeartbeats 4000000 in
theorem extra_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {zs : Nat} {s : InflateState} {bytes rest : List UInt8} (E : Env c h r zs z s)
    (g : GzAt c f h l zs s bytes rest) (mode : s.mode = EXTRA)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) :
    ∃ result l' h', runX (inflate_EXTRA c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have lo : TIME ≤ s.mode := by rw [mode]; decide
  have hi : s.mode ≤ HCRC := by rw [mode]; decide
  obtain ⟨gzb, len4, flagsInt, crcF, _, posAll⟩ := g.hm.2.2.2.2.1 lo hi
  obtain ⟨bits0, six, sixLen, withE, withoutE⟩ := posAll.2.2.2.1 mode
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
  obtain ⟨t, bytesForm⟩ : ∃ t, bytes = [31, 139, 8, bytes.getD 3 0] ++ t := by
    by_cases fe : (bytes.getD 3 0).toNat / 4 % 2 = 1
    · obtain ⟨e, _, eq⟩ := withE fe
      exact ⟨_, by rw [eq]; simp only [List.append_assoc]; rfl⟩
    · exact ⟨_, withoutE (by omega)⟩
  have method : bytes.getD 2 0 = 8 := by rw [bytesForm]; simp
  have flagsEq : s.flags = flagsWord (bytes.getD 3 0) := flagsWord_eq flagsInt method
  have small : (bytes.getD 3 0).toNat < 32 := by
    have v := g.viable
    rw [bytesForm] at v
    exact small_of_viable v
  unfold inflate_EXTRA
  rw [runX_bind, runX_rdS E]
  simp only [flagsEq, flagsWord_extra]
  by_cases fe : (bytes.getD 3 0).toNat / 4 % 2 = 1
  · obtain ⟨e, lim, bytesEq⟩ := withE fe
    simp only [fe, decide_true, ↓reduceIte]
    rw [runX_bind, runX_ldS E]
    simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_set]
    simp only []
    generalize mDef : (if s.length > l.have_ then l.have_ else s.length) = m
    have mNat : m.toNat = min s.length.toNat l.have_.toNat := by
      rw [← mDef]
      split
      · rename_i gt
        have := UInt32.lt_iff_toNat_lt.mp gt
        omega
      · rename_i ngt
        have : ¬ l.have_.toNat < s.length.toNat := fun lt => ngt (UInt32.lt_iff_toNat_lt.mpr lt)
        omega
    have bytesEq' : bytes = [31, 139, 8, bytes.getD 3 0] ++ six ++
        le16 (e.length + s.length.toNat) ++ e := bytesEq
    by_cases m0 : m = 0
    · simp only [m0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, runX_rdS E]
      simp only []
      by_cases len0 : s.length = 0
      · simp only [len0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_wrS E]
        simp only []
        have lenN : s.length.toNat = 0 := by rw [len0]; rfl
        let s3 : InflateState := { s with length := 0, mode := NAME }
        obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := []) bytesForm
        have formN : bytes ++ [] = [31, 139, 8, bytes.getD 3 0] ++ six ++
            gzipExtraPart (bytes.getD 3 0) e ++ [] := by
          rw [gzipExtraPart_of fe, List.append_nil, List.append_nil]
          conv => lhs; rw [bytesEq']
          rw [lenN, Nat.add_zero]
          simp only [List.append_assoc]
        have g3 : GzAt c f (Zlib.Inflate.Spec.setI h zs s3) { l with copy := 0 } zs s3 (bytes ++ []) [] := by
          refine g.step range (by simp) (InputKept.setI _ _ _ l) 0 (Nat.zero_le _)
            (inputAdvance_zero l.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ hold0 l0
            (by simp) (Kept.lengthMode s 0 NAME) (by show NAME ≠ SYNC; decide)
            (by rw [List.append_nil]; exact g.viable)
            (by show TIME ≤ NAME; decide) (by show NAME ≤ HCRC; decide) start
            (by show s.flags = _; rw [getSame, flagsEq])
            (fun fh => by
              show s.check = _
              rw [getSame] at fh
              have cf : s.check = (crc32 bytes).toUInt64 := crcF fh
              rw [cf, List.append_nil]) ?_
          rw [getSame]
          exact gzpos_name rfl ⟨l0, six, e, [], sixLen, by omega, by simp, fun _ => rfl, formN⟩
        exact name_step (envSetI E s3) g3 rfl (statics_setI statics zs s3)
      · have lenNe : (s.length != 0) = true := by simpa using len0
        simp only [lenNe, ↓reduceIte]
        rw [runX_bind, runX_throw]
        refine ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl ?_⟩⟩
        obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := []) bytesForm
        have g3 : GzAt c f h { l with copy := 0 } zs s (bytes ++ []) [] := by
          refine g.step range E.hs (InputKept.refl h l) 0 (Nat.zero_le _)
            (inputAdvance_zero l.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ hold0 l0
            (by simp) (Kept.refl s) (by rw [mode]; decide) (by rw [List.append_nil]; exact g.viable)
            lo hi start (by rw [getSame, flagsEq])
            (fun fh => by
              rw [getSame] at fh
              have cf : s.check = (crc32 bytes).toUInt64 := crcF fh
              rw [cf, List.append_nil]) ?_
          rw [getSame, List.append_nil]
          exact gzpos_extra mode ⟨l0, six, sixLen, fun _ => ⟨e, lim, bytesEq'⟩,
            fun nf => absurd fe (by omega)⟩
        have lenPos : 0 < s.length.toNat := by
          have : s.length.toNat ≠ 0 := fun z0 => len0 (UInt32.toNat_inj.mp (by simpa using z0))
          omega
        refine g3.loop ?_
        rw [List.append_nil, bytesEq']
        exact gzipShort_extra sixLen fe lim (by omega)
    · have mNe : (m != 0) = true := by simpa using m0
      simp only [mNe, ↓reduceIte, head, bne_self_eq_false, Bool.false_eq_true]
      have mPos : 0 < m.toNat := by
        have : m.toNat ≠ 0 := fun z0 => m0 (UInt32.toNat_inj.mp (by simpa using z0))
        omega
      have pos : 0 < l.have_.toNat := by omega
      have mle : m.toNat ≤ l.have_.toNat := by omega
      have mlen : m.toNat ≤ s.length.toNat := by omega
      obtain ⟨ref, off, A, next, get, fit, inpEq⟩ := g.view pos
      have add : ∀ H : Heap, Space.get H ref = some A →
          ({ l with copy := m } : IL).next.add (m.toNat : Int) H = .ok (.ref ref (off + m.toNat), H) := by
        intro H getH
        show l.next.add _ H = _
        rw [next]
        exact Ptr.add_nat_ok getH (by omega)
      have count1 : (l.have_ - m).toNat + m.toNat = l.have_.toNat := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr mle)]
        omega
      have len1 : (s.length - m).toNat = s.length.toNat - m.toNat :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr mlen)
      have next1 : (Ptr.ref ref (off + m.toNat) : BPtr) = inputAdvance l.next m.toNat := by
        rw [next]; rfl
      rw [runX_bind, runX_lift_ok (hcrcOn_env E)]
      simp only []
      rw [show (s.flags &&& 0x0200 != 0 && s.wrap &&& 4 != 0) =
        decide ((bytes.getD 3 0).toNat / 2 % 2 = 1) by rw [flagsEq, flagsWord_hcrc, w4, Bool.and_true]]
      by_cases fh : (bytes.getD 3 0).toNat / 2 % 2 = 1
      · simp only [fh, decide_true, ↓reduceIte]
        have crc := Zlib.Crc32.Proofs.ViewsProof.crc32_correct h statics s.check ref off A get m (by omega)
        let v : UInt64 := (ZlibF.Spec.crc32Update s.check.toUInt32 ((A.toList.drop off).take m.toNat)).toUInt64
        have crc' : Zlib.Crc32.crc32 s.check ({ l with copy := m } : IL).next m h = .ok (v, h) := by
          show Zlib.Crc32.crc32 s.check l.next m h = _
          rw [next]
          exact crc
        have vEq : v = (crc32 (bytes ++ (f.inp.drop (loopRead l)).take m.toNat)).toUInt64 := by
          have cf : s.check = (crc32 bytes).toUInt64 := crcF fh
          show (ZlibF.Spec.crc32Update s.check.toUInt32 ((A.toList.drop off).take m.toNat)).toUInt64 = _
          rw [take_view mle, ← inpEq, cf, toUInt32_of_crc, MeaningChecksum.crc_continue]
        let s1 : InflateState := { s with check := v }
        let s2 : InflateState := { s1 with length := s1.length - m }
        have E1 := envSetI E s1
        have E2 := envSetI E1 s2
        rw [runX_bind, runX_rdS E]
        simp only []
        rw [runX_bind, runX_get]
        simp only []
        rw [runX_bind, runX_lift_ok crc']
        simp only []
        rw [runX_bind, runX_wrS E]
        simp only []
        rw [runX_bind, runX_get]
        simp only []
        rw [runX_bind, runX_lift_ok (add _ (by rw [byte_view_get_setI]; exact get))]
        simp only []
        rw [runX_bind, runX_set]
        simp only []
        rw [runX_bind, runX_wrS E1]
        simp only []
        rw [runX_bind, runX_rdS E2]
        simp only []
        obtain ⟨leave, cont⟩ := extra_after (h1 := Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI h zs s1) zs s2)
          (s1 := s2) (l1 := { { l with copy := m } with next := .ref ref (off + m.toNat), have_ := l.have_ - m })
          g mode sixLen fe lim bytesEq' small hold0 l0 flagsEq mle mlen (by simp)
          ((InputKept.setI _ _ _ l).trans (InputKept.setI _ _ _ l))
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl len1 (fun _ => vEq) next1 count1
          ⟨rfl, rfl, rfl, rfl, rfl⟩ hold0 l0
        by_cases len0 : s.length - m = 0
        · simp only [show s2.length = 0 from len0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          rw [runX_bind, runX_wrS E2]
          simp only []
          exact name_step (envSetI E2 _) (cont len0) rfl (statics_setI (statics_setI (statics_setI statics zs s1) zs s2) zs { s2 with length := 0, mode := NAME })
        · have lenNe : (s2.length != 0) = true := by simpa using len0
          simp only [lenNe, ↓reduceIte]
          rw [runX_bind, runX_throw]
          exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (leave len0)⟩⟩
      · simp only [fh, decide_false, Bool.false_eq_true, ↓reduceIte]
        let s2 : InflateState := { s with length := s.length - m }
        have E2 := envSetI E s2
        rw [runX_bind, runX_get]
        simp only []
        rw [runX_bind, runX_lift_ok (add _ get)]
        simp only []
        rw [runX_bind, runX_set]
        simp only []
        rw [runX_bind, runX_wrS E]
        simp only []
        rw [runX_bind, runX_rdS E2]
        simp only []
        obtain ⟨leave, cont⟩ := extra_after (h1 := Zlib.Inflate.Spec.setI h zs s2)
          (s1 := s2) (l1 := { { l with copy := m } with next := .ref ref (off + m.toNat), have_ := l.have_ - m })
          g mode sixLen fe lim bytesEq' small hold0 l0 flagsEq mle mlen (by simp)
          (InputKept.setI _ _ _ l)
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl len1 (fun fh' => absurd fh' fh)
          next1 count1 ⟨rfl, rfl, rfl, rfl, rfl⟩ hold0 l0
        by_cases len0 : s.length - m = 0
        · simp only [show s2.length = 0 from len0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          rw [runX_bind, runX_wrS E2]
          simp only []
          exact name_step (envSetI E2 _) (cont len0) rfl (statics_setI (statics_setI statics zs s2) zs { s2 with length := 0, mode := NAME })
        · have lenNe : (s2.length != 0) = true := by simpa using len0
          simp only [lenNe, ↓reduceIte]
          rw [runX_bind, runX_throw]
          exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (leave len0)⟩⟩
  · simp only [fe, decide_false, Bool.false_eq_true, ↓reduceIte]
    have bytesEq : bytes = [31, 139, 8, bytes.getD 3 0] ++ six := withoutE (by omega)
    rw [runX_bind, runX_wrS E]
    simp only []
    let s3 : InflateState := { s with length := 0, mode := NAME }
    obtain ⟨getSame, start⟩ := start_append (bytes := bytes) (u := []) bytesForm
    have formN : bytes ++ [] = [31, 139, 8, bytes.getD 3 0] ++ six ++
        gzipExtraPart (bytes.getD 3 0) [] ++ [] := by
      conv => lhs; rw [bytesEq]
      simp only [gzipExtraPart, fe, ↓reduceIte, List.append_nil]
    have g3 : GzAt c f (Zlib.Inflate.Spec.setI h zs s3) l zs s3 (bytes ++ []) [] := by
      refine g.step range (by simp) (InputKept.setI _ _ _ l) 0 (Nat.zero_le _)
        (inputAdvance_zero l.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ hold0 l0
        (by simp) (Kept.lengthMode s 0 NAME) (by show NAME ≠ SYNC; decide)
        (by rw [List.append_nil]; exact g.viable)
        (by show TIME ≤ NAME; decide) (by show NAME ≤ HCRC; decide) start
        (by show s.flags = _; rw [getSame, flagsEq])
        (fun fh => by
          show s.check = _
          rw [getSame] at fh
          have cf : s.check = (crc32 bytes).toUInt64 := crcF fh
          rw [cf, List.append_nil]) ?_
      rw [getSame]
      exact gzpos_name rfl ⟨l0, six, [], [], sixLen, by simp, by simp, fun _ => rfl, formN⟩
    exact name_step (envSetI E s3) g3 rfl (statics_setI statics zs s3)

#print axioms extra_step

end Zlib.Inflate.Proofs.MeaningGzipFields
