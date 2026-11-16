import ZlibF.Proof.«inflate.c.meaning-gzip-fields-os»

/-!
# inflate.c: `FLAGS` keeps the format meaning

`FLAGS` waits for the method and flag bytes (`NEEDBITS(16)`) and stores the 16-bit word in
`flags`. A method other than 8, or a flag byte with a reserved bit (`0xe000` of the word), is
`BAD`: every gzip member has method 8 and flags below 32 (`gzipDecodes_flags`). Otherwise the two
bytes join the header CRC through `hbuf` when `FHCRC` is set (`CRC2`), and the mode falls
through to `TIME`.
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

theorem flags_word {hold : UInt64} {n : Nat} (v : hold.toNat = n) (small : n < 65536) :
    hold.toUInt32.toInt32 = Int32.ofNat n := by
  apply Int32.toBitVec_inj.mp
  simp [UInt32.toBitVec_toInt32]
  apply BitVec.eq_of_toNat_eq
  simp [v]

set_option maxHeartbeats 4000000 in
theorem flags_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {zs : Nat} {s : InflateState} {bytes rest : List UInt8} (E : Env c h r zs z s)
    (g : GzAt c f h l zs s bytes rest) (mode : s.mode = FLAGS)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) {b : Nat} {a : Array UInt8} (hb : Hbuf c h b a)
    (apart : HbufInputApart c l) :
    ∃ result l' h', runX (inflate_FLAGS c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have range : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  obtain ⟨bytesEq, bitsLe, checkEq, _⟩ := g.hm.2.2.2.1 mode
  have head := g.head
  have w4 := g.wrap4
  have short0 : GzipShort bytes := gzipShort_of_length (by rw [bytesEq]; simp)
  unfold inflate_FLAGS
  obtain ⟨result, l', j, run, shape, next, count, bitsCount, enough, leaveFacts, kinds, bitsMax,
    loopAt⟩ := g.needbits range short0 16 (by decide) (ok := fun b => b ≤ 16)
      (fun _ _ okb => okb)
      (fun hold bits b' okb lo _ _ _ => absurd (mode ▸ lo) (by decide))
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
    obtain ⟨m, fl, mfl⟩ : ∃ m fl, rest ++ (f.inp.drop (loopRead l)).take j = [m, fl] := by
      generalize rest ++ (f.inp.drop (loopRead l)).take j = w at restLen
      match w, restLen with
      | [m, fl], _ => exact ⟨m, fl, rfl⟩
    rw [mfl] at g'
    have holdVal : l'.hold.toNat = m.toNat + 256 * fl.toNat := by
      rw [g'.hold]
      simp [leValue]
    have hm := m.toNat_lt
    have hf := fl.toNat_lt
    have word := flags_word holdVal (by omega)
    have apart' : HbufInputApart c l' := apart.advance next count
    let s1 : InflateState := { s with flags := l'.hold.toUInt32.toInt32 }
    have E1 := envSetI E s1
    simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_wrS E]
    simp only []
    rw [runX_bind, runX_ldS E1]
    simp only []
    obtain ⟨methodCheck, reservedCheck⟩ := flags_checks fl.toNat hf m.toNat hm
    have inputEq : f.logIn ++ f.inp.take (loopRead l') = [31, 139, m, fl] := by
      rw [g'.input, bytesEq]; rfl
    have doomed : ¬ (m = 8 ∧ fl.toNat < 32) → LoopDoomed f l' := by
      intro bad
      refine gz_doomed g.gz inputEq ⟨[m, fl], rfl⟩ ?_
      intro source out valid pre
      exact bad (gzipDecodes_flags valid (rest := []) (by simpa using pre) (by simp))
    have badEnd : ∀ (i : Nat) (_ : ¬ (m = 8 ∧ fl.toNat < 32)),
        LoopBad c f (badHeap (Zlib.Inflate.Spec.setI h zs s1) r zs z s1 i) l' := by
      intro i bad
      exact g'.bad (s' := { s1 with mode := BAD }) (by simp [badHeap]) rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
        ⟨rfl, rfl⟩ (doomed bad)
    rw [show s1.flags = l'.hold.toUInt32.toInt32 from rfl, word, methodCheck, reservedCheck]
    by_cases m8 : m = 8
    · have mNat : m.toNat = 8 := by rw [m8]; rfl
      simp only [mNat, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases fl32 : fl.toNat < 32
      · have nr : decide (32 ≤ fl.toNat) = false := by simp; omega
        simp only [nr, Bool.false_eq_true, ↓reduceIte]
        simp only [show s1.head = none from head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_lift_ok (hcrcOn_env E1)]
        simp only []
        have wordEq : Int32.ofNat (m.toNat + 256 * fl.toNat) = flagsWord fl := by
          rw [mNat]; rfl
        rw [show (s1.flags &&& 0x0200 != 0 && s1.wrap &&& 4 != 0) =
          decide (fl.toNat / 2 % 2 = 1) by
            show (l'.hold.toUInt32.toInt32 &&& 0x0200 != 0 && s.wrap &&& 4 != 0) = _
            rw [word, wordEq, flagsWord_hcrc, w4, Bool.and_true]]
        have bytes' : bytes ++ [m, fl] = [31, 139, 8, fl] := by rw [bytesEq, m8]; rfl
        have getFl : (bytes ++ [m, fl]).getD 3 0 = fl := by rw [bytes']; rfl
        have start : ∃ t, bytes ++ [m, fl] = [31, 139, 8, (bytes ++ [m, fl]).getD 3 0] ++ t :=
          ⟨[], by rw [getFl, bytes']; rfl⟩
        have viable : GzipViable (bytes ++ [m, fl]) := by
          rw [bytes']
          exact (gzipViable_fixed fl32 [0, 0, 0, 0, 0, 0] rfl).of_prefix ⟨_, rfl⟩
        have position : ∀ s' : InflateState, s'.mode = TIME →
            GzipPosition (loopState s' { l' with hold := 0, bits := 0 }) ((bytes ++ [m, fl]).getD 3 0)
              (bytes ++ [m, fl]) := by
          intro s' m'
          rw [getFl]
          exact gzpos_time m' ⟨bytes', by show (0 : UInt32).toNat ≤ 32; decide⟩
        have flags3 : s1.flags = flagsWord ((bytes ++ [m, fl]).getD 3 0) := by
          rw [getFl, ← wordEq, ← word]
        by_cases fh : fl.toNat / 2 % 2 = 1
        · simp only [fh, decide_true, ↓reduceIte]
          rw [runX_bind, CRC2_run E1 l' (hb.setI zs s1).at_ (hb.setI zs s1).bytes hb.size
            (hb.setI zs s1).ro (statics_setI statics zs s1)]
          simp only []
          let s2 : InflateState := { s1 with check := crc2Value s1.check l'.hold }
          have E2 := env_crc E1 b (crc2Bytes a l'.hold) s2
          rw [runX_bind, runX_INITBITS]
          simp only []
          rw [runX_bind, runX_setMode E2]
          simp only []
          let s3 : InflateState := { s2 with mode := TIME }
          have size' : (crc2Bytes a l'.hold).size = 4 := by rw [crc2Bytes_size, hb.size]
          have g3 : GzAt c f (Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI (Space.put
              (Zlib.Inflate.Spec.setI h zs s1) (BRef.blk b) (crc2Bytes a l'.hold)) zs s2) zs s3)
              { l' with hold := 0, bits := 0 } zs s3 (bytes ++ [m, fl]) [] := by
            refine g'.step range (by simp)
              ((InputKept.setI h zs s1 l').trans (keep_crc0 (hb.setI zs s1) apart' size' zs s2 s3))
              0 (Nat.zero_le _) (inputAdvance_zero l'.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
              (by simp) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by show TIME ≠ SYNC; decide)
              viable (by show TIME ≤ TIME; decide) (by show TIME ≤ HCRC; decide) start flags3
              (fun _ => by
                show crc2Value s.check l'.hold = _
                exact crc2Value_of checkEq holdVal) (position s3 rfl)
          exact time_step (envSetI E2 s3) g3 rfl statics
            ((((hb.setI zs s1).put _ size').setI zs s2).setI zs s3) apart'
        · simp only [fh, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [runX_bind, runX_INITBITS]
          simp only []
          rw [runX_bind, runX_setMode E1]
          simp only []
          let s3 : InflateState := { s1 with mode := TIME }
          have g3 : GzAt c f (Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI h zs s1) zs s3)
              { l' with hold := 0, bits := 0 } zs s3 (bytes ++ [m, fl]) [] := by
            refine g'.step range (by simp) ((InputKept.setI _ _ _ l').trans (InputKept.setI _ _ _ l'))
              0 (Nat.zero_le _) (inputAdvance_zero l'.next).symm (by simp) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
              (by simp) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by show TIME ≠ SYNC; decide)
              viable (by show TIME ≤ TIME; decide) (by show TIME ≤ HCRC; decide) start flags3
              (fun fh' => absurd (by rw [getFl] at fh'; exact fh') fh) (position s3 rfl)
          exact time_step (envSetI E1 s3) g3 rfl statics ((hb.setI zs s1).setI zs s3) apart'
      · have nr : decide (32 ≤ fl.toNat) = true := by simp; omega
        simp only [nr, ↓reduceIte]
        obtain ⟨i, _, bad⟩ := runX_badMode E1 lit_unknown_header_flags l'
        rw [runX_bind, bad]
        simp only [runX_pure]
        exact ⟨_, _, _, rfl, Or.inl ⟨rfl, Or.inr (badEnd i (fun e => fl32 e.2))⟩⟩
    · have mNat : m.toNat ≠ 8 := fun e => m8 (UInt8.toNat_inj.mp (by rw [e]; rfl))
      simp only [show decide (m.toNat ≠ 8) = true from decide_eq_true mNat, ↓reduceIte]
      obtain ⟨i, _, bad⟩ := runX_badMode E1 lit_unknown_compression_method l'
      rw [runX_bind, bad]
      simp only [runX_pure]
      exact ⟨_, _, _, rfl, Or.inl ⟨rfl, Or.inr (badEnd i (fun e => m8 e.1))⟩⟩
  · have below := (leaveFacts rfl).2
    rw [n16] at below
    exact ⟨_, _, _, rfl, Or.inr ⟨rfl, Or.inl (loopAt (by omega))⟩⟩

#print axioms flags_step

end Zlib.Inflate.Proofs.MeaningGzipFields
