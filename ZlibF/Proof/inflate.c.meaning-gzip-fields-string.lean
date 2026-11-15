import ZlibF.Proof.«inflate.c.meaning-gzip-fields-hcrc»
import ZlibF.Proof.«crc32.c.views»

/-!
# inflate.c: the byte loop of `NAME` and `COMMENT`, without a header record

`do { len = next[copy++]; ... } while (len && copy < have);` with no header record reads the
unread input up to and including its first zero byte, or all of it (`firstStop`). Then the
header CRC is updated over the copied bytes when `FHCRC` is set, the bytes are consumed, and the
mode leaves when no zero was seen (`strCopyK_run`).
-/

namespace Zlib.Inflate.Proofs.MeaningGzipFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Where the loop stops -/

/-- The number of bytes the loop reads: through the first zero byte, or all bytes. -/
noncomputable def firstStop : List UInt8 → Nat
  | [] => 0
  | b :: t => if b = 0 then 1 else firstStop t + 1

theorem firstStop_le : ∀ bs : List UInt8, firstStop bs ≤ bs.length
  | [] => by simp [firstStop]
  | b :: t => by
    have := firstStop_le t
    simp only [firstStop, List.length_cons]
    split <;> omega

theorem firstStop_pos : ∀ bs : List UInt8, bs ≠ [] → 1 ≤ firstStop bs
  | [], ne => absurd rfl ne
  | b :: t, _ => by simp only [firstStop]; split <;> omega

theorem firstStop_nonzero : ∀ (bs : List UInt8) (i : Nat), i + 1 < firstStop bs → bs.getD i 0 ≠ 0
  | [], i, lt => by simp [firstStop] at lt
  | b :: t, i, lt => by
    simp only [firstStop] at lt
    split at lt
    · omega
    · rename_i nz
      cases i with
      | zero => simpa using nz
      | succ i =>
        simp only [List.getD_cons_succ]
        exact firstStop_nonzero t i (by omega)

theorem firstStop_last : ∀ bs : List UInt8, bs ≠ [] →
    bs.getD (firstStop bs - 1) 0 = 0 ∨ firstStop bs = bs.length
  | [], ne => absurd rfl ne
  | b :: t, _ => by
    simp only [firstStop]
    split
    · left; simpa
    · rename_i nz
      cases t with
      | nil => right; simp [firstStop]
      | cons b' t' =>
        rcases firstStop_last (b' :: t') (by simp) with z | e
        · left
          have pos := firstStop_pos (b' :: t') (by simp)
          obtain ⟨k, hk⟩ : ∃ k, firstStop (b' :: t') = k + 1 := ⟨firstStop (b' :: t') - 1, by omega⟩
          rw [hk] at z ⊢
          simpa using z
        · right; simp [e]

/-- The bytes before the stop contain no zero. -/
theorem firstStop_take_nonzero (bs : List UInt8) : (0 : UInt8) ∉ bs.take (firstStop bs - 1) := by
  intro mem
  obtain ⟨i, lt, eq⟩ := List.getElem_of_mem mem
  simp only [List.length_take] at lt
  have ne := firstStop_nonzero bs i (by omega)
  apply ne
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  rw [List.getElem_take] at eq
  exact eq

/-- With no zero at the stop, the loop read all bytes and none is zero. -/
theorem firstStop_all {bs : List UInt8} (ne : bs ≠ []) (last : bs.getD (firstStop bs - 1) 0 ≠ 0) :
    firstStop bs = bs.length ∧ (0 : UInt8) ∉ bs := by
  have all := (firstStop_last bs ne).resolve_left last
  refine ⟨all, fun mem => ?_⟩
  have pos := firstStop_pos bs ne
  have split : bs = bs.take (firstStop bs - 1) ++ [bs.getD (firstStop bs - 1) 0] := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.length_append, List.length_take, List.length_singleton] at h2
      by_cases lt : i < firstStop bs - 1
      · rw [List.getElem_append_left (by simp; omega)]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_take, List.getElem_singleton]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        simp only [Option.getD_some]
        congr 1
        omega
  rw [split] at mem
  rcases List.mem_append.mp mem with m | m
  · exact firstStop_take_nonzero bs m
  · simp at m
    exact last m.symm

/-- With a zero at the stop, the bytes read are the zero-free bytes before it and the zero. -/
theorem firstStop_zero {bs : List UInt8} (ne : bs ≠ []) (last : bs.getD (firstStop bs - 1) 0 = 0) :
    bs.take (firstStop bs) = bs.take (firstStop bs - 1) ++ [0] := by
  have pos := firstStop_pos bs ne
  have le := firstStop_le bs
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_take] at h1
    by_cases lt : i < firstStop bs - 1
    · rw [List.getElem_append_left (by simp; omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_take, List.getElem_singleton, List.getElem_take]
      rw [← last, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1
      omega

/-! ## The loop -/

/-- A byte of an array, 0 outside. -/
def byteAt (A : Array UInt8) (i : Nat) : UInt8 := A.toList.getD i 0

theorem byteAt_eq {A : Array UInt8} {i : Nat} (lt : i < A.size) : A[i] = byteAt A i := by
  simp [byteAt, List.getD_eq_getElem?_getD, lt]

theorem input_getD {A : Array UInt8} {off n i : Nat} (lt : i < n) :
    ((A.toList.drop off).take n).getD i 0 = byteAt A (off + i) := by
  simp [byteAt, List.getD_eq_getElem?_getD, List.getElem?_take, lt, List.getElem?_drop]

theorem uint8_toUInt32_ne {b : UInt8} : (b.toUInt32 != 0) = (b != 0) := by
  have : b.toUInt32 = 0 ↔ b = 0 := by
    constructor
    · intro e
      apply UInt8.toNat_inj.mp
      have := congrArg UInt32.toNat e
      simpa using this
    · intro e
      rw [e]
      rfl
  by_cases z : b = 0
  · rw [z]; rfl
  · have z' : b.toUInt32 ≠ 0 := fun e => z (this.mp e)
    rw [bne_iff_ne.mpr z', bne_iff_ne.mpr z]

theorem strBody_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {sel : GzHeader → BPtr} {cap : GzHeader → UInt32} (E : Env c h r zs z s) (head : s.head = none)
    {l : IL} {ref : BRef} {off : Nat} {A : Array UInt8} (next : l.next = .ref ref off)
    (get : Space.get h ref = some A) (lt : off + l.copy.toNat < A.size) :
    runX (strBody c sel cap) l h =
      .ok ((.ok (), { l with len := (byteAt A (off + l.copy.toNat)).toUInt32, copy := l.copy + 1 }), h) := by
  have idx : index8 l.next l.copy.toNat h = .ok (A[off + l.copy.toNat], h) := by
    rw [next]; exact Ptr.index_ok get lt
  unfold strBody
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok idx]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  rw [runX_bind, runX_ldS E]
  simp only [head, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [byteAt_eq lt]
  rfl

/-- The registers after the byte loop over `bs`. -/
noncomputable def loopRegs (l : IL) (bs : List UInt8) : IL :=
  { l with
    copy := UInt32.ofNat (firstStop bs)
    len := (bs.getD (firstStop bs - 1) 0).toUInt32 }

/-- The byte loop from `copy = 0` over `n > 0` readable bytes `bs`. -/
theorem strLoop_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {sel : GzHeader → BPtr} {cap : GzHeader → UInt32} (E : Env c h r zs z s) (head : s.head = none)
    {l : IL} {ref : BRef} {off : Nat} {A : Array UInt8} (next : l.next = .ref ref off)
    (get : Space.get h ref = some A) (fit : off + l.have_.toNat ≤ A.size)
    (copy0 : l.copy = 0) (pos : 0 < l.have_.toNat) :
    runX (xdoWhile (strBody c sel cap) strCond) l h =
      .ok ((.ok (), loopRegs l ((A.toList.drop off).take l.have_.toNat)), h) := by
  generalize bsDef : (A.toList.drop off).take l.have_.toNat = bs
  have bsLen : bs.length = l.have_.toNat := by rw [← bsDef]; simp; omega
  have ne : bs ≠ [] := by intro e; rw [e] at bsLen; simp at bsLen; omega
  have kpos := firstStop_pos bs ne
  have kle := firstStop_le bs
  have nSmall := l.have_.toNat_lt
  have getBs : ∀ i, i < l.have_.toNat → bs.getD i 0 = byteAt A (off + i) := by
    intro i lt; rw [← bsDef]; exact input_getD lt
  let P : IL → Heap → Prop := fun l' h' => h' = h ∧
    l' = { l with copy := l'.copy, len := l'.len } ∧ 1 ≤ l'.copy.toNat ∧ l'.copy.toNat ≤ firstStop bs ∧
    l'.len = (bs.getD (l'.copy.toNat - 1) 0).toUInt32
  let Q : Except Ex Unit → IL → Heap → Prop := fun res l' h' => res = .ok () ∧ h' = h ∧
    l' = loopRegs l bs
  have bodyRun : ∀ l', P l' h → l'.copy.toNat < l.have_.toNat →
      runX (strBody c sel cap) l' h =
        .ok ((.ok (), { l' with len := (byteAt A (off + l'.copy.toNat)).toUInt32, copy := l'.copy + 1 }),
          h) := by
    intro l' ⟨_, shape, _⟩ lt
    have next' : l'.next = .ref ref off := by rw [shape]; exact next
    exact strBody_run E head next' get (by omega)
  have l0copy : l.copy.toNat = 0 := by rw [copy0]; rfl
  have run1 := strBody_run (sel := sel) (cap := cap) E head next get (by omega)
  have P1 : P { l with len := (byteAt A (off + l.copy.toNat)).toUInt32, copy := l.copy + 1 } h := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · show 1 ≤ (l.copy + 1).toNat; rw [copy0]; decide
    · show (l.copy + 1).toNat ≤ firstStop bs; rw [copy0]; exact kpos
    · show (byteAt A (off + l.copy.toNat)).toUInt32 = (bs.getD ((l.copy + 1).toNat - 1) 0).toUInt32
      rw [copy0]
      show (byteAt A (off + 0)).toUInt32 = (bs.getD 0 0).toUInt32
      rw [getBs 0 pos]
  have step : ∀ l' h', P l' h' → ∃ test l1 h1, runX strCond l' h' = .ok ((test, l1), h1) ∧
      (match test with
       | .error fault => Q (.error fault) l1 h1
       | .ok false => Q (.ok ()) l1 h1
       | .ok true => ∃ result l2 h2,
           runX (do strBody c sel cap; pure false) l1 h1 = .ok ((result, l2), h2) ∧
           (match result with
            | .error fault => Q (.error fault) l2 h2
            | .ok true => Q (.ok ()) l2 h2
            | .ok false => P l2 h2 ∧ (fun (l : IL) (_ : Heap) => firstStop bs - l.copy.toNat) l2 h2 <
                (fun (l : IL) (_ : Heap) => firstStop bs - l.copy.toNat) l' h')) := by
    intro l' h' cur
    obtain ⟨hEq, shape, c1, c2, lenEq⟩ := cur
    subst hEq
    have haveEq : l'.have_ = l.have_ := by rw [shape]
    refine ⟨.ok (l'.len != 0 && decide (l'.copy < l'.have_)), l', h', rfl, ?_⟩
    by_cases more : l'.copy.toNat < firstStop bs
    · have nz : bs.getD (l'.copy.toNat - 1) 0 ≠ 0 := firstStop_nonzero bs _ (by omega)
      have test : (l'.len != 0 && decide (l'.copy < l'.have_)) = true := by
        rw [lenEq, uint8_toUInt32_ne, haveEq]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
        exact ⟨nz, UInt32.lt_iff_toNat_lt.mpr (by omega)⟩
      rw [test]
      have lt : l'.copy.toNat < l.have_.toNat := by omega
      have succ : (l'.copy + 1).toNat = l'.copy.toNat + 1 := by
        rw [UInt32.toNat_add]
        simp only [UInt32.toNat_one, UInt32.size]
        omega
      refine ⟨.ok false,
        { l' with len := (byteAt A (off + l'.copy.toNat)).toUInt32, copy := l'.copy + 1 }, h', ?_,
        ⟨rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [runX_bind, bodyRun l' ⟨rfl, shape, c1, c2, lenEq⟩ lt]
        rfl
      · rw [shape]
      · show 1 ≤ (l'.copy + 1).toNat; omega
      · show (l'.copy + 1).toNat ≤ firstStop bs; omega
      · show (byteAt A (off + l'.copy.toNat)).toUInt32 = (bs.getD ((l'.copy + 1).toNat - 1) 0).toUInt32
        rw [succ, Nat.add_sub_cancel, getBs _ lt]
      · show firstStop bs - (l'.copy + 1).toNat < firstStop bs - l'.copy.toNat
        omega
    · have atK : l'.copy.toNat = firstStop bs := by omega
      have test : (l'.len != 0 && decide (l'.copy < l'.have_)) = false := by
        rw [lenEq, uint8_toUInt32_ne, haveEq, atK]
        rcases firstStop_last bs ne with z | all
        · rw [z]; rfl
        · have : ¬ l'.copy < l.have_ := by
            rw [UInt32.lt_iff_toNat_lt]
            omega
          simp [this]
      rw [test]
      refine ⟨rfl, rfl, ?_⟩
      have c' : l'.copy = UInt32.ofNat (firstStop bs) := by
        apply UInt32.toNat_inj.mp
        rw [atK]
        simp only [UInt32.toNat_ofNat']
        omega
      rw [shape, lenEq, atK, c']
      rfl
  obtain ⟨result, regs, after, run, done, hEq, final⟩ := xwhileBrk_rank (cond := strCond)
    (body := (do strBody c sel cap; pure false)) P (fun l' _ => firstStop bs - l'.copy.toNat) Q step P1 (by
      show _ < C.fuel
      unfold C.fuel
      omega)
  subst done hEq final
  unfold xdoWhile xwhile
  rw [runX_bind, run1]
  exact run

/-! ## `NAME` and `COMMENT` with the flag set -/

theorem hcrcOn_env {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) :
    hcrcOn c.st h = .ok ((s.flags &&& 0x0200) != 0 && (s.wrap &&& 4) != 0, h) := by
  unfold hcrcOn
  rw [E.st]
  simp [bind_app, ldInflateState_tab E.hs]

/-- The registers after the bytes of a string field are consumed. -/
noncomputable def strRegs (l : IL) (ref : BRef) (off : Nat) (bs : List UInt8) : IL :=
  { l with
    copy := UInt32.ofNat (firstStop bs)
    len := (bs.getD (firstStop bs - 1) 0).toUInt32
    have_ := l.have_ - UInt32.ofNat (firstStop bs)
    next := .ref ref (off + firstStop bs) }

/-- The state after the header CRC of a string field. -/
noncomputable def strState (s : InflateState) (on : Bool) (bs : List UInt8) : InflateState :=
  if on then { s with check := (ZlibF.Spec.crc32Update s.check.toUInt32 (bs.take (firstStop bs))).toUInt64 }
  else s

theorem strCopyK_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {sel : GzHeader → BPtr} {cap : GzHeader → UInt32} (E : Env c h r zs z s) (head : s.head = none)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) {l : IL} {ref : BRef} {off : Nat} {A : Array UInt8}
    (next : l.next = .ref ref off) (get : Space.get h ref = some A) (fit : off + l.have_.toNat ≤ A.size)
    (pos : 0 < l.have_.toNat) (k : X Unit) :
    runX (strCopyK c sel cap k) l h =
      (if ((A.toList.drop off).take l.have_.toNat).getD
          (firstStop ((A.toList.drop off).take l.have_.toNat) - 1) 0 = 0 then
        runX k (strRegs l ref off ((A.toList.drop off).take l.have_.toNat))
          (if ((s.flags &&& 0x0200) != 0 && (s.wrap &&& 4) != 0) = true then
            Zlib.Inflate.Spec.setI h zs (strState s true ((A.toList.drop off).take l.have_.toNat))
          else h)
      else .ok ((.error Ex.leave, strRegs l ref off ((A.toList.drop off).take l.have_.toNat)),
          (if ((s.flags &&& 0x0200) != 0 && (s.wrap &&& 4) != 0) = true then
            Zlib.Inflate.Spec.setI h zs (strState s true ((A.toList.drop off).take l.have_.toNat))
          else h))) := by
  generalize bsDef : (A.toList.drop off).take l.have_.toNat = bs
  have bsLen : bs.length = l.have_.toNat := by rw [← bsDef]; simp; omega
  have ne : bs ≠ [] := by intro e; rw [e] at bsLen; simp at bsLen; omega
  have kpos := firstStop_pos bs ne
  have kle := firstStop_le bs
  have nSmall := l.have_.toNat_lt
  have nonempty : (l.have_ == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    rw [e] at pos
    simp at pos
  let l0 : IL := { l with copy := 0 }
  have loop := strLoop_run (sel := sel) (cap := cap) (l := l0) E head next get fit rfl pos
  simp only [l0] at loop
  rw [bsDef] at loop
  have kNat : (UInt32.ofNat (firstStop bs)).toNat = firstStop bs := by
    simp only [UInt32.toNat_ofNat']
    omega
  unfold strCopyK
  rw [runX_bind, runX_get]
  simp only [nonempty, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, runX_modify]
  simp only []
  rw [runX_bind, loop]
  simp only []
  rw [runX_bind, runX_lift_ok (hcrcOn_env E)]
  simp only []
  let l1 : IL := loopRegs { l with copy := 0 } bs
  have add : l1.next.add (l1.copy.toNat : Int) h = .ok (.ref ref (off + firstStop bs), h) := by
    show l.next.add ((UInt32.ofNat (firstStop bs)).toNat : Int) h = _
    rw [next, kNat]
    exact Ptr.add_nat_ok get (by omega)
  have advance : ∀ (h2 : Heap), (h2 = h ∨ ∃ s', h2 = Zlib.Inflate.Spec.setI h zs s') →
      runX (strAdvanceK k) l1 h2 =
        (if bs.getD (firstStop bs - 1) 0 = 0 then runX k (strRegs l ref off bs) h2
        else .ok ((.error Ex.leave, strRegs l ref off bs), h2)) := by
    intro h2 which
    have add2 : l1.next.add (l1.copy.toNat : Int) h2 = .ok (.ref ref (off + firstStop bs), h2) := by
      rcases which with rfl | ⟨s', rfl⟩
      · exact add
      · show l.next.add ((UInt32.ofNat (firstStop bs)).toNat : Int) _ = _
        rw [next, kNat]
        exact Ptr.add_nat_ok (by rw [byte_view_get_setI]; exact get) (by omega)
    unfold strAdvanceK
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_lift_ok add2]
    simp only []
    rw [runX_bind, runX_set]
    simp only []
    by_cases z0 : bs.getD (firstStop bs - 1) 0 = 0
    · have lz : (l1.len != 0) = false := by
        show ((bs.getD (firstStop bs - 1) 0).toUInt32 != 0) = false
        rw [uint8_toUInt32_ne, z0]
        rfl
      simp only [lz, Bool.false_eq_true, ↓reduceIte, z0]
      rfl
    · have lz : (l1.len != 0) = true := by
        show ((bs.getD (firstStop bs - 1) 0).toUInt32 != 0) = true
        rw [uint8_toUInt32_ne]
        simpa using z0
      simp only [lz, ↓reduceIte, z0]
      rw [runX_bind, runX_throw]
      rfl
  cases on : ((s.flags &&& 0x0200) != 0 && (s.wrap &&& 4) != 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact advance h (Or.inl rfl)
  · simp only [↓reduceIte]
    have crc := Zlib.Crc32.Proofs.ViewsProof.crc32_correct h statics s.check ref off A get
      (UInt32.ofNat (firstStop bs)) (by rw [kNat]; omega)
    have chunk : (A.toList.drop off).take (UInt32.ofNat (firstStop bs)).toNat = bs.take (firstStop bs) := by
      have e : bs.take (firstStop bs) = ((A.toList.drop off).take l.have_.toNat).take (firstStop bs) := by
        rw [bsDef]
      rw [kNat, e, List.take_take, Nat.min_eq_left (by omega)]
    rw [chunk] at crc
    have crc' : Zlib.Crc32.crc32 s.check l1.next l1.copy h =
        .ok ((ZlibF.Spec.crc32Update s.check.toUInt32 (bs.take (firstStop bs))).toUInt64, h) := by
      show Zlib.Crc32.crc32 s.check l.next (UInt32.ofNat (firstStop bs)) h = _
      rw [next]
      exact crc
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_rdS E]
    simp only []
    rw [runX_bind, runX_lift_ok crc']
    simp only []
    rw [runX_bind, runX_wrS E]
    simp only []
    exact advance _ (Or.inr ⟨_, rfl⟩)

#print axioms strCopyK_run

end Zlib.Inflate.Proofs.MeaningGzipFields
