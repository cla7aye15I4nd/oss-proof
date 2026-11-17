import ZlibF.Proof.«infback.c.inv»
import ZlibF.Proof.«infback.c.pure»
import ZlibF.Proof.«infback.c.wf»
import ZlibF.Proof.«inflate.c.main.stored»
import ZlibF.Proof.«inflate.c.main.stored2»

/-!
# infback.c: `ROOM()` on the loop invariant, and `case STORED`
-/

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-- Registers with the same input fields describe the same chunk. -/
theorem BIn.regs_eq {ownI : Nat → Prop} {h : Heap} {l l' : IL} {bs : List UInt8} (B : BIn ownI h l bs)
    (hn : l'.next = l.next) (hh : l'.have_ = l.have_) (hho : l'.hold = l.hold) (hb : l'.bits = l.bits) :
    BIn ownI h l' bs := by
  obtain ⟨⟨he, hn', hl⟩, ho⟩ := B
  refine ⟨⟨by rw [hh]; exact he, by rw [hn]; exact hn', by rw [hho, hb]; exact hl⟩, by rw [hn]; exact ho⟩

/-! ## `case STORED` -/

/-- The copy count of `case STORED`: `min(length, have, left)`, written with the two `if`s of the C. -/
def clampCopy (len hv lf : UInt32) : UInt32 :=
  let c1 := if len > hv then hv else len
  if c1 > lf then lf else c1

theorem clampCopy_le (len hv lf : UInt32) : (clampCopy len hv lf).toNat ≤ len.toNat ∧
    (clampCopy len hv lf).toNat ≤ hv.toNat ∧ (clampCopy len hv lf).toNat ≤ lf.toNat := by
  unfold clampCopy
  simp only [GT.gt, UInt32.lt_iff_toNat_lt]
  split <;> split <;> omega

theorem clampCopy_pos (len hv lf : UInt32) (h1 : len ≠ 0) (h2 : hv ≠ 0) (h3 : lf ≠ 0) : clampCopy len hv lf ≠ 0 := by
  have e1 : 0 < len.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h1 (UInt32.toNat_inj.mp (by simpa using e))
  have e2 : 0 < hv.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h2 (UInt32.toNat_inj.mp (by simpa using e))
  have e3 : 0 < lf.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h3 (UInt32.toNat_inj.mp (by simpa using e))
  intro e
  have := congrArg UInt32.toNat e
  unfold clampCopy at this
  simp only [GT.gt, UInt32.lt_iff_toNat_lt] at this
  split at this <;> split at this <;> simp at this <;> omega

/-- The part of the copy loop after `ROOM()`. -/
def storedTail (c : BCtx) : X Unit := do
  let l ← get
  let mut copy := l.copy
  if copy > l.have_ then copy := l.have_
  if copy > l.left then copy := l.left
  memcpyB l.put l.next copy.toNat
  let nx ← l.next.add (copy.toNat : Int)
  let pt ← l.put.add (copy.toNat : Int)
  set { l with copy := copy, have_ := l.have_ - copy, next := nx, left := l.left - copy, put := pt }
  wrS c.st fun s => { s with length := s.length - copy }

/-- The heap after the copy: `n` bytes written into the window block, and `state->length` set to `L`. -/
def copiedHeap (h : Heap) (zs win : Nat) (s : InflateState) (da sa : Array UInt8) (od off2 n : Nat) (L : UInt32) : Heap :=
  setI { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n)) } zs { s with length := L }

/-- The registers after the copy of `n` bytes. -/
def storedRegs (l : IL) (n : UInt32) (bb off2 win od : Nat) : IL :=
  { l with copy := n, have_ := l.have_ - n, next := .ref (.blk bb) (off2 + n.toNat), left := l.left - n, put := .ref (.blk win) (od + n.toNat) }

/-- **The copy of one piece.** `n = min(length, have, left)` bytes move from the input chunk (block `bb`) to the window (block
`win`); the two blocks differ, both ranges are inside their blocks. The heap changes in the window block and in
`state->length`. -/
theorem storedTail_run (c : BCtx) {h : Heap} {l : IL} {zs : Nat} {s : InflateState} {bb off2 win od : Nat}
    {da sa : Array UInt8} (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (hput : l.put = .ref (.blk win) od) (hnext : l.next = .ref (.blk bb) off2)
    (hd : h.bytes win = some da) (hsa : h.bytes bb = some sa) (hro : h.ro win = false) (hne : win ≠ bb)
    (_hhave : l.have_ ≠ 0) (_hleft : l.left ≠ 0) (_hcopy : l.copy ≠ 0)
    (h1 : od + l.left.toNat ≤ da.size) (h2 : off2 + l.have_.toNat ≤ sa.size) :
    runX (storedTail c) l h = .ok ((.ok (), storedRegs l (clampCopy l.copy l.have_ l.left) bb off2 win od),
      copiedHeap h zs win s da sa od off2 (clampCopy l.copy l.have_ l.left).toNat (s.length - clampCopy l.copy l.have_ l.left)) := by
  obtain ⟨hn1, hn2, hn3⟩ := clampCopy_le l.copy l.have_ l.left
  obtain ⟨n, hn⟩ : ∃ n, n = clampCopy l.copy l.have_ l.left := ⟨_, rfl⟩
  rw [← hn] at hn1 hn2 hn3 ⊢
  have hmc : memcpyB l.put l.next n.toNat h = .ok ((), { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) }) := by
    rw [hput, hnext]; exact memcpyB_blk_ok hd hsa hro hne (by omega) (by omega)
  have hsz : (copyRange da sa od off2 n.toNat).size = da.size := size_copyRange _ _ _ _ _
  have hdg : (Space.get h (BRef.blk win) : Option (Array UInt8)) = some da := hd
  have hsg : (Space.get h (BRef.blk bb) : Option (Array UInt8)) = some sa := hsa
  obtain ⟨a2, ha2, hs2⟩ := get_after_put hd hsz hsg
  obtain ⟨a3, ha3, hs3⟩ := get_after_put hd hsz hdg
  have hadd1 : OkOn { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } (l.next.add (n.toNat : Int))
      (.ref (.blk bb) (off2 + n.toNat)) := by
    rw [hnext]; exact Ptr.add_nat_ok ha2 (by omega)
  have hadd2 : OkOn { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } (l.put.add (n.toNat : Int))
      (.ref (.blk win) (od + n.toNat)) := by
    rw [hput]; exact Ptr.add_nat_ok ha3 (by omega)
  have hs' : ({ h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } : Heap).istates zs = some s := hs
  have hw : wrS c.st (fun s => { s with length := s.length - n })
      { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } =
      .ok ((), setI { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } zs
        { s with length := s.length - n }) := wrS_ok hc hs' _
  unfold storedTail storedRegs copiedHeap
  rw [runX_bind, runX_get]
  by_cases e1 : l.copy > l.have_
  · by_cases e2 : l.have_ > l.left
    · have hv : n = l.left := by rw [hn]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok hmc, runX_lift_ok hadd1, runX_lift_ok hadd2, runX_set,
        runX_lift_ok hw]
    · have hv : n = l.have_ := by rw [hn]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok hmc, runX_lift_ok hadd1, runX_lift_ok hadd2, runX_set,
        runX_lift_ok hw]
  · by_cases e2 : l.copy > l.left
    · have hv : n = l.left := by rw [hn]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok hmc, runX_lift_ok hadd1, runX_lift_ok hadd2, runX_set,
        runX_lift_ok hw]
    · have hv : n = l.copy := by rw [hn]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok hmc, runX_lift_ok hadd1, runX_lift_ok hadd2, runX_set,
        runX_lift_ok hw]

/-- The loop body of `case STORED`. -/
def storedBody (c : BCtx) : X Unit := do
  let s ← ldInflateState c.st
  modify fun l => { l with copy := s.length }
  PULL c
  ROOM c
  storedTail c

/-- The condition of the copy loop. -/
def storedCond (c : BCtx) : X Bool := do return (← rdS c.st (·.length)) != 0

/-- `case STORED` as the function `back_STORED`, with the loop split into `storedCond` and `storedBody`. -/
theorem back_STORED_eq (c : BCtx) : back_STORED c = (do
    BYTEBITS
    NEEDBITS c 32
    let l ← get
    if (l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64)) then
      badMode c "invalid stored block lengths"
      return
    wrS c.st fun s => { s with length := l.hold.toUInt32 &&& 0xffff }
    INITBITS
    xwhile (storedCond c) (storedBody c)
    setMode c.st TYPE) := rfl

theorem drop_take_drop (a : List UInt8) (o k n : Nat) :
    ((a.drop o).take k).drop n = (a.drop (o + n)).take (k - n) := by
  rw [List.drop_take, List.drop_drop]
  all_goals (try (congr 2; omega))

/-- The length of the state record in the heap (0 if there is none): the measure of the copy loop. -/
def stLen (zs : Nat) (h : Heap) : Nat := match h.istates zs with
  | some s => s.length.toNat
  | none => 0

theorem stLen_of {zs : Nat} {h : Heap} {s : InflateState} (hs : h.istates zs = some s) : stLen zs h = s.length.toNat := by
  simp [stLen, hs]

end Zlib.Infback.Proofs
