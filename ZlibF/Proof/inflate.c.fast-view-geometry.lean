import ZlibF.Proof.«inflate.c.fast-view-window-data»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast-loop output guard reserves enough space for every
decoded match, whose length is at most 258 bytes. -/
theorem fast_output_room_of_guard
    {h : Heap} {slow : IL} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx} {dest : BRef}
    {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (avail : 258 ≤ slow.left.toNat)
    (length : l.len.toNat ≤ 258)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    j ≤ output.size ∧
      (oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat) := by
  have endBound : oo + slow.left.toNat - 257 ≤ output.size := by omega
  have currentBound : j ≤ output.size := by
    by_cases inside : j ≤ output.size
    · exact inside
    · rw [outPtr, endPtr] at guard
      simp [C.run, Ptr.lt, outputGet, inside] at guard
  have run := Ptr.lt_ok (r := dest) (a := output)
    outputGet currentBound endBound
  rw [outPtr, endPtr] at guard
  change (Ptr.lt (.ref dest j)
    (.ref dest (oo + slow.left.toNat - 257))) h = .ok (true, h) at guard
  rw [run] at guard
  have strict : j < oo + slow.left.toNat - 257 := by
    simpa using guard
  exact ⟨currentBound, current, by omega⟩

/-- The `out - beg` pointer difference used by the translated distance
branch counts bytes produced since the beginning of this call. -/
theorem fast_produced_of_diff
    {h : Heap} {dest : BRef} {output : Array UInt8}
    {bg j : Nat} {d : Int64} {l : Zlib.Inffast.L}
    (outputGet : Space.get h dest = some output)
    (currentBound : j ≤ output.size)
    (beginBound : bg ≤ output.size)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (diff : C.run (Ptr.diff (.ref dest j) (.ref dest bg)) h =
      .ok (d, h))
    (opEq : l.op = d.toUInt64.toUInt32) :
    l.op.toNat = j - bg ∧ l.op.toNat ≤ j := by
  have intEq : (j : Int) - (bg : Int) = ((j - bg : Nat) : Int) := by
    omega
  have run := Ptr.diff_ok (r := dest) (a := output)
    outputGet currentBound beginBound
    (by omega : -(2 ^ 63 : Int) ≤ (j : Int) - (bg : Int) ∧
      (j : Int) - (bg : Int) < 2 ^ 63)
  change (Ptr.diff (.ref dest j) (.ref dest bg)) h =
    .ok (d, h) at diff
  rw [run] at diff
  have dEq : d = Int64.ofInt ((j : Int) - (bg : Int)) := by
    injection diff with eq
    exact congrArg Prod.fst eq.symm
  rw [intEq] at dEq
  have produced : l.op.toNat = j - bg := by
    rw [opEq, dEq]
    exact Zlib.Inffast.Proofs.i64_toU32 _ span
  exact ⟨produced, by omega⟩

end Zlib.Inflate.Proofs
