import ZlibF.Proof.«inflate.c.fast-view-dolen-len-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A selected second-level length entry remains inside the array and
is a leaf whose total code width fits the fifteen held bits. -/
theorem len_table_link_target
    {codes : Array Code} {baseOff rootBits rootIndex slice : Nat}
    (safe : LenTableSafe codes baseOff rootBits)
    (root : rootIndex < 2 ^ rootBits)
    (link : LenLink (codes.getD (baseOff + rootIndex) default))
    (sliceBound : slice <
      2 ^ (codes.getD (baseOff + rootIndex) default).op.toNat) :
    let entry := codes.getD (baseOff + rootIndex) default
    let target := baseOff + entry.val.toNat + slice
    target < codes.size ∧
      LenLeaf entry.bits.toNat (codes.getD target default) ∧
      (codes.getD target default).bits.toNat +
        entry.bits.toNat ≤ 15 := by
  rcases safe with ⟨_, _, entries⟩
  have selected := entries rootIndex root
  rw [ite_eq_left link] at selected
  rcases selected with ⟨_, _, _, size, leaves⟩
  have bound : baseOff +
      (codes.getD (baseOff + rootIndex) default).val.toNat +
      slice < codes.size := by
    omega
  have leaf := leaves slice sliceBound
  exact ⟨bound, leaf, leaf.1⟩

end Zlib.Inflate.Proofs
