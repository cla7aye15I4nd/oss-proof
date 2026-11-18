import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-four-byte-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The fast body's translated root lookup selects a bounded entry without
changing the synchronized caller byte view. -/
theorem FastInputPacket.fast_body_root_lookup
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1) :
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected : Zlib.Inffast.L :=
      { l with here := .ref codeRef (baseOff + rootSlice) }
    rootSlice < 2 ^ rootWidth ∧
      C.run (Ptr.add c.lcode rootSlice) h =
        .ok (.ref codeRef (baseOff + rootSlice), h) ∧
      FastInputPacket h slow bs selected := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  have sliceEq : rootSlice = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have sliceBound : rootSlice < 2 ^ rootWidth := by
    rw [sliceEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have addRun : C.run (Ptr.add c.lcode rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) := by
    rw [lcodePtr]
    exact Ptr.add_nat_ok codesGet (by
      have rootSize := safe.2.1
      omega)
  exact ⟨sliceBound, addRun,
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩⟩

end Zlib.Inflate.Proofs
