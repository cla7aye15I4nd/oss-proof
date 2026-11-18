import ZlibF.Proof.«inflate.c.fast-view-distance-class»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A linked distance leaf fits the held bits after the root code is
consumed. The bound follows from the unchanged unread byte suffix. -/
theorem linked_distance_leaf_bits_fit
    {slow next : IL} {bs : List UInt8}
    {rootBits leafBits : Nat}
    (held : 15 ≤ slow.bits.toNat)
    (rootFits : rootBits ≤ slow.bits.toNat)
    (total : leafBits + rootBits ≤ 15)
    (source : stream next bs = (stream slow bs).drop rootBits) :
    leafBits ≤ next.bits.toNat := by
  have lengths := congrArg List.length source
  simp only [stream, List.length_append, natBits_length,
    bytesBits_length, List.length_drop] at lengths
  omega

end Zlib.Inflate.Proofs
