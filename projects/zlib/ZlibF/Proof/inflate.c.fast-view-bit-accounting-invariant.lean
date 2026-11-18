import ZlibF.Proof.«inflate.c.fast-view-body-condition-heap-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An exact fast-body stream relation accounts for held bits and bytes read.
The bound on consumed bits rules out truncating past the end of the stream. -/
theorem fast_stream_drop_bit_accounting
    {slow slowFinal : IL} {bs : List UInt8} {used consumed : Nat}
    (usedBound : used ≤ bs.length)
    (consumedBound : consumed ≤ (stream slow bs).length)
    (source : stream slowFinal (bs.drop used) =
      (stream slow bs).drop consumed) :
    slowFinal.bits.toNat + consumed = slow.bits.toNat + 8 * used := by
  have lengths := congrArg List.length source
  simp only [stream, List.length_append, natBits_length,
    bytesBits_length, List.length_drop] at lengths consumedBound
  omega

/-- Even when a drop goes beyond the stream, the final held-bit count
cannot exceed the initial count plus the bits in the bytes read. -/
theorem fast_stream_drop_bit_upper
    {slow slowFinal : IL} {bs : List UInt8} {used consumed : Nat}
    (usedBound : used ≤ bs.length)
    (source : stream slowFinal (bs.drop used) =
      (stream slow bs).drop consumed) :
    slowFinal.bits.toNat ≤ slow.bits.toNat + 8 * used := by
  have lengths := congrArg List.length source
  simp only [stream, List.length_append, natBits_length,
    bytesBits_length, List.length_drop] at lengths
  omega

/-- The distance-extra-bit suffix removes held bits and therefore preserves
the fast-loop bound without a new assumption about the output heap. -/
theorem FastInputPacket.distCont_bits_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    (extraBits : l.op.toNat ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30) :
    let slowNext : IL := { slow with
      hold := slow.hold >>> l.op.toUInt64,
      bits := slow.bits - l.op }
    slowNext.bits.toNat ≤ 30 := by
  have dropped := DROPBITS_inv packet.source l.op extraBits (by omega)
  have count := dropped.2.2
  change (slow.bits - l.op).toNat =
    slow.bits.toNat - l.op.toNat at count
  change (slow.bits - l.op).toNat ≤ 30
  omega

end Zlib.Inflate.Proofs
