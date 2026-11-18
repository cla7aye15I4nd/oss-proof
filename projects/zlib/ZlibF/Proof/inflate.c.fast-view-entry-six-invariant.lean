import ZlibF.Proof.«inflate.c.fast-view-body-rank-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The synchronized input packet exposes exactly the six caller bytes
needed by the next actual fast-body iteration. -/
theorem FastInputPacket.six_unread
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    (margin : 6 ≤ slow.have_.toNat) :
    ∃ first second third fourth fifth sixth rest,
      bs = first :: second :: third :: fourth :: fifth :: sixth :: rest := by
  have length : 6 ≤ bs.length := by
    rw [← packet.source.have_eq]
    exact margin
  cases bs with
  | nil => simp at length
  | cons first bs =>
    cases bs with
    | nil => simp at length
    | cons second bs =>
      cases bs with
      | nil => simp at length
      | cons third bs =>
        cases bs with
        | nil => simp at length
        | cons fourth bs =>
          cases bs with
          | nil => simp at length
          | cons fifth bs =>
            cases bs with
            | nil => simp at length
            | cons sixth rest =>
              exact ⟨first, second, third, fourth, fifth, sixth, rest, rfl⟩

/-- The consumed-byte count in a fast-body packet gives the exact remaining
public input count, independent of output writes. -/
theorem FastInputPacket.have_after_drop
    {h after : Heap} {slow slowFinal : IL}
    {bs : List UInt8} {l result : Zlib.Inffast.L}
    {used : Nat}
    (before : FastInputPacket h slow bs l)
    (final : FastInputPacket after slowFinal (bs.drop used) result)
    (bound : used ≤ bs.length) :
    slowFinal.have_.toNat + used = slow.have_.toNat := by
  have initial := before.source.have_eq
  have remaining := final.source.have_eq
  rw [List.length_drop] at remaining
  omega

/-- Advancing the input cursor and decreasing its count by the same number
of bytes keeps the fixed `last` pointer aligned with the unread suffix. -/
theorem fast_last_after_advance
    {c : Zlib.Inffast.Ctx} {ref : BRef}
    {off haveCount remaining used : Nat}
    (last : c.last = .ref ref (off + haveCount - 5))
    (count : remaining + used = haveCount) :
    c.last = .ref ref (off + used + remaining - 5) := by
  rw [last]
  congr 1
  omega

end Zlib.Inflate.Proofs
