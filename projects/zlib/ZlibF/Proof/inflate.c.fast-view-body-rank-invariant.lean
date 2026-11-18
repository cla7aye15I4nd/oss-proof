import ZlibF.Proof.«inflate.c.fast-view-loop-measure-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A retained dispatch packet supplies the next iteration's concrete
output view once its ghost cursor and count are identified. -/
theorem fast_packet_output_view
    {after : Heap} {r : ZStreamRef} {slow : IL} {bs : List UInt8}
    {dest : BRef} {oo left : Nat}
    (buffers : DispatchBuffers after r slow bs)
    (put : slow.put = .ref dest oo)
    (count : slow.left.toNat = left) :
    ∃ output, Space.get after dest = some output ∧
      Space.ro after dest = false ∧
      oo + left ≤ output.size := by
  rcases buffers.output.range with null | ⟨_, writable, _⟩
  · rw [put] at null
    simp at null
  · rcases writable rfl with null | ⟨ref, off, output, ptr, get, ro, fit⟩
    · rw [put] at null
      simp at null
    · rw [put] at ptr
      cases ptr
      exact ⟨output, get, ro, by simpa only [count] using fit⟩

end Zlib.Inflate.Proofs
