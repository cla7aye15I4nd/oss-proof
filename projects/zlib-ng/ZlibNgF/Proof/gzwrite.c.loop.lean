import ZlibNgF.Proof.«gzwrite.c.errx»
import ZlibNgF.Proof.«gzwrite.c.deflx»

/-!
# The loop of `gz_comp` (`ZlibNgF`)

The body of the loop is split at its join points: `cTail` (`deflate` and its check) and `cRT` (reset a full output
buffer, move `x.next`, then `cTail`). The loop ends by the potential `pot` of the stream (`DeflateGz`, module comment of
`gzwrite.c.needs.lean`): `(2^31 + 2^30) avail_in + 3 ψ + 2 (S - avail_out')`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds
open ZlibNg.Inflate ZlibNg.Deflate

theorem rdZ_run {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) {α : Type} (f : ZStream → α) :
    rdZ (some i) f h = .ok (f z, h) := by
  simp [rdZ, ldStream, hz, bind, pure]

theorem wrZ_run {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) (f : ZStream → ZStream) :
    wrZ (some i) f h = .ok ((), setZ h i (f z)) := by
  simp [wrZ, ldStream, stStream, hz, bind, setZ]

/-- The potential of stream `i` (see the module comment); `S` is the size of the buffer. -/
def pot (ψ : Int32 → C.DeflateState → Nat) (f : Int32) (S : Nat) (H : Heap) (i : Nat) : Nat :=
  match H.streams i with
  | some z => match z.state with
    | some sb => match H.dstate sb with
      | some st => (2 ^ 31 + 2 ^ 30) * z.avail_in.toNat + 3 * ψ f st +
          2 * (S - (if z.avail_out = 0 then S else z.avail_out.toNat))
      | none => 0
    | none => 0
  | none => 0

theorem pot_eq (ψ : Int32 → C.DeflateState → Nat) (f : Int32) (S : Nat) {H : Heap} {i : Nat} {z : ZStream}
    (hz : H.streams i = some z) {sb : Nat} (hsb : z.state = some sb) {st : C.DeflateState}
    (hst : H.dstate sb = some st) :
    pot ψ f S H i = (2 ^ 31 + 2 ^ 30) * z.avail_in.toNat + 3 * ψ f st +
      2 * (S - (if z.avail_out = 0 then S else z.avail_out.toNat)) := by
  simp [pot, hz, hsb, hst]

/-- The potential drops on a call that produces output. -/
theorem pot_arith (G S ai ai' ao ao' p p' : Nat) (hG : G ≤ 2 ^ 28) (h1 : ai' ≤ ai) (h2 : ao' ≤ ao) (h3 : ao ≤ S)
    (hS : 8 ≤ S)
    (hmu : p' + (ao - ao') ≤ p + G * (ai - ai') + (if ao' = 0 then 5 else 0)) (hp : ao' ≠ ao) :
    (2 ^ 31 + 2 ^ 30) * ai' + 3 * p' + 2 * (S - (if ao' = 0 then S else ao')) <
      (2 ^ 31 + 2 ^ 30) * ai + 3 * p + 2 * (S - ao) := by
  have e1 : ai = ai' + (ai - ai') := by omega
  have e2 : G * (ai - ai') ≤ 2 ^ 28 * (ai - ai') := Nat.mul_le_mul_right _ hG
  rw [e1, Nat.mul_add]
  generalize ai - ai' = k at e2 hmu
  generalize G * k = gk at e2 hmu
  by_cases h4 : ao' = 0
  · simp only [h4, ite_true] at hmu ⊢; omega
  · simp only [h4, ite_false] at hmu ⊢; omega

/-- The facts of a write handle in the state `GzWX` (not direct) that the loop uses. -/
theorem wx_facts {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z)
    (hd : s.direct = 0) :
    ∃ sb st, z.state = some sb ∧ H.dstate sb = some st ∧ DeflateInv.DInv H (some s.strm) ∧
      DRegisteredHeader H (some s.strm) none ∧ 8 ≤ s.size.toNat ∧ s.size.toNat ≤ 2 ^ 30 ∧
      z.avail_out.toNat ≤ s.size.toNat := by
  obtain ⟨hs, hz, hsz, hv, -⟩ := hx
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hs
  have hwm := modeOf hsF hv.2.1
  obtain ⟨sh, -⟩ := inv_of hsF hv.1
  obtain ⟨c, base, zF, hB, hzF, WB⟩ := (sh.write hwm).bufs hsz
  rw [setZ_streams_same] at hzF; cases hzF
  obtain ⟨hdiF, hsideF⟩ := WB.deflate hd
  have hreg := regNone (setZ_streams_same _ _ _) WB hdiF
  obtain ⟨hdi, -⟩ := dinv_setZ (a := z) (setZ_streams_same _ _ _) (flat_eq z) hdiF hsideF WB.nohdr
  rw [setZ_setZ, setZ_self hz] at hdi
  have hdi0 := hdiF
  obtain ⟨i, z0, sb, st, al, e0, hz0, hsb, hst, -, -⟩ := hdi0
  cases e0; rw [setZ_streams_same] at hz0; cases hz0
  obtain ⟨ko, kx, -, -, -, hko⟩ := WB.out hd
  have hko' : ko + z.avail_out.toNat = s.size.toNat := hko
  have hsw : s.size.toNat = s.want.toNat := by rw [hB.size]
  refine ⟨sb, st, hsb, hst, hdi, ?_, by rw [hsw]; exact sh.want_lo, by rw [hsw]; exact sh.want_hi,
    by omega⟩
  obtain ⟨sb', st', ⟨⟨z1, ⟨_, e1, hz1⟩, hsb1⟩, hst1⟩, hg⟩ := hreg
  cases e1; rw [setZ_streams_same] at hz1; cases hz1
  exact ⟨sb', st', ⟨⟨z, ⟨_, rfl, hz⟩, hsb1⟩, hst1⟩, hg⟩

end ZlibNgF.Proof.GzWrite
