import ZlibNgF.Proof.«gzread.c.lookspec»

/-!
# Parts of `gzungetc` on a read handle (`ZlibNgF`)

The slide of the output buffer (`gzread.c:498-504`): when `x.next == out`, the `x.have` bytes at the start of `out`
move to its end, one byte at a time from the top. Every pointer the loop forms stays inside `[out, out + 2 * size]`
of the one buffer block, the comparison `src > out` is between two pointers into that block, and only bytes of
`out` change (ISO C17 §6.5.6p8, §6.5.8p5).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-- The condition of the slide loop of `gzungetc` (copied from the translation). -/
def slideCond (state : GzPtr) (s : SlideLoop) : G (Bool × SlideLoop) := do
  return (← lm (Ptr.lt (← (← ldGz state).out.get) s.src), s)

/-- The body of the slide loop of `gzungetc` (copied from the translation). -/
def slideBody (s : SlideLoop) : G SlideLoop := do
  let dest ← lm (s.dest.add (-1))
  let src ← lm (s.src.add (-1))
  lm (store8 dest (← lm (load8 src)))
  return ⟨src, dest⟩

theorem subH {h : Heap} {c off : Nat} {a : Array UInt8} (ha : h.bytes c = some a) (hk : off + 1 ≤ a.size) :
    (Ptr.ref (BRef.heap c) (off + 1) : BPtr).add (-1) h = .ok (.ref (.heap c) off, h) := by
  have hg : Space.get h (BRef.heap c) = some a := ha
  rw [Inftrees.add_ok hg (by omega) (by omega) (by omega)]
  congr 3; omega

/-- **The slide loop.** With `out` at offset `o` of block `c` (not the state's block), `hv < n2` bytes to move and
`o + n2` inside the block: the loop ends with `dest = out + n2 - hv`, the world unchanged, and only the bytes of
`[o, o + n2)` of block `c` changed. -/
theorem slide_spec {W : World} {H : Heap} {b c o : Nat} {s : GzState} {a : Array UInt8}
    (hs : W.gz H b = some s) (hout : s.out = .val (.ref (.heap c) o)) (hcb : c ≠ b) (ha : H.bytes c = some a)
    {hv n2 : Nat} (hlt : hv < n2) (hfit : o + n2 ≤ a.size) (hvb : hv < 2 ^ 32) :
    GSat W H (gwhile (slideCond (some b)) slideBody ⟨.ref (.heap c) (o + hv), .ref (.heap c) (o + n2)⟩)
      (fun lp W' H' => W' = W ∧ lp.dest = .ref (.heap c) (o + (n2 - hv)) ∧ HBuf H H' c o (o + n2)) := by
  let I : SlideLoop → World → Heap → Prop := fun st W' H' => W' = W ∧ ∃ k, k ≤ hv ∧
    st = ⟨.ref (.heap c) (o + k), .ref (.heap c) (o + (n2 - hv) + k)⟩ ∧ HBuf H H' c o (o + n2)
  let μ : SlideLoop → Nat := fun st => match st.src with | .ref _ off => off - o | _ => 0
  refine gsat_gwhile I μ (fun lp W' H' => W' = W ∧ lp.dest = .ref (.heap c) (o + (n2 - hv)) ∧ HBuf H H' c o (o + n2))
    ?_ (s := ⟨.ref (.heap c) (o + hv), .ref (.heap c) (o + n2)⟩)
    ⟨rfl, hv, Nat.le_refl _, by congr 2; omega, HBuf.refl H c o (o + n2)⟩ (by show o + hv - o < 2 ^ 64; omega)
  rintro st W' H' ⟨rfl, k, hk, rfl, x⟩
  obtain ⟨a', ha', hsz⟩ := x.size ha
  have hsW : W'.gz H' b = some s := by rw [x.gz (Ne.symm hcb)]; exact hs
  unfold slideCond
  refine GSat.bind (GSat.of_eq (ldGz_app hsW) ?_)
  refine GSat.bind (GSat.lm ⟨_, H', by rw [hout]; rfl, ?_⟩)
  have hg : Space.get H' (BRef.heap c) = some a' := ha'
  have hcmp : o ≤ a'.size ∧ o + k ≤ a'.size := ⟨by omega, by omega⟩
  refine GSat.bind (GSat.lm ⟨decide (o < o + k), H', by
    simp only [Ptr.lt, hg, ite_true, hcmp, and_self], ?_⟩)
  refine GSat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · -- one more byte
    have hk0 : 0 < k := by simpa using hc
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    unfold slideBody
    have e1 := subH ha' (off := o + (n2 - hv) + k') (by omega)
    rw [show o + (n2 - hv) + (k' + 1) = o + (n2 - hv) + k' + 1 by omega]
    refine GSat.bind (GSat.lm ⟨_, H', e1, ?_⟩)
    have e2 := subH ha' (off := o + k') (by omega)
    rw [show o + (k' + 1) = o + k' + 1 by omega]
    refine GSat.bind (GSat.lm ⟨_, H', e2, ?_⟩)
    obtain ⟨v, ev⟩ := load8_heap ha' (off := o + k') (by omega)
    refine GSat.bind (GSat.lm ⟨_, H', ev, ?_⟩)
    refine GSat.bind (GSat.lm ⟨(), _, store8_heap ha' (off := o + (n2 - hv) + k') (by omega) v, ?_⟩)
    refine GSat.pure ⟨⟨rfl, k', by omega, rfl, x.trans (HBuf.store8 ha' (by omega) (by omega) v) (Nat.le_refl _)
      (Nat.le_refl _)⟩, ?_⟩
    show o + k' - o < o + (k' + 1) - o
    omega
  · -- `src == out`: done
    have hk0 : k = 0 := by simp at hc; omega
    subst hk0
    exact ⟨rfl, rfl, x⟩

end ZlibNgF.Proof.GzMode
