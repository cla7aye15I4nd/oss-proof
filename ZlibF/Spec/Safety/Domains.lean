import ZlibF.Spec.Common.Domains

/-!
# Domains: safety goals

Split from `ZlibF/Spec/Public/Domains.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs

/-- Every accepted signed window parameter has a non-failing init on every permitted heap.
The fixed witness additionally rules out an empty caller domain. -/
def Goal.inflate_initialisation_domain : Prop :=
  (∀ h r version wb wrap bits,
    InitDomain h r version → Api.inflWbits wb.toInt = some (wrap, bits) →
    h.allocOk h.nalloc = true →
    ∃ after, C.run (Zlib.Inflate.inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r wrap bits ∧ StreamReachable .inflate after r) ∧
  InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
  (∀ wb wrap bits, Api.inflWbits wb.toInt = some (wrap, bits) →
    ∃ after, C.run (Zlib.Inflate.inflateInit2_ (some (.tab 0)) wb (.ref (.blk 1) 0) 112)
      witnessHeap = .ok (Z_OK, after) ∧ InflateInitial witnessHeap after (.tab 0) wrap bits)

/-- Full level, method, window, memory-level and strategy coverage, including normalisation.
No assumption that the post-init invariant already holds is permitted. -/
def Goal.deflate_initialisation_domain : Prop :=
  (∀ h r version level method wb mem strategy p,
    InitDomain h r version →
    Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
    (∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) →
    ∃ after, C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
      .ok (Z_OK, after) ∧ DeflateInitial h after r p ∧ StreamReachable .deflate after r) ∧
  InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
  (∀ level method wb mem strategy p,
    Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
    ∃ after, C.run (Zlib.Deflate.deflateInit2_ (some (.tab 0)) level method wb mem strategy
      (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DeflateInitial witnessHeap after (.tab 0) p)

/-- All eight documented callback-window sizes, with an arbitrary valid caller window.
Init establishes the back-decoder invariant and retains ownership of the window. -/
def Goal.inflate_back_initialisation_domain : Prop :=
  (∀ h r version wb window,
    InitDomain h r version → 8 ≤ wb.toInt → wb.toInt ≤ 15 →
    window ≠ .null → Writable h window (2 ^ wb.toInt.toNat) → h.allocOk h.nalloc = true →
    ∃ after z s, C.run (Zlib.Infback.inflateBackInit_ (some r) wb window version 112) h =
      .ok (Z_OK, after) ∧ BackValid after r h.nextBlk z s ∧ s.window = window ∧
      s.wbits = wb.toUInt32 ∧ Frame h after (StreamRoot r) ∧
      LiveChange h after (fun b => b = h.nextBlk) (fun _ => False)) ∧
  InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
  (∀ wb : Int32, 8 ≤ wb.toInt → wb.toInt ≤ 15 →
    ∃ after z s, C.run (Zlib.Infback.inflateBackInit_ (some (.tab 0)) wb (.ref (.blk 2) 0)
      (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      BackValid after (.tab 0) witnessHeap.nextBlk z s ∧ s.window = .ref (.blk 2) 0)

end ZlibF.Spec.Public
