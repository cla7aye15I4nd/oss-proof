import ZlibF.Spec.Common.Back
import ZlibF.Spec.Functional.Format.Deflate

/-!
# The callback decoder: the functional goal of `inflateBack`

`Goal.inflateBack`, split from `ZlibF/Spec/Public/Back.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`): it states that the delivered output decodes the input
(`Deflate.Decodes`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C Zlib.Infback ZlibF.Spec

/-- `int inflateBack(z_streamp strm, in_func in, void *in_desc, out_func out, void *out_desc)`.
For every finite, returning caller protocol, decode raw DEFLATE and deliver the chunks through
that actual output callback. The protocol's observation relation records the bytes delivered.
No allocation or free by the library is charged to the caller's callbacks. -/
def Goal.inflateBack : Prop :=
  (∀ h input inDesc output outDesc,
    C.run (Zlib.Infback.inflateBack none input inDesc output outDesc) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r i z s input inDesc output outDesc
      (protocol : CallbackProtocol r i s.window s.wsize.toNat input inDesc output outDesc) first,
    BackValid h r i z s →
    (if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first) →
    Separate z.next_in first.length s.window s.wsize.toNat →
    protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first } →
    ∃ rc after z' s' log unused consumed,
      C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (rc, after) ∧
      BackValid after r i z' s' ∧ s'.window = s.window ∧ s'.wsize = s.wsize ∧
      protocol.invariant after log ∧
      (rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) ∧
      consumed ++ unused = log.supplied ∧ unused.length = z'.avail_in.toNat ∧
      unused <:+ log.held ∧
      (log.exhausted = true → z'.next_in = .null ∧ unused = []) ∧
      (log.exhausted = false → z'.next_in = advance log.active (log.held.length - unused.length)) ∧
      (∀ chunk, chunk ∈ log.chunks → chunk ≠ [] ∧ chunk.length ≤ s.wsize.toNat) ∧
      (rc = Z_STREAM_END → Deflate.Decodes [] consumed log.chunks.flatten ∧ log.failed = false) ∧
      (rc = Z_BUF_ERROR → log.exhausted = true ∨ log.failed = true) ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out ∧ z'.adler = z.adler ∧
      CallbackFrame protocol.own h after r i s.window s.wsize.toNat ∧
      (∀ b, ¬ protocol.own b → (after.live b ↔ h.live b)))

end ZlibF.Spec.Public
