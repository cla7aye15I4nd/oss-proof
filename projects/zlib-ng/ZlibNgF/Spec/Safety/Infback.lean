import ZlibNgF.Spec.Common.Infback

/-!
# Safety goals of the call-back decoder (`ZlibNgF`)

`infback.c`: `inflateBackInit_`, `inflateBack`, `inflateBackEnd`. Each goal says that the call does not fault (no
undefined behaviour, and it returns) for every stream the function accepts, and, where the call-backs do not run, that
it changes only what the frame names. The premises on the call-backs are in `ZlibNgF.Spec.Common.Infback` and on the
deviations page.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec.Safety
open ZlibNgF.Spec C

/-- `int inflateBackInit_(z_stream *strm, int windowBits, unsigned char *window, const char *version,
int stream_size)`: for a `Z_NULL` stream or a live `z_stream` with the default allocator, a `NULL` or readable
`version`, and every `windowBits`, `window` and `stream_size`, does not fault and changes only the stream record and
fresh blocks (the call does not touch the window). The heap is well formed (`FreshBlocks`). -/
def Goal.inflateBackInit__safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (windowBits : Int32) (window version : BPtr) (size : Int32),
    FreshBlocks h → InitReady h s → VersionOk h version →
    ∃ r h', C.run (ZlibNg.Infback.inflateBackInit_ s windowBits window version size) h = .ok (r, h') ∧
      Frame h h' (streamIds s) [] [] []

/-- `int inflateBack(z_stream *strm, in_func in, void *in_desc, out_func out, void *out_desc)`: for every accepted
stream, and, on a reachable stream with window `w` of `n` bytes, call-backs that are well behaved for some invariant
holding of the first chunk (`BackCallPre`), does not fault and returns. -/
def Goal.inflateBack_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (inCb : ZlibNg.Infback.InCb) (inDesc : BPtr) (outCb : ZlibNg.Infback.OutCb)
    (outDesc : BPtr),
    BackHandle h s →
    (∀ w n, BackReachable h s w n → ∃ I, BackCallPre h s w n inCb inDesc outCb outDesc I) →
    ∃ r h', C.run (ZlibNg.Infback.inflateBack s inCb inDesc outCb outDesc) h = .ok (r, h')

/-- Non-vacuity of `inflateBack_safety`: its premises hold together on a reachable stream whose first chunk
(`next_in`, `avail_in`) is non-null and non-empty. -/
def Goal.inflateBack_nonvacuous : Prop :=
  ∃ h s w n z inCb inDesc outCb outDesc I, BackReachable h s w n ∧ BackCallPre h s w n inCb inDesc outCb outDesc I ∧
    StreamAt h s z ∧ z.next_in ≠ .null ∧ 0 < z.avail_in

/-- `int inflateBackEnd(z_stream *strm)`: for every accepted stream, does not fault and frees only the stream's state
block. -/
def Goal.inflateBackEnd_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    BackHandle h s →
    ∃ r h', C.run (ZlibNg.Infback.inflateBackEnd s) h = .ok (r, h') ∧
      Frame h h' (streamIds s) (stateIds h s) [] []

end ZlibNgF.Spec.Safety
