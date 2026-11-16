import ZlibF.Spec.Common.GzState

namespace ZlibF.Spec.Public
open C Zlib.Infback ZlibF.Spec

def BackValid (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : InflateState) : Prop :=
  r.get h = some z ∧ h.istates i = some s ∧ z.state = some (.inflate i) ∧
  z.zalloc = .fn "zcalloc" ∧ z.zfree = .fn "zcfree" ∧ s.WellFormed ∧
  8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 ∧ s.wsize.toNat = 2 ^ s.wbits.toNat ∧
  s.window ≠ .null ∧ Writable h s.window s.wsize.toNat ∧
  Fresh h ∧ Zlib.Inflate.Spec.Uniq h ∧ LibraryGlobals h

def backInitialState (garbage : Nat → UInt64) (window : BPtr) (bits : Int32) : InflateState :=
  { InflateState.garbage garbage with
    dmax := 32768, wbits := bits.toUInt32, wsize := 1 <<< bits.toUInt32
    window := window, wnext := 0, whave := 0, sane := 1 }

/-- `int inflateBackInit_(z_streamp strm, int windowBits, unsigned char *window,
const char *version, int stream_size)`.
The caller retains the window. Only the state record is allocated; its other integer fields
remain arbitrary. Refusal precedes allocation, and allocation failure retains the old state field. -/
def Goal.inflateBackInit_ : Prop :=
  (∀ h p wb window version head size, VersionValue h version head →
    (head ≠ some 49 ∨ size ≠ 112) →
    C.run (Zlib.Infback.inflateBackInit_ p wb window version size) h = .ok (Z_VERSION_ERROR, h)) ∧
  (∀ h p wb window version, VersionValue h version (some 49) →
    (p = none ∨ window = .null ∨ wb.toInt < 8 ∨ 15 < wb.toInt) →
    C.run (Zlib.Infback.inflateBackInit_ p wb window version 112) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r z wb window version,
    Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h → r.get h = some z →
    DefaultOrNull z → VersionValue h version (some 49) →
    8 ≤ wb.toInt → wb.toInt ≤ 15 → window ≠ .null → Writable h window (2 ^ wb.toInt.toNat) →
    ∃ rc after,
      C.run (Zlib.Infback.inflateBackInit_ (some r) wb window version 112) h = .ok (rc, after) ∧
      after.nalloc = h.nalloc + 1 ∧
      if h.allocOk h.nalloc = false then
        rc = Z_MEM_ERROR ∧ SameObjects (r.put h (preparedStream z)) after
      else rc = Z_OK ∧
        let z' := { preparedStream z with state := some (.inflate h.nextBlk) }
        let s := backInitialState (h.garbage h.nalloc) window wb
        BackValid after r h.nextBlk z' s ∧
        Frame h after (StreamRoot r) ∧
        LiveChange h after (fun b => b = h.nextBlk) (fun _ => False))

structure BackLog where
  supplied : List UInt8
  chunks : List (List UInt8)
  active : BPtr
  held : List UInt8
  exhausted : Bool := false
  failed : Bool := false

/-- Caller callbacks may allocate, free, and update any of their own objects, including records.
They cannot change whether a block that stays live is read-only: C code has no way to make memory
read-only or writable (the model's `ro` marks `const` storage from its allocation on). -/
def ExternalFrame (own : Nat → Prop) (h after : Heap) : Prop :=
  Frame h after own ∧ Fresh after ∧ Zlib.Inflate.Spec.Uniq after ∧
  (∀ b, ¬ h.live b → after.live b → own b) ∧
  (∀ b, h.live b → after.live b → after.ro b = h.ro b)

def ExternalAgreement (own : Nat → Prop) (h after : Heap) : Prop :=
  h.nextBlk = after.nextBlk ∧ h.nalloc = after.nalloc ∧ h.allocOk = after.allocOk ∧
  h.garbage = after.garbage ∧ h.static = after.static ∧
  ∀ b, own b → h.bytes b = after.bytes b ∧ h.words b = after.words b ∧
    h.streams b = after.streams b ∧ h.gzheaders b = after.gzheaders b ∧
    h.dstates b = after.dstates b ∧ h.istates b = after.istates b ∧
    h.gzstates b = after.gzstates b ∧ h.ro b = after.ro b

/-- Hide only the window slice when comparing a callback's private state. A descriptor can
share the allocation while using bytes outside that slice. -/
def restoreWindow (before after : Heap) (window : BPtr) (capacity : Nat) : Heap :=
  match window with
  | .null => after
  | .ref r off => match Space.get before r, Space.get after r with
    | some old, some current => Space.put after r
        (current.extract 0 off ++ old.extract off (off + capacity) ++
          current.extract (off + capacity) current.size)
    | _, _ => after

def CallbackFrame (own : Nat → Prop) (h after : Heap) (r : ZStreamRef) (state : Nat)
    (window : BPtr) (capacity : Nat) : Prop :=
  Frame h after (fun b => StreamRoot r b ∨ b = state ∨ own b ∨ ByteRoot window b) ∧
  ((∀ b, ByteRoot window b → ¬ own b) →
    BufferFrame h after (fun b => StreamRoot r b ∨ b = state ∨ own b) [⟨window, capacity⟩])

/-- These are contracts of caller code, not assumed library callee contracts.
The input may depend on previous output. A finite source has an explicit total-input bound.
Output must preserve the current input until the next input callback. -/
structure CallbackProtocol (r : ZStreamRef) (state : Nat) (window : BPtr) (capacity : Nat)
    (input : InCb) (inDesc : BPtr) (output : OutCb) (outDesc : BPtr) where
  own : Nat → Prop
  invariant : Heap → BackLog → Prop
  inputBound : Nat
  disjoint : (¬ own state) ∧ (∀ b, StreamRoot r b → ¬ own b)
  local_ : ∀ h after log, ExternalAgreement own h (restoreWindow h after window capacity) →
    (invariant h log ↔ invariant after log)
  bounded : ∀ h log, invariant h log → log.supplied.length ≤ inputBound
  liveInput : ∀ h log, invariant h log → log.held ≠ [] → Bytes h log.active log.held.length log.held
  inStep : ∀ h log next, invariant h log → ∃ n pointer after bytes,
    input inDesc next h = .ok ((n, pointer), after) ∧
    bytes.length = n.toNat ∧ ExternalFrame own h after ∧
    SameBytePrefix h after window window capacity ∧
    (n ≠ 0 → Bytes after pointer n.toNat bytes ∧ Separate pointer n.toNat window capacity ∧
      ∀ b, ByteRoot pointer b → b ≠ state ∧ ¬ StreamRoot r b) ∧
    invariant after { log with
      supplied := log.supplied ++ bytes, active := pointer, held := bytes, exhausted := n == 0 }
  outStep : ∀ h log pointer n bytes, invariant h log →
    Bytes h pointer n.toNat bytes → n.toNat ≤ capacity →
    ∃ rc after, output outDesc pointer n h = .ok (rc, after) ∧ ExternalFrame own h after ∧
      SameBytePrefix h after window window capacity ∧
      (log.held ≠ [] → Bytes after log.active log.held.length log.held) ∧
      invariant after { log with chunks := log.chunks ++ [bytes], failed := log.failed || rc != 0 }

/-- `int inflateBackEnd(z_streamp strm)`.
Free only the state record. The caller's window is retained, even when it is a slice of another object. -/
def Goal.inflateBackEnd : Prop :=
  (∀ h, C.run (Zlib.Infback.inflateBackEnd none) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r z, r.get h = some z → z.state = none ∨ z.zfree = .null →
    C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r i z s, BackValid h r i z s →
    ∃ after, C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_OK, after) ∧
      r.get after = some { z with state := none } ∧
      LiveChange h after (fun _ => False) (fun b => b = i) ∧
      Frame h after (fun b => StreamRoot r b ∨ b = i) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk)

end ZlibF.Spec.Public
