import ZlibF.Spec.InflateFastBodyToken
import ZlibF.Spec.InflateFastCallOrigin
import ZlibF.Spec.InflateFastDistanceOrigin

/-!
# Fast decoder over byte views: every old goal follows from the new one

The commit "Fast decoder environment: input and output in any byte view" changed the situation
of `inflate_fast` (`Zlib.Inffast.Proofs.EnvG`): its input and output were heap blocks (`ib ob :
Nat`, read through `h0.bytes`), and are now byte views (`ib ob : BRef`, read through `Space.get`).
The statements of the registered `Zlib.Inffast.Spec` goals changed with it.

This file restates the old definitions verbatim, from the parent of that commit (`4ed7315e^` on
`dev`), under the
namespace `InffastOld` (`InffastOld.Proofs` for the definitions of `ZlibF/Proof/inffast.c.*`,
`InffastOld.Spec` for those of `ZlibF/Spec/InflateFast*`). Only the namespace lines and the `open`
lines differ from the old source, so that the old text names the old definitions. A definition
that does not depend on the situation (`pullL`, `matchArr`, the table predicates, the format) is
the current one.

`toNew` maps an old situation to a new one: a heap block `b` becomes the byte view `BRef.blk b`.
Each `X_old_of_new : Zlib.Inffast.Spec.Goal.X → InffastOld.Spec.Goal.X` shows that the new goal
is at least as strong as the old one. Nothing is evaluated: every fact is checked by the kernel.

How the old and new forms relate. `toNew` itself needs `BRef.blk.inj` for two fields: `hsep`
(`ib ≠ ob` becomes `BRef.blk ib ≠ BRef.blk ob`) and `hwin` (`WinRel`). Of the definitions the
goals use, `InputFrame` is related only through `BRef.blk.inj` (`ib = ob` against
`BRef.blk ib = BRef.blk ob`, `inputFrame_iff`). Every other old definition is definitionally the
new one on `toNew`: the heap (a record update against `Space.put` and `setI` on `BRef.blk`), the
pointers (`.ref (.blk e.ib)` against `.ref (toNew e).ib`), `Sg`, `DistLook`, `Look`, `ready` and
`FastPost`; the old structures (`CtxOK`, `LS`, `Origin.Inv`, `StepPre`, `Tables`) are
repackaged field by field, each field definitionally equal. The docstring of each
`X_old_of_new` says which case its goal is in.
-/

set_option autoImplicit false

namespace InffastOld.Proofs
open C Zlib.Inffast ZlibF.Spec
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec

section EnvSection

/-- How the window block relates to the output block. Without `alias` (every `Env`): another
block. With `alias` (`inflateBack`, whose output is the window): the output block itself is
allowed, and then `wnext = 0` and the window ends no later than the output range (`inside`). -/
@[reducible] def WinRel : Bool → Nat → Nat → UInt32 → Prop → Prop
  | false, wb, ob, _, _ => wb ≠ ob
  | true, wb, ob, wnext, inside => wb = ob → wnext = 0 ∧ inside

/-- Everything `inflate_fast` needs of the heap `h0` at entry, with the witnesses. These are the preconditions of
`inflate_fast_safe` (`Zlib.Inffast.Proofs.Env.of_pre` builds one from the hypotheses of the theorem). -/
structure EnvG (alias : Bool) where
  h0 : Heap
  strm : ZStreamPtr
  start : UInt32
  -- the stream record and the state
  r : ZStreamRef
  sm0 : ZStream
  stid : Nat
  s0 : InflateState
  hstrm : strm = some r
  hsm : r.get h0 = some sm0
  hrw : r.isRo = false
  hstate : sm0.state = some (StateRef.inflate stid)
  hs0 : h0.istates stid = some s0
  -- the input
  ib : Nat
  i0 : Nat
  IN : Array UInt8
  hnin : sm0.next_in = .ref (BRef.blk ib) i0
  hIN : h0.bytes ib = some IN
  hai : 6 ≤ sm0.avail_in.toNat
  hINsz : i0 + sm0.avail_in.toNat ≤ IN.size
  hINbig : IN.size < 2 ^ 63
  -- the output
  ob : Nat
  o0 : Nat
  A0 : Array UInt8
  hnout : sm0.next_out = .ref (BRef.blk ob) o0
  hA0 : h0.bytes ob = some A0
  hro : h0.ro ob = false
  hao : 258 ≤ sm0.avail_out.toNat
  hAsz : o0 + sm0.avail_out.toNat ≤ A0.size
  hAbig : A0.size < 2 ^ 63
  hstart : sm0.avail_out.toNat ≤ start.toNat
  hbeg : start.toNat - sm0.avail_out.toNat ≤ o0
  /-- Input and output are distinct blocks, or disjoint ranges of one block
  (`tests/regression/inflate-shared-block`). -/
  hsep : ib ≠ ob ∨ (ib = ob ∧
    (i0 + sm0.avail_in.toNat ≤ o0 ∨ o0 + sm0.avail_out.toNat ≤ i0))
  -- the bit buffer
  hbits : s0.bits.toNat < 8
  hhold : s0.hold.toNat < 2 ^ s0.bits.toNat
  hsane : s0.sane ≠ 0
  -- the window
  hws : s0.wsize.toNat ≤ 32768
  hwh : s0.whave.toNat ≤ s0.wsize.toNat
  hwn : s0.wnext.toNat ≤ s0.wsize.toNat
  wb : Nat
  woff : Nat
  W : Array UInt8
  hwin : s0.whave ≠ 0 →
    s0.window = .ref (BRef.blk wb) woff ∧
      WinRel alias wb ob s0.wnext (woff + s0.wsize.toNat ≤ o0 + sm0.avail_out.toNat) ∧ h0.bytes wb = some W ∧
      woff + s0.wsize.toNat ≤ W.size
  -- the tables
  rl : CodeRef
  ol : Nat
  LCA : Array Code
  hlc : s0.lencode = .ref rl ol
  hLCA : Space.get h0 rl = some LCA
  hlt : LenTableSafe LCA ol s0.lenbits.toNat
  rd : CodeRef
  od : Nat
  DCA : Array Code
  hdc : s0.distcode = .ref rd od
  hDCA : Space.get h0 rd = some DCA
  hdt : DistTableSafe DCA od s0.distbits.toNat

/-- The situation of every caller but `inflateBack`: the window is another block than the output. -/
abbrev Env := EnvG false

/-- The heap while `inflate_fast` runs: the output block is `A`, the message of the stream is `msg` and the mode of
the state is `m`; nothing else differs from `h0`. -/
def EnvG.heap {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32) : Heap :=
  ZStreamRef.put
    { e.h0 with bytes := upd e.h0.bytes e.ob (some A),
                istates := upd e.h0.istates e.stid (some { e.s0 with mode := m }) }
    e.r { e.sm0 with msg := msg }

variable {α : Bool} (e : EnvG α)

/-- The array at the input block while the output block holds `A`. -/
def EnvG.inArr (A : Array UInt8) : Array UInt8 := if e.ib = e.ob then A else e.IN

/-- When input and output share a block, the output array `A` has the size of
the block at entry and agrees with the input at entry from `i` to the end of
the input. -/
def EnvG.InputFrame (A : Array UInt8) (i : Nat) : Prop :=
  e.ib = e.ob → A.size = e.A0.size ∧
    ∀ k, i ≤ k → k < e.i0 + e.sm0.avail_in.toNat → A[k]? = e.IN[k]?

end EnvSection
section MatchSection

/-- The offset of `beg` in the output block: `next_out - (start - avail_out)`. -/
def EnvG.bg {α : Bool} (e : EnvG α) : Nat := e.o0 - (e.start.toNat - e.sm0.avail_out.toNat)

/-- The context `c` that `inflate_fast` builds is the one the situation `e` describes. -/
structure CtxOK {α : Bool} (e : EnvG α) (c : Ctx) : Prop where
  strm : c.strm = e.strm
  state : c.state = some (InflateStateRef.tab e.stid)
  last : c.last = .ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5)
  beg : c.beg = .ref (BRef.blk e.ob) e.bg
  end_ : c.end_ = .ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257)
  wsize : c.wsize = e.s0.wsize
  whave : c.whave = e.s0.whave
  wnext : c.wnext = e.s0.wnext
  window : c.window = e.s0.window
  lcode : c.lcode = e.s0.lencode
  dcode : c.dcode = e.s0.distcode
  lmask : c.lmask = ((1 : UInt32) <<< e.s0.lenbits) - 1
  dmask : c.dmask = ((1 : UInt32) <<< e.s0.distbits) - 1

/-- The match result of the situation: `matchArr` over the window array, or `matchArrA` when the
window is the output block. -/
def EnvG.mArr : {α : Bool} → EnvG α → Nat → Nat → Nat → Nat → Array UInt8 → Array UInt8
  | false, e, bg, o, dist, len, A => matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W bg o dist len A
  | true, e, bg, o, dist, len, A =>
    if e.wb = e.ob then matchArrA e.s0.wsize.toNat e.woff bg o dist len A
    else matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W bg o dist len A

end MatchSection
section LocalsSection
variable {α : Bool} (e : EnvG α)

/-- The locals are consistent with the situation: `in` is at offset `i` of the input block, `out` at offset `o` of the
output block, both within their windows; the bit buffer holds `bits ≤ 30` bits; and the bits read so far account for
the bytes consumed (`bits ≤ bits_at_entry + 8 * (i - i0)`). -/
structure LS (l : L) (i o : Nat) : Prop where
  hin : l.in_ = .ref (BRef.blk e.ib) i
  hout : l.out = .ref (BRef.blk e.ob) o
  hi0 : e.i0 ≤ i
  hi1 : i ≤ e.i0 + e.sm0.avail_in.toNat
  ho0 : e.o0 ≤ o
  hb : l.bits.toNat ≤ 30
  hH : l.hold.toNat < 2 ^ l.bits.toNat
  hacc : l.bits.toNat + 8 * e.i0 ≤ e.s0.bits.toNat + 8 * i

/-- The bits of the input bytes from offset `i` to the end of the input range. -/
def inBits (i : Nat) : List Bool :=
  bytesToBits ((e.IN.toList.drop i).take (e.i0 + e.sm0.avail_in.toNat - i))

/-- The bit sequence of a state: the bits of the buffer, then the bits of the unread input. -/
def Sg (H b i : Nat) : List Bool := bitsOfNat H b ++ inBits e i

end LocalsSection

/-- The entry on which a distance lookup ends and the number of bits it consumes, for the hold value `H` and the root
index `kidx`: a root leaf, or a root link and a leaf of its second level. -/
def DistLook {α : Bool} (e : EnvG α) (H kidx : Nat) (E : Code) (cb : Nat) : Prop :=
  (e.DCA.getD (e.od + kidx) default = E ∧ cb = E.bits.toNat ∧ ¬ DistLink E) ∨
  (∃ E0 j, e.DCA.getD (e.od + kidx) default = E0 ∧ DistLink E0 ∧ j < 2 ^ E0.op.toNat ∧
     j = (H / 2 ^ E0.bits.toNat) % 2 ^ E0.op.toNat ∧ e.DCA.getD (e.od + E0.val.toNat + j) default = E ∧
     cb = E0.bits.toNat + E.bits.toNat ∧ E0.bits.toNat + E.bits.toNat ≤ 15 ∧ ¬ DistLink E)

/-- How a distance-table entry is treated by `dodist`. -/
abbrev DistClass {α : Bool} (e : EnvG α) (E : Code) : Prop :=
  (E.op &&& 16 ≠ 0 ∧ (E.op &&& 15).toNat ≤ 13 ∧ 1 ≤ E.val.toNat) ∨
  (E.op &&& 16 = 0 ∧ E.op &&& 64 = 0 ∧ 1 ≤ E.op.toNat ∧ E.op.toNat ≤ 15 ∧ e.od + E.val.toNat + 2 ^ E.op.toNat ≤ e.DCA.size) ∨
  (E.op &&& 16 = 0 ∧ E.op &&& 64 ≠ 0)

/-- A distance block that ended (no link): a match of length `len` was copied, or an error was found. `S` is the bit
stream after the code of the distance symbol. -/
def DistEnd {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32) (S : List Bool) (i o len : Nat) (E : Code) (l' : L)
    (h' : Heap) : Prop :=
  ¬ DistLink E ∧ l'.againD = false ∧
  ((∃ i' xv rest, i ≤ i' ∧ i' ≤ i + 2 ∧ readBits (E.op &&& 15).toNat S = some (xv, rest) ∧
      l'.broke = false ∧ LS e l' i' (o + len) ∧ Sg e l'.hold.toNat l'.bits.toNat i' = rest ∧
      h' = e.heap (e.mArr e.bg o (E.val.toNat + xv) len A) msg m) ∨
   (∃ i' p, i ≤ i' ∧ i' ≤ i + 2 ∧ l'.broke = true ∧ LS e l' i' o ∧ h' = e.heap A p BAD))

/-- What follows the refill: the stream, and the lookup and the end of the distance block. -/
def RefillPost {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32) (S : List Bool) (i o len : Nat)
    (l' : L) (h' : Heap) : Prop :=
  ∃ i3 H3 b3 E cb, i ≤ i3 ∧ i3 ≤ i + 2 ∧ Sg e H3 b3 i3 = S ∧ H3 < 2 ^ b3 ∧ 15 ≤ b3 ∧ b3 ≤ 30 ∧ cb ≤ 15 ∧
    DistLook e H3 (H3 % 2 ^ e.s0.distbits.toNat) E cb ∧ DistEnd e A msg m (S.drop cb) i3 o len E l' h'

end InffastOld.Proofs

/-! ### Old `Spec/InflateFast.lean` -/

namespace InffastOld.Spec
open C Zlib.Inffast
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec

/-- The loop's six-byte and 258-byte margins, and the existing concrete heap/table context.
`A` is the current output array, with its original allocation size. No function contract occurs
in this precondition. -/
structure StepPre {α : Bool} (e : Proofs.EnvG α) (c : Ctx) (A : Array UInt8) (l : L) (i o : Nat) : Prop where
  context : Proofs.CtxOK e c
  locals : Proofs.LS e l i o
  outputSize : A.size = e.A0.size
  inputRoom : i + 6 ≤ e.i0 + e.sm0.avail_in.toNat
  outputRoom : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat
  notStopped : l.broke = false
  /-- When input and output share one block, `A` still holds the unread input. -/
  inputFrame : e.InputFrame A i

/-- One actual body execution reads at most six bytes and writes at most 258 bytes. A continuing
iteration writes at least one byte. Only the newly written output interval and the stream's
message/state mode may change; table storage, input and other allocations are framed by `heap`.
This is a safety/progress contract, not the still-required Huffman-format refinement. -/
def StepPost {α : Bool} (e : Proofs.EnvG α) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (i o : Nat) (l' : L) (h' : Heap) : Prop :=
  ∃ i' o' A' msg' mode',
    Proofs.LS e l' i' o' ∧
    i ≤ i' ∧ i' ≤ i + 6 ∧ o ≤ o' ∧ o' ≤ o + 258 ∧
    A'.size = A.size ∧ h' = e.heap A' msg' mode' ∧ l'.againL = false ∧
    (∀ j, (j < o ∨ o' ≤ j) → A'[j]? = A[j]?) ∧
    (l'.broke = false → o < o' ∧ msg' = msg ∧ mode' = mode) ∧
    (l'.broke = true → mode' = TYPE ∨ mode' = BAD)

/-- Safety and progress of the actual fast body on every concrete permitted state. -/
def Goal.step_safe : Prop :=
  ∀ (e : Proofs.Env) (c : Ctx) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
      (l : L) (i o : Nat),
    StepPre e c A l i o →
    ∃ l' h', C.run (inflate_fast_body c l) (e.heap A msg mode) = .ok (l', h') ∧
      StepPost e A msg mode i o l' h'

/-- The complete fast call restores normalized bits and exact remaining input/output counts.
Only the produced output interval, stream buffer fields/message, and state bits/mode change.
The internal `Env` table predicates must be established by the main decoder; they do not
assert RFC decoding for arbitrary safe tables. -/
def FastPost {α : Bool} (e : Proofs.EnvG α) (after : Heap) : Prop :=
  ∃ (inputUsed outputUsed bufferedBytes : Nat) (bytes : Array UInt8) (msg : BPtr)
    (mode bits : UInt32) (hold : UInt64),
    inputUsed + bufferedBytes ≤ e.sm0.avail_in.toNat ∧ bufferedBytes ≤ 3 ∧
    outputUsed ≤ e.sm0.avail_out.toNat ∧
    bytes.size = e.A0.size ∧ bits.toNat < 8 ∧ hold.toNat < 2 ^ bits.toNat ∧
    after = e.r.put
      { e.h0 with bytes := upd e.h0.bytes e.ob (some bytes), istates := upd e.h0.istates e.stid (some { e.s0 with mode, bits, hold }) }
      { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + inputUsed), next_out := .ref (.blk e.ob) (e.o0 + outputUsed), avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - inputUsed), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - outputUsed), msg } ∧
    (∀ index, (index < e.o0 ∨ e.o0 + outputUsed ≤ index) → bytes[index]? = e.A0[index]?) ∧
    ((mode = e.s0.mode ∧ msg = e.sm0.msg) ∨ (mode = TYPE ∧ msg = e.sm0.msg) ∨ mode = BAD) ∧
    (mode ≠ TYPE → mode ≠ BAD →
      e.sm0.avail_in.toNat - inputUsed < 6 + bufferedBytes ∨
      e.sm0.avail_out.toNat - outputUsed < 258)

/-- Safety, termination, frame and exact register writeback of the actual whole fast decoder.
No body/callee contract is a hypothesis. The complete format-refinement goal is separate. -/
def Goal.fast_safe : Prop :=
  ∀ e : Proofs.Env, ∃ after,
    C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧ FastPost e after

end InffastOld.Spec

/-! ### Old `Spec/InflateFastOrigin.lean` -/

namespace InffastOld.Spec.Origin
open C Zlib.Inffast InffastOld.Proofs
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec

/-- The complete logical input remaining at entry to this fast call. -/
def initial (e : Env) : List Bool := Sg e e.s0.hold.toNat e.s0.bits.toNat e.i0

/-- Current buffered bits followed by unread bytes are the exact suffix
after consuming `used` entry bits. The accounting prevents an unrelated
suffix or guessed buffered value from satisfying the invariant. -/
structure Inv (e : Env) (hold bits input used : Nat) : Prop where
  inputLower : e.i0 ≤ input
  inputUpper : input ≤ e.i0 + e.sm0.avail_in.toNat
  normalized : hold < 2 ^ bits
  accounting : used + bits = e.s0.bits.toNat + 8 * (input - e.i0)
  stream : Sg e hold bits input = (initial e).drop used

def Goal.initial_origin : Prop :=
  ∀ e : Env, Inv e e.s0.hold.toNat e.s0.bits.toNat e.i0 0

/-- Reading the actual next byte preserves the source suffix without
consuming any logical bit. This is the data equation used by actual pull. -/
def Goal.pull_preserves_origin : Prop :=
  ∀ (e : Env) (hold bits input used : Nat),
    Inv e hold bits input used → input < e.i0 + e.sm0.avail_in.toNat →
    Inv e (hold + (e.IN.getD input 0).toNat * 2 ^ bits) (bits + 8) (input + 1) used

/-- Dropping available low bits consumes exactly that entry-stream prefix. -/
def Goal.drop_preserves_origin : Prop :=
  ∀ (e : Env) (hold bits input used count : Nat),
    Inv e hold bits input used → count ≤ bits →
    Inv e (hold / 2 ^ count) (bits - count) input (used + count)

/-- Returning unused whole bytes restores the exact same remaining input,
not merely its length. The retained low bits are the actual mask result.
The byte rollback bound follows from origin accounting and entry bits < 8. -/
def Goal.rollback_preserves_origin : Prop :=
  ∀ (e : Env) (hold bits input used : Nat),
    Inv e hold bits input used →
    let returned := bits / 8
    let residual := bits % 8
    returned ≤ input - e.i0 ∧
    Sg e (hold % 2 ^ residual) residual (input - returned) = Sg e hold bits input ∧
    Inv e (hold % 2 ^ residual) residual (input - returned) used

/-- The actual input-byte load and register updates establish the same
origin relation. The bound is the source pull helper's internal bound. -/
def Goal.actual_pull_preserves_origin : Prop :=
  ∀ (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    LS e l i o → Inv e l.hold.toNat l.bits.toNat i used →
    l.bits.toNat ≤ 22 → i < e.i0 + e.sm0.avail_in.toNat → e.InputFrame bytes i →
    ∃ l',
      C.run (pull l) (e.heap bytes msg mode) = .ok (l', e.heap bytes msg mode) ∧
      LS e l' (i + 1) o ∧ Inv e l'.hold.toNat l'.bits.toNat (i + 1) used

/-- The source shift and unsigned count subtraction consume exactly the
available low bits, with no heap effect or unchecked shift. -/
def Goal.actual_drop_preserves_origin : Prop :=
  ∀ (e : Env) (h : Heap) (l : L) (i o used : Nat) (count : UInt32),
    LS e l i o → Inv e l.hold.toNat l.bits.toNat i used →
    count.toNat ≤ l.bits.toNat →
    C.run (do
      let hold ← shr64 l.hold count.toUInt64
      pure { l with hold, bits := l.bits - count }) h = .ok (dropL l count, h) ∧
    LS e (dropL l count) i o ∧
    Inv e (dropL l count).hold.toNat (dropL l count).bits.toNat i (used + count.toNat)

/-- Actual epilogue pointer rollback and masking preserve the same exact
stream. This source prefix is checked separately from counter writeback;
the loop still has to establish origin at its exit. -/
def Goal.actual_rollback_preserves_origin : Prop :=
  ∀ (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    LS e l i o → Inv e l.hold.toNat l.bits.toNat i used → e.InputFrame bytes i →
    let returned := l.bits >>> 3
    let bits := l.bits - (returned <<< 3)
    let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
    C.run (do
      let input ← subn l.in_ returned
      let mask ← shl32 1 bits
      pure (input, l.hold &&& (mask - 1).toUInt64, bits)) (e.heap bytes msg mode) =
        .ok ((.ref (.blk e.ib) (i - l.bits.toNat / 8), hold, bits), e.heap bytes msg mode) ∧
    bits.toNat < 8 ∧
    Inv e hold.toNat bits.toNat (i - l.bits.toNat / 8) used ∧
    Sg e hold.toNat bits.toNat (i - l.bits.toNat / 8) = Sg e l.hold.toNat l.bits.toNat i

end InffastOld.Spec.Origin

/-! ### Old `Spec/InflateFastBodyOrigin.lean` -/

namespace InffastOld.Spec.BodyOrigin
open C Zlib.Inffast InffastOld.Proofs
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec

/-- Actual bit movement consumes a nonnegative exact prefix of the
original fast-call input and retains the complete existing body result.
This property alone does not assign DEFLATE meanings to the consumed bits. -/
def Goal.actual_body_preserves_origin : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    StepPre e c bytes l i o → Origin.Inv e l.hold.toNat l.bits.toNat i used →
    ∃ (l' : L) (after : Heap),
      C.run (inflate_fast_body c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      StepPost e bytes msg mode i o l' after ∧
      ∃ i' o' used',
        LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used'

end InffastOld.Spec.BodyOrigin

/-! ### Old `Spec/InflateFastCallOrigin.lean` -/

namespace InffastOld.Spec.CallOrigin
open C Zlib.Inffast InffastOld.Proofs
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec

def HasOrigin (e : Env) (after : Heap) : Prop :=
  ∃ (state : InflateState) (stream : ZStream) (input used : Nat),
    after.istates e.stid = some state ∧ e.r.get after = some stream ∧
    stream.next_in = .ref (.blk e.ib) input ∧
    input + stream.avail_in.toNat = e.i0 + e.sm0.avail_in.toNat ∧
    Origin.Inv e state.hold.toNat state.bits.toNat input used

/-- The actual whole call preserves the source suffix through every
body and rollback, retaining its full existing safety/frame result.
The actual body-origin theorem must be proved, not taken as a premise. -/
def Goal.actual_fast_preserves_origin : Prop :=
  ∀ e : Env, ∃ after,
    C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧
    FastPost e after ∧ HasOrigin e after

end InffastOld.Spec.CallOrigin

/-! ### Old `Spec/InflateFastLengthSemantics.lean` -/

namespace InffastOld.Spec.LengthSemantics
open C Zlib.Inffast InffastOld.Proofs
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec

/-- The final entry selected by the actual fast root/link branch order.
The second index uses the hold value after dropping the root code bits. -/
def Look (e : Env) (hold index : Nat) (entry : Code) (consumed : Nat) : Prop :=
  (e.LCA.getD (e.ol + index) default = entry ∧
    consumed = entry.bits.toNat ∧ ¬ LenLink entry) ∨
  (∃ first next,
    e.LCA.getD (e.ol + index) default = first ∧ LenLink first ∧
    next < 2 ^ first.op.toNat ∧
    next = (hold / 2 ^ first.bits.toNat) % 2 ^ first.op.toNat ∧
    e.LCA.getD (e.ol + first.val.toNat + next) default = entry ∧
    consumed = first.bits.toNat + entry.bits.toNat ∧
    first.bits.toNat + entry.bits.toNat ≤ 15 ∧ ¬ LenLink entry)

/-- A selected fast leaf has the independent symbol meaning and exact
code length, or rejects every future extension. This includes reserved
symbols and incomplete-table padding. It does not assume valid input or
assert that the main decoder has established the table predicates. -/
def Goal.length_lookup_matches_format : Prop :=
  ∀ (e : Env) (hold bits input tableUsed : Nat) (lens : List Nat)
    (entry : Code) (consumed : Nat),
    DecodeTableInvariant.Inv LENS e.LCA e.ol e.s0.lenbits.toNat tableUsed lens →
    DecodeTableStability.StableQuery LENS e.LCA e.ol e.s0.lenbits.toNat →
    FastTableFlags.QueryCompatible LENS e.LCA e.ol e.s0.lenbits.toNat →
    hold < 2 ^ bits → 15 ≤ bits →
    Look e hold (hold % 2 ^ e.s0.lenbits.toNat) entry consumed →
    let stream := Sg e hold bits input
    DecodeSemantics.tableRead LENS e.LCA e.ol e.s0.lenbits.toNat stream =
      some (entry, consumed) ∧
    1 ≤ consumed ∧ consumed ≤ 15 ∧ LenLeaf 0 entry ∧
    ((¬ FastTableFlags.FastLeafAccepted LENS entry ∧
      ∀ more : List Bool,
        ¬ ∃ (symbol : Nat) (rest : List Bool),
          ZlibF.Spec.decodeSym lens (stream ++ more) = some (symbol, rest) ∧ symbol ≤ 285) ∨
     (FastTableFlags.FastLeafAccepted LENS entry ∧
      ∃ symbol, symbol ≤ 285 ∧ DecodeSemantics.SymbolEntry LENS symbol entry ∧
        consumed = lens.getD symbol 0 ∧
        ZlibF.Spec.decodeSym lens stream = some (symbol, stream.drop consumed) ∧
        ∀ more : List Bool,
          ZlibF.Spec.decodeSym lens (stream ++ more) =
            some (symbol, stream.drop consumed ++ more)))

end InffastOld.Spec.LengthSemantics

/-! ### Old `Spec/InflateFastLengthTrace.lean` -/

namespace InffastOld.Spec.LengthTrace
open C Zlib.Inffast InffastOld.Proofs ZlibF.Spec
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec

/-- The two actual pre-lookup pulls, when needed, expressed with the
existing register-update function. No output or table storage changes. -/
def ready (e : Env) (l : L) (input : Nat) : L × Nat :=
  if l.bits < 15 then
    let first := pullL l (e.IN.getD input 0) (.ref (.blk e.ib) (input + 1))
    (pullL first (e.IN.getD (input + 1) 0) (.ref (.blk e.ib) (input + 2)), input + 2)
  else (l, input)

/-- The source branches after dropping the selected literal/length code.
The length branch retains actual extra-bit reading, refill and distance
lookup/copy results. Symbol meaning is supplied by the separate format
bridge, and saved-window provenance remains an enclosing invariant. -/
def End (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (remaining : List Bool) (input output : Nat) (entry : Code)
    (l' : L) (after : Heap) : Prop :=
  ¬ LenLink entry ∧ l'.againL = false ∧
  ((entry.op = 0 ∧ l'.broke = false ∧ LS e l' input (output + 1) ∧
      Sg e l'.hold.toNat l'.bits.toNat input = remaining ∧
      after = e.heap (bytes.set! output entry.val.toUInt8) msg mode) ∨
   (entry.op ≠ 0 ∧ entry.op &&& 16 ≠ 0 ∧
      ∃ input' extra rest,
        input ≤ input' ∧ input' ≤ input + 1 ∧
        readBits (entry.op &&& 15).toNat remaining = some (extra, rest) ∧
        RefillPost e bytes msg mode rest input' output (entry.val.toNat + extra) l' after) ∨
   (entry.op ≠ 0 ∧ entry.op &&& 16 = 0 ∧ entry.op &&& 64 ≠ 0 ∧
      entry.op &&& 32 ≠ 0 ∧ l'.broke = true ∧ LS e l' input output ∧
      Sg e l'.hold.toNat l'.bits.toNat input = remaining ∧
      after = e.heap bytes msg TYPE) ∨
   (entry.op ≠ 0 ∧ entry.op &&& 16 = 0 ∧ entry.op &&& 64 ≠ 0 ∧
      entry.op &&& 32 = 0 ∧ l'.broke = true ∧ LS e l' input output ∧
      Sg e l'.hold.toNat l'.bits.toNat input = remaining ∧
      ∃ errorMsg, after = e.heap bytes errorMsg BAD))

/-- The actual whole body returns its original safety result and the
selected leaf's exact effects. All source exits are retained. No body or
callee contract is a hypothesis, and no format-validity assumption hides
an invalid-code exit. These are the existing internal fast-body bounds. -/
def Goal.actual_body_retains_selected_length : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (input output : Nat),
    StepPre e c bytes l input output →
    let prepared := ready e l input
    ∃ (l' : L) (after : Heap),
      C.run (inflate_fast_body c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      StepPost e bytes msg mode input output l' after ∧
      Sg e prepared.1.hold.toNat prepared.1.bits.toNat prepared.2 =
        Sg e l.hold.toNat l.bits.toNat input ∧
      ∃ entry consumed,
        consumed ≤ 15 ∧
        LengthSemantics.Look e prepared.1.hold.toNat
          (prepared.1.hold.toNat % 2 ^ e.s0.lenbits.toNat) entry consumed ∧
        End e bytes msg mode
          ((Sg e prepared.1.hold.toNat prepared.1.bits.toNat prepared.2).drop consumed)
          prepared.2 output entry l' after

end InffastOld.Spec.LengthTrace

/-! ### Old `Spec/InflateFastMatchHistory.lean` -/

namespace InffastOld.Spec.MatchHistory
open C Zlib.Inffast InffastOld.Proofs ZlibF.Math.LZ77Copy
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec

/-- The saved bytes in chronological order at the window's actual base
offset. No default array access may be selected when the window is used. -/
def saved (window : Array UInt8) (ws wn wh woff : Nat) : List UInt8 :=
  (List.range wh).map fun j =>
    window.getD (woff + Zlib.Inflate.Spec.ringSlot ws wn wh j) 0

/-- All physical branches of the fast array result implement the same
independent match, including wraparound and overlap into current output.
An unused window need not have backing storage. -/
def Goal.match_array_refines_lz77 : Prop :=
  ∀ (window bytes : Array UInt8) (ws wn wh woff bg o dist len : Nat),
    wh ≤ ws → wn ≤ ws →
    (wh ≠ 0 → woff + ws ≤ window.size) →
    bg ≤ o → o + len ≤ bytes.size → 0 < dist →
    dist ≤ wh + (o - bg) →
    writtenBytes (matchArr ws wn woff window bg o dist len bytes)
      (o + len) (o - bg + len) =
      ZlibF.Spec.copyBack (saved window ws wn wh woff) dist len
        (writtenBytes bytes o (o - bg))

/-- Actual source copying is a clean too-far rejection or the independent
match on saved bytes and current output. The complete old input/bit/link
frame is retained. This starts at the internal copyMatch cut point. -/
def Goal.actual_copy_match_refines_lz77 : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (o : Nat),
    CtxOK e c →
    l.out = .ref (.blk e.ob) o → e.bg ≤ o →
    l.op.toNat = o - e.bg →
    1 ≤ l.dist.toNat → 3 ≤ l.len.toNat →
    o + l.len.toNat ≤ bytes.size → l.broke = false →
    let history := saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff
    let current := writtenBytes bytes o (o - e.bg)
    if history.length + current.length < l.dist.toNat then
      ∃ (l' : L) (after : Heap) (p : BPtr),
        C.run (copyMatch c l) (e.heap bytes msg mode) = .ok (l', after) ∧
        l'.in_ = l.in_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧
        l'.againL = l.againL ∧ l'.againD = l.againD ∧
        l'.broke = true ∧ l'.out = l.out ∧ after = e.heap bytes p BAD
    else
      ∃ (l' : L) (after : Heap),
        C.run (copyMatch c l) (e.heap bytes msg mode) = .ok (l', after) ∧
        l'.in_ = l.in_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧
        l'.againL = l.againL ∧ l'.againD = l.againD ∧
        l'.broke = false ∧ l'.out = .ref (.blk e.ob) (o + l.len.toNat) ∧
        let result := matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o
          l.dist.toNat l.len.toNat bytes
        after = e.heap result msg mode ∧
        writtenBytes result (o + l.len.toNat) (o - e.bg + l.len.toNat) =
          ZlibF.Spec.copyBack history l.dist.toNat l.len.toNat current

end InffastOld.Spec.MatchHistory

/-! ### Old `Spec/InflateFastDistanceOrigin.lean` -/

namespace InffastOld.Spec.DistanceOrigin
open C Zlib.Inffast InffastOld.Proofs
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec

/-- The complete actual distance sub-block retains its existing result
and the exact source suffix on every exit. These are internal data
preconditions, not an assumed distance-callee contract. -/
def Goal.actual_distance_block_preserves_origin : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    CtxOK e c → LS e l i o →
    e.o0 + e.sm0.avail_out.toNat ≤ bytes.size →
    o + 258 ≤ e.o0 + e.sm0.avail_out.toNat → bytes.size < 2 ^ 63 →
    l.broke = false → (3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) →
    15 ≤ l.bits.toNat →
    (i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
      (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat)) →
    Origin.Inv e l.hold.toNat l.bits.toNat i used → e.InputFrame bytes i →
    ∃ (l' : L) (after : Heap),
      C.run (dolenDist c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      (∃ entry consumed,
        consumed ≤ 15 ∧
        DistLook e l.hold.toNat (l.hold.toNat % 2 ^ e.s0.distbits.toNat) entry consumed ∧
        DistEnd e bytes msg mode ((Sg e l.hold.toNat l.bits.toNat i).drop consumed)
          i o l.len.toNat entry l' after) ∧
      ∃ i' o' used',
        LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used'

end InffastOld.Spec.DistanceOrigin

/-! ### Old `Spec/InflateFastDistanceSemantics.lean` -/

namespace InffastOld.Spec.DistanceSemantics
open C Zlib.Inffast InffastOld.Proofs
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec

/-- A selected fast leaf has the exact query, consumed code length and
independent symbol meaning, or rejects every future extension. This is
a lookup-data bridge, not complete extra-bit or copy execution. -/
def Goal.distance_lookup_matches_format : Prop :=
  ∀ (e : Env) (hold bits input tableUsed : Nat) (lens : List Nat)
    (entry : Code) (consumed : Nat),
    DecodeTableInvariant.Inv DISTS e.DCA e.od e.s0.distbits.toNat tableUsed lens →
    DecodeTableStability.StableQuery DISTS e.DCA e.od e.s0.distbits.toNat →
    FastTableFlags.QueryCompatible DISTS e.DCA e.od e.s0.distbits.toNat →
    hold < 2 ^ bits → 15 ≤ bits →
    DistLook e hold (hold % 2 ^ e.s0.distbits.toNat) entry consumed →
    let stream := Sg e hold bits input
    DecodeSemantics.tableRead DISTS e.DCA e.od e.s0.distbits.toNat stream = some (entry, consumed) ∧
    1 ≤ consumed ∧ consumed ≤ 15 ∧ DistLeaf 0 entry ∧
    ((entry.op &&& 16 = 0 ∧
      ∀ more : List Bool,
        ¬ ∃ (symbol : Nat) (rest : List Bool),
          ZlibF.Spec.decodeSym lens (stream ++ more) = some (symbol, rest) ∧ symbol ≤ 29) ∨
     (entry.op &&& 16 ≠ 0 ∧
      ∃ symbol, symbol ≤ 29 ∧ DecodeSemantics.SymbolEntry DISTS symbol entry ∧
        consumed = lens.getD symbol 0 ∧
        ZlibF.Spec.decodeSym lens stream = some (symbol, stream.drop consumed) ∧
        ∀ more : List Bool,
          ZlibF.Spec.decodeSym lens (stream ++ more) =
            some (symbol, stream.drop consumed ++ more)))

end InffastOld.Spec.DistanceSemantics

/-! ### Old `Spec/InflateFastDistanceResult.lean` -/

namespace InffastOld.Spec.DistanceResult
open C Zlib.Inffast InffastOld.Proofs ZlibF.Spec
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec
open ZlibF.Math.LZ77Copy

/-- Physical copying after the distance extras have been consumed. Both
branches preserve the exact remaining input, including a too-far error. -/
def CopyOutcome (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (output len distance : Nat) (l' : L) (after : Heap) : Prop :=
  let history := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
    e.s0.whave.toNat e.woff
  let current := writtenBytes bytes output (output - e.bg)
  if history.length + current.length < distance then
    ∃ input' errorMsg,
      l'.broke = true ∧ LS e l' input' output ∧
      Sg e l'.hold.toNat l'.bits.toNat input' = source ∧
      after = e.heap bytes errorMsg BAD
  else
    ∃ input',
      let result := matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg output
        distance len bytes
      l'.broke = false ∧ LS e l' input' (output + len) ∧
      Sg e l'.hold.toNat l'.bits.toNat input' = source ∧
      after = e.heap result msg mode ∧
      writtenBytes result (output + len) (output - e.bg + len) =
        copyBack history distance len current

/-- Physical leaf dispatch, before relating the selected entry to an
independent symbol. This is a result to prove about the actual source,
not a callee contract assumed by the distance-block goal. -/
def PhysicalOutcome (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (output len : Nat) (entry : Code) (consumed : Nat)
    (l' : L) (after : Heap) : Prop :=
  (entry.op &&& 16 = 0 ∧
    ∃ input' errorMsg,
      l'.broke = true ∧ LS e l' input' output ∧
      Sg e l'.hold.toNat l'.bits.toNat input' = source.drop consumed ∧
      after = e.heap bytes errorMsg BAD) ∨
  (entry.op &&& 16 ≠ 0 ∧
    ∃ extra rest,
      readBits (entry.op &&& 15).toNat (source.drop consumed) = some (extra, rest) ∧
      CopyOutcome e bytes msg mode rest output len (entry.val.toNat + extra) l' after)

/-- The complete distance result, including the exact remaining source
bits on both errors. A successful copy equals independent bytewise LZ77
copying on the actual saved window and current output. -/
def Outcome (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (input output : Nat) (lens : List Nat) (entry : Code) (consumed : Nat)
    (l' : L) (after : Heap) : Prop :=
  let source := Sg e l.hold.toNat l.bits.toNat input
  let history := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
    e.s0.whave.toNat e.woff
  let current := writtenBytes bytes output (output - e.bg)
  (entry.op &&& 16 = 0 ∧
    (∀ more : List Bool,
      ¬ ∃ (symbol : Nat) (rest : List Bool),
        decodeSym lens (source ++ more) = some (symbol, rest) ∧ symbol ≤ 29) ∧
    ∃ input' errorMsg,
      l'.broke = true ∧ LS e l' input' output ∧
      Sg e l'.hold.toNat l'.bits.toNat input' = source.drop consumed ∧
      after = e.heap bytes errorMsg BAD) ∨
  (entry.op &&& 16 ≠ 0 ∧
    ∃ symbol extra codeRest rest,
      symbol ≤ 29 ∧ DecodeSemantics.SymbolEntry DISTS symbol entry ∧
      consumed = lens.getD symbol 0 ∧
      decodeSym lens source = some (symbol, codeRest) ∧
      readBits (distExtras.getD symbol 0) codeRest = some (extra, rest) ∧
      let distance := distBases.getD symbol 0 + extra
      if history.length + current.length < distance then
        ∃ input' errorMsg,
          l'.broke = true ∧ LS e l' input' output ∧
          Sg e l'.hold.toNat l'.bits.toNat input' = rest ∧
          after = e.heap bytes errorMsg BAD
      else
        ∃ input',
          let result := matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg output
            distance l.len.toNat bytes
          l'.broke = false ∧ LS e l' input' (output + l.len.toNat) ∧
          Sg e l'.hold.toNat l'.bits.toNat input' = rest ∧
          after = e.heap result msg mode ∧
          writtenBytes result (output + l.len.toNat) (output - e.bg + l.len.toNat) =
            copyBack history distance l.len.toNat current)

/-- Every actual distance-block exit retains the old execution result and
has its independent symbol/copy meaning. Internal table data facts must
still be established by actual construction. No callee contract or input
validity is a hypothesis. The physical domain is the existing distance
block's safety domain, not a restriction added to the public API. -/
def Goal.actual_distance_refines_lz77 : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (input output tableUsed : Nat) (lens : List Nat),
    CtxOK e c → LS e l input output →
    e.o0 + e.sm0.avail_out.toNat ≤ bytes.size →
    output + 258 ≤ e.o0 + e.sm0.avail_out.toNat → bytes.size < 2 ^ 63 →
    l.broke = false → (3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) →
    15 ≤ l.bits.toNat →
    (input + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
      (input + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat)) →
    DecodeTableInvariant.Inv DISTS e.DCA e.od e.s0.distbits.toNat tableUsed lens →
    DecodeTableStability.StableQuery DISTS e.DCA e.od e.s0.distbits.toNat →
    FastTableFlags.QueryCompatible DISTS e.DCA e.od e.s0.distbits.toNat →
    e.InputFrame bytes input →
    ∃ (l' : L) (after : Heap) (entry : Code) (consumed : Nat),
      C.run (dolenDist c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      consumed ≤ 15 ∧
      DistLook e l.hold.toNat (l.hold.toNat % 2 ^ e.s0.distbits.toNat) entry consumed ∧
      DistEnd e bytes msg mode
        ((Sg e l.hold.toNat l.bits.toNat input).drop consumed)
        input output l.len.toNat entry l' after ∧
      Outcome e bytes msg mode l input output lens entry consumed l' after

end InffastOld.Spec.DistanceResult

/-! ### Old `Spec/InflateFastBodyToken.lean` -/

namespace InffastOld.Spec.BodyToken
open C Zlib.Inffast InffastOld.Proofs ZlibF.Spec
open Zlib.Inffast.Proofs hiding WinRel EnvG Env CtxOK LS inBits Sg DistLook DistClass DistEnd RefillPost
open Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec
open ZlibF.Math.LZ77Copy

/-- Data facts about the same actual arrays used by the fast decoder.
Actual construction and installation must establish these fields; no
translated function contract is stored here. -/
structure Tables (e : Env) (L D : List Nat) : Prop where
  lengthTable : ∃ used,
    DecodeTableInvariant.Inv LENS e.LCA e.ol e.s0.lenbits.toNat used L
  distanceTable : ∃ used,
    DecodeTableInvariant.Inv DISTS e.DCA e.od e.s0.distbits.toNat used D
  lengthStable : DecodeTableStability.StableQuery LENS e.LCA e.ol e.s0.lenbits.toNat
  distanceStable : DecodeTableStability.StableQuery DISTS e.DCA e.od e.s0.distbits.toNat
  lengthFlags : FastTableFlags.QueryCompatible LENS e.LCA e.ol e.s0.lenbits.toNat
  distanceFlags : FastTableFlags.QueryCompatible DISTS e.DCA e.od e.s0.distbits.toNat

/-- The actual distance call reached after length extras and refill.
Its physical entry state is retained so that the proved distance result
can be applied. The run equation is a conclusion, never a hypothesis
standing in for a callee's correctness theorem. -/
def DistanceEntry (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (beforeRefill output len : Nat)
    (l' : Zlib.Inffast.L) (after : Heap) : Prop :=
  ∃ (entry : Zlib.Inffast.L) (input : Nat),
    beforeRefill ≤ input ∧ input ≤ beforeRefill + 2 ∧
    LS e entry input output ∧ entry.broke = false ∧ entry.len.toNat = len ∧
    15 ≤ entry.bits.toNat ∧
    (input + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
      (input + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ entry.bits.toNat)) ∧
    Sg e entry.hold.toNat entry.bits.toNat input = source ∧
    C.run (dolenDist c entry) (e.heap bytes msg mode) = .ok (l', after)

/-- The source length tail retains its extra-bit read and the actual
distance-entry cut point. The old `RefillPost` alone loses that cut point
on errors and cannot justify applying a distance execution theorem. -/
def LengthTail (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (input output : Nat) (entry : Code)
    (l' : Zlib.Inffast.L) (after : Heap) : Prop :=
  ∃ input' extra rest,
    input ≤ input' ∧ input' ≤ input + 1 ∧
    readBits (entry.op &&& 15).toNat source = some (extra, rest) ∧
    DistanceEntry e c bytes msg mode rest input' output (entry.val.toNat + extra) l' after

/-- Strengthen the source result without changing the already proved
length trace or the public target. Only a length-base branch needs the
additional actual distance-entry equation. -/
def EndWithDistanceEntry (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (input output : Nat) (entry : Code)
    (l' : Zlib.Inffast.L) (after : Heap) : Prop :=
  LengthTrace.End e bytes msg mode source input output entry l' after ∧
  (entry.op ≠ 0 ∧ entry.op &&& 16 ≠ 0 →
    LengthTail e c bytes msg mode source input output entry l' after)

/-- The actual body emits exactly one independently decoded token, ends
the block, or rejects that token without output. The full old safety
postcondition and actual heap result are retained. Source-origin and the
across-call history invariant connect these local inputs to public runs.
This is the existing internal physical domain, not the public API goal. -/
def Goal.actual_body_refines_token : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : Zlib.Inffast.L) (input output : Nat) (L D : List Nat),
    StepPre e c bytes l input output → Tables e L D →
    ∃ (l' : Zlib.Inffast.L) (after : Heap) (input' output' : Nat)
      (result : Array UInt8) (resultMsg : BPtr) (resultMode : UInt32),
      C.run (inflate_fast_body c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      StepPost e bytes msg mode input output l' after ∧
      LS e l' input' output' ∧ result.size = bytes.size ∧
      after = e.heap result resultMsg resultMode ∧
      let history := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
        e.s0.whave.toNat e.woff
      let current := writtenBytes bytes output (output - e.bg)
      let produced := writtenBytes result output' (output' - e.bg)
      let source := Sg e l.hold.toNat l.bits.toNat input
      let rest := Sg e l'.hold.toNat l'.bits.toNat input'
      ((l'.broke = false ∧ Token.Step L D history current source rest produced false) ∨
       (l'.broke = true ∧ resultMode = TYPE ∧
         Token.Step L D history current source rest produced true) ∨
       (l'.broke = true ∧ resultMode = BAD ∧ produced = current ∧
         Token.Rejected L D history current source))

end InffastOld.Spec.BodyToken

/-! ## From an old situation to a new one -/

namespace InffastOld
open C Zlib.Inffast
set_option autoImplicit false

/-- The window relation of a heap block output is that of its byte view. -/
theorem winRel_new {α : Bool} {wb ob : Nat} {wn : UInt32} {P : Prop}
    (rel : Proofs.WinRel α wb ob wn P) : Zlib.Inffast.Proofs.WinRel α wb (BRef.blk ob) wn P := by
  cases α with
  | false => exact fun same => rel (BRef.blk.inj same)
  | true => exact fun same => rel (BRef.blk.inj same)

/-- An old situation, with input and output in heap blocks, as a new one: the block `b` is the
byte view `BRef.blk b`. Every other field is the same. -/
def toNew {α : Bool} (e : Proofs.EnvG α) : Zlib.Inffast.Proofs.EnvG α where
  h0 := e.h0
  strm := e.strm
  start := e.start
  r := e.r
  sm0 := e.sm0
  stid := e.stid
  s0 := e.s0
  hstrm := e.hstrm
  hsm := e.hsm
  hrw := e.hrw
  hstate := e.hstate
  hs0 := e.hs0
  ib := BRef.blk e.ib
  i0 := e.i0
  IN := e.IN
  hnin := e.hnin
  hIN := e.hIN
  hai := e.hai
  hINsz := e.hINsz
  hINbig := e.hINbig
  ob := BRef.blk e.ob
  o0 := e.o0
  A0 := e.A0
  hnout := e.hnout
  hA0 := e.hA0
  hro := e.hro
  hao := e.hao
  hAsz := e.hAsz
  hAbig := e.hAbig
  hstart := e.hstart
  hbeg := e.hbeg
  hsep := e.hsep.imp (fun ne same => ne (BRef.blk.inj same))
    (fun both => ⟨congrArg BRef.blk both.1, both.2⟩)
  hbits := e.hbits
  hhold := e.hhold
  hsane := e.hsane
  hws := e.hws
  hwh := e.hwh
  hwn := e.hwn
  wb := e.wb
  woff := e.woff
  W := e.W
  hwin := fun nonzero =>
    ⟨(e.hwin nonzero).1, winRel_new (e.hwin nonzero).2.1, (e.hwin nonzero).2.2.1,
      (e.hwin nonzero).2.2.2⟩
  rl := e.rl
  ol := e.ol
  LCA := e.LCA
  hlc := e.hlc
  hLCA := e.hLCA
  hlt := e.hlt
  rd := e.rd
  od := e.od
  DCA := e.DCA
  hdc := e.hdc
  hDCA := e.hDCA
  hdt := e.hdt

/-! ## Each old definition is the new one on `toNew` -/

section Bridge
variable {e : Proofs.Env}

theorem inputFrame_iff {A : Array UInt8} {i : Nat} :
    Proofs.EnvG.InputFrame e A i ↔ Zlib.Inffast.Proofs.EnvG.InputFrame (toNew e) A i := by
  constructor
  · intro frame same
    exact frame (BRef.blk.inj same)
  · intro frame same
    exact frame (congrArg BRef.blk same)

theorem ctx_iff {c : Ctx} : Proofs.CtxOK e c ↔ Zlib.Inffast.Proofs.CtxOK (toNew e) c :=
  ⟨fun h => ⟨h.strm, h.state, h.last, h.beg, h.end_, h.wsize, h.whave, h.wnext, h.window, h.lcode,
      h.dcode, h.lmask, h.dmask⟩,
    fun h => ⟨h.strm, h.state, h.last, h.beg, h.end_, h.wsize, h.whave, h.wnext, h.window, h.lcode,
      h.dcode, h.lmask, h.dmask⟩⟩

theorem ls_iff {l : L} {i o : Nat} : Proofs.LS e l i o ↔ Zlib.Inffast.Proofs.LS (toNew e) l i o :=
  ⟨fun h => ⟨h.hin, h.hout, h.hi0, h.hi1, h.ho0, h.hb, h.hH, h.hacc⟩,
    fun h => ⟨h.hin, h.hout, h.hi0, h.hi1, h.ho0, h.hb, h.hH, h.hacc⟩⟩

theorem inv_iff {hold bits input used : Nat} :
    Spec.Origin.Inv e hold bits input used ↔
      Zlib.Inffast.Spec.Origin.Inv (toNew e) hold bits input used :=
  ⟨fun h => ⟨h.inputLower, h.inputUpper, h.normalized, h.accounting, h.stream⟩,
    fun h => ⟨h.inputLower, h.inputUpper, h.normalized, h.accounting, h.stream⟩⟩

theorem stepPre_iff {c : Ctx} {A : Array UInt8} {l : L} {i o : Nat} :
    Spec.StepPre e c A l i o ↔ Zlib.Inffast.Spec.StepPre (toNew e) c A l i o :=
  ⟨fun h => ⟨ctx_iff.1 h.context, ls_iff.1 h.locals, h.outputSize, h.inputRoom, h.outputRoom,
      h.notStopped, inputFrame_iff.1 h.inputFrame⟩,
    fun h => ⟨ctx_iff.2 h.context, ls_iff.2 h.locals, h.outputSize, h.inputRoom, h.outputRoom,
      h.notStopped, inputFrame_iff.2 h.inputFrame⟩⟩

theorem tables_iff {Ls Ds : List Nat} :
    Spec.BodyToken.Tables e Ls Ds ↔ Zlib.Inffast.Spec.BodyToken.Tables (toNew e) Ls Ds :=
  ⟨fun h => ⟨h.lengthTable, h.distanceTable, h.lengthStable, h.distanceStable, h.lengthFlags,
      h.distanceFlags⟩,
    fun h => ⟨h.lengthTable, h.distanceTable, h.lengthStable, h.distanceStable, h.lengthFlags,
      h.distanceFlags⟩⟩

theorem distEnd_iff {A : Array UInt8} {msg : BPtr} {m : UInt32} {S : List Bool} {i o len : Nat}
    {E : Code} {l' : L} {h' : Heap} :
    Proofs.DistEnd e A msg m S i o len E l' h' ↔
      Zlib.Inffast.Proofs.DistEnd (toNew e) A msg m S i o len E l' h' := by
  unfold Proofs.DistEnd
  simp only [ls_iff]
  all_goals exact Iff.rfl

theorem refillPost_iff {A : Array UInt8} {msg : BPtr} {m : UInt32} {S : List Bool} {i o len : Nat}
    {l' : L} {h' : Heap} :
    Proofs.RefillPost e A msg m S i o len l' h' ↔
      Zlib.Inffast.Proofs.RefillPost (toNew e) A msg m S i o len l' h' := by
  unfold Proofs.RefillPost
  simp only [distEnd_iff]
  all_goals exact Iff.rfl

theorem stepPost_iff {A : Array UInt8} {msg : BPtr} {mode : UInt32} {i o : Nat} {l' : L}
    {h' : Heap} :
    Spec.StepPost e A msg mode i o l' h' ↔ Zlib.Inffast.Spec.StepPost (toNew e) A msg mode i o l' h' := by
  unfold Spec.StepPost
  simp only [ls_iff]
  all_goals exact Iff.rfl

theorem fastPost_iff {after : Heap} :
    Spec.FastPost e after ↔ Zlib.Inffast.Spec.FastPost (toNew e) after :=
  Iff.rfl

theorem hasOrigin_iff {after : Heap} :
    Spec.CallOrigin.HasOrigin e after ↔ Zlib.Inffast.Spec.CallOrigin.HasOrigin (toNew e) after := by
  unfold Spec.CallOrigin.HasOrigin
  simp only [inv_iff]
  all_goals exact Iff.rfl

theorem end_iff {A : Array UInt8} {msg : BPtr} {mode : UInt32} {remaining : List Bool}
    {input output : Nat} {entry : Code} {l' : L} {after : Heap} :
    Spec.LengthTrace.End e A msg mode remaining input output entry l' after ↔
      Zlib.Inffast.Spec.LengthTrace.End (toNew e) A msg mode remaining input output entry l' after := by
  unfold Spec.LengthTrace.End
  simp only [ls_iff, refillPost_iff]
  all_goals exact Iff.rfl

theorem outcome_iff {A : Array UInt8} {msg : BPtr} {mode : UInt32} {l : L} {input output : Nat}
    {lens : List Nat} {entry : Code} {consumed : Nat} {l' : L} {after : Heap} :
    Spec.DistanceResult.Outcome e A msg mode l input output lens entry consumed l' after ↔
      Zlib.Inffast.Spec.DistanceResult.Outcome (toNew e) A msg mode l input output lens entry
        consumed l' after := by
  unfold Spec.DistanceResult.Outcome
  simp only [ls_iff]
  all_goals exact Iff.rfl

end Bridge

/-! ## Each old goal follows from the new one -/

/-- Through `BRef.blk.inj`: the premise `StepPre` contains `InputFrame`. -/
theorem step_safe_old_of_new (g : Zlib.Inffast.Spec.Goal.step_safe) : Spec.Goal.step_safe := by
  intro e c A msg mode l i o pre
  obtain ⟨l', h', run, post⟩ := g (toNew e) c A msg mode l i o (stepPre_iff.1 pre)
  exact ⟨l', h', run, stepPost_iff.2 post⟩

/-- Definitional on `toNew` (`FastPost` is `Iff.rfl`). -/
theorem fast_safe_old_of_new (g : Zlib.Inffast.Spec.Goal.fast_safe) : Spec.Goal.fast_safe := by
  intro e
  obtain ⟨after, run, post⟩ := g (toNew e)
  exact ⟨after, run, fastPost_iff.2 post⟩

/-- Definitional on `toNew` (`FastPost`, and `HasOrigin` up to the repackaged `Origin.Inv`). -/
theorem actual_fast_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.CallOrigin.Goal.actual_fast_preserves_origin) :
    Spec.CallOrigin.Goal.actual_fast_preserves_origin := by
  intro e
  obtain ⟨after, run, post, origin⟩ := g (toNew e)
  exact ⟨after, run, fastPost_iff.2 post, hasOrigin_iff.2 origin⟩

/-- Through `BRef.blk.inj`: the premise `StepPre` contains `InputFrame`. -/
theorem actual_body_retains_selected_length_old_of_new
    (g : Zlib.Inffast.Spec.LengthTrace.Goal.actual_body_retains_selected_length) :
    Spec.LengthTrace.Goal.actual_body_retains_selected_length := by
  intro e c bytes msg mode l input output pre
  have result := g (toNew e) c bytes msg mode l input output (stepPre_iff.1 pre)
  simp only [stepPost_iff, end_iff]
  exact result

/-- The same statement: it does not depend on the situation. -/
theorem match_array_refines_lz77_old_of_new
    (g : Zlib.Inffast.Spec.MatchHistory.Goal.match_array_refines_lz77) :
    Spec.MatchHistory.Goal.match_array_refines_lz77 :=
  g

/-- Definitional on `toNew` (`CtxOK` repackaged). -/
theorem actual_copy_match_refines_lz77_old_of_new
    (g : Zlib.Inffast.Spec.MatchHistory.Goal.actual_copy_match_refines_lz77) :
    Spec.MatchHistory.Goal.actual_copy_match_refines_lz77 := by
  intro e c bytes msg mode l o context out begin op dist len room running
  exact g (toNew e) c bytes msg mode l o (ctx_iff.1 context) out begin op dist len room running

/-- Definitional on `toNew` (`Origin.Inv` repackaged). -/
theorem initial_origin_old_of_new (g : Zlib.Inffast.Spec.Origin.Goal.initial_origin) :
    Spec.Origin.Goal.initial_origin := by
  intro e
  exact inv_iff.2 (g (toNew e))

/-- Definitional on `toNew` (`Origin.Inv` repackaged). -/
theorem pull_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.Origin.Goal.pull_preserves_origin) :
    Spec.Origin.Goal.pull_preserves_origin := by
  intro e hold bits input used inv more
  exact inv_iff.2 (g (toNew e) hold bits input used (inv_iff.1 inv) more)

/-- Definitional on `toNew` (`Origin.Inv` repackaged). -/
theorem drop_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.Origin.Goal.drop_preserves_origin) :
    Spec.Origin.Goal.drop_preserves_origin := by
  intro e hold bits input used count inv le
  exact inv_iff.2 (g (toNew e) hold bits input used count (inv_iff.1 inv) le)

/-- Definitional on `toNew` (`Origin.Inv` repackaged). -/
theorem rollback_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.Origin.Goal.rollback_preserves_origin) :
    Spec.Origin.Goal.rollback_preserves_origin := by
  intro e hold bits input used inv
  obtain ⟨returned, stream, inv'⟩ := g (toNew e) hold bits input used (inv_iff.1 inv)
  exact ⟨returned, stream, inv_iff.2 inv'⟩

/-- Through `BRef.blk.inj`: the premise `InputFrame`. -/
theorem actual_pull_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.Origin.Goal.actual_pull_preserves_origin) :
    Spec.Origin.Goal.actual_pull_preserves_origin := by
  intro e bytes msg mode l i o used locals inv bound more frame
  obtain ⟨l', run, locals', inv'⟩ := g (toNew e) bytes msg mode l i o used (ls_iff.1 locals)
    (inv_iff.1 inv) bound more (inputFrame_iff.1 frame)
  exact ⟨l', run, ls_iff.2 locals', inv_iff.2 inv'⟩

/-- Definitional on `toNew` (`LS`, `Origin.Inv` repackaged). -/
theorem actual_drop_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.Origin.Goal.actual_drop_preserves_origin) :
    Spec.Origin.Goal.actual_drop_preserves_origin := by
  intro e h l i o used count locals inv le
  obtain ⟨run, locals', inv'⟩ := g (toNew e) h l i o used count (ls_iff.1 locals) (inv_iff.1 inv) le
  exact ⟨run, ls_iff.2 locals', inv_iff.2 inv'⟩

/-- Through `BRef.blk.inj`: the premise `InputFrame`. -/
theorem actual_rollback_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.Origin.Goal.actual_rollback_preserves_origin) :
    Spec.Origin.Goal.actual_rollback_preserves_origin := by
  intro e bytes msg mode l i o used locals inv frame
  obtain ⟨run, small, inv', stream⟩ := g (toNew e) bytes msg mode l i o used (ls_iff.1 locals)
    (inv_iff.1 inv) (inputFrame_iff.1 frame)
  exact ⟨run, small, inv_iff.2 inv', stream⟩

/-- Through `BRef.blk.inj`: the premise `StepPre` contains `InputFrame`. -/
theorem actual_body_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.BodyOrigin.Goal.actual_body_preserves_origin) :
    Spec.BodyOrigin.Goal.actual_body_preserves_origin := by
  intro e c bytes msg mode l i o used pre inv
  obtain ⟨l', after, run, post, i', o', used', locals, inv', le⟩ :=
    g (toNew e) c bytes msg mode l i o used (stepPre_iff.1 pre) (inv_iff.1 inv)
  exact ⟨l', after, run, stepPost_iff.2 post, i', o', used', ls_iff.2 locals, inv_iff.2 inv', le⟩

/-- Through `BRef.blk.inj`: the premise `StepPre` contains `InputFrame`. -/
theorem actual_body_refines_token_old_of_new
    (g : Zlib.Inffast.Spec.BodyToken.Goal.actual_body_refines_token) :
    Spec.BodyToken.Goal.actual_body_refines_token := by
  intro e c bytes msg mode l input output Ls Ds pre tables
  have result := g (toNew e) c bytes msg mode l input output Ls Ds (stepPre_iff.1 pre)
    (tables_iff.1 tables)
  simp only [stepPost_iff, ls_iff]
  exact result

/-- Through `BRef.blk.inj`: the premise `InputFrame`. -/
theorem actual_distance_block_preserves_origin_old_of_new
    (g : Zlib.Inffast.Spec.DistanceOrigin.Goal.actual_distance_block_preserves_origin) :
    Spec.DistanceOrigin.Goal.actual_distance_block_preserves_origin := by
  intro e c bytes msg mode l i o used context locals h1 h2 h3 h4 h5 h6 h7 inv frame
  have result := g (toNew e) c bytes msg mode l i o used (ctx_iff.1 context) (ls_iff.1 locals)
    h1 h2 h3 h4 h5 h6 h7 (inv_iff.1 inv) (inputFrame_iff.1 frame)
  simp only [distEnd_iff, ls_iff, inv_iff]
  exact result

/-- Through `BRef.blk.inj`: the premise `InputFrame`. -/
theorem actual_distance_refines_lz77_old_of_new
    (g : Zlib.Inffast.Spec.DistanceResult.Goal.actual_distance_refines_lz77) :
    Spec.DistanceResult.Goal.actual_distance_refines_lz77 := by
  intro e c bytes msg mode l input output tableUsed lens context locals h1 h2 h3 h4 h5 h6 h7
    t1 t2 t3 frame
  have result := g (toNew e) c bytes msg mode l input output tableUsed lens (ctx_iff.1 context)
    (ls_iff.1 locals) h1 h2 h3 h4 h5 h6 h7 t1 t2 t3 (inputFrame_iff.1 frame)
  simp only [distEnd_iff, outcome_iff]
  exact result

/-- Definitional on `toNew`: the text of the goal did not change, only the type of the situation. -/
theorem distance_lookup_matches_format_old_of_new
    (g : Zlib.Inffast.Spec.DistanceSemantics.Goal.distance_lookup_matches_format) :
    Spec.DistanceSemantics.Goal.distance_lookup_matches_format := by
  intro e
  exact g (toNew e)

/-- Definitional on `toNew`: the text of the goal did not change, only the type of the situation. -/
theorem length_lookup_matches_format_old_of_new
    (g : Zlib.Inffast.Spec.LengthSemantics.Goal.length_lookup_matches_format) :
    Spec.LengthSemantics.Goal.length_lookup_matches_format := by
  intro e
  exact g (toNew e)

#print axioms step_safe_old_of_new
#print axioms fast_safe_old_of_new
#print axioms actual_fast_preserves_origin_old_of_new
#print axioms actual_body_retains_selected_length_old_of_new
#print axioms match_array_refines_lz77_old_of_new
#print axioms actual_copy_match_refines_lz77_old_of_new
#print axioms initial_origin_old_of_new
#print axioms pull_preserves_origin_old_of_new
#print axioms drop_preserves_origin_old_of_new
#print axioms rollback_preserves_origin_old_of_new
#print axioms actual_pull_preserves_origin_old_of_new
#print axioms actual_drop_preserves_origin_old_of_new
#print axioms actual_rollback_preserves_origin_old_of_new
#print axioms actual_body_preserves_origin_old_of_new
#print axioms actual_body_refines_token_old_of_new
#print axioms actual_distance_block_preserves_origin_old_of_new
#print axioms actual_distance_refines_lz77_old_of_new
#print axioms distance_lookup_matches_format_old_of_new
#print axioms length_lookup_matches_format_old_of_new

end InffastOld
