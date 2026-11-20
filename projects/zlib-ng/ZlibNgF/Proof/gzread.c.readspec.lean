import ZlibNgF.Proof.«gzread.c.decomp»
import ZlibNgF.Proof.«gzread.c.lookspec»

/-!
# The specifications of `gz_fetch`, `gz_skip` and `gz_read` (`ZlibNgF`)

Statements only; the proofs are in `gzread.c.fetch` (`gz_fetch_spec`), `gzread.c.skip` (`gz_skip_spec`) and
`gzread.c.read` (`gz_read_spec`). They are shaped for the callers: `gz_skip` and `gz_read` call
`gz_fetch`; `gzungetc`, `gzgetc`, `gzgets` and `gz_read` call `gz_skip` when a seek is pending; `gzread`, `gzfread` and
`gzgetc` call `gz_read`.

* **The mid-call state** (`GzMid`): what `gz_look` leaves (`LookPost`) and what `consume_spec` and `invR_restore` take:
  the read invariant of the world with `x.have` cleared, the `x.have` bytes from `x.next` inside `out`, and `PosHave`.
  A pending skip may still sit next to buffered output (`GzRead.skip_have` may fail): `gzungetc` calls `gz_look` and
  then `gz_skip`, and `gz_skip` consumes `min(x.have, skip)` first. Every read handle is in this state (`GzInvR` with
  `x.have` cleared is a read handle again).
* **`gz_fetch`** (`gzread.c:227-272`, patch 0013) is called with `x.have == 0`; it leaves output in `out` (or none at the
  end of the input) without moving `x.pos` or `skip`. With no skip pending the result is a read handle again.
* **`gz_skip`** (`gzread.c:259-284`) is called with `skip > 0`; it restores the read invariant, keeps `x.pos + skip`, and
  on success either skipped everything or reached the end of the input with no output left.
* **`gz_read`** (`gzread.c:308-388`, patch 0013) writes at most `len` bytes into the caller's buffer and nothing else
  outside the file; it returns at most `len`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-- The state of a read handle inside a call (`LookPost`'s last clauses): the `gz_state` `s` of block `b`, the read
invariant of the world with `x.have` cleared, the `x.have` bytes from `x.next` inside the `out` buffer, and the
position bounds of the output (`PosHave`). -/
def GzMid (W : World) (H : Heap) (b : Nat) (s : GzState) : Prop :=
  W.gz H b = some s ∧
  GzInvR { W with gzs := upd W.gzs b (some { s with «have» := 0 }) } H (some b) ∧
  (s.«have» = 0 ∨ (s.size ≠ 0 ∧ ∀ c base, GzBufs H s c base →
    ∃ p, s.next = .val p ∧ Inside c base (inSize s) (inSize s + outSize s) p s.«have».toNat)) ∧
  PosHave s

/-- No more input: `eof` is set and the input buffer is empty (the test `state->eof && state->strm.avail_in == 0`). -/
def AtEnd (H : Heap) (s : GzState) : Prop :=
  s.eof ≠ 0 ∧ ∃ z, H.streams s.strm = some z ∧ z.avail_in = 0

/-- What `gz_fetch` leaves on a read handle `s` with `x.have == 0`: `-1` or `0`; a step of the call that writes nothing
outside the file and only reads the file system; a mid-call state with the same `x.pos` and `skip`; buffers kept; a
read handle when no skip was pending; and on `0`, output buffered or the end of the input. -/
def FetchPost (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  (r = -1 ∨ r = 0) ∧ GStep w h W H b [] ∧ FsRd w.fs W.fs ∧
  ∃ s', GzMid W H b s' ∧ s'.pos = s.pos ∧ s'.skip = s.skip ∧ (s.size ≠ 0 → s'.size ≠ 0) ∧
    (s.skip = 0 → GzInvR W H (some b)) ∧
    (r = 0 → s'.«have» ≠ 0 ∨ AtEnd H s')

/-- **`gz_fetch`** on a read handle with `x.have == 0`. -/
def GzFetchSpec : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (s : GzState),
    GzInvR w h (some b) → w.gz h b = some s → s.«have» = 0 →
    GSat w h (gz_fetch (some b)) (FetchPost w h b s)

/-- What `gz_skip` leaves from the mid-call state `s`: `-1` or `0`; a read handle; a step of the call that writes
nothing outside the file and only reads the file system; `x.pos + skip` kept; buffers kept; and on `0`, the skip done
or the end of the input reached with no output left. -/
def SkipPost (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  (r = -1 ∨ r = 0) ∧ GzInvR W H (some b) ∧ GStep w h W H b [] ∧ FsRd w.fs W.fs ∧
  ∃ s', W.gz H b = some s' ∧ s'.pos.toInt + s'.skip.toInt = s.pos.toInt + s.skip.toInt ∧
    (s.size ≠ 0 → s'.size ≠ 0) ∧
    (r = 0 → s'.skip = 0 ∨ (s'.«have» = 0 ∧ AtEnd H s'))

/-- **`gz_skip`** from the mid-call state with a pending skip (its callers test `skip` first). -/
def GzSkipSpec : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (s : GzState),
    GzMid w h b s → s.skip ≠ 0 →
    GSat w h (gz_skip (some b)) (SkipPost w h b s)

/-- What `gz_read` leaves: at most `len` bytes delivered; a read handle; a step of the call whose only write outside
the file is `[buf, buf + len)`; the file system only read. -/
def ReadPost (w : World) (h : Heap) (b : Nat) (buf : BPtr) (len : UInt64) (r : UInt64) (W : World) (H : Heap) :
    Prop :=
  r.toNat ≤ len.toNat ∧ GzInvR W H (some b) ∧ GStep w h W H b [(buf, len.toNat)] ∧ FsRd w.fs W.fs

/-- **`gz_read`** on a read handle, into `len` writable bytes of the caller outside the file's blocks (none needed for
`len == 0`). -/
def GzReadSpec : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (buf : BPtr) (len : UInt64),
    GzInvR w h (some b) → GzOut w h (some b) buf len.toNat →
    GSat w h (gz_read (some b) buf len) (ReadPost w h b buf len)

/-! ## `LookIdle` across the calls

Each of `gz_fetch`, `gz_skip` and `gz_read` that returns leaves `LookIdle` when it held at the call (stated on runs, so
that they combine with the specifications above by determinism). -/

/-- `gz_fetch` keeps `LookIdle`. -/
def GzFetchIdle : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap),
    GzInvR w h (some b) → LookIdle w h (some b) → w.gz h b = some s → s.«have» = 0 →
    GzRun (gz_fetch (some b)) w h r W H → LookIdle W H (some b)

/-- `gz_skip` keeps `LookIdle`. -/
def GzSkipIdle : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap),
    GzMid w h b s → LookIdle w h (some b) → s.skip ≠ 0 →
    GzRun (gz_skip (some b)) w h r W H → LookIdle W H (some b)

/-- `gz_read` keeps `LookIdle`. -/
def GzReadIdle : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (buf : BPtr) (len r : UInt64) (W : World) (H : Heap),
    GzInvR w h (some b) → LookIdle w h (some b) → GzOut w h (some b) buf len.toNat →
    GzRun (gz_read (some b) buf len) w h r W H → LookIdle W H (some b)

end ZlibNgF.Proof.GzMode
