import ZlibNgF.Proof.«gzwrite.c.loop»

/-!
# The specification of `gz_comp` (`ZlibNgF`)

`GzCompSpec` states what `gz_comp(state, flush)` does on a write handle, for every `flush`:

* **Entry** (`w.gz h b = some s`, `h.streams s.strm = some z`): the invariant of the write handle (`GzInvWS`: no
  buffers yet, or the input inside `in`), or the state `GzWX` (the invariant of the flat heap, with the input inside
  `in` or a readable caller range outside the file's blocks: the large path of `gz_write`).
* **Deflate facts**: `DeflateGz` (the init and reset clauses) and a potential `ψ` with growth `Gr` that meets the
  `deflate` clause and the bound of `DeflateGz` (`DeflatePsi`; the `ψ` of `DeflateGz` itself is one).
* **Exit** (`CompPost`): the result is 0 or -1; the fields of `WFix` stay, and the buffers once they exist; a step of
  the file from the entry heap (and between the flat heaps); the file system changes only by `write` calls on the file's descriptor
  (`FdWrites`); the invariant (no buffers) or the state `GzWX` (buffers), and the invariant again when the call
  started with it; the input only moves forward (with buffers and not direct: `next_in` by the bytes consumed;
  direct: `next_in` stays; `gz_write_init` sets `next_in` to `NULL` when there is no input); on success the buffers exist, the input is consumed unless `flush` is `Z_FINISH`, and a non-direct call
  with a flush leaves room in the output (and, unless `Z_FINISH`, no pending `reset`); with `flush ≠ Z_FINISH`,
  `reset` stays or is cleared, and on success on a non-direct handle with buffers and no pending `reset` (no
  `deflateReset`) the potential `pot` of the stream does not grow (the measure of the loop of `gzsetparams`).

The entry input may lie anywhere in the `2 size` bytes of `in` (`InX`): `gzvprintf` calls `gz_comp` with `size`
bytes from `next_in`, which need not be `in`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- `fs'` is `fs` after a sequence of `write` calls on the descriptor `fd`. -/
def FdWrites (fd : Int32) (fs fs' : Fs) : Prop :=
  ∃ l : List (Array UInt8), fs' = l.foldl (fun f bs => (f.writeCall fd bs).2) fs

/-- A potential `ψ` with growth `Gr` for the `deflate` calls of the write side: the bound and the `deflate` clause of
`DeflateGz`. -/
def DeflatePsi (ψ : Int32 → C.DeflateState → Nat) (Gr : Nat) : Prop :=
  Gr ≤ 2 ^ 28 ∧
  (∀ (h : Heap) (s : StreamPtr) (sb : Nat) (st : C.DeflateState) (f : Int32), DeflateInv.DInv h s →
    DRegisteredHeader h s none → DStateOf h s sb st → ψ f st ≤ 2 ^ 48) ∧
  DeflateClause ψ Gr

/-- **What `gz_comp(state, flush)` leaves** (see the module comment), for the entry state `s` and stream `z`. -/
def CompPost (ψ : Int32 → C.DeflateState → Nat) (w : World) (h : Heap) (b : Nat) (s : GzState) (z : ZStream)
    (flush : Int32) (r : Int32) (W : World) (H : Heap) : Prop :=
  ∃ s' z', W.gz H b = some s' ∧ H.streams s.strm = some z' ∧ WFix s s' ∧
    (s.size ≠ 0 → s'.size = s.size ∧ s'.buffers = s.buffers ∧ s'.«in» = s.«in» ∧ s'.out = s.out) ∧
    GStep w h W H b [] ∧ GStep w (setZ h s.strm (flatZ z)) W (setZ H s.strm (flatZ z')) b [] ∧ FdWrites s.fd w.fs W.fs ∧
    (s'.size = 0 → GzInvWS W H (some b)) ∧ (s'.size ≠ 0 → GzWX W H b s' z') ∧
    (GzInvWS w h (some b) → GzInvWS W H (some b)) ∧
    z'.avail_in ≤ z.avail_in ∧
    (s.size ≠ 0 → s.direct = 0 → Adv z.next_in z'.next_in (z.avail_in.toNat - z'.avail_in.toNat)) ∧
    (s.direct ≠ 0 → z'.next_in = z.next_in) ∧
    (r = 0 ∨ r = -1) ∧
    (r = 0 → s'.size ≠ 0 ∧ (flush ≠ ZlibNg.Inflate.Z_FINISH → z'.avail_in = 0) ∧
      (s.direct = 0 → flush ≠ ZlibNg.Deflate.Z_NO_FLUSH → z'.avail_out ≠ 0 ∧
        (flush ≠ ZlibNg.Inflate.Z_FINISH → s'.reset = 0))) ∧
    (flush ≠ ZlibNg.Inflate.Z_FINISH → s'.reset = s.reset ∨ s'.reset = 0) ∧
    (r = 0 → flush ≠ ZlibNg.Inflate.Z_FINISH → s.size ≠ 0 → s.direct = 0 → s.reset = 0 →
      pot ψ flush s.size.toNat H s.strm ≤ pot ψ flush s.size.toNat h s.strm)

/-- **The specification of `gz_comp`.** -/
def GzCompSpec : Prop :=
  DeflateGz → ∀ (ψ : Int32 → C.DeflateState → Nat) (Gr : Nat), DeflatePsi ψ Gr →
    ∀ (w : World) (h : Heap) (b : Nat) (flush : Int32) (s : GzState) (z : ZStream),
      w.gz h b = some s → h.streams s.strm = some z → (GzInvWS w h (some b) ∨ GzWX w h b s z) →
      GSat w h (gz_comp (some b) flush) (CompPost ψ w h b s z flush)

end ZlibNgF.Proof.GzWrite
