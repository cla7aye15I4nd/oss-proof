import ZlibF.Proof.«inffast.c.base»
import ZlibF.Proof.«inffast.c.tableok»
import ZlibF.Proof.«inflate.c.byte-views»

/-!
# inffast.c: what `inflate_fast` needs of its situation

`Zlib.Inffast.Spec` states the entry conditions and the facts about the decoding tables as predicates over the heap.
`Zlib.Inffast.Proofs.Env` bundles them with the witnesses (byte views, offsets, arrays) that the proofs of the
loop use.

**Tables.** `TableSafe` is the shape that `inflate_table` gives (`proof/inftrees.md`, theorem T2) and that `lenfix`
and `distfix` have: the root table has `2^root` entries inside the array, an entry is a leaf (literal, base value,
end of block, invalid code) or a link to a second level inside the array whose entries are leaves; the number of
bits of a root entry plus that of a second-level entry is at most 15; the extra bits of a length base are at most 5 and
those of a distance base at most 13; a length base is between 3 and 258 and a distance base is at least 1.
-/


namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

/-! ### `ZStreamRef.put` leaves every table but the stream tables alone -/

theorem put_bytes (r : ZStreamRef) (h : Heap) (v : ZStream) : (r.put h v).bytes = h.bytes := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_ro (r : ZStreamRef) (h : Heap) (v : ZStream) : (r.put h v).ro = h.ro := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_istates (r : ZStreamRef) (h : Heap) (v : ZStream) : (r.put h v).istates = h.istates := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_static (r : ZStreamRef) (h : Heap) (v : ZStream) : (r.put h v).static = h.static := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_get (r : ZStreamRef) (h : Heap) (v0 v : ZStream) (hg : r.get h = some v0) :
    r.get (r.put h v) = some v := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at hg
    simp only [ZStreamRef.put, hg, ZStreamRef.get]
    exact upd_same _ _ _
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at hg
    cases hs : h.gzstates i with
    | none => simp [hs] at hg
    | some g => simp [ZStreamRef.put, ZStreamRef.get, hs]

theorem put_put (r : ZStreamRef) (h : Heap) (v0 v v' : ZStream) (hg : r.get h = some v0) :
    r.put (r.put h v) v' = r.put h v' := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at hg
    simp [ZStreamRef.put, hg, upd_upd]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at hg
    cases hs : h.gzstates i with
    | none => simp [hs] at hg
    | some g => simp [ZStreamRef.put, hs, upd_upd]

theorem put_istates_comm (r : ZStreamRef) (h : Heap) (v : ZStream) (t : Tbl (Option InflateState)) :
    ({ r.put h v with istates := t } : Heap) = r.put { h with istates := t } v := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem put_bytes_comm (r : ZStreamRef) (h : Heap) (v : ZStream) (t : Tbl (Option (Array UInt8))) :
    ({ r.put h v with bytes := t } : Heap) = r.put { h with bytes := t } v := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

/-! ### The situation -/

/-- How the window block relates to the output view. Without `alias` (every `Env`): another
view. With `alias` (`inflateBack`, whose output is the window): the output view itself is
allowed, and then `wnext = 0` and the window ends no later than the output range (`inside`). -/
@[reducible] def WinRel : Bool → Nat → BRef → UInt32 → Prop → Prop
  | false, wb, ob, _, _ => BRef.blk wb ≠ ob
  | true, wb, ob, wnext, inside => BRef.blk wb = ob → wnext = 0 ∧ inside

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
  ib : BRef
  i0 : Nat
  IN : Array UInt8
  hnin : sm0.next_in = .ref ib i0
  hIN : Space.get h0 ib = some IN
  hai : 6 ≤ sm0.avail_in.toNat
  hINsz : i0 + sm0.avail_in.toNat ≤ IN.size
  hINbig : IN.size < 2 ^ 63
  -- the output
  ob : BRef
  o0 : Nat
  A0 : Array UInt8
  hnout : sm0.next_out = .ref ob o0
  hA0 : Space.get h0 ob = some A0
  hro : Space.ro h0 ob = false
  hao : 258 ≤ sm0.avail_out.toNat
  hAsz : o0 + sm0.avail_out.toNat ≤ A0.size
  hAbig : A0.size < 2 ^ 63
  hstart : sm0.avail_out.toNat ≤ start.toNat
  hbeg : start.toNat - sm0.avail_out.toNat ≤ o0
  /-- Input and output are distinct byte views, or disjoint ranges of one view
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

/-- The heap while `inflate_fast` runs: the output view is `A`, the message of the stream is `msg` and the mode of
the state is `m`; nothing else differs from `h0`. -/
def EnvG.heap {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32) : Heap :=
  ZStreamRef.put
    (Space.put (Zlib.Inflate.Spec.setI e.h0 e.stid { e.s0 with mode := m }) e.ob A)
    e.r { e.sm0 with msg := msg }

/-- The heap of the loop before any `break`: the message and the mode are those of the entry. -/
def EnvG.hp {α : Bool} (e : EnvG α) (A : Array UInt8) : Heap := e.heap A e.sm0.msg e.s0.mode

variable {α : Bool} (e : EnvG α)

/-- A write to a byte view commutes with a write to the stream record. -/
theorem put_space_comm (r : ZStreamRef) (h : Heap) (v : ZStream) (ref : BRef) (a : Array UInt8) :
    Space.put (r.put h v) ref a = r.put (Space.put h ref a) v := by
  cases ref with
  | blk b => cases r <;> simp only [Space.put, ZStreamRef.put] <;> split <;> rfl
  | dstate_depth id =>
    cases r with
    | tab i =>
      cases hs : h.streams i <;> cases hd : h.dstates id <;> simp [Space.put, ZStreamRef.put, hs, hd]
    | in_gzstate_strm i =>
      cases hs : h.gzstates i <;> cases hd : h.dstates id <;> simp [Space.put, ZStreamRef.put, hs, hd]
  | str i => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

/-- A write to a byte view keeps every view's read-only flag. -/
theorem space_ro_put (h : Heap) (dest ref : BRef) (a : Array UInt8) :
    Space.ro (Space.put h dest a) ref = Space.ro h ref := by
  cases dest <;> simp only [Space.put]
  all_goals (try split)
  all_goals (cases ref <;> rfl)

theorem space_put_static (h : Heap) (dest : BRef) (a : Array UInt8) :
    (Space.put h dest a).static = h.static := by
  cases dest <;> simp only [Space.put]
  all_goals (try split)
  all_goals rfl

/-- The output view holds `A`; every other byte view is that of `h0`. -/
theorem EnvG.heap_get (A msg m) (ref : BRef) :
    (Space.get (e.heap A msg m) ref : Option (Array UInt8)) = Space.get (Space.put e.h0 e.ob A) ref := by
  unfold EnvG.heap
  rw [Zlib.Inflate.Proofs.byte_view_get_stream_put, Zlib.Inflate.Proofs.byte_view_put_setI, Zlib.Inflate.Proofs.byte_view_get_setI]

/-- Writing the output view of `e.heap A` gives `e.heap A'`. -/
theorem EnvG.heap_put (A A' : Array UInt8) (msg m) :
    Space.put (e.heap A msg m) e.ob A' = e.heap A' msg m := by
  unfold EnvG.heap
  rw [put_space_comm, Zlib.Inflate.Proofs.byte_view_put_put
    (by rw [Zlib.Inflate.Proofs.byte_view_get_setI]; exact e.hA0)
    (by rw [Zlib.Inflate.Proofs.byte_view_ro_setI]; exact e.hro)]

theorem EnvG.heap_ro (A msg m) : (e.heap A msg m).ro = e.h0.ro := by
  unfold EnvG.heap
  rw [put_ro]
  generalize e.ob = ob
  cases ob <;> simp only [Space.put, Zlib.Inflate.Spec.setI]
  all_goals (try split)
  all_goals rfl

theorem EnvG.heap_istates (A msg m) :
    (e.heap A msg m).istates = upd e.h0.istates e.stid (some { e.s0 with mode := m }) := by
  unfold EnvG.heap
  rw [put_istates, Zlib.Inflate.Proofs.byte_view_put_istates]
  rfl

theorem EnvG.heap_static (A msg m) : (e.heap A msg m).static = e.h0.static := by
  unfold EnvG.heap
  rw [put_static]
  generalize e.ob = ob
  cases ob <;> simp only [Space.put, Zlib.Inflate.Spec.setI]
  all_goals (try split)
  all_goals rfl

theorem EnvG.stream_get_frame (A : Array UInt8) (s : InflateState) :
    e.r.get (Space.put (Zlib.Inflate.Spec.setI e.h0 e.stid s) e.ob A) = some e.sm0 := by
  rw [Zlib.Inflate.Proofs.byte_view_put_stream]
  have hh := e.hsm
  cases hr : e.r <;> (rw [hr] at hh; simpa [ZStreamRef.get, Zlib.Inflate.Spec.setI] using hh)

/-- The stream record under the heap of the call, before the message is written. -/
theorem EnvG.base_rget (A : Array UInt8) (m : UInt32) :
    e.r.get (Space.put (Zlib.Inflate.Spec.setI e.h0 e.stid { e.s0 with mode := m }) e.ob A) = some e.sm0 := by
  rw [Zlib.Inflate.Proofs.byte_view_put_stream]
  have := e.hsm
  cases hr : e.r <;> (rw [hr] at this; simpa [ZStreamRef.get, Zlib.Inflate.Spec.setI] using this)

theorem EnvG.heap_rget (A msg m) : e.r.get (e.heap A msg m) = some { e.sm0 with msg := msg } := by
  unfold EnvG.heap
  exact put_get e.r _ e.sm0 _ (e.base_rget A m)

/-- Writing the message of the stream record. -/
theorem EnvG.heap_msg (A msg msg' m) :
    e.r.put (e.heap A msg m) { e.sm0 with msg := msg' } = e.heap A msg' m := by
  unfold EnvG.heap
  rw [put_put _ _ e.sm0 _ _ (e.base_rget A m)]

theorem setI_stream_put (r : ZStreamRef) (h : Heap) (v : ZStream) (i : Nat) (s : InflateState) :
    Zlib.Inflate.Spec.setI (r.put h v) i s = r.put (Zlib.Inflate.Spec.setI h i s) v := by
  unfold Zlib.Inflate.Spec.setI
  rw [put_istates, put_istates_comm]

theorem setI_twice (h : Heap) (i : Nat) (s s' : InflateState) :
    Zlib.Inflate.Spec.setI (Zlib.Inflate.Spec.setI h i s) i s' = Zlib.Inflate.Spec.setI h i s' := by
  unfold Zlib.Inflate.Spec.setI
  simp [upd_upd]

/-- Writing the state record with another mode. -/
theorem EnvG.heap_setI (A msg m m') :
    Zlib.Inflate.Spec.setI (e.heap A msg m) e.stid { e.s0 with mode := m' } = e.heap A msg m' := by
  unfold EnvG.heap
  rw [setI_stream_put, ← Zlib.Inflate.Proofs.byte_view_put_setI, setI_twice]

theorem EnvG.heap_bytes_ob (A msg m) : Space.get (e.heap A msg m) e.ob = some A := by
  rw [e.heap_get]
  exact Zlib.Inflate.Proofs.byte_view_get_put e.hA0 e.hro A

/-- A byte view other than the output view is that of `h0`. -/
theorem EnvG.heap_get_ne (A msg m) {ref : BRef} (hb : ref ≠ e.ob) :
    (Space.get (e.heap A msg m) ref : Option (Array UInt8)) = Space.get e.h0 ref := by
  rw [e.heap_get]
  exact Zlib.Inflate.Proofs.byte_view_get_put_ne _ hb A

/-- A heap block other than the output view is that of `h0` (the window). -/
theorem EnvG.heap_bytes_ne (A msg m) {b : Nat} (hb : BRef.blk b ≠ e.ob) :
    (e.heap A msg m).bytes b = e.h0.bytes b :=
  e.heap_get_ne A msg m hb

theorem EnvG.heap_ro_view (A msg m) (ref : BRef) :
    Space.ro (e.heap A msg m) ref = Space.ro e.h0 ref := by
  cases ref <;> simp [Space.ro, e.heap_ro]

theorem EnvG.heap_ro_ob (A msg m) : Space.ro (e.heap A msg m) e.ob = false := by
  rw [e.heap_ro_view]
  exact e.hro

/-! ### The input view

The input and the output are byte views (`BRef`): a heap block, a static string or table, or the
`depth` array of a deflate state. The input may be a range of the output view, disjoint from the
output range. The array at the input view is then the current output array; it
agrees with the input at entry on the unread input (`InputFrame`), since the
decoder writes only in the output range. -/

/-- The array at the input view while the output view holds `A`. -/
def EnvG.inArr (A : Array UInt8) : Array UInt8 := if e.ib = e.ob then A else e.IN

/-- When input and output share a block, the output array `A` has the size of
the block at entry and agrees with the input at entry from `i` to the end of
the input. -/
def EnvG.InputFrame (A : Array UInt8) (i : Nat) : Prop :=
  e.ib = e.ob → A.size = e.A0.size ∧
    ∀ k, i ≤ k → k < e.i0 + e.sm0.avail_in.toNat → A[k]? = e.IN[k]?

theorem EnvG.heap_bytes_in (A msg m) : Space.get (e.heap A msg m) e.ib = some (e.inArr A) := by
  unfold EnvG.inArr
  by_cases same : e.ib = e.ob
  · rw [if_pos same, same, e.heap_bytes_ob]
  · rw [if_neg same, e.heap_get_ne A msg m same, e.hIN]

theorem EnvG.IN_eq_A0 (same : e.ib = e.ob) : e.IN = e.A0 := by
  have a := e.hIN
  rw [same, e.hA0] at a
  exact (Option.some.inj a).symm

theorem EnvG.inArr_size {A : Array UInt8} {i : Nat} (frame : e.InputFrame A i) :
    (e.inArr A).size = e.IN.size := by
  unfold EnvG.inArr
  by_cases same : e.ib = e.ob
  · rw [if_pos same, (frame same).1, e.IN_eq_A0 same]
  · rw [if_neg same]

theorem EnvG.InputFrame.get {α : Bool} {e : EnvG α} {A : Array UInt8} {s k : Nat} (frame : e.InputFrame A s)
    (le : s ≤ k) (lt : k < e.i0 + e.sm0.avail_in.toNat) : (e.inArr A)[k]? = e.IN[k]? := by
  unfold EnvG.inArr
  by_cases same : e.ib = e.ob
  · rw [if_pos same]
    exact (frame same).2 k le lt
  · rw [if_neg same]

theorem EnvG.InputFrame.mono {α : Bool} {e : EnvG α} {A : Array UInt8} {s s' : Nat} (frame : e.InputFrame A s)
    (le : s ≤ s') : e.InputFrame A s' :=
  fun same => ⟨(frame same).1, fun k le' lt => (frame same).2 k (Nat.le_trans le le') lt⟩

/-- At entry the output array is the block itself. -/
theorem EnvG.inputFrame_entry (i : Nat) : e.InputFrame e.A0 i :=
  fun same => ⟨rfl, fun k _ _ => by rw [e.IN_eq_A0 same]⟩

/-- Writes inside the output range keep the frame. -/
theorem EnvG.InputFrame.write {α : Bool} {e : EnvG α} {A A' : Array UInt8} {s s' o o' : Nat}
    (frame : e.InputFrame A s) (le : s ≤ s') (start : e.i0 ≤ s) (lo : e.o0 ≤ o)
    (hi : o' ≤ e.o0 + e.sm0.avail_out.toNat) (size : A'.size = A.size)
    (outside : ∀ j, (j < o ∨ o' ≤ j) → A'[j]? = A[j]?) : e.InputFrame A' s' := by
  intro same
  obtain ⟨sz, agree⟩ := frame same
  refine ⟨size.trans sz, fun k le' lt => ?_⟩
  have apart : k < o ∨ o' ≤ k := by
    rcases e.hsep with ne | ⟨_, disjoint⟩
    · exact absurd same ne
    · omega
  rw [outside k apart]
  exact agree k (Nat.le_trans le le') lt

/-- An output array that agrees with the block at entry outside the written
output holds the unread input. -/
theorem EnvG.inputFrame_of_frame {A : Array UInt8} {i o : Nat} (size : A.size = e.A0.size)
    (outside : ∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?)
    (hi : o ≤ e.o0 + e.sm0.avail_out.toNat) (start : e.i0 ≤ i) : e.InputFrame A i := by
  intro same
  refine ⟨size, fun k le lt => ?_⟩
  have apart : k < e.o0 ∨ o ≤ k := by
    rcases e.hsep with ne | ⟨_, disjoint⟩
    · exact absurd same ne
    · omega
  rw [outside k apart, e.IN_eq_A0 same]

theorem EnvG.inArr_size_of {A : Array UInt8} (size : A.size = e.A0.size) :
    (e.inArr A).size = e.IN.size := by
  unfold EnvG.inArr
  by_cases same : e.ib = e.ob
  · rw [if_pos same, size, e.IN_eq_A0 same]
  · rw [if_neg same]

end Zlib.Inffast.Proofs
