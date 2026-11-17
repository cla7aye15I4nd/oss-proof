import ZlibF.Proof.«deflate.c.borrow-stable-strategies»
import ZlibF.Proof.«deflate.c.engine.fill-caller-storage»
import ZlibF.Proof.«deflate.c.engine.content-refill»

/-! # Real slow coding retains external storage and public caller buffers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Exact union of the record fields written by refill and slow coding. -/
def SlowIterationFrame (before after : DeflateState) : Prop :=
  after = { before with
    strstart := after.strstart, lookahead := after.lookahead, ins_h := after.ins_h,
    match_start := after.match_start, match_length := after.match_length,
    prev_match := after.prev_match, prev_length := after.prev_length, match_available := after.match_available,
    sym_next := after.sym_next, dyn_ltree := after.dyn_ltree, dyn_dtree := after.dyn_dtree,
    block_start := after.block_start, insert := after.insert, high_water := after.high_water, slid := after.slid }

theorem SlowIterationFrame.trans {a b c : DeflateState} (first : SlowIterationFrame a b)
    (second : SlowIterationFrame b c) : SlowIterationFrame a c := by
  unfold SlowIterationFrame at *
  rw [second, first]

theorem iteration_frame_fill {d result : DeflateState} (frame : FillRecordFrame d result) :
    SlowIterationFrame d result := by
  unfold FillRecordFrame at frame
  unfold SlowIterationFrame
  rw [frame]

theorem iteration_frame_slow {d result : DeflateState} (frame : SlowRecordFrame d result) :
    SlowIterationFrame d result := by
  unfold SlowRecordFrame at frame
  unfold SlowIterationFrame
  rw [frame]

theorem fill_owned_frame {d result : DeflateState} (frame : FillRecordFrame d result) (ds : Nat) :
    DeflateOwned ds result = DeflateOwned ds d := by
  unfold FillRecordFrame at frame
  rw [frame]
  rfl

end Zlib.Deflate.Engine.Proofs
