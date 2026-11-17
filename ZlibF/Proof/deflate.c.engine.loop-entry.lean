import ZlibF.Proof.«deflate.c.engine.slow-loop»

/-! # The outer-loop path starts from actual default initialization -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

theorem EngineStart.symbol_capacity {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (start : EngineStart h r ds z d) : d.sym_end.toNat = 49149 := by
  have hash : d.hash_size.toNat = 32768 := by rw [start.good.inv.hsize, start.hashBits]; rfl
  have lit : d.lit_bufsize.toNat = 16384 := by have size := start.good.inv.lit; omega
  rw [start.good.inv.sym.2.1, lit]

/-- Actual default entry retains caller bindings while establishing the
content boundary. Both conclusions concern its one returned heap. -/
theorem default_content_bindings {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ ContentBoundary after r h.nextBlk zf sf input 0 0 [] ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r ∧
      zf.next_in = z.next_in ∧ zf.avail_in = z.avail_in ∧ zf.next_out = z.next_out ∧ zf.avail_out = z.avail_out := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_content_boundary hf hu hg hz ha hv params alloc input
  obtain ⟨other, otherZ, otherD, otherRun, otherStart, _, _, nextIn, availIn, nextOut, availOut⟩ :=
    default_initialization_engine_bindings hf hu hg hz ha hv params alloc
  have same : other = after := congrArg Prod.snd (Except.ok.inj (otherRun.symm.trans run))
  subst other
  have sameZ : otherZ = zf := Option.some.inj (otherStart.good.live.hz.symm.trans start.good.live.hz)
  subst otherZ
  exact ⟨after, zf, sf, run, start, boundary, initial, reachable, nextIn, availIn, nextOut, availOut⟩

def loopWitnessStream : ZStream :=
  { (default : ZStream) with
    next_in := .ref .st_dist_code 0, avail_in := 300,
    next_out := .ref (.blk 1) 0, avail_out := 2 }

def loopWitnessHeap : Heap := (ZStreamRef.tab 0).put witnessHeap loopWitnessStream

end Zlib.Deflate.Engine.Proofs
