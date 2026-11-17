import ZlibF.Proof.«deflate.c.engine.slow-boundary»
import ZlibF.Proof.«deflate.c.engine.fill-pending-call»

/-! # Pending positions retain their earlier hash-chain frontier -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

structure PendingBoundary (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin : Nat) (xs : List Symbol) : Prop extends SlowBoundary h r ds z d input origin xs where
  insert_le : d.insert.toNat ≤ d.strstart.toNat
  frontier : HeapChains h d (d.strstart.toNat - d.insert.toNat)
  ready : 3 ≤ d.lookahead.toNat → d.insert = 0

theorem heap_chains_raise {h : Heap} {d : DeflateState} {top next : Nat}
    (chains : HeapChains h d top) (ordered : top ≤ next) : HeapChains h d next := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, chains_mono H ordered (Nat.le_refl _)⟩

/-- Actual default initialization establishes both frontiers, with insert=0. -/
theorem default_initialization_pending_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ PendingBoundary after r h.nextBlk zf sf input 0 [] ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_slow_boundary hf hu hg hz ha hv params alloc input
  refine ⟨after, zf, sf, run, start, ⟨boundary, ?_, ?_, fun _ => start.insert⟩, initial, reachable⟩
  · simp [start.insert]
  · simpa only [start.insert, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using boundary.chains

open ZlibF.Spec.Public.Proofs.DeflateInit in
/-- The strengthened boundary is inhabited by an actual successful
default entry on the existing concrete caller heap. -/
theorem default_pending_boundary_witness :
    ∃ after zf sf,
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        witnessHeap = .ok (Z_OK, after) ∧
      PendingBoundary after (.tab 0) 2 zf sf (fun _ => 0) 0 [] := by
  obtain ⟨after, zf, sf, run, _, boundary, _, _⟩ :=
    default_initialization_pending_boundary (h := witnessHeap) (r := .tab 0) (z := default)
      (version := .ref (.blk 1) 0) (level := Z_DEFAULT_COMPRESSION) (p := settings 6)
      witness_fresh witness_uniq rfl (by simp [ZStreamRef.get, witnessHeap])
      ⟨Or.inl rfl, Or.inl rfl⟩ witness_version (by decide +kernel) (by intro _ _; rfl) (fun _ => 0)
  exact ⟨after, zf, sf, run, boundary⟩

end Zlib.Deflate.Engine.Proofs
