import ZlibNgF.Proof.«trees.c.init»

/-!
# The state arrays of `build_tree` on `SH` heaps (`ZlibNgF`)

`build_tree`, `gen_bitlen` and `gen_codes` touch only arrays of the `deflate_state`: the tree selected by the
descriptor (`dyn_ltree`, `dyn_dtree` or `bl_tree`), the two `uint32_t` queues `pq_leaves` / `pq_scratch` and
`bl_count`, plus the read-only static tables. On an `SH` heap each access is an access to a field of the state
record: reads leave the heap, writes replace the state by one with that array `set!`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesPrims
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.InflateInv (upd_upd)

/-! ## The tree of a descriptor -/

/-- The reference of the tree array of descriptor `t` of the state in block `b`. -/
def tRef : DescSel → Nat → CtRef
  | .l_desc, b => .dyn_ltree b
  | .d_desc, b => .dyn_dtree b
  | .bl_desc, b => .bl_tree b

/-- The tree array of descriptor `t`. -/
def tArr : DescSel → DeflateState → Array Ct
  | .l_desc, s => s.dyn_ltree
  | .d_desc, s => s.dyn_dtree
  | .bl_desc, s => s.bl_tree

/-- The state with the tree array of descriptor `t` replaced. -/
def tPut : DescSel → DeflateState → Array Ct → DeflateState
  | .l_desc, s, A => { s with dyn_ltree := A }
  | .d_desc, s, A => { s with dyn_dtree := A }
  | .bl_desc, s, A => { s with bl_tree := A }

/-- The static descriptor of `t`. -/
def tSD : DescSel → StaticDescPtr
  | .l_desc => .static_l_desc
  | .d_desc => .static_d_desc
  | .bl_desc => .static_bl_desc

@[simp] theorem tArr_tPut (t : DescSel) (s : DeflateState) (A : Array Ct) : tArr t (tPut t s A) = A := by
  cases t <;> rfl

@[simp] theorem tPut_tPut (t : DescSel) (s : DeflateState) (A B : Array Ct) :
    tPut t (tPut t s A) B = tPut t s B := by
  cases t <;> rfl

/-- The fields of the state other than the tree of `t` are those of `s`. -/
theorem tPut_get (t : DescSel) (s : DeflateState) (A : Array Ct) : t.get (tPut t s A) = t.get s := by
  cases t <;> rfl

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

theorem t_get (t : DescSel) (s : DeflateState) : Space.get (SH H i z b s d) (tRef t b) = some (tArr t s) := by
  cases t
  · exact ctl_get s
  · exact ctd_get s
  · exact ctb_get s

theorem t_mod (t : DescSel) (s : DeflateState) (g : Array Ct → Array Ct) :
    Space.modify (SH H i z b s d) (tRef t b) g = SH H i z b (tPut t s (g (tArr t s))) d := by
  cases t
  · exact ctl_mod s g
  · exact ctd_mod s g
  · exact ctb_mod s g

theorem t_ro (t : DescSel) (s : DeflateState) : Space.ro (SH H i z b s d) (tRef t b) = false := by
  cases t <;> rfl

theorem tadd (t : DescSel) (s : DeflateState) (k : Nat) (hk : k < (tArr t s).size) :
    Ptr.add (Ptr.ref (tRef t b) 0) (k : Int) (SH H i z b s d) = .ok (Ptr.ref (tRef t b) k, SH H i z b s d) := by
  simp only [Ptr.add, t_get]
  rw [ite_t (by omega)]
  congr 3; omega

theorem ctGet_T (t : DescSel) (s : DeflateState) (k : Nat) (hk : k < (tArr t s).size) :
    ctGet (.ref (tRef t b) 0) (k : Int) (SH H i z b s d) = .ok ((tArr t s)[k]!, SH H i z b s d) := by
  simp [ctGet, Ptr.index, bind_app, tadd t s k hk, Ptr.load, t_get, hk]

theorem ctFc_T (t : DescSel) (s : DeflateState) (k : Nat) (hk : k < (tArr t s).size) :
    ctFc (.ref (tRef t b) 0) (k : Int) (SH H i z b s d) = .ok (((tArr t s)[k]!).fc, SH H i z b s d) := by
  simp [ctFc, bind_app, ctGet_T t s k hk]

theorem ctDl_T (t : DescSel) (s : DeflateState) (k : Nat) (hk : k < (tArr t s).size) :
    ctDl (.ref (tRef t b) 0) (k : Int) (SH H i z b s d) = .ok (((tArr t s)[k]!).dl, SH H i z b s d) := by
  simp [ctDl, bind_app, ctGet_T t s k hk]

theorem ctSet_T (t : DescSel) (s : DeflateState) (k : Nat) (hk : k < (tArr t s).size) (c : Ct) :
    ctSet (.ref (tRef t b) 0) (k : Int) c (SH H i z b s d) =
      .ok ((), SH H i z b (tPut t s ((tArr t s).set! k c)) d) := by
  simp only [ctSet, bind_app, tadd t s k hk, Ptr.store, t_get, t_ro, hk, Bool.false_eq_true, ↓reduceIte, t_mod]

theorem ctSetFc_T (t : DescSel) (s : DeflateState) (k : Nat) (hk : k < (tArr t s).size) (v : UInt16) :
    ctSetFc (.ref (tRef t b) 0) (k : Int) v (SH H i z b s d) =
      .ok ((), SH H i z b (tPut t s ((tArr t s).set! k { (tArr t s)[k]! with fc := v })) d) := by
  simp only [ctSetFc, bind_app, ctGet_T t s k hk]
  exact ctSet_T t s k hk _

theorem ctSetDl_T (t : DescSel) (s : DeflateState) (k : Nat) (hk : k < (tArr t s).size) (v : UInt16) :
    ctSetDl (.ref (tRef t b) 0) (k : Int) v (SH H i z b s d) =
      .ok ((), SH H i z b (tPut t s ((tArr t s).set! k { (tArr t s)[k]! with dl := v })) d) := by
  simp only [ctSetDl, bind_app, ctGet_T t s k hk]
  exact ctSet_T t s k hk _

/-- `desc->dyn_tree` when the descriptor points at its tree. -/
theorem descDynTree_SH (t : DescSel) (s : DeflateState) (h : (t.get s).dyn_tree = .val (.ref (tRef t b) 0)) :
    descDynTree (some b) t (SH H i z b s d) = .ok (.ref (tRef t b) 0, SH H i z b s d) := by
  simp [descDynTree, bind_app, ldDState_SH, h, Ival.get]

/-- `*desc->stat_desc` when the descriptor points at its static descriptor. -/
theorem descStat_SH (t : DescSel) (s : DeflateState) (h : (t.get s).stat_desc = .val (tSD t)) :
    descStat (some b) t (SH H i z b s d) = .ok ((tSD t).get, SH H i z b s d) := by
  simp [descStat, bind_app, ldDState_SH, h, Ival.get]

/-! ## The queues `pq_leaves` / `pq_scratch` -/

/-- `pq_scratch` (`true`) or `pq_leaves` (`false`) of the state in block `b`. -/
def qRef (q : Bool) (b : Nat) : DWRef := if q then .pq_scratch b else .pq_leaves b

/-- The queue array `q`. -/
def qArr (q : Bool) (s : DeflateState) : Array UInt32 := if q then s.pq_scratch else s.pq_leaves

/-- The state with queue array `q` replaced. -/
def qPut (q : Bool) (s : DeflateState) (A : Array UInt32) : DeflateState :=
  if q then { s with pq_scratch := A } else { s with pq_leaves := A }

theorem q_get (q : Bool) (s : DeflateState) : Space.get (SH H i z b s d) (qRef q b) = some (qArr q s) := by
  cases q <;> simp [qRef, qArr, Space.get, Heap.getDW]

theorem q_mod (q : Bool) (s : DeflateState) (g : Array UInt32 → Array UInt32) :
    Space.modify (SH H i z b s d) (qRef q b) g = SH H i z b (qPut q s (g (qArr q s))) d := by
  cases q
  · show Heap.modifyDW _ _ _ = _
    simp only [qRef, Bool.false_eq_true, ↓reduceIte, Heap.modifyDW, qPut, qArr]
    rw [Heap.dstates_modify_eq _ b _ s (SH_dstates H i z b s d)]
    simp [SH, upd_upd]
  · show Heap.modifyDW _ _ _ = _
    simp only [qRef, ↓reduceIte, Heap.modifyDW, qPut, qArr]
    rw [Heap.dstates_modify_eq _ b _ s (SH_dstates H i z b s d)]
    simp [SH, upd_upd]

theorem qadd (q : Bool) (s : DeflateState) (k : Nat) (hk : k < (qArr q s).size) :
    Ptr.add (Ptr.ref (qRef q b) 0) (k : Int) (SH H i z b s d) = .ok (Ptr.ref (qRef q b) k, SH H i z b s d) := by
  simp only [Ptr.add, q_get]
  rw [ite_t (by omega)]
  congr 3; omega

theorem dwGet_Q (q : Bool) (s : DeflateState) (k : Nat) (hk : k < (qArr q s).size) :
    dwGet (.ref (qRef q b) 0) (k : Int) (SH H i z b s d) = .ok ((qArr q s)[k]!, SH H i z b s d) := by
  simp [dwGet, Ptr.index, bind_app, qadd q s k hk, Ptr.load, q_get, hk]

theorem dwSet_Q (q : Bool) (s : DeflateState) (k : Nat) (hk : k < (qArr q s).size) (v : UInt32) :
    dwSet (.ref (qRef q b) 0) (k : Int) v (SH H i z b s d) =
      .ok ((), SH H i z b (qPut q s ((qArr q s).set! k v)) d) := by
  simp only [dwSet, bind_app, qadd q s k hk, Ptr.store, q_get, hk, ↓reduceIte, q_mod]
  rfl

@[simp] theorem qArr_qPut (q : Bool) (s : DeflateState) (A : Array UInt32) : qArr q (qPut q s A) = A := by
  cases q <;> rfl

@[simp] theorem qArr_qPut_ne (q : Bool) (s : DeflateState) (A : Array UInt32) : qArr (!q) (qPut q s A) = qArr (!q) s := by
  cases q <;> rfl

theorem pqLeavesP_eq (s : DeflateState) :
    pqLeavesP (some b) (SH H i z b s d) = .ok (.ref (qRef false b) 0, SH H i z b s d) := rfl

theorem pqScratchP_eq (s : DeflateState) :
    pqScratchP (some b) (SH H i z b s d) = .ok (.ref (qRef true b) 0, SH H i z b s d) := rfl

/-! ## `bl_count` -/

theorem bc_get (s : DeflateState) : Space.get (SH H i z b s d) (DHRef.bl_count b) = some s.bl_count := by
  simp [Space.get, Heap.getDH]

theorem bc_mod (s : DeflateState) (g : Array UInt16 → Array UInt16) :
    Space.modify (SH H i z b s d) (DHRef.bl_count b) g = SH H i z b { s with bl_count := g s.bl_count } d := by
  show Heap.modifyDH _ _ _ = _
  simp only [Heap.modifyDH]
  rw [Heap.dstates_modify_eq _ b _ s (SH_dstates H i z b s d)]
  simp [SH, upd_upd]

theorem bcadd (s : DeflateState) (k : Nat) (hk : k < s.bl_count.size) :
    Ptr.add (Ptr.ref (DHRef.bl_count b) 0) (k : Int) (SH H i z b s d) =
      .ok (Ptr.ref (DHRef.bl_count b) k, SH H i z b s d) := by
  simp only [Ptr.add, bc_get]
  rw [ite_t (by omega)]
  congr 3; omega

theorem blCountGet_SH (s : DeflateState) (k : Nat) (hk : k < s.bl_count.size) :
    blCountGet (some b) (k : Int) (SH H i z b s d) = .ok (s.bl_count[k]!, SH H i z b s d) := by
  simp only [blCountGet, blCountP, pure_bind_M]
  simp [Ptr.index, bind_app, bcadd s k hk, Ptr.load, bc_get, hk]

theorem blCountSet_SH (s : DeflateState) (k : Nat) (hk : k < s.bl_count.size) (v : UInt16) :
    blCountSet (some b) (k : Int) v (SH H i z b s d) =
      .ok ((), SH H i z b { s with bl_count := s.bl_count.set! k v } d) := by
  simp only [blCountSet, blCountP, pure_bind_M]
  simp only [bind_app, bcadd s k hk, Ptr.store, bc_get, hk, ↓reduceIte, bc_mod]
  rfl

end

end ZlibNgF.Proof.TreesPrims
