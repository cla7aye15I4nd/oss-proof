import ZlibNgF.Runtime.Inflate
import ZlibNgF.Runtime.CExpr

/-!
# Runtime objects of the deflate side (`ZlibNgF`)

* The single allocation of `alloc_deflate`: a byte block from `zalloc`, carved into one `deflate_allocs` record and
  one `deflate_state` (`carveDAllocs`, `carveDState`, same rules as the inflate carves of `Runtime/Inflate.lean`:
  the region must lie in the plain bytes of the live block, the address must be aligned for the type, the block
  must not hold an object of that type yet, and the byte array is cut at the start of the region). The window,
  `prev`, `head` and `pending_buf` stay plain bytes of the block, below the state.
* `Space` instances for the `ct_data` arrays (`dyn_ltree`, `dyn_dtree`, `bl_tree` of a state; the read-only
  `static_ltree` / `static_dtree`), the `uint32_t` arrays `pq_leaves` / `pq_scratch`, the `uint16_t` array
  `bl_count`, and the read-only `const int` arrays `extra_lbits` / `extra_dbits` / `extra_blbits` of `trees.h`.
* The three `static const static_tree_desc` objects of `trees.c`.
* `zng_memwrite_2` / `zng_memwrite_4` (`zmemory.h`) and the two-byte `Pos` accesses of `prev` / `head`.

Trusted (see `AGENTS.md`): `SIZEOF_DEFLATE_STATE`, `ALIGNOF_DEFLATE_STATE`, `SIZEOF_DEFLATE_ALLOCS`,
`ALIGNOF_DEFLATE_ALLOCS`, measured on the built configuration; that the C accesses a carved object only through a
pointer to its type (`deflateCopy`'s `memcpy` of a whole `deflate_state` is a record copy, `copyDState`); the static
tables of `Runtime/TreesTbl.lean`, copied from `trees_tbl.h` by a script.
-/

set_option autoImplicit false

namespace C

/-! ## Liveness of carved objects -/

/-- The `deflate_state` of block `b`, while the block is alive. -/
def Heap.dstate (h : Heap) (b : Nat) : Option DeflateState :=
  match h.bytes b with
  | some _ => h.dstates b
  | none => none

/-- The `deflate_allocs` record of block `b`, while the block is alive. -/
def Heap.dallocsOf (h : Heap) (b : Nat) : Option DeflateAllocs :=
  match h.bytes b with
  | some _ => h.dallocs b
  | none => none

/-! ## Loads and stores of typed objects -/

def ldDState (p : StatePtr) : M DeflateState := fun h =>
  match p with
  | none => .error (.ub "null deflate_state pointer")
  | some b => match h.dstate b with
    | some s => .ok (s, h)
    | none => .error (.ub "dangling deflate_state pointer")

def stDState (p : StatePtr) (s : DeflateState) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null deflate_state pointer")
  | some b => match h.dstate b with
    | some _ => .ok ((), { h with dstates := upd h.dstates b (some s) })
    | none => .error (.ub "dangling deflate_state pointer")

def ldDAllocs (p : DAllocsPtr) : M DeflateAllocs := fun h =>
  match p with
  | none => .error (.ub "null deflate_allocs pointer")
  | some b => match h.dallocsOf b with
    | some a => .ok (a, h)
    | none => .error (.ub "dangling deflate_allocs pointer")

def stDAllocs (p : DAllocsPtr) (a : DeflateAllocs) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null deflate_allocs pointer")
  | some b => match h.dallocsOf b with
    | some _ => .ok ((), { h with dallocs := upd h.dallocs b (some a) })
    | none => .error (.ub "dangling deflate_allocs pointer")

/-- `memcpy(dest, source, sizeof(z_stream))` between two caller `z_stream` objects (a record copy). The two objects
must be distinct (ISO C17 §7.24.2.1p2). -/
def copyStream (dst src : StreamPtr) : M Unit := do
  if dst == src then ub "overlapping memcpy"
  let z ← ldStream src
  let _ ← ldStream dst
  stStream dst z

/-- `memcpy(dst, src, sizeof(deflate_state))` between two `deflate_state` objects (a record copy). -/
def copyDState (dst src : StatePtr) : M Unit := do
  if dst == src then ub "overlapping memcpy"
  let s ← ldDState src
  let _ ← ldDState dst
  stDState dst s

/-! ## Carving `alloc_deflate`'s block -/

/-- `L_CODES = LITERALS + 1 + LENGTH_CODES` (`deflate.h`). -/
def L_CODES : Nat := 256 + 1 + 29
/-- `HEAP_SIZE = 2 * L_CODES + 1` (`deflate.h`). -/
def HEAP_SIZE : Nat := 2 * L_CODES + 1

/-- An uninitialised `tree_desc`; integers from `g`. -/
def TreeDesc.garbage (g : UInt64) : TreeDesc := ⟨.uninit, Junk.of g, .uninit⟩

/-- A `deflate_state` with uninitialised fields; integers from the garbage stream `g`. -/
def DeflateState.garbage (g : Nat → UInt64) : DeflateState where
  strm := .uninit
  pending_buf := .uninit
  pending_out := .uninit
  pending_buf_size := Junk.of (g 0)
  pending := Junk.of (g 1)
  wrap := Junk.of (g 2)
  gzindex := Junk.of (g 3)
  gzhead := .uninit
  status := Junk.of (g 4)
  last_flush := Junk.of (g 5)
  reproducible := Junk.of (g 6)
  block_open := Junk.of (g 7)
  lookahead := Junk.of (g 8)
  strstart := Junk.of (g 9)
  w_size := Junk.of (g 10)
  block_start := Junk.of (g 11)
  high_water := Junk.of (g 12)
  window_size := Junk.of (g 13)
  window := .uninit
  prev := .uninit
  head := .uninit
  ins_h := Junk.of (g 14)
  match_length := Junk.of (g 15)
  match_available := Junk.of (g 16)
  prev_match := Junk.of (g 17)
  match_start := Junk.of (g 18)
  prev_length := Junk.of (g 19)
  max_chain_length := Junk.of (g 20)
  max_lazy_match := Junk.of (g 21)
  level := Junk.of (g 22)
  strategy := Junk.of (g 23)
  good_match := Junk.of (g 24)
  nice_match := Junk.of (g 25)
  insert := Junk.of (g 26)
  bi_used := Junk.of (g 27)
  bi_buf := Junk.of (g 28)
  bi_valid := Junk.of (g 29)
  lit_bufsize := Junk.of (g 30)
  sym_buf := .uninit
  sym_next := Junk.of (g 31)
  sym_end := Junk.of (g 32)
  opt_len := Junk.of (g 33)
  static_len := Junk.of (g 34)
  l_desc := TreeDesc.garbage (g 35)
  d_desc := TreeDesc.garbage (g 36)
  bl_desc := TreeDesc.garbage (g 37)
  bl_count := Array.ofFn (n := 16) fun i => Junk.of (g (100 + i.val))
  pq_leaves := Array.ofFn (n := L_CODES + 1) fun i => Junk.of (g (200 + i.val))
  pq_scratch := Array.ofFn (n := L_CODES + 1) fun i => Junk.of (g (500 + i.val))
  dyn_ltree := Array.ofFn (n := HEAP_SIZE) fun i =>
    ⟨Junk.of (g (1000 + 2 * i.val)), Junk.of (g (1001 + 2 * i.val))⟩
  dyn_dtree := Array.ofFn (n := 2 * 30 + 1) fun i =>
    ⟨Junk.of (g (3000 + 2 * i.val)), Junk.of (g (3001 + 2 * i.val))⟩
  bl_tree := Array.ofFn (n := 2 * 19 + 1) fun i =>
    ⟨Junk.of (g (3200 + 2 * i.val)), Junk.of (g (3201 + 2 * i.val))⟩
  alloc_bufs := .uninit
  longest_match := .uninit
  insert_batch := .uninit
  slide_len := Junk.of (g 38)
  fill_end := Junk.of (g 39)

/-- `(deflate_state *)p` on a pointer into a block from `zalloc`: the `deflate_state` object there. -/
def carveDState (p : BPtr) : M StatePtr := do
  let b ← carveCheck p SIZEOF_DEFLATE_STATE ALIGNOF_DEFLATE_STATE
  let h ← fun h => .ok (h, h)
  if (h.dstates b).isSome then ub "second deflate_state in one block (not modelled)"
  match p with
  | .ref _ off => cutBytes b off
  | .null => ub "carve of a null pointer"
  fun h => .ok (some b, { h with dstates := upd h.dstates b (some (DeflateState.garbage (h.garbage (2 ^ 43 + b)))) })

/-- `(deflate_allocs *)p` on a pointer into a block from `zalloc`: the `deflate_allocs` record there. -/
def carveDAllocs (p : BPtr) : M DAllocsPtr := do
  let b ← carveCheck p SIZEOF_DEFLATE_ALLOCS ALIGNOF_DEFLATE_ALLOCS
  let h ← fun h => .ok (h, h)
  if (h.dallocs b).isSome then ub "second deflate_allocs in one block (not modelled)"
  match p with
  | .ref _ off => cutBytes b off
  | .null => ub "carve of a null pointer"
  let a : DeflateAllocs := ⟨.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit⟩
  fun h => .ok (some b, { h with dallocs := upd h.dallocs b (some a) })

/-! ## `ct_data` arrays -/

def Heap.getCts (h : Heap) : CtRef → Option (Array Ct)
  | .dyn_ltree b => (h.dstate b).map (·.dyn_ltree)
  | .dyn_dtree b => (h.dstate b).map (·.dyn_dtree)
  | .bl_tree b => (h.dstate b).map (·.bl_tree)
  | .static_ltree => some static_ltree
  | .static_dtree => some static_dtree

/-- Replace one tree array of the state in block `b` (no-op on other references). -/
def Heap.putCts (h : Heap) (r : CtRef) (a : Array Ct) : Heap :=
  match r with
  | .dyn_ltree b => match h.dstates b with
    | some s => { h with dstates := upd h.dstates b (some { s with dyn_ltree := a }) }
    | none => h
  | .dyn_dtree b => match h.dstates b with
    | some s => { h with dstates := upd h.dstates b (some { s with dyn_dtree := a }) }
    | none => h
  | .bl_tree b => match h.dstates b with
    | some s => { h with dstates := upd h.dstates b (some { s with bl_tree := a }) }
    | none => h
  | _ => h

def Heap.roCts (_h : Heap) : CtRef → Bool
  | .static_ltree => true
  | .static_dtree => true
  | _ => false

def Heap.modifyCts (h : Heap) (r : CtRef) (f : Array Ct → Array Ct) : Heap :=
  match r with
  | .dyn_ltree b => { h with dstates := h.dstates.modify b (Option.map fun s => { s with dyn_ltree := f s.dyn_ltree }) }
  | .dyn_dtree b => { h with dstates := h.dstates.modify b (Option.map fun s => { s with dyn_dtree := f s.dyn_dtree }) }
  | .bl_tree b => { h with dstates := h.dstates.modify b (Option.map fun s => { s with bl_tree := f s.bl_tree }) }
  | _ => h

/-- Shared step of the `modify_eq` proofs: a live state in block `b` updated through `Tbl.modify`. -/
theorem Heap.dstates_modify_eq (h : Heap) (b : Nat) (g : DeflateState → DeflateState) (s : DeflateState)
    (hs : h.dstates b = some s) :
    h.dstates.modify b (Option.map g) = upd h.dstates b (some (g s)) :=
  Tbl.modify_opt h.dstates b g s hs

theorem Heap.dstate_some {h : Heap} {b : Nat} {s : DeflateState} (hg : h.dstate b = some s) :
    h.dstates b = some s := by
  unfold Heap.dstate at hg
  split at hg
  · exact hg
  · simp at hg

theorem Heap.modifyCts_eq (h : Heap) (r : CtRef) (a : Array Ct) (f : Array Ct → Array Ct)
    (hg : getCts h r = some a) (hro : roCts h r = false) :
    modifyCts h r f = putCts h r (f a) := by
  cases r with
  | dyn_ltree b =>
    simp only [getCts] at hg
    cases hs : h.dstate b with
    | none => rw [hs] at hg; simp at hg
    | some s =>
      rw [hs] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg
      have hs' := Heap.dstate_some hs
      simp only [modifyCts, putCts, hs', Heap.dstates_modify_eq h b _ s hs']
  | dyn_dtree b =>
    simp only [getCts] at hg
    cases hs : h.dstate b with
    | none => rw [hs] at hg; simp at hg
    | some s =>
      rw [hs] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg
      have hs' := Heap.dstate_some hs
      simp only [modifyCts, putCts, hs', Heap.dstates_modify_eq h b _ s hs']
  | bl_tree b =>
    simp only [getCts] at hg
    cases hs : h.dstate b with
    | none => rw [hs] at hg; simp at hg
    | some s =>
      rw [hs] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg
      have hs' := Heap.dstate_some hs
      simp only [modifyCts, putCts, hs', Heap.dstates_modify_eq h b _ s hs']
  | static_ltree => simp [roCts] at hro
  | static_dtree => simp [roCts] at hro

instance : Space Heap CtRef Ct where
  get := Heap.getCts
  put := Heap.putCts
  ro := Heap.roCts
  modify := Heap.modifyCts
  modify_eq := Heap.modifyCts_eq

/-! ## `uint32_t` arrays `pq_leaves` / `pq_scratch` -/

def Heap.getDW (h : Heap) : DWRef → Option (Array UInt32)
  | .pq_leaves b => (h.dstate b).map (·.pq_leaves)
  | .pq_scratch b => (h.dstate b).map (·.pq_scratch)

def Heap.putDW (h : Heap) (r : DWRef) (a : Array UInt32) : Heap :=
  match r with
  | .pq_leaves b => match h.dstates b with
    | some s => { h with dstates := upd h.dstates b (some { s with pq_leaves := a }) }
    | none => h
  | .pq_scratch b => match h.dstates b with
    | some s => { h with dstates := upd h.dstates b (some { s with pq_scratch := a }) }
    | none => h

def Heap.modifyDW (h : Heap) (r : DWRef) (f : Array UInt32 → Array UInt32) : Heap :=
  match r with
  | .pq_leaves b => { h with dstates := h.dstates.modify b (Option.map fun s => { s with pq_leaves := f s.pq_leaves }) }
  | .pq_scratch b => { h with dstates := h.dstates.modify b (Option.map fun s => { s with pq_scratch := f s.pq_scratch }) }

theorem Heap.modifyDW_eq (h : Heap) (r : DWRef) (a : Array UInt32) (f : Array UInt32 → Array UInt32)
    (hg : getDW h r = some a) (_hro : false = false) :
    modifyDW h r f = putDW h r (f a) := by
  cases r with
  | pq_leaves b =>
    simp only [getDW] at hg
    cases hs : h.dstate b with
    | none => rw [hs] at hg; simp at hg
    | some s =>
      rw [hs] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg
      have hs' := Heap.dstate_some hs
      simp only [modifyDW, putDW, hs', Heap.dstates_modify_eq h b _ s hs']
  | pq_scratch b =>
    simp only [getDW] at hg
    cases hs : h.dstate b with
    | none => rw [hs] at hg; simp at hg
    | some s =>
      rw [hs] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg
      have hs' := Heap.dstate_some hs
      simp only [modifyDW, putDW, hs', Heap.dstates_modify_eq h b _ s hs']

instance : Space Heap DWRef UInt32 where
  get := Heap.getDW
  put := Heap.putDW
  ro := fun _ _ => false
  modify := Heap.modifyDW
  modify_eq := fun h r a f hg hro => Heap.modifyDW_eq h r a f hg hro

/-! ## `uint16_t` array `bl_count` -/

def Heap.getDH (h : Heap) : DHRef → Option (Array UInt16)
  | .bl_count b => (h.dstate b).map (·.bl_count)

def Heap.putDH (h : Heap) (r : DHRef) (a : Array UInt16) : Heap :=
  match r with
  | .bl_count b => match h.dstates b with
    | some s => { h with dstates := upd h.dstates b (some { s with bl_count := a }) }
    | none => h

def Heap.modifyDH (h : Heap) (r : DHRef) (f : Array UInt16 → Array UInt16) : Heap :=
  match r with
  | .bl_count b => { h with dstates := h.dstates.modify b (Option.map fun s => { s with bl_count := f s.bl_count }) }

theorem Heap.modifyDH_eq (h : Heap) (r : DHRef) (a : Array UInt16) (f : Array UInt16 → Array UInt16)
    (hg : getDH h r = some a) (_hro : false = false) :
    modifyDH h r f = putDH h r (f a) := by
  cases r with
  | bl_count b =>
    simp only [getDH] at hg
    cases hs : h.dstate b with
    | none => rw [hs] at hg; simp at hg
    | some s =>
      rw [hs] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg
      have hs' := Heap.dstate_some hs
      simp only [modifyDH, putDH, hs', Heap.dstates_modify_eq h b _ s hs']

instance : Space Heap DHRef UInt16 where
  get := Heap.getDH
  put := Heap.putDH
  ro := fun _ _ => false
  modify := Heap.modifyDH
  modify_eq := fun h r a f hg hro => Heap.modifyDH_eq h r a f hg hro

/-! ## The static `const int` arrays of `trees.h` -/

/-- `static const int extra_lbits[LENGTH_CODES]` (`trees.h`). -/
def extra_lbits : Array Int32 := #[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0]
/-- `static const int extra_dbits[D_CODES]` (`trees.h`). -/
def extra_dbits : Array Int32 := #[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13]
/-- `static const int extra_blbits[BL_CODES]` (`trees.h`). -/
def extra_blbits : Array Int32 := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,7]

def Heap.getInts (_h : Heap) : IRef → Option (Array Int32)
  | .extra_lbits => some extra_lbits
  | .extra_dbits => some extra_dbits
  | .extra_blbits => some extra_blbits

instance : Space Heap IRef Int32 where
  get := Heap.getInts
  put := fun h _ _ => h
  ro := fun _ _ => true
  modify := fun h _ _ => h
  modify_eq := fun _ _ _ _ _ hro => by simp at hro

/-! ## `static_tree_desc` -/

/-- `struct static_tree_desc_s` (`trees.c`). -/
structure StaticTreeDesc where
  static_tree : CtPtr
  extra_bits : IPtr
  extra_base : Int32
  elems : Int32
  max_length : UInt32

/-- The three `static const static_tree_desc` of `trees.c:56-63`. -/
def StaticDescPtr.get : StaticDescPtr → StaticTreeDesc
  | .static_l_desc => ⟨.ref .static_ltree 0, .ref .extra_lbits 0, 256 + 1, 286, 15⟩
  | .static_d_desc => ⟨.ref .static_dtree 0, .ref .extra_dbits 0, 0, 30, 15⟩
  | .static_bl_desc => ⟨.null, .ref .extra_blbits 0, 0, 19, 7⟩

/-! ## Static tables read by index, scalar accesses -/

/-- `tbl[i]` on a static `const` array of the translation (`zng_dist_code`, `zng_length_code`, `lmask_extra`, ...):
faults outside the array. -/
def tblGet {α : Type} [Inhabited α] (tbl : Array α) (i : Nat) : M α :=
  if h : i < tbl.size then pure tbl[i] else ub "read outside a static table"

/-- `zng_memwrite_2(p, v)` (little-endian). -/
def memwrite2 (p : BPtr) (v : UInt16) : M Unit := do
  Ptr.store (← p.add 0) v.toUInt8
  Ptr.store (← p.add 1) (v >>> 8).toUInt8

/-- `zng_memwrite_4(p, v)` (little-endian). -/
def memwrite4 (p : BPtr) (v : UInt32) : M Unit := do
  Ptr.store (← p.add 0) v.toUInt8
  Ptr.store (← p.add 1) (v >>> 8).toUInt8
  Ptr.store (← p.add 2) (v >>> 16).toUInt8
  Ptr.store (← p.add 3) (v >>> 24).toUInt8

/-- `p[i]` for `Pos *p` (`prev`, `head`): the two bytes at `p + 2 * i`. -/
def posLoad (p : BPtr) (i : Int) : M UInt16 := do
  memread2 (← p.add (2 * i))

/-- `p[i] = v` for `Pos *p`. -/
def posStore (p : BPtr) (i : Int) (v : UInt16) : M Unit := do
  memwrite2 (← p.add (2 * i)) v

end C
