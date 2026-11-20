import ZlibNgF.Runtime.Libc

/-!
# Runtime objects of the inflate side (`ZlibNgF`)

* `z_stream` and `gz_header` objects of the caller (`Heap.streams`, `Heap.gzheaders`): load, store, and the
  allocation of a fresh one (a caller's object, or the local `z_stream` of `uncompress`).
* The single allocation of `alloc_inflate`: a byte block from `zalloc`, carved into the window bytes, one
  `inflate_state` and one `inflate_allocs` record (`carveState`, `carveAllocs`). A carve checks that the region
  lies inside the bytes of the block that are still plain bytes, that the address is aligned for the type
  (as `Ptr.castAligned`), and that the block holds no object of that type yet; it then cuts the byte array of
  the block at the start of the region. The carved region and everything after it are no longer bytes: a byte
  access there faults. Regions carved in decreasing address order are therefore disjoint; carving below an
  existing typed object, or a second object of one type in one block, faults (the C code never does either).
  The fields of a carved object are uninitialised: integers come from `Heap.garbage`, pointer fields are
  `Ival.uninit` and fault when read before written.
* `Space` instances for the `code` arrays (`codes` of a state, static `lenfix`/`distfix`) and the `uint16_t`
  arrays `lens`/`work` of a state.

Trusted (see `AGENTS.md`): the sizes and alignments of the structures (`SIZEOF_INFLATE_STATE`, ...), measured on
the built configuration; that a carved typed object stands for the bytes it occupies (the C stores into it
through a pointer to its type only, except `inflateCopy`'s `memcpy` of a whole `inflate_state`, which the
translation performs as a copy of the record).
-/

set_option autoImplicit false

namespace C

instance : Junk Int32 := ⟨fun x => x.toUInt32.toInt32⟩

/-- Read a pointer field of a carved object: faults if it was never written (ISO C17 §6.2.4p6, §6.3.2.1p2). -/
def Ival.get {α : Type} (v : Ival α) : M α :=
  match v with
  | .val a => pure a
  | .uninit => ub "read of an uninitialised pointer field"

/-! ## Liveness of carved objects -/

/-- The `inflate_state` of block `b`, while the block is alive. -/
def Heap.istate (h : Heap) (b : Nat) : Option InflateState :=
  match h.bytes b with
  | some _ => h.istates b
  | none => none

/-- The `inflate_allocs` record of block `b`, while the block is alive. -/
def Heap.iallocsOf (h : Heap) (b : Nat) : Option InflateAllocs :=
  match h.bytes b with
  | some _ => h.iallocs b
  | none => none

/-! ## Loads and stores of typed objects -/

def ldStream (p : StreamPtr) : M ZStream := fun h =>
  match p with
  | none => .error (.ub "null z_stream pointer")
  | some i => match h.streams i with
    | some z => .ok (z, h)
    | none => .error (.ub "dangling z_stream pointer")

def stStream (p : StreamPtr) (z : ZStream) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null z_stream pointer")
  | some i => match h.streams i with
    | some _ => .ok ((), { h with streams := upd h.streams i (some z) })
    | none => .error (.ub "dangling z_stream pointer")

def ldHeader (p : HeaderPtr) : M GzHeader := fun h =>
  match p with
  | none => .error (.ub "null gz_header pointer")
  | some i => match h.gzheaders i with
    | some g => .ok (g, h)
    | none => .error (.ub "dangling gz_header pointer")

def stHeader (p : HeaderPtr) (g : GzHeader) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null gz_header pointer")
  | some i => match h.gzheaders i with
    | some _ => .ok ((), { h with gzheaders := upd h.gzheaders i (some g) })
    | none => .error (.ub "dangling gz_header pointer")

def ldState (p : StatePtr) : M InflateState := fun h =>
  match p with
  | none => .error (.ub "null inflate_state pointer")
  | some b => match h.istate b with
    | some s => .ok (s, h)
    | none => .error (.ub "dangling inflate_state pointer")

def stState (p : StatePtr) (s : InflateState) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null inflate_state pointer")
  | some b => match h.istate b with
    | some _ => .ok ((), { h with istates := upd h.istates b (some s) })
    | none => .error (.ub "dangling inflate_state pointer")

def ldAllocs (p : AllocsPtr) : M InflateAllocs := fun h =>
  match p with
  | none => .error (.ub "null inflate_allocs pointer")
  | some b => match h.iallocsOf b with
    | some a => .ok (a, h)
    | none => .error (.ub "dangling inflate_allocs pointer")

def stAllocs (p : AllocsPtr) (a : InflateAllocs) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null inflate_allocs pointer")
  | some b => match h.iallocsOf b with
    | some _ => .ok ((), { h with iallocs := upd h.iallocs b (some a) })
    | none => .error (.ub "dangling inflate_allocs pointer")

/-- A new caller `z_stream` object holding `z` (a caller's declaration, or the local `z_stream` of `uncompress`). -/
def newStream (z : ZStream) : M StreamPtr := fun h =>
  let i := h.streams.arr.size
  .ok (some i, { h with streams := upd h.streams i (some z) })

/-- The end of the lifetime of a `z_stream` made by `newStream`. -/
def dropStream (p : StreamPtr) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null z_stream pointer")
  | some i => match h.streams i with
    | some _ => .ok ((), { h with streams := upd h.streams i none })
    | none => .error (.ub "dangling z_stream pointer")

/-- A new caller `gz_header` object holding `g`. -/
def newHeader (g : GzHeader) : M HeaderPtr := fun h =>
  let i := h.gzheaders.arr.size
  .ok (some i, { h with gzheaders := upd h.gzheaders i (some g) })

/-! ## Carving `alloc_inflate`'s block -/

/-- An `inflate_state` with uninitialised fields; integers from the garbage stream `g`. -/
def InflateState.garbage (g : Nat → UInt64) : InflateState where
  strm := .uninit
  mode := Junk.of (g 0)
  last := Junk.of (g 1)
  wrap := Junk.of (g 2)
  havedict := Junk.of (g 3)
  flags := Junk.of (g 4)
  was := Junk.of (g 5)
  check := Junk.of (g 6)
  total := Junk.of (g 7)
  head := .uninit
  back := Junk.of (g 8)
  wide_len := Junk.of (g 26)
  wbits := Junk.of (g 9)
  wsize := Junk.of (g 10)
  wbufsize := Junk.of (g 11)
  whave := Junk.of (g 12)
  wnext := Junk.of (g 13)
  window := .uninit
  hold := Junk.of (g 14)
  bits := Junk.of (g 15)
  lenbits := Junk.of (g 16)
  lencode := .uninit
  distcode := .uninit
  distbits := Junk.of (g 17)
  length := Junk.of (g 18)
  offset := Junk.of (g 19)
  extra := Junk.of (g 20)
  ncode := Junk.of (g 21)
  nlen := Junk.of (g 22)
  ndist := Junk.of (g 23)
  «have» := Junk.of (g 24)
  next := .uninit
  lens := Array.ofFn (n := 320) fun i => Junk.of (g (100 + i.val))
  work := Array.ofFn (n := 288) fun i => Junk.of (g (500 + i.val))
  codes := Array.ofFn (n := ENOUGH) fun i =>
    ⟨Junk.of (g (1000 + 3 * i.val)), Junk.of (g (1001 + 3 * i.val)), Junk.of (g (1002 + 3 * i.val))⟩
  alloc_bufs := .uninit
  reqbits := Junk.of (g 25)

/-- Common checks of a carve of `size` bytes aligned to `align` at `p`: returns the block number. -/
def carveCheck (p : BPtr) (size align : Nat) : M Nat := fun h =>
  match p with
  | .ref (.heap b) off =>
    match h.bytes b with
    | some a =>
      if off + size ≤ a.size then
        if (h.baseAddr (.heap b) + UInt64.ofNat off).toNat % align == 0 then .ok (b, h)
        else .error (.ub "conversion to a misaligned pointer")
      else .error (.ub "object does not fit in the plain bytes of its block")
    | none => .error (.ub "carve of a dangling block")
  | _ => .error (.ub "carve of a non-heap pointer")

/-- Cut the byte array of block `b` at `off`: the bytes from `off` on become a typed object. -/
def cutBytes (b off : Nat) : M Unit := fun h =>
  match h.bytes b with
  | some a => .ok ((), { h with bytes := upd h.bytes b (some (a.extract 0 off)) })
  | none => .error (.ub "carve of a dangling block")

/-- `(struct inflate_state *)p` on a pointer into a block from `zalloc`: the `inflate_state` object there. -/
def carveState (p : BPtr) : M StatePtr := do
  let b ← carveCheck p SIZEOF_INFLATE_STATE ALIGNOF_INFLATE_STATE
  let h ← fun h => .ok (h, h)
  if (h.istates b).isSome then ub "second inflate_state in one block (not modelled)"
  match p with
  | .ref _ off => cutBytes b off
  | .null => ub "carve of a null pointer"
  fun h => .ok (some b, { h with istates := upd h.istates b (some (InflateState.garbage (h.garbage (2 ^ 40 + b)))) })

/-- `(inflate_allocs *)p` on a pointer into a block from `zalloc`: the `inflate_allocs` record there. -/
def carveAllocs (p : BPtr) : M AllocsPtr := do
  let b ← carveCheck p SIZEOF_INFLATE_ALLOCS ALIGNOF_INFLATE_ALLOCS
  let h ← fun h => .ok (h, h)
  if (h.iallocs b).isSome then ub "second inflate_allocs in one block (not modelled)"
  match p with
  | .ref _ off => cutBytes b off
  | .null => ub "carve of a null pointer"
  fun h => .ok (some b, { h with iallocs := upd h.iallocs b (some ⟨.uninit, .uninit, .uninit, .uninit⟩) })

/-- `memcpy(dst, src, sizeof(struct inflate_state))` between two `inflate_state` objects (the C copies the bytes of
the object; the model copies the record). -/
def copyState (dst src : StatePtr) : M Unit := do
  if dst == src then ub "overlapping memcpy"
  let s ← ldState src
  let _ ← ldState dst
  stState dst s

/-! ## `code` and `uint16_t` arrays -/

def Heap.getCodes (h : Heap) : CodeRef → Option (Array Code)
  | .codes b => (h.istate b).map (·.codes)
  | .lenfix => some lenfix
  | .distfix => some distfix

def Heap.putCodes (h : Heap) (r : CodeRef) (a : Array Code) : Heap :=
  match r with
  | .codes b => match h.istates b with
    | some s => { h with istates := upd h.istates b (some { s with codes := a }) }
    | none => h
  | _ => h

def Heap.roCodes (_h : Heap) : CodeRef → Bool
  | .codes _ => false
  | _ => true

def Heap.modifyCodes (h : Heap) (r : CodeRef) (f : Array Code → Array Code) : Heap :=
  match r with
  | .codes b => { h with istates := h.istates.modify b (Option.map fun s => { s with codes := f s.codes }) }
  | _ => h

theorem Heap.modifyCodes_eq (h : Heap) (r : CodeRef) (a : Array Code) (f : Array Code → Array Code)
    (hg : getCodes h r = some a) (hro : roCodes h r = false) :
    modifyCodes h r f = putCodes h r (f a) := by
  cases r with
  | codes b =>
    simp only [getCodes, Heap.istate] at hg
    split at hg
    · cases hs : h.istates b with
      | none => rw [hs] at hg; simp at hg
      | some s =>
        rw [hs] at hg
        simp only [Option.map_some, Option.some.injEq] at hg
        subst hg
        simp only [modifyCodes, putCodes, hs, Tbl.modify_opt h.istates b _ s hs]
    · simp at hg
  | lenfix => simp [roCodes] at hro
  | distfix => simp [roCodes] at hro

instance : Space Heap CodeRef Code where
  get := Heap.getCodes
  put := Heap.putCodes
  ro := Heap.roCodes
  modify := Heap.modifyCodes
  modify_eq := Heap.modifyCodes_eq

def Heap.getWords (h : Heap) : WRef → Option (Array UInt16)
  | .lens b => (h.istate b).map (·.lens)
  | .work b => (h.istate b).map (·.work)

def Heap.putWords (h : Heap) (r : WRef) (a : Array UInt16) : Heap :=
  match r with
  | .lens b => match h.istates b with
    | some s => { h with istates := upd h.istates b (some { s with lens := a }) }
    | none => h
  | .work b => match h.istates b with
    | some s => { h with istates := upd h.istates b (some { s with work := a }) }
    | none => h

def Heap.modifyWords (h : Heap) (r : WRef) (f : Array UInt16 → Array UInt16) : Heap :=
  match r with
  | .lens b => { h with istates := h.istates.modify b (Option.map fun s => { s with lens := f s.lens }) }
  | .work b => { h with istates := h.istates.modify b (Option.map fun s => { s with work := f s.work }) }

theorem Heap.modifyWords_eq (h : Heap) (r : WRef) (a : Array UInt16) (f : Array UInt16 → Array UInt16)
    (hg : getWords h r = some a) (_hro : false = false) :
    modifyWords h r f = putWords h r (f a) := by
  cases r with
  | lens b =>
    simp only [getWords, Heap.istate] at hg
    split at hg
    · cases hs : h.istates b with
      | none => rw [hs] at hg; simp at hg
      | some s =>
        rw [hs] at hg
        simp only [Option.map_some, Option.some.injEq] at hg
        subst hg
        simp only [modifyWords, putWords, hs, Tbl.modify_opt h.istates b _ s hs]
    · simp at hg
  | work b =>
    simp only [getWords, Heap.istate] at hg
    split at hg
    · cases hs : h.istates b with
      | none => rw [hs] at hg; simp at hg
      | some s =>
        rw [hs] at hg
        simp only [Option.map_some, Option.some.injEq] at hg
        subst hg
        simp only [modifyWords, putWords, hs, Tbl.modify_opt h.istates b _ s hs]
    · simp at hg

instance : Space Heap WRef UInt16 where
  get := Heap.getWords
  put := Heap.putWords
  ro := fun _ _ => false
  modify := Heap.modifyWords
  modify_eq := fun h r a f hg hro => Heap.modifyWords_eq h r a f hg hro

end C
