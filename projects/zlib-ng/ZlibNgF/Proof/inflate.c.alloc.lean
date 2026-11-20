import ZlibNgF.Proof.«inflate.c.reset»

/-!
# `alloc_inflate`, `free_inflate`, `inflateInit2` (`ZlibNgF`)

The symbolic run of `alloc_inflate` for every `baseAddr` and garbage oracle: one `zcalloc` of 42112 bytes (or its
failure), the 64-byte alignment pad `PADSZ`, the carves of the `inflate_allocs` record at `pad + 41984` and of the
`inflate_state` at `pad + 32832`, the window at `pad`. Then `inflateInit2`: the state set-up, `inflateReset2` for every
`windowBits`, and `free_inflate` when it fails. A successful call leaves the structural invariant; every call changes
only the stream record and the fresh block (`Fr`).

Proof engineering: the simp sets keep `2 ^ 40` and `Array.extract` of the fresh block unnormalised
(`-Nat.reducePow`, `-Array.extract_extract`); otherwise the kernel compares the 1924-entry garbage `codes` array or the
42112-byte block element by element.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateAlloc
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Live setZS upd_upd ldState_app ldStream_app Shape Core Inv view CodeTarget)

/-- `alloc_inflate` with its constant sizes evaluated (`window_pos = 0`, `state_pos = 32832`, `alloc_pos = 41984`,
`total_size = 42112`). -/
theorem alloc_pre (s : StreamPtr) : alloc_inflate s = (do
    let z ← ldStream s
    let original_buf ← callZalloc z.zalloc z.«opaque» 1 42112
    if original_buf == .null then return none
    let ob ← addrOf original_buf
    let buff ← HINT_ALIGNED_64 (← original_buf.add (Int.ofNat (PADSZ ob 64).toNat))
    let alloc_bufs ← carveAllocs (← buff.add 41984)
    let a ← ldAllocs alloc_bufs
    stAllocs alloc_bufs { a with buf_start := .val original_buf }
    let z ← ldStream s
    let a ← ldAllocs alloc_bufs
    stAllocs alloc_bufs { a with zfree := .val z.zfree }
    let w ← HINT_ALIGNED_64 (← buff.add 0)
    let a ← ldAllocs alloc_bufs
    stAllocs alloc_bufs { a with window := .val w }
    let sp ← carveState (← buff.add 32832)
    let a ← ldAllocs alloc_bufs
    stAllocs alloc_bufs { a with state := .val sp }
    return alloc_bufs) := by
  rfl

theorem padsz_toNat (A : UInt64) : (PADSZ A 64).toNat = (64 - A.toNat % 64) % 64 := by
  unfold PADSZ
  have h1 : A % 64 ≤ 64 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; show A.toNat % 64 ≤ 64; omega
  rw [UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ h1, UInt64.toNat_mod]
  rfl

theorem padsz_lt (A : UInt64) : (PADSZ A 64).toNat < 64 := by
  rw [padsz_toNat]; omega

theorem space_get_heap (h : Heap) (b : Nat) : Space.get h (BRef.heap b) = h.bytes b := rfl

/-- The heap after a successful `alloc_inflate` for a stream whose `zfree` is `zf`: block `h.nextBlk` holds the
window bytes up to the state, the state and the allocation record. -/
def allocHeap (h : Heap) (zf : FnPtr) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (((Array.ofFn (n := 42112) fun j =>
      (Junk.of (h.garbage h.nalloc j.val) : UInt8)).extract 0
      ((PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + 41984)).extract 0
      ((PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + 32832)))
    savedPtrs := upd h.savedPtrs h.nextBlk none
    nextBlk := h.nextBlk + 1
    nalloc := h.nalloc + 1
    iallocs := upd h.iallocs h.nextBlk (some ⟨.val (.ref (.heap h.nextBlk) 0), .val zf, .val (some h.nextBlk),
      .val (.ref (.heap h.nextBlk) (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat)⟩)
    istates := upd h.istates h.nextBlk (some (InflateState.garbage (h.garbage (2 ^ 40 + h.nextBlk)))) }

/-- `bind_app` for a first action or continuation written as a function on heaps (simp matches at reducible
transparency, where `M` does not unfold). -/
theorem bind_ff {α β : Type} (m : Heap → Except Fault (α × Heap)) (f : α → Heap → Except Fault (β × Heap))
    (h : Heap) :
    (@bind M _ α β m f) h = match m h with | .ok (a, h') => f a h' | .error e => .error e := rfl
theorem bind_mf {α β : Type} (m : M α) (f : α → Heap → Except Fault (β × Heap)) (h : Heap) :
    (@bind M _ α β m f) h = match m h with | .ok (a, h') => f a h' | .error e => .error e := rfl
theorem bind_fm {α β : Type} (m : Heap → Except Fault (α × Heap)) (f : α → M β) (h : Heap) :
    (@bind M _ α β m f) h = match m h with | .ok (a, h') => f a h' | .error e => .error e := rfl

theorem carveState_ok {h : Heap} {b off : Nat} (a : Array UInt8) (hb : h.bytes b = some a)
    (hoff : off + 9152 ≤ a.size) (hal : ((h.baseAddr (.heap b)).toNat + off) % 64 = 0)
    (hfs : h.istates b = none) :
    carveState (.ref (.heap b) off) h = .ok (some b,
      { h with
        bytes := upd h.bytes b (some (a.extract 0 off))
        istates := upd h.istates b (some (InflateState.garbage (h.garbage (2 ^ 40 + b)))) }) := by
  simp [carveState, carveCheck, cutBytes, bind_app, bind_mf, bind_fm, hb, hoff, hal, hfs,
    SIZEOF_INFLATE_STATE, ALIGNOF_INFLATE_STATE]

theorem carveState_fault {h : Heap} {b off : Nat} (a : Array UInt8) (x : InflateState) (hb : h.bytes b = some a)
    (hoff : off + 9152 ≤ a.size) (hal : ((h.baseAddr (.heap b)).toNat + off) % 64 = 0)
    (hfs : h.istates b = some x) :
    carveState (.ref (.heap b) off) h = .error (.ub "second inflate_state in one block (not modelled)") := by
  simp [carveState, carveCheck, bind_app, bind_fm, hb, hoff, hal, hfs, SIZEOF_INFLATE_STATE,
    ALIGNOF_INFLATE_STATE, ub]

theorem alloc_ok {h : Heap} {i : Nat} (hza : (h.streams i).map ZStream.zalloc = some .zcalloc)
    (hfs : h.istates h.nextBlk = none) (hfa : h.iallocs h.nextBlk = none) (hok : h.allocOk h.nalloc = true) :
    alloc_inflate (some i) h = .ok (some h.nextBlk, allocHeap h ((h.streams i).elim .null ZStream.zfree)) := by
  obtain ⟨z, hz, hza⟩ : ∃ z, h.streams i = some z ∧ z.zalloc = .zcalloc := by
    cases e : h.streams i with
    | none => rw [e] at hza; simp at hza
    | some z => rw [e] at hza; exact ⟨z, rfl, by simpa using hza⟩
  have hpn := padsz_toNat (h.baseAddr (.heap h.nextBlk))
  generalize hP : (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat = p at hpn
  have hp : p < 64 := by omega
  have a0 : ((h.baseAddr (.heap h.nextBlk)).toNat + p) % 64 = 0 := by omega
  have a1 : ((h.baseAddr (.heap h.nextBlk)).toNat + (p + 41984)) % 8 = 0 := by omega
  have a2 : ((h.baseAddr (.heap h.nextBlk)).toNat + (p + 32832)) % 64 = 0 := by
    rw [show (h.baseAddr (.heap h.nextBlk)).toNat + (p + 32832) = (h.baseAddr (.heap h.nextBlk)).toNat + p + 64 * 513
      by omega, Nat.add_mul_mod_self_left]
    exact a0
  have f1 : (p : Int) ≤ 42112 := by omega
  have f2 : (p : Int) + 41984 ≤ 42112 := by omega
  have f3 : p ≤ 42112 := by omega
  have f4 : 0 ≤ (p : Int) + 41984 := by omega
  have f5 : p + 41984 + 32 ≤ 42112 := by omega
  have f6 : min (p + 41984) 42112 = p + 41984 := by omega
  have f7 : 0 ≤ (p : Int) + 32832 := by omega
  have f9 : p ≤ p + 41984 := by omega
  have f12 : (p : Int) ≤ (p : Int) + 41984 := by omega
  have e1 : ((p : Int) + 41984).toNat = p + 41984 := by omega
  have e2 : ((p : Int) + 32832).toNat = p + 32832 := by omega
  rw [alloc_pre]
  simp [bind_app, ldStream, hz, callZalloc, hza, ZlibNg.Zutil.zcalloc, allocB, hok, addrOf, Ptr.add,
    space_get_heap, HINT_ALIGNED_64, Ptr.castAligned, carveAllocs, carveCheck, cutBytes, ldAllocs, stAllocs,
    Heap.iallocsOf, SIZEOF_INFLATE_ALLOCS, ALIGNOF_INFLATE_ALLOCS,
    hP, a0, a1, hfa, f1, f2, f3, f4, f5, f6, f7, f9, f12, upd_upd, e1, e2, bind_mf, bind_fm]
  rw [carveState_ok ((Array.ofFn (n := 42112) fun j => (Junk.of (h.garbage h.nalloc j.val) : UInt8)).extract 0
    (p + 41984))]
  · simp [-Nat.reducePow, -Array.extract_extract, upd_upd, allocHeap, hP]
  · simp
  · simp; omega
  · exact a2
  · simpa using hfs

/-- `alloc_inflate` faults when the heap records a typed object in the block it gets (`FreshBlocks` fails there). -/
theorem alloc_fault {h : Heap} {i : Nat} (hza : (h.streams i).map ZStream.zalloc = some .zcalloc)
    (hok : h.allocOk h.nalloc = true) (hx : h.istates h.nextBlk ≠ none ∨ h.iallocs h.nextBlk ≠ none) :
    ∃ e, alloc_inflate (some i) h = .error e := by
  obtain ⟨z, hz, hza⟩ : ∃ z, h.streams i = some z ∧ z.zalloc = .zcalloc := by
    cases e : h.streams i with
    | none => rw [e] at hza; simp at hza
    | some z => rw [e] at hza; exact ⟨z, rfl, by simpa using hza⟩
  have hpn := padsz_toNat (h.baseAddr (.heap h.nextBlk))
  generalize hP : (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat = p at hpn
  have hp : p < 64 := by omega
  have a0 : ((h.baseAddr (.heap h.nextBlk)).toNat + p) % 64 = 0 := by omega
  have a1 : ((h.baseAddr (.heap h.nextBlk)).toNat + (p + 41984)) % 8 = 0 := by omega
  have a2 : ((h.baseAddr (.heap h.nextBlk)).toNat + (p + 32832)) % 64 = 0 := by
    rw [show (h.baseAddr (.heap h.nextBlk)).toNat + (p + 32832) = (h.baseAddr (.heap h.nextBlk)).toNat + p + 64 * 513
      by omega, Nat.add_mul_mod_self_left]
    exact a0
  have f1 : (p : Int) ≤ 42112 := by omega
  have f2 : (p : Int) + 41984 ≤ 42112 := by omega
  have f3 : p ≤ 42112 := by omega
  have f4 : 0 ≤ (p : Int) + 41984 := by omega
  have f5 : p + 41984 + 32 ≤ 42112 := by omega
  have f6 : min (p + 41984) 42112 = p + 41984 := by omega
  have f7 : 0 ≤ (p : Int) + 32832 := by omega
  have f9 : p ≤ p + 41984 := by omega
  have f12 : (p : Int) ≤ (p : Int) + 41984 := by omega
  have e1 : ((p : Int) + 41984).toNat = p + 41984 := by omega
  have e2 : ((p : Int) + 32832).toNat = p + 32832 := by omega
  cases hfa : h.iallocs h.nextBlk with
  | some x =>
    rw [alloc_pre]
    simp [bind_app, ldStream, hz, callZalloc, hza, ZlibNg.Zutil.zcalloc, allocB, hok, addrOf, Ptr.add,
      space_get_heap, HINT_ALIGNED_64, Ptr.castAligned, carveAllocs, carveCheck,
      SIZEOF_INFLATE_ALLOCS, ALIGNOF_INFLATE_ALLOCS, hP, a0, a1, hfa, f1, f2, f3, f4, f5, e1, bind_fm, ub]
  | none =>
    obtain ⟨x, hfs⟩ : ∃ x, h.istates h.nextBlk = some x := by
      rcases hx with hx | hx
      · cases e : h.istates h.nextBlk with
        | none => exact absurd e hx
        | some x => exact ⟨x, rfl⟩
      · exact absurd hfa hx
    rw [alloc_pre]
    simp [bind_app, ldStream, hz, callZalloc, hza, ZlibNg.Zutil.zcalloc, allocB, hok, addrOf, Ptr.add,
      space_get_heap, HINT_ALIGNED_64, Ptr.castAligned, carveAllocs, carveCheck, cutBytes, ldAllocs, stAllocs,
      Heap.iallocsOf, SIZEOF_INFLATE_ALLOCS, ALIGNOF_INFLATE_ALLOCS,
      hP, a0, a1, hfa, f1, f2, f3, f4, f5, f6, f7, f9, f12, upd_upd, e1, e2, bind_mf, bind_fm]
    rw [carveState_fault ((Array.ofFn (n := 42112) fun j => (Junk.of (h.garbage h.nalloc j.val) : UInt8)).extract 0
      (p + 41984)) x]
    · simp
    · simp
    · simp; omega
    · exact a2
    · simpa using hfs

theorem alloc_fail {h : Heap} {i : Nat} (hza : (h.streams i).map ZStream.zalloc = some .zcalloc)
    (hok : h.allocOk h.nalloc = false) :
    alloc_inflate (some i) h = .ok (none, { h with nalloc := h.nalloc + 1 }) := by
  obtain ⟨z, hz, hza⟩ : ∃ z, h.streams i = some z ∧ z.zalloc = .zcalloc := by
    cases e : h.streams i with
    | none => rw [e] at hza; simp at hza
    | some z => rw [e] at hza; exact ⟨z, rfl, by simpa using hza⟩
  rw [alloc_pre]
  simp [bind_app, ldStream, hz, callZalloc, hza, ZlibNg.Zutil.zcalloc, allocB, hok]

/-- The stream after the allocator set-up of `inflateInit2`. -/
def initZ (z : ZStream) : ZStream :=
  { z with msg := .null, zalloc := .zcalloc, «opaque» := if z.zalloc = .null then .null else z.«opaque»,
           zfree := .zcfree }

theorem init2_pre {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree) (wb : Int32) :
    inflateInit2 (some i) wb h = (do
      let alloc_bufs ← alloc_inflate (some i)
      if alloc_bufs == none then return Z_MEM_ERROR
      let a ← ldAllocs alloc_bufs
      let st ← a.state.get
      let w ← (← ldAllocs alloc_bufs).window.get
      wrS st fun s => { s with window := .val w }
      wrS st fun s => { s with alloc_bufs := .val alloc_bufs }
      wrS st fun s => { s with wbufsize := ((1 : UInt32) <<< 15) + 64 }
      wrZ (some i) fun z => { z with state := st }
      wrS st fun s => { s with strm := .val (some i) }
      wrS st fun s => { s with mode := HEAD }
      let ret ← inflateReset2 (some i) wb
      if ret != Z_OK then
        free_inflate (some i)
      return ret : M Int32) { h with streams := upd h.streams i (some (initZ z)) } := by
  rcases hza with ha | ha <;> rcases hzf with hf | hf <;>
  simp [inflateInit2, bind_app, wrZ, rdZ, ldStream, stStream, hz, ha, hf, upd_upd, initZ]

theorem garbage_codes (g : Nat → UInt64) : (InflateState.garbage g).codes.size = ENOUGH := by
  simp [InflateState.garbage]
theorem garbage_lens (g : Nat → UInt64) : (InflateState.garbage g).lens.size = 320 := by
  simp [InflateState.garbage]
theorem garbage_work (g : Nat → UInt64) : (InflateState.garbage g).work.size = 288 := by
  simp [InflateState.garbage]

/-! ### Projections of `allocHeap` -/
section
variable (h : Heap) (zf : FnPtr)
@[simp] theorem allocHeap_streams : (allocHeap h zf).streams = h.streams := rfl
@[simp] theorem allocHeap_gz : (allocHeap h zf).gzheaders = h.gzheaders := rfl
@[simp] theorem allocHeap_nextBlk : (allocHeap h zf).nextBlk = h.nextBlk + 1 := rfl
@[simp] theorem allocHeap_consts : (allocHeap h zf).consts = h.consts := rfl
@[simp] theorem allocHeap_crc : (allocHeap h zf).crcTable = h.crcTable := rfl
@[simp] theorem allocHeap_x2n : (allocHeap h zf).x2nTable = h.x2nTable := rfl
@[simp] theorem allocHeap_base : (allocHeap h zf).baseAddr = h.baseAddr := rfl
@[simp] theorem allocHeap_istates (b : Nat) : (allocHeap h zf).istates b =
    if b = h.nextBlk then some (InflateState.garbage (h.garbage (2 ^ 40 + h.nextBlk))) else h.istates b := by
  show upd h.istates h.nextBlk _ b = _
  by_cases e : b = h.nextBlk
  · subst e; simp only [upd_same, ite_true]
  · simp only [upd_ne _ _ _ _ e, e, ite_false]
@[simp] theorem allocHeap_iallocs (b : Nat) : (allocHeap h zf).iallocs b =
    if b = h.nextBlk then some ⟨.val (.ref (.heap h.nextBlk) 0), .val zf, .val (some h.nextBlk),
      .val (.ref (.heap h.nextBlk) (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat)⟩ else h.iallocs b := by
  show upd h.iallocs h.nextBlk _ b = _
  by_cases e : b = h.nextBlk
  · subst e; simp only [upd_same, ite_true]
  · simp only [upd_ne _ _ _ _ e, e, ite_false]
theorem allocHeap_bytes_ne (b : Nat) (e : b ≠ h.nextBlk) : (allocHeap h zf).bytes b = h.bytes b := by
  show upd h.bytes h.nextBlk _ b = _
  exact upd_ne _ _ _ _ e
/-- The bytes of the new block. -/
def allocBytes : Array UInt8 :=
  ((Array.ofFn (n := 42112) fun j => (Junk.of (h.garbage h.nalloc j.val) : UInt8)).extract 0
    ((PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + 41984)).extract 0
    ((PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + 32832)
@[simp] theorem allocHeap_bytes_self : (allocHeap h zf).bytes h.nextBlk = some (allocBytes h) :=
  upd_same _ _ _
theorem allocBytes_size : (allocBytes h).size = (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + 32832 := by
  have := padsz_lt (h.baseAddr (.heap h.nextBlk))
  simp only [allocBytes, Array.size_extract, Array.size_ofFn]
  omega
/-- The bytes of the new block: the window, up to the state. -/
theorem allocHeap_bytes : ∃ d, (allocHeap h zf).bytes h.nextBlk = some d ∧
    d.size = (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + 32832 := by
  refine ⟨_, upd_same _ _ _, ?_⟩
  have := padsz_lt (h.baseAddr (.heap h.nextBlk))
  simp only [Array.size_extract, Array.size_ofFn]
  omega
end

/-! ## `free_inflate` -/

theorem free_run {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8} {st : InflateState}
    {al : InflateAllocs} (hz : h.streams i = some z) (hb : z.state = some b) (hd : h.bytes b = some d)
    (hst : h.istates b = some st) (hab : st.alloc_bufs = .val (some b)) (hal : h.iallocs b = some al)
    (hzf : al.zfree = .val .zcfree) (hbuf : al.buf_start = .val (.ref (.heap b) 0)) :
    free_inflate (some i) h = .ok ((),
      { h with
        bytes := upd h.bytes b none
        savedPtrs := upd h.savedPtrs b none
        streams := upd h.streams i (some { z with state := none }) }) := by
  simp [free_inflate, ZlibNg.Inflate.stateOf, rdZ, bind_app, ldStream, hz, hb, ldState, Heap.istate, hd, hst, hab,
    Ival.get, ldAllocs, Heap.iallocsOf, hal, callZfree, hzf, hbuf, ZlibNg.Zutil.zcfree, freeB, wrZ, stStream]

/-! ## Frames of the allocating calls -/

/-- From `h` to `h'` only stream `i` and blocks from `h.nextBlk` on changed. -/
structure Fr (h h' : Heap) (i : Nat) : Prop where
  streams : ∀ j, j ≠ i → h'.streams j = h.streams j
  gz : h'.gzheaders = h.gzheaders
  old : ∀ b, b < h.nextBlk → h'.istates b = h.istates b ∧ h'.iallocs b = h.iallocs b ∧ h'.bytes b = h.bytes b
  consts : h'.consts = h.consts
  crc : h'.crcTable = h.crcTable
  x2n : h'.x2nTable = h.x2nTable
  base : h'.baseAddr = h.baseAddr
  next : h.nextBlk ≤ h'.nextBlk

theorem Fr.refl (h : Heap) (i : Nat) : Fr h h i :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem Fr.frame {h h' : Heap} {i : Nat} (f : Fr h h' i) : Frame h h' [i] [] [] [] := by
  refine ⟨fun j hj => f.streams j (by simpa using hj), fun k _ => by rw [f.gz], fun b hb _ => ⟨(f.old b hb).1,
    (f.old b hb).2.1⟩, fun b hb _ data hd => ⟨data, by rw [(f.old b hb).2.2, hd], rfl, fun _ _ _ => rfl⟩,
    fun b hb _ hn => by rw [(f.old b hb).2.2, hn], f.consts, f.crc, f.x2n, f.base, f.next⟩

theorem view_codes (st : InflateState) : (view st).codes_size = st.codes.size := rfl
theorem view_lens (st : InflateState) : (view st).lens_size = st.lens.size := rfl
theorem view_work (st : InflateState) : (view st).work_size = st.work.size := rfl

section
open ZlibNgF.Proof.InflateReset
variable (b : Nat) (st : InflateState) (wrap : Int32) (wb : UInt32)
theorem rkS_codes : (rkS b st).codes = st.codes := rfl
theorem rkS_lens : (rkS b st).lens = st.lens := rfl
theorem rkS_work : (rkS b st).work = st.work := rfl
theorem rS_codes : (rS st).codes = st.codes := rfl
theorem rS_lens : (rS st).lens = st.lens := rfl
theorem rS_work : (rS st).work = st.work := rfl
theorem r2S_codes : (r2S st wrap wb).codes = st.codes := rfl
theorem r2S_lens : (r2S st wrap wb).lens = st.lens := rfl
theorem r2S_work : (r2S st wrap wb).work = st.work := rfl
end

/-! ## `inflateInit2` -/

/-- The state that `inflateInit2` sets up before `inflateReset2`. -/
def initS (g : Nat → UInt64) (i b p : Nat) : InflateState :=
  { InflateState.garbage g with
    window := .val (.ref (.heap b) p)
    alloc_bufs := .val (some b)
    wbufsize := ((1 : UInt32) <<< 15) + 64
    strm := .val (some i)
    mode := HEAD }

theorem initS_codes (g : Nat → UInt64) (i b p : Nat) : (initS g i b p).codes = (InflateState.garbage g).codes := by
  simp only [initS]
theorem initS_lens (g : Nat → UInt64) (i b p : Nat) : (initS g i b p).lens = (InflateState.garbage g).lens := by
  simp only [initS]
theorem initS_work (g : Nat → UInt64) (i b p : Nat) : (initS g i b p).work = (InflateState.garbage g).work := by
  simp only [initS]

theorem init2_ok {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree)
    (hfs : h.istates h.nextBlk = none) (hfa : h.iallocs h.nextBlk = none) (wb : Int32) :
    ∃ r h', inflateInit2 (some i) wb h = .ok (r, h') ∧ Fr h h' i ∧ (r = Z_OK → Inv h' (some i)) ∧
      (h.allocOk h.nalloc = true → wb = 15 → r = Z_OK) ∧
      (r = Z_OK → ∃ z' st', h'.streams i = some z' ∧ z'.state = some h.nextBlk ∧ h'.istate h.nextBlk = some st' ∧
        st'.head = .val none ∧ z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in) ∧
      ∃ z', h'.streams i = some z' := by
  rw [init2_pre hz hza hzf wb]
  have hza0 : (({ h with streams := upd h.streams i (some (initZ z)) } : Heap).streams i).map ZStream.zalloc =
      some .zcalloc := by simp [initZ]
  cases hok : h.allocOk h.nalloc
  · refine ⟨Z_MEM_ERROR, { h with streams := upd h.streams i (some (initZ z)), nalloc := h.nalloc + 1 }, ?_, ?_,
      fun e => absurd e (by decide), fun e => absurd e (by simp), fun e => absurd e (by decide), ⟨_, by simp; rfl⟩⟩
    · simp only [bind_app, alloc_fail hza0 hok]; rfl
    · exact ⟨fun j hj => by simp [hj], rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  · simp only [bind_app, alloc_ok hza0 hfs hfa hok]
    let H0 : Heap := { h with streams := upd h.streams i (some (initZ z)) }
    let b := h.nextBlk
    let p := (PADSZ (h.baseAddr (.heap b)) 64).toNat
    let z2 : ZStream := { initZ z with state := some b }
    let st2 := initS (h.garbage (2 ^ 40 + b)) i b p
    let H2 := setZS (allocHeap H0 .zcfree) i z2 b st2
    have L2 : Live H2 i z2 b st2 := by
      refine ⟨by simp [H2, setZS], rfl, ⟨allocBytes H0, by simp [H2, setZS, H0, b]⟩, by simp [H2, setZS],
        by simp [z2, initZ],
        by simp [z2, initZ], ⟨b, rfl⟩, rfl, by show HEAD ≤ HEAD; decide, by show HEAD ≤ SYNC; decide⟩
    rcases InflateReset.reset2_run L2 wb with e | ⟨wrap, wb', hwb, e⟩
    · have hne : wb ≠ 15 := by
        intro hw; subst hw
        obtain ⟨H, eH⟩ := InflateReset.reset2_15 L2
        rw [eH] at e
        simp [Z_OK, Z_STREAM_ERROR] at e
      simp [-Nat.reducePow, H2, setZS, z2, st2, initS, H0, b, p, upd_upd, initZ] at e
      simp [-Nat.reducePow, ldAllocs, Heap.iallocsOf, Ival.get, wrS, ldState, stState, Heap.istate, wrZ, ldStream,
        stStream, upd_upd, initZ, e, Z_STREAM_ERROR, Z_OK, free_inflate, ZlibNg.Inflate.stateOf, rdZ, callZfree,
        ZlibNg.Zutil.zcfree, freeB]
      refine ⟨_, _, ⟨rfl, rfl⟩, ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, by simp⟩,
        by intro e; exact absurd e (by decide),
        fun hw => absurd hw hne, fun e => absurd e (by decide), ⟨_, by simp; rfl⟩⟩
      · intro j hj; simp [hj]
      · intro b' hb'
        have ne : b' ≠ h.nextBlk := Nat.ne_of_lt hb'
        simp [-Nat.reducePow, ne, allocHeap_bytes_ne]
    · let al : InflateAllocs := ⟨.val (.ref (.heap b) 0), .val .zcfree, .val (some b), .val (.ref (.heap b) p)⟩
      let st4 := InflateReset.rkS b (InflateReset.rS
        (InflateReset.r2S st2 wrap wb'))
      let z4 := InflateReset.rkZ z2 wrap
      obtain ⟨Hf, hHf⟩ : ∃ Hf, Hf = setZS H2 i z4 b st4 := ⟨_, rfl⟩
      rw [← hHf] at e
      have hinv : Inv Hf (some i) := by
        rw [hHf]
        have hal : H2.iallocsOf b = some al := by
          simp [Heap.iallocsOf, H2, setZS, H0, b, al, p]
        refine InflateReset.inv_setZS rfl ⟨allocBytes H0, by simp [H2, setZS, H0, b]⟩ hal ?_
        have hsz := allocBytes_size H0
        refine InflateReset.core_rkS (z := z2) ?_ rfl rfl hwb hwb (by show (0 : UInt32) ≤ 32768; decide) (UInt32.le_refl _)
          (Or.inl rfl) (UInt32.le_refl _) (fun _ => rfl)
        exact {
          zalloc := rfl
          zfree := rfl
          strm := rfl
          alloc_bufs := rfl
          al_state := rfl
          al_zfree := rfl
          al_buf := rfl
          window := ⟨p, allocBytes H0, rfl, rfl, by simp [H2, setZS, H0, b], by
            rw [hsz]; show p + 32832 ≤ (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + 32832; exact Nat.le_refl _⟩
          wbufsize := rfl
          mode_lo := by show HEAD ≤ HEAD; decide
          mode_hi := by show HEAD ≤ SYNC; decide
          codes_size := by
            simp only [st2, view_codes, rS_codes, r2S_codes, initS_codes, garbage_codes]
          lens_size := by
            simp only [st2, view_lens, rS_lens, r2S_lens, initS_lens, garbage_lens]
          work_size := by
            simp only [st2, view_work, rS_work, r2S_work, initS_work, garbage_work] }
      have hhead : ∃ z' st', Hf.streams i = some z' ∧ z'.state = some h.nextBlk ∧ Hf.istate h.nextBlk = some st' ∧
          st'.head = .val none ∧ z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in := by
        have hby : Hf.bytes h.nextBlk = some (allocBytes H0) := by
          rw [hHf]; simp [H2, setZS, H0, b]
        refine ⟨z4, st4, by rw [hHf]; simp [setZS], rfl, ?_, rfl, rfl, rfl⟩
        show (match Hf.bytes h.nextBlk with | some _ => Hf.istates h.nextBlk | none => none) = some st4
        rw [hby]; rw [hHf]; simp [setZS, b]
      simp [-Nat.reducePow, H2, setZS, z2, st2, initS, H0, b, p, upd_upd, initZ] at e
      simp [-Nat.reducePow, ldAllocs, Heap.iallocsOf, Ival.get, wrS, ldState, stState, Heap.istate, wrZ, ldStream,
        stStream, upd_upd, initZ, e, Z_OK]
      refine ⟨_, _, ⟨rfl, rfl⟩, ?_, fun _ => hinv, fun _ => rfl, fun _ => by obtain ⟨z1, s1, a1, a2, a3, a4, a5, a6⟩ := hhead; exact ⟨z1, a1, a2, s1, a3, a4, a5, a6⟩,
        by obtain ⟨z1, s1, a1, -⟩ := hhead; exact ⟨z1, a1⟩⟩
      rw [hHf]
      refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, by simp [H2, setZS, H0]⟩
      · intro j hj; simp [H2, setZS, hj, H0]
      · intro b' hb'
        have ne : b' ≠ h.nextBlk := Nat.ne_of_lt hb'
        simp [-Nat.reducePow, H2, setZS, H0, b, ne, allocHeap_bytes_ne]

/-- A successful `inflateInit2` leaves the structural invariant, on every heap (on a heap where `FreshBlocks` fails at
the new block, the call faults). -/
theorem init2_inv {h h' : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree) (wb : Int32)
    (e : inflateInit2 (some i) wb h = .ok (Z_OK, h')) : Inv h' (some i) := by
  by_cases hx : h.istates h.nextBlk = none ∧ h.iallocs h.nextBlk = none
  · obtain ⟨r, h'', e', _, hinv, _⟩ := init2_ok hz hza hzf hx.1 hx.2 wb
    rw [e'] at e
    obtain ⟨rfl, rfl⟩ : r = Z_OK ∧ h'' = h' := by simpa using e
    exact hinv rfl
  · exfalso
    rw [init2_pre hz hza hzf wb] at e
    have hza0 : (({ h with streams := upd h.streams i (some (initZ z)) } : Heap).streams i).map ZStream.zalloc =
        some .zcalloc := by simp [initZ]
    cases hok : h.allocOk h.nalloc
    · simp only [bind_app, alloc_fail hza0 hok] at e
      simp [Z_MEM_ERROR, Z_OK] at e
    · have hx' : ({ h with streams := upd h.streams i (some (initZ z)) } : Heap).istates h.nextBlk ≠ none ∨
          ({ h with streams := upd h.streams i (some (initZ z)) } : Heap).iallocs h.nextBlk ≠ none := by
        by_cases a : h.istates h.nextBlk = none
        · exact Or.inr fun b => hx ⟨a, b⟩
        · exact Or.inl a
      obtain ⟨err, he⟩ := alloc_fault hza0 hok hx'
      simp only [bind_app, he] at e
      cases e

end ZlibNgF.Proof.InflateAlloc
