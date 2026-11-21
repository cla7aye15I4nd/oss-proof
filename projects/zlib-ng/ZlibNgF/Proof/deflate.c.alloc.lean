import ZlibNgF.Proof.«deflate.c.invariant»
import ZlibNgF.Proof.«public-inflate-init»
import ZlibNgF.Proof.«chunkset.mem»

/-!
# `alloc_deflate` (`ZlibNgF`)

The symbolic run of `alloc_deflate` for every `windowBits` (9..15 after `deflateInit2`'s adjustment) and every
`lit_bufsize` (`1 << (memLevel + 6)`, 128..32768), every `baseAddr` and garbage oracle. The `int` size computations
are evaluated generically (`alloc_pre`): with `w = 1 << windowBits`, the window part is `dWS w = MAX(2 * w, 32768)`,
then `prev` (`2 * w` bytes), `head` (131072 bytes), `pending_buf` (`4 * lit_bufsize + 9` bytes, padded to
`+ 64`), the `deflate_state` (5440 bytes) and the `deflate_allocs` record, and `total_size` is 128 bytes past the
state. The run on the heap (`alloc_ok`, `alloc_fail`, `alloc_fault`) goes through `AH`, the heap with the new block
and the two typed-object tables as parameters, so the block's bytes stay a variable and are never normalised.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateAlloc
open C ZlibNg.Inflate ZlibNg.Deflate

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : ite c a b = a := by simp [h]
theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : ite c a b = b := by simp [h]

theorem pure_bind_M {α β : Type} (a : α) (f : α → M β) : (pure a >>= f : M β) = f a := rfl

theorem chk_eq {v : Int} (x : Int32) (hx : x.toInt = v) : chkI32 v = pure x := by
  subst hx
  have := x.toInt_lt; have := x.le_toInt
  simp only [chkI32]; rw [ite_t (by constructor <;> omega)]; simp [Int32.ofInt_toInt]

theorem i32_ofNat_toInt {k : Nat} (h : k < 2 ^ 31) : (Int32.ofNat k).toInt = k := Int32.toInt_ofNat_of_lt h

theorem u32_toInt32_toInt (x : UInt32) (h : x.toNat < 2^31) : x.toInt32.toInt = x.toNat := by
  simp only [UInt32.toInt32, Int32.toInt]
  rw [BitVec.toInt_eq_toNat_of_lt (by show 2 * x.toNat < 2^32; omega)]; rfl

theorem i32_u64_toNat (x : Int32) (h0 : 0 ≤ x.toInt) : x.toInt64.toUInt64.toNat = x.toInt.toNat := by
  rw [Int64.toNat_toUInt64_of_le (by rw [Int64.le_iff_toInt_le]; simpa using h0), Int32.toNatClampNeg_toInt64]; rfl

theorem pad64_toInt (x : Int32) (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 2 ^ 30) :
    (PAD_64 x).toInt = x.toInt + ((64 - x.toInt.toNat % 64) % 64 : Nat) := by
  unfold PAD_64 PADSZ
  have e := i32_u64_toNat x h0
  have hm : x.toInt64.toUInt64 % 64 ≤ 64 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; show _ % 64 ≤ 64; omega
  rw [u32_toInt32_toInt]
  · rw [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ hm, UInt64.toNat_mod, e]
    simp only [UInt64.reduceToNat]
    omega
  · rw [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ hm, UInt64.toNat_mod, e]
    simp only [UInt64.reduceToNat]
    omega

theorem pad16_toInt (x : Int32) (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 2 ^ 30) :
    (PAD_16 x).toInt = x.toInt + ((16 - x.toInt.toNat % 16) % 16 : Nat) := by
  unfold PAD_16 PADSZ
  have e := i32_u64_toNat x h0
  have hm : x.toInt64.toUInt64 % 16 ≤ 16 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; show _ % 16 ≤ 16; omega
  rw [u32_toInt32_toInt]
  · rw [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ hm, UInt64.toNat_mod, e]
    simp only [UInt64.reduceToNat]
    omega
  · rw [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ hm, UInt64.toNat_mod, e]
    simp only [UInt64.reduceToNat]
    omega

/-- The window part `W_BUF_SIZE` of `alloc_deflate` for a window of `w` bytes. -/
def dWS (w : Nat) : Nat := if 2 * w > 32768 then 2 * w else 32768

/-- `alloc_deflate` with its sizes evaluated, for a window of `w = 2^n` bytes (`9 ≤ n ≤ 15`) and `lit_bufsize = l`
(`128 ≤ l ≤ 32768`, a multiple of 16): the window at 0, `prev` at `dWS w`, `head` at `dWS w + 2w`, `pending_buf`
at `dWS w + 2w + 131072`, the state at `dWS w + 2w + 131072 + 4l + 64`, the allocation record 5440 bytes further,
and `total_size` 128 bytes beyond that. -/
theorem alloc_pre (s : StreamPtr) (wb lb : Int32) (n l : Nat) (hn : wb.toInt = n) (hn1 : 9 ≤ n) (hn2 : n ≤ 15)
    (hl : lb.toInt = l) (hl1 : 128 ≤ l) (hl2 : l ≤ 32768) (hl3 : l % 16 = 0) :
    alloc_deflate s wb lb = (do
      let z ← ldStream s
      let original_buf ← callZalloc z.zalloc z.«opaque» 1
        (UInt32.ofNat (dWS (2 ^ n) + 2 * 2 ^ n + 131072 + 4 * l + 64 + 5440 + 128))
      if original_buf == .null then return none
      let ob ← addrOf original_buf
      let buff ← HINT_ALIGNED_64 (← original_buf.add (Int.ofNat (PADSZ ob 64).toNat))
      let alloc_bufs ← carveDAllocs (← buff.add ((dWS (2 ^ n) + 2 * 2 ^ n + 131072 + 4 * l + 64 + 5440 : Nat) : Int))
      let a ← ldDAllocs alloc_bufs
      stDAllocs alloc_bufs { a with buf_start := .val original_buf }
      let z ← ldStream s
      let a ← ldDAllocs alloc_bufs
      stDAllocs alloc_bufs { a with zfree := .val z.zfree }
      let w ← HINT_ALIGNED_64 (← buff.add 0)
      let a ← ldDAllocs alloc_bufs
      stDAllocs alloc_bufs { a with window := .val w }
      let p ← HINT_ALIGNED_64 (← buff.add ((dWS (2 ^ n) : Nat) : Int))
      let a ← ldDAllocs alloc_bufs
      stDAllocs alloc_bufs { a with prev := .val p }
      let hd ← HINT_ALIGNED_64 (← buff.add ((dWS (2 ^ n) + 2 * 2 ^ n : Nat) : Int))
      let a ← ldDAllocs alloc_bufs
      stDAllocs alloc_bufs { a with head := .val hd }
      let pb ← HINT_ALIGNED_64 (← buff.add ((dWS (2 ^ n) + 2 * 2 ^ n + 131072 : Nat) : Int))
      let a ← ldDAllocs alloc_bufs
      stDAllocs alloc_bufs { a with pending_buf := .val pb }
      let sp ← carveDState (← HINT_ALIGNED_16 (← buff.add ((dWS (2 ^ n) + 2 * 2 ^ n + 131072 + 4 * l + 64 : Nat) : Int)))
      let a ← ldDAllocs alloc_bufs
      stDAllocs alloc_bufs { a with state := .val sp }
      Ptr.memset (← (← ldDAllocs alloc_bufs).prev.get) 0 (2 * 2 ^ n)
      return alloc_bufs : M DAllocsPtr) := by
  have p15 : 2 ^ n ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hn2
  have p9 : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn1
  have m64 : 2 ^ n % 64 = 0 := by
    have : 2 ^ n = 2 ^ (n - 6) * 2 ^ 6 := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; simp
  have ws1 : dWS (2 ^ n) % 64 = 0 := by unfold dWS; split <;> omega
  have ws2 : dWS (2 ^ n) ≤ 65536 := by unfold dWS; split <;> omega
  have e1 : shlI32 1 wb = pure (Int32.ofNat (2 ^ n)) := by
    unfold shlI32
    have : ¬ ((1 : Int32) < 0 || wb < 0 || wb ≥ 32) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, hn]
      simp; omega
    rw [ite_f this]
    refine chk_eq _ ?_
    rw [i32_ofNat_toInt (by omega)]
    have : wb.toNatClampNeg = n := by simp [Int32.toNatClampNeg, hn]
    rw [this]; simp
  have hW := i32_ofNat_toInt (k := 2 ^ n) (by omega)
  have pv : (PAD_64 0).toInt = 0 := by decide
  generalize 2 ^ n = w at *
  have i1 := i32_ofNat_toInt (k := 2 * w) (by omega)
  have i2 := i32_ofNat_toInt (k := 4 * l + 9) (by omega)
  have i3 := i32_ofNat_toInt (k := dWS w) (by omega)
  have e4 : PENDING_BUF_SIZE lb = pure (Int32.ofNat (4 * l + 9)) := by
    unfold PENDING_BUF_SIZE
    rw [chk_eq (Int32.ofNat (4 * l)) (by rw [i32_ofNat_toInt (by omega), hl]; simp [LIT_BUFS]; omega), pure_bind_M,
      chk_eq _ (by rw [i2, i32_ofNat_toInt (by omega)]; simp [PENDING_BUF_PAD]; omega)]
  have hIf : (if Int32.ofNat (2 * w) > 32768 then Int32.ofNat (2 * w) else 32768) = Int32.ofNat (dWS w) := by
    unfold dWS
    by_cases c : 2 * w > 32768
    · rw [ite_t c, ite_t (by rw [GT.gt, Int32.lt_iff_toInt_lt, i1]; simp; omega)]
    · rw [ite_f c, ite_f (by rw [GT.gt, Int32.lt_iff_toInt_lt, i1]; simp; omega)]; rfl
  simp only [alloc_deflate, e1, pure_bind_M, hW, e4]
  rw [chk_eq (Int32.ofNat (2 * w)) (by rw [i1]; push_cast; rfl), pure_bind_M]
  rw [chk_eq (Int32.ofNat (2 * w)) (by rw [i1]; push_cast; omega), pure_bind_M]
  simp only [hIf, pv, i3]
  generalize hD : dWS w = D at *
  have hp : ∀ k, k % 64 = 0 → k < 2 ^ 30 → (PAD_64 (Int32.ofNat k)).toInt = k := by
    intro k hk1 hk2
    rw [pad64_toInt _ (by rw [i32_ofNat_toInt (by omega)]; omega) (by rw [i32_ofNat_toInt (by omega)]; omega),
      i32_ofNat_toInt (by omega)]
    simp [hk1]
  have hh : (HASH_SIZE.toUInt64 * 2).toUInt32.toInt32.toInt = 131072 := by decide
  have hs : SIZEOF_DEFLATE_STATE.toInt32.toInt = 5440 := by decide
  have ha : SIZEOF_DEFLATE_ALLOCS.toInt32.toInt = 56 := by decide
  have hwp : WINDOW_PAD_SIZE.toInt - 1 = 63 := by decide
  rw [chk_eq (Int32.ofNat D) (by rw [i32_ofNat_toInt (by omega)]; omega), pure_bind_M]
  rw [chk_eq (Int32.ofNat (D + 2 * w)) (by rw [hp D (by omega) (by omega), i1, i32_ofNat_toInt (by omega)]; omega),
    pure_bind_M]
  rw [chk_eq (Int32.ofNat (D + 2 * w + 131072)) (by rw [hp _ (by omega) (by omega), hh, i32_ofNat_toInt (by omega)]; omega),
    pure_bind_M]
  rw [chk_eq (Int32.ofNat (D + 2 * w + 131072 + (4 * l + 9))) (by
      rw [hp _ (by omega) (by omega), i2, i32_ofNat_toInt (by omega)]; omega), pure_bind_M]
  have hp3 : (PAD_64 (Int32.ofNat (D + 2 * w + 131072 + (4 * l + 9)))).toInt = ((D + 2 * w + 131072 + 4 * l + 64 : Nat) : Int) := by
    rw [pad64_toInt _ (by rw [i32_ofNat_toInt (by omega)]; omega) (by rw [i32_ofNat_toInt (by omega)]; omega),
      i32_ofNat_toInt (by omega)]
    simp only [Int.toNat_natCast]; omega
  rw [hp3]
  rw [chk_eq (Int32.ofNat (D + 2 * w + 131072 + 4 * l + 64 + 5440)) (by rw [hs, i32_ofNat_toInt (by omega)]; omega),
    pure_bind_M]
  have hp4 : (PAD_16 (Int32.ofNat (D + 2 * w + 131072 + 4 * l + 64 + 5440))).toInt =
      ((D + 2 * w + 131072 + 4 * l + 64 + 5440 : Nat) : Int) := by
    rw [pad16_toInt _ (by rw [i32_ofNat_toInt (by omega)]; omega) (by rw [i32_ofNat_toInt (by omega)]; omega),
      i32_ofNat_toInt (by omega)]
    simp only [Int.toNat_natCast]; omega
  rw [hp4]
  rw [chk_eq (Int32.ofNat (D + 2 * w + 131072 + 4 * l + 64 + 5440 + 56)) (by rw [ha, i32_ofNat_toInt (by omega)]; omega),
    pure_bind_M]
  rw [chk_eq (Int32.ofNat (D + 2 * w + 131072 + 4 * l + 64 + 5440 + 56 + 63)) (by
      rw [hwp, i32_ofNat_toInt (by omega), i32_ofNat_toInt (by omega)]; omega), pure_bind_M]
  have hp6 : (PAD_64 (Int32.ofNat (D + 2 * w + 131072 + 4 * l + 64 + 5440 + 56 + 63))).toUInt32 =
      UInt32.ofNat (D + 2 * w + 131072 + 4 * l + 64 + 5440 + 128) := by
    have e := pad64_toInt (Int32.ofNat (D + 2 * w + 131072 + 4 * l + 64 + 5440 + 56 + 63))
      (by rw [i32_ofNat_toInt (by omega)]; omega) (by rw [i32_ofNat_toInt (by omega)]; omega)
    rw [i32_ofNat_toInt (by omega)] at e
    simp only [Int.toNat_natCast] at e
    apply UInt32.toNat_inj.mp
    rw [Int32.toNat_toUInt32_of_le, UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
    · show (PAD_64 _).toInt.toNat = _
      rw [e]; omega
    · rw [Int32.le_iff_toInt_le, e]; simp only [Int32.toInt_zero]; omega
  rw [hp6, hp D (by omega) (by omega), hp _ (by omega) (by omega), hp _ (by omega) (by omega)]
  have hc : (Int32.ofNat (2 * w)).toNatClampNeg = 2 * w := by
    show (Int32.ofNat (2 * w)).toInt.toNat = 2 * w
    rw [i1]; exact Nat.add_zero (Nat.mul 2 w)
  rw [hc]
  done

open ZlibNgF.Proof.InflateAlloc (padsz_toNat padsz_lt space_get_heap bind_ff bind_mf bind_fm)
open ZlibNgF.Proof.InflateInv (upd_upd ldStream_app)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.ChunkMem (fillFold fillFold_size fillFold_get memset_loop modify_heap mem_range'_bound)

/-- The `deflate_allocs` record that `alloc_deflate` fills in block `b`. -/
def dAllocRec (b p D w : Nat) (zf : FnPtr) : DeflateAllocs :=
  ⟨.val (.ref (.heap b) 0), .val zf, .val (some b), .val (.ref (.heap b) p),
    .val (.ref (.heap b) (p + D + 2 * w + 131072)), .val (.ref (.heap b) (p + D)),
    .val (.ref (.heap b) (p + D + 2 * w))⟩

/-- `h` after the allocation of block `h.nextBlk` by `alloc_deflate`, with the bytes `X` of the block and the tables
`Y` of `deflate_allocs` records and `Z` of `deflate_state` objects. -/
def AH (h : Heap) (X : Array UInt8) (Y : Tbl (Option DeflateAllocs)) (Z : Tbl (Option DeflateState)) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some X)
    savedPtrs := upd h.savedPtrs h.nextBlk none
    nextBlk := h.nextBlk + 1
    nalloc := h.nalloc + 1
    dallocs := Y
    dstates := Z }

section AH
variable (h : Heap) (X : Array UInt8) (Y : Tbl (Option DeflateAllocs)) (Z : Tbl (Option DeflateState))
@[simp] theorem AH_bytes : (AH h X Y Z).bytes h.nextBlk = some X := upd_same _ _ _
@[simp] theorem AH_dallocs : (AH h X Y Z).dallocs = Y := rfl
@[simp] theorem AH_dstates : (AH h X Y Z).dstates = Z := rfl
@[simp] theorem AH_base : (AH h X Y Z).baseAddr = h.baseAddr := rfl
@[simp] theorem AH_streams : (AH h X Y Z).streams = h.streams := rfl
end AH

syntax "dstep " tacticSeq : tactic
macro_rules
  | `(tactic| dstep $t) => `(tactic| (refine Sat.bind (Sat.of_eq (a := ?_) (H' := ?_) ?e ?_); (case e => $t); all_goals (try dsimp only)))

/-! ### Steps of the run on `AH` heaps -/

section
variable {h : Heap} {X : Array UInt8} {Y : Tbl (Option DeflateAllocs)} {Z : Tbl (Option DeflateState)}

theorem add_AH {off : Nat} (k : Nat) (hk : off + k ≤ X.size) :
    Ptr.add (Ptr.ref (BRef.heap h.nextBlk) off) (k : Int) (AH h X Y Z) =
      .ok (.ref (.heap h.nextBlk) (off + k), AH h X Y Z) := by
  simp only [Ptr.add, space_get_heap, AH_bytes]
  rw [ite_t (by omega), show ((off : Int) + k).toNat = off + k by omega]

theorem add0_AH (k : Nat) (hk : k ≤ X.size) :
    Ptr.add (Ptr.ref (BRef.heap h.nextBlk) 0) (k : Int) (AH h X Y Z) = .ok (.ref (.heap h.nextBlk) k, AH h X Y Z) := by
  have := add_AH (h := h) (X := X) (Y := Y) (Z := Z) (off := 0) k (by omega)
  rwa [Nat.zero_add] at this

theorem cast_heap {h : Heap} {r : BRef} {off al : Nat} (hal : al ∣ 2 ^ 64)
    (ha : ((h.baseAddr r).toNat + off) % al = 0) :
    Ptr.castAligned (.ref r off) al h = .ok (.ref r off, h) := by
  have : ((h.baseAddr r).toNat + off) % 18446744073709551616 % al = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by simpa using hal)]; exact ha
  simp [Ptr.castAligned, bind_app, addrOf, this]

theorem cast_AH {off al : Nat} (hal : al ∣ 2 ^ 64)
    (ha : ((h.baseAddr (.heap h.nextBlk)).toNat + off) % al = 0) :
    Ptr.castAligned (.ref (.heap h.nextBlk) off) al (AH h X Y Z) = .ok (.ref (.heap h.nextBlk) off, AH h X Y Z) :=
  cast_heap hal ha

theorem ldStream_AH {i : Nat} {z : ZStream} (hz : h.streams i = some z) :
    ldStream (some i) (AH h X Y Z) = .ok (z, AH h X Y Z) := ldStream_app hz

/-- The `deflate_allocs` record right after its carve. -/
def U0 : DeflateAllocs := ⟨.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit⟩

theorem carveDAllocs_AH {off : Nat} (hY : Y h.nextBlk = none)
    (hoff : off + 56 ≤ X.size) (hal : ((h.baseAddr (.heap h.nextBlk)).toNat + off) % 8 = 0) :
    carveDAllocs (.ref (.heap h.nextBlk) off) (AH h X Y Z) =
      .ok (some h.nextBlk, AH h (X.extract 0 off) (upd Y h.nextBlk (some U0)) Z) := by
  simp [carveDAllocs, carveCheck, cutBytes, bind_app, bind_mf, bind_fm, hoff, hal, hY,
    SIZEOF_DEFLATE_ALLOCS, ALIGNOF_DEFLATE_ALLOCS, AH, upd_upd, U0]

theorem carveDState_AH {off : Nat} (hZ : Z h.nextBlk = none)
    (hoff : off + 5440 ≤ X.size) (hal : ((h.baseAddr (.heap h.nextBlk)).toNat + off) % 64 = 0) :
    carveDState (.ref (.heap h.nextBlk) off) (AH h X Y Z) = .ok (some h.nextBlk,
      AH h (X.extract 0 off) Y (upd Z h.nextBlk (some (DeflateState.garbage (h.garbage (2 ^ 43 + h.nextBlk)))))) := by
  simp [carveDState, carveCheck, cutBytes, bind_app, bind_mf, bind_fm, hoff, hal, hZ,
    SIZEOF_DEFLATE_STATE, ALIGNOF_DEFLATE_STATE, AH, upd_upd]

theorem ldDAllocs_AH {al : DeflateAllocs} :
    ldDAllocs (some h.nextBlk) (AH h X (upd Y h.nextBlk (some al)) Z) =
      .ok (al, AH h X (upd Y h.nextBlk (some al)) Z) := by
  simp [ldDAllocs, Heap.dallocsOf]

theorem stDAllocs_AH {al : DeflateAllocs} (al' : DeflateAllocs) :
    stDAllocs (some h.nextBlk) al' (AH h X (upd Y h.nextBlk (some al)) Z) =
      .ok ((), AH h X (upd Y h.nextBlk (some al')) Z) := by
  simp [stDAllocs, Heap.dallocsOf, AH, upd_upd]

theorem memset_AH {off n : Nat} (hn : off + n ≤ X.size) (byte : UInt8) :
    Ptr.memset (Ptr.ref (BRef.heap h.nextBlk) off) byte n (AH h X Y Z) =
      .ok ((), AH h (fillFold byte off (List.range' 0 n) X) Y Z) := by
  simp only [Ptr.memset, space_get_heap, AH_bytes, Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, hn]
  rw [modify_heap _ _ X (AH_bytes h X Y Z), memset_loop]
  simp [AH, upd_upd]

end

theorem allocB_AH {h : Heap} (hok : h.allocOk h.nalloc = true) (T : Nat) :
    allocB T h = .ok (.ref (.heap h.nextBlk) 0,
      AH h (Array.ofFn (n := T) fun j => Junk.of (h.garbage h.nalloc j.val)) h.dallocs h.dstates) := by
  simp [allocB, hok, AH]

theorem fillFold_keep (byte : UInt8) (off : Nat) (l : List Nat) (a : Array UInt8) (k : Nat) (h : a[k]! = byte) :
    (fillFold byte off l a)[k]! = byte := by
  induction l generalizing a with
  | nil => exact h
  | cons x l ih =>
    simp only [fillFold, List.foldl_cons] at ih ⊢
    apply ih
    simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
    by_cases e : off + x = k
    · subst e
      by_cases hs : off + x < a.size
      · simp [hs]
      · simp only [getElem!_def] at h
        simpa [hs] using h
    · simp only [getElem!_def] at h; simp [e, h]

theorem fillFold_in (byte : UInt8) (off : Nat) (l : List Nat) (a : Array UInt8) (k : Nat)
    (hk : ∃ i ∈ l, off + i = k) (hs : k < a.size) : (fillFold byte off l a)[k]! = byte := by
  induction l generalizing a with
  | nil => simp at hk
  | cons x l ih =>
    simp only [fillFold, List.foldl_cons] at ih ⊢
    by_cases e : off + x = k
    · apply fillFold_keep
      subst e
      simp [Array.set!_eq_setIfInBounds, hs]
    · obtain ⟨i, hi, rfl⟩ := hk
      rcases List.mem_cons.mp hi with rfl | hi
      · exact absurd rfl e
      · exact ih _ ⟨i, hi, rfl⟩ (by simpa [Array.set!_eq_setIfInBounds] using hs)

theorem alloc_mods (B p D w l : Nat) (h : (B + p) % 64 = 0) (hD : D % 64 = 0) (hw : w % 64 = 0) (hl : l % 16 = 0) :
    (B + (p + (D + 2 * w + 131072 + 4 * l + 64 + 5440))) % 8 = 0 ∧
    (B + (p + (D + 2 * w + 131072 + 4 * l + 64))) % 64 = 0 ∧ (B + (p + D)) % 64 = 0 ∧
    (B + (p + (D + 2 * w))) % 64 = 0 ∧ (B + (p + (D + 2 * w + 131072))) % 64 = 0 ∧
    (B + (p + (D + 2 * w + 131072 + 4 * l + 64))) % 16 = 0 := by
  omega

theorem alloc_sizes (p D w l T N : Nat) (hp : p < 64) (hT : D + 2 * w + 131072 + 4 * l + 64 + 5440 + 128 = T)
    (hN : N = T) :
    p ≤ N ∧ p + (D + 2 * w + 131072 + 4 * l + 64 + 5440) ≤ N ∧
    p + (D + 2 * w + 131072 + 4 * l + 64 + 5440) + 56 ≤ N := by
  omega

theorem alloc_sizes2 (p D w l N : Nat) (hN : N = p + (D + 2 * w + 131072 + 4 * l + 64 + 5440)) :
    p + 0 ≤ N ∧ p + D ≤ N ∧ p + (D + 2 * w) ≤ N ∧ p + (D + 2 * w + 131072) ≤ N ∧
    p + (D + 2 * w + 131072 + 4 * l + 64) + 5440 ≤ N ∧
    p + D + 2 * w ≤ p + (D + 2 * w + 131072 + 4 * l + 64) ∧ p + (D + 2 * w + 131072 + 4 * l + 64) ≤ N := by
  omega

/-- The garbage `deflate_state` that `alloc_deflate` carves in block `b`. -/
abbrev gState (h : Heap) : DeflateState := DeflateState.garbage (h.garbage (2 ^ 43 + h.nextBlk))

/-- `alloc_deflate` with the default allocator when the allocation succeeds, for every window size and
`lit_bufsize` of `deflateInit2`. The bytes of the block below the state are `d`, of the size given, with `prev`
zeroed. -/
theorem alloc_ok {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) (hza : z.zalloc = .zcalloc)
    (hfs : h.dstates h.nextBlk = none) (hfa : h.dallocs h.nextBlk = none) (hok : h.allocOk h.nalloc = true)
    (wb lb : Int32) (n l : Nat) (hn : wb.toInt = n) (hn1 : 9 ≤ n) (hn2 : n ≤ 15)
    (hl : lb.toInt = l) (hl1 : 128 ≤ l) (hl2 : l ≤ 32768) (hl3 : l % 16 = 0) :
    Sat h (alloc_deflate (some i) wb lb) fun r H => r = some h.nextBlk ∧ ∃ d, H = AH h d
      (upd h.dallocs h.nextBlk (some
        (dAllocRec h.nextBlk (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat (dWS (2 ^ n)) (2 ^ n) z.zfree)))
      (upd h.dstates h.nextBlk (some (gState h))) ∧
      d.size = (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + (dWS (2 ^ n) + 2 * 2 ^ n + 131072 + 4 * l + 64) ∧
      ∀ j, j < 2 * 2 ^ n → d[(PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat + dWS (2 ^ n) + j]! = 0 := by
  rw [alloc_pre (some i) wb lb n l hn hn1 hn2 hl hl1 hl2 hl3]
  have p15 : 2 ^ n ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hn2
  have p9 : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn1
  have m64 : 2 ^ n % 64 = 0 := by
    have : 2 ^ n = 2 ^ (n - 6) * 2 ^ 6 := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; simp
  have ws1 : dWS (2 ^ n) % 64 = 0 := by unfold dWS; split <;> omega
  have ws2 : dWS (2 ^ n) ≤ 65536 := by unfold dWS; split <;> omega
  generalize 2 ^ n = w at *
  generalize dWS w = D at *
  have hpn := padsz_toNat (h.baseAddr (.heap h.nextBlk))
  generalize hP : (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat = p at hpn
  have hp : p < 64 := by omega
  have a0 : ((h.baseAddr (.heap h.nextBlk)).toNat + p) % 64 = 0 := by omega
  obtain ⟨aD8, aS, aPv, aH, aPb, aS16⟩ := alloc_mods ((h.baseAddr (.heap h.nextBlk)).toNat) p D w l a0 ws1 m64 hl3
  generalize hT : D + 2 * w + 131072 + 4 * l + 64 + 5440 + 128 = T
  have hz2 : ZlibNg.Zutil.zcalloc z.«opaque» 1 (UInt32.ofNat T) = allocB T := by
    have e : ((1 : UInt32).toUInt64 * (UInt32.ofNat T).toUInt64).toNat = T := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, UInt32.toNat_ofNat_of_lt' (by
        simp only [UInt32.size]; omega)]
      simp; omega
    simp only [ZlibNg.Zutil.zcalloc, e]
  refine Sat.bind (Sat.of_eq (ldStream_app hz) ?_)
  simp only [callZalloc, hza, hz2]
  refine Sat.bind (Sat.of_eq (allocB_AH hok T) ?_)
  simp only [show ((Ptr.ref (BRef.heap h.nextBlk) 0 : BPtr) == Ptr.null) = false from rfl, Bool.false_eq_true,
    ↓reduceIte]
  refine Sat.bind (Sat.of_eq rfl ?_)
  simp only [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero, AH_base, hP]
  have hA0 := Array.size_ofFn (n := T) (f := fun j => (Junk.of (h.garbage h.nalloc j.val) : UInt8))
  generalize (Array.ofFn (n := T) fun j => (Junk.of (h.garbage h.nalloc j.val) : UInt8)) = A0 at *
  obtain ⟨f0, f1, f2⟩ := alloc_sizes p D w l T A0.size hp hT hA0
  dstep exact add0_AH p f0
  dstep exact cast_AH (al := 64) (by decide) a0
  dstep exact add_AH (D + 2 * w + 131072 + 4 * l + 64 + 5440) f1
  dstep exact carveDAllocs_AH hfa f2 aD8
  have hA1 := Array.size_extract (xs := A0) (start := 0) (stop := p + (D + 2 * w + 131072 + 4 * l + 64 + 5440))
  generalize A0.extract 0 (p + (D + 2 * w + 131072 + 4 * l + 64 + 5440)) = A1 at *
  obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := alloc_sizes2 p D w l A1.size (by rw [hA1]; omega)
  dstep exact ldDAllocs_AH
  dstep exact stDAllocs_AH _
  dstep exact ldStream_AH hz
  dstep exact ldDAllocs_AH
  dstep exact stDAllocs_AH _
  dstep exact add_AH 0 g0
  dstep exact cast_AH (al := 64) (by decide) a0
  dstep exact ldDAllocs_AH
  dstep exact stDAllocs_AH _
  dstep exact add_AH D g1
  dstep exact cast_AH (al := 64) (by decide) aPv
  dstep exact ldDAllocs_AH
  dstep exact stDAllocs_AH _
  dstep exact add_AH (D + 2 * w) g2
  dstep exact cast_AH (al := 64) (by decide) aH
  dstep exact ldDAllocs_AH
  dstep exact stDAllocs_AH _
  dstep exact add_AH (D + 2 * w + 131072) g3
  dstep exact cast_AH (al := 64) (by decide) aPb
  dstep exact ldDAllocs_AH
  dstep exact stDAllocs_AH _
  dstep exact add_AH (D + 2 * w + 131072 + 4 * l + 64) g6
  dstep exact cast_AH (al := 16) (by decide) aS16
  dstep exact carveDState_AH hfs g4 aS
  dstep exact ldDAllocs_AH
  dstep exact stDAllocs_AH _
  dstep exact ldDAllocs_AH
  dstep exact rfl
  have hA2 := Array.size_extract (xs := A1) (start := 0) (stop := p + (D + 2 * w + 131072 + 4 * l + 64))
  generalize A1.extract 0 (p + (D + 2 * w + 131072 + 4 * l + 64)) = A2 at *
  have g7 : p + D + 2 * w ≤ A2.size := by rw [hA2]; omega
  dstep exact memset_AH g7 0
  refine Sat.pure ⟨rfl, fillFold 0 (p + D) (List.range' 0 (2 * w)) A2, ?_, ?_, ?_⟩
  · simp only [dAllocRec, gState, Nat.add_assoc]
  · rw [fillFold_size, hA2]; omega
  · intro j hj
    exact fillFold_in 0 (p + D) _ A2 (p + D + j) ⟨j, List.mem_range'.mpr ⟨j, hj, by omega⟩, rfl⟩ (by omega)

/-- `m` faults on `H`. -/
def Fl {α : Type} (H : Heap) (m : M α) : Prop := ∃ e, m H = .error e

theorem Fl.bind_sat {α β : Type} {H : Heap} {m : M α} {f : α → M β} (hm : Sat H m (fun a H' => Fl H' (f a))) :
    Fl H (m >>= f) := by
  obtain ⟨a, H1, e1, e, e2⟩ := hm
  exact ⟨e, by simp only [bind_app, e1]; exact e2⟩

theorem Fl.bind_now {α β : Type} {H : Heap} {m : M α} {f : α → M β} (hm : Fl H m) : Fl H (m >>= f) := by
  obtain ⟨e, e1⟩ := hm
  exact ⟨e, by simp only [bind_app, e1]⟩

syntax "fstep " tacticSeq : tactic
macro_rules
  | `(tactic| fstep $t) => `(tactic| (refine Fl.bind_sat (Sat.of_eq (a := ?_) (H' := ?_) ?e ?_); (case e => $t); all_goals (try dsimp only)))

theorem alloc_fail {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) (hza : z.zalloc = .zcalloc)
    (hok : h.allocOk h.nalloc = false)
    (wb lb : Int32) (n l : Nat) (hn : wb.toInt = n) (hn1 : 9 ≤ n) (hn2 : n ≤ 15)
    (hl : lb.toInt = l) (hl1 : 128 ≤ l) (hl2 : l ≤ 32768) (hl3 : l % 16 = 0) :
    alloc_deflate (some i) wb lb h = .ok (none, { h with nalloc := h.nalloc + 1 }) := by
  rw [alloc_pre (some i) wb lb n l hn hn1 hn2 hl hl1 hl2 hl3]
  simp [bind_app, ldStream_app hz, callZalloc, hza, ZlibNg.Zutil.zcalloc, allocB, hok]

theorem carveDAllocs_AH_fault {h : Heap} {X : Array UInt8} {Y : Tbl (Option DeflateAllocs)}
    {Z : Tbl (Option DeflateState)} {off : Nat} {x : DeflateAllocs} (hY : Y h.nextBlk = some x)
    (hoff : off + 56 ≤ X.size) (hal : ((h.baseAddr (.heap h.nextBlk)).toNat + off) % 8 = 0) :
    Fl (AH h X Y Z) (carveDAllocs (.ref (.heap h.nextBlk) off)) :=
  ⟨_, by simp [carveDAllocs, carveCheck, bind_app, bind_fm, hoff, hal, hY, SIZEOF_DEFLATE_ALLOCS,
    ALIGNOF_DEFLATE_ALLOCS, ub]; rfl⟩

theorem carveDState_AH_fault {h : Heap} {X : Array UInt8} {Y : Tbl (Option DeflateAllocs)}
    {Z : Tbl (Option DeflateState)} {off : Nat} {x : DeflateState} (hZ : Z h.nextBlk = some x)
    (hoff : off + 5440 ≤ X.size) (hal : ((h.baseAddr (.heap h.nextBlk)).toNat + off) % 64 = 0) :
    Fl (AH h X Y Z) (carveDState (.ref (.heap h.nextBlk) off)) :=
  ⟨_, by simp [carveDState, carveCheck, bind_app, bind_fm, hoff, hal, hZ, SIZEOF_DEFLATE_STATE,
    ALIGNOF_DEFLATE_STATE, ub]; rfl⟩

/-- `alloc_deflate` faults when the heap records a deflate object in the block it gets (`DFreshBlocks` fails
there). -/
theorem alloc_fault {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) (hza : z.zalloc = .zcalloc)
    (hok : h.allocOk h.nalloc = true) (hx : h.dstates h.nextBlk ≠ none ∨ h.dallocs h.nextBlk ≠ none)
    (wb lb : Int32) (n l : Nat) (hn : wb.toInt = n) (hn1 : 9 ≤ n) (hn2 : n ≤ 15)
    (hl : lb.toInt = l) (hl1 : 128 ≤ l) (hl2 : l ≤ 32768) (hl3 : l % 16 = 0) :
    Fl h (alloc_deflate (some i) wb lb) := by
  rw [alloc_pre (some i) wb lb n l hn hn1 hn2 hl hl1 hl2 hl3]
  have p15 : 2 ^ n ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hn2
  have p9 : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn1
  have m64 : 2 ^ n % 64 = 0 := by
    have : 2 ^ n = 2 ^ (n - 6) * 2 ^ 6 := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; simp
  have ws1 : dWS (2 ^ n) % 64 = 0 := by unfold dWS; split <;> omega
  have ws2 : dWS (2 ^ n) ≤ 65536 := by unfold dWS; split <;> omega
  generalize 2 ^ n = w at *
  generalize dWS w = D at *
  have hpn := padsz_toNat (h.baseAddr (.heap h.nextBlk))
  generalize hP : (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat = p at hpn
  have hp : p < 64 := by omega
  have a0 : ((h.baseAddr (.heap h.nextBlk)).toNat + p) % 64 = 0 := by omega
  obtain ⟨aD8, aS, aPv, aH, aPb, aS16⟩ := alloc_mods ((h.baseAddr (.heap h.nextBlk)).toNat) p D w l a0 ws1 m64 hl3
  generalize hT : D + 2 * w + 131072 + 4 * l + 64 + 5440 + 128 = T
  have hz2 : ZlibNg.Zutil.zcalloc z.«opaque» 1 (UInt32.ofNat T) = allocB T := by
    have e : ((1 : UInt32).toUInt64 * (UInt32.ofNat T).toUInt64).toNat = T := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, UInt32.toNat_ofNat_of_lt' (by
        simp only [UInt32.size]; omega)]
      simp; omega
    simp only [ZlibNg.Zutil.zcalloc, e]
  refine Fl.bind_sat (Sat.of_eq (ldStream_app hz) ?_)
  simp only [callZalloc, hza, hz2]
  refine Fl.bind_sat (Sat.of_eq (allocB_AH hok T) ?_)
  simp only [show ((Ptr.ref (BRef.heap h.nextBlk) 0 : BPtr) == Ptr.null) = false from rfl, Bool.false_eq_true,
    ↓reduceIte]
  refine Fl.bind_sat (Sat.of_eq rfl ?_)
  simp only [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero, AH_base, hP]
  have hA0 := Array.size_ofFn (n := T) (f := fun j => (Junk.of (h.garbage h.nalloc j.val) : UInt8))
  generalize (Array.ofFn (n := T) fun j => (Junk.of (h.garbage h.nalloc j.val) : UInt8)) = A0 at *
  obtain ⟨f0, f1, f2⟩ := alloc_sizes p D w l T A0.size hp hT hA0
  fstep exact add0_AH p f0
  fstep exact cast_AH (al := 64) (by decide) a0
  fstep exact add_AH (D + 2 * w + 131072 + 4 * l + 64 + 5440) f1
  cases hfa : h.dallocs h.nextBlk with
  | some x => exact Fl.bind_now (carveDAllocs_AH_fault hfa f2 aD8)
  | none =>
  obtain ⟨x, hfs⟩ : ∃ x, h.dstates h.nextBlk = some x := by
    cases e : h.dstates h.nextBlk with
    | none => exact absurd hfa (hx.resolve_left (by simp [e]))
    | some x => exact ⟨x, rfl⟩
  fstep exact carveDAllocs_AH hfa f2 aD8
  have hA1 := Array.size_extract (xs := A0) (start := 0) (stop := p + (D + 2 * w + 131072 + 4 * l + 64 + 5440))
  generalize A0.extract 0 (p + (D + 2 * w + 131072 + 4 * l + 64 + 5440)) = A1 at *
  obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := alloc_sizes2 p D w l A1.size (by rw [hA1]; omega)
  fstep exact ldDAllocs_AH
  fstep exact stDAllocs_AH _
  fstep exact ldStream_AH hz
  fstep exact ldDAllocs_AH
  fstep exact stDAllocs_AH _
  fstep exact add_AH 0 g0
  fstep exact cast_AH (al := 64) (by decide) a0
  fstep exact ldDAllocs_AH
  fstep exact stDAllocs_AH _
  fstep exact add_AH D g1
  fstep exact cast_AH (al := 64) (by decide) aPv
  fstep exact ldDAllocs_AH
  fstep exact stDAllocs_AH _
  fstep exact add_AH (D + 2 * w) g2
  fstep exact cast_AH (al := 64) (by decide) aH
  fstep exact ldDAllocs_AH
  fstep exact stDAllocs_AH _
  fstep exact add_AH (D + 2 * w + 131072) g3
  fstep exact cast_AH (al := 64) (by decide) aPb
  fstep exact ldDAllocs_AH
  fstep exact stDAllocs_AH _
  fstep exact add_AH (D + 2 * w + 131072 + 4 * l + 64) g6
  fstep exact cast_AH (al := 16) (by decide) aS16
  exact Fl.bind_now (carveDState_AH_fault hfs g4 aS)

end ZlibNgF.Proof.DeflateAlloc
