import ZlibNgF.Proof.«deflate.c.alloc»

/-!
# `deflateInit2`, `deflateReset`, `deflateResetKeep`, `lm_init`, `zng_tr_init` (`ZlibNgF`)

Runs on `SH` heaps (a heap with one stream record and one block's bytes and `deflate_state` as parameters):
`zng_tr_init` with the three tree loops of `init_block` (`ctLoop`), `deflateResetKeep`, `lm_init` (the `head` clear
of `CLEAR_HASH` and `lm_set_level` for every level), `deflateReset`. Then `deflateInit2` for every argument: the
allocator set-up, the `windowBits` decoding, the argument check (`init2Tail`, the part of the translation after the
decoding, unfolded once so that the duplicated continuations of the `do` blocks are proved once), `alloc_deflate`
(`Proof/deflate.c.alloc.lean`) and the state set-up. A successful call leaves the structural invariant `DInv`; every
call changes only the stream record and the fresh block (`InitPost`). On a heap where `DFreshBlocks` fails at the new
block the call returns an error code or faults (`SF`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateInit
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate
open ZlibNgF.Proof.DeflateAlloc
open ZlibNgF.Proof.InflateInv (upd_upd ldStream_app)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem (fillFold fillFold_size fillFold_get modify_heap memset_loop)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)

theorem dif_t {α : Type} {c : Prop} [Decidable c] {a : c → α} {b : ¬ c → α} (h : c) : dite c a b = a h := by
  simp [h]

/-- `H` with stream `i` holding `z`, and block `b` holding the bytes `d` and the `deflate_state` `st`. -/
def SH (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) : Heap :=
  { H with
    streams := upd H.streams i (some z)
    dstates := upd H.dstates b (some st)
    bytes := upd H.bytes b (some d) }

section SH
variable (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8)
@[simp] theorem SH_streams : (SH H i z b st d).streams i = some z := upd_same _ _ _
@[simp] theorem SH_dstates : (SH H i z b st d).dstates b = some st := upd_same _ _ _
@[simp] theorem SH_bytes : (SH H i z b st d).bytes b = some d := upd_same _ _ _
@[simp] theorem SH_dstate : (SH H i z b st d).dstate b = some st := by simp [Heap.dstate]
@[simp] theorem SH_dallocs : (SH H i z b st d).dallocs = H.dallocs := rfl
@[simp] theorem SH_base : (SH H i z b st d).baseAddr = H.baseAddr := rfl
end SH

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem wrD_SH (f : DeflateState → DeflateState) :
    wrD (some b) f (SH H i z b st d) = .ok ((), SH H i z b (f st) d) := by
  simp only [wrD, stDState, ldDState, bind_app, SH_dstate]
  simp [SH, upd_upd]

theorem rdD_SH {α : Type} (f : DeflateState → α) :
    rdD (some b) f (SH H i z b st d) = .ok (f st, SH H i z b st d) := by
  simp [rdD, ldDState, bind_app]

theorem ldDState_SH : ldDState (some b) (SH H i z b st d) = .ok (st, SH H i z b st d) := by
  simp [ldDState]

theorem wrZ_SH (f : ZStream → ZStream) :
    wrZ (some i) f (SH H i z b st d) = .ok ((), SH H i (f z) b st d) := by
  simp [wrZ, stStream, ldStream, bind_app, SH, upd_upd]

theorem rdZ_SH {α : Type} (f : ZStream → α) :
    rdZ (some i) f (SH H i z b st d) = .ok (f z, SH H i z b st d) := by
  simp [rdZ, ldStream, bind_app]

theorem ldStream_SH : ldStream (some i) (SH H i z b st d) = .ok (z, SH H i z b st d) := by
  simp [ldStream]

theorem memset_SH {off n : Nat} (hn : off + n ≤ d.size) (byte : UInt8) :
    Ptr.memset (Ptr.ref (BRef.heap b) off) byte n (SH H i z b st d) =
      .ok ((), SH H i z b st (fillFold byte off (List.range' 0 n) d)) := by
  simp only [Ptr.memset, space_get_heap, SH_bytes, Space.ro, Heap.isRo, Bool.false_eq_true, ↓reduceIte, hn]
  rw [modify_heap _ _ d (SH_bytes H i z b st d), memset_loop]
  simp [SH, upd_upd]

end

/-! ## The tree loops of `init_block` -/

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- `for (n = 0; n < N; n++) tree[n].Freq = 0;` over one tree array of the state. -/
theorem ctLoop (mk : Nat → CtRef) (getT : DeflateState → Array Ct) (setT : DeflateState → Array Ct → DeflateState)
    (hget : ∀ s, Space.get (SH H i z b s d) (mk b) = some (getT s))
    (hmod : ∀ s g, Space.modify (SH H i z b s d) (mk b) g = SH H i z b (setT s (g (getT s))) d)
    (hro : ∀ s, Space.ro (SH H i z b s d) (mk b) = false)
    (hgs : ∀ s A, getT (setT s A) = A) (hss : ∀ s A B, setT (setT s A) B = setT s B)
    (hsg : ∀ s, setT s (getT s) = s) (st : DeflateState) (N : Nat) (hN : N < 2 ^ 31) (hsz : N ≤ (getT st).size) :
    Sat (SH H i z b st d) (cwhile (fun (n : Int32) => pure (n < N.toInt32, n))
      (fun n => do ctSetFc (.ref (mk b) 0) n.toInt 0; pure (n + 1)) 0)
      (fun _ H' => ∃ A, H' = SH H i z b (setT st A) d ∧ A.size = (getT st).size) := by
  have hNi : (N.toInt32).toInt = N := by
    rw [Nat.toInt32, Int32.toInt_ofNat_of_lt hN]
  refine sat_cwhile (fun (n : Int32) H' => ∃ A, H' = SH H i z b (setT st A) d ∧ A.size = (getT st).size ∧
      0 ≤ n.toInt ∧ n.toInt ≤ N) (fun n => N - n.toInt.toNat) _ ?_ ⟨(getT st), ?_, rfl, by decide, by simp⟩ ?_
  · rintro n H' ⟨A, rfl, hA, h0, h1⟩
    refine ⟨(n < N.toInt32, n), _, rfl, ?_, ?_⟩
    · intro hc
      have hlt : n.toInt < N := by
        have := Int32.lt_iff_toInt_lt.mp (of_decide_eq_true hc); rwa [hNi] at this
      have hk : n.toInt.toNat < A.size := by omega
      have e1 : Ptr.add (Ptr.ref (mk b) 0) n.toInt (SH H i z b (setT st A) d) =
          .ok (Ptr.ref (mk b) n.toInt.toNat, SH H i z b (setT st A) d) := by
        simp only [Ptr.add, hget, hgs]
        rw [ite_t (by omega)]
        congr 3; omega
      have hn1 : (n + 1).toInt = n.toInt + 1 := by
        rw [Int32.toInt_add, Int32.toInt_one]; exact Int.bmod_eq_of_le (by omega) (by omega)
      refine ⟨n + 1, _, ?_, ⟨A.set! n.toInt.toNat { (A[n.toInt.toNat]'hk) with fc := 0 }, rfl, by simp [hA], by omega,
        by omega⟩, by omega⟩
      · simp only [ctSetFc, ctGet, ctSet, Ptr.index, bind_app, e1, Ptr.load, hget, hgs, hk, ↓reduceDIte,
          Ptr.store, hro, Bool.false_eq_true, ↓reduceIte, hmod, hss, pure_app]
    · intro hc
      refine ⟨A, rfl, hA⟩
  · rw [hsg]
  · simp [fuel]; omega

theorem ctl_get (s : DeflateState) : Space.get (SH H i z b s d) (CtRef.dyn_ltree b) = some s.dyn_ltree := by
  show Heap.getCts _ _ = _; simp [Heap.getCts]
theorem ctd_get (s : DeflateState) : Space.get (SH H i z b s d) (CtRef.dyn_dtree b) = some s.dyn_dtree := by
  show Heap.getCts _ _ = _; simp [Heap.getCts]
theorem ctb_get (s : DeflateState) : Space.get (SH H i z b s d) (CtRef.bl_tree b) = some s.bl_tree := by
  show Heap.getCts _ _ = _; simp [Heap.getCts]
theorem ctl_mod (s : DeflateState) (g : Array Ct → Array Ct) :
    Space.modify (SH H i z b s d) (CtRef.dyn_ltree b) g = SH H i z b { s with dyn_ltree := g s.dyn_ltree } d := by
  show Heap.modifyCts _ _ _ = _
  simp only [Heap.modifyCts]
  rw [Heap.dstates_modify_eq _ b _ s (SH_dstates H i z b s d)]
  simp [SH, upd_upd]
theorem ctd_mod (s : DeflateState) (g : Array Ct → Array Ct) :
    Space.modify (SH H i z b s d) (CtRef.dyn_dtree b) g = SH H i z b { s with dyn_dtree := g s.dyn_dtree } d := by
  show Heap.modifyCts _ _ _ = _
  simp only [Heap.modifyCts]
  rw [Heap.dstates_modify_eq _ b _ s (SH_dstates H i z b s d)]
  simp [SH, upd_upd]
theorem ctb_mod (s : DeflateState) (g : Array Ct → Array Ct) :
    Space.modify (SH H i z b s d) (CtRef.bl_tree b) g = SH H i z b { s with bl_tree := g s.bl_tree } d := by
  show Heap.modifyCts _ _ _ = _
  simp only [Heap.modifyCts]
  rw [Heap.dstates_modify_eq _ b _ s (SH_dstates H i z b s d)]
  simp [SH, upd_upd]

theorem ctSetFc_l (s : DeflateState) (k : Nat) (v : UInt16) (hk : k < s.dyn_ltree.size) :
    ctSetFc (.ref (CtRef.dyn_ltree b) 0) (k : Int) v (SH H i z b s d) =
      .ok ((), SH H i z b { s with dyn_ltree := s.dyn_ltree.set! k { (s.dyn_ltree[k]'hk) with fc := v } } d) := by
  have e1 : Ptr.add (Ptr.ref (CtRef.dyn_ltree b) 0) (k : Int) (SH H i z b s d) =
      .ok (Ptr.ref (CtRef.dyn_ltree b) k, SH H i z b s d) := by
    simp only [Ptr.add, ctl_get]
    rw [ite_t (by omega)]
    congr 3; omega
  simp only [ctSetFc, ctGet, ctSet, Ptr.index, bind_app, e1, Ptr.load, ctl_get, hk, ↓reduceDIte,
    Ptr.store, ↓reduceIte, ctl_mod]
  rfl

end

/-- The fields that `zng_tr_init` sets, with the three tree arrays `A`, `B`, `C`. -/
def trS (b : Nat) (st : DeflateState) (A B C : Array Ct) : DeflateState :=
  { st with
    l_desc := { st.l_desc with dyn_tree := .val (.ref (.dyn_ltree b) 0), stat_desc := .val .static_l_desc }
    d_desc := { st.d_desc with dyn_tree := .val (.ref (.dyn_dtree b) 0), stat_desc := .val .static_d_desc }
    bl_desc := { st.bl_desc with dyn_tree := .val (.ref (.bl_tree b) 0), stat_desc := .val .static_bl_desc }
    bi_buf := 0
    bi_valid := 0
    bi_used := 0
    dyn_ltree := A
    dyn_dtree := B
    bl_tree := C
    static_len := 0
    opt_len := 0
    sym_next := 0 }

/-- `zng_tr_init` on a state whose tree arrays have their C sizes. -/
theorem tr_init_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8} (st : DeflateState)
    (h1 : st.dyn_ltree.size = HEAP_SIZE) (h2 : st.dyn_dtree.size = 2 * 30 + 1) (h3 : st.bl_tree.size = 2 * 19 + 1) :
    Sat (SH H i z b st d) (ZlibNg.Trees.zng_tr_init (some b)) (fun _ H' => ∃ A B C, H' = SH H i z b (trS b st A B C) d ∧
      A.size = HEAP_SIZE ∧ B.size = 2 * 30 + 1 ∧ C.size = 2 * 19 + 1) := by
  simp only [ZlibNg.Trees.zng_tr_init, ZlibNg.Trees.init_block, dynLtreeP, dynDtreeP, blTreeP, pure_bind_M]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.mono (ctLoop CtRef.dyn_ltree (·.dyn_ltree) (fun s A => { s with dyn_ltree := A })
    ctl_get ctl_mod (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) _ L_CODES (by decide)
    (by simp [h1, HEAP_SIZE, L_CODES])) ?_)
  rintro _ _ ⟨A, rfl, hA⟩
  refine Sat.bind (Sat.mono (ctLoop CtRef.dyn_dtree (·.dyn_dtree) (fun s A => { s with dyn_dtree := A })
    ctd_get ctd_mod (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) _ D_CODES (by decide)
    (by simp [h2, D_CODES])) ?_)
  rintro _ _ ⟨B, rfl, hB⟩
  refine Sat.bind (Sat.mono (ctLoop CtRef.bl_tree (·.bl_tree) (fun s A => { s with bl_tree := A })
    ctb_get ctb_mod (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) _ BL_CODES (by decide)
    (by simp [h3, BL_CODES])) ?_)
  rintro _ _ ⟨C, rfl, hC⟩
  simp only at hA hB hC
  refine Sat.bind (Sat.of_eq (ctSetFc_l _ END_BLOCK 1 (by simp [hA, h1, END_BLOCK, HEAP_SIZE, L_CODES])) ?_)
  try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.of_eq (wrD_SH _) ⟨_, B, C, rfl, ?_, by rw [hB, h2], by rw [hC, h3]⟩
  · simp [hA, h1]
  done

/-! ## `deflateResetKeep`, `deflateReset` -/

/-- The stream fields that `deflateResetKeep` sets. -/
def rkZ (z : ZStream) (wrap : Int32) : ZStream :=
  { z with
    total_out := 0
    total_in := 0
    msg := .null
    data_type := Z_UNKNOWN
    adler := if wrap == 2 then CRC32_INITIAL_VALUE else ADLER32_INITIAL_VALUE }

/-- The state fields that `deflateResetKeep` sets before `zng_tr_init`. -/
def rkS (st : DeflateState) : DeflateState :=
  { st with
    pending := 0
    pending_out := st.pending_buf
    status := if st.wrap == 2 then GZIP_STATE else INIT_STATE
    last_flush := -2
    gzhead := .val none }

/-- What `deflateStateCheck` accepts, on the state record. -/
structure DOk (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) : Prop where
  za : z.zalloc ≠ .null
  zf : z.zfree ≠ .null
  hb : z.state = some b
  ab : ∃ a, st.alloc_bufs = .val (some a)
  sm : st.strm = .val (some i)
  lo : INIT_STATE ≤ st.status
  hi : st.status ≤ MAX_STATE

theorem check_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (k : DOk i z b st) : deflateStateCheck (some i) (SH H i z b st d) = .ok (false, SH H i z b st d) := by
  obtain ⟨a, ha⟩ := k.ab
  have hm1 : ¬ st.status < INIT_STATE := fun hlt => absurd k.lo (Int32.not_le.mpr hlt)
  have hm2 : ¬ st.status > MAX_STATE := fun hlt => absurd k.hi (Int32.not_le.mpr hlt)
  simp [deflateStateCheck, bind_app, ldStream_SH, k.hb, ldDState_SH, k.za, k.zf, ha, k.sm, Ival.get, hm1, hm2]

/-- `deflateResetKeep` on an accepted stream whose `wrap` is 0, 1 or 2 and whose `pending_buf` is set. -/
theorem resetKeep_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (k : DOk i z b st) (hw : st.wrap = 0 ∨ st.wrap = 1 ∨ st.wrap = 2) {pb : BPtr} (hpb : st.pending_buf = .val pb)
    (h1 : st.dyn_ltree.size = HEAP_SIZE) (h2 : st.dyn_dtree.size = 2 * 30 + 1) (h3 : st.bl_tree.size = 2 * 19 + 1) :
    Sat (SH H i z b st d) (deflateResetKeep (some i)) (fun r H' => r = Z_OK ∧ ∃ A B C,
      H' = SH H i (rkZ z st.wrap) b (trS b (rkS st) A B C) d ∧
      A.size = HEAP_SIZE ∧ B.size = 2 * 30 + 1 ∧ C.size = 2 * 19 + 1) := by
  have hnw : ¬ st.wrap < 0 := by rcases hw with h | h | h <;> rw [h] <;> decide
  unfold deflateResetKeep
  refine Sat.bind (Sat.of_eq (check_SH k) ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_); try dsimp only
  simp only [k.hb]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  simp only [hpb, Ival.get, pure_bind_M]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  simp only [hnw, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
  by_cases hw2 : (st.wrap == 2) = true
  · simp only [hw2, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (tr_init_SH _ h1 h2 h3) ?_)
    rintro _ _ ⟨A, B, C, rfl, hA, hB, hC⟩
    refine Sat.pure ⟨rfl, A, B, C, ?_, hA, hB, hC⟩
    simp [rkZ, rkS, trS, hpb, hw2, k.hb]
  · simp only [hw2, Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (tr_init_SH _ h1 h2 h3) ?_)
    rintro _ _ ⟨A, B, C, rfl, hA, hB, hC⟩
    refine Sat.pure ⟨rfl, A, B, C, ?_, hA, hB, hC⟩
    simp [rkZ, rkS, trS, hpb, hw2, k.hb]


/-! ## `lm_init` -/

/-- The state fields that `lm_init` sets (`c` is the configuration of the level, `lm` / `ib` the function
pointers `lm_set_level` stores). -/
def lmS (st : DeflateState) (c : Config) (lm : Ival LongestMatchFn) (ib : Ival InsertBatchFn) : DeflateState :=
  { st with
    window_size := W_BUF_SIZE st.w_size
    slide_len := 0
    fill_end := 2 * st.w_size - MIN_LOOKAHEAD
    max_lazy_match := c.max_lazy.toUInt32
    good_match := c.good_length.toUInt32
    nice_match := c.nice_length.toUInt32.toInt32
    max_chain_length := c.max_chain.toUInt32
    longest_match := lm
    insert_batch := ib
    strstart := 0
    block_start := 0
    lookahead := 0
    insert := 0
    prev_length := 0
    match_available := 0
    match_start := 0
    ins_h := 0 }

theorem lm_set_level_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (level : Int32) (h0 : 0 ≤ level) (h9 : level ≤ 9) :
    ∃ (c : Config) (lm : LongestMatchFn) (ib : InsertBatchFn), lm_set_level (some b) level (SH H i z b st d) = .ok ((), SH H i z b
      { st with max_lazy_match := c.max_lazy.toUInt32, good_match := c.good_length.toUInt32,
                nice_match := c.nice_length.toUInt32.toInt32, max_chain_length := c.max_chain.toUInt32,
                longest_match := .val lm, insert_batch := .val ib, level := level } d) := by
  have hc : ∃ c, config level = pure c := by
    unfold config tblGet
    have : ¬ level < 0 := fun h => absurd h0 (Int32.not_le.mpr h)
    have hl : level.toNatClampNeg < configuration_table.size := by
      have := Int32.le_iff_toInt_le.mp h9
      have e : configuration_table.size = 10 := rfl
      rw [e]; show level.toInt.toNat < 10
      have : (9 : Int32).toInt = 9 := rfl
      omega
    exact ⟨_, by rw [ite_f this, dif_t hl]⟩
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, ?_⟩
  unfold lm_set_level
  rw [hc]
  by_cases h1 : level ≥ MIN_ROLL_LEVEL
  · exact ⟨.longest_match_slow_roll_c, .insert_roll_batch, by simp [bind_app, wrD_SH, h1]⟩
  · by_cases h2 : level == 1
    · exact ⟨.longest_match_slow_knuth_c, .insert_knuth_batch_head, by simp [bind_app, wrD_SH, h1, h2]⟩
    · exact ⟨.longest_match_slow_knuth_c, .insert_knuth_batch, by simp [bind_app, wrD_SH, h1, h2]⟩

theorem lm_set_level_sat {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (level : Int32) (h0 : 0 ≤ level) (h9 : level ≤ 9) :
    Sat (SH H i z b st d) (lm_set_level (some b) level) (fun _ H' => ∃ (c : Config) (lm : LongestMatchFn)
      (ib : InsertBatchFn), H' = SH H i z b
      { st with max_lazy_match := c.max_lazy.toUInt32, good_match := c.good_length.toUInt32,
                nice_match := c.nice_length.toUInt32.toInt32, max_chain_length := c.max_chain.toUInt32,
                longest_match := .val lm, insert_batch := .val ib, level := level } d) := by
  obtain ⟨c, lm, ib, e⟩ := lm_set_level_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d) level h0 h9
  exact ⟨(), _, e, c, lm, ib, rfl⟩

/-- `lm_init` on a state whose `head` lies in its block and whose `level` is 0..9. -/
theorem lm_init_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {ho : Nat}
    (hh : st.head = .val (.ref (.heap b) ho)) (hho : ho + 131072 ≤ d.size) (h0 : 0 ≤ st.level) (h9 : st.level ≤ 9) :
    Sat (SH H i z b st d) (lm_init (some b)) (fun _ H' => ∃ c lm ib d', H' = SH H i z b (lmS st c (.val lm) (.val ib)) d' ∧
      d'.size = d.size) := by
  unfold lm_init
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  by_cases hh2 : (!HASHLESS st.level st.strategy) = true
  · rw [ite_t hh2]
    refine Sat.bind (Sat.of_eq (by
      simp only [CLEAR_HASH, bind_app, ldDState_SH, hh, Ival.get, pure_app]
      exact memset_SH (off := ho) (n := HASH_SIZE.toNat * 2) hho 0) ?_)
    try dsimp only
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (lm_set_level_sat _ h0 h9) ?_)
    rintro _ _ ⟨c, lm, ib, rfl⟩
    refine Sat.of_eq (wrD_SH _) ⟨c, lm, ib, fillFold 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d, ?_, ?_⟩
    · simp [lmS, hh]
    · simp [fillFold_size]
  · rw [ite_f hh2]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_); try dsimp only
    refine Sat.bind (Sat.mono (lm_set_level_sat _ h0 h9) ?_)
    rintro _ _ ⟨c, lm, ib, rfl⟩
    refine Sat.of_eq (wrD_SH _) ⟨c, lm, ib, d, ?_, rfl⟩
    simp [lmS]

/-- The layout facts about a state before `deflateReset` (set by `deflateInit2`, kept by every later call) from
which the layout clauses of the invariant follow after the reset; `D` is the size of the block's bytes. -/
structure RLay (b : Nat) (st : DeflateState) (D : Nat) : Prop where
  ws : 512 ≤ st.w_size.toNat ∧ st.w_size.toNat ≤ 32768
  lb : 128 ≤ st.lit_bufsize.toNat ∧ st.lit_bufsize.toNat ≤ 32768
  pbs : st.pending_buf_size.toNat = 4 * st.lit_bufsize.toNat
  se : st.sym_end.toNat = 3 * (st.lit_bufsize.toNat - 1)
  lay : ∃ wo po ho pbo, st.window = .val (.ref (.heap b) wo) ∧ st.prev = .val (.ref (.heap b) po) ∧
    st.head = .val (.ref (.heap b) ho) ∧ st.pending_buf = .val (.ref (.heap b) pbo) ∧
    wo + (W_BUF_SIZE st.w_size).toNat ≤ po ∧ po + 2 * st.w_size.toNat ≤ ho ∧ ho + 131072 ≤ pbo ∧
    pbo + 4 * st.lit_bufsize.toNat + 64 ≤ D ∧ st.sym_buf = .val (.ref (.heap b) (pbo + st.lit_bufsize.toNat + 8))
  strat : 0 ≤ st.strategy ∧ st.strategy ≤ 4

/-- `deflateReset` on an accepted stream with the fields that `deflateResetKeep` and `lm_init` read in range. -/
theorem reset_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (k : DOk i z b st) (hw : st.wrap = 0 ∨ st.wrap = 1 ∨ st.wrap = 2) {pb : BPtr} (hpb : st.pending_buf = .val pb)
    (h1 : st.dyn_ltree.size = HEAP_SIZE) (h2 : st.dyn_dtree.size = 2 * 30 + 1) (h3 : st.bl_tree.size = 2 * 19 + 1)
    {ho : Nat} (hh : st.head = .val (.ref (.heap b) ho)) (hho : ho + 131072 ≤ d.size) (l0 : 0 ≤ st.level)
    (l9 : st.level ≤ 9) (R : RLay b st d.size) :
    Sat (SH H i z b st d) (deflateReset (some i)) (fun r H' => r = Z_OK ∧ ∃ A B C c lm ib d',
      H' = SH H i (rkZ z st.wrap) b (lmS (trS b (rkS st) A B C) c (.val lm) (.val ib)) d' ∧ d'.size = d.size ∧
      A.size = HEAP_SIZE ∧ B.size = 2 * 30 + 1 ∧ C.size = 2 * 19 + 1 ∧ RLay b st d.size) := by
  unfold deflateReset
  refine Sat.bind (Sat.mono (resetKeep_SH k hw hpb h1 h2 h3) ?_)
  rintro _ _ ⟨rfl, A, B, C, rfl, hA, hB, hC⟩
  simp only [show (Z_OK == Z_OK) = true from rfl, ↓reduceIte]
  have hzs : (rkZ z st.wrap).state = some b := k.hb
  refine Sat.bind (Sat.of_eq (by simp only [dstateOf]; exact rdZ_SH _) ?_)
  try dsimp only
  rw [hzs]
  refine Sat.bind (Sat.mono (lm_init_SH (ho := ho) hh hho l0 l9) ?_)
  rintro _ _ ⟨c, lm, ib, d', rfl, hd'⟩
  exact Sat.pure ⟨rfl, A, B, C, c, lm, ib, d', rfl, hd', hA, hB, hC, R⟩

/-- The layout and position clauses of the invariant after `deflateReset`. -/
theorem RLay.post {b : Nat} {st : DeflateState} {D : Nat} (r : RLay b st D) (H : Heap) (d : Array UInt8)
    (hd : H.bytes b = some d) (hD : d.size = D) (A B C : Array Ct) (c : Config) (lm : LongestMatchFn)
    (ib : InsertBatchFn) :
    let v := DeflateInv.dview (lmS (trS b (rkS st) A B C) c (.val lm) (.val ib))
    (512 ≤ v.w_size.toNat ∧ v.w_size.toNat ≤ 32768 ∧ v.window_size = W_BUF_SIZE v.w_size ∧
      128 ≤ v.lit_bufsize.toNat ∧ v.lit_bufsize.toNat ≤ 32768 ∧ v.pending_buf_size.toNat = 4 * v.lit_bufsize.toNat ∧
      v.sym_end.toNat = 3 * (v.lit_bufsize.toNat - 1)) ∧
    (∃ d wo po ho pbo, H.bytes b = some d ∧ v.window = .val (.ref (.heap b) wo) ∧
      v.prev = .val (.ref (.heap b) po) ∧ v.head = .val (.ref (.heap b) ho) ∧
      v.pending_buf = .val (.ref (.heap b) pbo) ∧ wo + v.window_size.toNat ≤ po ∧ po + 2 * v.w_size.toNat ≤ ho ∧
      ho + 131072 ≤ pbo ∧ pbo + 4 * v.lit_bufsize.toNat + 64 ≤ d.size ∧
      v.sym_buf = .val (.ref (.heap b) (pbo + v.lit_bufsize.toNat + 8)) ∧
      ∃ poo, v.pending_out = .val (.ref (.heap b) poo) ∧ pbo ≤ poo ∧
        poo - pbo + v.pending.toNat ≤ 4 * v.lit_bufsize.toNat + 9) ∧
    (v.pending = 0 → v.pending_out = v.pending_buf) ∧
    (v.sym_next ≤ v.sym_end ∧ v.sym_next.toNat % 3 = 0) ∧
    (0 ≤ v.bi_valid ∧ v.bi_valid < 8) ∧
    (v.strstart.toNat + v.lookahead.toNat ≤ v.window_size.toNat) ∧
    (0 ≤ v.strategy ∧ v.strategy ≤ 4) ∧
    ((∃ f, v.longest_match = .val f) ∧ (∃ f, v.insert_batch = .val f)) := by
  obtain ⟨wo, po, ho, pbo, hw, hp, hh, hpb, h1, h2, h3, h4, hs⟩ := r.lay
  refine ⟨⟨r.ws.1, r.ws.2, rfl, r.lb.1, r.lb.2, r.pbs, r.se⟩,
    ⟨d, wo, po, ho, pbo, hd, hw, hp, hh, hpb, h1, h2, h3, by rw [hD]; exact h4, hs, pbo, hpb, Nat.le_refl _,
      by simp [DeflateInv.dview, lmS, trS, rkS]⟩, fun _ => by simp [DeflateInv.dview, lmS, trS, rkS],
    ⟨by simp [DeflateInv.dview, lmS, trS, rkS], by simp [DeflateInv.dview, lmS, trS, rkS]⟩,
    by simp [DeflateInv.dview, lmS, trS, rkS], by simp [DeflateInv.dview, lmS, trS, rkS], r.strat,
    ⟨lm, rfl⟩, ⟨ib, rfl⟩⟩

/-! ## `deflateInit2` -/

theorem wrZ_app {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) (f : ZStream → ZStream) :
    wrZ (some i) f h = .ok ((), { h with streams := upd h.streams i (some (f z)) }) := by
  simp [wrZ, stStream, ldStream, bind_app, hz]

/-- The part of `deflateInit2` after the `windowBits` decoding, copied from the translation: the argument check,
`alloc_deflate` and the state set-up (`level` already normalised; `wrap`, `windowBits` decoded). -/
def init2Tail (strm : StreamPtr) (level method windowBits memLevel strategy wrap : Int32) : M Int32 := do
  if memLevel < 1 || memLevel > MAX_MEM_LEVEL || method.toInt64.toUInt64 != Z_DEFLATED || windowBits < MIN_WBITS ||
      windowBits > MAX_WBITS || level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED ||
      (windowBits == 8 && wrap != 1) then
    return Z_STREAM_ERROR
  let windowBits := if windowBits == 8 then 9 else windowBits
  let lit_bufsize ← shlI32 1 (memLevel + 6)
  let alloc_bufs ← alloc_deflate strm windowBits lit_bufsize
  if alloc_bufs == none then return Z_MEM_ERROR
  let st ← (← ldDAllocs alloc_bufs).state.get
  wrD st fun s => { s with alloc_bufs := .val alloc_bufs }
  let a ← ldDAllocs alloc_bufs
  let w ← a.window.get
  wrD st fun s => { s with window := .val w }
  let p ← (← ldDAllocs alloc_bufs).prev.get
  wrD st fun s => { s with prev := .val p }
  let hd ← (← ldDAllocs alloc_bufs).head.get
  wrD st fun s => { s with head := .val hd }
  let pb ← (← ldDAllocs alloc_bufs).pending_buf.get
  wrD st fun s => { s with pending_buf := .val pb }
  wrZ strm fun z => { z with state := st }
  wrD st fun s => { s with strm := .val strm }
  wrD st fun s => { s with status := INIT_STATE }
  wrD st fun s => { s with wrap := wrap }
  let ws ← shlI32 1 windowBits
  wrD st fun s => { s with w_size := ws.toUInt32 }
  wrD st fun s => { s with high_water := 0 }
  wrD st fun s => { s with lit_bufsize := lit_bufsize.toUInt32 }
  wrD st fun s => { s with pending_buf_size := s.lit_bufsize * 4 }
  let s ← ldDState st
  let sb ← (← (← s.pending_buf.get).add s.lit_bufsize.toNat).add PENDING_BUF_PAD.toInt
  wrD st fun s => { s with sym_buf := .val sb }
  wrD st fun s => { s with sym_end := (s.lit_bufsize - 1) * 3 }
  wrD st fun s => { s with level := level }
  wrD st fun s => { s with strategy := strategy }
  wrD st fun s => { s with block_open := 0 }
  wrD st fun s => { s with reproducible := 0 }
  deflateReset strm

theorem init2_eq (strm : StreamPtr) (level method windowBits memLevel strategy : Int32) :
    deflateInit2 strm level method windowBits memLevel strategy = (do
      let wrap : Int32 := 1
      if strm == none then return Z_STREAM_ERROR
      wrZ strm fun z => { z with msg := .null }
      if (← rdZ strm (·.zalloc)) == .null then
        wrZ strm fun z => { z with zalloc := .zcalloc }
        wrZ strm fun z => { z with «opaque» := .null }
      if (← rdZ strm (·.zfree)) == .null then
        wrZ strm fun z => { z with zfree := .zcfree }
      let level := if level == Z_DEFAULT_COMPRESSION then 6 else level
      let (wrap, windowBits, bad) ←
        if windowBits < 0 then do
          if windowBits < -MAX_WBITS then pure (0, windowBits, true)
          else pure ((0 : Int32), ← chkI32 (-windowBits.toInt), false)
        else if windowBits > MAX_WBITS then pure (2, windowBits - 16, false)
        else pure (wrap, windowBits, false)
      if bad then return Z_STREAM_ERROR
      init2Tail strm level method windowBits memLevel strategy wrap : M Int32) := by
  rfl

/-- A heap that differs from `h` only in stream `i` and in blocks from `h.nextBlk` on. -/
theorem dframe_of {h h' : Heap} {i : Nat} (hs : ∀ j, j ≠ i → h'.streams j = h.streams j)
    (hg : h'.gzheaders = h.gzheaders)
    (hb : ∀ c, c < h.nextBlk → h'.bytes c = h.bytes c ∧ h'.istates c = h.istates c ∧ h'.iallocs c = h.iallocs c ∧
      h'.dstates c = h.dstates c ∧ h'.dallocs c = h.dallocs c)
    (h1 : h'.consts = h.consts) (h2 : h'.crcTable = h.crcTable) (h3 : h'.x2nTable = h.x2nTable)
    (h4 : h'.baseAddr = h.baseAddr) (h5 : h.nextBlk ≤ h'.nextBlk) : DFrame h h' [i] [] [] [] := by
  refine ⟨⟨fun j hj => hs j (by simpa using hj), fun k _ => by rw [hg], fun c hc _ => ⟨(hb c hc).2.1,
    (hb c hc).2.2.1⟩, fun c hc _ data hd => ⟨data, by rw [(hb c hc).1, hd], rfl, fun _ _ _ => rfl⟩,
    fun c hc _ hn => by rw [(hb c hc).1, hn], h1, h2, h3, h4, h5⟩, fun c hc _ => ⟨(hb c hc).2.2.2.1, (hb c hc).2.2.2.2⟩⟩

theorem shl1_eq (x : Int32) (k : Nat) (hk : x.toInt = k) (h : k < 31) : shlI32 1 x = pure (Int32.ofNat (2 ^ k)) := by
  unfold shlI32
  have : ¬ ((1 : Int32) < 0 || x < 0 || x ≥ 32) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, hk]
    simp; omega
  rw [ite_f this]
  have p : 2 ^ k ≤ 2 ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
  refine chk_eq _ ?_
  rw [i32_ofNat_toInt (by omega)]
  have : x.toNatClampNeg = k := by simp [Int32.toNatClampNeg, hk]
  rw [this]; simp

theorem ldDAllocs_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    {al : DeflateAllocs} (ha : H.dallocs b = some al) :
    ldDAllocs (some b) (SH H i z b st d) = .ok (al, SH H i z b st d) := by
  simp [ldDAllocs, Heap.dallocsOf, ha]

theorem add_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {off : Nat}
    (k : Nat) (hk : off + k ≤ d.size) :
    Ptr.add (Ptr.ref (BRef.heap b) off) (k : Int) (SH H i z b st d) =
      .ok (.ref (.heap b) (off + k), SH H i z b st d) := by
  simp only [Ptr.add, space_get_heap, SH_bytes]
  rw [ite_t (by omega), show ((off : Int) + k).toNat = off + k by omega]

theorem garbage_sizes (g : Nat → UInt64) : (DeflateState.garbage g).dyn_ltree.size = HEAP_SIZE ∧
    (DeflateState.garbage g).dyn_dtree.size = 2 * 30 + 1 ∧ (DeflateState.garbage g).bl_tree.size = 2 * 19 + 1 := by
  simp [DeflateState.garbage]

theorem AH_SH (h : Heap) (i : Nat) (z1 : ZStream) (d : Array UInt8) (Y : Tbl (Option DeflateAllocs))
    (g : DeflateState) :
    AH { h with streams := upd h.streams i (some z1) } d Y (upd h.dstates h.nextBlk (some g)) =
      SH (AH { h with streams := upd h.streams i (some z1) } d Y h.dstates) i z1 h.nextBlk g d := by
  simp [AH, SH, upd_upd]

syntax "sstep " term : tactic
macro_rules
  | `(tactic| sstep $e) => `(tactic| (refine Sat.bind (Sat.of_eq $e ?_); try dsimp only))

theorem wsize_ne (n : Nat) (hn : n ≤ 15) : (Int32.ofNat (2 ^ n)).toUInt32 ≠ 0 := by
  have p : 0 < 2 ^ n := Nat.two_pow_pos n
  have p2 : 2 ^ n ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hn
  have h2 := i32_ofNat_toInt (k := 2 ^ n) (by omega)
  intro e
  have := congrArg UInt32.toNat e
  rw [Int32.toNat_toUInt32_of_le (by rw [Int32.le_iff_toInt_le, h2]; exact Int.natCast_nonneg _)] at this
  have h3 : (Int32.ofNat (2 ^ n)).toInt.toNat = 0 := this
  rw [h2, Int.toNat_natCast] at h3
  omega

theorem st_lo (w : Int32) : INIT_STATE ≤ (if (w == 2) = true then GZIP_STATE else INIT_STATE) := by
  split <;> decide
theorem st_hi (w : Int32) : (if (w == 2) = true then GZIP_STATE else INIT_STATE) ≤ MAX_STATE := by
  split <;> decide

/-- `m` runs on `H` to a result satisfying `Q`, or, when `P` fails, faults. -/
def SF {α : Type} (P : Prop) (H : Heap) (m : M α) (Q : α → Heap → Prop) : Prop := Sat H m Q ∨ (¬ P ∧ Fl H m)

theorem SF.bind_sat {α β : Type} {P : Prop} {H : Heap} {m : M α} {f : α → M β} {Q : β → Heap → Prop}
    (hm : Sat H m (fun a H' => SF P H' (f a) Q)) : SF P H (m >>= f) Q := by
  obtain ⟨a, H1, e1, hk⟩ := hm
  rcases hk with ⟨r, H2, e2, q⟩ | ⟨np, e, e2⟩
  · exact Or.inl ⟨r, H2, by simp only [bind_app, e1]; exact e2, q⟩
  · exact Or.inr ⟨np, e, by simp only [bind_app, e1]; exact e2⟩

theorem SF.pure {α : Type} {P : Prop} {H : Heap} {a : α} {Q : α → Heap → Prop} (q : Q a H) :
    SF P H (Pure.pure a) Q := Or.inl (Sat.pure q)

theorem SF.mono {α : Type} {P : Prop} {H : Heap} {m : M α} {Q Q' : α → Heap → Prop} (hm : SF P H m Q)
    (f : ∀ a H', Q a H' → Q' a H') : SF P H m Q' := by
  rcases hm with hs | hf
  · exact Or.inl (Sat.mono hs f)
  · exact Or.inr hf

theorem SF.sat {α : Type} {P : Prop} {H : Heap} {m : M α} {Q : α → Heap → Prop} (hm : SF P H m Q) (hp : P) :
    Sat H m Q := hm.resolve_right (fun h => h.1 hp)

theorem wsize_toNat (n : Nat) (hn : n ≤ 15) : (Int32.ofNat (2 ^ n)).toUInt32.toNat = 2 ^ n := by
  have p : 2 ^ n ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hn
  have hi := i32_ofNat_toInt (k := 2 ^ n) (by omega)
  have h0 : (0 : Int) ≤ ((2 ^ n : Nat) : Int) := Int.natCast_nonneg _
  rw [Int32.toNat_toUInt32_of_le (by rw [Int32.le_iff_toInt_le, hi]; exact h0)]
  show (Int32.ofNat (2 ^ n)).toInt.toNat = 2 ^ n
  rw [hi]; exact Int.toNat_natCast _

theorem wbuf_toNat (w : UInt32) (hw : w.toNat ≤ 32768) : (W_BUF_SIZE w).toNat = dWS w.toNat := by
  have h2 : (2 * w).toNat = 2 * w.toNat := by rw [UInt32.toNat_mul]; simp; omega
  unfold W_BUF_SIZE dWS W_BUF_MIN
  by_cases c : 2 * w.toNat > 32768
  · have : (32768 : UInt32) < 2 * w := by rw [UInt32.lt_iff_toNat_lt, h2]; simpa using c
    simp only [gt_iff_lt, this, ↓reduceIte, h2, c]
  · have : ¬ (32768 : UInt32) < 2 * w := by rw [UInt32.lt_iff_toNat_lt, h2]; simpa using c
    simp only [gt_iff_lt, this, ↓reduceIte, c]; rfl

theorem lb_one_le (l : Nat) {x : UInt32} (hx : x.toNat = l) (hl : 1 ≤ l) : 1 ≤ x := by
  rw [UInt32.le_iff_toNat_le, hx]; simpa using hl

/-- What a call of `deflateInit2` on stream `i` of `h` guarantees. -/
def InitPost (h : Heap) (i : Nat) (r : Int32) (h' : Heap) : Prop :=
  DFrame h h' [i] [] [] [] ∧ (r = Z_OK → DeflateInv.DInv h' (some i))

theorem tail_sat {h : Heap} {i : Nat} (z1 : ZStream) (hza : z1.zalloc = .zcalloc) (hzf : z1.zfree = .zcfree)
    (level method wb ml strat wrap : Int32) (hw : wrap = 0 ∨ wrap = 1 ∨ wrap = 2) :
    SF (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none) { h with streams := upd h.streams i (some z1) } (init2Tail (some i) level method wb ml strat wrap)
      (fun r h' => InitPost h i r h' ∧ (h.allocOk h.nalloc = true → level = 6 → method = 8 → wb = 15 → ml = 8 →
        strat = 0 → wrap = 1 → r = Z_OK)) := by
  have fr0 : DFrame h { h with streams := upd h.streams i (some z1) } [i] [] [] [] :=
    dframe_of (fun j hj => upd_ne _ _ _ _ hj) rfl (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl rfl rfl rfl (Nat.le_refl _)
  unfold init2Tail
  by_cases hc : (decide (ml < 1) || decide (ml > MAX_MEM_LEVEL) || method.toInt64.toUInt64 != Z_DEFLATED ||
      decide (wb < MIN_WBITS) || decide (wb > MAX_WBITS) || decide (level < 0) || decide (level > 9) ||
      decide (strat < 0) || decide (strat > Z_FIXED) || (wb == 8 && wrap != 1)) = true
  · rw [ite_t hc]
    refine SF.pure ⟨⟨fr0, fun e => absurd e (by decide)⟩, ?_⟩
    rintro - rfl rfl rfl rfl rfl rfl
    exact absurd hc (by decide)
  rw [ite_f hc]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq,
    not_and, Decidable.not_not] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hm1, hm9⟩, hmeth⟩, hw8⟩, hw15⟩, hl0⟩, hl9⟩, hs0⟩, hs4⟩, hw81⟩ := hc
  have tw8 := Int32.not_lt.mp hw8
  have tw15 := Int32.not_lt.mp hw15
  have tm1 := Int32.not_lt.mp hm1
  have tm9 := Int32.not_lt.mp hm9
  rw [Int32.le_iff_toInt_le] at tw8 tw15 tm1 tm9
  have e8 : (MIN_WBITS).toInt = 8 := rfl
  have e15 : (MAX_WBITS).toInt = 15 := rfl
  have e9 : (MAX_MEM_LEVEL).toInt = 9 := rfl
  have e1 : (1 : Int32).toInt = 1 := rfl
  rw [e8] at tw8; rw [e15] at tw15; rw [e9] at tm9; rw [e1] at tm1
  dsimp only
  obtain ⟨n, hn, hn1, hn2⟩ : ∃ n : Nat, (if (wb == 8) = true then (9 : Int32) else wb).toInt = n ∧ 9 ≤ n ∧ n ≤ 15 := by
    by_cases e : wb = 8
    · subst e; exact ⟨9, rfl, by omega, by omega⟩
    · have : (wb == 8) = false := by simpa using e
      rw [this]
      have : wb.toInt ≠ 8 := fun h' => e (Int32.toInt_inj.mp (by rw [h']; rfl))
      exact ⟨wb.toInt.toNat, by show wb.toInt = (wb.toInt.toNat : Int); omega, by omega, by omega⟩
  generalize (if (wb == 8) = true then (9 : Int32) else wb) = W at hn
  have hml : (ml + 6).toInt = (ml.toInt.toNat + 6 : Nat) := by
    rw [Int32.toInt_add]; rw [Int.bmod_eq_of_le (by have : (6 : Int32).toInt = 6 := rfl; omega)
      (by have : (6 : Int32).toInt = 6 := rfl; omega)]
    have : (6 : Int32).toInt = 6 := rfl
    omega
  rw [shl1_eq (ml + 6) _ hml (by omega), pure_bind_M]
  have pl1 : 2 ^ 7 ≤ 2 ^ (ml.toInt.toNat + 6) := Nat.pow_le_pow_right (by omega) (by omega)
  have pl2 : 2 ^ (ml.toInt.toNat + 6) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  have pl3 : 2 ^ (ml.toInt.toNat + 6) % 16 = 0 := by
    have : 2 ^ (ml.toInt.toNat + 6) = 2 ^ (ml.toInt.toNat + 2) * 2 ^ 4 := by rw [← Nat.pow_add]
    rw [this]; simp
  have hl := i32_ofNat_toInt (k := 2 ^ (ml.toInt.toNat + 6)) (by omega)
  generalize 2 ^ (ml.toInt.toNat + 6) = l at *
  cases hok : h.allocOk h.nalloc
  · refine Or.inl ?_
    refine Sat.bind (Sat.of_eq (alloc_fail (h := { h with streams := upd h.streams i (some z1) }) (z := z1)
      (by simp) hza hok W (Int32.ofNat l) n l hn hn1 hn2 hl pl1 pl2 pl3) ?_)
    refine Sat.pure ⟨⟨dframe_of (fun j hj => upd_ne _ _ _ _ hj) rfl (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl rfl rfl
      rfl (Nat.le_refl _), fun e => absurd e (by decide)⟩, fun e => absurd e (by simp)⟩
  by_cases hfr : ¬ (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none)
  · refine Or.inr ⟨hfr, Fl.bind_now (alloc_fault (h := { h with streams := upd h.streams i (some z1) }) (z := z1)
      (by simp) hza hok ?_ W (Int32.ofNat l) n l hn hn1 hn2 hl pl1 pl2 pl3)⟩
    by_cases a : h.dstates h.nextBlk = none
    · exact Or.inr (fun b => hfr ⟨a, b⟩)
    · exact Or.inl a
  obtain ⟨hfs, hfa⟩ := Classical.not_not.mp hfr
  refine Or.inl ?_
  refine Sat.bind (Sat.mono (alloc_ok (h := { h with streams := upd h.streams i (some z1) }) (z := z1) (by simp) hza
    hfs hfa hok W (Int32.ofNat l) n l hn hn1 hn2 hl pl1 pl2 pl3) ?_)
  rintro _ _ ⟨rfl, d, rfl, hdsz, hdz⟩
  have ⟨g1, g2, g3⟩ := garbage_sizes (h.garbage (2 ^ 43 + h.nextBlk))
  simp only [gState] at *
  generalize DeflateState.garbage (h.garbage (2 ^ 43 + h.nextBlk)) = g0 at *
  rw [AH_SH]
  simp only [show (some h.nextBlk == none) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hY : (AH { h with streams := upd h.streams i (some z1) } d (upd h.dallocs h.nextBlk (some
      (dAllocRec h.nextBlk (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat (dWS (2 ^ n)) (2 ^ n) z1.zfree)))
      h.dstates).dallocs h.nextBlk = some (dAllocRec h.nextBlk (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat
        (dWS (2 ^ n)) (2 ^ n) z1.zfree) := by rw [AH_dallocs]; exact upd_same _ _ _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, Ival.get, pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, pure_bind_M]
  sstep wrD_SH _
  sstep wrZ_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  rw [shl1_eq W n hn (by omega), pure_bind_M]
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep ldDState_SH
  simp only [pure_bind_M]
  have hl32 : (Int32.ofNat l).toUInt32.toNat = l := by
    rw [Int32.toNat_toUInt32_of_le (by rw [Int32.le_iff_toInt_le, hl]; simp)]
    show (Int32.ofNat l).toInt.toNat = l
    rw [hl]; simp
  rw [hl32]
  sstep add_SH l (by omega)
  sstep add_SH 8 (by omega)
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  refine Sat.mono (reset_SH (pb := .ref (.heap h.nextBlk)
      ((PADSZ (h.baseAddr (BRef.heap h.nextBlk)) 64).toNat + dWS (2 ^ n) + 2 * 2 ^ n + 131072))
    (ho := (PADSZ (h.baseAddr (BRef.heap h.nextBlk)) 64).toNat + dWS (2 ^ n) + 2 * 2 ^ n)
    ⟨by simp [hza], by simp [hzf], rfl, ⟨_, rfl⟩, rfl, by show INIT_STATE ≤ INIT_STATE; decide,
      by show INIT_STATE ≤ MAX_STATE; decide⟩ (by simpa using hw) rfl
    (by simpa using g1) (by simpa using g2) (by simpa using g3) rfl (by omega) ?_ ?_ ?_) ?_
  · exact Int32.not_lt.mp hl0
  · exact Int32.not_lt.mp hl9
  · have p9 : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn1
    have p15 : 2 ^ n ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hn2
    have hw32 : (Int32.ofNat (2 ^ n)).toUInt32.toNat = 2 ^ n := wsize_toNat n hn2
    refine ⟨?_, ?_, ?_, ?_, ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [hw32]; omega
    · simp only [hl32]; omega
    · simp only [UInt32.toNat_mul, hl32]; simp; omega
    · simp only [UInt32.toNat_mul, UInt32.toNat_sub_of_le _ _ (lb_one_le l hl32 (by omega)), hl32]; simp; omega
    · simp only [wbuf_toNat _ (by rw [hw32]; omega), hw32]; omega
    · simp only [hw32]; omega
    · omega
    · simp only [hl32]; omega
    · simp only [hl32]
    · exact ⟨Int32.not_lt.mp hs0, Int32.not_lt.mp hs4⟩
  rintro r H' ⟨rfl, A, B, C, c, lm, ib, d', rfl, hd', hA, hB, hC, RL⟩
  obtain ⟨q1, q2, q0, q3, q4, q5, q6, q7⟩ := RL.post _ d' (SH_bytes _ _ _ _ _ _) hd' A B C c lm ib
  refine ⟨⟨?_, fun _ => ?_⟩, fun _ _ _ _ _ _ _ => rfl⟩
  · refine dframe_of (fun j hj => by simp [SH, AH, upd_ne _ _ _ _ hj]) rfl (fun c hc => ?_) rfl rfl rfl rfl
      (by simp [SH, AH])
    have hne : c ≠ h.nextBlk := Nat.ne_of_lt hc
    simp [SH, AH, upd_ne _ _ _ _ hne]
  · refine ⟨i, _, h.nextBlk, _, dAllocRec h.nextBlk (PADSZ (h.baseAddr (.heap h.nextBlk)) 64).toNat (dWS (2 ^ n))
      (2 ^ n) z1.zfree, rfl, SH_streams _ _ _ _ _ _, rfl, SH_dstate _ _ _ _ _ _, ?_, ?_⟩
    · show (match (SH _ _ _ _ _ _).bytes h.nextBlk with | some _ => _ | none => none) = _
      rw [SH_bytes]
      exact upd_same _ _ _
    · refine ⟨by simp [rkZ, hza], by simp [rkZ, hzf], rfl, rfl, rfl, by simp [dAllocRec, hzf], rfl, ?_, ?_, ?_,
        ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact st_lo wrap
      · exact st_hi wrap
      · exact hw
      · exact wsize_ne n hn2
      · exact ⟨_, rfl⟩
      · exact ⟨_, d', SH_bytes _ _ _ _ _ _, rfl, by rw [hd', hdsz]; omega⟩
      · exact ⟨Int32.not_lt.mp hl0, Int32.not_lt.mp hl9⟩
      · exact ⟨hA, hB, hC⟩
      · exact q1
      · exact q2
      · exact q0
      · exact q3
      · exact q4
      · exact q5
      · exact q6
      · exact q7
      · obtain ⟨d0, _, _, _, pbo0, hd0, -, -, -, -, -, -, -, -, hs, -⟩ := q2
        exact ⟨d0, _, hd0, hs, fun j hj => by simp [DeflateInv.dview, lmS, trS, rkS] at hj⟩
      · exact fun hn => absurd (by simp [DeflateInv.dview, lmS, trS, rkS]) hn
      · exact fun _ _ => by simp [DeflateInv.dview, lmS, trS, rkS]
      · simp [DeflateInv.dview, lmS, trS, rkS]
      · simp [DeflateInv.dview, lmS, trS, rkS]

/-- The `windowBits` decoding and the tail, on a stream whose allocator fields are the defaults. -/
theorem decode_sat {h : Heap} {i : Nat} (z1 : ZStream) (hza : z1.zalloc = .zcalloc) (hzf : z1.zfree = .zcfree)
    (level method wb ml strat : Int32) :
    SF (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none) { h with streams := upd h.streams i (some z1) } (do
        let (wrap, windowBits, bad) ←
          if wb < 0 then do
            if wb < -MAX_WBITS then pure (0, wb, true)
            else pure ((0 : Int32), ← chkI32 (-wb.toInt), false)
          else if wb > MAX_WBITS then pure (2, wb - 16, false)
          else pure ((1 : Int32), wb, false)
        if bad then return Z_STREAM_ERROR
        init2Tail (some i) level method windowBits ml strat wrap : M Int32)
      (fun r h' => InitPost h i r h' ∧ (h.allocOk h.nalloc = true → level = 6 → method = 8 → wb = 15 → ml = 8 →
        strat = 0 → r = Z_OK)) := by
  have fr0 : DFrame h { h with streams := upd h.streams i (some z1) } [i] [] [] [] :=
    dframe_of (fun j hj => upd_ne _ _ _ _ hj) rfl (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl rfl rfl rfl (Nat.le_refl _)
  dsimp only
  by_cases h1 : wb < 0
  · rw [ite_t h1]
    by_cases h2 : wb < -MAX_WBITS
    · rw [ite_t h2]
      refine SF.bind_sat (Sat.of_eq rfl ?_)
      refine SF.pure ⟨⟨fr0, fun e => absurd e (by decide)⟩, ?_⟩
      rintro - - - rfl; exact absurd h1 (by decide)
    · rw [ite_f h2]
      have t1 := Int32.lt_iff_toInt_lt.mp h1
      have t2 := Int32.not_lt.mp h2
      rw [Int32.le_iff_toInt_le] at t2
      have e15 : (-MAX_WBITS).toInt = -15 := rfl
      rw [e15] at t2
      have t1' : wb.toInt < 0 := by simpa using t1
      have ec : (Int32.ofInt (-wb.toInt)).toInt = -wb.toInt := by
        have : Int32.size = 4294967296 := rfl
        rw [Int32.toInt_ofInt, this]; exact Int.bmod_eq_of_le (by omega) (by omega)
      rw [chk_eq (Int32.ofInt (-wb.toInt)) ec, pure_bind_M]
      refine SF.bind_sat (Sat.of_eq rfl ?_)
      refine SF.mono (tail_sat z1 hza hzf level method _ ml strat 0 (Or.inl rfl)) ?_
      rintro r h' ⟨post, _⟩
      refine ⟨post, ?_⟩
      rintro - - - rfl; exact absurd h1 (by decide)
  · rw [ite_f h1]
    by_cases h2 : wb > MAX_WBITS
    · rw [ite_t h2]
      refine SF.bind_sat (Sat.of_eq rfl ?_)
      refine SF.mono (tail_sat z1 hza hzf level method _ ml strat 2 (Or.inr (Or.inr rfl))) ?_
      rintro r h' ⟨post, _⟩
      refine ⟨post, ?_⟩
      rintro - - - rfl; exact absurd h2 (by decide)
    · rw [ite_f h2]
      refine SF.bind_sat (Sat.of_eq rfl ?_)
      refine SF.mono (tail_sat z1 hza hzf level method _ ml strat 1 (Or.inr (Or.inl rfl))) ?_
      rintro r h' ⟨post, nv⟩
      exact ⟨post, fun a b c d e f => nv a b c d e f rfl⟩

theorem rdZ_app {α : Type} {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) (f : ZStream → α) :
    rdZ (some i) f h = .ok (f z, h) := by
  simp [rdZ, bind_app, ldStream_app hz]

theorem wrZ_upd {h : Heap} {i : Nat} {z : ZStream} (f : ZStream → ZStream) :
    wrZ (some i) f { h with streams := upd h.streams i (some z) } =
      .ok ((), { h with streams := upd h.streams i (some (f z)) }) := by
  simp [wrZ, stStream, ldStream, bind_app, upd_upd]

theorem rdZ_upd {α : Type} {h : Heap} {i : Nat} {z : ZStream} (f : ZStream → α) :
    rdZ (some i) f { h with streams := upd h.streams i (some z) } =
      .ok (f z, { h with streams := upd h.streams i (some z) }) := by
  simp [rdZ, bind_app, ldStream]

theorem init2_sat {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree)
    (level method wb ml strat : Int32) :
    SF (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none) h (deflateInit2 (some i) level method wb ml strat)
      (fun r h' => InitPost h i r h' ∧ (h.allocOk h.nalloc = true → level = 6 → method = 8 → wb = 15 → ml = 8 →
        strat = 0 → r = Z_OK)) := by
  rw [init2_eq]
  simp only [show (some i == none) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  try dsimp only
  refine SF.bind_sat (Sat.of_eq (wrZ_app hz _) ?_)
  refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
  dsimp only
  rcases hza with ha | ha <;> rcases hzf with hf | hf
  · simp only [ha, show (FnPtr.null == FnPtr.null) = true from rfl, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
    dsimp only
    simp only [hf, show (FnPtr.null == FnPtr.null) = true from rfl, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.mono (decode_sat _ (by simp) (by simp) _ method wb ml strat) ?_
    rintro r h' ⟨post, nv⟩
    exact ⟨post, fun a b c d e f => nv a (by rw [b]; rfl) c d e f⟩
  · simp only [ha, show (FnPtr.null == FnPtr.null) = true from rfl, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
    dsimp only
    simp only [hf, show (FnPtr.zcfree == FnPtr.null) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine SF.mono (decode_sat _ (by simp) (by simp) _ method wb ml strat) ?_
    rintro r h' ⟨post, nv⟩
    exact ⟨post, fun a b c d e f => nv a (by rw [b]; rfl) c d e f⟩
  · simp only [ha, show (FnPtr.zcalloc == FnPtr.null) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
    dsimp only
    simp only [hf, show (FnPtr.null == FnPtr.null) = true from rfl, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (wrZ_upd _) ?_)
    refine SF.mono (decode_sat _ (by simp) (by simp) _ method wb ml strat) ?_
    rintro r h' ⟨post, nv⟩
    exact ⟨post, fun a b c d e f => nv a (by rw [b]; rfl) c d e f⟩
  · simp only [ha, show (FnPtr.zcalloc == FnPtr.null) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine SF.bind_sat (Sat.of_eq (rdZ_upd _) ?_)
    dsimp only
    simp only [hf, show (FnPtr.zcfree == FnPtr.null) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine SF.mono (decode_sat _ (by simp) (by simp) _ method wb ml strat) ?_
    rintro r h' ⟨post, nv⟩
    exact ⟨post, fun a b c d e f => nv a (by rw [b]; rfl) c d e f⟩

end ZlibNgF.Proof.DeflateInit
