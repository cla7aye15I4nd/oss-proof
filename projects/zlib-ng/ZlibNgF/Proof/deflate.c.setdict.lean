import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Proof.«deflate.c.prime»
import ZlibNgF.Proof.«adler32_c.c.safety»
import ZlibNgF.Proof.«inflate.c.steps»

/-!
# `deflateSetDictionary` (`ZlibNgF`)

On a stream with the structural invariant and a `NULL` dictionary or one of `dictLength` readable bytes outside the
library's block, `deflateSetDictionary` does not fault, keeps the invariant, and changes only the stream record and
the stream's block, given the window facts (`WindowFacts`: `fill_window`, `insert_batch`). The dictionary is fed
through `next_in` (saved and restored around the call); `fill_window` takes it into the window, and the loop
`while (s->lookahead >= STD_MIN_MATCH)` inserts the hash entries. Inside the loop `strstart` rises while
`block_start` stays, so the loop keeps `DInvW` (the invariant with `strstart - block_start` up to `2^30 + 2^16`,
bounded through the potential `strstart - block_start + lookahead + avail_in`, at most `2^30 + 32768` at the start);
the tail sets `block_start = (int)strstart` and so restores the invariant. The loop ends because `avail_in` drops on
every trip.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateSetDict
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InffastBase (sat_cwhile_rank)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)
open ZlibNgF.Proof.ChunkMem (fillFold fillFold_size fillFold_get)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## Frames -/

theorem DFrame.trans {h1 h2 h3 : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : DFrame h1 h2 S B G W)
    (g : DFrame h2 h3 S B G W) : DFrame h1 h3 S B G W := by
  refine ⟨ZlibNgF.Proof.InflateLoop.Frame.trans f.1 g.1, fun c hc hn => ?_⟩
  have hle : h1.nextBlk ≤ h2.nextBlk := f.1.2.2.2.2.2.2.2.2.2
  exact ⟨((g.2 c (by omega) hn).1).trans (f.2 c hc hn).1, ((g.2 c (by omega) hn).2).trans (f.2 c hc hn).2⟩

/-- An `SH` heap is in the frame of stream `i` and block `b`. -/
theorem dframe_SH' {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} :
    DFrame h (SH h i z b st d) [i] [b] [] [] := ZlibNgF.Proof.DeflateReset.dframe_SH h i z b st d

theorem space_SH_ne {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {r : BRef}
    (hr : r ≠ .heap b) : Space.get (SH H i z b st d) r = Space.get H r := by
  cases r with
  | heap c =>
    show (upd H.bytes b (some d)) c = H.bytes c
    exact upd_ne _ _ _ _ (fun e => hr (by rw [e]))
  | const c => rfl
  | str k => rfl


/-- The tail of `deflateSetDictionary` after the Adler-32 of the dictionary (copied from the translation; the
elaborated `if wrap == 1` repeats it in both branches). -/
def sdB (strm : StreamPtr) (st : StatePtr) (insert_batch : InsertBatchFn) (wrap : Int32) (dictionary : BPtr)
    (dictLength : UInt32) : M Int32 := do
  wrD st fun s => { s with wrap := 0 }
  let s ← ldDState st
  let hashless := HASHLESS s.level s.strategy
  let (dictionary, dictLength) ← if dictLength ≥ s.w_size then do
      if wrap == 0 then
        if !hashless then CLEAR_HASH st
        wrD st fun s => { s with strstart := 0 }
        wrD st fun s => { s with block_start := 0 }
        wrD st fun s => { s with insert := 0 }
      let s ← ldDState st
      pure (← dictionary.add (dictLength - s.w_size).toNat, s.w_size)
    else pure (dictionary, dictLength)
  let z ← ldStream strm
  let avail := z.avail_in
  let next := z.next_in
  wrZ strm fun z => { z with avail_in := dictLength }
  wrZ strm fun z => { z with next_in := dictionary }
  fill_window st
  let _ ← cwhile
    (fun (u : Unit) => do return ((← rdD st (·.lookahead)) ≥ STD_MIN_MATCH, u))
    (fun (u : Unit) => do
      let s ← ldDState st
      let str := s.strstart
      let n := s.lookahead - (STD_MIN_MATCH - 1)
      if !hashless then
        ZlibNg.InsertString.call_insert_batch insert_batch st (← (← ldDState st).window.get) str n
      wrD st fun s => { s with strstart := str + n }
      wrD st fun s => { s with lookahead := STD_MIN_MATCH - 1 }
      fill_window st
      pure u)
    ()
  wrD st fun s => { s with strstart := s.strstart + s.lookahead }
  wrD st fun s => { s with block_start := s.strstart.toInt32 }
  wrD st fun s => { s with insert := s.lookahead }
  wrD st fun s => { s with lookahead := 0, prev_length := 0, match_available := 0 }
  wrZ strm fun z => { z with next_in := next }
  wrZ strm fun z => { z with avail_in := avail }
  wrD st fun s => { s with wrap := wrap }
  return Z_OK

theorem add_in {h : Heap} {r : BRef} {off k : Nat} {a : Array UInt8} (hb : Space.get h r = some a)
    (hk : off + k ≤ a.size) : Ptr.add (Ptr.ref r off) (Int.ofNat k) h = .ok (.ref r (off + k), h) := by
  have e : ((off : Int) + Int.ofNat k).toNat = off + k := by simp only [Int.ofNat_eq_natCast]; omega
  have hc : off ≤ a.size ∧ 0 ≤ (off : Int) + Int.ofNat k ∧ (off : Int) + Int.ofNat k ≤ (a.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [Ptr.add, hb, hc, and_self, ↓reduceIte, e]

/-- One trip of the insertion loop of `deflateSetDictionary` (copied from the translation). -/
def sdBody (st : StatePtr) (insert_batch : InsertBatchFn) (hashless : Bool) (u : Unit) : M Unit := do
  let s ← ldDState st
  let str := s.strstart
  let n := s.lookahead - (STD_MIN_MATCH - 1)
  if !hashless then
    ZlibNg.InsertString.call_insert_batch insert_batch st (← (← ldDState st).window.get) str n
  wrD st fun s => { s with strstart := str + n }
  wrD st fun s => { s with lookahead := STD_MIN_MATCH - 1 }
  fill_window st
  pure u

/-- The final updates of `deflateSetDictionary` (copied from the translation). -/
def sdTail (strm : StreamPtr) (st : StatePtr) (wrap : Int32) (next : BPtr) (avail : UInt32) : M Int32 := do
  wrD st fun s => { s with strstart := s.strstart + s.lookahead }
  wrD st fun s => { s with block_start := s.strstart.toInt32 }
  wrD st fun s => { s with insert := s.lookahead }
  wrD st fun s => { s with lookahead := 0, prev_length := 0, match_available := 0 }
  wrZ strm fun z => { z with next_in := next }
  wrZ strm fun z => { z with avail_in := avail }
  wrD st fun s => { s with wrap := wrap }
  return Z_OK

/-- The part of `deflateSetDictionary` after the cut (the translation's code, with the loop body and the final
updates as `sdBody` and `sdTail`; the elaborated `let (dictionary, dictLength) ← if ...` repeats it in every
branch): feed the dictionary through `next_in`, `fill_window`, the insertion loop, and the final updates. -/
def sdC (strm : StreamPtr) (st : StatePtr) (insert_batch : InsertBatchFn) (hashless : Bool) (wrap : Int32)
    (dictionary : BPtr) (dictLength : UInt32) : M Int32 := do
  let z ← ldStream strm
  let avail := z.avail_in
  let next := z.next_in
  wrZ strm fun z => { z with avail_in := dictLength }
  wrZ strm fun z => { z with next_in := dictionary }
  fill_window st
  let _ ← cwhile
    (fun (u : Unit) => do return ((← rdD st (·.lookahead)) ≥ STD_MIN_MATCH, u))
    (sdBody st insert_batch hashless)
    ()
  sdTail strm st wrap next avail

/-- A change of the stream record and the state of an invariant stream that keeps the clauses keeps the invariant
(the `SH` heap with the same bytes). -/
theorem dinv_SH {H : Heap} {i : Nat} {z z' : ZStream} {b : Nat} {st st' : DeflateState} {d : Array UInt8}
    (hv : DInv H (some i)) (hz : H.streams i = some z) (hb : z.state = some b) (hst : H.dstate b = some st)
    (hd : H.bytes b = some d) (hzs : z'.state = z.state)
    (F : ∀ al, DCore H (some i) z b (dview st) al → DCore H (some i) z' b (dview st') al) :
    DInv (SH H i z' b st' d) (some i) := by
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, hal, c⟩ := hv
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  have hda : H.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  exact ⟨i, z', b, st', al, rfl, SH_streams _ _ _ _ _ _, by rw [hzs]; exact hb, SH_dstate _ _ _ _ _ _,
    by simp [Heap.dallocsOf, SH, hda], DCore.of_heap (h := H) (by simp [SH, hd]) (F al c)⟩

theorem SH_SH {H : Heap} {i : Nat} {z z' : ZStream} {b : Nat} {st st' : DeflateState} {d d' : Array UInt8} :
    SH (SH H i z b st d) i z' b st' d' = SH H i z' b st' d' := by
  simp only [SH, ZlibNgF.Proof.InflateInv.upd_upd]

/-- `DInput` on an `SH` heap of the same stream record. -/
theorem input_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (hi : DInput H (some i)) (hz : H.streams i = some z) (hb : z.state = some b) :
    DInput (SH H i z b st d) (some i) := by
  obtain ⟨z0, b0, ⟨i0, e, hz0⟩, hb0, hr, hnb, hnn⟩ := hi
  obtain rfl : i = i0 := Option.some.inj e
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  refine ⟨z, b, ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, hb, ?_, hnb, hnn⟩
  rcases hr with hr | ⟨r, o, data, e1, hg, hle⟩
  · exact .inl hr
  · refine .inr ⟨r, o, data, e1, ?_, hle⟩
    rw [space_SH_ne (fun e2 => hnb o (by rw [e1, e2]))]; exact hg

theorem rdD_gen {α : Type} {H : Heap} {b : Nat} {st : DeflateState} (hst : H.dstate b = some st)
    (f : DeflateState → α) : rdD (some b) f H = .ok (f st, H) := by
  simp [rdD, bind_app, ldDState, hst]

theorem clear_hash_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {ho : Nat}
    (hh : st.head = .val (.ref (.heap b) ho)) (hho : ho + 131072 ≤ d.size) :
    CLEAR_HASH (some b) (SH H i z b st d) =
      .ok ((), SH H i z b st (fillFold 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d)) := by
  simp only [CLEAR_HASH, bind_app, ldDState_SH, hh, Ival.get, pure_app]
  exact memset_SH (off := ho) (n := HASH_SIZE.toNat * 2) hho 0

/-- The potential of the insertion loop: `strstart - block_start + lookahead + avail_in` (the loop body moves bytes
from `lookahead` to `strstart`, `fill_window` from `avail_in` to `lookahead` and keeps `strstart - block_start`). -/
def pot (z : ZStream) (st : DeflateState) : Int :=
  (st.strstart.toNat : Int) - st.block_start.toInt + st.lookahead.toNat + z.avail_in.toNat

/-- The `SH` form of a heap at a stream record and a live state. -/
theorem sh_of {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (hz : H.streams i = some z)
    (hst : H.dstate b = some st) : ∃ d, H.bytes b = some d ∧ SH H i z b st d = H := by
  have hd : ∃ d, H.bytes b = some d := by
    unfold Heap.dstate at hst; split at hst <;> simp_all
  obtain ⟨d, hd⟩ := hd
  have hsts : H.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  exact ⟨d, hd, ZlibNgF.Proof.DeflateReset.SH_self hz hsts hd⟩

/-- The clauses of a `DInvW` stream at its stream record and state. -/
theorem dinvW_at {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (hv : DInvW H (some i))
    (hz : H.streams i = some z) (hb : z.state = some b) (hst : H.dstate b = some st) :
    ∃ al, H.dallocsOf b = some al ∧ DCore H (some i) z b (dview { st with block_start := st.strstart.toInt32 }) al ∧
      st.block_start.toInt ≤ st.strstart.toNat ∧
      (st.strstart.toNat : Int) - st.block_start.toInt ≤ 2 ^ 30 + 2 ^ 16 := by
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, hal, c, h1, h2⟩ := hv
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  exact ⟨al, hal, c, h1, h2⟩

/-- A change of the stream record and the state of a `DInvW` stream that keeps the clauses (the `SH` heap with the
same bytes). -/
theorem dinvW_SH {H : Heap} {i : Nat} {z z' : ZStream} {b : Nat} {st st' : DeflateState} {d : Array UInt8}
    (hv : DInvW H (some i)) (hz : H.streams i = some z) (hb : z.state = some b) (hst : H.dstate b = some st)
    (hd : H.bytes b = some d) (hzs : z'.state = z.state)
    (F : ∀ al, DCore H (some i) z b (dview { st with block_start := st.strstart.toInt32 }) al →
      DCore H (some i) z' b (dview { st' with block_start := st'.strstart.toInt32 }) al)
    (h1 : st'.block_start.toInt ≤ st'.strstart.toNat)
    (h2 : (st'.strstart.toNat : Int) - st'.block_start.toInt ≤ 2 ^ 30 + 2 ^ 16) :
    DInvW (SH H i z' b st' d) (some i) := by
  obtain ⟨al, hal, c, -, -⟩ := dinvW_at hv hz hb hst
  have hda : H.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  exact ⟨i, z', b, st', al, rfl, SH_streams _ _ _ _ _ _, by rw [hzs]; exact hb, SH_dstate _ _ _ _ _ _,
    by simp [Heap.dallocsOf, SH, hda], DCore.of_heap (h := H) (by simp [SH, hd]) (F al c), h1, h2⟩

/-- The invariant from a `DInvW` stream by a change of the stream record and the state. -/
theorem dinv_of_W_SH {H : Heap} {i : Nat} {z z' : ZStream} {b : Nat} {st st' : DeflateState} {d : Array UInt8}
    (hv : DInvW H (some i)) (hz : H.streams i = some z) (hb : z.state = some b) (hst : H.dstate b = some st)
    (hd : H.bytes b = some d) (hzs : z'.state = z.state)
    (F : ∀ al, DCore H (some i) z b (dview { st with block_start := st.strstart.toInt32 }) al →
      DCore H (some i) z' b (dview st') al) :
    DInv (SH H i z' b st' d) (some i) := by
  obtain ⟨al, hal, c, -, -⟩ := dinvW_at hv hz hb hst
  have hda : H.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  exact ⟨i, z', b, st', al, rfl, SH_streams _ _ _ _ _ _, by rw [hzs]; exact hb, SH_dstate _ _ _ _ _ _,
    by simp [Heap.dallocsOf, SH, hda], DCore.of_heap (h := H) (by simp [SH, hd]) (F al c)⟩

/-- The clauses with new `strstart`, `lookahead`, `block_start`, `insert`, `wrap` (over a generic view, so that the
kernel does not unfold state records field by field). -/
theorem DCore.mv {h : Heap} {s : StreamPtr} {z z' : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    (c : DCore h s z b v al) (hza : z'.zalloc = z.zalloc) (hzf : z'.zfree = z.zfree) (ss la : UInt32) (bs : Int32)
    (ins : UInt32) (wr : Int32) (hlook : ss.toNat + la.toNat ≤ v.window_size.toNat) (hbs : bs.toInt ≤ ss.toNat)
    (hins : ins ≤ ss) (hlo : (ss.toNat : Int) - bs.toInt ≤ 2 ^ 30) (hwr : wr = 0 ∨ wr = 1 ∨ wr = 2 ∨ wr = -1 ∨ wr = -2) :
    DCore h s z' b { v with strstart := ss, lookahead := la, block_start := bs, insert := ins, wrap := wr } al :=
  { c with
    zalloc := hza.trans c.zalloc
    zfree := hzf.trans c.zfree
    wrap := hwr
    look := hlook
    bstart := hbs
    ins := hins
    bs_lo := hlo }

theorem u32_add_toNat (x y : UInt32) (h : x.toNat + y.toNat ≤ 65536) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_add]; omega

theorem u32_toInt32_small (x : UInt32) (h : x.toNat ≤ 65536) : x.toInt32.toInt = x.toNat :=
  ZlibNgF.Proof.DeflateAlloc.u32_toInt32_toInt x (by omega)

/-- The invariant of the insertion loop of `deflateSetDictionary` on stream `i` (block `b`), started from heap `H`
(rank `m`: `avail_in`, plus one while the loop goes on). -/
def LoopI (H : Heap) (i b : Nat) (m : Nat) (_ : Unit) (H' : Heap) : Prop :=
  DInvW H' (some i) ∧ DInput H' (some i) ∧ DFrame H H' [i] [b] [] [] ∧
    ∃ z' st', H'.streams i = some z' ∧ z'.state = some b ∧ H'.dstate b = some st' ∧ st'.wrap = 0 ∧
      m = z'.avail_in.toNat + (if 3 ≤ st'.lookahead.toNat then 1 else 0) ∧ pot z' st' ≤ 2 ^ 30 + 32768

/-- `fill_window` inside the insertion loop. -/
theorem fw_ok (W : WindowFacts) {H H1 : Heap} {i b : Nat} {z1 : ZStream} {st1 : DeflateState}
    (f1 : DFrame H H1 [i] [b] [] []) (hv1 : DInvW H1 (some i)) (hz1 : H1.streams i = some z1)
    (hb1 : z1.state = some b) (hst1 : H1.dstate b = some st1) (hi1 : DInput H1 (some i)) (hw1 : st1.wrap = 0)
    (hl3 : st1.lookahead.toNat < 3) (hp1 : pot z1 st1 ≤ 2 ^ 30 + 32768) :
    Sat H1 (fill_window (some b)) (fun _ H2 => ∃ m', m' ≤ z1.avail_in.toNat ∧ LoopI H i b m' () H2) := by
  obtain ⟨H2, e, hv2, hi2, f2, i2, z2, z2', b2, st2, st2', e2', hz2, hz2', hb2, hst2, hst2', hzz, hle2, hlk,
      hcons, hdiff, -, hw2, -⟩ :=
    W.fill_window H1 (some i) b st1 hv1 ⟨i, z1, rfl, hz1, hb1, hst1⟩ hi1
      (fun h2 => absurd (hw1 ▸ h2) (by decide)) (by omega)
  obtain rfl : i = i2 := Option.some.inj e2'
  obtain rfl : z1 = z2 := Option.some.inj (hz1.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb1.symm.trans hb2)
  obtain rfl : st1 = st2 := Option.some.inj (hst1.symm.trans hst2)
  have hs : stateIds H1 (some i) = [b] := by simp [stateIds, hz1, hb1]
  rw [hs] at f2
  refine ⟨(), H2, e, _, ?_, hv2, hi2, DFrame.trans f1 f2, z2', st2', hz2', by rw [hzz]; exact hb1, hst2',
    by rw [hw2]; exact hw1, rfl, ?_⟩
  · split
    · rename_i h3
      have hne : st2'.lookahead ≠ st1.lookahead := fun e => by rw [e] at h3; omega
      have := hlk hne
      omega
    · omega
  · unfold pot at hp1 ⊢; omega

/-- The writes after the insertion of one loop trip, and `fill_window`. -/
theorem body_rest (W : WindowFacts) {H H' : Heap} {i b : Nat} {z' : ZStream} {st' st'' : DeflateState}
    {d'' : Array UInt8} (u : Unit) (f' : DFrame H H' [i] [b] [] []) (hi' : DInput H' (some i))
    (hz' : H'.streams i = some z') (hb' : z'.state = some b) (hw' : st'.wrap = 0) (hge : 3 ≤ st'.lookahead.toNat)
    (hp2 : (st'.strstart.toNat : Int) - st'.block_start.toInt + st'.lookahead.toNat + z'.avail_in.toNat ≤
      2 ^ 30 + 32768)
    (hbs1 : st'.block_start.toInt ≤ st'.strstart.toNat) (hlook : st'.strstart.toNat + st'.lookahead.toNat ≤ 65536)
    (hins : st'.insert ≤ st'.strstart)
    (hv'' : DInvW (SH H' i z' b st'' d'') (some i)) (hst'' : st'' = { st' with ins_h := st''.ins_h }) :
    Sat (SH H' i z' b st'' d'') (do
        wrD (some b) fun s => { s with strstart := st'.strstart + (st'.lookahead - (STD_MIN_MATCH - 1)) }
        wrD (some b) fun s => { s with lookahead := STD_MIN_MATCH - 1 }
        fill_window (some b)
        pure u)
      (fun s2 H2 => ∃ m', m' < z'.avail_in.toNat + (if 3 ≤ st'.lookahead.toNat then 1 else 0) ∧
        LoopI H i b m' s2 H2) := by
  have e2 : (STD_MIN_MATCH - 1 : UInt32) = 2 := rfl
  have e2n : (STD_MIN_MATCH - 1 : UInt32).toNat = 2 := by rw [e2]; rfl
  have hn2 : (st'.lookahead - (STD_MIN_MATCH - 1)).toNat = st'.lookahead.toNat - 2 := by
    rw [e2, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; rfl
  have hsum : (st'.strstart + (st'.lookahead - (STD_MIN_MATCH - 1))).toNat =
      st'.strstart.toNat + (st'.lookahead.toNat - 2) := by
    rw [u32_add_toNat _ _ (by rw [hn2]; omega), hn2]
  obtain ⟨ih, rfl⟩ : ∃ ih, st'' = { st' with ins_h := ih } := ⟨_, hst''⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  have hS := u32_toInt32_small (st'.strstart + (st'.lookahead - (STD_MIN_MATCH - 1))) (by rw [hsum]; omega)
  have hv3 := dinvW_SH (z' := z') (st' := { st' with
      ins_h := ih
      strstart := st'.strstart + (st'.lookahead - (STD_MIN_MATCH - 1))
      lookahead := STD_MIN_MATCH - 1 }) hv'' (SH_streams _ _ _ _ _ _) hb' (SH_dstate _ _ _ _ _ _)
    (SH_bytes _ _ _ _ _ _) rfl (fun al c => by
      have hl := c.look
      have hw := c.wrap
      simp only [dview] at hl hw
      exact DCore.mv c rfl rfl (st'.strstart + (st'.lookahead - (STD_MIN_MATCH - 1))) (STD_MIN_MATCH - 1)
        (st'.strstart + (st'.lookahead - (STD_MIN_MATCH - 1))).toInt32 st'.insert st'.wrap
        (by show _ ≤ st'.window_size.toNat; rw [hsum, e2n]; omega)
        (by rw [hS]; exact Int.le_refl _)
        (by rw [UInt32.le_iff_toNat_le, hsum]; have := UInt32.le_iff_toNat_le.mp hins; omega)
        (by rw [hS]; omega) hw)
    (by simp only []; rw [hsum]; omega) (by simp only []; rw [hsum]; omega)
  rw [SH_SH] at hv3
  refine Sat.bind (Sat.mono (fw_ok W (DFrame.trans f' dframe_SH') hv3
    (SH_streams _ _ _ _ _ _) hb' (SH_dstate _ _ _ _ _ _) (input_SH hi' hz' hb') hw'
    (by rw [e2n]; decide) ?_) ?_)
  · unfold pot; simp only []; rw [hsum, e2n]; omega
  · rintro _ H2 ⟨m', hm', hI2⟩
    refine Sat.pure ⟨m', ?_, hI2⟩
    split <;> omega

/-- One trip of the insertion loop. -/
theorem body_ok (W : WindowFacts) {H H' : Heap} {i b m : Nat} (ib : InsertBatchFn) (hl : Bool)
    (hI : LoopI H i b m () H') {st' : DeflateState} (hst' : H'.dstate b = some st')
    (hge : 3 ≤ st'.lookahead.toNat) :
    Sat H' (sdBody (some b) ib hl ()) (fun s2 H2 => ∃ m', m' < m ∧ LoopI H i b m' s2 H2) := by
  obtain ⟨hv', hi', f', z', st0, hz', hb', hst0, hw', rfl, hp'⟩ := hI
  obtain rfl : st' = st0 := Option.some.inj (hst'.symm.trans hst0)
  have e2 : (STD_MIN_MATCH - 1 : UInt32) = 2 := rfl
  have hp2 : (st'.strstart.toNat : Int) - st'.block_start.toInt + st'.lookahead.toNat + z'.avail_in.toNat ≤
      2 ^ 30 + 32768 := hp'
  obtain ⟨d', hd', e'⟩ := sh_of hz' hst'
  obtain ⟨al', -, cv, hbs1, hbs2⟩ := dinvW_at hv' hz' hb' hst'
  have hlook := cv.look
  have hws := cv.sizes
  have hins := cv.ins
  simp only [dview] at hlook hws hins
  have hws65 : st'.window_size.toNat ≤ 65536 := by
    rw [hws.2.2.1]; exact ZlibNgF.Proof.DeflateDict.wbuf_le _ hws.2.1
  have hn2 : (st'.lookahead - (STD_MIN_MATCH - 1)).toNat = st'.lookahead.toNat - 2 := by
    rw [e2, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; rfl
  rw [← e']
  unfold sdBody
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  by_cases hhl : (!hl) = true
  · rw [ite_t hhl]
    obtain ⟨_, wo, _, _, _, _, hwo, -⟩ := cv.lay
    simp only [dview] at hwo
    refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
    rw [hwo]
    refine Sat.bind (Sat.pure ?_); try dsimp only
    obtain ⟨st'', d'', e, hv'', hst'', -⟩ := W.insert_batch _ i z' b st' d' ib wo st'.strstart
      (st'.lookahead - (STD_MIN_MATCH - 1)) (by rw [e']; exact hv') (SH_streams _ _ _ _ _ _) hb'
      (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _) hwo (by rw [hn2]; omega) (by rw [hn2]; omega)
    rw [SH_SH] at e hv''
    exact Sat.bind (Sat.of_eq e (body_rest W () f' hi' hz' hb' hw' hge hp2 hbs1 (by omega) hins hv'' hst''))
  · rw [ite_f hhl]
    exact body_rest W () f' hi' hz' hb' hw' hge hp2 hbs1 (by omega) hins (by rw [e']; exact hv') rfl

/-- The final updates after the insertion loop. -/
theorem tail_ok {H He : Heap} {i b : Nat} {ze : ZStream} {ste : DeflateState} {wrap0 : Int32}
    (hwr : wrap0 = 0 ∨ wrap0 = 1 ∨ wrap0 = 2 ∨ wrap0 = -1 ∨ wrap0 = -2) (next : BPtr) (avail : UInt32) (hve : DInvW He (some i))
    (fe : DFrame H He [i] [b] [] []) (hze : He.streams i = some ze) (hbe : ze.state = some b)
    (hste : He.dstate b = some ste) :
    Sat He (sdTail (some i) (some b) wrap0 next avail)
      (fun _ H' => DInv H' (some i) ∧ DFrame H H' [i] [b] [] []) := by
  obtain ⟨de, hde, ee⟩ := sh_of hze hste
  obtain ⟨ale, -, ce, hb1, hb2⟩ := dinvW_at hve hze hbe hste
  have hlook := ce.look
  have hws := ce.sizes
  simp only [dview] at hlook hws
  have hws65 : ste.window_size.toNat ≤ 65536 := by
    rw [hws.2.2.1]; exact ZlibNgF.Proof.DeflateDict.wbuf_le _ hws.2.1
  have hsum : (ste.strstart + ste.lookahead).toNat = ste.strstart.toNat + ste.lookahead.toNat :=
    u32_add_toNat _ _ (by omega)
  have hS := u32_toInt32_small (ste.strstart + ste.lookahead) (by omega)
  rw [← ee]
  unfold sdTail
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.pure ⟨dinv_of_W_SH hve hze hbe hste hde rfl (fun al c =>
      DCore.mv (z' := { { ze with next_in := next } with avail_in := avail }) c rfl rfl (ste.strstart + ste.lookahead) 0 (ste.strstart + ste.lookahead).toInt32 ste.lookahead wrap0
        (by show _ ≤ ste.window_size.toNat; rw [hsum]; simp; omega) (by rw [hS, hsum]; exact Int.le_refl _)
        (by rw [UInt32.le_iff_toNat_le, hsum]; omega) (by rw [hS, hsum]; omega) hwr), ?_⟩
  exact DFrame.trans fe dframe_SH'

/-- The insertion loop and the tail of `deflateSetDictionary` (`sdC`) from the invariant after the cut. -/
theorem sdC_ok (W : WindowFacts) {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState}
    {d : Array UInt8} (hv : DInv H (some i)) (hz : H.streams i = some z) (hb : z.state = some b)
    (hst : H.dstate b = some st) (hd : H.bytes b = some d) (hw0 : st.wrap = 0) (hla0 : st.lookahead = 0)
    (ib : InsertBatchFn) (hl : Bool)
    {wrap0 : Int32} (hwr : wrap0 = 0 ∨ wrap0 = 1 ∨ wrap0 = 2 ∨ wrap0 = -1 ∨ wrap0 = -2) {r : BRef} {o : Nat} {data : Array UInt8}
    {dl : UInt32} (hrb : r ≠ .heap b) (hg : Space.get H r = some data) (hle : o + dl.toNat ≤ data.size)
    (hdl : dl.toNat ≤ 32768) :
    Sat H (sdC (some i) (some b) ib hl wrap0 (.ref r o) dl)
      (fun _ H' => DInv H' (some i) ∧ DFrame H H' [i] [b] [] []) := by
  have hsts : H.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  have e0 : SH H i z b st d = H := ZlibNgF.Proof.DeflateReset.SH_self hz hsts hd
  suffices S : Sat (SH H i z b st d) (sdC (some i) (some b) ib hl wrap0 (.ref r o) dl)
      (fun _ H' => DInv H' (some i) ∧ DFrame H H' [i] [b] [] []) by rwa [e0] at S
  unfold sdC
  refine Sat.bind (Sat.of_eq ldStream_SH ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
  have hv3 := dinv_SH (z' := { z with avail_in := dl, next_in := .ref r o }) (st' := st) hv hz hb hst hd rfl
    (fun _ c => { c with zalloc := c.zalloc, zfree := c.zfree })
  have hrefl : DFrame H H [i] [b] [] [] := ⟨InflateInit.frame_refl H _ _ _ _, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have hbs : (st.strstart.toNat : Int) - st.block_start.toInt ≤ 2 ^ 30 := by
    obtain ⟨i5, z5, b5, st5, al5, e5, L5, -, c5⟩ := live hv
    obtain rfl : i = i5 := Option.some.inj e5
    obtain rfl : z = z5 := Option.some.inj (hz.symm.trans L5.hz)
    obtain rfl : b = b5 := Option.some.inj (hb.symm.trans L5.hb)
    obtain rfl : st = st5 := Option.some.inj (hst.symm.trans L5.dstate)
    exact c5.bs_lo
  refine Sat.bind (Sat.mono (fw_ok W (DFrame.trans hrefl dframe_SH') (DInvW.of_inv hv3) (SH_streams _ _ _ _ _ _)
    hb (SH_dstate _ _ _ _ _ _) ⟨_, b, ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, hb,
    .inr ⟨r, o, data, rfl, by rw [space_SH_ne hrb]; exact hg, hle⟩, fun off e => hrb (by injection e),
    fun _ => by simp⟩ hw0 (by rw [hla0]; decide) (by unfold pot; simp only [hla0]; simp; omega)) ?_)
  rintro _ H1 ⟨m1, -, hI1⟩
  have hI1' := hI1
  refine Sat.bind (Sat.mono (sat_cwhile_rank (LoopI H i b)
    (fun _ H' => ∃ m, LoopI H i b m () H' ∧ ∀ st', H'.dstate b = some st' → st'.lookahead.toNat < 3) ?_ hI1 ?_) ?_)
  · intro m u H' hI
    have hI0 := hI
    obtain ⟨-, -, -, z', st', -, -, hst', -, -, -⟩ := hI
    refine Sat.bind (Sat.of_eq (rdD_gen hst' _) ?_)
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨_, hI0, fun st2 h2 => ?_⟩⟩
    · exact body_ok W ib hl hI0 hst' (UInt32.le_iff_toNat_le.mp (of_decide_eq_true hc))
    · obtain rfl : st' = st2 := Option.some.inj (hst'.symm.trans h2)
      have h' : st'.lookahead < STD_MIN_MATCH := UInt32.not_le.mp (of_decide_eq_false hc)
      have e3 : STD_MIN_MATCH.toNat = 3 := rfl
      rw [UInt32.lt_iff_toNat_lt, e3] at h'
      exact h'
  · obtain ⟨-, -, -, z', st', -, -, -, -, rfl, -⟩ := hI1'
    have := z'.avail_in.toNat_lt
    unfold fuel; split <;> omega
  · rintro _ He ⟨m, ⟨hve, -, fe, ze, ste, hze, hbe, hste, -⟩, -⟩
    exact tail_ok hwr _ _ hve fe hze hbe hste

/-- The state after the cut of `deflateSetDictionary` is invariant. -/
theorem inv_cut {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d d2 : Array UInt8}
    {al : DeflateAllocs} (c : DCore h (some i) z b (dview st) al) (hz : h.streams i = some z) (hb : z.state = some b)
    (hdd : h.bytes b = some d) (hst : h.dstates b = some st) (hda : h.dallocs b = some al) (a : UInt64)
    (hla : st.lookahead = 0) {ho : Nat} (hh : st.head = .val (.ref (.heap b) ho)) (ss : UInt32) (bs : Int32)
    (ins : UInt32) (h1 : bs.toInt ≤ ss.toNat) (h2 : ins ≤ ss) (h3 : ss ≤ st.strstart)
    (h4 : (ss.toNat : Int) - bs.toInt ≤ 2 ^ 30) (hsz : d2.size = d.size)
    (hout : ∀ j, (j < ho ∨ ho + 131072 ≤ j) → d2[j]! = d[j]!) :
    DInv (SH h i { z with adler := a } b
      { st with
        wrap := 0
        strstart := ss
        block_start := bs
        insert := ins } d2) (some i) := by
  have hv : DInv h (some i) := ⟨i, z, b, st, al, rfl, hz, hb, by simp [Heap.dstate, hdd, hst],
    by simp [Heap.dallocsOf, hdd, hda], c⟩
  refine ⟨i, _, b, _, al, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _, by simp [Heap.dallocsOf, SH, hda],
    ?_⟩
  obtain ⟨d0, wo, po, ho', pbo, hd0, hw, hp, hh', hpb, l1, l2, l3, l4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  obtain rfl : d = d0 := Option.some.inj (hdd.symm.trans hd0)
  simp only [dview] at hw hp hh' hpb l1 l2 l3 l4 hsb hpo hpoo hpe
  rw [hh] at hh'
  obtain rfl : ho = ho' := by injection hh' with e1; injection e1
  have hlook := c.look
  simp only [dview] at hlook
  have h3' := UInt32.le_iff_toNat_le.mp h3
  exact {
    zalloc := c.zalloc
    zfree := c.zfree
    strm := c.strm
    alloc_bufs := c.alloc_bufs
    al_state := c.al_state
    al_zfree := c.al_zfree
    al_buf := c.al_buf
    status_lo := c.status_lo
    status_hi := c.status_hi
    wrap := .inl rfl
    gzhead := c.gzhead
    w_size := c.w_size
    pbuf := c.pbuf
    head := ⟨ho, d2, SH_bytes _ _ _ _ _ _, hh, by rw [hsz]; omega⟩
    level := c.level
    trees := c.trees
    sizes := c.sizes
    lay := ⟨d2, wo, po, ho, pbo, SH_bytes _ _ _ _ _ _, hw, hp, hh, hpb, l1, l2, l3, by rw [hsz]; exact l4, hsb, poo,
      hpo, hpoo, hpe⟩
    pout := c.pout
    syms := c.syms
    bits := c.bits
    look := by simp only [dview] at hlook ⊢; rw [hla] at hlook ⊢; omega
    strategy := c.strategy
    fns := c.fns
    symv := by
      obtain ⟨d1, sbo, hd1, hs1, hv1⟩ := c.symv
      obtain rfl : d = d1 := Option.some.inj (hdd.symm.trans hd1)
      simp only [dview] at hs1 hv1
      rw [hsb] at hs1
      obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hs1 with e1; injection e1
      have hse := c.syms
      simp only [dview] at hse
      have hse' := UInt32.le_iff_toNat_le.mp hse.1
      have hlb := c.sizes
      simp only [dview] at hlb
      refine ⟨d2, _, SH_bytes _ _ _ _ _ _, hsb, hv1.of_eq fun k hk => hout _ (Or.inr (by omega))⟩
    psym := c.psym
    hdr := c.hdr
    bstart := h1
    ins := h2
    wpow := c.wpow
    lmod := c.lmod
    scratch := c.scratch
    fe_mod := c.fe_mod
    fe_hi := c.fe_hi
    bs_lo := h4
    descs := c.descs }

theorem sdB_ok (W : WindowFacts) {h : Heap} {i : Nat} {z z1 : ZStream} {b : Nat} {st : DeflateState}
    {d : Array UInt8} {al : DeflateAllocs} (c : DCore h (some i) z b (dview st) al) (hz : h.streams i = some z)
    (hb : z.state = some b) (hdd : h.bytes b = some d) (hst : h.dstates b = some st) (hda : h.dallocs b = some al)
    (hz1 : z1 = { z with adler := z1.adler }) (hla : st.lookahead = 0) (ib : InsertBatchFn) {r : BRef} {o : Nat}
    {data : Array UInt8} (hrb : r ≠ .heap b) (hg : Space.get h r = some data) {n : UInt32}
    (hle : o + n.toNat ≤ data.size) :
    Sat (SH h i z1 b st d) (sdB (some i) (some b) ib st.wrap (.ref r o) n)
      (fun _ h' => DInv h' (some i) ∧ DFrame h h' [i] [b] [] []) := by
  obtain ⟨ho, d0, hd0, hh, hho⟩ := c.head
  obtain rfl : d = d0 := Option.some.inj (hdd.symm.trans hd0)
  simp only [dview] at hh hho
  unfold sdB
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  obtain ⟨a, rfl⟩ : ∃ a, z1 = { z with adler := a } := ⟨_, hz1⟩
  have hwr := c.wrap
  simp only [dview] at hwr
  have hgS : ∀ (st' : DeflateState) (d' : Array UInt8),
      Space.get (SH h i { z with adler := a } b st' d') r = some data := fun _ _ => by rw [space_SH_ne hrb]; exact hg
  -- the tail from the `SH` heap after the cut
  have T : ∀ (ss : UInt32) (bs : Int32) (ins : UInt32) (d2 : Array UInt8) (o2 : Nat) (dl : UInt32),
      bs.toInt ≤ ss.toNat → ins ≤ ss → ss ≤ st.strstart → (ss.toNat : Int) - bs.toInt ≤ 2 ^ 30 →
      d2.size = d.size → (∀ j, (j < ho ∨ ho + 131072 ≤ j) → d2[j]! = d[j]!) → o2 + dl.toNat ≤ data.size →
      dl.toNat ≤ 32768 →
      Sat (SH h i { z with adler := a } b
          { st with
            wrap := 0
            strstart := ss
            block_start := bs
            insert := ins } d2)
        (sdC (some i) (some b) ib (HASHLESS st.level st.strategy) st.wrap (.ref r o2) dl)
        (fun _ h' => DInv h' (some i) ∧ DFrame h h' [i] [b] [] []) := by
    intro ss bs ins d2 o2 dl h1 h2 h3 h4 hsz hout hl2 hdl
    have hv0 := inv_cut c hz hb hdd hst hda a hla hh ss bs ins h1 h2 h3 h4 hsz hout
    refine Sat.mono (sdC_ok W hv0 (SH_streams _ _ _ _ _ _) hb (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _) rfl hla ib
      _ hwr hrb (hgS _ _) hl2 hdl) ?_
    rintro _ _ ⟨hv', f⟩
    exact ⟨hv', DFrame.trans dframe_SH' f⟩
  have hss := UInt32.le_refl st.strstart
  have hbs := c.bstart
  have hins := c.ins
  have hbl := c.bs_lo
  have hwsz := c.sizes
  simp only [dview] at hbs hins hbl hwsz
  by_cases hge : n ≥ st.w_size
  · rw [ite_t hge]
    have hge' := UInt32.le_iff_toNat_le.mp hge
    have hsub : (n - st.w_size).toNat = n.toNat - st.w_size.toNat := UInt32.toNat_sub_of_le _ _ hge
    by_cases hw0 : (st.wrap == 0) = true
    · rw [ite_t hw0]
      have hz0 : (0 : UInt32) ≤ 0 := UInt32.le_refl 0
      by_cases hhl : (!HASHLESS st.level st.strategy) = true
      · rw [ite_t hhl]
        refine Sat.bind (Sat.of_eq (clear_hash_SH (st := { st with wrap := 0 }) hh hho) ?_)
        try dsimp only
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
        refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
        refine Sat.bind (Sat.of_eq (add_in (hgS _ _) (k := (n - st.w_size).toNat) (by omega)) ?_); try dsimp only
        refine Sat.bind (Sat.pure ?_)
        exact T 0 0 0 (fillFold 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d) (o + (n - st.w_size).toNat) st.w_size
          (by decide) hz0 UInt32.zero_le (by decide) (fillFold_size _ _ _ _)
          (fun j hj => fillFold_get 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d j (fun x hx => by
            have e : HASH_SIZE.toNat * 2 = 131072 := rfl
            rw [e] at hx; simp only [List.mem_range'_1] at hx; omega)) (by omega) hwsz.2.1
      · rw [ite_f hhl]
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_); try dsimp only
        refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
        refine Sat.bind (Sat.of_eq (add_in (hgS _ _) (k := (n - st.w_size).toNat) (by omega)) ?_); try dsimp only
        refine Sat.bind (Sat.pure ?_)
        exact T 0 0 0 d _ _ (by decide) hz0 UInt32.zero_le (by decide) rfl (fun _ _ => rfl) (by dsimp only; omega)
          hwsz.2.1
    · rw [ite_f hw0]
      refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
      refine Sat.bind (Sat.of_eq (add_in (hgS _ _) (k := (n - st.w_size).toNat) (by omega)) ?_); try dsimp only
      refine Sat.bind (Sat.pure ?_)
      exact T _ _ _ d _ _ hbs hins hss hbl rfl (fun _ _ => rfl) (by dsimp only; omega) hwsz.2.1
  · rw [ite_f hge]
    refine Sat.bind (Sat.pure ?_)
    have hlt := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hge)
    exact T _ _ _ d _ _ hbs hins hss hbl rfl (fun _ _ => rfl) hle (by dsimp only; omega)

theorem setDict_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (d : BPtr) (n : UInt32) :
    C.run (deflateSetDictionary s d n) h = .ok (Z_STREAM_ERROR, h) := by
  simp only [C.run, deflateSetDictionary, bind_app, stateCheck_noState hn, Bool.true_or, ↓reduceIte]; rfl

/-- **`deflateSetDictionary`** on an invariant stream, given the window facts. -/
theorem setDict_inv (W : WindowFacts) {h : Heap} {s : StreamPtr} {dict : BPtr} {n : UInt32} (hv : DInv h s)
    (hd : NullOrRead h dict n.toNat) (hnb : ∀ b, StateBlock h s b → NotInBlock b dict) :
    ∃ r h', C.run (deflateSetDictionary s dict n) h = .ok (r, h') ∧ DInv h' s ∧
      DFrame h h' (streamIds s) (stateIds h s) [] [] := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  have hnb' := hnb b ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩
  obtain ⟨d, hdd⟩ := L.hd
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hdd] using hal
  rw [show stateIds h (some i) = [b] by simp [stateIds, L.hz, L.hb]]
  suffices S : Sat (SH h i z b st d) (deflateSetDictionary (some i) dict n)
      (fun _ h' => DInv h' (some i) ∧ DFrame h h' [i] [b] [] []) by
    rw [ZlibNgF.Proof.DeflateReset.SH_self L.hz L.hst hdd] at S
    obtain ⟨r, h', e, hv', f⟩ := S
    exact ⟨r, h', e, hv', f⟩
  have k : DOk i z b st := ⟨L.za, L.zf, L.hb, L.ab, L.sm, L.lo, L.hi⟩
  have e0 : SH h i z b st d = h := ZlibNgF.Proof.DeflateReset.SH_self L.hz L.hst hdd
  unfold deflateSetDictionary
  refine Sat.bind (Sat.of_eq (check_SH k) ?_)
  simp only [Bool.false_or]
  by_cases hdn : dict = .null
  · simp only [hdn, beq_self_eq_true, ↓reduceIte]
    exact Sat.pure ⟨by rw [e0]; exact hv, by rw [e0]; exact ⟨InflateInit.frame_refl h _ _ _ _, fun _ _ _ => ⟨rfl, rfl⟩⟩⟩
  have hdn' : (dict == .null) = false := by
    cases dict with
    | null => exact absurd rfl hdn
    | ref _ _ => rfl
  simp only [hdn', Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (by simp only [dstateOf]; exact rdZ_SH _) ?_); try dsimp only
  rw [L.hb]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_); try dsimp only
  by_cases hchk : (st.wrap == 2 || st.wrap == 1 && st.status != INIT_STATE || st.lookahead != 0) = true
  · rw [ite_t hchk]
    exact Sat.pure ⟨by rw [e0]; exact hv, by rw [e0]; exact ⟨InflateInit.frame_refl h _ _ _ _, fun _ _ _ => ⟨rfl, rfl⟩⟩⟩
  rw [ite_f hchk]
  obtain ⟨ib, hib⟩ := c.fns.2
  have hib' : st.insert_batch = .val ib := hib
  rw [hib']
  refine Sat.bind (Sat.pure ?_); try dsimp only
  obtain ⟨r, o, data, rfl, hg, hle⟩ := hd.resolve_left hdn
  have hrb : r ≠ .heap b := fun e => hnb' o (by rw [e])
  have hla : st.lookahead = 0 := by
    rcases Decidable.em (st.lookahead = 0) with h0 | hne
    · exact h0
    · exact absurd (by simp [hne]) hchk
  have hB : ∀ z1 : ZStream, z1 = { z with adler := z1.adler } →
      Sat (SH h i z1 b st d) (sdB (some i) (some b) ib st.wrap (.ref r o) n)
        (fun _ h' => DInv h' (some i) ∧ DFrame h h' [i] [b] [] []) := fun z1 hz1 =>
    sdB_ok W c L.hz L.hb hdd L.hst hda hz1 hla ib hrb hg hle
  by_cases hw1 : (st.wrap == 1) = true
  · rw [ite_t hw1]
    refine Sat.bind (Sat.of_eq ldStream_SH ?_); try dsimp only
    have hg' : Space.get (SH h i z b st d) r = some data := by rw [space_SH_ne hrb]; exact hg
    obtain ⟨v, ev, -⟩ := ZlibNgF.Proof.Adler32Safe.adler32_c_safe hg' z.adler.toUInt32 o n.toUInt64
      (by rw [show n.toUInt64.toNat = n.toNat from rfl]; exact hle)
    refine Sat.bind (Sat.of_eq ev ?_); try dsimp only
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_); try dsimp only
    exact hB _ rfl
  · rw [ite_f hw1]
    exact hB z rfl

end ZlibNgF.Proof.DeflateSetDict
