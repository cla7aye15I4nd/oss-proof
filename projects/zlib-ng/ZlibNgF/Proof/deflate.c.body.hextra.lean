import ZlibNgF.Proof.«deflate.c.body.hgzip»
import ZlibNgF.Proof.«deflate.c.fill_window.inv»

/-!
# `deflate`: the gzip extra field (`ZlibNgF`)

`extra_ok`: the `EXTRA_STATE` part of `deflateHeaders`. The extra field is copied into `pending_buf` from the saved
index `gzindex` on; while it does not fit, `pending_buf` is filled, the header CRC updated (`HCRC_UPDATE`, `hcrc_SH`)
and the pending output flushed, and the part returns when output is left pending. The loop measure is the length
left (`left`, which a filling copy lowers: `pending < pending_buf_size` there).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get memcpy_heap)

/-! ## Heap steps -/

/-- A `memcpy` into block `b` from another object. -/
theorem memcpy_in {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {r : BRef}
    {o n od : Nat} {src : Array UInt8} (hr : r ≠ .heap b) (hs : Space.get H r = some src) (h1 : od + n ≤ d.size)
    (h2 : o + n ≤ src.size) :
    Ptr.memcpy (.ref (.heap b) od) (.ref r o) n (SH H i z b st d) =
      .ok ((), SH H i z b st (copyFold src od o (List.range' 0 n) d)) := by
  rw [memcpy_heap (SH_bytes _ _ _ _ _ _) (by rw [DeflateSetDict.space_SH_ne hr]; exact hs) hr h1 h2]
  simp [SH, ZlibNgF.Proof.InflateInv.upd_upd]

theorem add_SH' {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {off k : Nat}
    (hk : off + k ≤ d.size) :
    Ptr.add (Ptr.ref (BRef.heap b) off) (k : Int) (SH H i z b st d) = .ok (.ref (.heap b) (off + k), SH H i z b st d) :=
  InflateWindow.add_ref (SH_bytes _ _ _ _ _ _) hk

/-- `HCRC_UPDATE(beg)` on an `SH` heap: only `adler` changes. -/
theorem hcrc_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {k : Nat}
    {g : GzHeader} {pbo : Nat} (hgz : st.gzhead = .val (some k)) (hg : H.gzheaders k = some g)
    (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hct : H.crcTable = ZlibNg.Crc32Tbl.crc_table)
    (hroom : pbo + st.pending.toNat ≤ d.size) (beg : UInt32) (hbeg : beg ≤ st.pending) :
    Sat (SH H i z b st d) (HCRC_UPDATE (some i) (some b) beg)
      (fun _ H' => ∃ a, H' = SH H i { z with adler := a } b st d) := by
  unfold HCRC_UPDATE
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine sat_ival hgz ?_
  refine Sat.bind (Sat.of_eq (ldHeader_SH hg) ?_)
  by_cases hc : (g.hcrc != 0 && decide (st.pending > beg)) = true
  · rw [ite_t hc]
    have hb := UInt32.le_iff_toNat_le.mp hbeg
    refine Sat.bind (Sat.of_eq ldStream_SH ?_)
    refine sat_ival hpb ?_
    refine Sat.bind (Sat.of_eq (add_SH' (k := beg.toNat) (by omega)) ?_)
    obtain ⟨v, ev, -⟩ := ZlibNgF.Proof.Crc32.crc32_small_ok (h := SH H i z b st d) hct (r := .heap b) (data := d)
      (SH_bytes _ _ _ _ _ _) z.adler.toUInt32 (pbo + beg.toNat) (st.pending - beg).toUInt64
      (by rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ hbeg]; omega)
    refine Sat.bind (Sat.of_eq ev ?_)
    exact Sat.of_eq (wrZ_SH _) ⟨_, rfl⟩
  · rw [ite_f hc]
    exact Sat.pure ⟨z.adler, rfl⟩

/-! ## The header's buffers -/

/-- The registered header's buffers, as `DStreamIO` gives them, with the header record. -/
theorem hdr_rd {h H : Heap} {i b : Nat} {st : DeflateState} {k : Nat} {g : GzHeader} (R : Run h i b H)
    (hst : H.dstate b = some st) (hgz : st.gzhead = .val (some k)) (hg : H.gzheaders k = some g) :
    NullOrRead H g.extra g.extra_len.toNat ∧ NotInBlock b g.extra ∧
      (g.name = .null ∨ ∃ n, CStringLen H g.name n) ∧ (∀ n, CStringLen H g.name n → NotInBlock b g.name) ∧
      (g.comment = .null ∨ ∃ n, CStringLen H g.comment n) ∧
      (∀ n, CStringLen H g.comment n → NotInBlock b g.comment) := by
  obtain ⟨z, hz, hb⟩ := R.blk
  obtain ⟨z0, b0, hp, ⟨i0, e0, hz0⟩, hb0, ⟨b1, st1, ⟨⟨z1, ⟨i1, e1, hz1⟩, hb1⟩, hst1⟩, hg1⟩, hhd, -, -, -, hdj⟩ :=
    R.io
  obtain rfl := Option.some.inj e0
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj (hz.symm.trans hz0)
  obtain rfl := Option.some.inj (hz.symm.trans hz1)
  obtain rfl := Option.some.inj (hb.symm.trans hb0)
  obtain rfl := Option.some.inj (hb.symm.trans hb1)
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  rw [hgz] at hg1
  have hpk : hp = some k := by injection hg1 with e; exact e.symm
  obtain ⟨g', hg', hx, hn, hc⟩ := hhd k hpk
  obtain rfl := Option.some.inj (hg.symm.trans hg')
  exact ⟨hx, (hdj _ (.inr ⟨k, hpk, g, hg, .inl rfl⟩)).2, hn,
    fun n c => (hdj _ (.inr ⟨k, hpk, g, hg, .inr (.inl ⟨n, c, rfl⟩)⟩)).2, hc,
    fun n c => (hdj _ (.inr ⟨k, hpk, g, hg, .inr (.inr ⟨n, c, rfl⟩)⟩)).2⟩

/-- A C string outside block `b` keeps its length on an `SH` heap. -/
theorem cstr_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {p : BPtr}
    {n : Nat} (c : CStringLen H p n) (nb : NotInBlock b p) : CStringLen (SH H i z b st d) p n :=
  DeflateSide.cstr_get c fun r off e => DeflateSetDict.space_SH_ne (by
    intro hr; subst hr; exact nb off e)

/-! ## The loop -/

/-- The loop condition of the extra field's copy. -/
def exCond (st : StatePtr) : Bool × UInt32 × UInt32 → M (Bool × Bool × UInt32 × UInt32) :=
  fun ((r, beg, left) : Bool × UInt32 × UInt32) => do
    if r then return (false, (r, beg, left))
    let s ← ldDState st
    return (s.pending + left > s.pending_buf_size, (r, beg, left))

/-- The loop body of the extra field's copy. -/
def exBody (st : StatePtr) (strm : StreamPtr) (gh : HeaderPtr) : Bool × UInt32 × UInt32 → M (Bool × UInt32 × UInt32) :=
  fun ((_, beg, left) : Bool × UInt32 × UInt32) => do
    let s ← ldDState st
    let copy := s.pending_buf_size - s.pending
    let g ← ldHeader gh
    Ptr.memcpy (← (← s.pending_buf.get).add s.pending.toNat) (← g.extra.add s.gzindex.toNat) copy.toNat
    wrD st fun s => { s with pending := s.pending_buf_size }
    HCRC_UPDATE strm st beg
    wrD st fun s => { s with gzindex := s.gzindex + copy }
    ZlibNg.DeflateP.flush_pending strm
    if ← pendingReturn st then return (true, beg, left)
    pure (false, 0, left - copy)

/-- `status = NAME_STATE` (`deflate.c:911`). -/
def exEnd (st : StatePtr) : M Bool := do
  wrD st fun s => { s with status := NAME_STATE }
  return false

/-- The copy of the rest of the extra field (`deflate.c:905-909`). -/
def exTail (st : StatePtr) (strm : StreamPtr) (gh : HeaderPtr) (beg left : UInt32) : M Bool := do
  let s ← ldDState st
  let g ← ldHeader gh
  Ptr.memcpy (← (← s.pending_buf.get).add s.pending.toNat) (← g.extra.add s.gzindex.toNat) left.toNat
  wrD st fun s => { s with pending := s.pending + left }
  HCRC_UPDATE strm st beg
  wrD st fun s => { s with gzindex := 0 }
  exEnd st

theorem extra_eq (st : StatePtr) (strm : StreamPtr) :
    headersExtra st strm = (do
      let gh ← (← ldDState st).gzhead.get
      if (← ldHeader gh).extra != .null then
        let s ← ldDState st
        let left := ((← ldHeader gh).extra_len &&& 0xffff) - s.gzindex
        let (r, beg, left) ← cwhile (exCond st) (exBody st strm gh) (false, s.pending, left)
        if r then return true
        exTail st strm gh beg left
      else exEnd st) := by
  rfl

/-! ## The loop's invariant -/

/-- The gzip-header facts that stay during a call: the header record `g` of `k` (in the heap at entry `h`). -/
theorem run_gz {h H : Heap} {i b : Nat} (R : Run h i b H) {k : Nat} {g : GzHeader} (hg : h.gzheaders k = some g) :
    H.gzheaders k = some g := by
  obtain ⟨⟨-, fg, -⟩, -⟩ := R.frame
  rw [fg k (by simp)]; exact hg

/-- The state inside the copy of the extra field: `EXTRA_STATE`, no symbols, `pending_out` at `pending_buf`, fewer
than `pending_buf_size` pending bytes from `beg` on, `gzindex + left` the field's length. -/
def EF (h : Heap) (i b k : Nat) (g : GzHeader) (L : Int32) (beg left : UInt32) (H : Heap) : Prop :=
  Run h i b H ∧ h.gzheaders k = some g ∧ g.extra ≠ .null ∧ ∀ st, H.dstate b = some st →
    st.status = EXTRA_STATE ∧ st.sym_next = 0 ∧ st.pending_out = st.pending_buf ∧
    st.pending < st.pending_buf_size ∧ beg ≤ st.pending ∧
    st.gzindex.toNat + left.toNat = (g.extra_len &&& 0xffff).toNat ∧ st.gzhead = .val (some k) ∧ st.last_flush = L

/-- The loop's invariant. -/
def EI (h : Heap) (i b k : Nat) (g : GzHeader) (L : Int32) (s : Bool × UInt32 × UInt32) (H : Heap) : Prop :=
  (s.1 = true → Run h i b H ∧ LastM1 H b) ∧ (s.1 = false → EF h i b k g L s.2.1 s.2.2 H)

/-- The facts of the stream's state and block under `EF`. -/
structure EFacts (h : Heap) (i b k : Nat) (g : GzHeader) (L : Int32) (beg left : UInt32) (H : Heap) (z : ZStream)
    (st : DeflateState) (d : Array UInt8) (pbo : Nat) (r : BRef) (o : Nat) (src : Array UInt8) : Prop where
  run : Run h i b (SH H i z b st d)
  e : SH H i z b st d = H
  hst : H.dstate b = some st
  hg : H.gzheaders k = some g
  pb : st.pending_buf = .val (.ref (.heap b) pbo)
  room : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size
  lb : 128 ≤ st.lit_bufsize.toNat
  lb2 : st.lit_bufsize.toNat ≤ 32768
  pbs : st.pending_buf_size.toNat = 4 * st.lit_bufsize.toNat
  status : st.status = EXTRA_STATE
  sym : st.sym_next = 0
  pout : st.pending_out = st.pending_buf
  plt : st.pending.toNat < st.pending_buf_size.toNat
  beg : beg.toNat ≤ st.pending.toNat
  idx : st.gzindex.toNat + left.toNat = (g.extra_len &&& 0xffff).toNat
  gz : st.gzhead = .val (some k)
  wrap : st.wrap = 2
  xe : g.extra = .ref r o
  rb : r ≠ .heap b
  hsrc : Space.get H r = some src
  xlen : o + g.extra_len.toNat ≤ src.size
  lf : st.last_flush = L

theorem ef_facts {h H : Heap} {i b k : Nat} {g : GzHeader} {L : Int32} {beg left : UInt32}
    (E : EF h i b k g L beg left H) : ∃ z st d pbo r o src, EFacts h i b k g L beg left H z st d pbo r o src := by
  obtain ⟨R, hg0, hxn, F⟩ := E
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, e, c⟩ := R.live
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := F st hst
  have hg := run_gz R hg0
  obtain ⟨hx, nbx, -⟩ := hdr_rd R hst f7 hg
  obtain ⟨r, o, src, hxe, hsrc, hle⟩ := hx.resolve_left hxn
  obtain ⟨d0, wo, po, ho, pbo, hd0, -, -, -, hpb, -, -, -, l4, -⟩ := c.lay
  obtain rfl := Option.some.inj (hd.symm.trans hd0)
  obtain ⟨-, -, -, k1, k2, k3, -⟩ := c.sizes
  have hw2 : st.wrap = 2 := (R.side st hst).2.2.1.1 (Or.inr (Or.inl f1))
  exact ⟨z, st, d, pbo, r, o, src, ⟨by rw [e]; exact R, e, hst, hg, hpb, l4, k1, k2, k3, f1, f2, f3,
    UInt32.lt_iff_toNat_lt.mp f4, UInt32.le_iff_toNat_le.mp f5, f6, f7, hw2, hxe,
    fun e' => nbx o (by rw [hxe, e']), hsrc, hle, f8⟩⟩

theorem land_le (x : UInt32) : (x &&& 0xffff).toNat ≤ x.toNat := by
  rw [UInt32.toNat_and]; exact Nat.and_le_left

theorem land_lt (x : UInt32) : (x &&& 0xffff).toNat ≤ 65535 := by
  rw [UInt32.toNat_and]; exact Nat.le_trans Nat.and_le_right (by decide)

/-- The loop measure. -/
def eμ (s : Bool × UInt32 × UInt32) : Nat := if s.1 then 0 else s.2.2.toNat + 1

theorem u32_add (x y : UInt32) (h : x.toNat + y.toNat < 2 ^ 32) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

/-- The header facts of a `NAME_STATE` with `gzindex = 0`. -/
theorem hdrOk_name {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {k : Nat}
    {g : GzHeader} (hgz : st.gzhead = .val (some k)) (hg : H0.gzheaders k = some g) (hw : st.wrap = 2)
    (hs : st.status = NAME_STATE) (h0 : st.gzindex = 0) (hn : g.name = .null ∨ ∃ n, CStringLen H0 g.name n)
    (nb : ∀ n, CStringLen H0 g.name n → NotInBlock b g.name) : HdrOk (SH H0 i z b st d) b st := by
  refine ⟨fun _ => hw, fun _ => ⟨k, g, hgz, hg, fun e => absurd (hs.symm.trans e) (by decide), fun _ hnn => ?_,
    fun e => absurd (hs.symm.trans e) (by decide), fun e => absurd (hs.symm.trans e) (by decide), fun _ _ => h0⟩⟩
  obtain ⟨n, c⟩ := hn.resolve_left hnn
  exact ⟨nb n c, n, cstr_SH c (nb n c), by rw [h0]; exact Nat.zero_le _⟩

/-- One trip of the copy loop (the condition held). -/
theorem exBody_ok {h H : Heap} {i b k : Nat} {g : GzHeader} {L : Int32} {beg left : UInt32} (r0 : Bool)
    (E : EF h i b k g L beg left H)
    (hc : ∀ st, H.dstate b = some st → st.pending_buf_size.toNat < st.pending.toNat + left.toNat) :
    Sat H (exBody (some b) (some i) (some k) (r0, beg, left))
      (fun s2 H2 => EI h i b k g L s2 H2 ∧ eμ s2 < eμ (false, beg, left)) := by
  obtain ⟨z, st, d, pbo, r, o, src, F⟩ := ef_facts E
  have hc' := hc st F.hst
  have hL := land_le g.extra_len
  have hL2 := land_lt g.extra_len
  have hpl := F.plt
  have hb := F.beg
  have hidx := F.idx
  have hroom := F.room
  have hpbs := F.pbs
  have hxl := F.xlen
  have hlb := F.lb
  have hlb2 := F.lb2
  have hcopy : (st.pending_buf_size - st.pending).toNat = st.pending_buf_size.toNat - st.pending.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  rw [← F.e]
  unfold exBody
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine Sat.bind (Sat.of_eq (ldHeader_SH F.hg) ?_)
  refine sat_ival F.pb ?_
  refine Sat.bind (Sat.of_eq (add_SH' (k := st.pending.toNat) (by omega)) ?_)
  rw [F.xe]
  refine Sat.bind (Sat.of_eq (InflateWindow.add_ref (h := SH H i z b st d)
    (by rw [DeflateSetDict.space_SH_ne F.rb]; exact F.hsrc) (k := st.gzindex.toNat) (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (memcpy_in F.rb F.hsrc (od := pbo + st.pending.toNat)
    (n := (st.pending_buf_size - st.pending).toNat) (by rw [hcopy]; omega) (by rw [hcopy]; omega)) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.mono (hcrc_SH (st := { st with pending := st.pending_buf_size }) F.gz F.hg F.pb E.1.crc.1
    (by rw [copyFold_size]; dsimp only; omega) beg (by dsimp only; exact UInt32.le_iff_toNat_le.mpr (by omega))) ?_)
  rintro _ _ ⟨a, rfl⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hix : (st.gzindex + (st.pending_buf_size - st.pending)).toNat =
      st.gzindex.toNat + (st.pending_buf_size.toNat - st.pending.toNat) := by
    rw [u32_add _ _ (by rw [hcopy]; omega), hcopy]
  have R' := seg_run (d := copyFold src (pbo + st.pending.toNat) (o + st.gzindex.toNat)
    (List.range' 0 (st.pending_buf_size - st.pending).toNat) d) F.run F.pb F.sym F.pout a st.pending_buf_size st.status
    (st.gzindex + (st.pending_buf_size - st.pending)) (copyFold_size _ _ _ _ _)
    (fun j hj => copyFold_get _ _ _ _ _ _ fun x hx => by simp only [List.mem_range'_1] at hx; omega)
    (by omega) (by rw [F.status]; decide) (by rw [F.status]; decide) (by rw [F.status]; decide)
    ⟨fun _ => F.wrap, fun _ => ⟨k, g, F.gz, F.hg, fun _ _ => by dsimp only; rw [hix]; omega,
      fun e => absurd (F.status.symm.trans e) (by decide), fun e => absurd (F.status.symm.trans e) (by decide),
      fun _ e => absurd (F.xe.symm.trans e) (by simp), fun e => absurd (F.status.symm.trans e) (by decide)⟩⟩
  refine flush_ret_k R' (SH_dstate _ _ _ _ _ _) fun rr H' q _ _ => ?_
  cases rr with
  | true =>
    rw [ite_t rfl]
    exact Sat.pure ⟨⟨fun _ => ⟨q.1, q.2.1 rfl⟩, nofun⟩, by simp [eμ]⟩
  | false =>
    rw [ite_f (by simp)]
    refine Sat.pure ⟨⟨nofun, fun _ => ⟨q.1, E.2.1, E.2.2.1, fun st' hst' => ?_⟩⟩, ?_⟩
    · obtain ⟨k1, k2⟩ := q.2.2 rfl st' hst'
      obtain ⟨z', st2, al', d', -, -, hst2, -, -, -, c'⟩ := q.1.live
      obtain rfl := Option.some.inj (hst'.symm.trans hst2)
      have hlc : left.toNat - (st.pending_buf_size - st.pending).toNat = left.toNat - (st.pending_buf_size.toNat - st.pending.toNat) := by rw [hcopy]
      refine ⟨by rw [k2]; exact F.status, by rw [k2]; exact F.sym, c'.pout k1, ?_, ?_, ?_, by rw [k2]; exact F.gz,
        by rw [k2]; exact F.lf⟩
      · rw [k1, UInt32.lt_iff_toNat_lt]; rw [k2]; show 0 < st.pending_buf_size.toNat; omega
      · rw [k1]; exact UInt32.le_iff_toNat_le.mpr (by simp)
      · rw [k2]; show (st.gzindex + (st.pending_buf_size - st.pending)).toNat +
          (left - (st.pending_buf_size - st.pending)).toNat = _
        rw [hix, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), hcopy]; omega
    · simp only [eμ]
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), hcopy]
      simp; omega

/-- What the copy loop leaves. -/
def EQ (h : Heap) (i b k : Nat) (g : GzHeader) (L : Int32) (s : Bool × UInt32 × UInt32) (H : Heap) : Prop :=
  (s.1 = true → Run h i b H ∧ LastM1 H b) ∧ (s.1 = false → EF h i b k g L s.2.1 s.2.2 H ∧
    ∀ st, H.dstate b = some st → st.pending.toNat + s.2.2.toNat ≤ st.pending_buf_size.toNat)

/-- The loop condition and, when it holds, the trip. -/
theorem exCond_ok {h : Heap} {i b k : Nat} {g : GzHeader} {L : Int32} (s : Bool × UInt32 × UInt32) (H : Heap)
    (I : EI h i b k g L s H) :
    Sat H (exCond (some b) s) (fun cs H1 =>
      (cs.1 = true → Sat H1 (exBody (some b) (some i) (some k) cs.2)
        (fun s2 H2 => EI h i b k g L s2 H2 ∧ eμ s2 < eμ s)) ∧ (cs.1 = false → EQ h i b k g L cs.2 H1)) := by
  obtain ⟨rr, beg, left⟩ := s
  cases rr with
  | true =>
    unfold exCond
    dsimp only
    rw [ite_t rfl]
    exact Sat.pure ⟨nofun, fun _ => ⟨fun _ => I.1 rfl, nofun⟩⟩
  | false =>
    have E : EF h i b k g L beg left H := I.2 rfl
    obtain ⟨z, st, d, pbo, r, o, src, F⟩ := ef_facts E
    have hL2 := land_lt g.extra_len
    have hidx := F.idx
    have hpl := F.plt
    have hpbs := F.pbs
    have hlb2 := F.lb2
    unfold exCond
    dsimp only
    rw [ite_f (by simp)]
    rw [← F.e]
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    have hadd : (st.pending + left).toNat = st.pending.toNat + left.toNat := u32_add _ _ (by omega)
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨nofun, fun _ => ⟨by rw [F.e]; exact E, fun st' hst' => ?_⟩⟩⟩
    · have hc' : st.pending_buf_size.toNat < st.pending.toNat + left.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc); rwa [hadd] at this
      rw [F.e]
      exact exBody_ok false E fun st' hst' => by
        obtain rfl := Option.some.inj (F.hst.symm.trans hst'); exact hc'
    · rw [F.e] at hst'
      obtain rfl := Option.some.inj (F.hst.symm.trans hst')
      have := of_decide_eq_false hc
      have h2 : ¬ st.pending_buf_size.toNat < (st.pending + left).toNat := fun x => this (UInt32.lt_iff_toNat_lt.mpr x)
      rw [hadd] at h2
      show st.pending.toNat + left.toNat ≤ _
      omega

/-- The rest of the extra field fits: the copy, `gzindex = 0`, `NAME_STATE`. -/
theorem exTail_ok {h H : Heap} {i b k : Nat} {g : GzHeader} {L : Int32} {beg left : UInt32}
    (E : EF h i b k g L beg left H)
    (hfit : ∀ st, H.dstate b = some st → st.pending.toNat + left.toNat ≤ st.pending_buf_size.toNat) :
    Sat H (exTail (some b) (some i) (some k) beg left)
      (HRet h i b fun st' => HK NAME_STATE st' ∧ st'.last_flush = L) := by
  obtain ⟨z, st, d, pbo, r, o, src, F⟩ := ef_facts E
  have hf := hfit st F.hst
  have hL := land_le g.extra_len
  have hL2 := land_lt g.extra_len
  have hpl := F.plt
  have hb := F.beg
  have hidx := F.idx
  have hroom := F.room
  have hpbs := F.pbs
  have hxl := F.xlen
  have hlb2 := F.lb2
  obtain ⟨-, -, hn, nbn, -⟩ := hdr_rd E.1 F.hst F.gz F.hg
  have hadd : (st.pending + left).toNat = st.pending.toNat + left.toNat := u32_add _ _ (by omega)
  rw [← F.e]
  unfold exTail exEnd
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine Sat.bind (Sat.of_eq (ldHeader_SH F.hg) ?_)
  refine sat_ival F.pb ?_
  refine Sat.bind (Sat.of_eq (add_SH' (k := st.pending.toNat) (by omega)) ?_)
  rw [F.xe]
  refine Sat.bind (Sat.of_eq (InflateWindow.add_ref (h := SH H i z b st d)
    (by rw [DeflateSetDict.space_SH_ne F.rb]; exact F.hsrc) (k := st.gzindex.toNat) (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (memcpy_in F.rb F.hsrc (od := pbo + st.pending.toNat) (n := left.toNat)
    (by omega) (by omega)) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.mono (hcrc_SH (st := { st with pending := st.pending + left }) F.gz F.hg F.pb E.1.crc.1
    (by rw [copyFold_size]; dsimp only; omega) beg
    (by dsimp only; exact UInt32.le_iff_toNat_le.mpr (by omega))) ?_)
  rintro _ _ ⟨a, rfl⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have R' := seg_run (d := copyFold src (pbo + st.pending.toNat) (o + st.gzindex.toNat)
    (List.range' 0 left.toNat) d) F.run F.pb F.sym F.pout a (st.pending + left) NAME_STATE 0 (copyFold_size _ _ _ _ _)
    (fun j hj => copyFold_get _ _ _ _ _ _ fun x hx => by simp only [List.mem_range'_1] at hx; omega)
    (by omega) (by decide) (by decide) (by decide)
    (hdrOk_name F.gz F.hg F.wrap rfl rfl hn nbn)
  refine Sat.pure ⟨R', nofun, fun _ st' hst' => ?_⟩
  rw [SH_dstate] at hst'; obtain rfl := Option.some.inj hst'
  exact ⟨.inr ⟨rfl, F.sym, F.pout, UInt32.le_iff_toNat_le.mpr (by dsimp only; omega)⟩, F.lf⟩

/-- No extra field: `NAME_STATE` (`gzindex` is 0 already). -/
theorem exEnd_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = EXTRA_STATE) (h0 : st.sym_next = 0) (hpo : st.pending_out = st.pending_buf)
    (hpl : st.pending < st.pending_buf_size) {k : Nat} {g : GzHeader} (hgz : st.gzhead = .val (some k))
    (hg : H.gzheaders k = some g) (hx : g.extra = .null) :
    Sat H (exEnd (some b)) (HRet h i b fun st' => HK NAME_STATE st' ∧ st'.last_flush = st.last_flush) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  obtain ⟨-, -, hn, nbn, -⟩ := hdr_rd R hst hgz hg
  obtain ⟨hw, H2⟩ := (R.side st hst).2.2.1
  obtain ⟨k', g', hgz', hg', -, -, -, x4, -⟩ := H2 (Or.inl hs)
  rw [hgz] at hgz'; obtain rfl : k = k' := by injection hgz' with e1; injection e1
  obtain rfl := Option.some.inj (hg.symm.trans hg')
  have hi0 := x4 hs hx
  obtain ⟨d0, wo, po, ho, pbo, hd0, -, -, -, hpb, -⟩ := c.lay
  obtain ⟨-, -, -, -, -, l3, -⟩ := c.sizes
  rw [← e] at R ⊢
  unfold exEnd
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have R' := seg_run R hpb h0 hpo z.adler st.pending NAME_STATE st.gzindex rfl (fun _ _ => rfl)
    (by have := UInt32.lt_iff_toNat_lt.mp hpl; simp only [dview] at l3; omega) (by decide) (by decide) (by decide)
    (hdrOk_name hgz hg (hw (Or.inr (Or.inl hs))) rfl hi0 hn nbn)
  refine Sat.pure ⟨R', nofun, fun _ st' hst' => ?_⟩
  rw [SH_dstate] at hst'; obtain rfl := Option.some.inj hst'
  exact ⟨.inr ⟨rfl, h0, hpo, UInt32.le_of_lt hpl⟩, rfl⟩

/-- The `EXTRA_STATE` part of `deflateHeaders`. -/
theorem extra_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = EXTRA_STATE) (h0 : st.sym_next = 0) (hpo : st.pending_out = st.pending_buf)
    (hpl : st.pending < st.pending_buf_size) :
    Sat H (headersExtra (some b) (some i))
      (HRet h i b fun st' => HK NAME_STATE st' ∧ st'.last_flush = st.last_flush) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  obtain ⟨hw, H2⟩ := (R.side st hst).2.2.1
  obtain ⟨k, g, hgz, hg, x1, -, -, -, -⟩ := H2 (Or.inl hs)
  have hg0 : h.gzheaders k = some g := by
    obtain ⟨⟨-, fg, -⟩, -⟩ := R.frame; rw [← fg k (by simp)]; exact hg
  rw [extra_eq]
  rw [← e]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine sat_ival hgz ?_
  refine Sat.bind (Sat.of_eq (ldHeader_SH hg) ?_)
  by_cases hx : (g.extra != .null) = true
  · rw [ite_t hx]
    have hxn : g.extra ≠ .null := by simpa using hx
    have hle := x1 hs hxn
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    refine Sat.bind (Sat.of_eq (ldHeader_SH hg) ?_)
    have hL2 := land_lt g.extra_len
    have E0 : EI h i b k g st.last_flush (false, st.pending, (g.extra_len &&& 0xffff) - st.gzindex) (SH H i z b st d) := by
      refine ⟨nofun, fun _ => ⟨by rw [e]; exact R, hg0, hxn, fun st' hst' => ?_⟩⟩
      rw [SH_dstate] at hst'; obtain rfl := Option.some.inj hst'
      refine ⟨hs, h0, hpo, hpl, UInt32.le_refl _, ?_, hgz, rfl⟩
      show st.gzindex.toNat + ((g.extra_len &&& 0xffff) - st.gzindex).toNat = _
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hle)]; omega
    refine Sat.bind (Sat.mono (WinInv.sat_cwhileH (EI h i b k g st.last_flush) (fun s _ => eμ s) (EQ h i b k g st.last_flush)
      (fun s H1 I => exCond_ok s H1 I) E0 (by
        have := UInt32.toNat_lt ((g.extra_len &&& 0xffff) - st.gzindex)
        simp only [eμ, fuel]; split <;> omega)) ?_)
    rintro ⟨rr, beg, left⟩ H1 Q1
    dsimp only
    cases rr with
    | true =>
      rw [ite_t rfl]
      obtain ⟨R1, l1⟩ := Q1.1 rfl
      exact Sat.pure ⟨R1, fun _ => l1, nofun⟩
    | false =>
      rw [ite_f (by simp)]
      obtain ⟨E1, f1⟩ := Q1.2 rfl
      exact exTail_ok E1 f1
  · rw [ite_f hx]
    rw [e]
    exact exEnd_ok R hst hs h0 hpo hpl hgz (by rw [← e]; exact hg) (by simpa using hx)

end ZlibNgF.Proof.DeflateBody
