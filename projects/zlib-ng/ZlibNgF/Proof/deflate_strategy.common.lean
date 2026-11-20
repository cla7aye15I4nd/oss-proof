import ZlibNgF.Proof.«deflate_p.h.tally.flush»
import ZlibNgF.Proof.«deflate.c.fill_window.io»

/-!
# The loop of the tally-based strategies (`ZlibNgF`)

`deflate_huff`, `deflate_rle`, `deflate_quick`, `deflate_fast`, `deflate_medium*` and `deflate_slow` share one loop
shape: `lookahead` and `strstart` live in locals and are written back to the state (`s->lookahead = lookahead;
s->strstart = strstart;`) only before `fill_window` and `FLUSH_BLOCK`; a trip tallies a literal or a match, and a full
symbol buffer flushes the block.

* `SLF h i b H`: the frame of a strategy call on stream `i` (block `b`) from its entry heap `h` to the heap `H`: the
  invariant, valid and set buffers, the CRC tables, a change of the stream record, the block and the output buffer
  only, the output of `H` a tail of the output at entry (`OutTail`), the fields of `StratKeeps` unchanged, and the
  state at a level above 0, past its header, with no symbols when `block_start` is at `strstart` (`GapOk`).
* `SLC h i b H`: `SLF` with no pending bytes.
* `SLI h i b la ss H`: the loop invariant. The heap `H` is an `SH` heap whose state has the stale
  `lookahead` / `strstart`; with the locals `la` / `ss` written back it satisfies `SLC`, and `sym_next < sym_end`
  (the last tally did not fill the symbol buffer). `SLW` is the same without the symbol bound (after a tally that
  filled it).

The steps (`sli_fill`, `sli_tally_lit`, `sli_tally_dist`, `sli_flush`, `slc_insert`, `slc_tail`, `slc_post`) are
stated with `Sat` over the translation's own statements, so a strategy proof walks its loop body and calls them;
`slf_post` gives `StratPost` from `SLF` and the exit facts (`ExitOk`).

`GapOk` is the part of `SymsOk` about `block_start`: no symbols when it is at `strstart`. A tally advances `strstart`
past `block_start` and adds one symbol, a flush sets `block_start = strstart` and empties the symbol buffer,
`fill_window` keeps the symbols and does not bring `strstart` down to `block_start`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Strategy
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateFlush
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.FlushBlock (dframe_trans dframe_wmono dframe_nil FBPost FBKeeps flush_block_ok)
open ZlibNgF.Proof.FillIO (FillIO fill_io streamIO_in)
open ZlibNg.DeflateP

/-! ## Definitions -/

/-- No symbols wait when `block_start` is at `strstart`, and fewer than 8 bits wait in `bi_buf`. -/
def GapOk (st : DeflateState) : Prop :=
  ((st.strstart.toNat : Int) = st.block_start.toInt → st.sym_next = 0) ∧ st.bi_valid < 8

/-- The state with the locals `lookahead` / `strstart` written back. -/
abbrev FS (st : DeflateState) (la ss : UInt32) : DeflateState := { st with lookahead := la, strstart := ss }

/-- The frame of a strategy call from its entry heap `h` (see the module comment). -/
structure SLF (h : Heap) (i b : Nat) (H : Heap) : Prop where
  inv : DInv H (some i)
  io : DStreamIO H (some i)
  set : DBufsSet H (some i)
  crc : CrcGlobals H
  blk : ∃ z, H.streams i = some z ∧ z.state = some b
  blk0 : ∃ z, h.streams i = some z ∧ z.state = some b
  frame : DFrame h H [i] [b] [] (dOutputRanges h (some i))
  out : OutTail h H i
  win : ∃ st0, h.dstate b = some st0 ∧ ∀ st, H.dstate b = some st → st.window = st0.window
  keeps : ∃ st0, h.dstate b = some st0 ∧ ∀ st, H.dstate b = some st → StratKeeps st0 st
  st : ∀ st, H.dstate b = some st → 0 < st.level ∧ (st.status = BUSY_STATE ∨ st.status = FINISH_STATE) ∧ GapOk st

/-- `SLF` with no pending bytes and room for one more symbol. -/
def SLC (h : Heap) (i b : Nat) (H : Heap) : Prop :=
  SLF h i b H ∧ ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.sym_next < st.sym_end

/-- After a tally that filled the symbol buffer: the heap with the locals `la` / `ss` written back satisfies `SLF`
with no pending bytes. -/
def SLW (h : Heap) (i b : Nat) (la ss : UInt32) (H : Heap) : Prop :=
  ∃ H0 z st d, H = SH H0 i z b st d ∧ SLF h i b (SH H0 i z b (FS st la ss) d) ∧ st.pending = 0

/-- The loop invariant: the heap with the locals `la` / `ss` written back satisfies `SLC`. -/
def SLI (h : Heap) (i b : Nat) (la ss : UInt32) (H : Heap) : Prop :=
  ∃ H0 z st d, H = SH H0 i z b st d ∧ SLC h i b (SH H0 i z b (FS st la ss) d)

/-- The `avail_in` of stream `i` (the loop measure). -/
def avIn (H : Heap) (i : Nat) : Nat :=
  match H.streams i with
  | some z => z.avail_in.toNat
  | none => 0

/-! ## Heap facts -/

theorem StratKeeps.trans {a b c : DeflateState} (h1 : StratKeeps a b) (h2 : StratKeeps b c) : StratKeeps a c := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h1
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := h2
  refine ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5, f6.trans e6, f7.trans e7, fun ht => ?_⟩
  obtain ⟨g1, g2⟩ := e8 ht
  obtain ⟨g3, g4⟩ := f8 fun hb => ht ((tableAt_congr e5 e6).mp hb)
  exact ⟨UInt32.le_trans g3 g1, g4.trans g2⟩

theorem StratKeeps.refl (a : DeflateState) : StratKeeps a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩

theorem SH_SH (H : Heap) (i : Nat) (z z' : ZStream) (b : Nat) (st st' : DeflateState) (d d' : Array UInt8) :
    SH (SH H i z b st d) i z' b st' d' = SH H i z' b st' d' := by
  simp only [SH, upd_upd]

theorem dframe_refl (h : Heap) (S B G : List Nat) (W : List (BPtr × Nat)) : DFrame h h S B G W :=
  ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ data hd => ⟨data, hd, rfl, fun _ _ _ => rfl⟩,
    fun _ _ _ hn => hn, rfl, rfl, rfl, rfl, Nat.le_refl _⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem bytes_of_dstate {H : Heap} {b : Nat} {st : DeflateState} (hst : H.dstate b = some st) :
    ∃ d, H.bytes b = some d := by
  unfold Heap.dstate at hst; split at hst <;> simp_all

theorem dstates_of_dstate {H : Heap} {b : Nat} {st : DeflateState} {d : Array UInt8} (hst : H.dstate b = some st)
    (hd : H.bytes b = some d) : H.dstates b = some st := by
  simpa [Heap.dstate, hd] using hst

/-- The invariant's record and block for stream `i` of an `SH` heap. -/
theorem inv_SH {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (hv : DInv (SH H0 i z b st d) (some i)) (hb : z.state = some b) :
    ∃ al, (SH H0 i z b st d).dallocsOf b = some al ∧ DCore (SH H0 i z b st d) (some i) z b (dview st) al := by
  obtain ⟨i', z', b', st', al, e, hz, hb', hst, hal, c⟩ := hv
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : st = st' := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
  exact ⟨al, hal, c⟩

/-- The clauses of `DCore` after a change of `strstart`, `lookahead`, `block_start` and `insert`. -/
theorem dcore_set {H : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    (c : DCore H s z b v al) (ss la ins : UInt32) (bs : Int32)
    (hlook : ss.toNat + la.toNat ≤ v.window_size.toNat) (hbs : bs.toInt ≤ ss.toNat) (hins : ins ≤ ss)
    (hlo : -(2 ^ 30 + 2 ^ 16) ≤ bs.toInt) :
    DCore H s z b { v with strstart := ss, lookahead := la, block_start := bs, insert := ins } al where
  zalloc := c.zalloc
  zfree := c.zfree
  strm := c.strm
  alloc_bufs := c.alloc_bufs
  al_state := c.al_state
  al_zfree := c.al_zfree
  al_buf := c.al_buf
  status_lo := c.status_lo
  status_hi := c.status_hi
  wrap := c.wrap
  gzhead := c.gzhead
  w_size := c.w_size
  pbuf := c.pbuf
  head := c.head
  level := c.level
  trees := c.trees
  sizes := c.sizes
  lay := c.lay
  pout := c.pout
  syms := c.syms
  bits := c.bits
  look := hlook
  strategy := c.strategy
  fns := c.fns
  symv := c.symv
  psym := c.psym
  hdr := c.hdr
  bstart := hbs
  ins := hins
  wpow := c.wpow
  fe_mod := c.fe_mod
  fe_hi := c.fe_hi
  bs_lo := hlo
  descs := c.descs
  lmod := c.lmod
  lpow := c.lpow
  scratch := c.scratch
  blk := c.blk

/-- `SLF` after a change of the state record and the bytes of block `b` (sizes kept) that keeps the invariant's
clauses, the header pointer, the level and the status, and `GapOk`. -/
theorem slf_SH {h H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState} {d d' : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d))
    (hc : ∀ al, (SH H0 i z b st d).dallocsOf b = some al → DCore (SH H0 i z b st d) (some i) z b (dview st) al →
      DCore (SH H0 i z b st' d') (some i) z b (dview st') al)
    (hgz : st'.gzhead = st.gzhead) (hlv : st'.level = st.level) (hstat : st'.status = st.status)
    (hwin : st'.window = st.window) (hgap : GapOk st') (hk : StratKeeps st st') : SLF h i b (SH H0 i z b st' d') := by
  obtain ⟨z1, hz1, hb⟩ := F.blk
  obtain rfl : z = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain ⟨al, hal, c⟩ := inv_SH F.inv hb
  have hal' : (SH H0 i z b st' d').dallocsOf b = some al := by
    simpa [Heap.dallocsOf, SH] using hal
  have hS : SH (SH H0 i z b st d) i z b st' d' = SH H0 i z b st' d' := SH_SH _ _ _ _ _ _ _ _ _
  have fr : DFrame (SH H0 i z b st d) (SH H0 i z b st' d') [i] [b] [] [] := by
    rw [← hS]; exact ZlibNgF.Proof.DeflateReset.dframe_SH _ _ _ _ _ _
  obtain ⟨z2, ⟨i2, e2, hz2⟩, hnn, hni⟩ := F.set
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz2)
  have hio0 := F.io
  obtain ⟨z3, b3, hp, ⟨i3, e3, hz3⟩, hb3, -, -, hin0, hout, hnb, hdj⟩ := hio0
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz3)
  obtain rfl : b = b3 := Option.some.inj (hb.symm.trans hb3)
  obtain ⟨ob, oo, ad, hno, had, hoo⟩ := hout.resolve_left hnn
  have hob : ob ≠ b := fun e => hnb oo (by rw [hno, e])
  have O : ZlibNgF.Proof.DeflateFlush.OutOnly (SH H0 i z b st d) (SH H0 i z b st' d') b ob oo 0 :=
    ⟨rfl, rfl, fun c' hc' data hd => ⟨data, by simp only [SH] at hd ⊢; rw [upd_ne _ _ _ _ hc'] at hd ⊢; exact hd,
      rfl, fun _ _ => rfl⟩⟩
  have hrd : NullOrRead (SH H0 i z b st' d') z.next_in z.avail_in.toNat :=
    ZlibNgF.Proof.DeflateFlush.nullOrRead_out O hin0 (hdj _ (.inl rfl)).2
  refine ⟨⟨i, z, b, st', al, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _, hal', hc al hal c⟩,
    streamIO_in F.io (SH_streams _ _ _ _ _ _) hb (SH_dstate _ _ _ _ _ _) hno (Nat.zero_le _) O
      (SH_streams _ _ _ _ _ _) rfl (Nat.le_refl _) (Or.inl ⟨rfl, rfl⟩) hrd (by rw [hno]; rfl) (by simp) (SH_dstate _ _ _ _ _ _)
      hgz,
    ⟨z, ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, hnn, hni⟩, ?_, ⟨z, SH_streams _ _ _ _ _ _, hb⟩, F.blk0,
    dframe_trans F.frame (dframe_nil _ fr), ?_, ?_, ?_, fun st2 hst2 => ?_⟩
  · exact F.crc
  · obtain ⟨z0, z4, ob4, oo4, k, h0, h4, e0, e4, ek⟩ := F.out
    obtain rfl : z = z4 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans h4)
    exact ⟨z0, z, ob4, oo4, k, h0, SH_streams _ _ _ _ _ _, e0, e4, ek⟩
  · obtain ⟨st0, h0, hw⟩ := F.win
    refine ⟨st0, h0, fun st2 hst2 => ?_⟩
    obtain rfl : st' = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    rw [hwin]; exact hw st (SH_dstate _ _ _ _ _ _)
  · obtain ⟨st0, h0, hw⟩ := F.keeps
    refine ⟨st0, h0, fun st2 hst2 => ?_⟩
    obtain rfl : st' = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    exact StratKeeps.trans (hw st (SH_dstate _ _ _ _ _ _)) hk
  · obtain rfl : st' = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    obtain ⟨l1, s1, -⟩ := F.st st (SH_dstate _ _ _ _ _ _)
    exact ⟨by rw [hlv]; exact l1, by rw [hstat]; exact s1, hgap⟩

/-! ## Exit -/

/-- The record and state of stream `i` under `SLF`. -/
theorem SLF.live {h H : Heap} {i b : Nat} (F : SLF h i b H) :
    ∃ z st al, H.streams i = some z ∧ z.state = some b ∧ H.dstate b = some st ∧ H.dallocsOf b = some al ∧
      DCore H (some i) z b (dview st) al := by
  obtain ⟨z, hz, hb⟩ := F.blk
  obtain ⟨i', z', b', st, al, e, hz', hb', hst, hal, c⟩ := F.inv
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  exact ⟨z, st, al, hz, hb, hst, hal, c⟩

/-- The exit facts of a strategy call with `flush` that returns `bs`, on the state after: room for one more symbol,
no pending bytes after `block_done` / `finish_done`, no symbols after a call with a flush, no symbols and no
lookahead after `finish_started` / `finish_done`, no symbols after `block_done`. -/
def ExitOk (flush : Int32) (bs : BlockState) (st : DeflateState) : Prop :=
  st.sym_next < st.sym_end ∧ (bs = .block_done ∨ bs = .finish_done → st.pending = 0) ∧
    (flush ≠ Z_NO_FLUSH → st.sym_next = 0) ∧
    (bs = .finish_started ∨ bs = .finish_done → st.sym_next = 0 ∧ st.lookahead = 0) ∧
    (bs = .block_done → st.sym_next = 0)

/-- `StratPost` from `SLF`, the exit facts, and `LazyOk` after from `LazyOk` at entry, for a strategy entered at a
level other than 1 or with a strategy other than `Z_FIXED`. -/
theorem slf_postL {h H : Heap} {i b : Nat} (F : SLF h i b H) (flush : Int32) (bs : BlockState)
    (hn : ∀ st0, h.dstate b = some st0 → st0.level = 1 → st0.strategy ≠ Z_FIXED)
    (hL : ∀ st0, h.dstate b = some st0 → LazyOk st0 → ∀ st, H.dstate b = some st →
      LazyOk st ∧ (bs = .block_done → st.match_available = 0))
    (hs : ∀ st, H.dstate b = some st → ExitOk flush bs st) : StratPost h (some i) flush bs H := by
  obtain ⟨z, st, al, hz, hb, hst, -, -⟩ := F.live
  obtain ⟨z0, hz0, hb0⟩ := F.blk0
  have hsi : stateIds h (some i) = [b] := by simp [stateIds, hz0, hb0]
  refine ⟨F.inv, F.io, F.set, ?_, fun _ e => by obtain rfl := Option.some.inj e; exact F.out, fun e => ⟨b, st, ⟨i, z, rfl, hz, hb, hst⟩, ((hs st hst).2.1 e)⟩, ?_⟩
  · rw [hsi]; exact F.frame
  · rintro b1 st1 st' ⟨i1, z1, e1, hz1, hb1, hst1⟩ ⟨i', z', e, hz', hb', hst'⟩
    obtain rfl : i = i' := Option.some.inj e
    obtain rfl : i = i1 := Option.some.inj e1
    obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
    obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb')
    obtain rfl : st = st' := Option.some.inj (hst.symm.trans hst')
    obtain ⟨hlv, -, hg2⟩ := F.st st hst
    obtain ⟨st0, h0, hk⟩ := F.keeps
    obtain rfl : st0 = st1 := Option.some.inj (h0.symm.trans hst1)
    have K := hk st hst
    obtain ⟨x1, x2, x3, x4, x5⟩ := hs st hst
    refine ⟨⟨x1, fun e0 => ?_, fun e1 e2 => ?_, hg2.1, fun e8 => absurd hg2.2 (Int32.not_lt.mpr e8)⟩, K,
      fun hf _ => x3 hf, x4, x5, fun L => hL st0 h0 L st hst⟩
    · rw [e0] at hlv; exact absurd hlv (by decide)
    · exact absurd (K.2.2.2.2.2.1.symm.trans e2) (hn st0 h0 (K.2.2.2.2.1.symm.trans e1))

/-- The entry facts of a strategy other than `deflate_slow` that `slf_post` needs: a strategy other than `Z_FIXED`,
and a state outside the levels of `deflate_slow`. -/
def NotSlow (h : Heap) (b : Nat) : Prop :=
  ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED ∧ ¬ TableAt 7 9 st0

/-- `StratPost` from `SLF` and the exit facts, for a strategy other than `deflate_slow` entered with a strategy
other than `Z_FIXED` (`LazyOk` is kept by `StratKeeps`). -/
theorem slf_post {h H : Heap} {i b : Nat} (F : SLF h i b H) (flush : Int32) (bs : BlockState) (hn : NotSlow h b)
    (hs : ∀ st, H.dstate b = some st → ExitOk flush bs st) : StratPost h (some i) flush bs H := by
  refine slf_postL F flush bs (fun st0 h0 _ => (hn st0 h0).1) (fun st0 h0 L st hst => ?_) hs
  obtain ⟨st1, h1, hk⟩ := F.keeps
  obtain rfl : st0 = st1 := Option.some.inj (h0.symm.trans h1)
  obtain ⟨L', hm⟩ := (hk st hst).lazy L (hn st0 h0).2
  exact ⟨L', fun _ => hm⟩

/-! ## `FLUSH_BLOCK` -/

/-- `FLUSH_BLOCK(s, window, last)` from `SLF` with no pending bytes: `SLF` after, no symbols, `lookahead`,
`strstart` and `window` kept, the input kept; no pending bytes when it does not return, and its return value. -/
theorem slf_flush (T : TreesFacts) {h H : Heap} {i b wo : Nat} (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1)
    (F : SLF h i b H) (hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo)) :
    Sat H (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun r H2 => avIn H2 i = avIn H i ∧ SLF h i b H2 ∧
      (∀ st2, H2.dstate b = some st2 → st2.sym_next = 0 ∧ st2.sym_next < st2.sym_end ∧
        ∃ st, H.dstate b = some st ∧ st2.lookahead = st.lookahead ∧ st2.strstart = st.strstart ∧
          st2.window = st.window) ∧
      (r = none → ∀ st2, H2.dstate b = some st2 → st2.pending = 0) ∧
      (r ≠ none → r = some (if last != 0 then .finish_started else .need_more))) := by
  obtain ⟨z, st, al, hz, hb, hst, hal, c⟩ := F.live
  obtain ⟨hp0, hwin⟩ := hp st hst
  obtain ⟨hlv, -, -, h8⟩ := F.st st hst
  obtain ⟨r, h', e, P, z', st', hz', hst', hr⟩ :=
    flush_block_ok T last hl0 hl1 F.inv F.io F.set hz hb hst hp0 hlv h8 hwin
  refine ⟨r, h', e, ?_⟩
  obtain ⟨z2, st2, L, hz2, hst2, hLo, hav, hze, hadv, hpz, hsym, st1, hK1, hst2e⟩ := P.out
  obtain rfl : z' = z2 := Option.some.inj (hz'.symm.trans hz2)
  obtain rfl : st' = st2 := Option.some.inj (hst'.symm.trans hst2)
  have hzs : z'.state = some b := by rw [hze]; exact hb
  have hss := (strstart_toInt32 c).1
  simp only [dview] at hss
  obtain ⟨-, -, -, hl2, -, -, hse⟩ := c.sizes
  simp only [dview] at hse hl2
  have hk : st'.lookahead = st.lookahead ∧ st'.strstart = st.strstart ∧ st'.window = st.window ∧
      st'.level = st.level ∧ st'.status = st.status ∧ st'.block_start = st.strstart.toInt32 ∧
      st'.sym_end = st.sym_end := by
    rw [hst2e, hK1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := hk
  have hK : StratKeeps st st' := by
    rw [hst2e, hK1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩
  have hsend : st'.sym_next < st'.sym_end := by
    rw [hsym, hk7]; apply UInt32.lt_iff_toNat_lt.mpr; simp; omega
  obtain ⟨z0, z4, ob, oo, k, h0, h4, e0, e4, ek⟩ := F.out
  obtain rfl : z = z4 := Option.some.inj (hz.symm.trans h4)
  have hdo : dOutputRanges h (some i) = [(z0.next_out, z0.avail_out.toNat)] := by simp [dOutputRanges, h0]
  refine ⟨by simp only [avIn, hz', hz]; rw [hze], ⟨P.inv, P.io, P.set, ?_, ⟨z', hz', hzs⟩, F.blk0, ?_, ?_,
    ?_, ?_, ?_⟩,
    fun st3 hst3 => ?_, fun hn st3 hst3 => ?_, fun hn => ?_⟩
  · obtain ⟨⟨-, -, -, -, -, -, ec, ex, -, -⟩, -⟩ := P.frame
    exact ⟨by rw [ec]; exact F.crc.1, by rw [ex]; exact F.crc.2⟩
  · refine dframe_trans F.frame (dframe_wmono P.frame ?_)
    rw [hdo]
    intro c' j hw w hm off he
    rw [List.mem_singleton] at hm; subst hm
    simp only [] at he
    rw [e4] at he
    injection he with he1 he2
    injection he1 with he1
    subst he1; subst he2
    have := hw _ (List.mem_singleton_self _) oo e0
    simp only [] at this
    omega
  · exact ⟨z0, z', ob, oo, k + L, h0, hz', e0, by rw [hadv ob (oo + k) e4]; rw [Nat.add_assoc], by omega⟩
  · obtain ⟨st0, h0', hw⟩ := F.win
    refine ⟨st0, h0', fun st3 hst3 => ?_⟩
    obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    rw [hk3]; exact hw st hst
  · obtain ⟨st0, h0', hw⟩ := F.keeps
    refine ⟨st0, h0', fun st3 hst3 => ?_⟩
    obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    exact StratKeeps.trans (hw st hst) hK
  · intro st3 hst3
    obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    exact ⟨by rw [hk4]; exact hlv, by rw [hk5]; exact (F.st st hst).2.1, fun _ => hsym, P.bits _ hst'⟩
  · obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    exact ⟨hsym, hsend, st, hst, hk1, hk2, hk3⟩
  · obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    rcases hr with ⟨-, hp'⟩ | ⟨-, rfl⟩
    · exact hp'
    · cases hn
  · rcases hr with ⟨rfl, -⟩ | ⟨-, e'⟩
    · exact absurd rfl hn
    · exact e'

theorem FS_self (st : DeflateState) : FS st st.lookahead st.strstart = st := rfl

theorem avIn_SH (H0 : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) :
    avIn (SH H0 i z b st d) i = z.avail_in.toNat := by
  simp [avIn]

/-- `SLI` of a heap whose state already holds the locals. -/
theorem sli_of_slc {h H : Heap} {i b : Nat} {st : DeflateState} (C : SLC h i b H) (hst : H.dstate b = some st) :
    SLI h i b st.lookahead st.strstart H := by
  obtain ⟨z, st1, -, hz, -, hst1, -, -⟩ := C.1.live
  obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans hst)
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  have e := ZlibNgF.Proof.DeflateReset.SH_self hz (dstates_of_dstate hst hd) hd
  exact ⟨H, z, st1, d, e.symm, by rw [FS_self, e]; exact C⟩

/-- The entry of a strategy: `SLI` of the entry heap with the state's `lookahead` / `strstart`. -/
theorem sli_entry {h : Heap} {i b : Nat} {z : ZStream} {flush : Int32} (P : StratPre h (some i) flush)
    (hz : h.streams i = some z) (hb : z.state = some b)
    (hE : ∀ b' st, DStateIs h (some i) b' st → 0 < st.level ∧ st.strategy ≠ Z_FIXED) :
    ∃ st, h.dstate b = some st ∧ SLI h i b st.lookahead st.strstart h := by
  obtain ⟨hv, hcrc, hio, hset, -, -, b1, st1, ⟨i1, z1, e1, hz1, hb1, hst1⟩, hp0, hs1⟩ := P
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  have hD : DStateIs h (some i) b st1 := ⟨i, z, rfl, hz, hb, hst1⟩
  obtain ⟨hlv, hfx⟩ := hE b st1 hD
  obtain ⟨hs1, ⟨hsym, -, -, hg2, hg8⟩, -⟩ := hs1
  have hgap : GapOk st1 := ⟨hg2, Int32.not_le.mp fun e8 => hfx (hg8 e8).2.1⟩
  refine ⟨st1, hst1, sli_of_slc ⟨⟨hv, hio, hset, hcrc, ⟨z, hz, hb⟩, ⟨z, hz, hb⟩, dframe_refl _ _ _ _ _, ?_,
    ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; rfl⟩,
    ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; exact StratKeeps.refl _⟩, fun st h1 => ?_⟩,
    fun st h1 => ?_⟩ hst1⟩
  · have hio0 := hio
    obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, -, hout, hnb, -⟩ := hio0
    obtain rfl : i = i2 := Option.some.inj e2
    obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
    obtain ⟨z3, ⟨i3, e3, hz3⟩, hnn, -⟩ := hset
    obtain rfl : i = i3 := Option.some.inj e3
    obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
    obtain ⟨ob, oo, ad, hno, -, -⟩ := hout.resolve_left hnn
    exact ⟨z, z, ob, oo, 0, hz, hz, hno, hno, rfl⟩
  · obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans h1)
    exact ⟨hlv, hs1, hgap⟩
  · obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans h1)
    exact ⟨hp0, hsym⟩

/-- Write the locals back and `FLUSH_BLOCK(s, window, last)` (`if (bflush) FLUSH_BLOCK(s, 0);` after a tally that
filled the symbol buffer): the loop invariant when it does not return, else its return value and `SLF`. -/
theorem sli_flush (T : TreesFacts) {h H : Heap} {i b wo : Nat} {la ss : UInt32} (last : Int32) (hl0 : 0 ≤ last)
    (hl1 : last ≤ 1) (I : SLW h i b la ss H)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) :
    Sat H (wrD (some b) fun s => { s with lookahead := la, strstart := ss }) (fun _ H1 =>
      Sat H1 (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun r H2 => avIn H2 i = avIn H i ∧
        (r = none → SLI h i b la ss H2) ∧
        (r ≠ none → r = some (if last != 0 then .finish_started else .need_more) ∧ SLF h i b H2 ∧
          ∀ st, H2.dstate b = some st → st.sym_next = 0 ∧ st.sym_next < st.sym_end))) := by
  obtain ⟨H0, z, st, d, rfl, F, hp0⟩ := I
  refine Sat.of_eq (wrD_SH _) ?_
  obtain ⟨st0, hst0, hw⟩ := F.win
  have hwin : (FS st la ss).window = .val (.ref (.heap b) wo) := by
    rw [hw _ (SH_dstate _ _ _ _ _ _)]; exact hw0 st0 hst0
  refine Sat.mono (slf_flush T last hl0 hl1 F fun st1 h1 => ?_) ?_
  · obtain rfl : FS st la ss = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h1)
    exact ⟨hp0, hwin⟩
  rintro r H2 ⟨hav, F2, hs2, hn, hsm⟩
  refine ⟨by rw [hav, avIn_SH, avIn_SH], fun e => ?_, fun e => ⟨hsm e, F2, fun st2 h2 => ⟨(hs2 st2 h2).1, (hs2 st2 h2).2.1⟩⟩⟩
  obtain ⟨z2, st2, -, hz2, -, hst2, -, -⟩ := F2.live
  obtain ⟨-, hsl, st3, hst3, hla, hss, -⟩ := hs2 st2 hst2
  obtain rfl : FS st la ss = st3 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst3)
  have C : SLC h i b H2 := ⟨F2, fun st4 h4 => by
    obtain rfl : st2 = st4 := Option.some.inj (hst2.symm.trans h4)
    exact ⟨hn e st2 hst2, hsl⟩⟩
  have := sli_of_slc C hst2
  rw [hla, hss] at this
  exact this

/-! ## `fill_window` -/

/-- `fill_window` keeps the fields of `StratKeeps`: it writes none of the fields it reads back, does not grow
`prev_length` and keeps `match_available` (`FillPost`). -/
theorem fill_keeps {h h' : Heap} {i b : Nat} {z : ZStream} {st st' : DeflateState} (FI : FillIO h h' i b)
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.dstate b = some st)
    (hst' : h'.dstate b = some st') : StratKeeps st st' := by
  obtain ⟨-, -, -, i6, z6, z7, b6, st6, st7, e6, hz6, -, hb6, hst6, hst7, -, -, -, -, -, -, -, x1, x2, x3, x4, x5,
    -, -, -, x6, x7, -, -, hpl, hma, -⟩ := FI.post
  obtain rfl : i = i6 := Option.some.inj e6
  obtain rfl : z = z6 := Option.some.inj (hz.symm.trans hz6)
  obtain rfl : b = b6 := Option.some.inj (hb.symm.trans hb6)
  obtain rfl : st = st6 := Option.some.inj (hst.symm.trans hst6)
  obtain rfl : st' = st7 := Option.some.inj (hst'.symm.trans hst7)
  exact ⟨x2, x1, x3, x6, x4, x5, x7, fun _ => ⟨hpl, hma⟩⟩

/-- Write the locals back and call `fill_window` (with `lookahead < MIN_LOOKAHEAD`): the loop invariant with the new
`lookahead` / `strstart` of the state, the lookahead plus the input not grown, the input dropped when the lookahead
changed, and the lookahead full or the input empty. -/
theorem sli_fill {h H : Heap} {i b : Nat} {la ss : UInt32} (I : SLI h i b la ss H) (hla : la.toNat < 262) :
    Sat H (wrD (some b) fun s => { s with lookahead := la, strstart := ss }) (fun _ H1 =>
      Sat H1 (ZlibNg.Deflate.fill_window (some b)) (fun _ H2 => ∃ H0 z st d, H2 = SH H0 i z b st d ∧
        SLI h i b st.lookahead st.strstart H2 ∧ z.avail_in.toNat + st.lookahead.toNat ≤ avIn H i + la.toNat ∧
        (st.lookahead ≠ la → z.avail_in.toNat < avIn H i) ∧ (262 ≤ st.lookahead.toNat ∨ z.avail_in = 0))) := by
  obtain ⟨H0, z, st, d, rfl, F, hC⟩ := I
  refine Sat.of_eq (wrD_SH _) ?_
  obtain ⟨z1, st1, al, hz1, hb, hst1, -, -⟩ := F.live
  obtain rfl : z = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain rfl : FS st la ss = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  obtain ⟨H2, e, FI⟩ := fill_io F.inv F.io F.set F.crc (SH_streams _ _ _ _ _ _) hb (SH_dstate _ _ _ _ _ _) hla
  refine ⟨(), H2, e, ?_⟩
  obtain ⟨z5, z', st5, st', d', hz5, hst5, rfl, zr, fws⟩ := FI.shape
  obtain rfl : z = z5 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz5)
  obtain rfl : FS st la ss = st5 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst5)
  obtain ⟨-, -, -, i6, z6, z7, b6, st6, st7, e6, hz6, hz7, hb6, hst6, hst7, -, -, hlt, hsum, -, hgap0, hend, -⟩ :=
    FI.post
  obtain rfl : i = i6 := Option.some.inj e6
  obtain rfl : z = z6 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz6)
  obtain rfl : z' = z7 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz7)
  obtain rfl : b = b6 := Option.some.inj (hb.symm.trans hb6)
  obtain rfl : FS st la ss = st6 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst6)
  obtain rfl : st' = st7 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst7)
  have hzs := ZlibNgF.Proof.FillWindow.ZR.state zr
  obtain ⟨-, ⟨ni, ai, ti, ad, hze⟩, -⟩ := zr
  obtain ⟨fe, ms, pl, ss', bs', ins', sl, la', ih, hw', hste⟩ := fws
  have hk : st'.window = st.window ∧ st'.level = st.level ∧ st'.status = st.status ∧ st'.sym_next = st.sym_next ∧
      st'.sym_end = st.sym_end ∧ st'.pending = st.pending ∧ st'.bi_valid = st.bi_valid := by
    rw [hste]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := hk
  have hK : StratKeeps (FS st la ss) st' := fill_keeps FI (SH_streams _ _ _ _ _ _) hb (SH_dstate _ _ _ _ _ _)
    (SH_dstate _ _ _ _ _ _)
  obtain ⟨hp0, hsl⟩ := hC _ (SH_dstate _ _ _ _ _ _)
  obtain ⟨hlv, hstat, hg⟩ := F.st _ (SH_dstate _ _ _ _ _ _)
  have C : SLC h i b (SH (SH H0 i z b (FS st la ss) d) i z' b st' d') := by
    refine ⟨⟨FI.inv, FI.io, FI.set, FI.crc, ⟨_, SH_streams _ _ _ _ _ _, hzs.trans hb⟩, F.blk0,
      dframe_trans F.frame (dframe_nil _ FI.frame), ?_, ?_, ?_, fun st2 h2 => ?_⟩, fun st2 h2 => ?_⟩
    · obtain ⟨z0, z4, ob, oo, k, h0, h4, e0, e4, ek⟩ := F.out
      obtain rfl : z = z4 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans h4)
      exact ⟨z0, _, ob, oo, k, h0, SH_streams _ _ _ _ _ _, e0, by rw [hze]; exact e4, by rw [hze]; exact ek⟩
    · obtain ⟨st0, h0, hw⟩ := F.win
      refine ⟨st0, h0, fun st2 h2 => ?_⟩
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
      exact hk1.trans (hw (FS st la ss) (SH_dstate _ _ _ _ _ _))
    · obtain ⟨st0, h0, hw⟩ := F.keeps
      refine ⟨st0, h0, fun st2 h2 => ?_⟩
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
      exact StratKeeps.trans (hw (FS st la ss) (SH_dstate _ _ _ _ _ _)) hK
    · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
      refine ⟨by rw [hk2]; exact hlv, by rw [hk3]; exact hstat, fun e0 => ?_, by rw [hk7]; exact hg.2⟩
      rw [hk4]; exact hg.1 (hgap0 e0)
    · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
      rw [hk4, hk5, hk6]; exact ⟨hp0, hsl⟩
  refine ⟨_, _, _, d', rfl, sli_of_slc C (SH_dstate _ _ _ _ _ _), ?_, fun hne => ?_, hend⟩
  · rw [avIn_SH]; simp only [] at hsum ⊢; omega
  · rw [avIn_SH]; exact hlt hne

/-! ## Tallies -/

open ZlibNgF.Proof.Tally (W4 W4_wr dcore_tally_le tally_lit_SH tally_dist_SH symok_lit symok_dist incF) in
/-- The loop invariant after a tally that advances `strstart` by `n` (1..258, at most `lookahead`), from `SLF` with
no pending bytes and `sym_next ≤ sym_end` (at `sym_next == sym_end` this is the continuation match of
`deflate_fast` / `deflate_medium`, after which `FLUSH_BLOCK` follows): `SLW`, and `SLI` when the buffer had room
(`sym_next < sym_end`) and is not full after the tally. -/
theorem sli_tally_core_le {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (F : SLF h i b (SH H0 i z b (FS st la ss) d)) (hp0 : st.pending = 0)
    (hle : st.sym_next ≤ st.sym_end) (n : UInt32) (hn1 : 1 ≤ n.toNat)
    (hn : n.toNat ≤ 258) (hnl : n.toNat ≤ la.toNat) {sbo : Nat} (hsb : st.sym_buf = .val (.ref (.heap b) sbo))
    (v : UInt32) (lt dt : Array Ct) (hlts : lt.size = st.dyn_ltree.size) (hdts : dt.size = st.dyn_dtree.size)
    (hsy : ∀ sbo, sbo + st.sym_next.toNat + 4 ≤ d.size → SymOk d sbo st.sym_next st.dyn_ltree st.dyn_dtree →
      st.sym_next.toNat % 3 = 0 → (st.sym_next + 3).toNat = st.sym_next.toNat + 3 → st.sym_next.toNat / 3 < 32768 →
      SymOk (W4 d (sbo + st.sym_next.toNat) v) sbo (st.sym_next + 3) lt dt) :
    SLW h i b (la - n) (ss + n) (SH H0 i z b { st with
      sym_next := st.sym_next + 3
      dyn_ltree := lt
      dyn_dtree := dt } (W4 d (sbo + st.sym_next.toNat) v)) ∧
    (st.sym_next < st.sym_end → st.sym_next + 3 ≠ st.sym_end → SLI h i b (la - n) (ss + n) (SH H0 i z b { st with
      sym_next := st.sym_next + 3
      dyn_ltree := lt
      dyn_dtree := dt } (W4 d (sbo + st.sym_next.toNat) v))) := by
  obtain ⟨hlv, hstat, hg⟩ := F.st _ (SH_dstate _ _ _ _ _ _)
  obtain ⟨z1, st1, al, hz1, hb, hst1, hal, c⟩ := F.live
  obtain rfl : z = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain rfl : FS st la ss = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  have hroom : ∃ pbo poo, (FS st la ss).pending_buf = .val (.ref (.heap b) pbo) ∧
      (FS st la ss).pending_out = .val (.ref (.heap b) poo) ∧
      poo - pbo + (FS st la ss).pending.toNat + (FS st la ss).bi_valid.toInt.toNat / 8 ≤
        (FS st la ss).lit_bufsize.toNat + 8 := by
    obtain ⟨-, -, -, -, pbo, -, -, -, -, hpb, -⟩ := c.lay
    have hpo := c.pout hp0
    simp only [dview] at hpb hpo
    refine ⟨pbo, pbo, hpb, by rw [hpo, hpb], ?_⟩
    show pbo - pbo + st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ _
    have h8 : st.bi_valid.toInt < (8 : Int32).toInt := Int32.lt_iff_toInt_lt.mp hg.2
    have h0 : (8 : Int32).toInt = 8 := rfl
    have hz8 : st.bi_valid.toInt.toNat / 8 = 0 := by omega
    rw [hp0, hz8]; simp
  have hv : dview (FS { st with
      sym_next := st.sym_next + 3
      dyn_ltree := lt
      dyn_dtree := dt } la ss) = { dview (FS st la ss) with
        sym_next := (FS st la ss).sym_next + 3
        ltree := lt
        dtree := dt } := by
    simp only [dview, hlts, hdts]
  have c1 := dcore_tally_le (H := H0) v c (SH_bytes _ _ _ _ _ _) hsb hv hle hsy hroom hstat
  -- the numbers
  have hlook : ss.toNat + la.toNat ≤ st.window_size.toNat := c.look
  have hbs : st.block_start.toInt ≤ ss.toNat := c.bstart
  have hins : st.insert.toNat ≤ ss.toNat := UInt32.le_iff_toNat_le.mp c.ins
  obtain ⟨-, w2, hws, -, hl2, -, hse⟩ := c.sizes
  have w2' : st.w_size.toNat ≤ 32768 := w2
  have hws' : st.window_size = W_BUF_SIZE st.w_size := hws
  have hl2' : st.lit_bufsize.toNat ≤ 32768 := hl2
  have hse' : st.sym_end.toNat = 3 * (st.lit_bufsize.toNat - 1) := hse
  have hle' : st.sym_next.toNat ≤ st.sym_end.toNat := UInt32.le_iff_toNat_le.mp hle
  have hmod : st.sym_next.toNat % 3 = 0 := c.syms.2
  have h65 : st.window_size.toNat ≤ 65536 := by
    rw [hws', DeflateInit.wbuf_toNat _ (by omega)]; unfold DeflateAlloc.dWS; split <;> omega
  have hssn : (ss + n).toNat = ss.toNat + n.toNat := by rw [UInt32.toNat_add]; omega
  have hlan : (la - n).toNat = la.toNat - n.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hnl)
  have hsn3 : (st.sym_next + 3).toNat = st.sym_next.toNat + 3 := by rw [UInt32.toNat_add]; simp; omega
  have c2 := dcore_set c1 (ss + n) (la - n) st.insert st.block_start
    (show (ss + n).toNat + (la - n).toNat ≤ st.window_size.toNat by omega)
    (show st.block_start.toInt ≤ (ss + n).toNat by omega)
    (UInt32.le_iff_toNat_le.mpr (by omega))
    c.bs_lo
  have F2 : SLF h i b (SH H0 i z b (FS { st with
      sym_next := st.sym_next + 3
      dyn_ltree := lt
      dyn_dtree := dt } (la - n) (ss + n)) (W4 d (sbo + st.sym_next.toNat) v)) := by
    refine slf_SH F (fun al' hal' _ => ?_) rfl rfl rfl rfl ⟨fun e0 => ?_, hg.2⟩ (StratKeeps.refl _)
    · obtain rfl : al = al' := Option.some.inj (hal.symm.trans (by simpa [Heap.dallocsOf, SH] using hal'))
      exact DCore.of_heap (by rw [SH_bytes, SH_bytes]) c2
    · exfalso
      have e1 : ((ss + n).toNat : Int) = st.block_start.toInt := e0
      rw [hssn] at e1; omega
  refine ⟨⟨H0, z, _, _, rfl, F2, hp0⟩, fun hlt hne => ⟨H0, z, _, _, rfl, F2, fun st2 h2 => ?_⟩⟩
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
  refine ⟨hp0, ?_⟩
  show st.sym_next + 3 < st.sym_end
  have hlt' : st.sym_next.toNat < st.sym_end.toNat := UInt32.lt_iff_toNat_lt.mp hlt
  have : (st.sym_next + 3).toNat ≠ st.sym_end.toNat := fun e => hne (UInt32.toNat_inj.mp e)
  apply UInt32.lt_iff_toNat_lt.mpr; omega

open ZlibNgF.Proof.Tally (W4) in
/-- `sli_tally_core_le` from `SLC` (room for one more symbol): `SLW`, and `SLI` when the buffer is not full. -/
theorem sli_tally_core {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (C : SLC h i b (SH H0 i z b (FS st la ss) d)) (n : UInt32) (hn1 : 1 ≤ n.toNat)
    (hn : n.toNat ≤ 258) (hnl : n.toNat ≤ la.toNat) {sbo : Nat} (hsb : st.sym_buf = .val (.ref (.heap b) sbo))
    (v : UInt32) (lt dt : Array Ct) (hlts : lt.size = st.dyn_ltree.size) (hdts : dt.size = st.dyn_dtree.size)
    (hsy : ∀ sbo, sbo + st.sym_next.toNat + 4 ≤ d.size → SymOk d sbo st.sym_next st.dyn_ltree st.dyn_dtree →
      st.sym_next.toNat % 3 = 0 → (st.sym_next + 3).toNat = st.sym_next.toNat + 3 → st.sym_next.toNat / 3 < 32768 →
      SymOk (W4 d (sbo + st.sym_next.toNat) v) sbo (st.sym_next + 3) lt dt) :
    SLW h i b (la - n) (ss + n) (SH H0 i z b { st with
      sym_next := st.sym_next + 3
      dyn_ltree := lt
      dyn_dtree := dt } (W4 d (sbo + st.sym_next.toNat) v)) ∧
    (st.sym_next + 3 ≠ st.sym_end → SLI h i b (la - n) (ss + n) (SH H0 i z b { st with
      sym_next := st.sym_next + 3
      dyn_ltree := lt
      dyn_dtree := dt } (W4 d (sbo + st.sym_next.toNat) v))) := by
  have hc : st.pending = 0 ∧ st.sym_next < st.sym_end := C.2 (FS st la ss) (SH_dstate _ _ _ _ _ _)
  have K := sli_tally_core_le C.1 hc.1 (UInt32.le_of_lt hc.2) n hn1 hn hnl hsb v lt dt hlts hdts hsy
  exact ⟨K.1, K.2 hc.2⟩

open ZlibNgF.Proof.Tally (W4 tally_lit_SH tally_dist_SH symok_lit symok_dist incF) in
/-- The bytes of the symbol buffer for one more tally at `sym_next ≤ sym_end`, and the tree sizes, under `SLF`: the
4-byte store at `sym_buf + sym_next` ends at most at `pending_buf + 4 * lit_bufsize + 9` (`PENDING_BUF_SIZE`). -/
theorem slf_sym {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (hle : st.sym_next ≤ st.sym_end) :
    ∃ sbo, st.sym_buf = .val (.ref (.heap b) sbo) ∧ sbo + st.sym_next.toNat + 4 ≤ d.size ∧
      st.dyn_ltree.size = HEAP_SIZE ∧ st.dyn_dtree.size = 2 * 30 + 1 := by
  obtain ⟨z1, st1, al, hz1, hb, hst1, -, c⟩ := F.live
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  obtain ⟨d1, -, -, -, pbo, hd1, -, -, -, -, -, -, -, h4, hsb, -⟩ := c.lay
  obtain rfl : d = d1 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd1)
  obtain ⟨-, -, -, hl1, -, -, hse⟩ := c.sizes
  have hs1 := UInt32.le_iff_toNat_le.mp hle
  have ht := c.trees
  simp only [dview] at hsb h4 hse hs1 ht hl1
  have h9 : pbo + st.lit_bufsize.toNat + 8 + st.sym_next.toNat + 4 ≤ pbo + 4 * st.lit_bufsize.toNat + 9 := by omega
  exact ⟨_, hsb, Nat.le_trans h9 (by omega), ht.1, ht.2.1⟩

/-- The bytes of the symbol buffer for one more tally, and the tree sizes, under `SLC`. -/
theorem slc_sym {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (C : SLC h i b (SH H0 i z b st d)) :
    ∃ sbo, st.sym_buf = .val (.ref (.heap b) sbo) ∧ sbo + st.sym_next.toNat + 4 ≤ d.size ∧
      st.dyn_ltree.size = HEAP_SIZE ∧ st.dyn_dtree.size = 2 * 30 + 1 :=
  slf_sym C.1 (UInt32.le_of_lt (C.2 st (SH_dstate _ _ _ _ _ _)).2)

/-- The bytes of block `b` change from `H` to `H'` only at or after `sym_buf` (in `[sbo, hi)`, `sbo` the offset of
`sym_buf`), so at or after the end of `head` (`MediumStep.chain_wr` keeps `ChainOk`). -/
def SymWr (b : Nat) (H H' : Heap) : Prop :=
  ∃ sbo hi d d', H.bytes b = some d ∧ H'.bytes b = some d' ∧
    (∀ st, H.dstate b = some st → st.sym_buf = .val (.ref (.heap b) sbo)) ∧
    ZlibNgF.Proof.DeflateBits.WrIn d sbo hi d'

/-- The symbol buffer of `H` has room for one more tally that `zng_tr_flush_block` can take: `sym_next ≤ sym_end`. -/
def SymLe (b : Nat) (H : Heap) : Prop := ∀ st, H.dstate b = some st → st.sym_next ≤ st.sym_end

/-- One tally from below `sym_end` leaves `sym_next + 3 ≤ sym_end` (whole symbols, `sym_end = 3 * (lit_bufsize - 1)`). -/
theorem slf_sym_step {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (hlt : st.sym_next < st.sym_end) : st.sym_next + 3 ≤ st.sym_end := by
  obtain ⟨z1, st1, al, -, -, hst1, -, c⟩ := F.live
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  have hm := c.syms.2
  obtain ⟨-, -, -, -, hl2, -, hse⟩ := c.sizes
  simp only [dview] at hm hse hl2
  have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
  have hsn3 : (st.sym_next + 3).toNat = st.sym_next.toNat + 3 := by rw [UInt32.toNat_add]; simp; omega
  apply UInt32.le_iff_toNat_le.mpr; rw [hsn3]; omega

open ZlibNgF.Proof.Tally (W4 W4_wr tally_lit_SH symok_lit incF) in
/-- `zng_tr_tally_lit(s, c)` (`strstart` advances by 1) from `SLF` with the locals `la` / `ss`, no pending bytes and
`sym_next ≤ sym_end`: `SLW`, the bytes of the block changed only inside `sym_buf` (`SymWr`), the result
`sym_next + 3 == sym_end`, and, when the buffer had room (`sym_next < sym_end`), `SymLe` after and `SLI` when the
result is false. -/
theorem slf_tally_lit {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (F : SLF h i b (SH H0 i z b (FS st la ss) d)) (hp0 : st.pending = 0)
    (hle : st.sym_next ≤ st.sym_end) (hl : 1 ≤ la.toNat) (c : UInt8) :
    Sat (SH H0 i z b st d) (zng_tr_tally_lit (some b) c) (fun r H' => avIn H' i = avIn (SH H0 i z b st d) i ∧
      SLW h i b (la - 1) (ss + 1) H' ∧ SymWr b (SH H0 i z b st d) H' ∧ r = (st.sym_next + 3 == st.sym_end) ∧
      (st.sym_next < st.sym_end → SymLe b H') ∧
      (st.sym_next < st.sym_end → r = false → SLI h i b (la - 1) (ss + 1) H')) := by
  obtain ⟨sbo, hsb, hk, hlt, -⟩ := slf_sym F hle
  refine Sat.mono (tally_lit_SH c hsb hk hlt) ?_
  rintro r H' ⟨rfl, rfl⟩
  have K := sli_tally_core_le F hp0 hle 1 (by decide) (by decide) hl hsb _ (incF st.dyn_ltree c.toNat)
    st.dyn_dtree (by simp [incF]) rfl (fun sbo hk hs hm hn hb => symok_lit hs hm hn hk c hlt hb)
  refine ⟨by rw [avIn_SH, avIn_SH], K.1, ⟨sbo, sbo + st.sym_next.toNat + 4, d, _, SH_bytes _ _ _ _ _ _,
    SH_bytes _ _ _ _ _ _, fun st2 h2 => ?_, (W4_wr _ _ _).widen (by omega) (by omega)⟩, rfl,
    fun hlt' st2 h2 => ?_, fun hlt' e => K.2 hlt' fun hne => by simp [hne] at e⟩
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); exact hsb
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); have e := slf_sym_step F hlt'; exact e

open ZlibNgF.Proof.Tally (W4 W4_wr tally_dist_SH symok_dist incF) in
/-- `zng_tr_tally_dist(s, dist, len)` with `len <= 255` and `1 <= dist <= 32768` (`strstart` advances by `n`,
1..258, at most `lookahead`) from `SLF` with the locals `la` / `ss`, no pending bytes and `sym_next ≤ sym_end`: as
`slf_tally_lit`. -/
theorem slf_tally_dist {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} (F : SLF h i b (SH H0 i z b (FS st la ss) d)) (hp0 : st.pending = 0)
    (hle : st.sym_next ≤ st.sym_end) (dist len n : UInt32) (hlen : len.toNat < 256) (hd1 : 1 ≤ dist.toNat)
    (hd2 : dist.toNat ≤ 32768) (hn1 : 1 ≤ n.toNat) (hn : n.toNat ≤ 258) (hnl : n.toNat ≤ la.toNat) :
    Sat (SH H0 i z b st d) (zng_tr_tally_dist (some b) dist len) (fun r H' =>
      avIn H' i = avIn (SH H0 i z b st d) i ∧
      SLW h i b (la - n) (ss + n) H' ∧ SymWr b (SH H0 i z b st d) H' ∧ r = (st.sym_next + 3 == st.sym_end) ∧
      (st.sym_next < st.sym_end → SymLe b H') ∧
      (st.sym_next < st.sym_end → r = false → SLI h i b (la - n) (ss + n) H')) := by
  obtain ⟨sbo, hsb, hk, hlt, hdt⟩ := slf_sym F hle
  refine Sat.mono (tally_dist_SH dist len hlen hd1 hd2 hsb hk hlt hdt) ?_
  rintro r H' ⟨rfl, rfl⟩
  have K := sli_tally_core_le F hp0 hle n hn1 hn hnl hsb _
    (incF st.dyn_ltree (zng_length_code[len.toNat]!.toNat + 257)) (incF st.dyn_dtree (dCodeOf (dist.toNat - 1)))
    (by simp [incF]) (by simp [incF]) (fun sbo hk hs hm hn hb => symok_dist hs hm hn hk dist len hlen hd1 hd2 hlt hdt hb)
  refine ⟨by rw [avIn_SH, avIn_SH], K.1, ⟨sbo, sbo + st.sym_next.toNat + 4, d, _, SH_bytes _ _ _ _ _ _,
    SH_bytes _ _ _ _ _ _, fun st2 h2 => ?_, (W4_wr _ _ _).widen (by omega) (by omega)⟩, rfl,
    fun hlt' st2 h2 => ?_, fun hlt' e => K.2 hlt' fun hne => by simp [hne] at e⟩
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); exact hsb
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); have e := slf_sym_step F hlt'; exact e

/-- `zng_tr_tally_lit(s, c)` in the loop (`strstart` advances by 1): `SLW`, the bytes changed only inside `sym_buf`
(`SymWr`), `sym_next ≤ sym_end` after (`SymLe`: one more tally, the continuation of `deflate_fast` /
`deflate_medium`, may follow before `FLUSH_BLOCK`), and `SLI` when the buffer is not full. -/
theorem sli_tally_lit_le {h H : Heap} {i b : Nat} {la ss : UInt32} (I : SLI h i b la ss H) (hl : 1 ≤ la.toNat)
    (c : UInt8) :
    Sat H (zng_tr_tally_lit (some b) c) (fun r H' => avIn H' i = avIn H i ∧ SLW h i b (la - 1) (ss + 1) H' ∧
      SymWr b H H' ∧ SymLe b H' ∧ (r = false → SLI h i b (la - 1) (ss + 1) H')) := by
  obtain ⟨H0, z, st, d, rfl, C⟩ := I
  have hc : st.pending = 0 ∧ st.sym_next < st.sym_end := C.2 (FS st la ss) (SH_dstate _ _ _ _ _ _)
  exact Sat.mono (slf_tally_lit C.1 hc.1 (UInt32.le_of_lt hc.2) hl c) fun _ _ q =>
    ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.2.1 hc.2, q.2.2.2.2.2 hc.2⟩

/-- `zng_tr_tally_dist(s, dist, len)` in the loop with `len <= 255` and `1 <= dist <= 32768` (`strstart` advances by
`n`, 1..258, at most `lookahead`): as `sli_tally_lit_le`. -/
theorem sli_tally_dist_le {h H : Heap} {i b : Nat} {la ss : UInt32} (I : SLI h i b la ss H) (dist len n : UInt32)
    (hlen : len.toNat < 256) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) (hn1 : 1 ≤ n.toNat)
    (hn : n.toNat ≤ 258) (hnl : n.toNat ≤ la.toNat) :
    Sat H (zng_tr_tally_dist (some b) dist len) (fun r H' => avIn H' i = avIn H i ∧
      SLW h i b (la - n) (ss + n) H' ∧ SymWr b H H' ∧ SymLe b H' ∧ (r = false → SLI h i b (la - n) (ss + n) H')) := by
  obtain ⟨H0, z, st, d, rfl, C⟩ := I
  have hc : st.pending = 0 ∧ st.sym_next < st.sym_end := C.2 (FS st la ss) (SH_dstate _ _ _ _ _ _)
  exact Sat.mono (slf_tally_dist C.1 hc.1 (UInt32.le_of_lt hc.2) dist len n hlen hd1 hd2 hn1 hn hnl) fun _ _ q =>
    ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.2.1 hc.2, q.2.2.2.2.2 hc.2⟩

/-- `zng_tr_tally_lit(s, c)` in the loop (`strstart` advances by 1). -/
theorem sli_tally_lit {h H : Heap} {i b : Nat} {la ss : UInt32} (I : SLI h i b la ss H) (hl : 1 ≤ la.toNat)
    (c : UInt8) :
    Sat H (zng_tr_tally_lit (some b) c) (fun r H' => avIn H' i = avIn H i ∧ SLW h i b (la - 1) (ss + 1) H' ∧
      (r = false → SLI h i b (la - 1) (ss + 1) H')) :=
  Sat.mono (sli_tally_lit_le I hl c) fun _ _ q => ⟨q.1, q.2.1, q.2.2.2.2⟩

/-- `zng_tr_tally_dist(s, dist, len)` in the loop with `len <= 255` and `1 <= dist <= 32768` (`strstart` advances by
`n`, 1..258, at most `lookahead`). -/
theorem sli_tally_dist {h H : Heap} {i b : Nat} {la ss : UInt32} (I : SLI h i b la ss H) (dist len n : UInt32)
    (hlen : len.toNat < 256) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) (hn1 : 1 ≤ n.toNat)
    (hn : n.toNat ≤ 258) (hnl : n.toNat ≤ la.toNat) :
    Sat H (zng_tr_tally_dist (some b) dist len) (fun r H' => avIn H' i = avIn H i ∧
      SLW h i b (la - n) (ss + n) H' ∧ (r = false → SLI h i b (la - n) (ss + n) H')) :=
  Sat.mono (sli_tally_dist_le I dist len n hlen hd1 hd2 hn1 hn hnl) fun _ _ q => ⟨q.1, q.2.1, q.2.2.2.2⟩

/-- A tally after one that filled the symbol buffer (`SLW` with `sym_next ≤ sym_end`, i.e. `sym_next == sym_end`):
the continuation match of `deflate_fast` (`deflate_fast.c:108`) and `deflate_medium` (`bflush |= tally`) before
their `FLUSH_BLOCK`. `SLW` again (`sym_next = sym_end + 3`, which `DCore.syms` and `zng_tr_flush_block` allow) and the
bytes changed only inside `sym_buf`. -/
theorem slw_tally_lit {h H : Heap} {i b : Nat} {la ss : UInt32} (W : SLW h i b la ss H) (hle : SymLe b H)
    (hl : 1 ≤ la.toNat) (c : UInt8) :
    Sat H (zng_tr_tally_lit (some b) c) (fun _ H' => avIn H' i = avIn H i ∧ SLW h i b (la - 1) (ss + 1) H' ∧
      SymWr b H H') := by
  obtain ⟨H0, z, st, d, rfl, F, hp0⟩ := W
  exact Sat.mono (slf_tally_lit F hp0 (hle st (SH_dstate _ _ _ _ _ _)) hl c) fun _ _ q => ⟨q.1, q.2.1, q.2.2.1⟩

/-- `zng_tr_tally_dist(s, dist, len)` after a tally that filled the symbol buffer: as `slw_tally_lit`. -/
theorem slw_tally_dist {h H : Heap} {i b : Nat} {la ss : UInt32} (W : SLW h i b la ss H) (hle : SymLe b H)
    (dist len n : UInt32) (hlen : len.toNat < 256) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768)
    (hn1 : 1 ≤ n.toNat) (hn : n.toNat ≤ 258) (hnl : n.toNat ≤ la.toNat) :
    Sat H (zng_tr_tally_dist (some b) dist len) (fun _ H' => avIn H' i = avIn H i ∧
      SLW h i b (la - n) (ss + n) H' ∧ SymWr b H H') := by
  obtain ⟨H0, z, st, d, rfl, F, hp0⟩ := W
  exact Sat.mono (slf_tally_dist F hp0 (hle st (SH_dstate _ _ _ _ _ _)) dist len n hlen hd1 hd2 hn1 hn hnl)
    fun _ _ q => ⟨q.1, q.2.1, q.2.2.1⟩

/-! ## The end of the loop -/

/-- `s->lookahead = lookahead; s->strstart = strstart;` after the loop. -/
theorem sli_wb {h H : Heap} {i b : Nat} {la ss : UInt32} (I : SLI h i b la ss H) :
    Sat H (wrD (some b) fun s => { s with lookahead := la, strstart := ss }) (fun _ H1 => SLC h i b H1 ∧
      avIn H1 i = avIn H i ∧ ∃ H0 z st d, H1 = SH H0 i z b st d ∧ st.lookahead = la ∧ st.strstart = ss) := by
  obtain ⟨H0, z, st, d, rfl, C⟩ := I
  exact Sat.of_eq (wrD_SH _) ⟨C, by rw [avIn_SH, avIn_SH], H0, z, FS st la ss, d, rfl, rfl, rfl⟩

/-- `s->insert = v` with `v <= strstart`. -/
theorem slc_insert {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (C : SLC h i b (SH H0 i z b st d)) (v : UInt32) (hv : v ≤ st.strstart) :
    Sat (SH H0 i z b st d) (wrD (some b) fun s => { s with insert := v }) (fun _ H1 => SLC h i b H1 ∧
      H1 = SH H0 i z b { st with insert := v } d) := by
  refine Sat.of_eq (wrD_SH _) ⟨⟨slf_SH C.1 (fun al _ c => DCore.of_heap (by rw [SH_bytes, SH_bytes])
    (dcore_set c st.strstart st.lookahead v st.block_start c.look c.bstart hv c.bs_lo)) rfl rfl rfl rfl
    (C.1.st st (SH_dstate _ _ _ _ _ _)).2.2 (StratKeeps.refl _), fun st2 h2 => ?_⟩, rfl⟩
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
  exact C.2 st (SH_dstate _ _ _ _ _ _)

/-- `avail_in` is below `2^32`. -/
theorem avIn_lt (H : Heap) (i : Nat) : avIn H i < 2 ^ 32 := by
  unfold avIn; split
  · exact UInt32.toNat_lt _
  · decide

/-- The common tail of `deflate_huff` and `deflate_rle` after `s->insert = 0` (`deflate_huff.c:49-56`):
`FLUSH_BLOCK(s, 1)` and `finish_done` for `Z_FINISH`, else `FLUSH_BLOCK(s, 0)` when symbols wait, and
`block_done`. -/
def strat_tail (st : StatePtr) (window : BPtr) (flush : Int32) : M BlockState := do
  if flush == Z_FINISH then
    if let some r ← FLUSH_BLOCK st window 1 then return r
    return .finish_done
  if (← rdD st (·.sym_next)) != 0 then
    if let some r ← FLUSH_BLOCK st window 0 then return r
  return .block_done

/-- `strat_tail` from `SLC` with an empty lookahead, for a strategy entered with a strategy other than `Z_FIXED`. -/
theorem slc_tail (T : TreesFacts) {h H : Heap} {i b wo : Nat} (flush : Int32) (C : SLC h i b H)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : NotSlow h b)
    (hla : ∀ st, H.dstate b = some st → st.lookahead = 0) :
    Sat H (strat_tail (some b) (.ref (.heap b) wo) flush) (fun r H' => StratPost h (some i) flush r H') := by
  have hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo) := by
    intro st hst
    obtain ⟨st0, h0, hw⟩ := C.1.win
    exact ⟨(C.2 st hst).1, (hw st hst).trans (hw0 st0 h0)⟩
  have fl : ∀ (last : Int32) (bs : BlockState), 0 ≤ last → last ≤ 1 →
      (bs = .block_done ∨ bs = .finish_done) → Sat H (do
        if let some r ← FLUSH_BLOCK (some b) (.ref (.heap b) wo) last then return r
        return bs) (fun r H' => StratPost h (some i) flush r H') := by
    intro last bs hl0 hl1 hbs
    refine Sat.bind (Sat.mono (slf_flush T last hl0 hl1 C.1 hp) ?_)
    rintro r H2 ⟨-, F2, hs2, hn2, hsm⟩
    have hx : ∀ st2, H2.dstate b = some st2 → st2.sym_next = 0 ∧ st2.sym_next < st2.sym_end ∧ st2.lookahead = 0 :=
      fun st2 h2 => by
        obtain ⟨e1, e2, st, hst, e3, -⟩ := hs2 st2 h2
        exact ⟨e1, e2, by rw [e3]; exact hla st hst⟩
    cases r with
    | none =>
      exact Sat.pure (slf_post F2 _ _ hn fun st2 h2 =>
        ⟨(hx st2 h2).2.1, fun _ => hn2 rfl st2 h2, fun _ => (hx st2 h2).1, fun _ => ⟨(hx st2 h2).1, (hx st2 h2).2.2⟩,
          fun _ => (hx st2 h2).1⟩)
    | some v =>
      obtain ⟨rfl⟩ := Option.some.inj (hsm (by simp))
      refine Sat.pure (slf_post F2 _ _ hn fun st2 h2 => ⟨(hx st2 h2).2.1, fun e => ?_, fun _ => (hx st2 h2).1,
        fun _ => ⟨(hx st2 h2).1, (hx st2 h2).2.2⟩, fun _ => (hx st2 h2).1⟩)
      split at e <;> rcases e with e | e <;> cases e
  unfold strat_tail
  by_cases hf : flush == Z_FINISH
  · simp only [hf, ↓reduceIte]
    exact fl 1 .finish_done (by decide) (by decide) (.inr rfl)
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨z, st, -, hz, hb, hst, -, -⟩ := C.1.live
    obtain ⟨i', z', b', st', al, e, L, -, -⟩ := live C.1.inv
    obtain rfl : i = i' := Option.some.inj e
    obtain rfl : z = z' := Option.some.inj (hz.symm.trans L.hz)
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans L.hb)
    obtain rfl : st = st' := Option.some.inj (hst.symm.trans L.dstate)
    refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
    by_cases hs : (st.sym_next != 0) = true
    · simp only [hs, ↓reduceIte]
      exact fl 0 .block_done (by decide) (by decide) (.inl rfl)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      have h0 : st.sym_next = 0 := by simpa using hs
      refine Sat.pure (slf_post C.1 _ _ hn fun st2 h2 => ?_)
      obtain rfl := Option.some.inj (hst.symm.trans h2)
      exact ⟨(C.2 st hst).2, fun _ => (C.2 st hst).1, fun _ => h0, fun e => (by rcases e with e | e <;> cases e),
        fun _ => h0⟩

/-- `SLI` of a heap whose state already holds the locals is `SLC`. -/
theorem sli_slc {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (I : SLI h i b st.lookahead st.strstart (SH H0 i z b st d)) : SLC h i b (SH H0 i z b st d) := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have hs : st1 = st := by
    have := congrArg (fun H => H.dstate b) e
    simp only [SH_dstate] at this
    exact (Option.some.inj this).symm
  subst hs
  rw [FS_self, ← e] at C
  exact C

/-- `StratPost` from `SLC` for `need_more` after a call without a flush. -/
theorem slc_post {h H : Heap} {i b : Nat} (C : SLC h i b H) (hn : NotSlow h b) :
    StratPost h (some i) Z_NO_FLUSH .need_more H := by
  refine slf_post C.1 _ _ hn fun st2 h2 => ⟨(C.2 st2 h2).2, ?_, ?_, ?_, ?_⟩
  · intro e; rcases e with e | e <;> cases e
  · intro e; exact absurd rfl e
  · intro e; rcases e with e | e <;> cases e
  · intro e; cases e

end ZlibNgF.Proof.Strategy
