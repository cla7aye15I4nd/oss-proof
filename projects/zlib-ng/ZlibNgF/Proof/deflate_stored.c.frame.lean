import ZlibNgF.Proof.«deflate_stored.c.io»
import ZlibNgF.Proof.«trees_emit.h.static»

/-!
# The frame of `deflate_stored` (`ZlibNgF`)

`SF h i b H`: the frame of a `deflate_stored` call on stream `i` (block `b`) from its entry heap `h` to the heap `H`:
the invariant, valid and set buffers, the CRC tables, a change of the stream record, the block and the output buffer
only, the output of `H` a tail of the output at entry (`OutTail`), the input a tail of the input at entry (`InTail`),
the fields that `deflate_stored` reads back from its entry state kept (`SK`: the fields of `StratKeeps`, `window`,
`w_size`, `lookahead`), the entry at level 0 with no lookahead, and `block_start` not negative with no symbols.

`sf_next` carries `SF` over one change of the stream record (input to a tail, `L` output bytes written and passed),
the state and the bytes of the block, and `L` bytes of the output block; `sf_post` gives `StratPost`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.StoredF
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateFlush ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.StoredIO
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateInv (upd_upd)
open ZlibNgF.Proof.FlushBlock (dframe_trans dframe_wmono dframe_nil)
open ZlibNgF.Proof.FillIO (streamIO_in)
open ZlibNgF.Proof.WinInv (InTail InTail.trans)

/-- The fields that `deflate_stored` reads back from its entry state: those of `StratKeeps`, `window` and `w_size`
(read once into locals), `lookahead` (never written at level 0), and `pending_buf_size`. -/
def SK (st0 st : DeflateState) : Prop :=
  StratKeeps st0 st ∧ st.window = st0.window ∧ st.w_size = st0.w_size ∧ st.lookahead = st0.lookahead ∧
    st.pending_buf_size = st0.pending_buf_size

theorem SK.trans {a b c : DeflateState} (h1 : SK a b) (h2 : SK b c) : SK a c :=
  ⟨StratKeeps.trans h1.1 h2.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem SK.refl (a : DeflateState) : SK a a := ⟨StratKeeps.refl _, rfl, rfl, rfl, rfl⟩

/-- The frame of a `deflate_stored` call (see the module comment). -/
structure SF (h : Heap) (i b : Nat) (H : Heap) : Prop where
  inv : DInv H (some i)
  io : DStreamIO H (some i)
  set : DBufsSet H (some i)
  crc : CrcGlobals H
  blk : ∃ z, H.streams i = some z ∧ z.state = some b
  blk0 : ∃ z, h.streams i = some z ∧ z.state = some b
  frame : DFrame h H [i] [b] [] (dOutputRanges h (some i))
  out : OutTail h H i
  inp : ∃ z0 z, h.streams i = some z0 ∧ H.streams i = some z ∧ z.avail_in.toNat ≤ z0.avail_in.toNat ∧ InTail z0 z
  keeps : ∃ st0, h.dstate b = some st0 ∧ st0.level = 0 ∧ st0.lookahead = 0 ∧ ∀ st, H.dstate b = some st → SK st0 st
  st : ∀ st, H.dstate b = some st → 0 ≤ st.block_start ∧ st.sym_next = 0 ∧ st.bi_valid < 8

/-- The clauses of `DCore` over a heap whose block `b` holds other bytes of the same size, for a stream record with
the same allocator, with no symbols. -/
theorem dcore_mv {H H' : Heap} {s : StreamPtr} {z z' : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    {d d' : Array UInt8} (c : DCore H s z b v al) (hd : H.bytes b = some d) (hd' : H'.bytes b = some d')
    (hs : d'.size = d.size) (h0 : v.sym_next = 0) (ha : z'.zalloc = z.zalloc) (hf : z'.zfree = z.zfree) :
    DCore H' s z' b v al :=
  { c with
    zalloc := by rw [ha]; exact c.zalloc
    zfree := by rw [hf]; exact c.zfree
    head := by
      obtain ⟨ho, d1, hd1, hh, hho⟩ := c.head
      obtain rfl : d = d1 := Option.some.inj (hd.symm.trans hd1)
      exact ⟨ho, d', hd', hh, by rw [hs]; exact hho⟩
    lay := by
      obtain ⟨d1, wo, po, ho, pbo, hd1, r⟩ := c.lay
      obtain rfl : d = d1 := Option.some.inj (hd.symm.trans hd1)
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := r
      exact ⟨d', wo, po, ho, pbo, hd', a1, a2, a3, a4, a5, a6, a7, by rw [hs]; exact a8, a9⟩
    symv := by
      obtain ⟨d1, sbo, hd1, hsb, hv⟩ := c.symv
      exact ⟨d', sbo, hd', hsb, hv.of_eq fun k hk => by rw [h0] at hk; exact absurd hk (Nat.not_lt_zero _)⟩ }

theorem bytes_SH_setB {H : Heap} {i : Nat} {z : ZStream} {b ob : Nat} {st : DeflateState} {d X : Array UInt8}
    (c : Nat) (hcb : c ≠ b) :
    (SH (setB H ob X) i z b st d).bytes c = if c = ob then some X else H.bytes c := by
  show upd (upd H.bytes ob (some X)) b (some d) c = _
  rw [upd_ne _ _ _ _ hcb]
  by_cases e : c = ob
  · subst e; simp
  · simp only [e, ↓reduceIte]; exact upd_ne _ _ _ _ e

/-- `SF` after one change (see the module comment). -/
theorem sf_next {h H : Heap} {i b ob oo L : Nat} {z z' : ZStream} {st st' : DeflateState}
    {d' X X' : Array UInt8}
    (F : SF h i b H) (hz : H.streams i = some z) (hst : H.dstate b = some st)
    (hno : z.next_out = .ref (.heap ob) oo) (hX : H.bytes ob = some X)
    (hXs : X'.size = X.size) (hXo : ∀ j, (j < oo ∨ oo + L ≤ j) → X'[j]! = X[j]!)
    (hL : L ≤ z.avail_out.toNat)
    (hze : z' = { z with
      next_in := z'.next_in
      avail_in := z'.avail_in
      total_in := z'.total_in
      adler := z'.adler
      next_out := z'.next_out
      avail_out := z'.avail_out
      total_out := z'.total_out })
    (ht : InTail z z') (hai : z'.avail_in.toNat ≤ z.avail_in.toNat)
    (hno' : z'.next_out = .ref (.heap ob) (oo + L)) (hav : z'.avail_out.toNat = z.avail_out.toNat - L)
    (hc : ∀ al, H.dallocsOf b = some al → DCore H (some i) z b (dview st) al →
      DCore (SH (setB H ob X') i z' b st' d') (some i) z' b (dview st') al)
    (hk : SK st st') (hS : 0 ≤ st'.block_start ∧ st'.sym_next = 0 ∧ st'.bi_valid < 8) :
    SF h i b (SH (setB H ob X') i z' b st' d') := by
  obtain ⟨z1, hz1, hb⟩ := F.blk
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain ⟨i', z2, b2, st2, al, e2, hz2, hb2, hst2, hal, c⟩ := F.inv
  obtain rfl : i = i' := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb.symm.trans hb2)
  obtain rfl : st = st2 := Option.some.inj (hst.symm.trans hst2)
  have hio0 := F.io
  obtain ⟨z3, b3, hp, ⟨i3, e3, hz3⟩, hb3, -, -, hin0, -, hnb, hdj⟩ := hio0
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  obtain rfl : b = b3 := Option.some.inj (hb.symm.trans hb3)
  have hob : ob ≠ b := fun e => hnb oo (by rw [hno, e])
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  have hzs : z'.state = z.state := by rw [hze]
  have O : OutOnly H (SH (setB H ob X') i z' b st' d') b ob oo L := by
    refine ⟨rfl, rfl, fun c hcb data hdc => ?_⟩
    rw [bytes_SH_setB c hcb]
    by_cases hco : c = ob
    · subst hco; rw [hX] at hdc; cases hdc
      exact ⟨X', by simp, hXs, fun j hj => hXo j (hj rfl)⟩
    · exact ⟨data, by simp [hco, hdc], rfl, fun _ _ => rfl⟩
  have fr : DFrame H (SH (setB H ob X') i z' b st' d') [i] [b] [] [(.ref (.heap ob) oo, L)] := by
    refine ⟨⟨fun j hj => ?_, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun c _ hc data hdc => ?_,
      fun c _ hc hn => ?_, rfl, rfl, rfl, rfl, Nat.le_refl _⟩, fun c _ hc => ⟨?_, rfl⟩⟩
    · simp only [SH, setB]; exact upd_ne _ _ _ _ (by simpa using hj)
    · obtain ⟨data', h1, h2, h3⟩ := O.2.2 c (by simpa using hc) data hdc
      refine ⟨data', h1, h2, fun j _ hw => h3 j fun e => ?_⟩
      subst e; exact hw _ (List.mem_singleton_self _) oo rfl
    · have hcb : c ≠ b := by simpa using hc
      have hco : c ≠ ob := fun e => by subst e; rw [hX] at hn; cases hn
      rw [bytes_SH_setB c hcb]; simp only [hco, ↓reduceIte]; exact hn
    · simp only [SH, setB]; exact upd_ne _ _ _ _ (by simpa using hc)
  have hal' : (SH (setB H ob X') i z' b st' d').dallocsOf b = some al := by
    have : H.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
    simp [Heap.dallocsOf, setB, SH, this]
  have hrd : NullOrRead (SH (setB H ob X') i z' b st' d') z'.next_in z'.avail_in.toNat := by
    rcases ht with ⟨e1, e2⟩ | ⟨r, os, e1, e2⟩
    · rw [e1, e2]; exact nullOrRead_out O hin0 (hdj _ (.inl rfl)).2
    · rcases hin0 with e | ⟨r', os', src, e, hg, hle⟩
      · rw [e1] at e; cases e
      · rw [e1] at e; injection e with e5 e6; subst e5; subst e6
        have hnb2 : r ≠ .heap b := fun e => (hdj _ (.inl rfl)).2 os (by rw [e1, e])
        obtain ⟨src', h1, h2, -⟩ := get_out O hnb2 hg
        exact .inr ⟨r, _, src', e2, h1, by omega⟩
  obtain ⟨z0, z4, ob4, oo4, k, h0, h4, e0, e4, ek⟩ := F.out
  obtain rfl : z = z4 := Option.some.inj (hz.symm.trans h4)
  rw [hno] at e4
  injection e4 with e5 e6; injection e5 with e5
  subst e5; subst e6
  have hdo : dOutputRanges h (some i) = [(z0.next_out, z0.avail_out.toNat)] := by simp [dOutputRanges, h0]
  refine ⟨⟨i, z', b, st', al, rfl, SH_streams _ _ _ _ _ _, by rw [hzs]; exact hb, SH_dstate _ _ _ _ _ _, hal',
      hc al hal c⟩,
    streamIO_in F.io hz hb hst hno hL O (SH_streams _ _ _ _ _ _) hzs hai ht hrd hno' hav (SH_dstate _ _ _ _ _ _)
      hk.1.2.2.1, ?_, F.crc, ⟨z', SH_streams _ _ _ _ _ _, hzs.trans hb⟩, F.blk0, ?_, ?_, ?_, ?_, fun st2 h2 => ?_⟩
  · obtain ⟨z5, ⟨i5, e5, hz5⟩, hnn, hni⟩ := F.set
    obtain rfl : i = i5 := Option.some.inj e5
    obtain rfl : z = z5 := Option.some.inj (hz.symm.trans hz5)
    refine ⟨z', ⟨i, rfl, SH_streams _ _ _ _ _ _⟩, by rw [hno']; simp, fun ha => ?_⟩
    rcases ht with ⟨e1, e2⟩ | ⟨r, os, e1, e2⟩
    · rw [e1]; exact hni (by rw [← e2]; exact ha)
    · rw [e2]; simp
  · refine dframe_trans F.frame (dframe_wmono fr ?_)
    rw [hdo]
    intro c' j hw w hm off he
    rw [List.mem_singleton] at hm; subst hm
    simp only [] at he
    injection he with he1 he2
    injection he1 with he1
    subst he1; subst he2
    have := hw _ (List.mem_singleton_self _) oo4 e0
    simp only [] at this
    omega
  · exact ⟨z0, z', ob, oo4, k + L, h0, SH_streams _ _ _ _ _ _, e0, by rw [hno', Nat.add_assoc], by omega⟩
  · obtain ⟨z6, z7, h6, h7, l7, t7⟩ := F.inp
    obtain rfl : z = z7 := Option.some.inj (hz.symm.trans h7)
    exact ⟨z6, z', h6, SH_streams _ _ _ _ _ _, by omega, InTail.trans l7 hai t7 ht⟩
  · obtain ⟨st0, h0', l0, la0, hw⟩ := F.keeps
    refine ⟨st0, h0', l0, la0, fun st2 h2 => ?_⟩
    obtain rfl : st' = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    exact SK.trans (hw st hst) hk
  · obtain rfl : st' = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    exact hS

/-- The entry of `deflate_stored`: `SF` of the entry heap, with no pending bytes. -/
theorem sf_entry {h : Heap} {i b : Nat} {z : ZStream} {flush : Int32} (P : StratPre h (some i) flush)
    (hz : h.streams i = some z) (hb : z.state = some b)
    (hE : ∀ b' st, DStateIs h (some i) b' st → st.level = 0) :
    ∃ st, h.dstate b = some st ∧ st.pending = 0 ∧ SF h i b h := by
  obtain ⟨hv, hcrc, hio, hset, -, -, b1, st1, ⟨i1, z1, e1, hz1, hb1, hst1⟩, hp0, -, hs1, -⟩ := P
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  have hlv := hE b st1 ⟨i, z, rfl, hz, hb, hst1⟩
  obtain ⟨-, hl0, -, -, h8c⟩ := hs1
  obtain ⟨hbs, hsn, hla⟩ := hl0 hlv
  refine ⟨st1, hst1, hp0, ⟨hv, hio, hset, hcrc, ⟨z, hz, hb⟩, ⟨z, hz, hb⟩, dframe_refl _ _ _ _ _, ?_,
    ⟨z, z, hz, hz, Nat.le_refl _, Or.inl ⟨rfl, rfl⟩⟩,
    ⟨st1, hst1, hlv, hla, fun st h1 => by rw [hst1] at h1; cases h1; exact SK.refl _⟩, fun st h1 => ?_⟩⟩
  · have hio0 := hio
    obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, -, hout, hnb, -⟩ := hio0
    obtain rfl : i = i2 := Option.some.inj e2
    obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
    obtain ⟨z3, ⟨i3, e3, hz3⟩, hnn, -⟩ := hset
    obtain rfl : i = i3 := Option.some.inj e3
    obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
    obtain ⟨ob, oo, ad, hno, -, -⟩ := hout.resolve_left hnn
    exact ⟨z, z, ob, oo, 0, hz, hz, hno, hno, rfl⟩
  · rw [hst1] at h1; cases h1
    exact ⟨hbs, hsn, Int32.not_le.mp fun e8 => absurd (h8c e8).1 (by rw [hlv]; decide)⟩

/-- `StratPost` from `SF`, with no pending bytes after `block_done` / `finish_done`. -/
theorem sf_post {h H : Heap} {i b : Nat} (F : SF h i b H) (flush : Int32) (bs : BlockState)
    (hB : bs = .need_more ∨ bs = .block_done → CF H i)
    (hF : bs = .finish_started ∨ bs = .finish_done → flush = Z_FINISH)
    (hP : flush = Z_FINISH → bs = .need_more ∨ bs = .finish_started → ∀ z z', StreamAt h (some i) z →
      StreamAt H (some i) z' → z.avail_out ≠ 0 → z'.avail_in < z.avail_in ∨ z'.avail_out < z.avail_out)
    (hp : bs = .block_done ∨ bs = .finish_done → ∀ st, H.dstate b = some st → st.pending = 0) :
    StratPost h (some i) flush bs H := by
  obtain ⟨z, hz, hb⟩ := F.blk
  obtain ⟨i', z', b', st, al, e, hz', hb', hst, -, c⟩ := F.inv
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨z0, hz0, hb0⟩ := F.blk0
  have hsi : stateIds h (some i) = [b] := by simp [stateIds, hz0, hb0]
  refine ⟨F.inv, F.io, F.set, by rw [hsi]; exact F.frame, fun _ e => by obtain rfl := Option.some.inj e; exact F.out,
    stateBlock_keep F.blk0 F.blk, fun _ e => by
      obtain rfl := Option.some.inj e
      obtain ⟨z1, z2, h1, h2, hle, ht⟩ := F.inp
      exact ZlibNgF.Proof.FillFacts.inTail_of_win h1 h2 hle ht, hB, hF, hP,
    fun e => ⟨b, st, ⟨i, z, rfl, hz, hb, hst⟩, hp e st hst⟩,
    ?_⟩
  rintro b1 st1 st' ⟨i1, z1, e1, hz1, hb1, hst1⟩ ⟨i2, z2, e2, hz2, hb2, hst2⟩
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z0 = z1 := Option.some.inj (hz0.symm.trans hz1)
  obtain rfl : b = b1 := Option.some.inj (hb0.symm.trans hb1)
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans hst2)
  obtain ⟨st0, h0, l0, la0, hw⟩ := F.keeps
  obtain rfl : st0 = st1 := Option.some.inj (h0.symm.trans hst1)
  obtain ⟨K, -, -, hla, -⟩ := hw st hst
  obtain ⟨hbs, hsn, h8⟩ := F.st st hst
  have hlv : st.level = 0 := K.2.2.2.2.1.trans l0
  have hla' : st.lookahead = 0 := hla.trans la0
  obtain ⟨-, -, -, hl1, -, -, hse⟩ := c.sizes
  simp only [dview] at hl1 hse
  refine ⟨⟨?_, fun _ => ⟨hbs, hsn, hla'⟩, fun e => absurd (hlv.symm.trans e) (by decide),
    fun _ => hsn, fun e8 => absurd h8 (Int32.not_lt.mpr e8)⟩, K, fun _ _ => hsn, fun _ => ⟨hsn, hla'⟩,
    fun _ => hsn, fun L => ?_⟩
  rotate_left
  · have N := K.lazy L fun ht => by
      have h7 := ht.1; rw [l0] at h7; exact absurd h7 (by decide)
    exact ⟨N.1, fun _ => N.2⟩
  rw [hsn]; apply UInt32.lt_iff_toNat_lt.mpr; simp; omega

/-- What `SF` gives about the current heap `H`: the stream record `z` (output at `ob + oo` with `X` the output block),
the state `st` and the bytes `d` of block `b`, the window at `wo`, `pending_buf` at `pbo`, and the numbers. -/
structure SFX (H : Heap) (i b wo : Nat) (z : ZStream) (st : DeflateState) (d : Array UInt8) (ob oo : Nat)
    (X : Array UInt8) (pbo : Nat) : Prop where
  hz : H.streams i = some z
  hb : z.state = some b
  hst : H.dstate b = some st
  hd : H.bytes b = some d
  hsts : H.dstates b = some st
  hno : z.next_out = .ref (.heap ob) oo
  hX : H.bytes ob = some X
  hoo : oo + z.avail_out.toNat ≤ X.size
  hob : ob ≠ b
  win : st.window = .val (.ref (.heap b) wo)
  hpb : st.pending_buf = .val (.ref (.heap b) pbo)
  lay : wo + st.window_size.toNat ≤ pbo ∧ pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size
  ws : st.window_size.toNat ≤ 65536 ∧ 2 * st.w_size.toNat ≤ st.window_size.toNat ∧ 512 ≤ st.w_size.toNat ∧
    st.w_size.toNat ≤ 32768
  lb : 128 ≤ st.lit_bufsize.toNat ∧ st.lit_bufsize.toNat ≤ 32768 ∧
    st.pending_buf_size.toNat = 4 * st.lit_bufsize.toNat
  strm : st.strm = .val (some i)
  bits : 0 ≤ st.bi_valid.toInt ∧ st.bi_valid.toInt < 8
  bs : 0 ≤ st.block_start.toInt ∧ st.block_start.toInt ≤ st.strstart.toNat ∧
    st.strstart.toNat ≤ st.window_size.toNat
  sym : st.sym_next = 0
  ins : st.insert.toNat ≤ st.strstart.toNat
  pout : st.pending = 0 → st.pending_out = st.pending_buf
  inr : NullOrRead H z.next_in z.avail_in.toNat
  inb : NotInBlock b z.next_in
  dj : Disjoint z.next_out z.avail_out.toNat z.next_in z.avail_in.toNat
  inset : z.avail_in ≠ 0 → z.next_in ≠ .null
  core : ∃ al, H.dallocsOf b = some al ∧ DCore H (some i) z b (dview st) al

theorem SF.facts {h H : Heap} {i b wo : Nat} (F : SF h i b H)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) :
    ∃ z st d ob oo X pbo, SFX H i b wo z st d ob oo X pbo := by
  obtain ⟨z, hz, hb⟩ := F.blk
  obtain ⟨i', z', b', st, al, e, hz', hb', hst, hal, c⟩ := F.inv
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  have hio0 := F.io
  obtain ⟨z3, b3, hp, ⟨i3, e3, hz3⟩, hb3, -, -, hin0, hout, hnb, hdj⟩ := hio0
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  obtain rfl : b = b3 := Option.some.inj (hb.symm.trans hb3)
  obtain ⟨z5, ⟨i5, e5, hz5⟩, hnn, hni⟩ := F.set
  obtain rfl : i = i5 := Option.some.inj e5
  obtain rfl : z = z5 := Option.some.inj (hz.symm.trans hz5)
  obtain ⟨ob, oo, X, hno, hX, hoo⟩ := hout.resolve_left hnn
  have hob : ob ≠ b := fun e => hnb oo (by rw [hno, e])
  obtain ⟨d, wo', po, ho, pbo, hd, hwo, -, -, hpb, h1, h2, h3, h4, -, -⟩ := c.lay
  obtain ⟨st0, h0, -, -, hk⟩ := F.keeps
  have hw : st.window = .val (.ref (.heap b) wo) := ((hk st hst).2.1).trans (hw0 st0 h0)
  simp only [dview] at hwo hpb h1 h2 h3 h4
  rw [hw] at hwo
  obtain rfl : wo = wo' := by injection hwo with e1; injection e1 with e1
  obtain ⟨w1, w2, hws, l1, l2, hpbs, -⟩ := c.sizes
  simp only [dview] at w1 w2 hws l1 l2 hpbs
  have h65 : st.window_size.toNat ≤ 65536 ∧ 2 * st.w_size.toNat ≤ st.window_size.toNat := by
    rw [hws, DeflateInit.wbuf_toNat _ w2]; unfold DeflateAlloc.dWS; split <;> omega
  have hbits := c.bits
  simp only [dview] at hbits
  obtain ⟨hbs, hsn, h8s⟩ := F.st st hst
  have hb0 : (0 : Int32).toInt ≤ st.bi_valid.toInt := Int32.le_iff_toInt_le.mp hbits.1
  have hb8 : st.bi_valid.toInt < (8 : Int32).toInt := Int32.lt_iff_toInt_lt.mp h8s
  have hbs' : (0 : Int32).toInt ≤ st.block_start.toInt := Int32.le_iff_toInt_le.mp hbs
  have hl := c.look
  have hbst := c.bstart
  have hins := c.ins
  simp only [dview] at hl hbst hins
  exact ⟨z, st, d, ob, oo, X, pbo, ⟨hz, hb, hst, hd, dstates_of_dstate hst hd, hno, hX, hoo, hob, hw, hpb,
    ⟨by omega, h4⟩, ⟨h65.1, h65.2, w1, w2⟩, ⟨l1, l2, hpbs⟩, c.strm, ⟨hb0, hb8⟩,
    ⟨hbs', hbst, by omega⟩, hsn, UInt32.le_iff_toNat_le.mp hins, c.pout, hin0, (hdj _ (.inl rfl)).2,
    (hdj _ (.inl rfl)).1, hni, al, hal, c⟩⟩

theorem SFX.b8 {H : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {ob oo : Nat}
    {X : Array UInt8} {pbo : Nat} (S : SFX H i b wo z st d ob oo X pbo) : st.bi_valid < 8 :=
  Int32.lt_iff_toInt_lt.mpr (by rw [show (8 : Int32).toInt = 8 from rfl]; exact S.bits.2)

end ZlibNgF.Proof.StoredF
