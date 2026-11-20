import ZlibNgF.Proof.«deflate.c.body.hinit»
import ZlibNgF.Proof.«public-crc32»

/-!
# `deflate`: the gzip header (`ZlibNgF`)

`gzip_ok`: the `GZIP_STATE` part of `deflateHeaders`: the ten fixed bytes (no header registered: then the flush), or
the header record's flags, time, `xfl`, `os`, the extra field's length, the header CRC so far, and `EXTRA_STATE`.
`PB` is the heap of a run of `put_*` stores from a state `st` with only `pending` changed.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateBits (WrIn put_byte_SH put_short_SH put_short_msb_SH put_uint32_SH put_uint32_msb_SH)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## Stores into `pending_buf` -/

/-- The heap after a run of `put_*` from `SH H0 i z b st d0`: only `pending` (now `q`) and the bytes from
`pending_buf` (offset `pbo`) on changed. -/
def PB (H0 : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d0 : Array UInt8) (pbo : Nat) (q : UInt32)
    (H : Heap) : Prop :=
  ∃ d, H = SH H0 i z b { st with pending := q } d ∧ d.size = d0.size ∧ ∀ j, j < pbo → d[j]! = d0[j]!

section PB
variable {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d0 : Array UInt8} {pbo : Nat}

theorem pb_byte (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hr : pbo + 64 ≤ d0.size) {q : UInt32}
    (hq : q.toNat ≤ 60) {H : Heap} (P : PB H0 i z b st d0 pbo q H) (c : UInt8) :
    Sat H (put_byte (some b) c) (fun _ H' => PB H0 i z b st d0 pbo (q + 1) H') := by
  obtain ⟨d, rfl, hs, hl⟩ := P
  exact Sat.mono (put_byte_SH (st := { st with pending := q }) hpb c (by dsimp only; omega))
    fun _ _ ⟨d', e, w⟩ => ⟨d', e, by rw [w.1, hs], fun j hj => by rw [w.2 j (Or.inl (by dsimp only; omega)), hl j hj]⟩

theorem pb_short (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hr : pbo + 64 ≤ d0.size) {q : UInt32}
    (hq : q.toNat ≤ 60) {H : Heap} (P : PB H0 i z b st d0 pbo q H) (w : UInt16) :
    Sat H (put_short (some b) w) (fun _ H' => PB H0 i z b st d0 pbo (q + 2) H') := by
  obtain ⟨d, rfl, hs, hl⟩ := P
  exact Sat.mono (put_short_SH (st := { st with pending := q }) hpb w (by dsimp only; omega))
    fun _ _ ⟨d', e, w⟩ => ⟨d', e, by rw [w.1, hs], fun j hj => by rw [w.2 j (Or.inl (by dsimp only; omega)), hl j hj]⟩

theorem pb_u32 (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hr : pbo + 64 ≤ d0.size) {q : UInt32}
    (hq : q.toNat ≤ 60) {H : Heap} (P : PB H0 i z b st d0 pbo q H) (w : UInt32) :
    Sat H (put_uint32 (some b) w) (fun _ H' => PB H0 i z b st d0 pbo (q + 4) H') := by
  obtain ⟨d, rfl, hs, hl⟩ := P
  exact Sat.mono (put_uint32_SH (st := { st with pending := q }) hpb w (by dsimp only; omega))
    fun _ _ ⟨d', e, w⟩ => ⟨d', e, by rw [w.1, hs], fun j hj => by rw [w.2 j (Or.inl (by dsimp only; omega)), hl j hj]⟩

theorem pb_u32_msb (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (hr : pbo + 64 ≤ d0.size) {q : UInt32}
    (hq : q.toNat ≤ 60) {H : Heap} (P : PB H0 i z b st d0 pbo q H) (w : UInt32) :
    Sat H (put_uint32_msb (some b) w) (fun _ H' => PB H0 i z b st d0 pbo (q + 4) H') := by
  obtain ⟨d, rfl, hs, hl⟩ := P
  exact Sat.mono (put_uint32_msb_SH (st := { st with pending := q }) hpb w (by dsimp only; omega))
    fun _ _ ⟨d', e, w⟩ => ⟨d', e, by rw [w.1, hs], fun j hj => by rw [w.2 j (Or.inl (by dsimp only; omega)), hl j hj]⟩

theorem pb_ld {q : UInt32} {H : Heap} (P : PB H0 i z b st d0 pbo q H) {β : Type} {f : DeflateState → M β}
    {Q : β → Heap → Prop} (k : Sat H (f { st with pending := q }) Q) : Sat H (ldDState (some b) >>= f) Q := by
  obtain ⟨d, rfl, -, -⟩ := P
  exact Sat.bind (Sat.of_eq ldDState_SH k)

theorem pb_rdZ {q : UInt32} {H : Heap} (P : PB H0 i z b st d0 pbo q H) {α β : Type} (g : ZStream → α)
    {f : α → M β} {Q : β → Heap → Prop} (k : Sat H (f (g z)) Q) : Sat H (rdZ (some i) g >>= f) Q := by
  obtain ⟨d, rfl, -, -⟩ := P
  exact Sat.bind (Sat.of_eq (rdZ_SH _) k)

end PB

theorem ldHeader_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {k : Nat}
    {g : GzHeader} (hg : H.gzheaders k = some g) :
    ldHeader (some k) (SH H i z b st d) = .ok (g, SH H i z b st d) := by
  show (match H.gzheaders k with | some g => _ | none => _) = _
  rw [hg]

theorem sat_ival {α β : Type} {H : Heap} {x : Ival α} {a : α} (hx : x = .val a) {f : α → M β}
    {Q : β → Heap → Prop} (k : Sat H (f a) Q) : Sat H (x.get >>= f) Q := by
  rw [hx]; exact k

/-- What a header part leaves when it goes on: the stream is done with the header (`BUSY_STATE`, no pending bytes),
or it is in the header state `s` with no symbols, `pending_out` at `pending_buf`, at most `pending_buf_size` pending
bytes. -/
def HK (s : Int32) (st : DeflateState) : Prop :=
  (st.status = BUSY_STATE ∧ st.pending = 0 ∧ st.sym_next = 0) ∨
    (st.status = s ∧ st.sym_next = 0 ∧ st.pending_out = st.pending_buf ∧ st.pending ≤ st.pending_buf_size)

/-- `HK` with fewer than `pending_buf_size` pending bytes (the extra field's copy needs room for one byte). -/
def HKs (s : Int32) (st : DeflateState) : Prop :=
  (st.status = BUSY_STATE ∧ st.pending = 0 ∧ st.sym_next = 0) ∨
    (st.status = s ∧ st.sym_next = 0 ∧ st.pending_out = st.pending_buf ∧ st.pending < st.pending_buf_size)

/-! ## The gzip header -/

/-- The end of the `GZIP_STATE` part with a header: `gzindex = 0`, `EXTRA_STATE`. -/
def gzEnd (st : StatePtr) : M Bool := do
  wrD st fun s => { s with gzindex := 0 }
  wrD st fun s => { s with status := EXTRA_STATE }
  return false

/-- The header CRC so far (`deflate.c:876-879`), then `gzEnd`. -/
def gzHcrc (st : StatePtr) (strm : StreamPtr) (gh : HeaderPtr) : M Bool := do
  if (← ldHeader gh).hcrc != 0 then
    let s ← ldDState st
    let c ← ZlibNg.Crc32.crc32_small (← rdZ strm (·.adler)).toUInt32 (← s.pending_buf.get) s.pending.toUInt64
    wrZ strm fun z => { z with adler := c.toUInt64 }
  gzEnd st

/-- The `GZIP_STATE` part with a header from the flags on (`deflate.c:861-882`). -/
def gzSome (st : StatePtr) (strm : StreamPtr) (gh : HeaderPtr) : M Bool := do
  let g ← ldHeader gh
  let fl : Int32 := (if g.text != 0 then 1 else 0) + (if g.hcrc != 0 then 2 else 0) +
    (if g.extra == .null then 0 else 4) + (if g.name == .null then 0 else 8) + (if g.comment == .null then 0 else 16)
  put_byte st fl.toUInt32.toUInt8
  put_uint32 st (← ldHeader gh).time.toUInt32
  let s ← ldDState st
  put_byte st (if s.level == 9 then 2 else if s.strategy ≥ Z_HUFFMAN_ONLY || s.level < 2 then 4 else 0)
  put_byte st ((← ldHeader gh).os &&& 0xff).toUInt32.toUInt8
  if (← ldHeader gh).extra != .null then
    put_short st (← ldHeader gh).extra_len.toUInt16
    gzHcrc st strm gh
  else
    gzHcrc st strm gh

/-- The `GZIP_STATE` part with no header (`deflate.c:851-859`). -/
def gzNone (st : StatePtr) (strm : StreamPtr) : M Bool := do
  put_uint32 st 0
  put_byte st 0
  let s ← ldDState st
  put_byte st (if s.level == 9 then 2 else if s.strategy ≥ Z_HUFFMAN_ONLY || s.level < 2 then 4 else 0)
  put_byte st OS_CODE
  wrD st fun s => { s with status := BUSY_STATE }
  ZlibNg.DeflateP.flush_pending strm
  pendingReturn st

theorem gzip_eq (st : StatePtr) (strm : StreamPtr) :
    headersGzip st strm = (do
      wrZ strm fun z => { z with adler := CRC32_INITIAL_VALUE }
      put_byte st 31
      put_byte st 139
      put_byte st 8
      let gh ← (← ldDState st).gzhead.get
      if gh == none then gzNone st strm else gzSome st strm gh) := by
  rfl

/-- The facts at the start of the `GZIP_STATE` part. -/
structure GzPre (h : Heap) (i b : Nat) (z : ZStream) (st : DeflateState) (d : Array UInt8) (H0 : Heap) (pbo : Nat) :
    Prop where
  run : Run h i b (SH H0 i z b st d)
  pb : st.pending_buf = .val (.ref (.heap b) pbo)
  room : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size
  lb : 128 ≤ st.lit_bufsize.toNat
  pbs : st.pending_buf_size.toNat = 4 * st.lit_bufsize.toNat
  sym : st.sym_next = 0
  pout : st.pending_out = st.pending_buf
  wrap : st.wrap = 2

/-- `gzEnd` after the stores: `EXTRA_STATE`. -/
theorem gzEnd_ok {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d0 : Array UInt8} {pbo : Nat}
    (G : GzPre h i b z st d0 H0 pbo) {k : Nat} {g : GzHeader} (hgz : st.gzhead = .val (some k))
    (hg : H0.gzheaders k = some g) (a : UInt64) {q : UInt32} (hq : q.toNat ≤ 60) {H : Heap}
    (P : PB H0 i { z with adler := a } b st d0 pbo q H) :
    Sat H (gzEnd (some b))
      (fun r H' => HRet h i b (fun st' => HKs EXTRA_STATE st' ∧ st'.last_flush = st.last_flush) r H') := by
  obtain ⟨d, rfl, hs, hl⟩ := P
  unfold gzEnd
  have hlb := G.lb
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have R' := seg_run G.run G.pb G.sym G.pout a q EXTRA_STATE 0 hs hl (by omega) (by decide) (by decide) (by decide)
    ⟨fun _ => G.wrap, fun _ => ⟨k, g, hgz, hg, fun _ _ => Nat.zero_le _,
      fun e => absurd e (by show ¬ (EXTRA_STATE = NAME_STATE); decide),
      fun e => absurd e (by show ¬ (EXTRA_STATE = COMMENT_STATE); decide), fun _ _ => rfl,
      fun e => absurd e (by show ¬ (EXTRA_STATE = NAME_STATE); decide)⟩⟩
  refine Sat.pure ⟨R', nofun, fun _ st' hst' => ?_⟩
  rw [SH_dstate] at hst'; obtain rfl := Option.some.inj hst'
  refine ⟨.inr ⟨rfl, G.sym, G.pout, ?_⟩, rfl⟩
  show q < st.pending_buf_size
  rw [UInt32.lt_iff_toNat_lt, G.pbs]; omega

theorem pb_hdr {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d0 : Array UInt8} {pbo : Nat}
    {q : UInt32} {H : Heap} (P : PB H0 i z b st d0 pbo q H) {k : Nat} {g : GzHeader} (hg : H0.gzheaders k = some g)
    {β : Type} {f : GzHeader → M β} {Q : β → Heap → Prop} (kk : Sat H (f g) Q) : Sat H (ldHeader (some k) >>= f) Q := by
  obtain ⟨d, rfl, -, -⟩ := P
  exact Sat.bind (Sat.of_eq (ldHeader_SH hg) kk)

/-- The registered header of a stream in `Run` is readable. -/
theorem reg_hdr {h H : Heap} {i b : Nat} {st : DeflateState} {k : Nat} (R : Run h i b H) (hst : H.dstate b = some st)
    (hgz : st.gzhead = .val (some k)) : DHeaderOk H k := by
  obtain ⟨z, hz, hb⟩ := R.blk
  obtain ⟨z0, b0, hp, ⟨i0, e0, hz0⟩, hb0, ⟨b1, st1, ⟨⟨z1, ⟨i1, e1, hz1⟩, hb1⟩, hst1⟩, hg1⟩, hhd, -⟩ := R.io
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj (hz.symm.trans hz1)
  obtain rfl := Option.some.inj (hb.symm.trans hb1)
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  rw [hgz] at hg1
  exact hhd k (by injection hg1 with e; exact e.symm)

/-- `gzHcrc` after the stores. -/
theorem gzHcrc_ok {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d0 : Array UInt8} {pbo : Nat}
    (G : GzPre h i b z st d0 H0 pbo) {k : Nat} {g : GzHeader} (hgz : st.gzhead = .val (some k))
    (hg : H0.gzheaders k = some g) (a : UInt64) {q : UInt32} (hq : q.toNat ≤ 60) {H : Heap}
    (P : PB H0 i { z with adler := a } b st d0 pbo q H) :
    Sat H (gzHcrc (some b) (some i) (some k))
      (fun r H' => HRet h i b (fun st' => HKs EXTRA_STATE st' ∧ st'.last_flush = st.last_flush) r H') := by
  have P0 := P
  obtain ⟨d, rfl, hs, hl⟩ := P0
  unfold gzHcrc
  refine Sat.bind (Sat.of_eq (ldHeader_SH hg) ?_)
  by_cases hc : (g.hcrc != 0) = true
  · rw [ite_t hc]
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
    refine sat_ival (a := .ref (.heap b) pbo) G.pb ?_
    have hr := G.room
    obtain ⟨v, ev, -⟩ := ZlibNgF.Proof.Crc32.crc32_small_ok (h := SH H0 i { z with adler := a } b
      { st with pending := q } d) G.run.crc.1 (r := .heap b) (data := d) (SH_bytes _ _ _ _ _ _)
      ({ z with adler := a }.adler.toUInt32) pbo q.toUInt64 (by rw [UInt32.toNat_toUInt64, hs]; omega)
    refine Sat.bind (Sat.of_eq ev ?_)
    refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
    exact gzEnd_ok G hgz hg v.toUInt64 hq ⟨d, rfl, hs, hl⟩
  · rw [ite_f hc]
    exact gzEnd_ok G hgz hg a hq P

/-- `gzSome` after the three fixed bytes. -/
theorem gzSome_ok {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d0 : Array UInt8} {pbo : Nat}
    (G : GzPre h i b z st d0 H0 pbo) {k : Nat} {g : GzHeader} (hgz : st.gzhead = .val (some k))
    (hg : H0.gzheaders k = some g) {H : Heap}
    (P : PB H0 i { z with adler := CRC32_INITIAL_VALUE } b st d0 pbo (0 + 1 + 1 + 1) H) :
    Sat H (gzSome (some b) (some i) (some k))
      (fun r H' => HRet h i b (fun st' => HKs EXTRA_STATE st' ∧ st'.last_flush = st.last_flush) r H') := by
  have hr : pbo + 64 ≤ d0.size := by have := G.room; omega
  unfold gzSome
  refine pb_hdr P hg ?_
  refine Sat.bind (Sat.mono (pb_byte G.pb hr (by decide) P _) ?_)
  rintro _ H1 P1
  refine pb_hdr P1 hg ?_
  refine Sat.bind (Sat.mono (pb_u32 G.pb hr (by decide) P1 _) ?_)
  rintro _ H2 P2
  refine pb_ld P2 ?_
  refine Sat.bind (Sat.mono (pb_byte G.pb hr (by decide) P2 _) ?_)
  rintro _ H3 P3
  refine pb_hdr P3 hg ?_
  refine Sat.bind (Sat.mono (pb_byte G.pb hr (by decide) P3 _) ?_)
  rintro _ H4 P4
  refine pb_hdr P4 hg ?_
  by_cases he : (g.extra != .null) = true
  · rw [ite_t he]
    refine pb_hdr P4 hg ?_
    refine Sat.bind (Sat.mono (pb_short G.pb hr (by decide) P4 _) ?_)
    rintro _ H5 P5
    exact gzHcrc_ok G hgz hg _ (by decide) P5
  · rw [ite_f he]
    exact gzHcrc_ok G hgz hg _ (by decide) P4

/-- `gzNone` after the three fixed bytes. -/
theorem gzNone_ok {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d0 : Array UInt8} {pbo : Nat}
    (G : GzPre h i b z st d0 H0 pbo) {H : Heap}
    (P : PB H0 i { z with adler := CRC32_INITIAL_VALUE } b st d0 pbo (0 + 1 + 1 + 1) H) :
    Sat H (gzNone (some b) (some i))
      (fun r H' => HRet h i b (fun st' => HKs EXTRA_STATE st' ∧ st'.last_flush = st.last_flush) r H') := by
  have hr : pbo + 64 ≤ d0.size := by have := G.room; omega
  have hlb := G.lb
  unfold gzNone
  refine Sat.bind (Sat.mono (pb_u32 G.pb hr (by decide) P _) ?_)
  rintro _ H1 P1
  refine Sat.bind (Sat.mono (pb_byte G.pb hr (by decide) P1 _) ?_)
  rintro _ H2 P2
  refine pb_ld P2 ?_
  refine Sat.bind (Sat.mono (pb_byte G.pb hr (by decide) P2 _) ?_)
  rintro _ H3 P3
  refine Sat.bind (Sat.mono (pb_byte G.pb hr (by decide) P3 _) ?_)
  rintro _ H4 ⟨d, rfl, hs, hl⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have R' := seg_run G.run G.pb G.sym G.pout CRC32_INITIAL_VALUE (0 + 1 + 1 + 1 + 4 + 1 + 1 + 1) BUSY_STATE
    st.gzindex hs hl (by have : (0 + 1 + 1 + 1 + 4 + 1 + 1 + 1 : UInt32).toNat = 10 := rfl; omega) (by decide)
    (by decide) (by decide) (hdrOk_busy (Or.inl rfl))
  exact Sat.mono (flush_ret R' (SH_dstate _ _ _ _ _ _)) fun r H' q' => q'.mono fun st' ⟨k1, k2⟩ => by
    rw [k2]; exact ⟨.inl ⟨rfl, k1, G.sym⟩, rfl⟩

/-- The `GZIP_STATE` part of `deflateHeaders`. -/
theorem gzip_ok {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = GZIP_STATE) (hp0 : st.pending = 0) :
    Sat H (headersGzip (some b) (some i))
      (HRet h i b fun st' => HKs EXTRA_STATE st' ∧ st'.last_flush = st.last_flush) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  have hw2 : st.wrap = 2 := (R.side st hst).2.2.1.1 (Or.inl hs)
  obtain ⟨gh, hgh⟩ := c.gzhead
  simp only [dview] at hgh
  have hreg : ∀ k, gh = some k → DHeaderOk H k := fun k ek => reg_hdr R hst (by rw [hgh, ek])
  rw [← e] at R ⊢
  obtain ⟨pbo, hpb, hpd, h0, hpo, l1, -, l3⟩ := hdr_facts c hd hp0 (by rw [hs]; decide) (by rw [hs]; decide)
  have G : GzPre h i b z st d H pbo := ⟨R, hpb, hpd, l1, l3, h0, hpo, hw2⟩
  have e0 : ({ st with pending := 0 } : DeflateState) = st := by rw [← hp0]
  rw [gzip_eq]
  refine Sat.bind (Sat.of_eq (wrZ_SH _) ?_)
  have P0 : PB H i { z with adler := CRC32_INITIAL_VALUE } b st d pbo 0
      (SH H i { z with adler := CRC32_INITIAL_VALUE } b st d) := ⟨d, by rw [e0], rfl, fun _ _ => rfl⟩
  have hr : pbo + 64 ≤ d.size := by omega
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P0 _) ?_)
  rintro _ H1 P1
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P1 _) ?_)
  rintro _ H2 P2
  refine Sat.bind (Sat.mono (pb_byte hpb hr (by decide) P2 _) ?_)
  rintro _ H3 P3
  refine pb_ld P3 ?_
  refine sat_ival (a := gh) hgh ?_
  cases gh with
  | none =>
    rw [ite_t (by decide)]
    exact gzNone_ok G P3
  | some k =>
    rw [ite_f (by simp)]
    obtain ⟨g, hg, -⟩ := hreg k rfl
    have hg' : H.gzheaders k = some g := by rw [← e] at hg; exact hg
    exact gzSome_ok G hgh hg' P3

end ZlibNgF.Proof.DeflateBody
