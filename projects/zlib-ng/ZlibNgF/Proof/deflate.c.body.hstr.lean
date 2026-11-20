import ZlibNgF.Proof.«deflate.c.body.hextra»

/-!
# `deflate`: the gzip name and comment (`ZlibNgF`)

`string_ok`: the copy loop of `headersString` over the header's name or comment, from the saved index `gzindex`
on: when `pending_buf` is full, the header CRC is updated and the pending output flushed, and the part returns when
output is left pending; each trip stores one byte, the string's zero byte last. The loop measure is
`n + 1 - gzindex` for the string's length `n`. After the zero byte, `gzindex` is past the string, so the stream is
not in `Run` until the caller resets `gzindex` or leaves the state: the loop ends in a header segment (`SegAt`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.DeflateBits (WrIn put_byte_SH)

/-! ## Header segments -/

/-- The start of a header segment: `Run` at `SH H0 i z0 b st0 d0`, no symbols, `pending_out` at `pending_buf`. -/
structure SegS (h : Heap) (i b : Nat) (H0 : Heap) (z0 : ZStream) (st0 : DeflateState) (d0 : Array UInt8) (pbo : Nat) :
    Prop where
  run : Run h i b (SH H0 i z0 b st0 d0)
  pb : st0.pending_buf = .val (.ref (.heap b) pbo)
  sym : st0.sym_next = 0
  pout : st0.pending_out = st0.pending_buf
  room : pbo + 4 * st0.lit_bufsize.toNat + 64 ≤ d0.size
  pbs : st0.pending_buf_size.toNat = 4 * st0.lit_bufsize.toNat
  lb : 128 ≤ st0.lit_bufsize.toNat
  lb2 : st0.lit_bufsize.toNat ≤ 32768

/-- A heap inside a header segment, whose state satisfies `P`. -/
def SegAt (h : Heap) (i b : Nat) (P : DeflateState → Prop) (H : Heap) : Prop :=
  ∃ H0 z0 st0 d0 pbo a p s g d, SegS h i b H0 z0 st0 d0 pbo ∧
    H = SH H0 i { z0 with adler := a } b { st0 with pending := p, status := s, gzindex := g } d ∧
    d.size = d0.size ∧ (∀ j, j < pbo → d[j]! = d0[j]!) ∧ p.toNat ≤ 4 * st0.lit_bufsize.toNat ∧
    P { st0 with pending := p, status := s, gzindex := g }

/-- A stream in `Run` with no symbols and `pending_out` at `pending_buf` starts a segment. -/
theorem segS_of {h H : Heap} {i b : Nat} {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (h0 : st.sym_next = 0) (hpo : st.pending_out = st.pending_buf) :
    ∃ z d pbo, SH H i z b st d = H ∧ SegS h i b H z st d pbo := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  obtain ⟨d0, wo, po, ho, pbo, hd0, -, -, -, hpb, -, -, -, l4, -⟩ := c.lay
  obtain rfl := Option.some.inj (hd.symm.trans hd0)
  obtain ⟨-, -, -, k1, k2, k3, -⟩ := c.sizes
  exact ⟨z, d, pbo, e, ⟨by rw [e]; exact R, hpb, h0, hpo, l4, k3, k1, k2⟩⟩

/-- `Run` after a change of `adler` only. -/
theorem run_adler {h H : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} (R : Run h i b H)
    (e : SH H i z b st d = H) (a : UInt64) : Run h i b (SH H i { z with adler := a } b st d) := by
  obtain ⟨z1, st1, al, d1, hz, hb, hst, hal, hd, e1, c⟩ := R.live
  have hz' : H.streams i = some z := by rw [← e]; exact SH_streams _ _ _ _ _ _
  have hst' : H.dstate b = some st := by rw [← e]; exact SH_dstate _ _ _ _ _ _
  have hd' : H.bytes b = some d := by rw [← e]; exact SH_bytes _ _ _ _ _ _
  obtain rfl := Option.some.inj (hz.symm.trans hz')
  obtain rfl := Option.some.inj (hst.symm.trans hst')
  obtain rfl := Option.some.inj (hd.symm.trans hd')
  refine run_SH R hz hst hal (DCore.of_heap (by simp [hd]) { c with zalloc := c.zalloc, zfree := c.zfree })
    rfl rfl rfl rfl rfl rfl ?_
  obtain ⟨S1, S2, S3, S4, S5, S6⟩ := R.side _ hst'
  exact ⟨S1, S2, S3.move (DeflateSide.hdrMove_out rfl fun r hr => DeflateSetDict.space_SH_ne hr), S4,
    fun d' hd2 => by rw [SH_bytes] at hd2; obtain rfl := Option.some.inj hd2; exact S5 _ hd, S6⟩

/-! ## Reading the string -/

theorem index8_ref {H : Heap} {r : BRef} {o : Nat} {a : Array UInt8} (hg : Space.get H r = some a) {k : Nat}
    (hk : o + k < a.size) : index8 (.ref r o) (k : Int) H = .ok (a[o + k]!, H) := by
  have hc : o ≤ a.size ∧ 0 ≤ (o : Int) + (k : Int) ∧ (o : Int) + (k : Int) ≤ (a.size : Int) := by omega
  have e1 : ((o : Int) + (k : Int)).toNat = o + k := by omega
  simp only [index8, Ptr.index, Ptr.add, Ptr.load, bind_app, hg, hc, and_self, ↓reduceIte, e1, hk, ↓reduceDIte,
    getElem!_pos a (o + k) hk]

/-- The loop body of `headersString`. -/
def strBody (st : StatePtr) (strm : StreamPtr) (str : GzHeader → BPtr) (gh : HeaderPtr) :
    Bool × UInt32 × UInt8 → M (Bool × UInt32 × UInt8) :=
  fun ((_, beg, _) : Bool × UInt32 × UInt8) => do
    let s ← ldDState st
    let (r, beg) ← if s.pending == s.pending_buf_size then do
        HCRC_UPDATE strm st beg
        ZlibNg.DeflateP.flush_pending strm
        if ← pendingReturn st then pure (true, beg) else pure (false, 0)
      else pure (false, beg)
    if r then return (true, beg, 0)
    let s ← ldDState st
    let gi := s.gzindex
    wrD st fun s => { s with gzindex := gi + 1 }
    let v ← index8 (str (← ldHeader gh)) gi.toNat
    put_byte st v
    pure (false, beg, v)

/-- The loop condition of `headersString`. -/
def strCond : Bool × UInt32 × UInt8 → M (Bool × Bool × UInt32 × UInt8) :=
  fun ((r, beg, v) : Bool × UInt32 × UInt8) => pure (!r && v != 0, (r, beg, v))

theorem string_eq (st : StatePtr) (strm : StreamPtr) (str : GzHeader → BPtr) :
    headersString st strm str = (do
      let gh ← (← ldDState st).gzhead.get
      let beg ← rdD st (·.pending)
      let (r, beg, _) ← cdoWhile (strBody st strm str gh) strCond (false, beg, 0)
      if r then return true
      HCRC_UPDATE strm st beg
      return false) := by
  rfl

/-! ## The loop -/

/-- The state facts inside the string's copy (status `S`, pending bytes from `beg` on). -/
def SF (S : Int32) (k : Nat) (beg : UInt32) (st : DeflateState) : Prop :=
  st.status = S ∧ st.sym_next = 0 ∧ st.pending_out = st.pending_buf ∧ st.pending ≤ st.pending_buf_size ∧
    beg ≤ st.pending ∧ st.gzhead = .val (some k) ∧ st.wrap = 2

/-- The loop measure: the output room of stream `i` and the room left in `pending_buf` of block `b`. Every trip stores
one byte into `pending_buf`, and a flush that empties a full `pending_buf` takes `pending_buf_size` bytes of output
room. -/
def oav (i b : Nat) (H : Heap) : Nat :=
  (match H.streams i with
    | some z => z.avail_out.toNat
    | none => 0) +
  (match H.dstate b with
    | some st => st.pending_buf_size.toNat - st.pending.toNat
    | none => 0)

/-- The selector of the string: the name in `NAME_STATE`, the comment in `COMMENT_STATE`. -/
def StrSel (S : Int32) (str : GzHeader → BPtr) : Prop :=
  (S = NAME_STATE ∧ str = GzHeader.name) ∨ (S = COMMENT_STATE ∧ str = GzHeader.comment)

/-- The loop's invariant (string `str g` of length `n`). -/
def SI (h : Heap) (i b k : Nat) (g : GzHeader) (str : GzHeader → BPtr) (S : Int32) (n : Nat)
    (s : Bool × UInt32 × UInt8) (H : Heap) : Prop :=
  s.1 = false ∧ Run h i b H ∧ ∀ st, H.dstate b = some st → SF S k s.2.1 st ∧ CStringLen H (str g) n ∧
    st.gzindex.toNat ≤ n

/-- What the loop leaves. -/
def SQ (h : Heap) (i b k : Nat) (S : Int32) (s : Bool × UInt32 × UInt8) (H : Heap) : Prop :=
  (s.1 = true → Run h i b H ∧ LastM1 H b) ∧ (s.1 = false → SegAt h i b (SF S k s.2.1) H)

/-- The header facts of a state in `NAME_STATE` / `COMMENT_STATE` with `gzindex` within its string. -/
theorem hdrOk_str {X : Heap} {b : Nat} {st : DeflateState} {k : Nat} {g : GzHeader} {str : GzHeader → BPtr}
    {S : Int32} {n : Nat} (hsel : StrSel S str) (hgz : st.gzhead = .val (some k)) (hg : X.gzheaders k = some g)
    (hw : st.wrap = 2) (hs : st.status = S) (hn : str g ≠ .null) (nb : NotInBlock b (str g))
    (c : CStringLen X (str g) n) (hi : st.gzindex.toNat ≤ n) : HdrOk X b st := by
  rcases hsel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨fun _ => hw, fun _ => ⟨k, g, hgz, hg, fun e => absurd (hs.symm.trans e) (by decide),
      fun _ _ => ⟨nb, n, c, hi⟩, fun e => absurd (hs.symm.trans e) (by decide),
      fun e => absurd (hs.symm.trans e) (by decide), fun _ e => absurd e hn⟩⟩
  · exact ⟨fun _ => hw, fun _ => ⟨k, g, hgz, hg, fun e => absurd (hs.symm.trans e) (by decide),
      fun e => absurd (hs.symm.trans e) (by decide), fun _ _ => ⟨nb, n, c, hi⟩,
      fun e => absurd (hs.symm.trans e) (by decide), fun e => absurd (hs.symm.trans e) (by decide)⟩⟩

/-- The store of one byte of the string, and the loop condition after it. -/
theorem strCont_ok {h H1 : Heap} {i b k : Nat} {g : GzHeader} {str : GzHeader → BPtr} {S : Int32} {n : Nat}
    (hsel : StrSel S str) (hg0 : h.gzheaders k = some g) (hn : str g ≠ .null) (nb : NotInBlock b (str g))
    {beg : UInt32} {st1 : DeflateState} (R1 : Run h i b H1) (hst1 : H1.dstate b = some st1) (F : SF S k beg st1)
    (hlt : st1.pending < st1.pending_buf_size) (hc : CStringLen H1 (str g) n) (hgi : st1.gzindex.toNat ≤ n) :
    Sat H1 (do
        let s ← ldDState (some b)
        let gi := s.gzindex
        wrD (some b) fun s => { s with gzindex := gi + 1 }
        let v ← index8 (str (← ldHeader (some k))) gi.toNat
        put_byte (some b) v
        pure (false, beg, v))
      (fun s1 H2 => Sat H2 (strCond s1) (fun cs H3 =>
        (cs.1 = true → SI h i b k g str S n cs.2 H3 ∧ oav i b H3 < oav i b H1) ∧
        (cs.1 = false → SQ h i b k S cs.2 H3))) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := F
  obtain ⟨z, d, pbo, e, SS⟩ := segS_of R1 hst1 f2 f3
  have hg := run_gz R1 hg0
  obtain ⟨r, o, data, hp, hgd, l1, l2, l3⟩ := hc
  have hr : r ≠ .heap b := fun e' => nb o (by rw [hp, e'])
  have hw2 : st1.wrap = 2 := by
    obtain ⟨hw, -⟩ := (R1.side st1 hst1).2.2.1
    refine hw (Or.inr ?_)
    unfold HdrState; rcases hsel with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [f1]
  have hroom := SS.room
  have hpbs := SS.pbs
  have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
  have hlb2 := SS.lb2
  have hgi1 : (st1.gzindex + 1).toNat ≤ st1.gzindex.toNat + 1 := by
    rw [UInt32.toNat_add]; exact Nat.le_trans (Nat.mod_le _ _) (by simp)
  have hp1 : (st1.pending + 1).toNat = st1.pending.toNat + 1 := u32_add _ _ (by simp; omega)
  rw [← e]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (ldHeader_SH hg) ?_)
  rw [hp]
  refine Sat.bind (Sat.of_eq (index8_ref (H := SH H1 i z b { st1 with gzindex := st1.gzindex + 1 } d)
    (by rw [DeflateSetDict.space_SH_ne hr]; exact hgd) (k := st1.gzindex.toNat) (by omega)) ?_)
  refine Sat.bind (Sat.mono (put_byte_SH (st := { st1 with gzindex := st1.gzindex + 1 }) SS.pb _
    (by dsimp only; omega)) ?_)
  rintro _ _ ⟨d', rfl, w⟩
  refine Sat.pure ?_
  unfold strCond
  refine Sat.pure ⟨fun hv => ?_, fun hv => ⟨nofun, fun _ => ?_⟩⟩
  · -- a byte other than zero: the index stays within the string
    have hv' : data[o + st1.gzindex.toNat]! ≠ 0 := by simpa using hv
    have hgn : st1.gzindex.toNat < n := by
      rcases Nat.lt_or_ge st1.gzindex.toNat n with x | x
      · exact x
      · exact absurd (by rw [show st1.gzindex.toNat = n by omega]; exact l2) hv'
    have c' : CStringLen (SH H1 i z b { st1 with gzindex := st1.gzindex + 1, pending := st1.pending + 1 } d')
        (str g) n := by rw [hp]; exact cstr_SH ⟨r, o, data, rfl, hgd, l1, l2, l3⟩ (by rw [← hp]; exact nb)
    have R' := seg_run (d := d') SS.run SS.pb SS.sym SS.pout z.adler (st1.pending + 1) st1.status
      (st1.gzindex + 1) w.1 (fun j hj => w.2 j (Or.inl (by omega))) (by omega)
      (by rw [f1]; rcases hsel with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
      (by rw [f1]; rcases hsel with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
      (by rw [f1]; rcases hsel with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
      (hdrOk_str hsel f6 hg hw2 f1 hn nb c' (by dsimp only; omega))
    refine ⟨⟨rfl, R', fun st' hst' => ?_⟩, ?_⟩
    · rw [SH_dstate] at hst'; obtain rfl := Option.some.inj hst'
      refine ⟨⟨f1, f2, f3, ?_, ?_, f6, f7⟩, c', by show (st1.gzindex + 1).toNat ≤ n; omega⟩
      · exact UInt32.le_iff_toNat_le.mpr (by dsimp only; omega)
      · exact UInt32.le_iff_toNat_le.mpr (by dsimp only; have := UInt32.le_iff_toNat_le.mp f5; omega)
    · simp only [oav, SH_dstate, SH_streams]; rw [hp1]
      exact Nat.add_lt_add_left (Nat.sub_lt_sub_left hlt' (Nat.lt_succ_self _)) _
  · refine ⟨H1, z, st1, d, pbo, z.adler, st1.pending + 1, st1.status, st1.gzindex + 1, d', SS, rfl, w.1,
      fun j hj => w.2 j (Or.inl (by omega)), by omega, f1, f2, f3, ?_, ?_, f6, f7⟩
    · exact UInt32.le_iff_toNat_le.mpr (by dsimp only; omega)
    · exact UInt32.le_iff_toNat_le.mpr (by dsimp only; have := UInt32.le_iff_toNat_le.mp f5; omega)

/-- The string's facts from the header facts of a state in `NAME_STATE` / `COMMENT_STATE`. -/
theorem str_of_hdr {H : Heap} {b : Nat} {st : DeflateState} {k : Nat} {g : GzHeader} {str : GzHeader → BPtr}
    {S : Int32} (hsel : StrSel S str) (HO : HdrOk H b st) (hs : st.status = S) (hgz : st.gzhead = .val (some k))
    (hg : H.gzheaders k = some g) (hn : str g ≠ .null) :
    st.wrap = 2 ∧ NotInBlock b (str g) ∧ ∃ n, CStringLen H (str g) n ∧ st.gzindex.toNat ≤ n := by
  obtain ⟨hw, H2⟩ := HO
  have hS : HdrState st := by
    unfold HdrState; rcases hsel with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [hs]
  obtain ⟨k', g', hgz', hg', -, x2, x3, -, -⟩ := H2 hS
  rw [hgz] at hgz'; obtain rfl : k = k' := by injection hgz' with e1; injection e1
  obtain rfl := Option.some.inj (hg.symm.trans hg')
  refine ⟨hw (Or.inr hS), ?_⟩
  rcases hsel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨nb, n, c, hi⟩ := x2 hs hn; exact ⟨nb, n, c, hi⟩
  · obtain ⟨nb, n, c, hi⟩ := x3 hs hn; exact ⟨nb, n, c, hi⟩

/-- One trip of the loop and its condition. -/
theorem strStep_ok {h : Heap} {i b k : Nat} {g : GzHeader} {str : GzHeader → BPtr} {S : Int32} {n : Nat}
    (hsel : StrSel S str) (hg0 : h.gzheaders k = some g) (hn : str g ≠ .null) (nb : NotInBlock b (str g))
    (s : Bool × UInt32 × UInt8) (H : Heap) (I : SI h i b k g str S n s H) :
    Sat H (strBody (some b) (some i) str (some k) s) (fun s1 H1 => Sat H1 (strCond s1) (fun cs H2 =>
      (cs.1 = true → SI h i b k g str S n cs.2 H2 ∧ oav i b H2 < oav i b H) ∧
      (cs.1 = false → SQ h i b k S cs.2 H2))) := by
  obtain ⟨rr, beg, v⟩ := s
  obtain ⟨rfl, R1, FI⟩ := I
  obtain ⟨z1, st1, al1, d1, hz1, hb1, hst1, hal1, hd1, e1, c1⟩ := R1.live
  obtain ⟨F, hc, hgi⟩ := FI st1 hst1
  have hgH : oav i b H = z1.avail_out.toNat + (st1.pending_buf_size.toNat - st1.pending.toNat) := by
    simp [oav, hst1, hz1]
  rw [hgH]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := F
  have hg := run_gz R1 hg0
  obtain ⟨-, -, -, k1, -, k3, -⟩ := c1.sizes
  obtain ⟨d0, wo, po, ho, pbo, hd0, -, -, -, hpb, -, -, -, l4, -⟩ := c1.lay
  obtain rfl := Option.some.inj (hd1.symm.trans hd0)
  simp only [dview] at k1 k3 hpb l4
  unfold strBody
  dsimp only
  rw [← e1]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  by_cases hf : (st1.pending == st1.pending_buf_size) = true
  · rw [ite_t hf]
    have hpe : st1.pending = st1.pending_buf_size := by simpa using hf
    refine Sat.bind (Sat.mono (hcrc_SH (H := H) (z := z1) (d := d1) f6 hg hpb R1.crc.1
      (by rw [hpe, k3]; omega) beg f5) ?_)
    rintro _ _ ⟨a, rfl⟩
    have R2 := run_adler R1 e1 a
    refine flush_ret_k R2 (SH_dstate _ _ _ _ _ _) fun rr H' q hm hav => ?_
    cases rr with
    | true =>
      rw [ite_t rfl]
      refine Sat.bind (Sat.pure ?_)
      dsimp only
      rw [ite_t rfl]
      refine Sat.pure ?_
      unfold strCond
      exact Sat.pure ⟨nofun, fun _ => ⟨fun _ => q.2.1 rfl |> fun l => ⟨q.1, l⟩, nofun⟩⟩
    | false =>
      rw [ite_f (by simp)]
      refine Sat.bind (Sat.pure ?_)
      dsimp only
      rw [ite_f (by simp)]
      obtain ⟨z', st', al', d', -, -, hst', -, -, -, c'⟩ := q.1.live
      obtain ⟨k1', k2'⟩ := q.2.2 rfl st' hst'
      have hS : HdrState st1 := by
        unfold HdrState; rcases hsel with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [f1]
      obtain ⟨g', hg', -, -, -, -, cm⟩ := hm hS k g f6 hg
      have hgq := run_gz q.1 hg0
      obtain rfl := Option.some.inj (hgq.symm.trans hg')
      have hc' : CStringLen H' (str g) n := by
        have hp : str g = g.name ∨ str g = g.comment := by
          rcases hsel with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact .inl rfl
          · exact .inr rfl
        exact (cm (str g) n hp nb (cstr_SH hc nb)).1
      have hpbs : st'.pending_buf_size.toNat = 4 * st1.lit_bufsize.toNat := by rw [k2']; exact k3
      refine Sat.mono (strCont_ok hsel hg0 hn nb q.1 hst' ⟨by rw [k2']; exact f1, by rw [k2']; exact f2,
        c'.pout k1', by rw [k1']; exact UInt32.le_iff_toNat_le.mpr (by simp),
        by rw [k1']; exact UInt32.le_iff_toNat_le.mpr (by simp), by rw [k2']; exact f6, by rw [k2']; exact f7⟩
        (by rw [k1', UInt32.lt_iff_toNat_lt, hpbs]; simp; omega) hc' (by rw [k2']; exact hgi)) ?_
      intro s1 H1 q1
      refine Sat.mono q1 fun cs H2 ⟨x1, x2⟩ => ⟨fun e => ⟨(x1 e).1, ?_⟩, x2⟩
      have := (x1 e).2
      obtain ⟨zq, hzq⟩ : ∃ zq, H'.streams i = some zq := by obtain ⟨zq, hzq, -⟩ := q.1.blk; exact ⟨zq, hzq⟩
      have hav' := hav _ zq st' (SH_streams _ _ _ _ _ _) hzq hst'
      have hoav : oav i b H' = zq.avail_out.toNat + (st'.pending_buf_size.toNat - st'.pending.toNat) := by
        simp [oav, hst', hzq]
      rw [hoav] at this
      rw [k1'] at hav' this
      rw [hpe] at hav'
      dsimp only at hav'
      have : st'.pending_buf_size = st1.pending_buf_size := by rw [k2']
      simp at hav' this ⊢
      omega
  · rw [ite_f hf]
    have hlt : st1.pending < st1.pending_buf_size := by
      have := UInt32.le_iff_toNat_le.mp f4
      have hne : st1.pending ≠ st1.pending_buf_size := by simpa using hf
      have hne' : st1.pending.toNat ≠ st1.pending_buf_size.toNat := fun x => hne (UInt32.toNat_inj.mp x)
      exact UInt32.lt_iff_toNat_lt.mpr (by omega)
    refine Sat.bind (Sat.pure ?_)
    dsimp only
    rw [ite_f (by simp)]
    rw [e1]
    refine Sat.mono (strCont_ok hsel hg0 hn nb R1 hst1 ⟨f1, f2, f3, f4, f5, f6, f7⟩ hlt hc hgi) ?_
    intro s1 H1 q1
    refine Sat.mono q1 fun cs H2 ⟨x1, x2⟩ => ⟨fun e => ⟨(x1 e).1, ?_⟩, x2⟩
    have := (x1 e).2
    rwa [show oav i b H = z1.avail_out.toNat + (st1.pending_buf_size.toNat - st1.pending.toNat) by
      simp [oav, hst1, hz1]] at this

/-- `headersString` on the name (`NAME_STATE`) or the comment (`COMMENT_STATE`). -/
theorem string_ok {h H : Heap} {i b : Nat} {st : DeflateState} {str : GzHeader → BPtr} {S : Int32}
    (hsel : StrSel S str) (R : Run h i b H) (hst : H.dstate b = some st) (hs : st.status = S)
    (h0 : st.sym_next = 0) (hpo : st.pending_out = st.pending_buf) (hple : st.pending ≤ st.pending_buf_size)
    {k : Nat} {g : GzHeader} (hgz : st.gzhead = .val (some k)) (hg : H.gzheaders k = some g) (hn : str g ≠ .null) :
    Sat H (headersString (some b) (some i) str) (fun r H' => (r = true → Run h i b H' ∧ LastM1 H' b) ∧
      (r = false → SegAt h i b (SF S k 0) H')) := by
  obtain ⟨hw, nb, n, hc, hgi⟩ := str_of_hdr hsel (R.side st hst).2.2.1 hs hgz hg hn
  have hg0 : h.gzheaders k = some g := by
    obtain ⟨⟨-, fg, -⟩, -⟩ := R.frame; rw [← fg k (by simp)]; exact hg
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  rw [string_eq, ← e]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine sat_ival hgz ?_
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  have I0 : SI h i b k g str S n (false, st.pending, 0) (SH H i z b st d) := by
    refine ⟨rfl, by rw [e]; exact R, fun st' hst' => ?_⟩
    rw [SH_dstate] at hst'; obtain rfl := Option.some.inj hst'
    exact ⟨⟨hs, h0, hpo, hple, UInt32.le_refl _, hgz, hw⟩, by rw [e]; exact hc, hgi⟩
  refine Sat.bind (Sat.mono (WinInv.sat_cdoWhileH (SI h i b k g str S n) (fun _ H => oav i b H)
    (SQ h i b k S) (fun s H I => strStep_ok hsel hg0 hn nb s H I) I0 (by
      have := z.avail_out.toNat_lt
      have := st.pending_buf_size.toNat_lt
      have : st.pending_buf_size.toNat - st.pending.toNat ≤ st.pending_buf_size.toNat := Nat.sub_le _ _
      simp only [oav, SH_dstate, SH_streams, fuel]; omega)) ?_)
  rintro ⟨rr, beg, v⟩ H2 Q2
  dsimp only
  cases rr with
  | true =>
    rw [ite_t rfl]
    exact Sat.pure ⟨fun _ => Q2.1 rfl, nofun⟩
  | false =>
    rw [ite_f (by simp)]
    obtain ⟨H0, z0, st0, d0, pbo, a, p, s, g', dd, SS, rfl, hsz, hlo, hp, F⟩ := Q2.2 rfl
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := F
    have hroom := SS.room
    have hg0' : H0.gzheaders k = some g := run_gz SS.run hg0
    have hct : H0.crcTable = ZlibNg.Crc32Tbl.crc_table := SS.run.crc.1
    have hpl : p.toNat ≤ 4 * st0.lit_bufsize.toNat := hp
    refine Sat.bind (Sat.mono (hcrc_SH (H := H0) (i := i) (z := { z0 with adler := a }) (d := dd)
      (st := { st0 with pending := p, status := s, gzindex := g' }) f6 hg0' SS.pb hct
      (by show pbo + p.toNat ≤ dd.size; omega) beg f5) ?_)
    rintro _ _ ⟨a', rfl⟩
    exact Sat.pure ⟨nofun, fun _ => ⟨H0, z0, st0, d0, pbo, a', p, s, g', dd, SS, rfl, hsz, hlo, hp,
      f1, f2, f3, f4, UInt32.le_iff_toNat_le.mpr (by simp), f6, f7⟩⟩

end ZlibNgF.Proof.DeflateBody
