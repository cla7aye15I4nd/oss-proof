import ZlibNgF.Proof.«inflate.c.sync»

/-!
# `inflateCopy` (`ZlibNgF`)

`inflateCopy(dest, source)` on an invariant source and a distinct destination ready for initialisation: the
destination record gets a copy of the source record, `alloc_inflate` gets a fresh block (or fails: `Z_MEM_ERROR`), the
state is copied as a record, `lencode` / `distcode` / `next` are rebased into the copy's `codes` (patch 0001: the test
is `lencode == codes`, and then `distcode` points into `codes` too, by the invariant), the window bytes are copied.
The source keeps its invariant, a successful copy has it, and only the destination record and the fresh block change.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateCopy
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv Core Shape Live view ldState_app ldStream_app setZS upd_upd CodeTarget)
open ZlibNgF.Proof.InflateAlloc (bind_mf bind_fm bind_ff allocHeap allocBytes Fr alloc_ok alloc_fail)
open ZlibNgF.Proof.InflateDict (memcpy_heap copyFold copyFold_size window_nat space_get_heap)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

theorem diff_codes {h : Heap} {b o : Nat} {st : InflateState} (hs : h.istate b = some st)
    (hsz : st.codes.size = ENOUGH) (ho : o ≤ ENOUGH) :
    Ptr.diff (Ptr.ref (CodeRef.codes b) o) (Ptr.ref (CodeRef.codes b) 0) h = .ok (Int64.ofInt (o : Int), h) := by
  have hcodes : Space.get h (CodeRef.codes b) = some st.codes := by
    show Heap.getCodes h (.codes b) = _
    simp [Heap.getCodes, hs]
  have hle : o ≤ st.codes.size := by rw [hsz]; exact ho
  have hE : ENOUGH = 1924 := rfl
  have ho' : (o : Int) < 9223372036854775808 := by rw [hE] at ho; omega
  simp [Ptr.diff, hcodes, hle, ho']

theorem add_codes {h : Heap} {b o : Nat} {st : InflateState} (hs : h.istate b = some st)
    (hsz : st.codes.size = ENOUGH) (ho : o ≤ ENOUGH) :
    Ptr.add (Ptr.ref (CodeRef.codes b) 0) (Int64.ofInt (o : Int)).toInt h = .ok (.ref (.codes b) o, h) := by
  have hcodes : Space.get h (CodeRef.codes b) = some st.codes := by
    show Heap.getCodes h (.codes b) = _
    simp [Heap.getCodes, hs]
  have hE : ENOUGH = 1924 := rfl
  have e : (Int64.ofInt (o : Int)).toInt = o := by
    rw [hE] at ho; exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  rw [e]
  have hle : o ≤ st.codes.size := by rw [hsz]; exact ho
  simp [Ptr.add, hcodes, hle]

/-! ## The heap during the copy -/

/-- `H` is `h` with stream `j` set to `zj` and the fresh block `nb` holding the bytes `bn`, the state `S` and the
allocation record `aN`. -/
structure CF (h H : Heap) (j nb : Nat) (zj : ZStream) (S : InflateState) (bn : Array UInt8) (aN : InflateAllocs) :
    Prop where
  streams : ∀ k, k ≠ j → H.streams k = h.streams k
  hj : H.streams j = some zj
  old : ∀ c, c ≠ nb → H.bytes c = h.bytes c ∧ H.istates c = h.istates c ∧ H.iallocs c = h.iallocs c
  bytes : H.bytes nb = some bn
  ist : H.istates nb = some S
  ial : H.iallocs nb = some aN
  gz : H.gzheaders = h.gzheaders
  consts : H.consts = h.consts
  crc : H.crcTable = h.crcTable
  x2n : H.x2nTable = h.x2nTable
  base : H.baseAddr = h.baseAddr
  next : h.nextBlk ≤ H.nextBlk

theorem CF.istate {h H : Heap} {j nb : Nat} {zj : ZStream} {S : InflateState} {bn : Array UInt8}
    {aN : InflateAllocs} (f : CF h H j nb zj S bn aN) : H.istate nb = some S := by
  simp [Heap.istate, f.bytes, f.ist]

theorem CF.istate_old {h H : Heap} {j nb : Nat} {zj : ZStream} {S : InflateState} {bn : Array UInt8}
    {aN : InflateAllocs} (f : CF h H j nb zj S bn aN) (c : Nat) (hc : c ≠ nb) : H.istate c = h.istate c := by
  simp [Heap.istate, (f.old c hc).1, (f.old c hc).2.1]

theorem CF.wrS {h H : Heap} {j nb : Nat} {zj : ZStream} {S : InflateState} {bn : Array UInt8} {aN : InflateAllocs}
    (f : CF h H j nb zj S bn aN) (g : InflateState → InflateState) :
    Sat H (ZlibNg.Inflate.wrS (some nb) g) (fun _ H' => CF h H' j nb zj (g S) bn aN) := by
  refine ⟨(), { H with istates := upd H.istates nb (some (g S)) }, ?_, ?_⟩
  · simp [ZlibNg.Inflate.wrS, bind_app, ldState_app f.istate, stState, f.istate]
  · exact ⟨f.streams, f.hj, fun c hc => ⟨(f.old c hc).1, by simp only [upd_ne _ _ _ _ hc]; exact (f.old c hc).2.1,
      (f.old c hc).2.2⟩, f.bytes, by simp, f.ial, f.gz, f.consts, f.crc, f.x2n, f.base, f.next⟩

theorem CF.wrZ {h H : Heap} {j nb : Nat} {zj : ZStream} {S : InflateState} {bn : Array UInt8} {aN : InflateAllocs}
    (f : CF h H j nb zj S bn aN) (g : ZStream → ZStream) :
    Sat H (ZlibNg.Inflate.wrZ (some j) g) (fun _ H' => CF h H' j nb (g zj) S bn aN) := by
  refine ⟨(), { H with streams := upd H.streams j (some (g zj)) }, ?_, ?_⟩
  · simp [ZlibNg.Inflate.wrZ, bind_app, ldStream_app f.hj, stStream, f.hj]
  · exact ⟨fun k hk => by simp only [upd_ne _ _ _ _ hk]; exact f.streams k hk, by simp, f.old, f.bytes, f.ist, f.ial,
      f.gz, f.consts, f.crc, f.x2n, f.base, f.next⟩

/-- `memcpy` into the fresh block from another block. -/
theorem CF.memcpy {h H : Heap} {j nb : Nat} {zj : ZStream} {S : InflateState} {bn : Array UInt8}
    {aN : InflateAllocs} (f : CF h H j nb zj S bn aN) {r : BRef} {od os n : Nat} {src : Array UInt8}
    (hs : Space.get H r = some src) (hr : r ≠ .heap nb) (h1 : od + n ≤ bn.size) (h2 : os + n ≤ src.size) :
    Sat H (Ptr.memcpy (Ptr.ref (BRef.heap nb) od) (Ptr.ref r os) n)
      (fun _ H' => CF h H' j nb zj S (copyFold src od os (List.range' 0 n) bn) aN) := by
  refine ⟨(), _, memcpy_heap f.bytes hs hr h1 h2, ?_⟩
  exact ⟨f.streams, f.hj, fun c hc => ⟨by simp only [upd_ne _ _ _ _ hc]; exact (f.old c hc).1, (f.old c hc).2.1,
    (f.old c hc).2.2⟩, by simp, f.ist, f.ial, f.gz, f.consts, f.crc, f.x2n, f.base, f.next⟩

theorem sat_rd {α : Type} {H : Heap} {m : M α} {a : α} (e : m H = .ok (a, H)) :
    Sat H m (fun r H' => a = r ∧ H = H') := Sat.of_eq e ⟨rfl, rfl⟩

theorem CF.copyState {h H : Heap} {j nb b : Nat} {zj : ZStream} {S st : InflateState} {bn : Array UInt8}
    {aN : InflateAllocs} (f : CF h H j nb zj S bn aN) (hb : b ≠ nb) (hst : h.istate b = some st) :
    Sat H (C.copyState (some nb) (some b)) (fun _ H' => CF h H' j nb zj st bn aN) := by
  have hst' : H.istate b = some st := by rw [f.istate_old b hb]; exact hst
  have hne : (some nb == some b) = false := by simp [Ne.symm hb]
  refine ⟨(), { H with istates := upd H.istates nb (some st) }, ?_, ?_⟩
  · simp [C.copyState, bind_app, hne, ldState_app hst', ldState_app f.istate, stState, f.istate]
  · exact ⟨f.streams, f.hj, fun c hc => ⟨(f.old c hc).1, by simp only [upd_ne _ _ _ _ hc]; exact (f.old c hc).2.1,
      (f.old c hc).2.2⟩, f.bytes, by simp, f.ial, f.gz, f.consts, f.crc, f.x2n, f.base, f.next⟩

/-- The invariant of stream `i` reads only its record, its block and the header records. -/
theorem inv_same {h h' : Heap} {i : Nat} (hv : Inv h (some i)) (hs : h'.streams i = h.streams i)
    (hb : ∀ b, StateBlock h (some i) b → h'.bytes b = h.bytes b ∧ h'.istates b = h.istates b ∧
      h'.iallocs b = h.iallocs b) (hg : h'.gzheaders = h.gzheaders) : Inv h' (some i) := by
  obtain ⟨i', z, b, st, al, e, hz, hzb, hst, hal, c⟩ := hv
  obtain rfl := Option.some.inj e
  obtain ⟨e1, e2, e3⟩ := hb b ⟨z, ⟨i, rfl, hz⟩, hzb⟩
  refine ⟨i, z, b, st, al, rfl, by rw [hs]; exact hz, hzb, by simp only [Heap.istate, e1, e2]; exact hst,
    by simp only [Heap.iallocsOf, e1, e3]; exact hal, Core.of_heap e1 hg c⟩

/-- `inflateCopy` up to the allocation: the destination record holds a copy of the source record. -/
theorem copy_pre {h : Heap} {i j : Nat} {z zd : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st)
    (hzd : h.streams j = some zd) (hji : j ≠ i) :
    inflateCopy (some j) (some i) h = (do
        let alloc_bufs ← alloc_inflate (some j)
        if alloc_bufs == none then return Z_MEM_ERROR
        let copy ← (← ldAllocs alloc_bufs).state.get
        copyState copy (some b)
        wrS copy fun s => { s with strm := .val (some j) }
        let s ← ldState (some b)
        let codes ← codesP (some b)
        let ccodes ← codesP copy
        if (← s.lencode.get) == codes then
          wrS copy fun s => { s with lencode := .val ccodes }
          let d ← Ptr.diff (← s.distcode.get) codes
          let dc ← ccodes.add d.toInt
          wrS copy fun s => { s with distcode := .val dc }
        let d ← Ptr.diff (← s.next.get) codes
        let nx ← ccodes.add d.toInt
        wrS copy fun s => { s with next := .val nx }
        let w ← (← ldAllocs alloc_bufs).window.get
        wrS copy fun s => { s with window := .val w }
        wrS copy fun s => { s with alloc_bufs := .val alloc_bufs }
        Ptr.memcpy w (← s.window.get) s.wsize.toNat
        wrZ (some j) fun z => { z with state := copy }
        return Z_OK : M Int32) { h with streams := upd h.streams j (some z) } := by
  have hne : (some j == some i) = false := by simp [hji]
  have hn0 : (some j == (none : StreamPtr)) = false := rfl
  simp only [inflateCopy, bind_app, L.check, L.stateOf, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hne, hn0,
    ldStream_app L.hz, ldStream_app hzd, stStream, hzd]

theorem copy_run {h : Heap} {i j : Nat} {z zd : ZStream} {b : Nat} {st : InflateState} {al : InflateAllocs}
    (L : Live h i z b st) (hal : h.iallocsOf b = some al) (c : Core h (some i) z b (view st) al)
    (hzd : h.streams j = some zd) (hji : j ≠ i)
    (hfr : h.allocOk h.nalloc = true → h.istates h.nextBlk = none ∧ h.iallocs h.nextBlk = none) :
    ∃ r h', inflateCopy (some j) (some i) h = .ok (r, h') ∧ Fr h h' j ∧ Inv h' (some i) ∧
      (r = Z_OK → Inv h' (some j)) := by
  have hne : (some j == some i) = false := by simp [hji]
  have hn0 : (some j == (none : StreamPtr)) = false := rfl
  let H1 : Heap := { h with streams := upd h.streams j (some z) }
  have hza1 : (H1.streams j).map ZStream.zalloc = some .zcalloc := by simp [H1, c.zalloc]
  have e1 := copy_pre L hzd hji
  obtain ⟨woff, data, hwin, hdata, hwsz, hws, hwh, hwn⟩ := window_nat c
  have hsrc : ∀ H', H'.streams i = h.streams i → (H'.bytes b = h.bytes b ∧
      H'.istates b = h.istates b ∧ H'.iallocs b = h.iallocs b) → H'.gzheaders = h.gzheaders → Inv H' (some i) := by
    intro H' e1 e2 e3
    refine inv_same ⟨i, z, b, st, al, rfl, L.hz, L.hb, L.istate, hal, c⟩ e1 (fun b' hb' => ?_) e3
    obtain ⟨z', ⟨i', hi', hz'⟩, hb''⟩ := hb'
    obtain rfl := Option.some.inj hi'
    rw [L.hz] at hz'; obtain rfl := Option.some.inj hz'
    rw [L.hb] at hb''; obtain rfl := Option.some.inj hb''
    exact e2
  rw [e1]
  suffices hS : Sat H1 (do
      let alloc_bufs ← alloc_inflate (some j)
      if alloc_bufs == none then return Z_MEM_ERROR
      let copy ← (← ldAllocs alloc_bufs).state.get
      copyState copy (some b)
      wrS copy fun s => { s with strm := .val (some j) }
      let s ← ldState (some b)
      let codes ← codesP (some b)
      let ccodes ← codesP copy
      if (← s.lencode.get) == codes then
        wrS copy fun s => { s with lencode := .val ccodes }
        let d ← Ptr.diff (← s.distcode.get) codes
        let dc ← ccodes.add d.toInt
        wrS copy fun s => { s with distcode := .val dc }
      let d ← Ptr.diff (← s.next.get) codes
      let nx ← ccodes.add d.toInt
      wrS copy fun s => { s with next := .val nx }
      let w ← (← ldAllocs alloc_bufs).window.get
      wrS copy fun s => { s with window := .val w }
      wrS copy fun s => { s with alloc_bufs := .val alloc_bufs }
      Ptr.memcpy w (← s.window.get) s.wsize.toNat
      wrZ (some j) fun z => { z with state := copy }
      return Z_OK : M Int32) (fun r H' => Fr h H' j ∧ Inv H' (some i) ∧ (r = Z_OK → Inv H' (some j))) by
    obtain ⟨r, h', e, q⟩ := hS; exact ⟨r, h', e, q⟩
  have hok1 : H1.allocOk H1.nalloc = h.allocOk h.nalloc := rfl
  cases hok : h.allocOk h.nalloc
  · refine Sat.bind (Sat.of_eq (alloc_fail hza1 (hok1.trans hok)) ?_)
    simp only [beq_self_eq_true, ↓reduceIte]
    refine Sat.pure ⟨⟨fun k hk => by simp [H1, hk], rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl,
      Nat.le_refl _⟩, hsrc _ (by simp [H1, hji.symm]) ⟨rfl, rfl, rfl⟩ rfl, fun e => ?_⟩
    exact absurd e (by decide)
  obtain ⟨hfs, hfa⟩ := hfr hok
  have hbn : b ≠ h.nextBlk := by
    intro e; have := L.hst; rw [e, hfs] at this; cases this
  have eo := alloc_ok hza1 (show H1.istates H1.nextBlk = none from hfs) (show H1.iallocs H1.nextBlk = none from hfa)
    (hok1.trans hok)
  refine Sat.bind (Sat.of_eq eo ?_)
  have hn1 : (some H1.nextBlk == none) = false := rfl
  simp only [hn1, Bool.false_eq_true, ↓reduceIte]
  have hzf : ((H1.streams j).elim .null ZStream.zfree) = z.zfree := by simp [H1]
  rw [hzf]
  let nb := h.nextBlk
  let p := (PADSZ (h.baseAddr (.heap nb)) 64).toNat
  let aN : InflateAllocs := ⟨.val (.ref (.heap nb) 0), .val z.zfree, .val (some nb), .val (.ref (.heap nb) p)⟩
  have f0 : CF h (allocHeap H1 z.zfree) j nb z (InflateState.garbage (H1.garbage (2 ^ 40 + nb))) (allocBytes H1)
      aN := by
    refine ⟨fun k hk => by simp [H1, hk], by simp [H1], fun c hc => ⟨?_, ?_, ?_⟩,
      InflateAlloc.allocHeap_bytes_self H1 _, by simp [-Nat.reducePow, nb, H1],
      by simp [nb, aN, p, H1], by simp [H1], rfl, rfl, rfl, rfl, by simp [H1]⟩
    · exact InflateAlloc.allocHeap_bytes_ne _ _ c hc
    · simp [hc, H1, nb]
    · simp [hc, H1, nb]
  have eA : ∀ H S bn, CF h H j nb z S bn aN → ldAllocs (some nb) H = .ok (aN, H) := by
    intro H S bn f; simp [ldAllocs, Heap.iallocsOf, f.bytes, f.ial]
  refine Sat.bind (Sat.mono (sat_rd (eA _ _ _ f0)) ?_)
  rintro r H2 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.of_eq rfl ?_)
  refine Sat.bind (Sat.mono (CF.copyState f0 hbn L.istate) ?_)
  rintro - H3 f3
  refine Sat.bind (Sat.mono (CF.wrS f3 (fun s => { s with strm := .val (some j) })) ?_)
  rintro - H4 f4
  have hst4 : H4.istate b = some st := by rw [f4.istate_old b hbn]; exact L.istate
  refine Sat.bind (Sat.mono (sat_rd (ldState_app hst4)) ?_)
  rintro r H5 ⟨rfl, rfl⟩
  refine Sat.bind (Sat.of_eq rfl ?_)
  refine Sat.bind (Sat.of_eq rfl ?_)
  obtain ⟨o, hnx, ho⟩ := c.next
  have hnx' : st.next = .val (.ref (.codes b) o) := hnx
  have hcs : st.codes.size = ENOUGH := c.codes_size
  have hsz1 := InflateAlloc.allocBytes_size H1
  have hp : p + 32832 ≤ (allocBytes H1).size := by rw [hsz1]; exact Nat.le_refl _
  have tail : ∀ (H : Heap) (lc dc : Ival CodePtr),
      CF h H j nb z { st with strm := .val (some j), lencode := lc, distcode := dc } (allocBytes H1) aN →
      ((lc = .val (.ref (.codes nb) 0) ∧ ∃ o, dc = .val (.ref (.codes nb) o) ∧ o ≤ ENOUGH) ∨
        (lc = .val (.ref .lenfix 0) ∧ dc = .val (.ref .distfix 0))) →
      InflateInv.ModeOK nb ⟨st.mode, lc, dc, st.lenbits, st.distbits, st.codes, st.lens, st.ncode, st.nlen, st.ndist,
        st.«have», st.extra, st.offset⟩ →
      Sat H (do
        let d ← Ptr.diff (← st.next.get) (Ptr.ref (CodeRef.codes b) 0)
        let nx ← (Ptr.ref (CodeRef.codes nb) 0).add d.toInt
        wrS (some nb) fun s => { s with next := .val nx }
        let w ← (← ldAllocs (some nb)).window.get
        wrS (some nb) fun s => { s with window := .val w }
        wrS (some nb) fun s => { s with alloc_bufs := .val (some nb) }
        Ptr.memcpy w (← st.window.get) st.wsize.toNat
        wrZ (some j) fun z => { z with state := some nb }
        return Z_OK : M Int32) (fun r H' => Fr h H' j ∧ Inv H' (some i) ∧ (r = Z_OK → Inv H' (some j))) := by
    intro H lc dc f htab hmo
    have hstH : H.istate b = some st := by rw [f.istate_old b hbn]; exact L.istate
    rw [hnx']
    refine Sat.bind (Sat.of_eq rfl ?_)
    refine Sat.bind (Sat.of_eq (diff_codes hstH hcs ho) ?_)
    refine Sat.bind (Sat.of_eq (add_codes f.istate hcs ho) ?_)
    refine Sat.bind (Sat.mono (CF.wrS f (fun s => { s with next := .val (.ref (.codes nb) o) })) ?_)
    rintro - Ha fa
    refine Sat.bind (Sat.mono (sat_rd (eA _ _ _ fa)) ?_)
    rintro r Hb ⟨rfl, rfl⟩
    refine Sat.bind (Sat.of_eq rfl ?_)
    refine Sat.bind (Sat.mono (CF.wrS fa (fun s => { s with window := .val (.ref (.heap nb) p) })) ?_)
    rintro - Hb fb
    refine Sat.bind (Sat.mono (CF.wrS fb (fun s => { s with alloc_bufs := .val (some nb) })) ?_)
    rintro - Hc fc
    rw [hwin]
    refine Sat.bind (Sat.of_eq rfl ?_)
    have hgb : Space.get Hc (BRef.heap b) = some data := by
      rw [space_get_heap, (fc.old b hbn).1]; exact hdata
    refine Sat.bind (Sat.mono (CF.memcpy fc hgb (fun e => hbn (BRef.heap.inj e)) (by omega) (by omega)) ?_)
    rintro - Hd fd
    refine Sat.bind (Sat.mono (CF.wrZ fd (fun z => { z with state := some nb })) ?_)
    rintro - He fe
    refine Sat.pure ⟨?_, ?_, fun _ => ?_⟩
    · exact ⟨fe.streams, fe.gz, fun c' hc' => ⟨(fe.old c' (Nat.ne_of_lt hc')).2.1, (fe.old c' (Nat.ne_of_lt hc')).2.2,
        (fe.old c' (Nat.ne_of_lt hc')).1⟩, fe.consts, fe.crc, fe.x2n, fe.base, fe.next⟩
    · exact hsrc He (by rw [fe.streams i (Ne.symm hji)]) (fe.old b hbn) fe.gz
    · have hwb : (view st).wbufsize = ((1 : UInt32) <<< 15) + 64 := c.wbufsize
      have hwb' : st.wbufsize.toNat = 32832 := by
        have : st.wbufsize = ((1 : UInt32) <<< 15) + 64 := hwb
        rw [this]; rfl
      have hbF := fe.bytes
      refine ⟨j, _, nb, _, aN, rfl, fe.hj, rfl, fe.istate, by simp [Heap.iallocsOf, fe.bytes, fe.ial], ?_⟩
      have hzF : ({ z with state := some nb } : ZStream).zalloc = .zcalloc := c.zalloc
      refine {
        zalloc := c.zalloc
        zfree := c.zfree
        strm := rfl
        alloc_bufs := rfl
        al_state := rfl
        al_zfree := by show Ival.val z.zfree = _; rw [c.zfree]
        al_buf := rfl
        window := ⟨p, _, rfl, rfl, hbF, by rw [copyFold_size]; show p + st.wbufsize.toNat ≤ _; rw [hwb']; exact hp⟩
        wbufsize := c.wbufsize
        mode_lo := c.mode_lo
        mode_hi := c.mode_hi
        codes_size := c.codes_size
        lens_size := c.lens_size
        work_size := c.work_size
        wbits := c.wbits
        reqbits := c.reqbits
        wsize := c.wsize
        whave := c.whave
        wnext := c.wnext
        wnext_le := c.wnext_le
        wnext_eq := c.wnext_eq
        bits := c.bits
        lencode := ?_
        distcode := ?_
        next := ⟨o, rfl, ho⟩
        tables := htab
        head := by rw [fe.gz]; exact c.head
        modes := hmo }
      · rcases htab with ⟨e1, -⟩ | ⟨e1, -⟩
        · exact ⟨_, e1, Or.inl ⟨0, rfl, Nat.zero_le _⟩⟩
        · exact ⟨_, e1, Or.inr (Or.inl rfl)⟩
      · rcases htab with ⟨-, o2, e2, ho2⟩ | ⟨-, e2⟩
        · exact ⟨_, e2, Or.inl ⟨o2, rfl, ho2⟩⟩
        · exact ⟨_, e2, Or.inr (Or.inr rfl)⟩
  rcases c.tables with ⟨hlc, o2, hdc, ho2⟩ | ⟨hlc, hdc⟩
  · have hlc' : st.lencode = .val (.ref (.codes b) 0) := hlc
    have hdc' : st.distcode = .val (.ref (.codes b) o2) := hdc
    rw [hlc']
    refine Sat.bind (Sat.of_eq rfl ?_)
    simp only [beq_self_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.mono (CF.wrS f4 (fun s => { s with lencode := .val (.ref (.codes nb) 0) })) ?_)
    rintro - H5 f5
    have hst5 : H5.istate b = some st := by rw [f5.istate_old b hbn]; exact L.istate
    rw [hdc']
    refine Sat.bind (Sat.of_eq rfl ?_)
    refine Sat.bind (Sat.of_eq (diff_codes hst5 hcs ho2) ?_)
    refine Sat.bind (Sat.of_eq (add_codes f5.istate hcs ho2) ?_)
    refine Sat.bind (Sat.mono (CF.wrS f5 (fun s => { s with distcode := .val (.ref (.codes nb) o2) })) ?_)
    rintro - H6 f6
    exact tail H6 _ _ f6 (Or.inl ⟨rfl, o2, rfl, ho2⟩) (c.modes.rebase hlc' hdc')
  · have hlc' : st.lencode = .val (.ref .lenfix 0) := hlc
    have hdc' : st.distcode = .val (.ref .distfix 0) := hdc
    rw [hlc']
    refine Sat.bind (Sat.of_eq rfl ?_)
    have hneq : (Ptr.ref CodeRef.lenfix 0 == Ptr.ref (CodeRef.codes b) 0) = false := by simp
    simp only [hneq, Bool.false_eq_true, ↓reduceIte]
    exact tail H4 st.lencode st.distcode f4 (Or.inr ⟨hlc', hdc'⟩) (c.modes.fixed hlc' hdc')

/-- On a heap that records a typed object in the block the allocator hands out next, the copy faults. -/
theorem copy_fault {h : Heap} {i j : Nat} {z zd : ZStream} {b : Nat} {st : InflateState} {al : InflateAllocs}
    (L : Live h i z b st) (c : Core h (some i) z b (view st) al) (hzd : h.streams j = some zd) (hji : j ≠ i)
    (hok : h.allocOk h.nalloc = true) (hx : ¬ (h.istates h.nextBlk = none ∧ h.iallocs h.nextBlk = none)) :
    ∃ e, inflateCopy (some j) (some i) h = .error e := by
  have hza1 : (({ h with streams := upd h.streams j (some z) } : Heap).streams j).map ZStream.zalloc =
      some .zcalloc := by simp [c.zalloc]
  have hx' : ({ h with streams := upd h.streams j (some z) } : Heap).istates h.nextBlk ≠ none ∨
      ({ h with streams := upd h.streams j (some z) } : Heap).iallocs h.nextBlk ≠ none := by
    by_cases a : h.istates h.nextBlk = none
    · exact Or.inr fun e => hx ⟨a, e⟩
    · exact Or.inl a
  obtain ⟨e, he⟩ := InflateAlloc.alloc_fault hza1 hok hx'
  exact ⟨e, by rw [copy_pre L hzd hji]; simp only [bind_app, he]⟩

theorem copy_none {h : Heap} {src : StreamPtr} {v : Bool} (hc : inflateStateCheck src h = .ok (v, h)) :
    C.run (inflateCopy none src) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateCopy, bind_app, hc]

theorem copy_noState {h : Heap} {src : StreamPtr} (hn : InflateControl.NoState h src) (dst : StreamPtr) :
    C.run (inflateCopy dst src) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateCopy, bind_app,
    show inflateStateCheck src h = .ok (true, h) from InflateControl.stateCheck_noState hn]

/-- `inflateCopy` on an invariant source and a distinct destination ready for initialisation: when it returns, the
source keeps its invariant and a successful copy has it. -/
theorem copy_inv {h h' : Heap} {src dst : StreamPtr} {r : Int32} (hv : Inv h src) (hdst : InitReady h dst)
    (hne : dst ≠ src) (e : C.run (inflateCopy dst src) h = .ok (r, h')) :
    Inv h' src ∧ (r = Z_OK → Inv h' dst) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  rcases hdst with rfl | ⟨zd, ⟨j, rfl, hzd⟩, -, -⟩
  · rw [copy_none L.check] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    exact ⟨hv, fun e => absurd e (by decide)⟩
  have hji : j ≠ i := fun e => hne (by rw [e])
  by_cases hfr : h.allocOk h.nalloc = true → h.istates h.nextBlk = none ∧ h.iallocs h.nextBlk = none
  · obtain ⟨r', h'', e', -, hi, hj⟩ := copy_run L hal c hzd hji hfr
    have : C.run (inflateCopy (some j) (some i)) h = .ok (r', h'') := e'
    rw [this] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    exact ⟨hi, hj⟩
  · have hok : h.allocOk h.nalloc = true :=
      Classical.byContradiction fun hc => hfr (fun hh => absurd hh hc)
    have hx : ¬ (h.istates h.nextBlk = none ∧ h.iallocs h.nextBlk = none) := fun hh => hfr (fun _ => hh)
    obtain ⟨err, he⟩ := copy_fault L c hzd hji hok hx
    have : C.run (inflateCopy (some j) (some i)) h = .error err := he
    rw [this] at e; cases e

/-- `inflateCopy` on a well-formed heap: no fault, only the destination record and the fresh block change. -/
theorem copy_safe {h : Heap} {src dst : StreamPtr} (hv : Inv h src) (hfr : FreshBlocks h) (hdst : InitReady h dst)
    (hne : dst ≠ src) :
    ∃ r h', C.run (inflateCopy dst src) h = .ok (r, h') ∧ Frame h h' (streamIds dst) [] [] [] := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := InflateInv.live hv
  rcases hdst with rfl | ⟨zd, ⟨j, rfl, hzd⟩, -, -⟩
  · exact ⟨_, _, copy_none L.check, InflateInit.frame_refl h _ _ _ _⟩
  have hji : j ≠ i := fun e => hne (by rw [e])
  obtain ⟨r, h', e, f, -, -⟩ := copy_run L hal c hzd hji (fun _ => ⟨(hfr _ (Nat.le_refl _)).1, (hfr _ (Nat.le_refl _)).2.1⟩)
  exact ⟨r, h', e, f.frame⟩

end ZlibNgF.Proof.InflateCopy
