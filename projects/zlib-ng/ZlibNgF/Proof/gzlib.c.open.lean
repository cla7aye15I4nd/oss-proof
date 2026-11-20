import ZlibNgF.Proof.«gzlib.c.gsat»

/-!
# `gz_open`, `gzopen`, `gzopen64` and `gzdopen` (`ZlibNgF`)

`OI w h b i w1 h1`: the world and heap `w1`, `h1` are well formed and differ from the start `w`, `h` of the call only
in fresh blocks, the fresh `gz_state` of block `b`, the fresh embedded stream `i`, and the file system. Every step of
`gz_open` keeps `OI`; at the end it gives `GzWF` and `GzOpenFrame`, and on success `GzInv`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzOpen
open C ZlibNgF.Spec ZlibNg.Gz ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzInv
open ZlibNgF.Proof.InflateSync (Sat)

/-- The fields of the heap that `gz_open` never changes. -/
structure HSame (h h1 : Heap) : Prop where
  consts : h1.consts = h.consts
  istates : h1.istates = h.istates
  iallocs : h1.iallocs = h.iallocs
  dstates : h1.dstates = h.dstates
  dallocs : h1.dallocs = h.dallocs
  gzheaders : h1.gzheaders = h.gzheaders
  crc : h1.crcTable = h.crcTable
  x2n : h1.x2nTable = h.x2nTable
  base : h1.baseAddr = h.baseAddr
  allocOk : h1.allocOk = h.allocOk
  garbage : h1.garbage = h.garbage

theorem HSame.refl (h : Heap) : HSame h h := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The file-system part of `GzWF`. -/
def FsWF (fs : Fs) : Prop :=
  fs.budget < 2 ^ 62 ∧ (∀ d ∈ fs.nodes, d.size < 2 ^ 62) ∧ (∀ n v, fs.lseekChoice n = .value v → v = -1 ∨ 0 ≤ v)

/-- The embedded stream of the new state: no inflate or deflate state, and the allocator fields `NULL`
(`gz_state_init`). -/
def SNone (z : ZStream) : Prop := z.state = none ∧ z.zalloc = .null ∧ z.zfree = .null

/-- The state of a call of `gz_open` (see the module doc). -/
structure OI (w : World) (h : Heap) (b i : Nat) (w1 : World) (h1 : Heap) : Prop where
  wf0 : GzWF w h
  wf : GzWF w1 h1
  nb : h.nextBlk ≤ b
  inone : h.streams i = none
  next : h.nextBlk ≤ h1.nextBlk
  bytes : ∀ c, c < h.nextBlk → h1.bytes c = h.bytes c
  strOld : ∀ j z, h.streams j = some z → h1.streams j = some z
  gzOld : ∀ c, c < h.nextBlk → w1.gzs c = w.gzs c
  gzNew : ∀ c, h.nextBlk ≤ c → c ≠ b → w1.gzs c = none
  same : HSame h h1
  snone : ∀ z, h1.streams i = some z → SNone z

theorem fsWF_of {w : World} {h : Heap} (hwf : GzWF w h) : FsWF w.fs :=
  ⟨hwf.2.2.2.2.2.1, hwf.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.1⟩

theorem gzWF_mk {w : World} {h : Heap} (c : CrcGlobals h) (d : DFreshBlocks h) (o : ObjBound h)
    (g : ∀ b, h.nextBlk ≤ b → w.gzs b = none) (s : ∀ b s, w.gz h b = some s → ∃ z, h.streams s.strm = some z)
    (f : FsWF w.fs) (l : LitOk w h) : GzWF w h := ⟨c, d, o, g, s, f.1, f.2.1, f.2.2, l⟩

/-! ## The file system -/

/-- `fs'` has the budget and `lseek` oracle of `fs`, and its files are files of `fs` or empty. -/
def FsLe (fs fs' : Fs) : Prop :=
  fs'.budget = fs.budget ∧ fs'.lseekChoice = fs.lseekChoice ∧ ∀ d ∈ fs'.nodes, d ∈ fs.nodes ∨ d.size = 0

theorem FsLe.wf {fs fs' : Fs} (hf : FsWF fs) (l : FsLe fs fs') : FsWF fs' := by
  obtain ⟨h1, h2, h3⟩ := hf
  obtain ⟨l1, l2, l3⟩ := l
  refine ⟨by rw [l1]; exact h1, fun d hd => ?_, by rw [l2]; exact h3⟩
  rcases l3 d hd with e | e
  · exact h2 d e
  · omega

theorem FsLe.refl (fs : Fs) : FsLe fs fs := ⟨rfl, rfl, fun _ hd => Or.inl hd⟩

theorem FsLe.trans {a b c : Fs} (x : FsLe a b) (y : FsLe b c) : FsLe a c := by
  refine ⟨y.1.trans x.1, y.2.1.trans x.2.1, fun d hd => ?_⟩
  rcases y.2.2 d hd with e | e
  · exact x.2.2 d e
  · exact Or.inr e

theorem setFd_le (fs : Fs) (k : Nat) (o : Option OFile) : FsLe fs (fs.setFd k o) :=
  ⟨rfl, rfl, fun _ hd => Or.inl hd⟩

theorem lastOflag_le (fs : Fs) (x : Int32) : FsLe fs { fs with lastOflag := x } :=
  ⟨rfl, rfl, fun _ hd => Or.inl hd⟩

theorem errno_le (fs : Fs) (x : Int32) : FsLe fs { fs with errno := x } :=
  ⟨rfl, rfl, fun _ hd => Or.inl hd⟩

theorem tick_le (fs : Fs) : FsLe fs fs.tick := ⟨rfl, rfl, fun _ hd => Or.inl hd⟩

theorem openReg_le (fs : Fs) (p : Array UInt8) (fl : Int32) : FsLe fs (fs.openReg p fl).2 := by
  unfold Fs.openReg
  simp only
  generalize (fl &&& 3 == O_WRONLY) = wr
  generalize (fl &&& O_CREAT != 0) = cr
  generalize (fl &&& O_EXCL != 0) = ex
  generalize (fl &&& O_TRUNC != 0) = tr
  generalize (fl &&& O_APPEND != 0) = ap
  cases fs.lookup p with
  | some n =>
    cases cr && ex
    · simp only [Bool.false_eq_true, ite_false]
      have l1 : FsLe fs (if (tr && wr) = true then { fs with nodes := fs.nodes.set! n #[] } else fs) := by
        split
        · refine ⟨rfl, rfl, fun d hd => ?_⟩
          rcases Array.mem_or_eq_of_mem_setIfInBounds hd with e | e
          · exact Or.inl e
          · subst e; exact Or.inr rfl
        · exact FsLe.refl fs
      generalize (if (tr && wr) = true then { fs with nodes := fs.nodes.set! n #[] } else fs) = g at l1
      exact l1.trans ((setFd_le _ _ _).trans (lastOflag_le _ _))
    · exact errno_le _ _
  | none =>
    cases cr
    · exact errno_le _ _
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      have l1 : FsLe fs { fs with nodes := fs.nodes.push #[], names := fs.names.push (p, fs.nodes.size) } := by
        refine ⟨rfl, rfl, fun d hd => ?_⟩
        simp only [Array.mem_push] at hd
        rcases hd with e | e
        · exact Or.inl e
        · subst e; exact Or.inr rfl
      generalize ({ fs with nodes := fs.nodes.push #[], names := fs.names.push (p, fs.nodes.size) } : Fs) = g at l1
      exact l1.trans ((setFd_le _ _ _).trans (lastOflag_le _ _))

theorem openCall_le (fs : Fs) (p : Array UInt8) (fl : Int32) : FsLe fs (fs.openCall p fl).2 := by
  unfold Fs.openCall
  simp only
  split
  · exact (tick_le fs).trans (errno_le _ _)
  · exact (tick_le fs).trans (openReg_le _ _ _)

theorem lseekCall_le (fs : Fs) (fd : Int32) (off : Int64) (wh : Int32) : FsLe fs (fs.lseekCall fd off wh).2 := by
  unfold Fs.lseekCall Fs.lseekReg
  simp only
  split
  · split
    · split
      · exact ⟨rfl, rfl, fun d hd => Or.inl hd⟩
      · split
        · exact ⟨rfl, rfl, fun d hd => Or.inl hd⟩
        · split
          · exact ⟨rfl, rfl, fun d hd => Or.inl hd⟩
          · exact setFd_le _ _ _
    · exact ⟨rfl, rfl, fun d hd => Or.inl hd⟩
  · exact ⟨rfl, rfl, fun d hd => Or.inl hd⟩
  · exact ⟨rfl, rfl, fun d hd => Or.inl hd⟩

theorem closeCall_le (fs : Fs) (fd : Int32) : FsLe fs (fs.closeCall fd).2 := by
  unfold Fs.closeCall Fs.closeReg
  simp only
  split <;> (try split) <;> (try split) <;> first | (exact ⟨rfl, rfl, fun _ hd => Or.inl hd⟩) | (exact setFd_le _ _ _)

/-! ## Byte stores -/

theorem getD_set (a : Array UInt8) (p x : Nat) (v : UInt8) (hp : p < a.size) :
    (a.set! p v)[x]! = if x = p then v else a[x]! := by
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hx : x = p
  · subst hx; simp [hp]
  · simp [hx, getElem!_def, Ne.symm hx]

theorem fold_set (bs : Array UInt8) (off : Nat) : ∀ (k s : Nat) (a : Array UInt8), off + s + k ≤ a.size →
    (List.foldl (fun out i => out.set! (off + i) bs[i]!) a (List.range' s k)).size = a.size ∧
    ∀ x, (List.foldl (fun out i => out.set! (off + i) bs[i]!) a (List.range' s k))[x]! =
      if off + s ≤ x ∧ x < off + s + k then bs[x - off]! else a[x]! := by
  intro k
  induction k with
  | zero =>
    intro s a _
    simp only [List.range'_zero, List.foldl_nil, true_and]
    intro x; simp only [Nat.add_zero]; split <;> first | rfl | omega
  | succ k ih =>
    intro s a hk
    simp only [List.range'_succ, List.foldl_cons]
    obtain ⟨e1, e2⟩ := ih (s + 1) (a.set! (off + s) bs[s]!) (by simp; omega)
    refine ⟨by rw [e1]; simp, fun x => ?_⟩
    rw [e2, getD_set _ _ _ _ (by omega)]
    by_cases h1 : x = off + s
    · subst h1; simp
    · by_cases h2 : off + (s + 1) ≤ x ∧ x < off + (s + 1) + k
      · have h3 : off + s ≤ x ∧ x < off + s + (k + 1) := by omega
        simp only [h2, h3, and_self, ite_true]
      · have h3 : ¬(off + s ≤ x ∧ x < off + s + (k + 1)) := by omega
        simp only [h2, h3, h1, ite_false]

/-- The bytes `storeBytes` leaves. -/
def stored (a bs : Array UInt8) (off : Nat) : Array UInt8 :=
  List.foldl (fun out i => out.set! (off + i) bs[i]!) a (List.range' 0 bs.size)

theorem storeBytes_heap {h : Heap} {c off cap : Nat} {a bs : Array UInt8} (ha : h.bytes c = some a)
    (hc : off + cap ≤ a.size) (hb : bs.size ≤ cap) :
    storeBytes (.ref (.heap c) off) bs cap h = .ok ((), { h with bytes := h.bytes.modify c (Option.map fun _ => stored a bs off) }) := by
  have hg : Space.get h (BRef.heap c) = some a := ha
  simp only [storeBytes, hg]
  simp only [Space.ro, Heap.isRo, Bool.false_eq_true, ite_false, hc, hb, and_self, ite_true]
  simp [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Space.modify, Heap.modifyBytes, stored]

theorem stored_size (a bs : Array UInt8) (off : Nat) (h : off + bs.size ≤ a.size) :
    (stored a bs off).size = a.size := (fold_set bs off bs.size 0 a (by omega)).1

theorem stored_get (a bs : Array UInt8) (off : Nat) (h : off + bs.size ≤ a.size) (x : Nat) :
    (stored a bs off)[x]! = if off ≤ x ∧ x < off + bs.size then bs[x - off]! else a[x]! := by
  have := (fold_set bs off bs.size 0 a (by omega)).2 x
  simp only [Nat.add_zero] at this
  exact this

theorem modify_some {α : Type} (t : Tbl (Option α)) (c : Nat) (a : α) (g : α → α) (ha : t c = some a) (x : Nat) :
    (t.modify c (Option.map g)) x = if x = c then some (g a) else t x := by
  rw [Tbl.modify_opt t c g a ha]
  by_cases e : x = c
  · subst e; simp
  · simp [e, upd_ne _ _ _ _ e]

/-! ## Strings -/

theorem strBytes_of {h : Heap} {p : BPtr} {n : Nat} (hs : CStringLen h p n) :
    ∃ bs, strBytes p h = .ok (bs, h) ∧ bs.size = n ∧ ∀ j, j < n → bs[j]! ≠ 0 := by
  obtain ⟨r, off, data, rfl, hd, hn, hz, hnz⟩ := hs
  have hf : (data.extract off data.size).findIdx? (· == 0) = some n := by
    rw [Array.findIdx?_eq_some_iff_getElem]
    refine ⟨by simp; omega, ?_, fun j hj => ?_⟩
    · simp only [Array.getElem_extract]
      have : data[off + n]! = data[off + n] := by simp [show off + n < data.size by omega]
      simpa [← this] using hz
    · simp only [Array.getElem_extract]
      have e := hnz j (by omega)
      have : data[off + j]! = data[off + j] := by simp [show off + j < data.size by omega]
      simpa [← this] using e
  refine ⟨(data.extract off data.size).extract 0 n, by simp [strBytes, hd, hf], by simp; omega, fun j hj => ?_⟩
  have e := hnz j hj
  have h1 : ((data.extract off data.size).extract 0 n)[j]! = data[off + j]! := by
    simp [show j < min (off + n) data.size - off by omega,
      show off + j < data.size by omega]
  rw [h1]; exact e

theorem cstr_of_get {h h' : Heap} {p : BPtr} {n : Nat}
    (hg : ∀ (r : BRef) (d : Array UInt8), Space.get h r = some d → Space.get h' r = some d) (hs : CStringLen h p n) : CStringLen h' p n := by
  obtain ⟨r, off, data, e, hd, rest⟩ := hs
  exact ⟨r, off, data, e, hg r data hd, rest⟩

/-! ## The state of `gz_open` -/

theorem gz_of_bytes {w : World} {h h' : Heap} {c : Nat} (e : h'.bytes c = h.bytes c) : w.gz h' c = w.gz h c := by
  unfold World.gz; rw [e]

theorem gz_of_isSome {w : World} {h h' : Heap} {c : Nat} (e : (h'.bytes c).isSome = (h.bytes c).isSome) :
    w.gz h' c = w.gz h c := by
  unfold World.gz
  cases h1 : h'.bytes c <;> cases h2 : h.bytes c <;> simp_all

theorem OI.get_old {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} (o : OI w h b i w1 h1) (r : BRef)
    (d : Array UInt8) (hd : Space.get h r = some d) : Space.get h1 r = some d := by
  cases r with
  | heap c =>
    have hc : c < h.nextBlk := by
      refine Nat.lt_of_not_le fun hc => ?_
      have := (o.wf0.2.1.1 c hc).2.2
      have hd' : h.bytes c = some d := hd
      rw [this] at hd'; cases hd'
    show h1.bytes c = some d
    rw [o.bytes c hc]; exact hd
  | const c =>
    show h1.consts c = some d
    rw [o.same.consts]; exact hd
  | str k => exact hd

theorem OI.refl_gz {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} (o : OI w h b i w1 h1) {c : Nat}
    (hc : c < h.nextBlk) : w1.gz h1 c = w.gz h c := by
  unfold World.gz; rw [o.bytes c hc, o.gzOld c hc]

/-- The fields `gz_state_init` sets and the mode loop keeps. -/
structure P0 (i : Nat) (st : GzState) : Prop where
  size : st.size = 0
  want : st.want = GZBUFSIZE
  inp : st.«in» = .val .null
  out : st.out = .val .null
  msg : st.msg = .val .null
  past : st.past = 0
  skip : st.skip = 0
  strm : st.strm = i
  buffers : st.buffers = .uninit

theorem gzs_beyond {w : World} {h : Heap} (hwf : GzWF w h) : w.gzs h.nextBlk = none := hwf.2.2.2.1 _ (Nat.le_refl _)

theorem streams_size_none (h : Heap) : h.streams h.streams.arr.size = none := by
  show h.streams.get h.streams.arr.size = none
  rw [Tbl.get_eq]; simp; rfl

theorem objBound_old {h H : Heap} (ho : ObjBound h) (hc : H.consts = h.consts)
    (hb : ∀ c d, H.bytes c = some d → h.bytes c = some d ∨ d.size < 2 ^ 63) : ObjBound H := by
  intro r d hd
  cases r with
  | heap c =>
    rcases hb c d hd with e | e
    · exact ho (.heap c) d e
    · exact e
  | const c =>
    have hd' : H.consts c = some d := hd
    rw [hc] at hd'
    exact ho (.const c) d hd'
  | str k => exact ho (.str k) d hd

/-- The world and heap right after a successful `gz_state_init`. -/
theorem oi_init {w : World} {h : Heap} {W : World} {H : Heap} (hwf : GzWF w h)
    (hb : ∀ c, c ≠ h.nextBlk → H.bytes c = h.bytes c) (hbb : H.bytes h.nextBlk = some #[])
    (hs : ∀ j, j ≠ h.streams.arr.size → H.streams j = h.streams j) (hsi : ∃ z, H.streams h.streams.arr.size = some z)
    (hg : ∀ c, c ≠ h.nextBlk → W.gzs c = w.gzs c)
    (hgb : ∃ st, W.gzs h.nextBlk = some st ∧ st.strm = h.streams.arr.size) (hfs : W.fs = w.fs) (hn : H.nextBlk = h.nextBlk + 1) (same : HSame h H)
    (hsn : ∀ z, H.streams h.streams.arr.size = some z → SNone z) (hk : W.litKeys = w.litKeys) :
    OI w h h.nextBlk h.streams.arr.size W H := by
  have hi := streams_size_none h
  obtain ⟨st, hgb, hst⟩ := hgb
  have hnone : ∀ c, h.nextBlk ≤ c → h.bytes c = none := fun c hc => (hwf.2.1.1 c hc).2.2
  refine ⟨hwf, gzWF_mk ?_ ?_ ?_ ?_ ?_ ?_ (LitOk.ext hwf.lit hk fun _ _ e => by rw [same.consts]; exact e), Nat.le_refl _, hi, by omega, fun c hc => hb c (by omega), ?_,
    fun c hc => hg c (by omega), fun c hc hne => by rw [hg c hne]; exact hwf.2.2.2.1 c hc, same, hsn⟩
  · exact ⟨by rw [same.crc]; exact hwf.1.1, by rw [same.x2n]; exact hwf.1.2⟩
  · refine ⟨fun c hc => ⟨by rw [same.istates]; exact (hwf.2.1.1 c (by omega)).1,
      by rw [same.iallocs]; exact (hwf.2.1.1 c (by omega)).2.1, by rw [hb c (by omega)]; exact hnone c (by omega)⟩,
      fun c hc => ⟨by rw [same.dstates]; exact (hwf.2.1.2 c (by omega)).1,
        by rw [same.dallocs]; exact (hwf.2.1.2 c (by omega)).2⟩⟩
  · refine objBound_old hwf.2.2.1 same.consts fun c d hd => ?_
    by_cases e : c = h.nextBlk
    · subst e; rw [hbb] at hd; cases hd; exact Or.inr (by simp)
    · rw [hb c e] at hd; exact Or.inl hd
  · intro c hc; rw [hg c (by omega)]; exact hwf.2.2.2.1 c (by omega)
  · intro c s hs'
    by_cases e : c = h.nextBlk
    · subst e
      unfold World.gz at hs'
      rw [hbb, hgb] at hs'
      cases hs'
      rw [hst]; exact hsi
    · have : W.gz H c = w.gz h c := by unfold World.gz; rw [hb c e, hg c e]
      rw [this] at hs'
      obtain ⟨z, hz⟩ := hwf.2.2.2.2.1 c s hs'
      have hne : s.strm ≠ h.streams.arr.size := by intro e2; rw [e2, hi] at hz; cases hz
      exact ⟨z, by rw [hs _ hne]; exact hz⟩
  · rw [hfs]; exact fsWF_of hwf
  · intro j z hz
    have hne : j ≠ h.streams.arr.size := by intro e2; rw [e2, hi] at hz; cases hz
    rw [hs j hne]; exact hz

set_option maxHeartbeats 1000000 in
theorem state_init_spec {w : World} {h : Heap} (hwf : GzWF w h) : GSat w h gz_state_init (fun r w1 h1 =>
    (r = none ∧ w1 = w ∧ h1 = { h with nalloc := h.nalloc + 1 }) ∨
    (r = some h.nextBlk ∧ OI w h h.nextBlk h.streams.arr.size w1 h1 ∧ h1.nextBlk = h.nextBlk + 1 ∧
      ∃ st, w1.gz h1 h.nextBlk = some st ∧ P0 h.streams.arr.size st ∧ st.mode = GZ_NONE ∧ st.direct = 0)) := by
  by_cases hok : h.allocOk h.nalloc = true
  · refine ⟨?r, ?w1, ?h1, ?e, ?q⟩
    case e =>
      simp [gz_state_init, gzStateAlloc, allocB, hok, gzs_beyond hwf, cutBytes, newStream, strmOf, ldGz, World.gz,
        wrG, stGz, ZlibNg.Inflate.wrZ, ldStream, stStream, GzState.garbage]
      and_intros <;> rfl
    case q =>
      refine Or.inr ⟨rfl, oi_init hwf (fun c hc => ?_) ?_ (fun j hj => ?_) (by simp) (fun c hc => ?_) (by simp) rfl rfl
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun z hz => ?_) rfl, rfl, ?_⟩
      all_goals (try simp [upd_ne, World.gz, *])
      · simp at hz; rw [← hz]; exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨none, w, { h with nalloc := h.nalloc + 1 }, ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩
    simp [gz_state_init, gzStateAlloc, allocB, hok]

/-! ## Steps that keep `OI` -/

theorem HSame.trans {a b c : Heap} (x : HSame a b) (y : HSame b c) : HSame a c :=
  ⟨y.consts.trans x.consts, y.istates.trans x.istates, y.iallocs.trans x.iallocs, y.dstates.trans x.dstates,
    y.dallocs.trans x.dallocs, y.gzheaders.trans x.gzheaders, y.crc.trans x.crc, y.x2n.trans x.x2n,
    y.base.trans x.base, y.allocOk.trans x.allocOk, y.garbage.trans x.garbage⟩

/-- A change of the heap only. -/
theorem oi_heap {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 H : Heap} (o : OI w h b i w1 h1)
    (same : HSame h1 H) (hn : h1.nextBlk ≤ H.nextBlk)
    (hbytes : ∀ c, c < h.nextBlk → H.bytes c = h1.bytes c)
    (hfresh : ∀ c, H.nextBlk ≤ c → H.bytes c = none)
    (hob : ∀ c d, H.bytes c = some d → h1.bytes c = some d ∨ d.size < 2 ^ 63)
    (hgz : ∀ c, H.nextBlk ≤ c → w1.gzs c = none)
    (hstr : ∀ c s, w1.gz H c = some s → ∃ z, H.streams s.strm = some z)
    (hold : ∀ j z, h1.streams j = some z → h.streams j = some z → H.streams j = some z)
    (hsn : ∀ z, H.streams i = some z → SNone z) : OI w h b i w1 H := by
  have wf := o.wf
  refine ⟨o.wf0, gzWF_mk ?_ ?_ ?_ hgz hstr (fsWF_of wf) (LitOk.ext wf.lit rfl fun _ _ e => by rw [same.consts]; exact e), o.nb, o.inone, by have := o.next; omega,
    fun c hc => by rw [hbytes c hc]; exact o.bytes c hc,
    fun j z hz => hold j z (o.strOld j z hz) hz, o.gzOld, o.gzNew, o.same.trans same, hsn⟩
  · exact ⟨by rw [same.crc]; exact wf.1.1, by rw [same.x2n]; exact wf.1.2⟩
  · exact ⟨fun c hc => ⟨by rw [same.istates]; exact (wf.2.1.1 c (by omega)).1,
      by rw [same.iallocs]; exact (wf.2.1.1 c (by omega)).2.1, hfresh c hc⟩,
      fun c hc => ⟨by rw [same.dstates]; exact (wf.2.1.2 c (by omega)).1,
        by rw [same.dallocs]; exact (wf.2.1.2 c (by omega)).2⟩⟩
  · refine objBound_old wf.2.2.1 same.consts fun c d hd => ?_
    rcases hob c d hd with e | e
    · exact Or.inl e
    · exact Or.inr e

/-- A change of the world only: the `gz_state` of `b` (keeping a live stream) and the file system. -/
theorem oi_world {w : World} {h : Heap} {b i : Nat} {w1 W : World} {h1 : Heap} (o : OI w h b i w1 h1)
    (hg : ∀ c, c ≠ b → W.gzs c = w1.gzs c) (hgb : ∀ s, W.gz h1 b = some s → ∃ z, h1.streams s.strm = some z)
    (hfs : FsLe w1.fs W.fs) (hb : b < h1.nextBlk) (hk : W.litKeys = w1.litKeys) : OI w h b i W h1 := by
  have wf := o.wf
  refine ⟨o.wf0, gzWF_mk wf.1 wf.2.1 wf.2.2.1 (fun c hc => ?_) (fun c s hs => ?_) (hfs.wf (fsWF_of wf))
    (LitOk.ext wf.lit hk fun _ _ e => e), o.nb,
    o.inone, o.next, o.bytes, o.strOld, fun c hc => ?_, fun c hc hne => ?_, o.same, o.snone⟩
  · by_cases e : c = b
    · omega
    · rw [hg c e]; exact wf.2.2.2.1 c hc
  · by_cases e : c = b
    · subst e; exact hgb s hs
    · have : W.gz h1 c = w1.gz h1 c := by unfold World.gz; rw [hg c e]
      rw [this] at hs; exact wf.2.2.2.2.1 c s hs
  · rw [hg c (by have := o.nb; omega)]; exact o.gzOld c hc
  · rw [hg c hne]; exact o.gzNew c hc hne

theorem gsat_wrG_oi {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} {s : GzState}
    (o : OI w h b i w1 h1) (hs : w1.gz h1 b = some s) (hbl : b < h1.nextBlk) (f : GzState → GzState)
    (hf : (f s).strm = s.strm) :
    GSat w1 h1 (wrG (some b) f) (fun _ W H => H = h1 ∧ W.gz H b = some (f s) ∧ OI w h b i W H) := by
  refine GSat.of_eq (wrG_app hs f) ⟨rfl, gz_upd_same hs _, oi_world o (fun c hc => ?_) (fun s' hs' => ?_)
    (FsLe.refl _) hbl rfl⟩
  · show (upd w1.gzs b (some (f s))) c = w1.gzs c
    rw [upd_ne _ _ _ _ hc]
  · rw [gz_upd_same hs] at hs'
    cases hs'
    rw [hf]; exact o.wf.2.2.2.2.1 b s hs

/-- The heap after a successful `malloc(n)`. -/
def allocH (h : Heap) (n : Nat) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := n) fun j => Junk.of (h.garbage h.nalloc j.val)))
    savedPtrs := upd h.savedPtrs h.nextBlk none
    nextBlk := h.nextBlk + 1
    nalloc := h.nalloc + 1 }

theorem allocB_ok {h : Heap} (hok : h.allocOk h.nalloc = true) (n : Nat) :
    allocB n h = .ok (.ref (.heap h.nextBlk) 0, allocH h n) := by
  simp [allocB, hok, allocH]

theorem sat_alloc_oi {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} (o : OI w h b i w1 h1)
    (n : Nat) (hn : n < 2 ^ 63) :
    Sat h1 (allocB n) (fun p H => OI w h b i w1 H ∧ h1.nextBlk ≤ H.nextBlk ∧
      (∀ c, c < h1.nextBlk → H.bytes c = h1.bytes c) ∧ H.streams = h1.streams ∧
      (p = .null ∨ (p = .ref (.heap h1.nextBlk) 0 ∧ ∃ d, H.bytes h1.nextBlk = some d ∧ d.size = n ∧
        H.nextBlk = h1.nextBlk + 1 ∧ w1.gzs h1.nextBlk = none))) := by
  have wf := o.wf
  by_cases hok : h1.allocOk h1.nalloc = true
  · refine ⟨_, _, allocB_ok hok n, ?_⟩
    have hne : ∀ c, c < h1.nextBlk → c ≠ h1.nextBlk := fun c hc => by omega
    refine ⟨oi_heap o ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by simp [allocH])
      (fun c hc => by simp [allocH, upd_ne _ _ _ _ (hne c (by have := o.next; omega))])
      (fun c hc => ?_) (fun c d hd => ?_) (fun c hc => wf.2.2.2.1 c (by simp [allocH] at hc; omega)) (fun c s hs => ?_)
      (fun j z hz _ => hz) o.snone, by simp [allocH], fun c hc => by simp [allocH, upd_ne _ _ _ _ (hne c hc)], rfl,
      Or.inr ⟨rfl, Array.ofFn (n := n) fun j => Junk.of (h1.garbage h1.nalloc j.val), by simp only [allocH, upd_same],
        Array.size_ofFn, rfl, gzs_beyond wf⟩⟩
    · simp only [allocH] at hc ⊢
      rw [upd_ne _ _ _ _ (by omega)]; exact (wf.2.1.1 c (by omega)).2.2
    · simp only [allocH] at hd
      by_cases e : c = h1.nextBlk
      · subst e; rw [upd_same] at hd; cases hd; exact Or.inr (by simp; omega)
      · rw [upd_ne _ _ _ _ e] at hd; exact Or.inl hd
    · by_cases e : c = h1.nextBlk
      · subst e; unfold World.gz at hs; simp only [allocH, upd_same] at hs; rw [gzs_beyond wf] at hs; cases hs
      · rw [gz_of_bytes (h := h1) (by simp [allocH, upd_ne _ _ _ _ e])] at hs; exact wf.2.2.2.2.1 c s hs
  · refine ⟨.null, { h1 with nalloc := h1.nalloc + 1 }, by simp [allocB, hok], ?_⟩
    refine ⟨oi_heap o ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _) (fun _ _ => rfl)
      (fun c hc => (wf.2.1.1 c hc).2.2) (fun c d hd => Or.inl hd) wf.2.2.2.1 (fun c s hs => wf.2.2.2.2.1 c s hs)
      (fun j z hz _ => hz) o.snone, Nat.le_refl _, fun _ _ => rfl, rfl, Or.inl rfl⟩

/-- `free` of a fresh block that holds no `gz_state`. -/
theorem sat_free_oi {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} (o : OI w h b i w1 h1) {c : Nat}
    (hc : h.nextBlk ≤ c) (hcb : c ≠ b) {d : Array UInt8} (hd : h1.bytes c = some d) :
    Sat h1 (freeB (.ref (.heap c) 0)) (fun _ H => OI w h b i w1 H ∧ H.bytes c = none ∧
      (∀ c', c' ≠ c → H.bytes c' = h1.bytes c') ∧ H.streams = h1.streams ∧ H.nextBlk = h1.nextBlk) := by
  have wf := o.wf
  refine ⟨(), _, by simp [freeB, hd]; rfl, ?_⟩
  refine ⟨oi_heap o ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _)
    (fun c' hc' => by simp [upd_ne _ _ _ _ (show c' ≠ c by omega)]) (fun c' hc' => ?_) (fun c' d' hd' => ?_)
    wf.2.2.2.1 (fun c' s hs => ?_) (fun j z hz _ => hz) o.snone, by simp, fun c' hc' => by simp [upd_ne _ _ _ _ hc'], rfl, rfl⟩
  · by_cases e : c' = c
    · subst e; simp
    · simp only; rw [upd_ne _ _ _ _ e]; exact (wf.2.1.1 c' hc').2.2
  · by_cases e : c' = c
    · subst e; simp at hd'
    · simp only at hd'; rw [upd_ne _ _ _ _ e] at hd'; exact Or.inl hd'
  · by_cases e : c' = c
    · subst e; unfold World.gz at hs; simp at hs
    · rw [gz_of_bytes (h := h1) (by simp [upd_ne _ _ _ _ e])] at hs; exact wf.2.2.2.2.1 c' s hs

/-- `gz_state_free` of the fresh state: everything of it is gone. -/
theorem gsat_free_state {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} {s : GzState}
    (o : OI w h b i w1 h1) (hs : w1.gz h1 b = some s) (hsi : s.strm = i) :
    GSat w1 h1 (gz_state_free (some b)) (fun _ W H => OI w h b i W H ∧ W.gzs b = none ∧ H.bytes b = none ∧
      H.streams i = none ∧ (∀ c, c ≠ b → H.bytes c = h1.bytes c) ∧ H.nextBlk = h1.nextBlk ∧ W.fs = w1.fs) := by
  have wf := o.wf
  have hb : ∃ d, h1.bytes b = some d := by
    unfold World.gz at hs; split at hs
    · next d hd => exact ⟨d, hd⟩
    · cases hs
  obtain ⟨d, hd⟩ := hb
  obtain ⟨z, hz⟩ := wf.2.2.2.2.1 b s hs
  rw [hsi] at hz
  have hbn : b < h1.nextBlk := by
    refine Nat.lt_of_not_le fun hc => ?_
    rw [(wf.2.1.1 b hc).2.2] at hd; cases hd
  have hio : ∀ c t, c ≠ b → w1.gz h1 c = some t → t.strm ≠ i := by
    intro c t hc ht e
    by_cases hc' : c < h.nextBlk
    · rw [o.refl_gz hc'] at ht
      obtain ⟨z', hz'⟩ := o.wf0.2.2.2.2.1 c t ht
      rw [e, o.inone] at hz'; cases hz'
    · unfold World.gz at ht
      rw [o.gzNew c (by omega) hc] at ht
      split at ht <;> cases ht
  refine ⟨(), { w1 with gzs := upd w1.gzs b none },
    { h1 with bytes := upd h1.bytes b none, savedPtrs := upd h1.savedPtrs b none, streams := upd h1.streams i none },
    by simp [gz_state_free, gzStateFree, ldGz_app hs, freeB, hd, dropStream, hsi, hz], ?_⟩
  have o1 : OI w h b i { w1 with gzs := upd w1.gzs b none } h1 :=
    oi_world o (fun c hc => by simp [upd_ne _ _ _ _ hc]) (fun s' hs' => by unfold World.gz at hs'; simp [hd] at hs')
      (FsLe.refl _) hbn rfl
  refine ⟨oi_heap o1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _)
    (fun c hc => by simp [upd_ne _ _ _ _ (show c ≠ b by have := o.nb; omega)]) (fun c hc => ?_)
    (fun c d' hd' => ?_) o1.wf.2.2.2.1 (fun c t ht => ?_) (fun j z' hz' hj => ?_) (fun z hz => by simp at hz), by simp, by simp, by simp,
    fun c hc => by simp [upd_ne _ _ _ _ hc], rfl, rfl⟩
  · by_cases e : c = b
    · subst e; simp
    · simp only; rw [upd_ne _ _ _ _ e]; exact (wf.2.1.1 c hc).2.2
  · by_cases e : c = b
    · subst e; simp at hd'
    · simp only at hd'; rw [upd_ne _ _ _ _ e] at hd'; exact Or.inl hd'
  · by_cases e : c = b
    · subst e; unfold World.gz at ht; simp at ht
    · rw [gz_of_bytes (h := h1) (by simp [upd_ne _ _ _ _ e])] at ht
      have ht' : w1.gz h1 c = some t := by unfold World.gz at ht ⊢; simpa [upd_ne _ _ _ _ e] using ht
      obtain ⟨z', hz'⟩ := wf.2.2.2.2.1 c t ht'
      exact ⟨z', by simp only; rw [upd_ne _ _ _ _ (hio c t e ht')]; exact hz'⟩
  · have : j ≠ i := by intro e; rw [e, o.inone] at hj; cases hj
    simp only; rw [upd_ne _ _ _ _ this]; exact hz'

/-- `snprintf(state->path, len + 1, "%s", path)` into the fresh path block: a copy of the string. -/
theorem sat_snprintf_path {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} (o : OI w h b i w1 h1)
    {c : Nat} (hc : h.nextBlk ≤ c) {d : Array UInt8} (hd : h1.bytes c = some d) {path : BPtr} {np : Nat}
    (hp : CStringLen h1 path np) (hds : d.size = np + 1) (hnp : np + 1 < 2 ^ 64) :
    Sat h1 (snprintfS (.ref (.heap c) 0) (UInt64.ofNat (np + 1)) path) (fun _ H => OI w h b i w1 H ∧
      CStringLen H (.ref (.heap c) 0) np ∧ (∀ c', c' ≠ c → H.bytes c' = h1.bytes c') ∧ H.streams = h1.streams ∧
      H.nextBlk = h1.nextBlk ∧ (∃ d', H.bytes c = some d')) := by
  have wf := o.wf
  obtain ⟨bs, ebs, hbs, hnz⟩ := strBytes_of hp
  have hsz : (UInt64.ofNat (np + 1)).toNat = np + 1 := by
    rw [UInt64.toNat_ofNat_of_lt' hnp]
  have hne : UInt64.ofNat (np + 1) ≠ 0 := by
    intro e; have := congrArg UInt64.toNat e; rw [hsz] at this; simp at this
  have hk : min bs.size ((UInt64.ofNat (np + 1)).toNat - 1) = np := by rw [hsz, hbs]; simp
  have hlen : ((bs.extract 0 np).push 0).size = np + 1 := by simp; omega
  have est := storeBytes_heap (h := h1) (c := c) (off := 0) (cap := np + 1) (bs := (bs.extract 0 np).push 0) hd
    (by omega) (by omega)
  have e : snprintfS (.ref (.heap c) 0) (UInt64.ofNat (np + 1)) path h1 =
      .ok ((if bs.size < 2 ^ 31 then Int32.ofNat bs.size else -1),
        { h1 with bytes := h1.bytes.modify c (Option.map fun _ => stored d ((bs.extract 0 np).push 0) 0) }) := by
    generalize UInt64.ofNat (np + 1) = L at hsz hne hk
    have e2 : min bs.size np = np := by rw [hbs]; simp
    simp [snprintfS, snprintfOut, ebs, hne, hsz, e2, est]
  refine ⟨_, _, e, ?_⟩
  have hget : ∀ x, (h1.bytes.modify c (Option.map fun _ => stored d ((bs.extract 0 np).push 0) 0)) x =
      if x = c then some (stored d ((bs.extract 0 np).push 0) 0) else h1.bytes x := modify_some _ _ _ _ hd
  refine ⟨oi_heap o ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _)
    (fun c' hc' => by simp only [hget]; simp [show c' ≠ c by omega]) (fun c' hc' => ?_) (fun c' d' hd' => ?_)
    wf.2.2.2.1 (fun c' t ht => ?_) (fun j z hz _ => hz) o.snone, ?_, fun c' hc' => by simp only [hget]; simp [hc'], rfl, rfl,
    ⟨stored d ((bs.extract 0 np).push 0) 0, by simp only [hget]; simp⟩⟩
  · simp only [hget]
    have : c' ≠ c := by
      intro e; subst e
      have := (wf.2.1.1 c' hc').2.2; rw [this] at hd; cases hd
    simp [this]; exact (wf.2.1.1 c' hc').2.2
  · simp only [hget] at hd'
    by_cases e : c' = c
    · subst e; simp at hd'; subst hd'
      right; rw [stored_size _ _ _ (by omega)]; exact wf.2.2.1 (.heap c') d hd
    · simp [e] at hd'; exact Or.inl hd'
  · rw [gz_of_isSome (h := h1) (by simp only [hget]; split <;> simp_all)] at ht
    exact wf.2.2.2.2.1 c' t ht
  · refine ⟨.heap c, 0, stored d ((bs.extract 0 np).push 0) 0, rfl, by show (h1.bytes.modify c _) c = _; rw [hget]; simp,
      by rw [stored_size _ _ _ (by omega)]; omega, ?_, fun j hj => ?_⟩
    · rw [stored_get _ _ _ (by omega)]
      simp only [Nat.zero_add, Nat.zero_le, true_and, hlen, Nat.lt_succ_self, ite_true, Nat.sub_zero]
      simp [Array.getElem_push, hbs]
    · rw [stored_get _ _ _ (by omega)]
      have hj' : j < np + 1 := by omega
      simp only [Nat.zero_add, Nat.zero_le, true_and, hlen, hj', ite_true, Nat.sub_zero]
      have := hnz j hj
      simpa [getElem!_def, Array.getElem?_push, hbs, hj, show j < np by omega, show j ≠ np by omega] using this

/-- A change of the stream record `i` (kept live) only. -/
theorem oi_stream {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} (o : OI w h b i w1 h1) (z : ZStream)
    (hzs : SNone z) :
    OI w h b i w1 { h1 with streams := upd h1.streams i (some z) } := by
  have wf := o.wf
  refine oi_heap o ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _) (fun _ _ => rfl)
    (fun c hc => (wf.2.1.1 c hc).2.2) (fun c d hd => Or.inl hd) wf.2.2.2.1 (fun c t ht => ?_) (fun j z' hz hj => ?_)
    (fun z' hz' => by simp at hz'; rw [← hz']; exact hzs)
  · obtain ⟨z0, hz0⟩ := wf.2.2.2.2.1 c t ht
    by_cases e : t.strm = i
    · exact ⟨z, by simp [e]⟩
    · exact ⟨z0, by simp only; rw [upd_ne _ _ _ _ e]; exact hz0⟩
  · have : j ≠ i := by intro e; rw [e, o.inone] at hj; cases hj
    simp only; rw [upd_ne _ _ _ _ this]; exact hz

/-- The file system calls of `gz_open`. -/
theorem oi_fs {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} (o : OI w h b i w1 h1) (fs : Fs)
    (hf : FsLe w1.fs fs) (hb : b < h1.nextBlk) : OI w h b i { w1 with fs := fs } h1 :=
  oi_world o (fun _ _ => rfl) (fun s hs => o.wf.2.2.2.2.1 b s hs) hf hb rfl

set_option maxHeartbeats 1000000 in
/-- `gz_reset` of the fresh state (no message yet). -/
theorem gsat_reset {w : World} {h : Heap} {b i : Nat} {w1 : World} {h1 : Heap} {st : GzState}
    (o : OI w h b i w1 h1) (hs : w1.gz h1 b = some st) (hbl : b < h1.nextBlk) (hmsg : st.msg = .val .null)
    (hsi : st.strm = i) :
    GSat w1 h1 (gz_reset (some b)) (fun _ W H => OI w h b i W H ∧ H.bytes = h1.bytes ∧ H.nextBlk = h1.nextBlk ∧
      (∀ z, H.streams i = some z → z.avail_in = 0) ∧ ∃ st', W.gz H b = some st' ∧ st'.path = st.path ∧ st'.mode = st.mode ∧ st'.strm = st.strm ∧
        st'.size = st.size ∧ st'.want = st.want ∧ st'.msg = st.msg ∧ st'.pos = 0 ∧ st'.skip = 0 ∧
        st'.err = ZlibNg.Inflate.Z_OK ∧ st'.«have» = 0 ∧ st'.buffers = st.buffers ∧ (st.mode = GZ_READ → st'.how = LOOK)) := by
  obtain ⟨d, hd⟩ : ∃ d, h1.bytes b = some d := by
    unfold World.gz at hs; split at hs
    · next d hd => exact ⟨d, hd⟩
    · cases hs
  have hgs : w1.gzs b = some st := by unfold World.gz at hs; rw [hd] at hs; exact hs
  obtain ⟨z, hz⟩ := o.wf.2.2.2.2.1 b st hs
  rw [hsi] at hz
  have hW : ∀ (W : World), W.fs = w1.fs → (∀ c, c ≠ b → W.gzs c = w1.gzs c) →
      (∃ s', W.gzs b = some s' ∧ s'.strm = i) → W.litKeys = w1.litKeys → OI w h b i W h1 := fun W hf hg ⟨s', e1, e2⟩ hk =>
    oi_world o hg (fun t ht => by unfold World.gz at ht; rw [hd, e1] at ht; cases ht; rw [e2]; exact ⟨z, hz⟩)
      (by rw [hf]; exact FsLe.refl _) hbl hk
  by_cases hm : st.mode = GZ_READ
  · refine ⟨?r, ?W, ?H, ?e, ?q⟩
    case e =>
      simp [gz_reset, gz_error, wrG, stGz, ldGz, rdG, World.gz, hd, hgs, hm, hmsg, strmOf, ZlibNg.Inflate.wrZ,
        ldStream, stStream, hsi, hz, Ival.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, getHeap_app]
      and_intros <;> rfl
    case q =>
      refine ⟨oi_stream (hW _ ?_ ?_ ?_ ?_) _ (o.snone z hz), rfl, rfl, fun z' hz' => by simp at hz'; rw [← hz'], ?_⟩
      · rfl
      · intro c hc; simp only [upd_ne _ _ _ _ hc]
      · simp
      · rfl
      · simp [World.gz, hd, hm, hmsg, ZlibNg.Inflate.Z_OK]
        exact hsi.symm
  · refine ⟨?r2, ?W2, ?H2, ?e2, ?q2⟩
    case e2 =>
      simp [gz_reset, gz_error, wrG, stGz, ldGz, rdG, World.gz, hd, hgs, hm, hmsg, strmOf, ZlibNg.Inflate.wrZ,
        ldStream, stStream, hsi, hz, Ival.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, getHeap_app]
      and_intros <;> rfl
    case q2 =>
      refine ⟨oi_stream (hW _ ?_ ?_ ?_ ?_) _ (o.snone z hz), rfl, rfl, fun z' hz' => by simp at hz'; rw [← hz'], ?_⟩
      · rfl
      · intro c hc; simp only [upd_ne _ _ _ _ hc]
      · simp
      · rfl
      · simp [World.gz, hd, hm, hsi, hmsg, ZlibNg.Inflate.Z_OK]

/-! ## The mode loop -/

/-- The modes the loop may leave. -/
def MS (m : Int32) : Prop := m = GZ_NONE ∨ m = GZ_READ ∨ m = GZ_WRITE ∨ m = GZ_APPEND

/-- The invariant of the mode loop: the mode string is `n` characters at `off0` of object `r0`. -/
abbrev LI (w : World) (h : Heap) (b i : Nat) (r0 : BRef) (off0 : Nat) (n : Nat) (s : OpenLoop) (W : World) (H : Heap) :
    Prop :=
  OI w h b i W H ∧ b < H.nextBlk ∧ (∃ k, s.mode = .ref r0 (off0 + k) ∧ k ≤ n) ∧
  ((s.ctl = .go ∧ ∃ st, W.gz H b = some st ∧ P0 i st ∧ MS st.mode) ∨
   (s.ctl = .ret ∧ W.gzs b = none ∧ H.bytes b = none ∧ H.streams i = none))

/-- The measure of the mode loop. -/
def LM (off0 n : Nat) (s : OpenLoop) : Nat :=
  match s.mode with
  | .ref _ o => if s.ctl = .go then off0 + n + 1 - o else 0
  | .null => 0

theorem load8_ok {H : Heap} {r : BRef} {d : Array UInt8} {o : Nat} (hd : Space.get H r = some d) (ho : o < d.size) :
    load8 (.ref r o) H = .ok (d[o]!, H) := by
  simp [load8, Ptr.load, hd, ho]

theorem add1_ok {H : Heap} {r : BRef} {d : Array UInt8} {o : Nat} (hd : Space.get H r = some d) (ho : o + 1 ≤ d.size) :
    Ptr.add (.ref r o) 1 H = .ok (.ref r (o + 1), H) := by
  have c : o ≤ d.size ∧ 0 ≤ (o : Int) + 1 ∧ (o : Int) + 1 ≤ (d.size : Int) := ⟨by omega, by omega, by omega⟩
  simp only [Ptr.add, hd, c, and_self, ite_true]
  rfl

/-- The end of a trip of the mode loop: `mode++`. -/
theorem jp_ok {w : World} {h : Heap} {b i : Nat} {r0 : BRef} {off0 n : Nat} {d : Array UInt8} {W : World} {H : Heap}
    {s : OpenLoop} {k : Nat} (o : OI w h b i W H) (hbl : b < H.nextBlk) (hd : Space.get H r0 = some d)
    (hn : off0 + n + 1 ≤ d.size) (hm : s.mode = .ref r0 (off0 + k)) (hk : k < n) (hc : s.ctl = .go)
    (hst : ∃ st, W.gz H b = some st ∧ P0 i st ∧ MS st.mode) (cl ex : Int32) :
    GSat W H (C.lm (Ptr.add s.mode 1) >>= fun m => pure ({ mode := m, cloexec := cl, exclusive := ex, ctl := s.ctl } : OpenLoop))
      (fun s2 W2 H2 => LI w h b i r0 off0 n s2 W2 H2 ∧ LM off0 n s2 < LM off0 n s) := by
  rw [hm]
  refine GSat.bind (GSat.lm ⟨_, H, add1_ok hd (by omega), ?_⟩)
  refine GSat.pure ⟨⟨o, hbl, ⟨k + 1, by simp; omega, by omega⟩, Or.inl ⟨hc, hst⟩⟩, ?_⟩
  simp [LM, hm, hc]
  omega

/-- The end of `gz_open`: well formed, and in the frame of an opening call. -/
theorem OI.post {w : World} {h : Heap} {b i : Nat} {W : World} {H : Heap} (o : OI w h b i W H) :
    GzWF W H ∧ GzOpenFrame w h W H := by
  refine ⟨o.wf, ⟨⟨fun _ _ => rfl, fun k _ => by simp [o.same.gzheaders],
    fun c _ _ => ⟨by simp [o.same.istates], by simp [o.same.iallocs]⟩,
    fun c hc _ d hd => ⟨d, by simp only; rw [o.bytes c hc]; exact hd, rfl, fun _ _ _ => rfl⟩,
    fun c hc _ hn => by simp only; rw [o.bytes c hc]; exact hn, rfl, o.same.crc, o.same.x2n, o.same.base, o.next⟩,
    fun c _ _ => ⟨by simp [o.same.dstates], by simp [o.same.dallocs]⟩⟩,
    o.strOld, fun k a e => by rw [o.same.consts]; exact e, o.gzOld⟩

/-- What a call of `gz_open` leaves. -/
def OpenPost (w : World) (h : Heap) (r : GzPtr) (W : World) (H : Heap) : Prop :=
  GzWF W H ∧ GzOpenFrame w h W H ∧
    ∀ b, r = some b → GzInv W H (some b) ∧ ∃ s, W.gz H b = some s ∧ h.streams s.strm = none ∧ s.size = 0 ∧
      s.msg = .val .null ∧ ∃ c, s.path = .val (.ref (.heap c) 0) ∧ h.nextBlk ≤ c

/-- A call that only counts a failed allocation (or changes nothing) is in the frame. -/
theorem post_refl {w : World} {h : Heap} (hwf : GzWF w h) (k : Nat) :
    OpenPost w h none w { h with nalloc := k } :=
  ⟨hwf, ⟨⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ d hd => ⟨d, hd, rfl, fun _ _ _ => rfl⟩,
    fun _ _ _ hn => hn, rfl, rfl, rfl, rfl, Nat.le_refl _⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩,
    fun _ _ e => e, fun _ _ e => e, fun _ _ => rfl⟩, fun _ e => by cases e⟩

set_option hygiene false in
/-- A trip of the mode loop that stores into the state, then `mode++`. -/
macro "leafA" : tactic => `(tactic| (
  refine GSat.bind (GSat.mono (gsat_wrG_oi o hst hbl _ rfl) fun _ W' H' q => ?_)
  obtain ⟨rfl, hst', o'⟩ := q
  exact jp_ok o' hbl hdH hn hmk hk hc ⟨_, hst', ⟨p0.1, p0.2, p0.3, p0.4, p0.5, p0.6, p0.7, p0.8, p0.9⟩,
    by unfold MS; first | exact hms | simp⟩ _ _))

/-! ## The tail of `gz_open`

The translation repeats the end of `gz_open` once per branch before it (the do-notation copies the continuation).
The copies below are the same source text; each copy in `gz_open` is the corresponding definition (`rfl`). -/

/-- From the `GZ_READ` test after the `GZ_APPEND` seek to the end (`gzlib.c:281-290`). -/
def tailRead (state : GzPtr) : G GzPtr := do
  if (← rdG state (·.mode)) == GZ_READ then
    let st ← lseekG (← rdG state (·.fd)) 0 SEEK_CUR
    wrG state fun s => { s with start := st }
    if (← rdG state (·.start)) == -1 then
      wrG state fun s => { s with start := 0 }
  gz_reset state
  return state

/-- From `state->fd = ...` to the end (`gzlib.c:266-290`). -/
def tailFd (state : GzPtr) (sfd : Int32) : G GzPtr := do
  wrG state fun s => { s with fd := sfd }
  if (← rdG state (·.fd)) == -1 then
    lm (freeB (← (← ldGz state).path.get))
    gz_state_free state
    return none
  if (← rdG state (·.mode)) == GZ_APPEND then
    let _ ← lseekG (← rdG state (·.fd)) 0 SEEK_END
    wrG state fun s => { s with mode := GZ_WRITE }
  if (← rdG state (·.mode)) == GZ_READ then
    let st ← lseekG (← rdG state (·.fd)) 0 SEEK_CUR
    wrG state fun s => { s with start := st }
    if (← rdG state (·.start)) == -1 then
      wrG state fun s => { s with start := 0 }
  gz_reset state
  return state

/-- From `len = strlen(path)` to the end (`gzlib.c:229-290`). -/
def tailPath (path : BPtr) (fd : Int32) (cloexec exclusive : Int32) (state : GzPtr) : G GzPtr := do
  let len ← lm (strlenB path)
  let p ← lm (allocB (len + 1).toNat)
  wrG state fun s => { s with path := .val p }
  if (← (← ldGz state).path.get) == .null then
    gz_state_free state
    return none
  let _ ← lm (snprintfS (← (← ldGz state).path.get) (len + 1) path)
  let smode ← rdG state (·.mode)
  let oflag : Int32 :=
    O_LARGEFILE |||
    (if cloexec != 0 then O_CLOEXEC else 0) |||
    (if smode == GZ_READ then O_RDONLY else
      (O_WRONLY ||| O_CREAT ||| (if exclusive != 0 then O_EXCL else 0) |||
        (if smode == GZ_WRITE then O_TRUNC else O_APPEND)))
  let sfd ← if fd > -1 then pure fd else openG path oflag
  wrG state fun s => { s with fd := sfd }
  if (← rdG state (·.fd)) == -1 then
    lm (freeB (← (← ldGz state).path.get))
    gz_state_free state
    return none
  if (← rdG state (·.mode)) == GZ_APPEND then
    let _ ← lseekG (← rdG state (·.fd)) 0 SEEK_END
    wrG state fun s => { s with mode := GZ_WRITE }
  if (← rdG state (·.mode)) == GZ_READ then
    let st ← lseekG (← rdG state (·.fd)) 0 SEEK_CUR
    wrG state fun s => { s with start := st }
    if (← rdG state (·.start)) == -1 then
      wrG state fun s => { s with start := 0 }
  gz_reset state
  return state

/-- The facts the tail needs about the state: the fields of `gz_state_init`, and the path, once set, an owned copy
in a fresh block. -/
structure TS (h : Heap) (b i : Nat) (W : World) (H : Heap) (st : GzState) : Prop where
  hst : W.gz H b = some st
  hbl : b < H.nextBlk
  p0 : P0 i st

theorem gzbufsize_toNat : GZBUFSIZE.toNat = 131072 := by decide

/-- `gz_reset(state); return state;` -/
theorem finish_ok {w : World} {h : Heap} {b i : Nat} {W : World} {H : Heap} {st : GzState}
    (o : OI w h b i W H) (t : TS h b i W H st) (hmode : st.mode = GZ_READ ∨ st.mode = GZ_WRITE)
    (hpath : OwnedStr H st.path) (hfr : ∃ c, st.path = .val (.ref (.heap c) 0) ∧ h.nextBlk ≤ c ∧ c ≠ b) :
    GSat W H (gz_reset (some b) >>= fun _ => pure (some b)) (OpenPost w h) := by
  refine GSat.bind (GSat.mono (gsat_reset o t.hst t.hbl t.p0.msg t.p0.strm) fun _ W' H' q => ?_)
  obtain ⟨o', hby, -, hav, st', hst', hpa, hmo, hstm, hsz, hwa, hms, hpo, hsk, -, hhv, hbu, hhow⟩ := q
  refine GSat.pure ⟨o'.post.1, o'.post.2, fun b' e => ?_⟩
  cases e
  have hsz0 : st'.size = 0 := by rw [hsz]; exact t.p0.size
  obtain ⟨cp, hcp, hcf, hcb⟩ := hfr
  refine ⟨?_, st', hst', by rw [hstm, t.p0.strm]; exact o'.inone, hsz0,
    by rw [hms]; exact t.p0.msg, cp, by rw [hpa]; exact hcp, hcf⟩
  refine ⟨b, st', rfl, hst', ?_, by simp [ownL, hsz0, blkOf, hpa, hcp, hms, t.p0.msg]; exact fun e => hcb e.symm⟩
  obtain ⟨c, n, hc, hcs⟩ := hpath
  refine ⟨by rw [hmo]; exact hmode, ⟨c, n, by rw [hpa]; exact hc, ?_⟩, o'.wf.2.2.2.2.1 b st' hst',
    by rw [hwa, t.p0.want, gzbufsize_toNat]; omega, by rw [hwa, t.p0.want, gzbufsize_toNat]; omega, Or.inl hsz0,
    ⟨by rw [hsk]; decide, by rw [hpo, hsk]; decide, by rw [hpo]; decide, fun _ => by rw [hpo]; decide⟩,
    ⟨Or.inl (by rw [hms]; exact t.p0.msg), fun _ => by rw [hms]; exact t.p0.msg⟩,
    fun hr => ⟨Or.inl (hhow (by rw [← hmo]; exact hr)), fun e => absurd hsz0 e, fun _ => hhv,
      fun e => absurd hsk e, fun _ => by
        obtain ⟨z, hz⟩ := o'.wf.2.2.2.2.1 b st' hst'
        have hz' : H'.streams i = some z := by rw [hstm, t.p0.strm] at hz; exact hz
        exact ⟨z, hz, Or.inl (o'.snone z hz').2.1, Or.inl (o'.snone z hz').2.2, hav z hz'⟩,
      fun _ => hhow (by rw [← hmo]; exact hr)⟩,
      fun _ => ⟨fun e => absurd hsz0 e, fun _ => by
          obtain ⟨z, hz⟩ := o'.wf.2.2.2.2.1 b st' hst'
          have hz' : H'.streams i = some z := by rw [hstm, t.p0.strm] at hz; exact hz
          exact ⟨z, hz, hav z hz', Or.inl (o'.snone z hz').2.1, Or.inl (o'.snone z hz').2.2,
            fun _ => (o'.snone z hz').1⟩,
        hhv⟩, fun _ c hc => by
        rw [hbu, t.p0.buffers] at hc
        obtain ⟨z, hz⟩ := o'.wf.2.2.2.2.1 b st' hst'
        have hz' : H'.streams i = some z := by rw [hstm, t.p0.strm] at hz; exact hz
        simp [blkOf, stBlk, hz, (o'.snone z hz').1] at hc⟩
  obtain ⟨r, off, d, e1, e2, e3⟩ := hcs
  exact ⟨r, off, d, e1, by cases e1; show H'.bytes c = some d; rw [hby]; exact e2, e3⟩

theorem Sat.mono' {α : Type} {H : Heap} {m : M α} {P Q : α → Heap → Prop} (hm : Sat H m P)
    (hpq : ∀ a H', P a H' → Q a H') : Sat H m Q := by
  obtain ⟨a, H', e, p⟩ := hm; exact ⟨a, H', e, hpq a H' p⟩

theorem gsat_lseek_oi {w : World} {h : Heap} {b i : Nat} {W : World} {H : Heap} (o : OI w h b i W H)
    (hbl : b < H.nextBlk) (fd : Int32) (off : Int64) (wh : Int32) :
    GSat W H (lseekG fd off wh) (fun _ W' H' => H' = H ∧ OI w h b i W' H' ∧ W'.gzs = W.gzs) :=
  ⟨(W.fs.lseekCall fd off wh).1, { W with fs := (W.fs.lseekCall fd off wh).2 }, H, by simp [lseekG, modifyFs],
    rfl, oi_fs o _ (lseekCall_le _ _ _ _) hbl, rfl⟩

theorem gsat_open_oi {w : World} {h : Heap} {b i : Nat} {W : World} {H : Heap} (o : OI w h b i W H)
    (hbl : b < H.nextBlk) (p : BPtr) (n : Nat) (hp : CStringLen H p n) (fl : Int32) :
    GSat W H (openG p fl) (fun _ W' H' => H' = H ∧ OI w h b i W' H' ∧ W'.gzs = W.gzs) := by
  obtain ⟨bs, ebs, -, -⟩ := strBytes_of hp
  exact ⟨(W.fs.openCall bs fl).1, { W with fs := (W.fs.openCall bs fl).2 }, H, by simp [openG, modifyFs, ebs],
    rfl, oi_fs o _ (openCall_le _ _ _) hbl, rfl⟩

theorem TS.wr {h : Heap} {b i : Nat} {W W' : World} {H : Heap} {st st' : GzState} (t : TS h b i W H st)
    (hst' : W'.gz H b = some st') (hp : P0 i st') : TS h b i W' H st' :=
  ⟨hst', t.hbl, hp⟩

theorem TS.fs {h : Heap} {b i : Nat} {W W' : World} {H : Heap} {st : GzState} (t : TS h b i W H st)
    (e : W'.gzs = W.gzs) : TS h b i W' H st :=
  ⟨by unfold World.gz; rw [e]; exact t.hst, t.hbl, t.p0⟩

theorem tailRead_ok {w : World} {h : Heap} {b i : Nat} {W : World} {H : Heap} {st : GzState}
    (o : OI w h b i W H) (t : TS h b i W H st) (hmode : st.mode = GZ_READ ∨ st.mode = GZ_WRITE)
    (hpath : OwnedStr H st.path) (hfr : ∃ c, st.path = .val (.ref (.heap c) 0) ∧ h.nextBlk ≤ c ∧ c ≠ b) :
    GSat W H (tailRead (some b)) (OpenPost w h) := by
  unfold tailRead
  refine GSat.bind (GSat.of_eq (rdG_app' t.hst _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' t.hst _) ?_)
    refine GSat.bind (GSat.mono (gsat_lseek_oi o t.hbl _ _ _) fun _ W1 H1 q => ?_)
    obtain ⟨rfl, o1, e1⟩ := q
    have t1 := t.fs e1
    refine GSat.bind (GSat.mono (gsat_wrG_oi o1 t1.hst t1.hbl _ rfl) fun _ W2 H2 q => ?_)
    obtain ⟨rfl, hst2, o2⟩ := q
    have t2 := t1.wr hst2 ⟨t.p0.1, t.p0.2, t.p0.3, t.p0.4, t.p0.5, t.p0.6, t.p0.7, t.p0.8, t.p0.9⟩
    refine GSat.bind (GSat.of_eq (rdG_app' t2.hst _) ?_)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.mono (gsat_wrG_oi o2 t2.hst t2.hbl _ rfl) fun _ W3 H3 q => ?_)
      obtain ⟨rfl, hst3, o3⟩ := q
      exact finish_ok o3 (t2.wr hst3 ⟨t.p0.1, t.p0.2, t.p0.3, t.p0.4, t.p0.5, t.p0.6, t.p0.7, t.p0.8, t.p0.9⟩) hmode hpath hfr
    · intro _
      exact finish_ok o2 t2 hmode hpath hfr
  · intro _
    exact finish_ok o t hmode hpath hfr

theorem liftGet_app {v : Ival BPtr} {p : BPtr} (e : v = Ival.val p) (W : World) (H : Heap) :
    (liftM (Ival.get v) : G BPtr) W H = .ok ((p, W), H) := by
  subst e
  simp [Ival.get, liftM, monadLift, MonadLift.monadLift, StateT.lift]

/-- The path, once set: an owned string in a fresh block. -/
structure PathOk (h : Heap) (b : Nat) (H : Heap) (st : GzState) (c np : Nat) : Prop where
  path : st.path = .val (.ref (.heap c) 0)
  str : CStringLen H (.ref (.heap c) 0) np
  fresh : h.nextBlk ≤ c
  ne : c ≠ b

theorem tailFd_ok {w : World} {h : Heap} {b i : Nat} {W : World} {H : Heap} {st : GzState} {c np : Nat}
    (o : OI w h b i W H) (t : TS h b i W H st) (hmode : st.mode = GZ_READ ∨ st.mode = GZ_WRITE ∨ st.mode = GZ_APPEND)
    (pk : PathOk h b H st c np) (sfd : Int32) : GSat W H (tailFd (some b) sfd) (OpenPost w h) := by
  unfold tailFd
  refine GSat.bind (GSat.mono (gsat_wrG_oi o t.hst t.hbl _ rfl) fun _ W1 H1 q => ?_)
  obtain ⟨rfl, hst1, o1⟩ := q
  have t1 := t.wr hst1 ⟨t.p0.1, t.p0.2, t.p0.3, t.p0.4, t.p0.5, t.p0.6, t.p0.7, t.p0.8, t.p0.9⟩
  refine GSat.bind (GSat.of_eq (rdG_app' t1.hst _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.of_eq (ldGz_app t1.hst) ?_)
    refine GSat.bind (GSat.of_eq (liftGet_app pk.path _ _) ?_)
    obtain ⟨r, off, d, e1, e2, -⟩ := pk.str
    cases e1
    refine GSat.bind (GSat.lm (Sat.mono' (sat_free_oi o1 pk.fresh pk.ne e2) fun _ H2 q => ?_))
    obtain ⟨o2, -, hby, -, hnb⟩ := q
    refine GSat.bind (GSat.mono (gsat_free_state o2 (by rw [gz_of_bytes (hby b pk.ne.symm)]; exact t1.hst)
      t1.p0.strm) fun _ W3 H3 q => ?_)
    exact GSat.pure ⟨q.1.post.1, q.1.post.2, fun _ e => by cases e⟩
  · intro _
    refine GSat.bind (GSat.of_eq (rdG_app' t1.hst _) ?_)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.of_eq (rdG_app' t1.hst _) ?_)
      refine GSat.bind (GSat.mono (gsat_lseek_oi o1 t1.hbl _ _ _) fun _ W2 H2 q => ?_)
      obtain ⟨rfl, o2, e2⟩ := q
      have t2 := t1.fs e2
      refine GSat.bind (GSat.mono (gsat_wrG_oi o2 t2.hst t2.hbl _ rfl) fun _ W3 H3 q => ?_)
      obtain ⟨rfl, hst3, o3⟩ := q
      exact tailRead_ok o3 (t2.wr hst3 ⟨t.p0.1, t.p0.2, t.p0.3, t.p0.4, t.p0.5, t.p0.6, t.p0.7, t.p0.8, t.p0.9⟩)
        (Or.inr rfl) ⟨c, np, pk.path, pk.str⟩ ⟨c, pk.path, pk.fresh, pk.ne⟩
    · intro hna
      have hm' : st.mode = GZ_READ ∨ st.mode = GZ_WRITE := by
        rcases hmode with e | e | e
        · exact Or.inl e
        · exact Or.inr e
        · simp [e] at hna
      exact tailRead_ok o1 t1 hm' ⟨c, np, pk.path, pk.str⟩ ⟨c, pk.path, pk.fresh, pk.ne⟩

theorem strlenB_of {H : Heap} {p : BPtr} {n : Nat} (hs : CStringLen H p n) :
    strlenB p H = .ok (UInt64.ofNat n, H) := by
  obtain ⟨bs, e, hb, -⟩ := strBytes_of hs
  simp [strlenB, e, hb]

theorem tailPath_ok {w : World} {h : Heap} {b i : Nat} {W : World} {H : Heap} {st : GzState} {np : Nat}
    (o : OI w h b i W H) (t : TS h b i W H st) (hmode : st.mode = GZ_READ ∨ st.mode = GZ_WRITE ∨ st.mode = GZ_APPEND)
    {path : BPtr} (hp : CStringLen H path np) (fd cl ex : Int32) :
    GSat W H (tailPath path fd cl ex (some b)) (OpenPost w h) := by
  have hnp : np + 1 < 2 ^ 63 := by
    obtain ⟨r, off, d, -, hd, hn, -⟩ := hp
    have := o.wf.2.2.1 r d hd; omega
  have hlen : (UInt64.ofNat np + 1).toNat = np + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  unfold tailPath
  refine GSat.bind (GSat.lm ⟨_, H, strlenB_of hp, ?_⟩)
  dsimp only
  rw [hlen]
  refine GSat.bind (GSat.lm (Sat.mono' (sat_alloc_oi o (np + 1) hnp) fun p H1 q => ?_))
  obtain ⟨o1, hn1, hby1, hstr1, hp1⟩ := q
  have t1 : TS h b i W H1 st := ⟨by rw [gz_of_bytes (hby1 b t.hbl)]; exact t.hst, by have := t.hbl; omega, t.p0⟩
  refine GSat.bind (GSat.mono (gsat_wrG_oi o1 t1.hst t1.hbl _ rfl) fun _ W2 H2 q => ?_)
  obtain ⟨rfl, hst2, o2⟩ := q
  have t2 := t1.wr hst2 ⟨t.p0.1, t.p0.2, t.p0.3, t.p0.4, t.p0.5, t.p0.6, t.p0.7, t.p0.8, t.p0.9⟩
  refine GSat.bind (GSat.of_eq (ldGz_app t2.hst) ?_)
  refine GSat.bind (GSat.of_eq (liftGet_app rfl _ _) ?_)
  apply GSat.ite
  · intro _
    refine GSat.bind (GSat.mono (gsat_free_state o2 t2.hst t2.p0.strm) fun _ W3 H3 q => ?_)
    exact GSat.pure ⟨q.1.post.1, q.1.post.2, fun _ e => by cases e⟩
  · intro hpn
    rcases hp1 with e | ⟨rfl, d, hd, hds, hnb, -⟩
    · subst e; simp at hpn
    refine GSat.bind (GSat.of_eq (ldGz_app t2.hst) ?_)
    refine GSat.bind (GSat.of_eq (liftGet_app rfl _ _) ?_)
    have hb2 : ∀ (r : BRef) (d' : Array UInt8), Space.get H r = some d' → Space.get H2 r = some d' := by
      intro r d' hd'
      cases r with
      | heap c =>
        have hc : c < H.nextBlk := by
          refine Nat.lt_of_not_le fun hc => ?_
          have := (o.wf.2.1.1 c hc).2.2
          have hd'' : H.bytes c = some d' := hd'
          rw [this] at hd''; cases hd''
        show H2.bytes c = some d'
        rw [hby1 c hc]; exact hd'
      | const c =>
        show H2.consts c = some d'
        rw [o2.same.consts, ← o.same.consts]; exact hd'
      | str k => exact hd'
    have hsz : UInt64.ofNat np + 1 = UInt64.ofNat (np + 1) := by
      apply UInt64.toNat_inj.mp; rw [hlen, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hnp (by decide))]
    rw [hsz]
    refine GSat.bind (GSat.lm (Sat.mono' (sat_snprintf_path o2 (by have := o.next; omega) hd
      (cstr_of_get hb2 hp) hds (Nat.lt_trans hnp (by decide))) fun _ H3 q => ?_))
    obtain ⟨o3, hcs3, hby3, -, hnb3, -⟩ := q
    have hbH : b < H.nextBlk := t.hbl
    have hS2 : W2.gz H2 b = some { st with path := .val (.ref (.heap H.nextBlk) 0) } := hst2
    generalize hS : ({ st with path := .val (.ref (.heap H.nextBlk) 0) } : GzState) = S at hS2 t2
    have t3 : TS h b i W2 H3 S := ⟨by rw [gz_of_bytes (hby3 b (by omega))]; exact hS2,
      by rw [hnb3]; exact t2.hbl, t2.p0⟩
    have pk : PathOk h b H3 S H.nextBlk np := ⟨by rw [← hS], hcs3, by have := o.next; omega, by omega⟩
    have hmode : S.mode = GZ_READ ∨ S.mode = GZ_WRITE ∨ S.mode = GZ_APPEND := by rw [← hS]; exact hmode
    refine GSat.bind (GSat.of_eq (rdG_app' t3.hst _) ?_)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.pure ?_)
      exact tailFd_ok o3 t3 hmode pk fd
    · intro _
      refine GSat.bind (GSat.mono (gsat_open_oi o3 t3.hbl path np (cstr_of_get (fun r d' e => ?_) hp) _)
        fun sfd W4 H4 q => ?_)
      · cases r with
        | heap c =>
          have hc : c < H.nextBlk := by
            refine Nat.lt_of_not_le fun hc => ?_
            have := (o.wf.2.1.1 c hc).2.2
            have e' : H.bytes c = some d' := e
            rw [this] at e'; cases e'
          show H3.bytes c = some d'
          rw [hby3 c (by omega), hby1 c hc]; exact e
        | const c =>
          show H3.consts c = some d'
          rw [o3.same.consts, ← o.same.consts]; exact e
        | str k => exact e
      · obtain ⟨rfl, o4, e4⟩ := q
        exact tailFd_ok o4 (t3.fs e4) hmode pk sfd

set_option maxHeartbeats 4000000 in
theorem gz_open_spec {w : World} {h : Heap} (hwf : GzWF w h) (path mode : BPtr) (fd : Int32)
    (hp : path = .null ∨ CStr h path) (hm : mode = .null ∨ CStr h mode) :
    GSat w h (gz_open path fd mode) (OpenPost w h) := by
  unfold gz_open
  simp only []
  by_cases hnull : (path == .null || mode == .null) = true
  · simp only [hnull, ite_true]
    exact GSat.pure (post_refl hwf h.nalloc)
  · simp only [hnull, Bool.false_eq_true, ite_false]
    have hp' : CStr h path := by
      rcases hp with e | e
      · subst e; simp at hnull
      · exact e
    have hm' : CStr h mode := by
      rcases hm with e | e
      · subst e; simp at hnull
      · exact e
    obtain ⟨n, r0, off0, data, rfl, hd0, hn, hz, hnz⟩ := hm'
    refine GSat.bind (GSat.mono (state_init_spec hwf) fun r W1 H1 q => ?_)
    rcases q with ⟨rfl, rfl, rfl⟩ | ⟨rfl, o1, hn1, st1, hst1, p01, hmo1, -⟩
    · exact GSat.pure (post_refl hwf _)
    · simp only [show (some h.nextBlk == none) = false from rfl, Bool.false_eq_true, ite_false]
      refine GSat.bind (GSat.mono (gsat_gwhile (LI w h h.nextBlk h.streams.arr.size r0 off0 n) (LM off0 n)
        (fun s W H => LI w h h.nextBlk h.streams.arr.size r0 off0 n s W H ∧
          (s.ctl = .go → s.mode = .ref r0 (off0 + n))) ?step ?init ?mu) fun lp W2 H2 hq => ?rest)
      case init =>
        exact ⟨o1, by omega, ⟨0, by simp, by omega⟩, Or.inl ⟨rfl, st1, hst1, p01, Or.inl hmo1⟩⟩
      case mu =>
        have := hwf.2.2.1 r0 data hd0
        simp [LM, fuel]; omega
      case step =>
        intro s W H hli
        obtain ⟨o, hbl, ⟨k, hmk, hkn⟩, hctl⟩ := hli
        have hdH : Space.get H r0 = some data := o.get_old r0 data hd0
        rcases hctl with ⟨hc, st, hst, p0, hms⟩ | ⟨hc, hret⟩
        · have hcne : (s.ctl != Ctl.go) = false := by simp [hc]
          simp only [hcne, Bool.false_eq_true, ite_false]
          refine GSat.bind (GSat.lm ⟨_, H, by rw [hmk]; exact load8_ok hdH (by omega), ?_⟩)
          refine GSat.pure ⟨fun ht => ?_, fun hf => ?_⟩
          · have hk : k < n := by
              refine Nat.lt_of_le_of_ne hkn fun e => ?_
              subst e; simp [hz] at ht
            simp only
            refine GSat.bind (GSat.lm ⟨_, H, by rw [hmk]; exact load8_ok hdH (by omega), ?_⟩)
            simp only []
            repeat' (apply GSat.ite <;> intro _)
            all_goals first
              | leafA
              | (exact jp_ok o hbl hdH hn hmk hk hc ⟨st, hst, p0, hms⟩ _ _)
              | (refine GSat.bind (GSat.lm ⟨_, H, by rw [hmk]; exact load8_ok hdH (by omega), ?_⟩)
                 leafA)
              | (refine GSat.bind (GSat.mono (gsat_free_state o hst p0.strm) fun _ W' H' q => ?_)
                 obtain ⟨o', hgz, hbn, hsn, -, hnb, -⟩ := q
                 refine GSat.pure ⟨⟨o', by rw [hnb]; exact hbl, ⟨k, hmk, hkn⟩, Or.inr ⟨rfl, hgz, hbn, hsn⟩⟩, ?_⟩
                 simp [LM, hmk, hc]; omega)
          · refine ⟨⟨o, hbl, ⟨k, hmk, hkn⟩, Or.inl ⟨hc, st, hst, p0, hms⟩⟩, fun _ => ?_⟩
            have : k = n := by
              refine Nat.le_antisymm hkn (Nat.not_lt.mp fun hk => ?_)
              have := hnz k hk; simp at hf; exact this hf
            simp only; rw [hmk, this]
        · have hcne : (s.ctl != Ctl.go) = true := by simp [hc]
          simp only [hcne, ite_true]
          exact GSat.pure ⟨fun e => by simp at e, fun _ =>
            ⟨⟨o, hbl, ⟨k, hmk, hkn⟩, Or.inr ⟨hc, hret⟩⟩, fun e => by rw [hc] at e; cases e⟩⟩
      case rest =>
      obtain ⟨⟨o, hbl, -, hctl⟩, -⟩ := hq
      obtain ⟨np, hpn⟩ := hp'
      have hpH : CStringLen H2 path np := cstr_of_get (fun r d e => o.get_old r d e) hpn
      rcases hctl with ⟨hc, st, hst, p0, hms⟩ | ⟨hc, hgz, -, -⟩
      · have hcr : (lp.ctl == Ctl.ret) = false := by simp [hc]
        simp only [hcr, Bool.false_eq_true, ite_false]
        have t : TS h h.nextBlk h.streams.arr.size W2 H2 st := ⟨hst, hbl, p0⟩
        have fin : GSat W2 H2 (gz_state_free (some h.nextBlk) >>= fun _ => pure none) (OpenPost w h) :=
          GSat.bind (GSat.mono (gsat_free_state o hst p0.strm) fun _ W3 H3 q =>
            GSat.pure ⟨q.1.post.1, q.1.post.2, fun _ e => by cases e⟩)
        refine GSat.bind (GSat.of_eq (rdG_app' hst _) ?_)
        apply GSat.ite
        · intro _; exact fin
        · intro hnn
          refine GSat.bind (GSat.of_eq (rdG_app' hst _) ?_)
          apply GSat.ite
          · intro hr
            have hr' : st.mode = GZ_READ := by simpa using hr
            refine GSat.bind (GSat.of_eq (rdG_app' hst _) ?_)
            apply GSat.ite
            · intro _; exact fin
            · intro _
              refine GSat.bind (GSat.of_eq (rdG_app' hst _) ?_)
              apply GSat.ite
              · intro _
                refine GSat.bind (GSat.mono (gsat_wrG_oi o hst hbl _ rfl) fun _ W3 H3 q => ?_)
                obtain ⟨rfl, hst3, o3⟩ := q
                exact tailPath_ok o3 (t.wr hst3 ⟨p0.1, p0.2, p0.3, p0.4, p0.5, p0.6, p0.7, p0.8, p0.9⟩) (Or.inl hr')
                  hpH fd lp.cloexec lp.exclusive
              · intro _
                exact tailPath_ok o t (Or.inl hr') hpH fd lp.cloexec lp.exclusive
          · intro hnr
            have hm2 : st.mode = GZ_READ ∨ st.mode = GZ_WRITE ∨ st.mode = GZ_APPEND := by
              rcases hms with e | e | e | e
              · simp [e] at hnn
              · simp [e] at hnr
              · exact Or.inr (Or.inl e)
              · exact Or.inr (Or.inr e)
            refine GSat.bind (GSat.of_eq (rdG_app' hst _) ?_)
            apply GSat.ite
            · intro _; exact fin
            · intro _
              exact tailPath_ok o t hm2 hpH fd lp.cloexec lp.exclusive
      · have hcr : (lp.ctl == Ctl.ret) = true := by simp [hc]
        simp only [hcr, ite_true]
        exact GSat.pure ⟨o.post.1, o.post.2, fun _ e => by cases e⟩

/-- The frame `GzFrame w h w' h' none []` that the goals of `gzopen` / `gzopen64` / `gzdopen` first stated fails
on every successful open: the new file's embedded stream is a live entry of `Heap.streams` that was not live
before, and `GzFrame` with no file leaves every stream entry as it was. -/
theorem open_frame_fails {w : World} {h : Heap} {f : GzPtr} {W : World} {H : Heap}
    (hp : OpenPost w h f W H) (hf : f ≠ none) : ¬ GzFrame w h W H none [] := by
  intro hfr
  obtain ⟨b, rfl⟩ : ∃ b, f = some b := by cases f with | none => exact absurd rfl hf | some b => exact ⟨b, rfl⟩
  obtain ⟨⟨b0, s, e0, hs, sh, -⟩, s', hs', hnone, -⟩ := hp.2.2 b rfl
  cases e0
  rw [hs] at hs'; cases hs'
  obtain ⟨z, hz⟩ := sh.strm
  have e := hfr.1.1.1 s.strm (by simp)
  simp only at e
  rw [hz, hnone] at e; cases e

end ZlibNgF.Proof.GzOpen
