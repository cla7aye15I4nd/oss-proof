import ZlibNgF.Proof.«deflate_stored.c.trip»

/-!
# The window update of `deflate_stored` (`ZlibNgF`)

`uw_ok`: the window update after the copy loop (`stored_update_window`, `deflate_stored.c:107-130`) keeps `SF` and no
pending bytes. When the loop copied `used` input bytes straight to the output, they are the `used` bytes before
`next_in` in the caller's input object (`InTail` from the entry): the window takes the last `w_size` of them
(`next_in - w_size`, inside the object since `used >= w_size`), or slides down (`strstart > window_size - used >=
w_size`) and appends them (`next_in - used` is the entry `next_in`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.StoredWin
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateFlush ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.StoredIO ZlibNgF.Proof.StoredF ZlibNgF.Proof.StoredTrip
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size copyFold_get)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.WinInv (InTail)
open ZlibNg.DeflateStored

/-- `SF` after a change of `strstart`, `insert`, `block_start`, `high_water` and the bytes of the block (same size). -/
theorem sf_state {h H : Heap} {i b wo : Nat} {z : ZStream} {st st' : DeflateState} {d d' : Array UInt8}
    {ob oo pbo : Nat} {X : Array UInt8} (F : SF h i b H) (S : SFX H i b wo z st d ob oo X pbo)
    (he : st' = { st with
      strstart := st'.strstart
      insert := st'.insert
      block_start := st'.block_start
      high_water := st'.high_water
      bi_used := st'.bi_used })
    (hss : st'.strstart.toNat ≤ st.window_size.toNat) (hb0 : 0 ≤ st'.block_start.toInt)
    (hbs : st'.block_start.toInt ≤ st'.strstart.toNat) (hins : st'.insert.toNat ≤ st'.strstart.toNat)
    (hd : d'.size = d.size) :
    SF h i b (SH (setB H ob X) i z b st' d') := by
  obtain ⟨st0, h0, -, la0, hk⟩ := F.keeps
  have hla : st.lookahead = 0 := (hk st S.hst).2.2.2.trans la0
  have hsy : (dview st').sym_next = 0 := by show st'.sym_next = 0; rw [he]; exact S.sym
  have hws := S.ws.1
  refine sf_next F S.hz S.hst S.hno S.hX (L := 0) rfl (fun _ _ => rfl) (Nat.zero_le _) rfl (Or.inl ⟨rfl, rfl⟩)
    (Nat.le_refl _) (by rw [S.hno]; rfl) (by simp) (fun al _ c => dcore_mv ?_ S.hd (SH_bytes _ _ _ _ _ _) hd hsy rfl rfl)
    ?_ ?_
  · rw [he]
    exact dcore_set c st'.strstart st.lookahead st'.insert st'.block_start (by simp only [dview, hla]; simpa using hss)
      hbs (UInt32.le_iff_toNat_le.mpr hins) (by omega)
  · rw [he]; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩, rfl, rfl, rfl⟩
  · refine ⟨Int32.le_iff_toInt_le.mpr (by rw [show (0 : Int32).toInt = 0 from rfl]; exact hb0), ?_, ?_⟩
    · rw [he]; exact S.sym
    · rw [he]; exact S.b8

/-- A pointer moved back by `k` bytes within its object. -/
theorem add_back {H0 : Heap} {r : BRef} {src : Array UInt8} {off k : Nat} (hg : Space.get H0 r = some src)
    (h1 : off ≤ src.size) (h2 : k ≤ off) :
    Ptr.add (Ptr.ref r off) (-(k : Int)) H0 = .ok (.ref r (off - k), H0) := by
  simp only [Ptr.add, hg]
  rw [ite_t ⟨h1, by omega, by omega⟩]
  congr 3; omega

theorem get_SHB {H : Heap} {i : Nat} {z : ZStream} {b ob : Nat} {st : DeflateState} {d X : Array UInt8} {r : BRef}
    {src : Array UInt8} (hX : H.bytes ob = some X) (hr : r ≠ .heap b) (hg : Space.get H r = some src) :
    Space.get (SH (setB H ob X) i z b st d) r = some src := by
  rw [ZlibNgF.Proof.ReadBuf.get_SH_ne hr, setB_self hX]; exact hg

/-- The window update after the copy loop keeps `SF`, no pending bytes, and the stream record. -/
theorem uw_ok {h H : Heap} {i b wo : Nat} (F : SF h i b H) (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (last : Int32)
    {z0 : ZStream} {st0 : DeflateState} (h0 : h.streams i = some z0) (hs0 : h.dstate b = some st0) :
    Sat H (stored_update_window (some b) (.ref (.heap b) wo) st0.w_size z0.avail_in last) (fun _ H' =>
      SF h i b H' ∧ (∀ st, H'.dstate b = some st → st.pending = 0) ∧ avIn H' i = avIn H i ∧
        avOut H' i = avOut H i) := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by
    rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  have hav : avOut H i = z.avail_out.toNat := by simp [avOut, S.hz]
  have hai : avIn H i = z.avail_in.toNat := by simp [avIn, S.hz]
  rw [hav, hai]
  have hp := hp0 st S.hst
  obtain ⟨st1, h1, -, -, hk⟩ := F.keeps
  obtain rfl : st0 = st1 := Option.some.inj (hs0.symm.trans h1)
  have hwz : st.w_size = st0.w_size := (hk st S.hst).2.2.1
  obtain ⟨z1, z2, hz1, hz2, hle, ht⟩ := F.inp
  obtain rfl : z0 = z1 := Option.some.inj (h0.symm.trans hz1)
  obtain rfl : z = z2 := Option.some.inj (S.hz.symm.trans hz2)
  obtain ⟨hws, hw2, hw512, hw32⟩ := S.ws
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  obtain ⟨hl1, hl2⟩ := S.lay
  have hins := S.ins
  -- the final step: any `strstart` / `insert` / `block_start = strstart` / `high_water`
  have fin : ∀ (ss ins : UInt32) (d1 : Array UInt8), ss.toNat ≤ st.window_size.toNat → ins.toNat ≤ ss.toNat →
      d1.size = d.size →
      Sat (SH (setB H ob X) i z b { st with strstart := ss, insert := ins } d1) (do
        wrD (some b) fun s => { s with block_start := s.strstart.toInt32 }
        wrD (some b) fun s => { s with high_water := MAX32 s.high_water s.strstart }) (fun _ H' =>
          SF h i b H' ∧ (∀ st, H'.dstate b = some st → st.pending = 0) ∧ avIn H' i = z.avail_in.toNat ∧
            avOut H' i = z.avail_out.toNat) := by
    intro ss ins d1 h1 h2 h3
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    refine Sat.of_eq (wrD_SH _) ⟨sf_state F S rfl h1 ?_ ?_ h2 h3, fun st2 h4 => ?_, by simp [avIn], by simp [avOut]⟩
    · show 0 ≤ ss.toInt32.toInt; rw [DeflateAlloc.u32_toInt32_toInt _ (by omega)]; omega
    · show ss.toInt32.toInt ≤ ss.toNat; rw [DeflateAlloc.u32_toInt32_toInt _ (by omega)]; omega
    · rw [SH_dstate] at h4; cases h4; exact hp
  rw [← e0]
  unfold stored_update_window
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  have hu : (z0.avail_in - z.avail_in).toNat = z0.avail_in.toNat - z.avail_in.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hle)
  generalize z0.avail_in - z.avail_in = used at hu ⊢
  by_cases hc : (used != 0 && last == 0) = true
  rotate_left
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    refine Sat.of_eq (wrD_SH _) ⟨sf_state F S rfl (by omega) (by omega) (by omega) (by omega) rfl, fun st2 h4 => ?_,
      by simp [avIn], by simp [avOut]⟩
    rw [SH_dstate] at h4; cases h4; exact hp
  simp only [hc, ↓reduceIte]
  have hu0 : used.toNat ≠ 0 := by
    intro e; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    exact hc.1 (UInt32.toNat_inj.mp (by rw [e]; rfl))
  obtain ⟨r, os0, e1, e2⟩ : ∃ r os0, z0.next_in = .ref r os0 ∧
      z.next_in = .ref r (os0 + (z0.avail_in.toNat - z.avail_in.toNat)) := by
    rcases ht with ⟨-, e⟩ | ⟨r, os0, e1, e2⟩
    · rw [e] at hu; omega
    · exact ⟨r, os0, e1, e2⟩
  rw [← hu] at e2
  obtain ⟨r', os', src, e3, hg, hin⟩ := S.inr.resolve_left (by rw [e2]; simp)
  rw [e2] at e3; injection e3 with e4 e5; subst e4; subst e5
  have hr : r ≠ .heap b := fun e => S.inb (os0 + used.toNat) (by rw [e2, e])
  rw [← hwz]
  by_cases hge : used ≥ st.w_size
  · have hge' := UInt32.le_iff_toNat_le.mp hge
    simp only [hge, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
    refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
    rw [e2]
    refine Sat.bind (Sat.of_eq (add_back (get_SHB S.hX hr hg) (by omega) (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.ReadBuf.memcpy_SH hr (by rw [setB_self S.hX]; exact hg)
      (by omega) (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    exact fin st.w_size st.w_size _ (by omega) (Nat.le_refl _) (copyFold_size _ _ _ _ _)
  have hlt : used.toNat < st.w_size.toNat := by
    have := UInt32.not_le.mp hge; exact UInt32.lt_iff_toNat_lt.mp this
  simp only [hge, ↓reduceIte]
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  have tail : ∀ (ss ins : UInt32) (d1 : Array UInt8), ss.toNat + used.toNat < st.window_size.toNat →
      ins.toNat ≤ ss.toNat → d1.size = d.size →
      Sat (SH (setB H ob X) i z b { st with strstart := ss, insert := ins } d1) (do
        let ss ← rdD (some b) (·.strstart)
        let strm ← strmOf (some b)
        Ptr.memcpy (← (Ptr.ref (.heap b) wo).add ss.toNat) (← (← rdZ strm (·.next_in)).add (-(used.toNat : Int)))
          used.toNat
        wrD (some b) fun s => { s with strstart := s.strstart + used }
        wrD (some b) fun s => { s with insert := s.insert + MIN32 used (st.w_size - s.insert) }
        wrD (some b) fun s => { s with block_start := s.strstart.toInt32 }
        wrD (some b) fun s => { s with high_water := MAX32 s.high_water s.strstart }) (fun _ H' =>
          SF h i b H' ∧ (∀ st, H'.dstate b = some st → st.pending = 0) ∧ avIn H' i = z.avail_in.toNat ∧
            avOut H' i = z.avail_out.toNat) := by
    intro ss ins d1 h1 h2 h3
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
    refine Sat.bind (Sat.of_eq (add_SH ss.toNat (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
    simp only [e2]
    refine Sat.bind (Sat.of_eq (add_back (get_SHB S.hX hr hg) (by omega) (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.ReadBuf.memcpy_SH hr (by rw [setB_self S.hX]; exact hg)
      (by omega) (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    have hm := min32_toNat used (st.w_size - ins)
    have hs1 : (ss + used).toNat = ss.toNat + used.toNat := by rw [UInt32.toNat_add]; omega
    have hs2 : (ins + MIN32 used (st.w_size - ins)).toNat ≤ ins.toNat + used.toNat := by
      rw [UInt32.toNat_add]; omega
    exact fin (ss + used) (ins + MIN32 used (st.w_size - ins)) _ (by omega) (by omega) (by rw [copyFold_size, h3])
  have hd0 : (st.window_size - st.strstart).toNat = st.window_size.toNat - st.strstart.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hss)
  by_cases hsl : st.window_size - st.strstart ≤ used
  · have hsl' := UInt32.le_iff_toNat_le.mp hsl
    simp only [hsl, ↓reduceIte]
    have hsw : (st.strstart - st.w_size).toNat = st.strstart.toNat - st.w_size.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    refine Sat.bind (Sat.of_eq (add_SH (st.strstart - st.w_size).toNat (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    refine Sat.bind (Sat.of_eq (memmove_SH (od := wo) (os := wo + (st.strstart - st.w_size).toNat)
      (n := st.w_size.toNat) (by omega) (by omega)) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    have hm := min32_toNat st.insert st.w_size
    exact tail st.w_size (MIN32 st.insert st.w_size) _ (by omega) (by omega) (copyFold_size _ _ _ _ _)
  · have hsl' : ¬ (st.window_size.toNat - st.strstart.toNat ≤ used.toNat) := fun e =>
      hsl (UInt32.le_iff_toNat_le.mpr (by omega))
    simp only [hsl, ↓reduceIte]
    exact tail st.strstart st.insert d (by omega) hins rfl

section parts
open ZlibNg.DeflateP

/-- The filling of the window from the input (`deflate_stored.c:143-161`), followed by `k`. -/
def fill_part {α : Type} (st : StatePtr) (window : BPtr) (w_size : UInt32) (k : M α) : M α := do
  let s ← ldDState st
  let have_ : UInt32 := s.window_size - s.strstart
  let c : Bool ← if (← rdZ (← strmOf st) (·.avail_in)) > have_ then do
      pure ((← rdD st (·.block_start)) ≥ w_size.toInt32)
    else pure false
  let have_ ← if c then do
      let s ← ldDState st
      let slide_len : UInt32 := MIN32 s.block_start.toUInt32 (s.strstart - w_size)
      let bs ← chkI32 (s.block_start.toInt - slide_len.toInt32.toInt)
      wrD st fun s => { s with block_start := bs }
      wrD st fun s => { s with strstart := s.strstart - slide_len }
      Ptr.memmove window (← window.add slide_len.toNat) (← rdD st (·.strstart)).toNat
      let have_ := have_ + slide_len
      wrD st fun s => { s with insert := MIN32 s.insert s.strstart }
      pure have_
    else pure have_
  let have_ := MIN32 have_ (← rdZ (← strmOf st) (·.avail_in))
  if have_ != 0 then
    let strm ← strmOf st
    let _ ← read_buf strm (← window.add (← rdD st (·.strstart)).toNat) have_
    wrD st fun s => { s with strstart := s.strstart + have_ }
    wrD st fun s => { s with insert := s.insert + MIN32 have_ (w_size - s.insert) }
  wrD st fun s => { s with high_water := MAX32 s.high_water s.strstart }
  k

end parts

/-- The tail of the filling: `read_buf` of `min(have, avail_in)` input bytes into the window at `strstart`, and
`high_water`. -/
theorem fill_tail {h H : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {ob oo pbo : Nat}
    {X : Array UInt8} (F : SF h i b H) (S : SFX H i b wo z st d ob oo X pbo) (hp : st.pending = 0)
    {α : Type} (k : M α) (Q : α → Heap → Prop)
    (hk : ∀ H', SF h i b H' → (∀ st, H'.dstate b = some st → st.pending = 0) → Sat H' k Q)
    (hv ss ins : UInt32) (bs : Int32) (d1 : Array UInt8) :
    hv.toNat = st.window_size.toNat - ss.toNat →
      ss.toNat ≤ st.window_size.toNat → 0 ≤ bs.toInt → bs.toInt ≤ ss.toNat → ins.toNat ≤ ss.toNat →
      d1.size = d.size →
      Sat (SH (setB H ob X) i z b { st with strstart := ss, block_start := bs, insert := ins } d1) (do
        let have_ := MIN32 hv (← rdZ (← strmOf (some b)) (·.avail_in))
        if have_ != 0 then
          let strm ← strmOf (some b)
          let _ ← ZlibNg.DeflateP.read_buf strm (← (Ptr.ref (.heap b) wo).add (← rdD (some b) (·.strstart)).toNat)
            have_
          wrD (some b) fun s => { s with strstart := s.strstart + have_ }
          wrD (some b) fun s => { s with insert := s.insert + MIN32 have_ (st.w_size - s.insert) }
        wrD (some b) fun s => { s with high_water := MAX32 s.high_water s.strstart }
        k) Q := by
  obtain ⟨hws, hw2, hw512, hw32⟩ := S.ws
  obtain ⟨hl1, hl2⟩ := S.lay
  revert hv ss ins bs d1
  intro hv ss ins bs d1 h1 h2 h3 h4 h5 h6
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  have hm := min32_toNat hv z.avail_in
  generalize MIN32 hv z.avail_in = n at hm ⊢
  have fin : ∀ (z' : ZStream) (ss' ins' : UInt32) (d2 : Array UInt8), z' = { z with
        next_in := z'.next_in
        avail_in := z'.avail_in
        total_in := z'.total_in
        adler := z'.adler
        next_out := z'.next_out
        avail_out := z'.avail_out
        total_out := z'.total_out } → InTail z z' → z'.avail_in.toNat ≤ z.avail_in.toNat →
      z'.next_out = z.next_out → z'.avail_out = z.avail_out →
      ss'.toNat ≤ st.window_size.toNat → bs.toInt ≤ ss'.toNat → ins'.toNat ≤ ss'.toNat → d2.size = d.size →
      Sat (SH (setB H ob X) i z' b { st with strstart := ss', block_start := bs, insert := ins' } d2) (do
        wrD (some b) fun s => { s with high_water := MAX32 s.high_water s.strstart }
        k) Q := by
    intro z' ss' ins' d2 e1 e2 e3 e4 e5 e6 e7 e8 e9
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    have hws' := hws
    obtain ⟨st2, h0', -, la0, hk2⟩ := F.keeps
    have hla : st.lookahead = 0 := (hk2 st S.hst).2.2.2.trans la0
    refine hk _ (sf_next F S.hz S.hst S.hno S.hX (L := 0) rfl (fun _ _ => rfl) (Nat.zero_le _) e1 e2 e3
      (by rw [e4, S.hno]; rfl) (by rw [e5]; simp) (fun al _ c => dcore_mv (z := z) ?_ S.hd (SH_bytes _ _ _ _ _ _) e9 (by exact S.sym)
        (by rw [e1]) (by rw [e1])) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩, rfl, rfl, rfl⟩
      ⟨Int32.le_iff_toInt_le.mpr (by rw [show (0 : Int32).toInt = 0 from rfl]; exact h3), S.sym, S.b8⟩) ?_
    · exact dcore_set c ss' st.lookahead ins' bs (by simp only [dview, hla]; simpa using e6) e7
        (UInt32.le_iff_toNat_le.mpr e8) (by omega)
    · intro st3 h7; rw [SH_dstate] at h7; cases h7; exact hp
  by_cases hn0 : n = 0
  · subst hn0
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact fin z ss ins d1 rfl (Or.inl ⟨rfl, rfl⟩) (Nat.le_refl _) rfl rfl h2 h4 h5 h6
  have hn0' : (n != 0) = true := by simpa using hn0
  have hn1 : n.toNat ≠ 0 := fun e => hn0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
  simp only [hn0', ↓reduceIte]
  have hni0 : z.next_in ≠ .null := S.inset (fun e => by rw [e] at hm; simp at hm; omega)
  obtain ⟨r, os, src, hni, hg, hin⟩ := S.inr.resolve_left hni0
  have hr : r ≠ .heap b := fun e => S.inb os (by rw [hni, e])
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (add_SH ss.toNat (by omega)) ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.ReadBuf.read_buf_SH (H := setB H ob X) (i := i)
    (st := { st with strstart := ss, block_start := bs, insert := ins }) (d := d1) (off := wo + ss.toNat) S.hb hni hr (by rw [setB_self S.hX]; exact hg) hin
    (fun _ => F.crc.1) n (by omega)) ?_)
  rintro m H2 ⟨hm1, hm2, -, d2, a, rfl, w2⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hm3 := min32_toNat n (st.w_size - ins)
  have hs1 : (ss + n).toNat = ss.toNat + n.toNat := by rw [UInt32.toNat_add]; omega
  have hs2 : (ins + MIN32 n (st.w_size - ins)).toNat ≤ ins.toNat + n.toNat := by
    rw [UInt32.toNat_add]; omega
  have hsub : (z.avail_in - m).toNat = z.avail_in.toNat - m.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  exact fin _ (ss + n) (ins + MIN32 n (st.w_size - ins)) d2 rfl
    (Or.inr ⟨r, os, hni, by simp only [ZlibNgF.Proof.ReadBuf.RBZ]; rw [hsub]; congr 2; omega⟩)
    (by simp only [ZlibNgF.Proof.ReadBuf.RBZ]; omega) rfl rfl (by omega) (by omega) (by omega) (by rw [w2.1, h6])

/-- The filling of the window keeps `SF` and no pending bytes. -/
theorem fill_ok {h H : Heap} {i b wo : Nat} (F : SF h i b H) (hp0 : ∀ st, H.dstate b = some st → st.pending = 0)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) {st0 : DeflateState}
    (hs0 : h.dstate b = some st0) {α : Type} (k : M α) (Q : α → Heap → Prop)
    (hk : ∀ H', SF h i b H' → (∀ st, H'.dstate b = some st → st.pending = 0) → Sat H' k Q) :
    Sat H (fill_part (some b) (.ref (.heap b) wo) st0.w_size k) Q := by
  obtain ⟨z, st, d, ob, oo, X, pbo, S⟩ := F.facts hw0
  have e0 : SH (setB H ob X) i z b st d = H := by
    rw [setB_self S.hX]; exact ZlibNgF.Proof.DeflateReset.SH_self S.hz S.hsts S.hd
  have hp := hp0 st S.hst
  obtain ⟨st1, h1, -, -, hk1⟩ := F.keeps
  obtain rfl : st0 = st1 := Option.some.inj (hs0.symm.trans h1)
  have hwz : st.w_size = st0.w_size := (hk1 st S.hst).2.2.1
  obtain ⟨hws, hw2, hw512, hw32⟩ := S.ws
  obtain ⟨hb0, hbs, hss⟩ := S.bs
  obtain ⟨hl1, hl2⟩ := S.lay
  have hins := S.ins
  rw [← e0, ← hwz]
  have hd0 : (st.window_size - st.strstart).toNat = st.window_size.toNat - st.strstart.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hss)
  have hwi : st.w_size.toInt32.toInt = st.w_size.toNat := DeflateAlloc.u32_toInt32_toInt _ (by omega)
  unfold fill_part
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine Sat.bind (Sat.of_eq (strmOf_SH S.strm) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  have noslide : Sat (SH (setB H ob X) i z b st d) (do
      let have_ := MIN32 (st.window_size - st.strstart) (← rdZ (← strmOf (some b)) (·.avail_in))
      if have_ != 0 then
        let strm ← strmOf (some b)
        let _ ← ZlibNg.DeflateP.read_buf strm (← (Ptr.ref (.heap b) wo).add (← rdD (some b) (·.strstart)).toNat)
          have_
        wrD (some b) fun s => { s with strstart := s.strstart + have_ }
        wrD (some b) fun s => { s with insert := s.insert + MIN32 have_ (st.w_size - s.insert) }
      wrD (some b) fun s => { s with high_water := MAX32 s.high_water s.strstart }
      k) Q :=
    fill_tail F S hp k Q hk _ st.strstart st.insert st.block_start d hd0 hss hb0 hbs hins rfl
  by_cases hgt : z.avail_in > st.window_size - st.strstart
  · simp only [hgt, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    by_cases hge : st.block_start ≥ st.w_size.toInt32
    · simp only [hge, decide_true]
      refine Sat.bind (Sat.pure ?_)
      simp only [↓reduceIte]
      have hge' : (st.w_size.toNat : Int) ≤ st.block_start.toInt := by
        have := Int32.le_iff_toInt_le.mp hge; omega
      refine Sat.bind (Sat.of_eq ldDState_SH ?_)
      have hbu : st.block_start.toUInt32.toNat = st.block_start.toInt.toNat :=
        Int32.toNat_toUInt32_of_le (Int32.le_iff_toInt_le.mpr (by show (0 : Int) ≤ _; omega))
      have hsw : (st.strstart - st.w_size).toNat = st.strstart.toNat - st.w_size.toNat :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
      have hsl := min32_toNat st.block_start.toUInt32 (st.strstart - st.w_size)
      generalize MIN32 st.block_start.toUInt32 (st.strstart - st.w_size) = sl at hsl ⊢
      have hsli : sl.toInt32.toInt = sl.toNat := DeflateAlloc.u32_toInt32_toInt _ (by omega)
      simp only [chkI32, hsli]
      rw [ite_t (by omega), pure_bind_M]
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      refine Sat.bind (Sat.of_eq (add_SH sl.toNat (by omega)) ?_)
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      have hss' : (st.strstart - sl).toNat = st.strstart.toNat - sl.toNat :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
      refine Sat.bind (Sat.of_eq (memmove_SH (od := wo) (os := wo + sl.toNat) (n := (st.strstart - sl).toNat)
        (by omega) (by omega)) ?_)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      have hbn : (Int32.ofInt (st.block_start.toInt - ↑sl.toNat)).toInt = st.block_start.toInt - sl.toNat :=
        Int32.toInt_ofInt_of_le (by omega) (by omega)
      have hm := min32_toNat st.insert (st.strstart - sl)
      have hhv : (st.window_size - st.strstart + sl).toNat = st.window_size.toNat - (st.strstart - sl).toNat := by
        rw [UInt32.toNat_add, hd0, hss']; omega
      refine sat_gen (fun st' => st' = { st with
        strstart := st.strstart - sl
        block_start := Int32.ofInt (st.block_start.toInt - ↑sl.toNat)
        insert := MIN32 st.insert (st.strstart - sl) }) rfl ?_
      rintro st' rfl
      refine Sat.bind (Sat.pure ?_)
      have T := fill_tail F S hp k Q hk (st.window_size - st.strstart + sl) (st.strstart - sl)
        (MIN32 st.insert (st.strstart - sl)) (Int32.ofInt (st.block_start.toInt - ↑sl.toNat))
        (copyFold d wo (wo + sl.toNat) (List.range' 0 (st.strstart - sl).toNat) d) hhv (by omega) (by omega)
        (by omega) (by omega) (copyFold_size _ _ _ _ _)
      dsimp only at T
      exact T
    · simp only [hge, decide_false]
      refine Sat.bind (Sat.pure ?_)
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact noslide
  · simp only [hgt, ↓reduceIte]
    refine Sat.bind (Sat.pure ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact noslide

end ZlibNgF.Proof.StoredWin
