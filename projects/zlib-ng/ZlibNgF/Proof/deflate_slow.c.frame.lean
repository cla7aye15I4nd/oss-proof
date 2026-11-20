import ZlibNgF.Proof.«deflate_slow.c.lazy»
import ZlibNgF.Proof.«deflate_quick.c.emit»
import ZlibNgF.Proof.«insert_string_p.h.tail»
import ZlibNgF.Proof.«deflate_medium.c.step»
import ZlibNgF.Proof.«deflate_strategy.chain»
import ZlibNgF.Proof.«match_tpl.h.top»
import ZlibNgF.ZlibNg.«deflate_slow.c»

/-!
# The frame of `deflate_slow` (`ZlibNgF`)

`deflate_slow` keeps `lookahead` and `strstart` in the state and writes them one at a time, between the tally and the
insertions of a match. The loop frame of `Proof/deflate_strategy.common.lean` (`SLF`, `SLC`) is used on the state
itself, or on the state with the values that the trip will write (`FS st la ss`), and these steps carry it:

* `slf_view`: a change of fields that the invariant does not read (`prev_length`, `match_start`, `prev_match`,
  `match_available`, `ins_h`) at the levels of `deflate_slow`;
* `slf_move`: `strstart` and `lookahead` moved within the window, `block_start` and `insert` not above `strstart`;
* `slf_tally_lit0`: the literal of the byte before `strstart` (`window[strstart - 1]`), tallied before `strstart`
  moves, with `block_start` below `strstart`;
* `slf_insH`, `slf_insert_*`: the insertion functions, with the frame on any written-back `la` / `ss`;
* `slf_match`: `longest_match` through the function pointer, from the frame's layout;
* `slf_flush_keep`, `slf_flush_only_keep`: `FLUSH_BLOCK` / `FLUSH_BLOCK_ONLY` keep the state fields that the
  emitters do not write (`FBKeeps`) and the bytes before `pending_buf`;
* `chain_tr`: `ChainOk` carries to a state with the same tables and a larger `strstart` (at a level outside 3..6)
  and to bytes equal on `head` and `prev`;
* `lazy_fill`: `fill_window` keeps `LazyOk`;
* `slf_postW`: `StratPost` from `SLF` for a strategy entered at a level other than 1, with the symbol clause only for
  a stream with output room.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.SlowFrame
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InsertSafe (HLay)
open ZlibNgF.Proof.InsertGrow (Grow GPost GPostH)
open ZlibNgF.Proof.InsertLoop (GrowSt slf_bytes slf_hlay)
open ZlibNgF.Proof.FlushBlock (FBKeeps)
open ZlibNg.DeflateP

/-! ## The frame on a changed state -/

/-- `wrD` on an `SH` heap, with the new state named. -/
theorem wrD_SH' {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState} {d : Array UInt8}
    (f : DeflateState → DeflateState) (e : f st = st') :
    wrD (some b) f (SH H i z b st d) = .ok ((), SH H i z b st' d) := by
  rw [wrD_SH, e]

/-- `SLF` on a state with the same view of the invariant, `gzindex` and `last_flush`, at the levels of
`deflate_slow`. -/
theorem slf_view {h H0 : Heap} {i b : Nat} {z : ZStream} {st st' : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (hv : dview st' = dview st) (hg : st'.gzindex = st.gzindex)
    (hl : st'.last_flush = st.last_flush) (hT : TableAt 7 9 st) : SLF h i b (SH H0 i z b st' d) := by
  have e1 : st'.gzhead = st.gzhead := congrArg DView.gzhead hv
  have e2 : st'.level = st.level := congrArg DView.level hv
  have e3 : st'.status = st.status := congrArg DView.status hv
  have e4 : st'.window = st.window := congrArg DView.window hv
  have e5 : st'.wrap = st.wrap := congrArg DView.wrap hv
  have e6 : st'.strategy = st.strategy := congrArg DView.strategy hv
  have e7 : st'.strstart = st.strstart := congrArg DView.strstart hv
  have e8 : st'.block_start = st.block_start := congrArg DView.block_start hv
  have e9 : st'.sym_next = st.sym_next := congrArg DView.sym_next hv
  have e10 : st'.bi_valid = st.bi_valid := congrArg DView.bi_valid hv
  obtain ⟨-, -, hg0⟩ := F.st st (SH_dstate _ _ _ _ _ _)
  refine slf_SH F (fun al _ c => by rw [hv]; exact DCore.of_heap (by rw [SH_bytes, SH_bytes]) c) e1 e2 e3 e4
    ⟨fun e => by rw [e9]; exact hg0.1 (by rw [← e7, ← e8]; exact e), by rw [e10]; exact hg0.2⟩
    ⟨e3, e5, e1, hg, e2, e6, hl, fun hn => absurd hT hn⟩

/-- `SLF` with `strstart` and `lookahead` moved within the window, `block_start` and `insert` not above `strstart`, and
no symbols if `strstart` is at `block_start`. -/
theorem slf_move {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (ss la : UInt32) (hlook : ss.toNat + la.toNat ≤ st.window_size.toNat)
    (hbs : st.block_start.toInt ≤ ss.toNat) (hins : st.insert ≤ ss)
    (hgap : (ss.toNat : Int) = st.block_start.toInt → st.sym_next = 0) :
    SLF h i b (SH H0 i z b { st with strstart := ss, lookahead := la } d) := by
  obtain ⟨-, -, hg0⟩ := F.st st (SH_dstate _ _ _ _ _ _)
  exact slf_SH F (fun al _ c => DCore.of_heap (by rw [SH_bytes, SH_bytes])
    (dcore_set c ss la st.insert st.block_start hlook hbs hins c.bs_lo)) rfl rfl rfl rfl ⟨hgap, hg0.2⟩
    (StratKeeps.refl _)

/-- The numbers of the invariant of an `SLF` state. -/
theorem slf_nums {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) :
    st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat ∧ st.window_size.toNat ≤ 65536 ∧
      st.block_start.toInt ≤ st.strstart.toNat ∧ st.insert ≤ st.strstart ∧ 512 ≤ st.w_size.toNat ∧
      st.w_size.toNat ≤ 32768 ∧ 2 * st.w_size.toNat ≤ st.window_size.toNat ∧ 0 < st.sym_end.toNat := by
  obtain ⟨z1, st1, al, -, -, hst1, -, c⟩ := F.live
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  obtain ⟨w1, w2, hws, -, hl, -, hse⟩ := c.sizes
  have hws' : st.window_size = W_BUF_SIZE st.w_size := hws
  have w1' : 512 ≤ st.w_size.toNat := w1
  have w2' : st.w_size.toNat ≤ 32768 := w2
  have hl' : 128 ≤ st.lit_bufsize.toNat := by
    obtain ⟨k, hk1, -, hk⟩ := c.lpow
    have hk' : st.lit_bufsize.toNat = 2 ^ k := hk
    rw [hk']; exact Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk1)
  have hse' : st.sym_end.toNat = 3 * (st.lit_bufsize.toNat - 1) := hse
  have h65 : st.window_size.toNat ≤ 65536 := by
    rw [hws', DeflateInit.wbuf_toNat _ w2']; unfold DeflateAlloc.dWS; split <;> omega
  have h2w : 2 * st.w_size.toNat ≤ st.window_size.toNat := by
    rw [hws', DeflateInit.wbuf_toNat _ w2']; unfold DeflateAlloc.dWS; split <;> omega
  exact ⟨c.look, h65, c.bstart, c.ins, w1', w2', h2w, by omega⟩

/-! ## The literal before `strstart` -/

open ZlibNgF.Proof.Tally (W4 W4_wr dcore_tally_le tally_lit_SH symok_lit incF incF_size) in
/-- `zng_tr_tally_lit(s, c)` before `strstart` moves (the pending literal `window[strstart - 1]`), from `SLF` with no
pending bytes, `sym_next ≤ sym_end` and `block_start < strstart`: the state with one more symbol and the bytes
changed inside `sym_buf` (`SymWr`), `SLF` after, the result `sym_next + 3 == sym_end`. -/
theorem slf_tally_lit0 {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (hp0 : st.pending = 0) (hle : st.sym_next ≤ st.sym_end)
    (hbs : st.block_start.toInt < st.strstart.toNat) (c : UInt8) :
    Sat (SH H0 i z b st d) (zng_tr_tally_lit (some b) c) (fun r H' => ∃ lt d',
      H' = SH H0 i z b { st with sym_next := st.sym_next + 3, dyn_ltree := lt } d' ∧
      SLF h i b H' ∧ SymWr b (SH H0 i z b st d) H' ∧ r = (st.sym_next + 3 == st.sym_end)) := by
  obtain ⟨sbo, hsb, hk, hlt, -⟩ := slf_sym F hle
  refine Sat.mono (tally_lit_SH c hsb hk hlt) ?_
  rintro r H' ⟨rfl, rfl⟩
  obtain ⟨hlv, hstat, hg⟩ := F.st _ (SH_dstate _ _ _ _ _ _)
  obtain ⟨z1, st1, al, hz1, hb, hst1, hal, cc⟩ := F.live
  obtain rfl : z = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  have hroom : ∃ pbo poo, st.pending_buf = .val (.ref (.heap b) pbo) ∧
      st.pending_out = .val (.ref (.heap b) poo) ∧
      poo - pbo + st.pending.toNat + st.bi_valid.toInt.toNat / 8 ≤ st.lit_bufsize.toNat + 8 := by
    obtain ⟨-, -, -, -, pbo, -, -, -, -, hpb, -⟩ := cc.lay
    have hpo := cc.pout hp0
    simp only [dview] at hpb hpo
    refine ⟨pbo, pbo, hpb, by rw [hpo, hpb], ?_⟩
    have h8 : st.bi_valid.toInt < (8 : Int32).toInt := Int32.lt_iff_toInt_lt.mp hg.2
    have h0 : (8 : Int32).toInt = 8 := rfl
    have hz8 : st.bi_valid.toInt.toNat / 8 = 0 := by omega
    rw [hp0, hz8]; simp
  have hv : dview { st with sym_next := st.sym_next + 3, dyn_ltree := incF st.dyn_ltree c.toNat } =
      { dview st with
        sym_next := st.sym_next + 3
        ltree := incF st.dyn_ltree c.toNat
        dtree := st.dyn_dtree } := by
    simp only [dview, incF_size]
  have c1 := dcore_tally_le (H := H0) (c.toUInt32 <<< 16) cc (SH_bytes _ _ _ _ _ _) hsb hv hle
    (fun sbo hk hs hm hn hb => symok_lit hs hm hn hk c hlt hb) hroom hstat
  refine ⟨_, _, rfl, ?_, ⟨sbo, sbo + st.sym_next.toNat + 4, d, _, SH_bytes _ _ _ _ _ _,
    SH_bytes _ _ _ _ _ _, fun st2 h2 => ?_, (W4_wr _ _ _).widen (by omega) (by omega)⟩, rfl⟩
  · refine slf_SH F (fun al' hal' _ => ?_) rfl rfl rfl rfl ⟨fun e0 => ?_, hg.2⟩ (StratKeeps.refl _)
    · obtain rfl : al = al' := Option.some.inj (hal.symm.trans (by simpa [Heap.dallocsOf, SH] using hal'))
      exact c1
    · exfalso
      have e1 : (st.strstart.toNat : Int) = st.block_start.toInt := e0
      omega
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); exact hsb

/-! ## Layout, insertions, the matcher -/

/-- The layout of an `SLF` state: the hash tables (`HLay`), `w_size` a power of two, the window before `prev`, the
room of `longest_match`, and `pending_buf` / `sym_buf` after `head`. -/
theorem slf_lay {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) :
    ∃ wo po ho pbo, HLay b d.size st wo po ho ∧ (∃ k, st.w_size.toNat = 2 ^ k) ∧ wo + st.window_size.toNat ≤ po ∧
      wo + 131400 ≤ d.size ∧ st.pending_buf = .val (.ref (.heap b) pbo) ∧ ho + 131072 ≤ pbo ∧
      st.sym_buf = .val (.ref (.heap b) (pbo + st.lit_bufsize.toNat + 8)) := by
  obtain ⟨z1, st1, al, -, -, hst1, -, c⟩ := F.live
  obtain rfl : st = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
  obtain ⟨wo, po, ho, pbo, L, hwp, hpb, hhp, hsb⟩ := ZlibNgF.Proof.FillFacts.hlay_of c (SH_bytes _ _ _ _ _ _)
  obtain ⟨k, -, -, hk⟩ := c.wpow
  obtain ⟨-, -, -, -, w1, -, h2w, -⟩ := slf_nums F
  have hLp := L.pw
  have hLh := L.hd
  have hLph := L.ph
  exact ⟨wo, po, ho, pbo, L, ⟨k, hk⟩, hwp, by omega, hpb, hhp, hsb⟩

/-- An insertion function (post `GPostH`) on `SH H0 i z b st d` whose state with `la` / `ss` written back satisfies
`SLF`: `SLF` again with the new bytes and `ins_h`, and the chains grown. -/
theorem slf_insH {α : Type} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {la ss : UInt32} {m : M α} {S : Nat → Prop} (F : SLF h i b (SH H0 i z b (FS st la ss) d))
    (hm : ∀ wo po ho, HLay b d.size st wo po ho → (∃ k, st.w_size.toNat = 2 ^ k) →
      wo + st.window_size.toNat ≤ po → Sat (SH H0 i z b st d) m (GPostH H0 i z b st d ho po st.w_size.toNat S)) :
    Sat (SH H0 i z b st d) m (fun _ H' => ∃ d' x, H' = SH H0 i z b { st with ins_h := x } d' ∧
      SLF h i b (SH H0 i z b (FS { st with ins_h := x } la ss) d') ∧ GrowSt b st d d' S) := by
  obtain ⟨wo, po, ho, L, hp, hwp⟩ := slf_hlay F
  have L' : HLay b d.size st wo po ho := ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩
  refine Sat.mono (hm wo po ho L' hp hwp) ?_
  rintro _ _ ⟨d', x, rfl, w, g⟩
  have F1 : SLF h i b (SH H0 i z b (FS st la ss) d') := slf_bytes F fun ho' hh => by
    have hh' : st.head = .val (.ref (.heap b) ho') := hh
    rw [L'.head] at hh'
    obtain rfl : ho = ho' := by injection hh' with e; injection e
    exact w.widen (Nat.zero_le _) (Nat.le_refl _)
  refine ⟨d', x, rfl, ?_, fun ho' po' hh hpv => ?_⟩
  · exact slf_SH F1 (fun al _ c => DCore.of_heap (by rw [SH_bytes, SH_bytes]) c) rfl rfl rfl rfl
      (F1.st _ (SH_dstate _ _ _ _ _ _)).2.2 (StratKeeps.refl _)
  · rw [L'.head] at hh; rw [L'.prev] at hpv
    obtain rfl : ho = ho' := by injection hh with e; injection e
    obtain rfl : po = po' := by injection hpv with e; injection e
    exact g

section
open ZlibNg.InsertStringP ZlibNg.InsertString
open ZlibNgF.Proof.InsertTail (insert_roll_G insert_knuth_batch_tail_G insert_roll_batch_tail_G)
open ZlibNgF.Proof.InsertGrow (insert_knuth_G call_insert_batch_G)
variable {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}

/-- `insert_roll(s, window, str)` (level 9) under the frame. -/
theorem slf_insert_roll (F : SLF h i b (SH H0 i z b (FS st la ss) d)) (hw : st.window = .val (.ref (.heap b) wo))
    (str : UInt32) (hr : str.toNat + 3 ≤ st.window_size.toNat) (hs : str.toNat < 65536) :
    Sat (SH H0 i z b st d) (insert_roll (some b) (.ref (.heap b) wo) str) (fun _ H' => ∃ d' x,
      H' = SH H0 i z b { st with ins_h := x } d' ∧ SLF h i b (SH H0 i z b (FS { st with ins_h := x } la ss) d') ∧
      GrowSt b st d d' (· = str.toNat)) :=
  slf_insH F fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_roll_G L hp str (by have := L.pw; omega) hs

/-- `insert_knuth(s, window, str)` (levels 7-8) under the frame. -/
theorem slf_insert_knuth (F : SLF h i b (SH H0 i z b (FS st la ss) d)) (hw : st.window = .val (.ref (.heap b) wo))
    (str : UInt32) (hr : str.toNat + 4 ≤ st.window_size.toNat) (hs : str.toNat < 65536) :
    Sat (SH H0 i z b st d) (insert_knuth (some b) (.ref (.heap b) wo) str) (fun _ H' => ∃ d' x,
      H' = SH H0 i z b { st with ins_h := x } d' ∧ SLF h i b (SH H0 i z b (FS { st with ins_h := x } la ss) d') ∧
      GrowSt b st d d' (· = str.toNat)) :=
  slf_insH F fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact Sat.mono (insert_knuth_G L hp str (by have := L.pw; omega) hs) fun _ _ ⟨d', e, w, g⟩ =>
      ⟨d', st.ins_h, e, w, g⟩

/-- `insert_batch(s, window, str, count)` through the function pointer under the frame; the last 4-byte read ends at
most one byte past the window (`str + count + 2 <= window_size`), inside the block. -/
theorem slf_call_insert_batch (F : SLF h i b (SH H0 i z b (FS st la ss) d))
    (hw : st.window = .val (.ref (.heap b) wo)) (f : InsertBatchFn) (hf : f ≠ .insert_knuth_batch_head)
    (str count : UInt32) (hr : str.toNat + count.toNat + 2 ≤ st.window_size.toNat)
    (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H0 i z b st d) (call_insert_batch f (some b) (.ref (.heap b) wo) str count) (fun _ H' => ∃ d' x,
      H' = SH H0 i z b { st with ins_h := x } d' ∧ SLF h i b (SH H0 i z b (FS { st with ins_h := x } la ss) d') ∧
      GrowSt b st d d' (fun q => str.toNat ≤ q ∧ q < str.toNat + count.toNat)) :=
  slf_insH F fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact call_insert_batch_G L hp f hf str count (by have := L.pw; have := L.w1; omega) hs

/-- `insert_knuth_batch_tail_static(s, window, str, count, tail)` under the frame. -/
theorem slf_insert_knuth_tail (F : SLF h i b (SH H0 i z b (FS st la ss) d))
    (hw : st.window = .val (.ref (.heap b) wo)) (str count tail : UInt32) (ht : tail.toNat ≤ count.toNat)
    (hc : count.toNat - tail.toNat ≤ st.w_size.toNat) (hr : str.toNat + count.toNat + 2 ≤ st.window_size.toNat)
    (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H0 i z b st d) (insert_knuth_batch_tail_static (some b) (.ref (.heap b) wo) str count tail)
      (fun _ H' => ∃ d' x, H' = SH H0 i z b { st with ins_h := x } d' ∧
        SLF h i b (SH H0 i z b (FS { st with ins_h := x } la ss) d') ∧
        GrowSt b st d d' (fun q => str.toNat + count.toNat - tail.toNat ≤ q ∧ q < str.toNat + count.toNat)) :=
  slf_insH F fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact Sat.mono (insert_knuth_batch_tail_G L hp str count tail ht hc (by have := L.pw; have := L.w1; omega) hs)
      fun _ _ ⟨d', e, w, g⟩ => ⟨d', st.ins_h, e, w, g⟩

/-- `insert_roll_batch_tail_static(s, window, str, count, tail)` under the frame. -/
theorem slf_insert_roll_tail (F : SLF h i b (SH H0 i z b (FS st la ss) d))
    (hw : st.window = .val (.ref (.heap b) wo)) (str count tail : UInt32) (ht : tail.toNat ≤ count.toNat)
    (hc : count.toNat - tail.toNat ≤ st.w_size.toNat) (hr : str.toNat + count.toNat + 2 ≤ st.window_size.toNat)
    (hs : str.toNat + count.toNat ≤ 65536) :
    Sat (SH H0 i z b st d) (insert_roll_batch_tail_static (some b) (.ref (.heap b) wo) str count tail)
      (fun _ H' => ∃ d' x, H' = SH H0 i z b { st with ins_h := x } d' ∧
        SLF h i b (SH H0 i z b (FS { st with ins_h := x } la ss) d') ∧
        GrowSt b st d d' (fun q => str.toNat + count.toNat - tail.toNat ≤ q ∧ q < str.toNat + count.toNat)) :=
  slf_insH F fun wo' po ho L hp hwp => by
    rw [L.win] at hw
    obtain rfl : wo' = wo := by injection hw with e; injection e
    exact insert_roll_batch_tail_G L hp str count tail ht hc (by have := L.pw; have := L.w1; omega) hs

end

/-- `longest_match(s, cur_match)` through the function pointer under the frame, with the candidate a `Pos` at or
above `limit_base`: only `match_start` changes, and the result (`PR`) is at most the initial `best_len`, or within
the lookahead and 258 with `limit_base <= match_start`. -/
theorem slf_match {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (f : LongestMatchFn) (cm : UInt32) (hcm : cm.toNat < 65536)
    (hlb : (ZlibNgF.Proof.LongestMatch.limitBase st).toNat ≤ cm.toNat) :
    Sat (SH H0 i z b st d) (ZlibNg.Compare256.call_longest_match f (some b) cm) (fun r H' => ∃ ms,
      H' = SH H0 i z b { st with match_start := ms } d ∧
      ZlibNgF.Proof.LongestMatch.PR st 65536
        (if st.prev_length != 0 then st.prev_length else STD_MIN_MATCH - 1).toNat r ms) := by
  obtain ⟨wo, po, ho, pbo, L, -, hwp, hbig, -⟩ := slf_lay F
  obtain ⟨hlook, h65, -, -, w1, w2, -⟩ := slf_nums F
  have N : ZlibNgF.Proof.LongestMatch.LN d wo po ho st := ⟨w1, w2, by omega, by omega, by omega, hbig, L.pw, L.hd⟩
  cases f
  · exact ZlibNgF.Proof.LongestMatch.longest_match_slow_knuth_c_safe L.win L.prev L.head N hcm hlb
  · exact ZlibNgF.Proof.LongestMatch.longest_match_slow_roll_c_safe L.win L.prev L.head N hcm hlb

/-! ## `FLUSH_BLOCK` -/

/-- The fields that `FLUSH_BLOCK_ONLY` keeps (`FBKeeps`). -/
theorem fbkeeps_fields {st st2 : DeflateState} (K : FBKeeps st st2) :
    st2.prev_length = st.prev_length ∧ st2.match_start = st.match_start ∧ st2.match_available = st.match_available ∧
      st2.strstart = st.strstart ∧ st2.lookahead = st.lookahead ∧ st2.w_size = st.w_size ∧ st2.level = st.level ∧
      st2.strategy = st.strategy ∧ st2.last_flush = st.last_flush ∧ st2.head = st.head ∧ st2.prev = st.prev ∧
      st2.block_start = st.strstart.toInt32 ∧ st2.window = st.window ∧ st2.pending_buf = st.pending_buf ∧
      st2.prev_match = st.prev_match ∧ st2.insert = st.insert ∧ st2.window_size = st.window_size := by
  obtain ⟨st1, hK1, hst2e⟩ := K
  rw [hst2e, hK1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `FLUSH_BLOCK(s, window, last)` from `SLF` with no pending bytes keeps the fields of `FBKeeps` and the bytes of the
block outside `pending_buf`. -/
theorem slf_flush_keep (T : TreesFacts) {h H : Heap} {i b wo : Nat} (last : Int32) (hl0 : 0 ≤ last)
    (hl1 : last ≤ 1) (F : SLF h i b H)
    (hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo)) :
    Sat H (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun _ H2 => ∀ st, H.dstate b = some st →
      ∃ st2, H2.dstate b = some st2 ∧ FBKeeps st st2 ∧ ∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) →
        PbufOnly H H2 b pbo (4 * st.lit_bufsize.toNat + 9)) := by
  obtain ⟨z, st, al, hz, hb, hst, -, -⟩ := F.live
  obtain ⟨hp0, hwin⟩ := hp st hst
  obtain ⟨hlv, -, -, h8⟩ := F.st st hst
  obtain ⟨r, h', e, P, -⟩ := ZlibNgF.Proof.FlushBlock.flush_block_ok T last hl0 hl1 F.inv F.io F.set hz hb hst hp0
    hlv h8 hwin
  refine ⟨r, h', e, fun st1 h1 => ?_⟩
  obtain rfl := Option.some.inj (hst.symm.trans h1)
  obtain ⟨z', st', -, -, hst', -, -, -, -, -, -, K⟩ := P.out
  exact ⟨st', hst', K, P.pbuf⟩

/-- `FLUSH_BLOCK_ONLY(s, window, last)` from `SLF` with no pending bytes keeps the fields of `FBKeeps` and the bytes
of the block outside `pending_buf`. -/
theorem slf_flush_only_keep (T : TreesFacts) {h H : Heap} {i b wo : Nat} (window : M BPtr) (last : Int32)
    (hl0 : 0 ≤ last) (hl1 : last ≤ 1) (F : SLF h i b H)
    (hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo))
    (hwm : window H = .ok (.ref (.heap b) wo, H)) :
    Sat H (FLUSH_BLOCK_ONLY (some b) window last) (fun _ H2 => ∀ st, H.dstate b = some st →
      ∃ st2, H2.dstate b = some st2 ∧ FBKeeps st st2 ∧ ∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) →
        PbufOnly H H2 b pbo (4 * st.lit_bufsize.toNat + 9)) := by
  obtain ⟨z, st, al, hz, hb, hst, -, -⟩ := F.live
  obtain ⟨hp0, hwin⟩ := hp st hst
  obtain ⟨hlv, -, -, h8⟩ := F.st st hst
  obtain ⟨h', e, P⟩ := ZlibNgF.Proof.FlushBlock.flush_block_only_ok T window last hl0 hl1 F.inv F.io F.set hz hb hst
    hp0 hlv h8 hwin hwm
  refine ⟨(), h', e, fun st1 h1 => ?_⟩
  obtain rfl := Option.some.inj (hst.symm.trans h1)
  obtain ⟨z', st', -, -, hst', -, -, -, -, -, -, K⟩ := P.out
  exact ⟨st', hst', K, P.pbuf⟩

/-! ## The hash chains -/

/-- `ChainOk` carries to a state with the same level, strategy, tables and `w_size` and a larger `strstart`, at a
level of 7 or more, and to bytes equal below the end of `head`. -/
theorem chain_tr {b : Nat} {d d' : Array UInt8} {X X' : DeflateState} (C : ChainOk b d X)
    (e1 : X'.level = X.level) (e2 : X'.strategy = X.strategy) (e3 : X'.head = X.head) (e4 : X'.prev = X.prev)
    (e5 : X'.w_size = X.w_size) (hss : X.strstart.toNat ≤ X'.strstart.toNat) (hlv : 7 ≤ X.level)
    (hw : 0 < X.w_size.toNat)
    (hb : ∀ ho po, X.head = .val (.ref (.heap b) ho) → X.prev = .val (.ref (.heap b) po) →
      po + 2 * X.w_size.toNat ≤ ho ∧ ∀ j, j < ho + 131072 → d'[j]! = d[j]!) : ChainOk b d' X' := by
  have C1 : ChainOk b d' X := ZlibNgF.Proof.DeflateSide.ChainOk.of_bytes C hw fun ho po hh hp => by
    obtain ⟨h1, h2⟩ := hb ho po hh hp
    exact ⟨fun j _ hj => h2 j (by omega), fun j _ hj => h2 j (by omega)⟩
  have hn : ¬ (3 ≤ X.level ∧ X.level ≤ 6) := fun ⟨_, h6⟩ => by
    have a := Int32.le_iff_toInt_le.mp hlv
    have c := Int32.le_iff_toInt_le.mp h6
    have e7 : (7 : Int32).toInt = 7 := rfl
    have e6 : (6 : Int32).toInt = 6 := rfl
    omega
  refine ZlibNgF.Proof.InsertGrow.ChainOk.grow (S := fun _ => False) C1 (fun ho po _ _ => Grow.refl _ _ _ _ _)
    e1 e2 e3 e4 e5 hss ?_ (fun q hq => hq.elim)
  unfold chainLim
  rw [e1]
  simp only [hn, ↓reduceIte]
  omega

/-! ## `fill_window` -/

/-- `fill_window` keeps `LazyOk`: a pending match keeps its length and its distance, a pending literal stays after
`block_start`, the lookahead does not drop, and `w_size`, `level`, `strategy`, `last_flush` are kept. -/
theorem lazy_fill {st st' : DeflateState} (L : LazyOk st)
    (hpl : 3 ≤ st'.prev_length → st'.prev_length = st.prev_length ∧
      (st.strstart.toNat : Int) - st.match_start.toNat = (st'.strstart.toNat : Int) - st'.match_start.toNat ∧
      st'.match_start ≤ st.match_start)
    (hle : st'.prev_length ≤ st.prev_length) (hma : st'.match_available = st.match_available)
    (hla : st.lookahead.toNat ≤ st'.lookahead.toNat) (hs1 : 1 ≤ st.strstart.toNat → 1 ≤ st'.strstart.toNat)
    (hgap0 : (st'.strstart.toNat : Int) = st'.block_start.toInt → (st.strstart.toNat : Int) = st.block_start.toInt)
    (hbs : st'.block_start.toInt ≤ st'.strstart.toNat)
    (hw : st'.w_size = st.w_size) (hlv : st'.level = st.level) (hsg : st'.strategy = st.strategy)
    (hlf : st'.last_flush = st.last_flush) : LazyOk st' := by
  obtain ⟨l1, l2, l3, l4⟩ := L
  have hmd : (MAX_DIST st').toNat = (MAX_DIST st).toNat := by unfold MAX_DIST; rw [hw]
  refine ⟨fun h3 => ?_, fun hm => ?_, fun ht => ?_, fun e => ?_⟩
  · obtain ⟨e1, e2, -⟩ := hpl h3
    rw [e1] at h3 ⊢
    obtain ⟨a1, a2, a3, a4⟩ := l1 h3
    rw [hmd]
    exact ⟨a1, by omega, by omega, by omega⟩
  · rw [hma] at hm
    obtain ⟨a1, a2⟩ := l2 hm
    refine ⟨hs1 a1, ?_⟩
    by_cases hc : st'.block_start.toInt < st'.strstart.toNat
    · exact hc
    · have := hgap0 (by omega); omega
  · have ht' : ¬ TableAt 7 9 st := fun hh => ht ((tableAt_congr hlv hsg).mpr hh)
    obtain ⟨a1, a2⟩ := l3 ht'
    exact ⟨UInt32.lt_of_le_of_lt hle a1, hma.trans a2⟩
  · obtain ⟨a1, a2⟩ := l4 (hlf ▸ e)
    exact ⟨UInt32.lt_of_le_of_lt hle a1, hma.trans a2⟩

/-- The input that `fill_window` reads, from the frame. -/
theorem slf_input {h H : Heap} {i b : Nat} (F : SLF h i b H) : DInput H (some i) := by
  obtain ⟨z, hz, hb⟩ := F.blk
  have hio0 := F.io
  obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, hin0, -, -, hdj⟩ := hio0
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb.symm.trans hb2)
  obtain ⟨z3, ⟨i3, e3, hz3⟩, -, hni⟩ := F.set
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  exact ⟨z, b, ⟨i, rfl, hz⟩, hb, hin0, (hdj _ (.inl rfl)).2, hni⟩

/-- `fill_window` (with `lookahead < MIN_LOOKAHEAD`) on the state itself under `SLC`: `SLC` after, the hash chains and
`LazyOk` kept, the lookahead plus the input not grown, the input dropped when the lookahead changed, and the
lookahead full or the input empty. -/
theorem slc_fill {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (C : SLC h i b (SH H0 i z b st d)) (hla : st.lookahead.toNat < 262) (Ch : ChainOk b d st) (L : LazyOk st) :
    Sat (SH H0 i z b st d) (ZlibNg.Deflate.fill_window (some b)) (fun _ H2 => ∃ H1 z' st' d',
      H2 = SH H1 i z' b st' d' ∧ SLC h i b H2 ∧ ChainOk b d' st' ∧ LazyOk st' ∧
      z'.avail_in.toNat + st'.lookahead.toNat ≤ z.avail_in.toNat + st.lookahead.toNat ∧
      (st'.lookahead ≠ st.lookahead → z'.avail_in.toNat < z.avail_in.toNat) ∧
      (262 ≤ st'.lookahead.toNat ∨ z'.avail_in = 0)) := by
  have I := sli_of_slc C (SH_dstate _ _ _ _ _ _)
  obtain ⟨_, H1, e, p⟩ := sli_fill I hla
  rw [wrD_SH] at e
  obtain rfl : SH H0 i z b { st with lookahead := st.lookahead, strstart := st.strstart } d = H1 := by
    injection e with e; injection e
  have p' := p
  obtain ⟨z1, hz1, hb⟩ := C.1.blk
  obtain rfl : z = z1 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz1)
  obtain ⟨H2, e2, FI⟩ := ZlibNgF.Proof.FillIO.fill_io C.1.inv C.1.io C.1.set C.1.crc (SH_streams _ _ _ _ _ _) hb
    (SH_dstate _ _ _ _ _ _) hla
  obtain ⟨r, H3, e3, ⟨H1', z', st', d', rfl, I', hsum, hlt, hend⟩, e4⟩ :=
    ZlibNgF.Proof.MediumStep.Sat.and p' (⟨(), H2, e2, rfl⟩ : Sat (SH H0 i z b st d)
      (ZlibNg.Deflate.fill_window (some b)) (fun _ H' => H' = H2))
  subst e4
  have C' := sli_slc I'
  refine ⟨r, _, e3, H1', z', st', d', rfl, C', ?_, ?_, by rw [avIn_SH] at hsum; exact hsum,
    fun hn => by have := hlt hn; rw [avIn_SH] at this; exact this, hend⟩
  · obtain ⟨z6, hz6, hb6⟩ := C'.1.blk
    obtain rfl : z' = z6 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz6)
    exact ZlibNgF.Proof.FillFacts.fill_window_chain _ _ (some i) b st d C.1.inv ⟨i, z, rfl, SH_streams _ _ _ _ _ _,
      hb, SH_dstate _ _ _ _ _ _⟩ (SH_bytes _ _ _ _ _ _) (slf_input C.1) (fun _ => C.1.crc) hla Ch e2 st' d'
      ⟨i, z', rfl, SH_streams _ _ _ _ _ _, hb6, SH_dstate _ _ _ _ _ _⟩ (SH_bytes _ _ _ _ _ _)
  · obtain ⟨-, -, -, i6, z6, z7, b6, st6, st7, e6, hz6, -, hb6, hst6, hst7, -, -, -, -, -, hgap0, -, -, -, -,
      hlv, hsg, -, -, -, -, hlf, -, hpl3, hle, hma, hla', hs1⟩ := FI.post
    obtain rfl : i = i6 := Option.some.inj e6
    obtain rfl : z = z6 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz6)
    obtain rfl : b = b6 := Option.some.inj (hb.symm.trans hb6)
    obtain rfl : st = st6 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst6)
    obtain rfl : st' = st7 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst7)
    obtain ⟨z5, z8, st5, st8, d8, hz5, hst5, e8, -, fws⟩ := FI.shape
    obtain rfl : st = st5 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst5)
    have e9 := congrArg (fun H => H.dstate b) e8
    simp only [SH_dstate] at e9
    obtain rfl := Option.some.inj e9
    exact lazy_fill L hpl3 hle hma hla' hs1 hgap0 (slf_nums C'.1).2.2.1
      (ZlibNgF.Proof.FillWindow.FWS.sizes fws).2 hlv hsg hlf

/-! ## Normal forms -/

/-- `SLW` of an `SH` heap, on the same base heap and stream record. -/
theorem slw_norm {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (W : SLW h i b la ss (SH H0 i z b st d)) : SLF h i b (SH H0 i z b (FS st la ss) d) ∧ st.pending = 0 := by
  obtain ⟨H1, z1, st1, d1, e, F, hp⟩ := W
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  have e3 := congrArg (fun H => H.streams i) e
  simp only [SH_dstate, SH_bytes, SH_streams] at e1 e2 e3
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj e3
  refine ⟨?_, hp⟩
  rw [← SH_SH H0 i z z b st (FS st la ss) d d, e, SH_SH]; exact F

/-- `SLI` of an `SH` heap, on the same base heap and stream record. -/
theorem sli_norm {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d)) : SLC h i b (SH H0 i z b (FS st la ss) d) := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  have e3 := congrArg (fun H => H.streams i) e
  simp only [SH_dstate, SH_bytes, SH_streams] at e1 e2 e3
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain rfl := Option.some.inj e3
  rw [← SH_SH H0 i z z b st (FS st la ss) d d, e, SH_SH]; exact C

/-- `SLC` of a state with `SLF` and the two numbers. -/
theorem slc_of {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (hp : st.pending = 0) (hs : st.sym_next < st.sym_end) :
    SLC h i b (SH H0 i z b st d) :=
  ⟨F, fun st2 h2 => by obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); exact ⟨hp, hs⟩⟩

/-! ## Entry and exit -/

/-- The levels of `deflate_slow`: above 0, not 1, at least 7. -/
theorem tab_lv {st : DeflateState} (hT : TableAt 7 9 st) : 0 < st.level ∧ st.level ≠ 1 ∧ 7 ≤ st.level := by
  have a := Int32.le_iff_toInt_le.mp hT.1
  have e7 : (7 : Int32).toInt = 7 := rfl
  refine ⟨Int32.lt_iff_toInt_lt.mpr (by have : (0 : Int32).toInt = 0 := rfl; omega), fun e => ?_, hT.1⟩
  rw [e] at a; exact absurd a (by decide)

/-- The levels, strategy and `last_flush` at entry stay under `SLF`. -/
theorem slf_table {h H : Heap} {i b : Nat} (F : SLF h i b H)
    (hT : ∀ st0, h.dstate b = some st0 → TableAt 7 9 st0 ∧ 0 ≤ st0.last_flush) :
    ∀ st, H.dstate b = some st → TableAt 7 9 st ∧ 0 ≤ st.last_flush := by
  intro st hst
  obtain ⟨st0, h0, hk⟩ := F.keeps
  have K := hk st hst
  obtain ⟨a, c⟩ := hT st0 h0
  exact ⟨(tableAt_congr K.2.2.2.2.1 K.2.2.2.2.2.1).mpr a, by rw [K.2.2.2.2.2.2.1]; exact c⟩

/-- `StratPost` from `SLF` and the exit facts, for a strategy entered at a level other than 1, with `LazyOk` after
from `LazyOk` at entry; the symbols need to be gone after a flush only when the output has room. -/
theorem slf_postW {h H : Heap} {i b : Nat} (F : SLF h i b H) (flush : Int32) (bs : BlockState)
    (hn : ∀ st0, h.dstate b = some st0 → st0.level ≠ 1)
    (hL : ∀ st0, h.dstate b = some st0 → LazyOk st0 → ∀ st, H.dstate b = some st →
      LazyOk st ∧ (bs = .block_done → st.match_available = 0))
    (hs : ∀ st, H.dstate b = some st → st.sym_next < st.sym_end ∧
      (bs = .block_done ∨ bs = .finish_done → st.pending = 0) ∧
      (flush ≠ Z_NO_FLUSH → (∀ z', StreamAt H (some i) z' → z'.avail_out ≠ 0) → st.sym_next = 0) ∧
      (bs = .finish_started ∨ bs = .finish_done → st.sym_next = 0 ∧ st.lookahead = 0) ∧
      (bs = .block_done → st.sym_next = 0)) : StratPost h (some i) flush bs H := by
  obtain ⟨z, st, al, hz, hb, hst, -, -⟩ := F.live
  obtain ⟨z0, hz0, hb0⟩ := F.blk0
  have hsi : stateIds h (some i) = [b] := by simp [stateIds, hz0, hb0]
  refine ⟨F.inv, F.io, F.set, ?_, fun _ e => by obtain rfl := Option.some.inj e; exact F.out,
    stateBlock_keep F.blk0 F.blk, fun e => ⟨b, st, ⟨i, z, rfl, hz, hb, hst⟩, ((hs st hst).2.1 e)⟩, ?_⟩
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
    refine ⟨⟨x1, fun e0 => ?_, fun e1 _ => ?_, hg2.1, fun e8 => absurd hg2.2 (Int32.not_lt.mpr e8)⟩, K,
      x3, x4, x5, fun L => hL st0 h0 L st hst⟩
    · rw [e0] at hlv; exact absurd hlv (by decide)
    · exact absurd (K.2.2.2.2.1.symm.trans e1) (hn st0 h0)

/-- The entry of `deflate_slow`: `SLC` of the entry heap, `LazyOk`, `last_flush` not negative. -/
theorem slow_entry {h : Heap} {i b : Nat} {z : ZStream} {flush : Int32} (P : StratPre h (some i) flush)
    (hz : h.streams i = some z) (hb : z.state = some b)
    (hT : ∀ b' st, DStateIs h (some i) b' st → TableAt 7 9 st) :
    ∃ st, h.dstate b = some st ∧ SLC h i b h ∧ LazyOk st ∧ 0 ≤ st.last_flush ∧ TableAt 7 9 st := by
  obtain ⟨hv, hcrc, hio, hset, -, -, b1, st1, ⟨i1, z1, e1, hz1, hb1, hst1⟩, hp0, hs1, ⟨hsym, -, -, hg2, hg8⟩, hL,
    hlf⟩ := P
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  have hT1 := hT b st1 ⟨i, z, rfl, hz, hb, hst1⟩
  obtain ⟨hlv, hn1, -⟩ := tab_lv hT1
  have hgap : GapOk st1 := ⟨hg2, Int32.not_le.mp fun e8 => hn1 (hg8 e8).1⟩
  refine ⟨st1, hst1, ⟨⟨hv, hio, hset, hcrc, ⟨z, hz, hb⟩, ⟨z, hz, hb⟩, dframe_refl _ _ _ _ _, ?_,
    ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; rfl⟩,
    ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; exact StratKeeps.refl _⟩, fun st h1 => ?_⟩,
    fun st h1 => ?_⟩, hL, hlf, hT1⟩
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

end ZlibNgF.Proof.SlowFrame
