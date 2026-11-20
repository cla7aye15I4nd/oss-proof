import ZlibNgF.Proof.«match_tpl.h.bits»
import ZlibNgF.Proof.«insert_string_p.h.base»

/-!
# Safety of `LONGEST_MATCH` (`match_tpl.h`, `ZlibNgF`)

The three instantiations `longest_match_c`, `longest_match_slow_knuth_c` and `longest_match_slow_roll_c` run on an `SH`
heap (`Proof/deflate.c.init.lean`) whose block `b` holds the window at `wo`, `prev` at `po` and `head` at `ho`.

Read ranges. Every candidate position is a 16-bit `Pos` (the argument `cur_match`, or a value of `prev` / `head`), and
with patch 0009 every candidate address is `window + (cur_match - match_offset) (+ offset)`, where
`limit_base + match_offset <= cur_match` keeps the subtraction from wrapping. The reads are
* `[window + strstart, + 8)` (`scan_start`), `[window + strstart + offset, + 8)` (`scan_end`, `offset < lookahead`),
  the bytes `scan[i]` / `scan + i .. + 4` of the lazy re-anchoring (`i <= best_len < lookahead`);
* `[window + c, + 8)` and `[window + offset + c, + 8)` for a candidate `c = cur_match - match_offset < 65536`;
* `compare256(scan + 2, window + c + 2)`: `[window + strstart + 2, + 256)` and `[window + c + 2, + 256)`;
* `prev[k & wmask]` (`k & wmask < w_size`) and `head[h]` (`h < HASH_SIZE`).
All of them end below `window + 2^17 + 300`, inside block `b`: `alloc_deflate` places `prev` (at least 1024 bytes) and
`head` (131072 bytes) after the window of at least 32768 bytes. Reads past `window + window_size` are reads of `prev`
/ `head` bytes, inside the allocation (one object in C); the result does not depend on them for matches within the
lookahead, and the model's bytes are defined (`Heap.garbage` for never-written bytes).

Termination. Every trip of the outer loop either decrements `chain_length` (whose distance to the stop at zero,
`chainLeft`, falls by one; the C's unsigned wrap from 0 to `2^32 - 1` gives at most `2^32` steps) or, in the
offset search of the slow variants, raises `best_len` (a short-candidate accept has `len > best_len`,
`MatchBits.short_len_gt`); `best_len < 2^17`.

The result (`LMPost`): at most the initial `best_len` (`prev_length` or `STD_MIN_MATCH - 1`), or at most `lookahead`
and 258 with `match_start` a candidate position with `limit_base <= match_start < B`. Only `match_start` of the
state changes. The bound `B` comes from `PrevBelow d po st B` (every `prev` entry is 0 or below `B`, `B <= 65536`).
`B = 65536` holds of every state (`prevBelow_65536`): memory safety and termination need nothing of the hash chains.
`B = strstart` gives `match_start < strstart` (so `strstart - match_start <= MAX_DIST`), but only where every `prev`
entry is below `strstart`; that is not true of every reachable state (a `prev` slot not written since a reset of the
positions, read through the offset search of the slow variants, can hold a position at or above `strstart`).

Candidate sets. The walk also keeps every candidate in a set `Ch` closed under the chain step (`PrevCh`: a candidate of
`Ch` at or above `limit_base` has `prev[c & w_mask]` 0 or in `Ch`), given the entry candidate in `Ch`; an accepted
`match_start` of `longest_match_c` (which keeps `match_offset == 0`) is then in `Ch` (`BLC`, `PRC`). With `Ch` the
positions of the hash chains (clause (C3) of `ChainOk`, which covers every candidate since `limit_base > strstart -
w_size`) this bounds `match_start` without a bound on all of `prev`. The slow variants run with `Ch = fun _ => True`
(their offset search moves to positions outside the walked chain).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.LongestMatch
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Compare256 ZlibNg.InsertStringP ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem (sat_add sat_memread8 sat_memread4 sat_index8)
open ZlibNgF.Proof.Compare256 (compare256_ok)
open ZlibNgF.Proof.MatchBits (mask_ok short_len_gt)
open ZlibNgF.Proof.WinBase (knuth_lt roll_lt mask_lt)

variable {B : Nat}

/-- The `Pos` stored at byte offset `o` (little-endian). -/
def rd2 (d : Array UInt8) (o : Nat) : UInt16 := d[o]!.toUInt16 ||| (d[o + 1]!.toUInt16 <<< 8)

/-- The number of decrements of `chain_length` before `--chain_length == 0` stops the walk. -/
def chainLeft (c : UInt32) : Nat := (c.toNat + 4294967295) % 4294967296

theorem chainLeft_dec (c : UInt32) (h : c - 1 ≠ 0) : chainLeft (c - 1) + 1 = chainLeft c := by
  have h2 : (c - 1).toNat ≠ 0 := fun e => h (UInt32.toNat_inj.mp (by rw [e]; rfl))
  have hc := c.toNat_lt
  by_cases h0 : c = 0
  · subst h0; unfold chainLeft; rw [show ((0 : UInt32) - 1).toNat = 4294967295 from rfl]; rfl
  · have h1 : (c - 1).toNat = c.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]
        have : c.toNat ≠ 0 := fun e => h0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
        show 1 ≤ c.toNat; omega)]
      rfl
    unfold chainLeft; rw [h1]; rw [h1] at h2
    omega

theorem chainLeft_lt (c : UInt32) : chainLeft c < 4294967296 := Nat.mod_lt _ (by decide)

/-- `limit_base` of `LONGEST_MATCH`. -/
def limitBase (st : DeflateState) : UInt32 :=
  if st.strstart > MAX_DIST st then st.strstart - MAX_DIST st else 0

/-- The numeric facts of the layout and the state that `LONGEST_MATCH` needs. -/
structure LN (d : Array UInt8) (wo po ho : Nat) (st : DeflateState) : Prop where
  w_lo : 512 ≤ st.w_size.toNat
  w_hi : st.w_size.toNat ≤ 32768
  ss_le : st.strstart.toNat ≤ 65536
  la_le : st.lookahead.toNat ≤ 65536
  look : st.strstart.toNat + st.lookahead.toNat ≤ 65536 + 512
  big : wo + 131400 ≤ d.size
  pw : po + 2 * st.w_size.toNat ≤ d.size
  hd : ho + 131072 ≤ d.size

/-- Every `prev` entry is 0 or below the bound `B` (at most 65536). -/
def PrevBelow (d : Array UInt8) (po : Nat) (st : DeflateState) (B : Nat) : Prop :=
  B ≤ 65536 ∧ ∀ k, k < st.w_size.toNat → (rd2 d (po + 2 * k)).toNat = 0 ∨ (rd2 d (po + 2 * k)).toNat < B

/-- Every `prev` entry is below 65536: `PrevBelow` with the bound 65536 holds of every state. -/
theorem prevBelow_65536 (d : Array UInt8) (po : Nat) (st : DeflateState) : PrevBelow d po st 65536 :=
  ⟨Nat.le_refl _, fun _ _ => Or.inr (UInt16.toNat_lt _)⟩

/-- The chain closure of a set `Ch` of candidate positions: for every candidate `c` of `Ch` at or above `limit_base`,
the `prev` entry `prev[c & w_mask]` that `GOTO_NEXT_CHAIN` reads next is 0 or in `Ch`. With `Ch` the positions of the
hash chains (`ChainOk`) this is clause (C3); `Ch = fun _ => True` holds of every state (`prevCh_true`). -/
def PrevCh (d : Array UInt8) (po : Nat) (st : DeflateState) (Ch : Nat → Prop) : Prop :=
  ∀ c : UInt32, Ch c.toNat → (limitBase st).toNat ≤ c.toNat →
    (rd2 d (po + 2 * (c &&& (st.w_size - 1)).toNat)).toNat = 0 ∨
      Ch (rd2 d (po + 2 * (c &&& (st.w_size - 1)).toNat)).toNat

theorem prevCh_true (d : Array UInt8) (po : Nat) (st : DeflateState) : PrevCh d po st (fun _ => True) :=
  fun _ _ _ => Or.inr trivial

theorem limitBase_le (st : DeflateState) (hw : 512 ≤ st.w_size.toNat) :
    (limitBase st).toNat ≤ st.strstart.toNat ∧
      st.strstart.toNat ≤ (limitBase st).toNat + (MAX_DIST st).toNat := by
  have hm : (MAX_DIST st).toNat = st.w_size.toNat - 262 := by
    unfold MAX_DIST MIN_LOOKAHEAD STD_MAX_MATCH STD_MIN_MATCH
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; rfl
  unfold limitBase
  split
  · rename_i hg
    have hg' : (MAX_DIST st).toNat < st.strstart.toNat := UInt32.lt_iff_toNat_lt.mp hg
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]; omega
  · rename_i hg
    have hg' : st.strstart.toNat ≤ (MAX_DIST st).toNat := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hg)
    simp only [UInt32.toNat_zero]; omega

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- The heap during `LONGEST_MATCH`: only `match_start` changed. -/
abbrev LH (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (ms : UInt32) : Heap :=
  SH H i z b { st with match_start := ms } d

theorem LH_get (ms : UInt32) : Space.get (LH H i z b st d ms) (BRef.heap b) = some d :=
  SH_bytes H i z b _ d

theorem sat_load_v {H0 : Heap} {r : BRef} {a : Array UInt8} {k : Nat} (hb : Space.get H0 r = some a)
    (hk : k < a.size) : Sat H0 (Ptr.load (.ref r k) : M UInt8) (fun v H' => H' = H0 ∧ v = a[k]!) :=
  ⟨a[k], H0, by simp [Ptr.load, hb, hk], rfl, by simp [hk]⟩

theorem index8_v {H0 : Heap} {r : BRef} {a : Array UInt8} {off : Nat} (hb : Space.get H0 r = some a) (j : Nat)
    (hk : off + j < a.size) : Sat H0 (index8 (.ref r off) (j : Int)) (fun v H' => H' = H0 ∧ v = a[off + j]!) := by
  unfold index8 Ptr.index
  refine Sat.bind (Sat.mono (sat_add hb (by omega) _ (off + j) (by omega) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  exact sat_load_v hb hk

theorem sat_add' {H0 : Heap} {r : BRef} {a : Array UInt8} {off : Nat} {p : BPtr} (hp : p = .ref r off)
    (hb : Space.get H0 r = some a) (ho : off ≤ a.size) (k : Int) (m : Nat) (hm : (off : Int) + k = m)
    (hmN : m ≤ a.size) : Sat H0 (Ptr.add p k) (fun p H' => p = .ref r m ∧ H' = H0) := by
  subst hp; exact sat_add hb ho k m hm hmN

theorem posLoad_v {H0 : Heap} {po : Nat} (hb : Space.get H0 (BRef.heap b) = some d) (k : Nat)
    (hk : po + 2 * k + 2 ≤ d.size) :
    Sat H0 (posLoad (.ref (.heap b) po) (k : Int)) (fun v H' => H' = H0 ∧ v = rd2 d (po + 2 * k)) := by
  unfold posLoad memread2
  refine Sat.bind (Sat.mono (sat_add hb (by omega) (2 * (k : Int)) (po + 2 * k) (by omega) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (index8_v hb 0 (by omega)) ?_)
  rintro v0 _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (index8_v hb 1 (by omega)) ?_)
  rintro v1 _ ⟨rfl, rfl⟩
  exact Sat.pure ⟨rfl, rfl⟩

end

/-- The environment of `LONGEST_MATCH` after its prologue. -/
structure LE (b wo po ho : Nat) (st : DeflateState) (e : LMEnv) : Prop where
  hst : e.st = some b
  wmask : e.wmask = st.w_size - 1
  strstart : e.strstart = st.strstart
  prev : e.prev = .ref (.heap b) po
  head : e.slow = true → e.head = .ref (.heap b) ho
  scan : e.scan = .ref (.heap b) (wo + st.strstart.toNat)
  lookahead : e.lookahead = st.lookahead
  lb : e.limit_base = limitBase st
  osr : e.offset_search = true → e.slow = true

/-- A written `match_start`: a candidate with `limit_base <= match_start < B`. -/
def MSOk (st : DeflateState) (B : Nat) (ms : UInt32) : Prop :=
  (limitBase st).toNat ≤ ms.toNat ∧ ms.toNat < B

/-- The invariant of the mutable locals between steps. -/
structure VI (b wo : Nat) (st : DeflateState) (v : LMVars) : Prop where
  ms : v.mbase_start = .ref (.heap b) wo
  me : v.mbase_end = .ref (.heap b) (wo + v.offset.toNat)
  off : v.offset.toNat ≤ v.best_len.toNat
  bl : v.best_len.toNat ≤ 65536
  cur : v.cur_match.toNat < 65536
  mo : v.match_offset.toNat ≤ 65536
  lim : v.limit.toNat = (limitBase st).toNat + v.match_offset.toNat
  le : v.limit.toNat ≤ v.cur_match.toNat

/-- `best_len` is the initial `bl0`, or a longer match within the lookahead whose start was written. -/
def BL (st : DeflateState) (B : Nat) (bl0 : Nat) (best ms : UInt32) : Prop :=
  best.toNat = bl0 ∨ (bl0 < best.toNat ∧ best.toNat < st.lookahead.toNat ∧ best.toNat ≤ 258 ∧ MSOk st B ms)

/-- The result `r` of `LONGEST_MATCH` with `match_start = ms`. -/
def PR (st : DeflateState) (B : Nat) (bl0 : Nat) (r ms : UInt32) : Prop :=
  r.toNat ≤ bl0 ∨ (r.toNat ≤ st.lookahead.toNat ∧ r.toNat ≤ 258 ∧ MSOk st B ms)

theorem BL.pr {st : DeflateState} {bl0 : Nat} {best ms : UInt32} (h : BL st B bl0 best ms) : PR st B bl0 best ms := by
  rcases h with h | ⟨_, h2, h3, h4⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, h3, h4⟩

/-- `BL` with a written `match_start` in the candidate set `Ch`. -/
def BLC (st : DeflateState) (B : Nat) (Ch : Nat → Prop) (bl0 : Nat) (best ms : UInt32) : Prop :=
  BL st B bl0 best ms ∧ (bl0 < best.toNat → Ch ms.toNat)

/-- `PR` with a written `match_start` in the candidate set `Ch`. -/
def PRC (st : DeflateState) (B : Nat) (Ch : Nat → Prop) (bl0 : Nat) (r ms : UInt32) : Prop :=
  PR st B bl0 r ms ∧ (bl0 < r.toNat → Ch ms.toNat)

theorem BLC.pr {st : DeflateState} {Ch : Nat → Prop} {bl0 : Nat} {best ms : UInt32} (h : BLC st B Ch bl0 best ms) :
    PRC st B Ch bl0 best ms := ⟨h.1.pr, h.2⟩

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem prev_idx {e : LMEnv} {wo po ho : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st) (x : UInt32) :
    (x &&& e.wmask).toNat < st.w_size.toNat := by
  rw [E.wmask]; exact mask_lt x st.w_size (by have := N.w_lo; omega)

/-- `GOTO_NEXT_CHAIN`: `chain_length` drops by one; on `continue` the new candidate is a `prev` entry above
`limit`, hence (`PrevBelow`) below `B`. -/
theorem goto_ok {e : LMEnv} {v : LMVars} {wo po ho : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st)
    (hp : PrevBelow d po st B) {Ch : Nat → Prop} (hpc : PrevCh d po st Ch) (hcur : v.cur_match.toNat < 65536)
    (hch : Ch v.cur_match.toNat) (hlb : (limitBase st).toNat ≤ v.cur_match.toNat) (ms : UInt32) :
    Sat (LH H i z b st d ms) (LM.GOTO_NEXT_CHAIN e v) (fun rv H' => H' = LH H i z b st d ms ∧
      rv.2 = { v with chain_length := v.chain_length - 1, cur_match := rv.2.cur_match } ∧
      rv.2.cur_match.toNat < 65536 ∧
      (rv.1 = none → v.chain_length - 1 ≠ 0 ∧ v.limit < rv.2.cur_match ∧
        rv.2.cur_match.toNat < B ∧ Ch rv.2.cur_match.toNat) ∧
      (∀ x, rv.1 = some x → x = v.best_len)) := by
  unfold LM.GOTO_NEXT_CHAIN
  dsimp only
  by_cases hc : (v.chain_length - 1 != 0) = true
  · simp only [hc, ↓reduceIte, E.prev]
    have hk := prev_idx E N v.cur_match
    have hq := hpc v.cur_match hch hlb
    rw [← E.wmask] at hq
    refine Sat.bind (Sat.mono (posLoad_v (LH_get ms) _ (by have := N.pw; omega)) ?_)
    rintro p _ ⟨rfl, rfl⟩
    have hpv : (rd2 d (po + 2 * (v.cur_match &&& e.wmask).toNat)).toUInt32.toNat < 65536 := by
      rw [UInt16.toNat_toUInt32]; exact UInt16.toNat_lt _
    split
    · rename_i hg
      have hg' := UInt32.lt_iff_toNat_lt.mp hg
      rw [UInt16.toNat_toUInt32] at hg'
      refine Sat.pure ⟨rfl, rfl, hpv, fun _ => ⟨by simpa using hc, hg, ?_, ?_⟩, fun x hx => by simp at hx⟩
      · rw [UInt16.toNat_toUInt32]
        rcases hp.2 _ hk with h0 | h0
        · exfalso; omega
        · exact h0
      · rw [UInt16.toNat_toUInt32]
        rcases hq with h0 | h0
        · exfalso; omega
        · exact h0
    · exact Sat.pure ⟨rfl, rfl, hpv, fun hx => by simp at hx, fun x hx => by simp at hx; exact hx.symm⟩
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact Sat.pure ⟨rfl, rfl, hcur, fun hx => by simp at hx, fun x hx => by simp at hx; exact hx.symm⟩

end

/-- A candidate below `B`, in the candidate set `Ch`, at or above `limit` (so `cur_match - match_offset` does not
wrap). -/
def CurOk (B : Nat) (Ch : Nat → Prop) (v v' : LMVars) : Prop :=
  v'.cur_match.toNat < B ∧ v.limit.toNat ≤ v'.cur_match.toNat ∧ Ch v'.cur_match.toNat

/-- How a candidate filter that started from `v` may end in `v'`. -/
def SelTail (B : Nat) (Ch : Nat → Prop) (v : LMVars) : LMSel → LMVars → Prop
  | .ret x, _ => x = v.best_len
  | .accept len, v' => v.best_len < len ∧ len.toNat ≤ 8 ∧ CurOk B Ch v v' ∧
      chainLeft v'.chain_length ≤ chainLeft v.chain_length
  | .compare, v' => CurOk B Ch v v' ∧ chainLeft v'.chain_length ≤ chainLeft v.chain_length

/-- A candidate filter changes only `chain_length` and `cur_match`. -/
def SelOk (B : Nat) (Ch : Nat → Prop) (v : LMVars) (sel : LMSel) (v' : LMVars) : Prop :=
  v' = { v with chain_length := v'.chain_length, cur_match := v'.cur_match } ∧ SelTail B Ch v sel v'

theorem xor_ne {a c : UInt64} (h : a ≠ c) : a ^^^ c ≠ 0 := fun e => h (by
  have := congrArg (· ^^^ c) e
  simpa [UInt64.xor_assoc, UInt64.xor_self] using this)

theorem sub_mo {v : LMVars} {lb : Nat} (hl : v.limit.toNat = lb + v.match_offset.toNat)
    (hle : v.limit.toNat ≤ v.cur_match.toNat) :
    (v.cur_match - v.match_offset).toNat = v.cur_match.toNat - v.match_offset.toNat :=
  UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- The walk over the remaining short candidates (`match_tpl.h:169-180`). -/
theorem short_walk_ok {e : LMEnv} {v : LMVars} {fm c : UInt64} {wo po ho : Nat}
    (E : LE b wo po ho st e) (N : LN d wo po ho st) (hp : PrevBelow d po st B) {Ch : Nat → Prop}
    (hpc : PrevCh d po st Ch) (V : VI b wo st v)
    (hbl : v.best_len.toNat + 1 ≤ 8) (hfm : fm.toNat = 2 ^ (8 * (v.best_len.toNat + 1)) - 1)
    (hc : e.scan_start ≠ c) (hcur : CurOk B Ch v v) (ms : UInt32) :
    Sat (LH H i z b st d ms) (LM.short_walk e fm v c)
      (fun sv H' => H' = LH H i z b st d ms ∧ SelOk B Ch v sv.1 sv.2) := by
  unfold LM.short_walk
  refine Sat.bind (Sat.mono (sat_cwhile
    (fun (s : LMVars × UInt64 × Option LMSel) H' => H' = LH H i z b st d ms ∧
      s.1 = { v with chain_length := s.1.chain_length, cur_match := s.1.cur_match } ∧
      (match s.2.2 with
       | none => e.scan_start ≠ s.2.1 ∧ CurOk B Ch v s.1 ∧ chainLeft s.1.chain_length ≤ chainLeft v.chain_length
       | some sel => SelTail B Ch v sel s.1))
    (fun s => if s.2.2.isNone then 1 + chainLeft s.1.chain_length else 0)
    (fun s H' => H' = LH H i z b st d ms ∧ ∃ sel, s.2.2 = some sel ∧ SelOk B Ch v sel s.1)
    ?_ ⟨rfl, rfl, hc, hcur, Nat.le_refl _⟩
    (by have := chainLeft_lt v.chain_length; simp [fuel]; omega)) ?_)
  rotate_left
  · rintro ⟨v1, c1, r⟩ _ ⟨rfl, sel, hs, hok⟩
    simp only at hs; subst hs
    exact Sat.pure ⟨rfl, hok⟩
  rintro ⟨v1, c1, r⟩ _ ⟨rfl, hv1, hr⟩
  refine Sat.pure ⟨fun ht => ?_, fun hf => ?_⟩
  rotate_left
  · cases r with
    | none => simp at hf
    | some sel => exact ⟨rfl, sel, rfl, hv1, hr⟩
  cases r with
  | some sel => simp at ht
  | none =>
  obtain ⟨hne, hco, hch⟩ := hr
  simp only at hv1 hne hco hch
  have hb1 : v1.best_len = v.best_len := by rw [hv1]
  have hl1 : v1.limit = v.limit := by rw [hv1]
  have hm1 : v1.match_offset = v.match_offset := by rw [hv1]
  have hs1 : v1.mbase_start = v.mbase_start := by rw [hv1]
  dsimp only
  split
  · rename_i hz
    refine Sat.bind (Sat.mono (short_len_gt (H := LH H i z b st d ms) _ fm v.best_len.toNat hbl (xor_ne hne) hfm hz) ?_)
    rintro len _ ⟨rfl, h1, h2⟩
    refine Sat.pure ⟨⟨rfl, hv1, UInt32.lt_iff_toNat_lt.mpr h1, h2, hco, hch⟩, by simp <;> omega⟩
  · rename_i hz
    split
    · rename_i h0
      refine Sat.pure ⟨⟨rfl, by rw [hv1], by simp only [SelTail]; rw [hb1]⟩, by simp <;> omega⟩
    · rename_i h0
      have h0' : v1.chain_length - 1 ≠ 0 := by simpa using h0
      have hdec := chainLeft_dec _ h0'
      have hk := prev_idx E N v1.cur_match
      have hq := hpc v1.cur_match hco.2.2 (by have := V.lim; have := hco.2.1; omega)
      rw [← E.wmask] at hq
      rw [E.prev]
      refine Sat.bind (Sat.mono (posLoad_v (LH_get ms) _ (by have := N.pw; omega)) ?_)
      rintro p _ ⟨rfl, rfl⟩
      split
      · refine Sat.pure ⟨⟨rfl, by rw [hv1], by simp only [SelTail]; rw [hb1]⟩, by simp <;> omega⟩
      · rename_i hgt
        simp only [UInt32.not_le] at hgt
        rw [hl1] at hgt
        have hgt' := UInt32.lt_iff_toNat_lt.mp hgt
        rw [UInt16.toNat_toUInt32] at hgt'
        have hlt : (rd2 d (po + 2 * (v1.cur_match &&& e.wmask).toNat)).toNat < B := by
          rcases hp.2 _ hk with h | h
          · omega
          · exact h
        have hqc : Ch (rd2 d (po + 2 * (v1.cur_match &&& e.wmask).toNat)).toNat := by
          rcases hq with h | h
          · omega
          · exact h
        have hB := hp.1
        have hle2 : v1.match_offset.toNat ≤ (rd2 d (po + 2 * (v1.cur_match &&& e.wmask).toNat)).toNat := by
          have := V.lim; rw [hm1]; omega
        have hsub : ((rd2 d (po + 2 * (v1.cur_match &&& e.wmask).toNat)).toUInt32 - v1.match_offset).toNat =
            (rd2 d (po + 2 * (v1.cur_match &&& e.wmask).toNat)).toNat - v1.match_offset.toNat := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, UInt16.toNat_toUInt32]; omega),
            UInt16.toNat_toUInt32]
        have hst := N.look
        refine Sat.bind (Sat.mono (sat_add' (hs1.trans V.ms) (LH_get ms) (by have := N.big; omega) _
          (wo + ((rd2 d (po + 2 * (v1.cur_match &&& e.wmask).toNat)).toNat - v1.match_offset.toNat))
          (by rw [hsub]; omega) (by have := N.big; omega)) ?_)
        rintro _ _ ⟨rfl, rfl⟩
        refine Sat.bind (Sat.mono (sat_memread8 (LH_get ms) (by have := N.big; omega)) ?_)
        rintro c2 _ rfl
        generalize hq : rd2 d (po + 2 * (v1.cur_match &&& e.wmask).toNat) = q at *
        have hco2 : CurOk B Ch v { v1 with chain_length := v1.chain_length - 1, cur_match := q.toUInt32 } :=
          ⟨by simp only [UInt16.toNat_toUInt32]; exact hlt, by simp only [UInt16.toNat_toUInt32]; omega,
            by simp only [UInt16.toNat_toUInt32]; exact hqc⟩
        have hv2 : ({ v1 with chain_length := v1.chain_length - 1, cur_match := q.toUInt32 } : LMVars) =
            { v with chain_length := v1.chain_length - 1, cur_match := q.toUInt32 } := by
          rw [hv1]
        have hch2 : chainLeft (v1.chain_length - 1) ≤ chainLeft v.chain_length := by omega
        split
        · exact Sat.pure ⟨⟨rfl, hv2, hco2, hch2⟩, by simp <;> omega⟩
        · rename_i hq
          exact Sat.pure ⟨⟨rfl, hv2, fun e2 => hq (by simp [e2]), hco2, hch2⟩, by simp <;> omega⟩

theorem VI.upd {wo : Nat} {v : LMVars} (V : VI b wo st v) (c u : UInt32) (hu : u.toNat < 65536)
    (hle : v.limit.toNat ≤ u.toNat) : VI b wo st { v with chain_length := c, cur_match := u } :=
  { V with cur := hu, le := hle }

/-- A filter run from the state `v'` that `v` reached by a chain step is a filter run from `v`. -/
theorem SelOk.trans {Ch : Nat → Prop} {v v' v3 : LMVars} {sel : LMSel}
    (h' : v' = { v with chain_length := v'.chain_length, cur_match := v'.cur_match }) (hc : chainLeft v'.chain_length ≤ chainLeft v.chain_length)
    (h : SelOk B Ch v' sel v3) : SelOk B Ch v sel v3 := by
  obtain ⟨h3, ht⟩ := h
  have e1 : v'.best_len = v.best_len := by rw [h']
  have e2 : v'.limit = v.limit := by rw [h']
  refine ⟨by rw [h3, h'], ?_⟩
  cases sel with
  | ret x => simp only [SelTail] at ht ⊢; rw [ht, e1]
  | accept len =>
    obtain ⟨a1, a2, ⟨a3, a4, a6⟩, a5⟩ := ht
    exact ⟨by rw [← e1]; exact a1, a2, ⟨a3, by rw [← e2]; exact a4, a6⟩, by omega⟩
  | compare =>
    obtain ⟨⟨a3, a4, a6⟩, a5⟩ := ht
    exact ⟨⟨a3, by rw [← e2]; exact a4, a6⟩, by omega⟩

/-- The candidate filter for `best_len < 8` (`match_tpl.h:150-183`). -/
theorem short_filter_ok {e : LMEnv} {v : LMVars} {wo po ho : Nat}
    (E : LE b wo po ho st e) (N : LN d wo po ho st) (hp : PrevBelow d po st B) {Ch : Nat → Prop}
    (hpc : PrevCh d po st Ch) (V : VI b wo st v)
    (hbl : v.best_len.toNat < 8) (hcur : CurOk B Ch v v) (ms : UInt32) :
    Sat (LH H i z b st d ms) (LM.short_filter e v)
      (fun sv H' => H' = LH H i z b st d ms ∧ SelOk B Ch v sv.1 sv.2) := by
  have hB := hp.1
  unfold LM.short_filter
  have hsub := sub_mo V.lim V.le
  have hst := N.look
  have hbig := N.big
  have hcl := hcur.1
  refine Sat.bind (Sat.mono (sat_add' V.ms (LH_get ms) (by omega) _ (wo + (v.cur_match - v.match_offset).toNat)
    (by omega) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_memread8 (LH_get ms) (by omega)) ?_)
  rintro c0 _ rfl
  have hself : v = { v with chain_length := v.chain_length, cur_match := v.cur_match } := rfl
  split
  · rename_i hne
    have hne' : e.scan_start ≠ c0 := by simpa using hne
    have hb1 : (v.best_len + 1).toNat = v.best_len.toNat + 1 := by
      rw [UInt32.toNat_add]; simp; omega
    refine Sat.bind (Sat.mono (mask_ok (v.best_len + 1) (by omega) (by omega)) ?_)
    rintro fm _ ⟨rfl, hfm⟩
    rw [hb1] at hfm
    dsimp only
    split
    · rename_i hz
      refine Sat.bind (Sat.mono (short_len_gt _ fm v.best_len.toNat (by omega) (xor_ne hne') hfm hz) ?_)
      rintro len _ ⟨rfl, h1, h2⟩
      exact Sat.pure ⟨rfl, hself, UInt32.lt_iff_toNat_lt.mpr h1, h2, hcur, Nat.le_refl _⟩
    · split
      · exact Sat.pure ⟨rfl, rfl, rfl⟩
      · rename_i h0
        have h0' : v.chain_length - 1 ≠ 0 := by simpa using h0
        have hdec := chainLeft_dec _ h0'
        have hk := prev_idx E N v.cur_match
        have hqc0 := hpc v.cur_match hcur.2.2 (by have := V.lim; have := V.le; omega)
        rw [← E.wmask] at hqc0
        rw [E.prev]
        refine Sat.bind (Sat.mono (posLoad_v (LH_get ms) _ (by have := N.pw; omega)) ?_)
        rintro p _ ⟨rfl, rfl⟩
        generalize hq : rd2 d (po + 2 * (v.cur_match &&& e.wmask).toNat) = q at *
        split
        · exact Sat.pure ⟨rfl, rfl, rfl⟩
        · rename_i hgt
          simp only [UInt32.not_le] at hgt
          have hgt' := UInt32.lt_iff_toNat_lt.mp hgt
          rw [UInt16.toNat_toUInt32] at hgt'
          have hlt : q.toNat < B := by
            rcases hp.2 _ hk with h | h
            · rw [hq] at h; omega
            · rw [hq] at h; exact h
          have hB := hp.1
          have hle2 : v.match_offset.toNat ≤ q.toNat := by have := V.lim; omega
          have hsub2 : (q.toUInt32 - v.match_offset).toNat = q.toNat - v.match_offset.toNat := by
            rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, UInt16.toNat_toUInt32]; omega),
              UInt16.toNat_toUInt32]
          refine Sat.bind (Sat.mono (sat_add' V.ms (LH_get ms) (by omega) _
            (wo + (q.toNat - v.match_offset.toNat)) (by rw [hsub2]; omega) (by omega)) ?_)
          rintro _ _ ⟨rfl, rfl⟩
          refine Sat.bind (Sat.mono (sat_memread8 (LH_get ms) (by omega)) ?_)
          rintro c2 _ rfl
          have hv2 : ({ v with chain_length := v.chain_length - 1, cur_match := q.toUInt32 } : LMVars) =
              { v with chain_length := v.chain_length - 1, cur_match := q.toUInt32 } := rfl
          have hqc : Ch q.toNat := by
            rcases hqc0 with h | h
            · omega
            · exact h
          have hco2 : CurOk B Ch v { v with chain_length := v.chain_length - 1, cur_match := q.toUInt32 } :=
            ⟨by simp only [UInt16.toNat_toUInt32]; exact hlt, by simp only [UInt16.toNat_toUInt32]; omega,
              by simp only [UInt16.toNat_toUInt32]; exact hqc⟩
          split
          · rename_i hne2
            have V2 := V.upd (v.chain_length - 1) q.toUInt32 (by simp only [UInt16.toNat_toUInt32]; omega)
              (by simp only [UInt16.toNat_toUInt32]; omega)
            refine Sat.mono (short_walk_ok E N hp hpc V2 (by simp only []; omega) hfm (by simpa using hne2)
              ⟨hco2.1, hco2.2.1, hco2.2.2⟩ ms) ?_
            rintro ⟨sel, v3⟩ _ ⟨rfl, hs⟩
            exact ⟨rfl, SelOk.trans hv2 (by simp only []; omega) hs⟩
          · exact Sat.pure ⟨rfl, hv2, hco2, by simp only []; omega⟩
  · exact Sat.pure ⟨rfl, hself, hcur, Nat.le_refl _⟩

/-- The filter for `best_len >= 8` (`match_tpl.h:187-194`): the end and start sentinels of each candidate, then
`GOTO_NEXT_CHAIN`. -/
theorem long_filter_ok {e : LMEnv} {v : LMVars} {wo po ho : Nat}
    (E : LE b wo po ho st e) (N : LN d wo po ho st) (hp : PrevBelow d po st B) {Ch : Nat → Prop}
    (hpc : PrevCh d po st Ch) (V : VI b wo st v)
    (hcur : CurOk B Ch v v) (ms : UInt32) :
    Sat (LH H i z b st d ms) (LM.long_filter e v)
      (fun sv H' => H' = LH H i z b st d ms ∧ SelOk B Ch v sv.1 sv.2) := by
  have hB := hp.1
  unfold LM.long_filter
  have hst := N.look
  have hbig := N.big
  have hoff := V.off
  have hbl := V.bl
  refine Sat.bind (Sat.mono (sat_cwhile
    (fun (s : LMVars × Option LMSel) H' => H' = LH H i z b st d ms ∧
      s.1 = { v with chain_length := s.1.chain_length, cur_match := s.1.cur_match } ∧
      (match s.2 with
       | none => CurOk B Ch v s.1 ∧ chainLeft s.1.chain_length ≤ chainLeft v.chain_length
       | some sel => SelTail B Ch v sel s.1))
    (fun s => if s.2.isNone then 1 + chainLeft s.1.chain_length else 0)
    (fun s H' => H' = LH H i z b st d ms ∧ ∃ sel, s.2 = some sel ∧ SelOk B Ch v sel s.1)
    ?_ ⟨rfl, rfl, hcur, Nat.le_refl _⟩
    (by have := chainLeft_lt v.chain_length; simp [fuel]; omega)) ?_)
  rotate_left
  · rintro ⟨v1, r⟩ _ ⟨rfl, sel, hs, hok⟩
    simp only at hs; subst hs
    exact Sat.pure ⟨rfl, hok⟩
  rintro ⟨v1, r⟩ _ ⟨rfl, hv1, hr⟩
  refine Sat.pure ⟨fun ht => ?_, fun hf => ?_⟩
  rotate_left
  · cases r with
    | none => simp at hf
    | some sel => exact ⟨rfl, sel, rfl, hv1, hr⟩
  cases r with
  | some sel => simp at ht
  | none =>
  obtain ⟨hco, hch⟩ := hr
  simp only at hv1 hco hch
  have hb1 : v1.best_len = v.best_len := by rw [hv1]
  have hl1 : v1.limit = v.limit := by rw [hv1]
  have hm1 : v1.match_offset = v.match_offset := by rw [hv1]
  have ho1 : v1.offset = v.offset := by rw [hv1]
  have hs1 : v1.mbase_start = v.mbase_start := by rw [hv1]
  have he1 : v1.mbase_end = v.mbase_end := by rw [hv1]
  have hle1 : v1.limit.toNat ≤ v1.cur_match.toNat := by rw [hl1]; exact hco.2.1
  have hsub := sub_mo (v := v1) (lb := (limitBase st).toNat) (by rw [hl1, hm1]; exact V.lim) hle1
  have hcl := hco.1
  have hmo : v1.match_offset.toNat ≤ v1.cur_match.toNat := by have := V.lim; rw [hl1] at hle1; rw [hm1]; omega
  -- the `GOTO_NEXT_CHAIN` that ends a rejected candidate
  have G : Sat (LH H i z b st d ms) (do
      let (x, v) ← LM.GOTO_NEXT_CHAIN e v1
      match x with
      | none => return (v, none)
      | some b => return (v, some (LMSel.ret b)))
      (fun s2 H2 => (H2 = LH H i z b st d ms ∧
        s2.1 = { v with chain_length := s2.1.chain_length, cur_match := s2.1.cur_match } ∧
        (match s2.2 with
         | none => CurOk B Ch v s2.1 ∧ chainLeft s2.1.chain_length ≤ chainLeft v.chain_length
         | some sel => SelTail B Ch v sel s2.1)) ∧
        (if s2.2.isNone then 1 + chainLeft s2.1.chain_length else 0) <
          (if (none : Option LMSel).isNone then 1 + chainLeft v1.chain_length else 0)) := by
    have hlb1 : (limitBase st).toNat ≤ v1.cur_match.toNat := by have := V.lim; rw [hl1] at hle1; omega
    refine Sat.bind (Sat.mono (goto_ok E N hp hpc (by rw [hv1]; simp only []; omega) hco.2.2 hlb1 ms) ?_)
    rintro ⟨x, v2⟩ _ ⟨rfl, h2, h2c, hn, hs⟩
    simp only at h2 h2c hn hs
    have hv2 : v2 = { v with chain_length := v2.chain_length, cur_match := v2.cur_match } := by
      rw [h2]; simp only []; rw [hv1]
    cases x with
    | none =>
      obtain ⟨h0, hgt, hlt, hcq⟩ := hn rfl
      have hdec := chainLeft_dec _ h0
      have hc2 : v2.chain_length = v1.chain_length - 1 := by rw [h2]
      have hgt' := UInt32.lt_iff_toNat_lt.mp hgt
      rw [hl1] at hgt'
      refine Sat.pure ⟨⟨rfl, hv2, ⟨hlt, Nat.le_of_lt hgt', hcq⟩, by rw [hc2]; omega⟩, by simp only [Option.isNone_none]; rw [hc2]; simp <;> omega⟩
    | some x =>
      have := hs x rfl
      refine Sat.pure ⟨⟨rfl, hv2, by simp only [SelTail]; rw [this, hb1]⟩, by simp <;> omega⟩
  have hme : v1.mbase_end = .ref (.heap b) (wo + v1.offset.toNat) := by rw [he1, ho1]; exact V.me
  dsimp only
  unfold zng_memcmp_8_local
  refine Sat.bind (Sat.mono (sat_add' hme (LH_get (H := H) (i := i) (z := z) (st := st) (d := d) ms) (by rw [ho1]; omega) _
    (wo + v1.offset.toNat + (v1.cur_match - v1.match_offset).toNat) (by omega) (by rw [ho1, hsub]; omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.bind (Sat.mono (sat_memread8 (LH_get (H := H) (i := i) (z := z) (st := st) (d := d) ms) (by rw [ho1, hsub]; omega)) (fun a1 _ h1 => ?_)))
  subst h1
  refine Sat.pure ?_
  split
  · split
    · rename_i h; exact absurd h (by decide)
    · exact G
  split
  rotate_left
  · rename_i h; exact absurd h (by decide)
  refine Sat.bind (Sat.mono (sat_add' (hs1.trans V.ms) (LH_get (H := H) (i := i) (z := z) (st := st) (d := d) ms)
    (by omega) _ (wo + (v1.cur_match - v1.match_offset).toNat) (by omega) (by rw [hsub]; omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.bind (Sat.mono (sat_memread8 (LH_get (H := H) (i := i) (z := z) (st := st) (d := d) ms)
    (by rw [hsub]; omega)) (fun a2 _ h2 => ?_)))
  subst h2
  refine Sat.pure ?_
  split
  · split
    · rename_i h; exact absurd h (by decide)
    · exact G
  exact Sat.pure ⟨⟨rfl, hv1, ⟨hcl, by rw [← hl1]; exact hle1, hco.2.2⟩, hch⟩, by simp <;> omega⟩

end

/-! ## The outer loop -/

/-- The invariant of the outer `for (;;)` with the candidate set `Ch`: only `match_start` changed in the heap; a
running loop has `VI`, `BLC`, its candidate in `Ch`, and `match_offset = 0` unless `Ch` holds of every position;
`break` keeps `BLC`; a `return r` has `PRC`. -/
def LI (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (B : Nat) (Ch : Nat → Prop) (d : Array UInt8)
    (wo bl0 : Nat) (s : LMExit × LMVars) (H' : Heap) : Prop :=
  ∃ ms, H' = LH H i z b st d ms ∧
    (match s.1 with
     | .cont => VI b wo st s.2 ∧ BLC st B Ch bl0 s.2.best_len ms ∧ Ch s.2.cur_match.toNat ∧
        (s.2.match_offset = 0 ∨ ∀ n, Ch n)
     | .brk => BLC st B Ch bl0 s.2.best_len ms
     | .ret r => PRC st B Ch bl0 r ms)

/-- The measure of the outer loop. -/
def lmMu (s : LMExit × LMVars) : Nat :=
  if s.1.isCont then 1 + chainLeft s.2.chain_length * 131072 + (131072 - s.2.best_len.toNat) else 0

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- `GOTO_NEXT_CHAIN` at `match_tpl.h:294`. -/
theorem goto_outer_ok {e : LMEnv} {v : LMVars} {wo po ho bl0 : Nat} (E : LE b wo po ho st e)
    (N : LN d wo po ho st) (hp : PrevBelow d po st B) {Ch : Nat → Prop} (hpc : PrevCh d po st Ch)
    (V : VI b wo st v) (hcc : Ch v.cur_match.toNat) (hmo : v.match_offset = 0 ∨ ∀ n, Ch n) {ms : UInt32}
    (hb : BLC st B Ch bl0 v.best_len ms) :
    Sat (LH H i z b st d ms) (LM.goto_next_chain_outer e v) (fun s H' => LI H i z b st B Ch d wo bl0 s H' ∧
      (s.1.isCont = true → chainLeft s.2.chain_length < chainLeft v.chain_length ∧ s.2.best_len = v.best_len)) := by
  unfold LM.goto_next_chain_outer
  refine Sat.bind (Sat.mono (goto_ok E N hp hpc V.cur hcc (by have := V.lim; have := V.le; omega) ms) ?_)
  rintro ⟨x, v2⟩ _ ⟨rfl, h2, h2c, hn, hs⟩
  simp only at h2 h2c hn hs
  cases x with
  | none =>
    obtain ⟨h0, hgt, hlt, hcq⟩ := hn rfl
    have hdec := chainLeft_dec _ h0
    have hgt' := UInt32.lt_iff_toNat_lt.mp hgt
    have hc2 : v2.chain_length = v.chain_length - 1 := by rw [h2]
    have hb2 : v2.best_len = v.best_len := by rw [h2]
    have hm2 : v2.match_offset = v.match_offset := by rw [h2]
    have V2 := V.upd (v.chain_length - 1) v2.cur_match h2c (Nat.le_of_lt hgt')
    rw [← h2] at V2
    refine Sat.pure ⟨⟨ms, rfl, V2, by rw [hb2]; exact hb, hcq, by rw [hm2]; exact hmo⟩,
      fun _ => ⟨by rw [hc2]; omega, hb2⟩⟩
  | some x =>
    refine Sat.pure ⟨⟨ms, rfl, by simp only []; rw [hs x rfl]; exact hb.pr⟩, fun h => absurd h (by simp [LMExit.isCont])⟩

/-- The walk over `prev` of the offset search (`match_tpl.h:237-249`): positions `cm + i`, `i <= bound`; a more
distant chain head `pos` replaces `next_pos` with `match_offset = i`, or ends the search when it is at or below
`limit_base + i`. -/
theorem os_walk_ok {e : LMEnv} {wo po ho : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st)
    (cm bound best : UInt32) (hcm : cm.toNat < 65536) (hb : bound.toNat ≤ 255) (hlb : (limitBase st).toNat ≤ cm.toNat)
    (ms : UInt32) :
    Sat (LH H i z b st d ms) (cwhile
      (fun ((i, np, mo, r) : UInt32 × UInt32 × UInt32 × Option UInt32) => pure (r.isNone && i <= bound, (i, np, mo, r)))
      (fun ((i, next_pos, match_offset, _) : UInt32 × UInt32 × UInt32 × Option UInt32) => do
        let pos := (← posLoad e.prev ((cm + i) &&& e.wmask).toNat).toUInt32
        if pos < next_pos then
          if pos <= e.limit_base + i then return (i, next_pos, match_offset, some best)
          return (i + 1, pos, i, none)
        return (i + 1, next_pos, match_offset, none))
      ((0 : UInt32), cm, (0 : UInt32), none))
      (fun s H' => H' = LH H i z b st d ms ∧ s.2.1.toNat < 65536 ∧ s.2.2.1.toNat ≤ 255 ∧
        (limitBase st).toNat + s.2.2.1.toNat ≤ s.2.1.toNat ∧ ∀ x, s.2.2.2 = some x → x = best) := by
  have hlb2 := (limitBase_le st N.w_lo).1
  have hst := N.look
  refine sat_cwhile
    (fun (s : UInt32 × UInt32 × UInt32 × Option UInt32) H' => H' = LH H i z b st d ms ∧
      s.1.toNat ≤ bound.toNat + 1 ∧ s.2.1.toNat < 65536 ∧ s.2.2.1.toNat ≤ 255 ∧
      (limitBase st).toNat + s.2.2.1.toNat ≤ s.2.1.toNat ∧ ∀ x, s.2.2.2 = some x → x = best)
    (fun s => if s.2.2.2.isNone then bound.toNat + 2 - s.1.toNat else 0) _ ?_
    ⟨rfl, by simp, hcm, by simp, by simpa using hlb, fun x h => by simp at h⟩ (by simp [fuel]; omega)
  rintro ⟨i1, np, mo, r⟩ _ ⟨rfl, hi, hnp, hmo, hle, hr⟩
  refine Sat.pure ⟨fun ht => ?_, fun _ => ⟨rfl, hnp, hmo, hle, hr⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨hn, hib⟩ := ht
  cases r with
  | some x => simp at hn
  | none =>
  have hib' := UInt32.le_iff_toNat_le.mp hib
  have hi1 : (i1 + 1).toNat = i1.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  have hk := prev_idx E N (cm + i1)
  dsimp only
  rw [E.prev]
  refine Sat.bind (Sat.mono (posLoad_v (LH_get ms) _ (by have := N.pw; omega)) ?_)
  rintro p _ ⟨rfl, rfl⟩
  generalize rd2 d (po + 2 * ((cm + i1) &&& e.wmask).toNat) = q
  have hq := UInt16.toNat_lt q
  split
  · rename_i hlt
    have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
    rw [UInt16.toNat_toUInt32] at hlt'
    split
    · exact Sat.pure ⟨⟨rfl, by simp only []; omega, hnp, hmo, hle, fun x h => by simp at h; exact h.symm⟩,
        by simp; omega⟩
    · rename_i hgt
      simp only [UInt32.not_le] at hgt
      have hgt' := UInt32.lt_iff_toNat_lt.mp hgt
      rw [UInt16.toNat_toUInt32, UInt32.toNat_add, E.lb] at hgt'
      have : ((limitBase st).toNat + i1.toNat) % 2 ^ 32 = (limitBase st).toNat + i1.toNat := by
        apply Nat.mod_eq_of_lt; omega
      rw [this] at hgt'
      exact Sat.pure ⟨⟨rfl, by simp only []; omega, by simp only [UInt16.toNat_toUInt32]; omega,
        by simp only []; omega, by simp only [UInt16.toNat_toUInt32]; omega, fun x h => by simp at h⟩,
        by simp only [Option.isNone_none, ↓reduceIte]; omega⟩
  · exact Sat.pure ⟨⟨rfl, by simp only []; omega, hnp, hmo, hle, fun x h => by simp at h⟩,
      by simp only [Option.isNone_none, ↓reduceIte]; omega⟩

end

end ZlibNgF.Proof.LongestMatch
