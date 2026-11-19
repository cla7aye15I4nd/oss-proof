import ZlibNgF.Proof.«inflate.c.invariant»

/-!
# The callees of `inflate` that other proof files cover (`ZlibNgF`)

The proof of `inflate` (state by state) takes the safety facts of three callees as hypotheses, each collected in one
structure. These are statements about translated C functions, to be proved as theorems:

* `TableFacts`: `zng_inflate_table` (`inftrees.c`) as `CODELENS` and `LENLENS` call it: no fault, it writes only the
  `codes` and `work` arrays of the state (the entries before the table start unchanged), and on success the region
  `[o, o')` it returns is a `CodeTable` (`Proof/inflate.c.tables.lean`) with the returned root bits;
* `FastFacts`: `inflate_fast_c` / `inflate_fast_safe_c` (`inffast_tpl.h`) as `LEN` calls them (patch 0010: fewer than
  8 bits held): no fault, they advance `next_in` / `next_out` by what they consume / produce, write only the output
  buffer `[next_out, next_out + avail_out)`, the stream record and the state's `mode`, `hold`, `bits`; they leave
  `LEN`, `TYPE` or `BAD`, never increase the input bits plus output bytes still available, and unless `BAD`
  consume a bit or produce a byte;
* `CopyFacts`: `chunkmemset_safe_c` (`chunkset_tpl.h`) as `MATCH` calls it, for a distance `d ≥ 1` back into the
  bytes already written to the output buffer: no fault, it returns `out + len` and writes only `[out, out + left)`.

None of them is assumed by a registered result: a result is registered only when these are proved.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateFacts
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv)
open ZlibNgF.Proof.InflateTab (CodeTable)

/-- The three calls of `zng_inflate_table` in `inflate`: the code length code (`LENLENS`: 19 lengths at `lens[0]`,
table at `codes[0]`, 7 root bits), the literal/length code (`CODELENS`: `nlen` lengths at `lens[0]`, table at
`codes[0]`, 10 root bits) and the distance code (`ndist` lengths at `lens[nlen]`, table at `codes[o]` after the
literal/length table, 9 root bits). -/
def TableCall (type : UInt32) (lo : Nat) (n : UInt32) (o : Nat) (bits : UInt32) : Prop :=
  (type = ZlibNg.Inftrees.CODES ∧ lo = 0 ∧ n = 19 ∧ o = 0 ∧ bits = 7) ∨
  (type = ZlibNg.Inftrees.LENS ∧ lo = 0 ∧ 257 ≤ n.toNat ∧ n.toNat ≤ 286 ∧ o = 0 ∧ bits = 10) ∨
  (type = ZlibNg.Inftrees.DISTS ∧ 257 ≤ lo ∧ lo ≤ 286 ∧ 1 ≤ n.toNat ∧ n.toNat ≤ 30 ∧ o ≤ 1332 ∧ bits = 9)

/-- `zng_inflate_table` as `inflate` calls it. The lengths are in range (`inftrees.c`: "The caller must assure
this"): at most 7 for the code length code (3-bit fields), at most 15 otherwise. -/
structure TableFacts : Prop where
  table : ∀ (h : Heap) (b : Nat) (st : InflateState) (type : UInt32) (lo : Nat) (n : UInt32) (o : Nat)
      (bits : UInt32),
    h.istate b = some st → st.codes.size = ENOUGH → st.lens.size = 320 → st.work.size = 288 →
    TableCall type lo n o bits →
    (∀ j, j < n.toNat → (st.lens[lo + j]!).toNat ≤ (if type = ZlibNg.Inftrees.CODES then 7 else 15)) →
    ∃ (ret : Int32) (o' : Nat) (lb : UInt32) (codes' : Array Code) (work' : Array UInt16),
      C.run (ZlibNg.Inftrees.zng_inflate_table type (.ref (.lens b) lo) n (.ref (.codes b) o) bits
        (.ref (.work b) 0)) h =
        .ok ((ret, .ref (.codes b) o', lb),
          { h with istates := upd h.istates b (some { st with codes := codes', work := work' }) }) ∧
      codes'.size = ENOUGH ∧ work'.size = 288 ∧ (∀ j, j < o → codes'[j]! = st.codes[j]!) ∧
      (ret = 0 → o' ≤ o + (if type = ZlibNg.Inftrees.DISTS then 592 else 1332) ∧
        CodeTable codes' o o' lb.toNat (if type = ZlibNg.Inftrees.CODES then 25 else 28)
          (type == ZlibNg.Inftrees.DISTS))

/-- `inflate_fast_c` (`safe = false`, at least 260 output bytes) and `inflate_fast_safe_c` (`safe = true`, 3 to 259
output bytes) as `LEN` calls them after `RESTORE()`: a state in `LEN` with the invariant (so with its tables,
`ModeOK`), fewer than 8 bits held, at least 15 input bytes at `next_in`, and an output buffer that started `start -
avail_out` bytes before `next_out` (the bytes written by this `inflate` call, which a match may copy from), with the
input, the output buffer and the state's block disjoint. -/
structure FastFacts : Prop where
  fast : ∀ (safe : Bool) (h : Heap) (i b : Nat) (z : ZStream) (st : InflateState) (start : UInt32) (ri : BRef)
      (oi bo oo : Nat),
    Inv h (some i) → h.streams i = some z → z.state = some b → h.istate b = some st →
    st.mode = LEN → st.bits < 8 → 15 ≤ z.avail_in →
    (if safe then 3 ≤ z.avail_out ∧ z.avail_out < 260 else 260 ≤ z.avail_out) → z.avail_out ≤ start →
    z.next_in = .ref ri oi → ReadSlice h z.next_in z.avail_in.toNat →
    z.next_out = .ref (.heap bo) (oo + (start - z.avail_out).toNat) → WriteSlice h (.ref (.heap bo) oo) start.toNat →
    Disjoint z.next_in z.avail_in.toNat (.ref (.heap bo) oo) start.toNat → NotInBlock b z.next_in → bo ≠ b →
    ∃ (h' : Heap) (ai ao : UInt32) (m : UInt32) (hold : UInt64) (bits : UInt32) (msg : BPtr),
      C.run ((if safe then ZlibNg.ChunksetC.inflate_fast_safe_c else ZlibNg.ChunksetC.inflate_fast_c) (some i)
        start) h = .ok ((), h') ∧
      ai ≤ z.avail_in ∧ ao ≤ z.avail_out ∧
      h'.streams i = some { z with
        next_in := .ref ri (oi + (z.avail_in - ai).toNat)
        avail_in := ai
        next_out := .ref (.heap bo) (oo + (start - ao).toNat)
        avail_out := ao
        msg := msg } ∧
      h'.istates b = some { st with mode := m, hold := hold, bits := bits } ∧
      (m = LEN ∨ m = TYPE ∨ m = BAD) ∧ bits < 8 ∧
      8 * ai.toNat + bits.toNat + ao.toNat + (if m = BAD then 0 else 1) ≤
        8 * z.avail_in.toNat + st.bits.toNat + z.avail_out.toNat ∧
      h'.bytes b = h.bytes b ∧ h'.iallocs b = h.iallocs b ∧
      Frame h h' [i] [b] [] [(z.next_out, z.avail_out.toNat)]

/-- `chunkmemset_safe_c(out, out - d, len, left)` as `MATCH` calls it: `out` at offset `p` of a heap block with `left`
bytes after it, the source `d ≥ 1` bytes back in the same block, `len ≤ left`. -/
structure CopyFacts : Prop where
  memset : ∀ (h : Heap) (bo p d : Nat) (data : Array UInt8) (len left : UInt64),
    h.bytes bo = some data → 1 ≤ d → d ≤ p → p + left.toNat ≤ data.size → len ≤ left → 1 ≤ left →
    ∃ data' : Array UInt8,
      C.run (ZlibNg.ChunksetC.chunkmemset_safe_c (.ref (.heap bo) p) (.ref (.heap bo) (p - d)) len left) h =
        .ok (.ref (.heap bo) (p + len.toNat), { h with bytes := upd h.bytes bo (some data') }) ∧
      data'.size = data.size ∧ ∀ j, (j < p ∨ p + left.toNat ≤ j) → data'[j]! = data[j]!

end ZlibNgF.Proof.InflateFacts
