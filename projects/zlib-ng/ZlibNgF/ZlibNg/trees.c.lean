import ZlibNgF.ZlibNg.«trees_emit.h»

/-!
# `trees.c` — Huffman tree construction and block emission of deflate (`ZlibNgF`)

Source: `zlib-ng/trees.c` and the constants of `zlib-ng/trees.h`, verified configuration: x86_64 LP64,
little-endian, `OPTIMAL_CMP == 64` (so both `OPTIMAL_CMP >= 32` and `OPTIMAL_CMP >= 64` branches of
`compress_block` are compiled), no `ZLIB_DEBUG` (`Assert`, `Trace*`, `cmpr_bits_align`, `sent_bits_align` are empty;
`cmpr_bits_add(s, x)` / `sent_bits_add(s, x)` are `(void)(x)`), no `DUMP_BL_TREE`.

Model choices:
* `tree_desc *desc` (always `&s->l_desc`, `&s->d_desc` or `&s->bl_desc`) is a selector `DescSel`; the descriptor
  is read and written through the state. `desc->stat_desc->f` reads the pointer field (`Ival.get` faults when it
  was never written) and then the static descriptor.
* `ct_data *` are `CtPtr`, `uint32_t *` into `pq_leaves` / `pq_scratch` are `DWPtr`, `s->bl_count` is `DHPtr`,
  `const int *extra_bits` is `IPtr`; all element accesses go through the strict `Ptr.add` / `Ptr.index`.
* Local arrays (`count_lo`, `count_hi`, `next_code`) are Lean arrays with checked access (`aget` / `aset`).
  `memset(count_lo, 0, sizeof(count_lo))` on a fresh local array is its creation filled with zeros.
  `next_code[0]` is never written in C and never read (a length 0 is skipped); the model starts it at 0.
* Out-parameters and in-out arrays of internal functions (`pq_radix_pass`'s `count`, `pq_take`'s `li` / `ihead`)
  are passed by value and returned (normalisation 1).
* `int` arithmetic that no preceding test keeps in range is checked (`chkI32`); conversions of out-of-range values
  to signed types take GCC's modulo result.
-/

set_option autoImplicit false

namespace ZlibNg.Trees
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.TreesEmit
open ZlibNg.Inftrees (aget aset)

/-! ## Constants of `trees.h` and `zutil.h` -/

/-- `#define DIST_CODE_LEN 512` (`trees.h`) -/
def DIST_CODE_LEN : Nat := 512
/-- `#define MAX_BL_BITS 7` (`trees.h`) -/
def MAX_BL_BITS : UInt32 := 7
/-- `#define REP_3_6 16` (`trees.h`) -/
def REP_3_6 : Int := 16
/-- `#define REPZ_3_10 17` (`trees.h`) -/
def REPZ_3_10 : Int := 17
/-- `#define REPZ_11_138 18` (`trees.h`) -/
def REPZ_11_138 : Int := 18
/-- `static const unsigned char bl_order[BL_CODES]` (`trees.h`) -/
def bl_order : Array UInt8 := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- `#define STORED_BLOCK 0` (`zutil.h`) -/
def STORED_BLOCK : Int32 := 0
/-- `#define STATIC_TREES 1` (`zutil.h`) -/
def STATIC_TREES : Int32 := 1
/-- `#define DYN_TREES 2` (`zutil.h`) -/
def DYN_TREES : Int32 := 2

/-- `#define PQ_NODE_BITS 10` (`trees.c:127`) -/
def PQ_NODE_BITS : UInt32 := 10
/-- `#define pq_pack(freq, node) (((uint32_t)(freq) << PQ_NODE_BITS) | (unsigned)(node))` (`trees.c:128`) -/
def pq_pack (freq : UInt32) (node : Int32) : UInt32 := (freq <<< PQ_NODE_BITS) ||| node.toUInt32
/-- `#define pq_node(e) ((int)((e) & ((1u << PQ_NODE_BITS) - 1)))` (`trees.c:129`) -/
def pq_node (e : UInt32) : Int32 := (e &&& ((1 <<< PQ_NODE_BITS) - 1)).toInt32
/-- `#define pq_freq(e) ((e) >> PQ_NODE_BITS)` (`trees.c:130`) -/
def pq_freq (e : UInt32) : UInt32 := e >>> PQ_NODE_BITS

/-- `#define LIT3_DIST1_MASK 0x000000FFFF000000ULL` (`trees.c:718`) -/
def LIT3_DIST1_MASK : UInt64 := 0x000000FFFF000000

/-! ## Helpers of other files -/

/-- `Z_FORCEINLINE static uint16_t bi_reverse(uint16_t code, int len)` (`deflate_p.h:134-139`):
`zng_bitreverse16(code) >> (16 - len)`. The shift is on the promoted `int`; `16 - len` is checked signed
arithmetic and a count outside `[0, 32)` faults. The `int` result is converted to `uint16_t`. -/
def bi_reverse (code : UInt16) (len : Int32) : M UInt16 := do
  let k ← chkI32 (16 - len.toInt)
  return (← shr32 (zng_bitreverse16 code).toUInt32 k.toUInt32).toUInt16

/-- `a[i]` for a local array indexed by an `int`: faults outside the array (negative included). -/
def lget {α : Type} [Inhabited α] (a : Array α) (i : Int32) : M α :=
  if i < 0 then ub "local array index outside its array" else aget a i.toInt.toNat

/-- `a[i] = v` for a local array indexed by an `int`: faults outside the array (negative included). -/
def lset {α : Type} (a : Array α) (i : Int32) (v : α) : M (Array α) :=
  if i < 0 then ub "local array index outside its array" else aset a i.toInt.toNat v

/-! ## Tree descriptors -/

/-- `tree_desc *desc`: one of `&s->l_desc`, `&s->d_desc`, `&s->bl_desc`. -/
inductive DescSel where
  | l_desc
  | d_desc
  | bl_desc
  deriving DecidableEq, Repr, Inhabited

/-- `*desc` -/
def DescSel.get (d : DescSel) (s : DeflateState) : TreeDesc :=
  match d with
  | .l_desc => s.l_desc
  | .d_desc => s.d_desc
  | .bl_desc => s.bl_desc

/-- `*desc = t` -/
def DescSel.set (d : DescSel) (s : DeflateState) (t : TreeDesc) : DeflateState :=
  match d with
  | .l_desc => { s with l_desc := t }
  | .d_desc => { s with d_desc := t }
  | .bl_desc => { s with bl_desc := t }

/-- `desc->dyn_tree` -/
def descDynTree (st : StatePtr) (d : DescSel) : M CtPtr := do
  (d.get (← ldDState st)).dyn_tree.get

/-- `*desc->stat_desc` -/
def descStat (st : StatePtr) (d : DescSel) : M StaticTreeDesc := do
  return (← (d.get (← ldDState st)).stat_desc.get).get

/-- `s->bl_count[i]` -/
def blCountGet (st : StatePtr) (i : Int) : M UInt16 := do Ptr.index (← blCountP st) i
/-- `s->bl_count[i] = v` -/
def blCountSet (st : StatePtr) (i : Int) (v : UInt16) : M Unit := do Ptr.store (← (← blCountP st).add i) v

/-- `p[i]` for `uint32_t *p` -/
def dwGet (p : DWPtr) (i : Int) : M UInt32 := Ptr.index p i
/-- `p[i] = v` for `uint32_t *p` -/
def dwSet (p : DWPtr) (i : Int) (v : UInt32) : M Unit := do Ptr.store (← p.add i) v

/-! ## Functions of `trees.c` -/

/-- `static void init_block(deflate_state *s)` (`trees.c:108-122`). -/
def init_block (st : StatePtr) : M Unit := do
  let ltree ← dynLtreeP st
  let _ ← cwhile (fun (n : Int32) => pure (n < L_CODES.toInt32, n))
    (fun n => do ctSetFc ltree n.toInt 0; pure (n + 1)) 0
  let dtree ← dynDtreeP st
  let _ ← cwhile (fun (n : Int32) => pure (n < D_CODES.toInt32, n))
    (fun n => do ctSetFc dtree n.toInt 0; pure (n + 1)) 0
  let bltree ← blTreeP st
  let _ ← cwhile (fun (n : Int32) => pure (n < BL_CODES.toInt32, n))
    (fun n => do ctSetFc bltree n.toInt 0; pure (n + 1)) 0
  ctSetFc (← dynLtreeP st) END_BLOCK 1
  wrD st fun s => { s with static_len := 0, opt_len := 0 }
  wrD st fun s => { s with sym_next := 0 }

/-- `void Z_INTERNAL zng_tr_init(deflate_state *s)` (`trees.c:83-103`). -/
def zng_tr_init (st : StatePtr) : M Unit := do
  let ltree ← dynLtreeP st
  wrD st fun s => { s with l_desc := { s.l_desc with dyn_tree := .val ltree } }
  wrD st fun s => { s with l_desc := { s.l_desc with stat_desc := .val .static_l_desc } }
  let dtree ← dynDtreeP st
  wrD st fun s => { s with d_desc := { s.d_desc with dyn_tree := .val dtree } }
  wrD st fun s => { s with d_desc := { s.d_desc with stat_desc := .val .static_d_desc } }
  let bltree ← blTreeP st
  wrD st fun s => { s with bl_desc := { s.bl_desc with dyn_tree := .val bltree } }
  wrD st fun s => { s with bl_desc := { s.bl_desc with stat_desc := .val .static_bl_desc } }
  wrD st fun s => { s with bi_buf := 0, bi_valid := 0, bi_used := 0 }
  init_block st

/-- `static void pq_radix_pass(const uint32_t *src, uint32_t *dst, int n, int shift, uint16_t *count)`
(`trees.c:137-144`). `count` is a local array of the caller, passed by value and returned. -/
def pq_radix_pass (src dst : DWPtr) (n shift : Int32) (count : Array UInt16) : M (Array UInt16) := do
  let (_, count) ← cwhile (fun ((i, count) : Int32 × Array UInt16) => pure (i <= 256, (i, count)))
    (fun ((i, count) : Int32 × Array UInt16) => do
      let a ← lget count i
      let b ← lget count (i - 1)
      let count ← lset count i (a.toUInt32 + b.toUInt32).toUInt16
      pure (i + 1, count))
    (1, count)
  let (_, count) ← cwhile (fun ((i, count) : Int32 × Array UInt16) => pure (i < n, (i, count)))
    (fun ((i, count) : Int32 × Array UInt16) => do
      let v ← dwGet src i.toInt
      let d := ((← shr32 v shift.toUInt32) &&& 0xFF).toNat
      let k ← aget count d
      let count ← aset count d (k + 1)
      dwSet dst k.toNat v
      pure (i + 1, count))
    (0, count)
  return count

/-- `static inline uint32_t pq_take(const uint32_t *leaves, int *li, int nleaves, const uint32_t *internals,
int *ihead, int itail)` (`trees.c:150-155`). Returns `(result, *li, *ihead)`. -/
def pq_take (leaves : DWPtr) (li nleaves : Int32) (internals : DWPtr) (ihead itail : Int32) :
    M (UInt32 × Int32 × Int32) := do
  let take ← if li < nleaves then
      (if ihead == itail then pure true
       else do pure ((← dwGet leaves li.toInt) < (← dwGet internals ihead.toInt)))
    else pure false
  if take then
    let v ← dwGet leaves li.toInt
    return (v, li + 1, ihead)
  let v ← dwGet internals ihead.toInt
  return (v, li, ← chkI32 (ihead.toInt + 1))

/-- `static void gen_bitlen(deflate_state *s, tree_desc *desc, const uint32_t *sorted, int nleaves, int root)`
(`trees.c:283-373`). -/
def gen_bitlen (st : StatePtr) (desc : DescSel) (sorted : DWPtr) (nleaves root : Int32) : M Unit := do
  let tree ← descDynTree st desc
  let elems := (← descStat st desc).elems
  let stree := (← descStat st desc).static_tree
  let extra := (← descStat st desc).extra_bits
  let base := (← descStat st desc).extra_base
  let max_length := (← descStat st desc).max_length
  let _ ← cwhile (fun (bits : UInt32) => pure (bits <= MAX_BITS.toUInt32, bits))
    (fun bits => do blCountSet st bits.toNat 0; pure (bits + 1)) 0
  -- first pass
  ctSetDl tree root.toInt 0
  let (_, overflow) ← cwhile
    (fun ((n, overflow) : Int32 × Int32) => pure (n >= elems, (n, overflow)))
    (fun ((n, overflow) : Int32 × Int32) => do
      let dad ← ctDl tree n.toInt
      let mut bits : UInt32 := (← ctDl tree dad.toNat).toUInt32 + 1
      let mut overflow := overflow
      if bits > max_length then
        bits := max_length
        overflow ← chkI32 (overflow.toInt + 1)
      ctSetDl tree n.toInt bits.toUInt16
      pure (← chkI32 (n.toInt - 1), overflow))
    (← chkI32 (root.toInt - 1), 0)
  let (_, overflow) ← cwhile
    (fun ((i, overflow) : Int32 × Int32) => pure (i < nleaves, (i, overflow)))
    (fun ((i, overflow) : Int32 × Int32) => do
      let n := pq_node (← dwGet sorted i.toInt)
      let dad ← ctDl tree n.toInt
      let mut bits : UInt32 := (← ctDl tree dad.toNat).toUInt32 + 1
      let mut overflow := overflow
      if bits > max_length then
        bits := max_length
        overflow ← chkI32 (overflow.toInt + 1)
      ctSetDl tree n.toInt bits.toUInt16
      blCountSet st bits.toNat ((← blCountGet st bits.toNat) + 1)
      let mut xbits : Int32 := 0
      if n >= base then
        xbits ← Ptr.index extra (← chkI32 (n.toInt - base.toInt)).toInt
      let f ← ctFc tree n.toInt
      wrD st fun s => { s with opt_len := s.opt_len + f.toUInt32 * (bits + xbits.toUInt32) }
      match stree with
      | .null => pure ()
      | _ =>
        let sl ← ctDl stree n.toInt
        let v ← chkI32 (sl.toNat + xbits.toInt)
        wrD st fun s => { s with static_len := s.static_len + f.toUInt32 * v.toUInt32 }
      pure (i + 1, overflow))
    (0, overflow)
  if overflow == 0 then
    return
  -- Find the first bit length which could increase
  let _ ← cdoWhile
    (fun (overflow : Int32) => do
      let bits := max_length - 1
      let bits ← cwhile
        (fun (bits : UInt32) => do pure ((← blCountGet st bits.toNat) == 0, bits))
        (fun (bits : UInt32) => pure (bits - 1))
        bits
      blCountSet st bits.toNat ((← blCountGet st bits.toNat) - 1)
      blCountSet st (bits + 1).toNat ((← blCountGet st (bits + 1).toNat).toUInt32 + 2).toUInt16
      blCountSet st max_length.toNat ((← blCountGet st max_length.toNat) - 1)
      chkI32 (overflow.toInt - 2))
    (fun overflow => pure (overflow > 0, overflow))
    overflow
  -- Now recompute all bit lengths, scanning in increasing frequency.
  let _ ← cwhile
    (fun ((bits, i) : UInt32 × Int32) => pure (bits != 0, (bits, i)))
    (fun ((bits, i) : UInt32 × Int32) => do
      let n : Int32 := (← blCountGet st bits.toNat).toUInt32.toInt32
      let (_, i) ← cwhile
        (fun ((n, i) : Int32 × Int32) => pure (n != 0, (n, i)))
        (fun ((n, i) : Int32 × Int32) => do
          let m := pq_node (← dwGet sorted i.toInt)
          let i ← chkI32 (i.toInt + 1)
          let len ← ctDl tree m.toInt
          if len.toUInt32 != bits then
            let fr ← ctFc tree m.toInt
            wrD st fun s => { s with opt_len := s.opt_len + bits * fr.toUInt32 }
            let len ← ctDl tree m.toInt
            let fr ← ctFc tree m.toInt
            let p ← chkI32 (len.toNat * fr.toNat)
            wrD st fun s => { s with opt_len := s.opt_len - p.toUInt32 }
            ctSetDl tree m.toInt bits.toUInt16
          pure (← chkI32 (n.toInt - 1), i))
        (n, i)
      pure (bits - 1, i))
    (max_length, (0 : Int32))

/-- `Z_INTERNAL void gen_codes(ct_data *tree, int max_code, uint16_t *bl_count)` (`trees.c:383-415`). -/
def gen_codes (tree : CtPtr) (max_code : Int32) (bl_count : DHPtr) : M Unit := do
  let next_code : Array UInt16 := Array.replicate (MAX_BITS + 1) 0
  let (_, _, next_code) ← cwhile
    (fun ((bits, code, nc) : Int32 × UInt16 × Array UInt16) => pure (bits <= MAX_BITS.toInt32, (bits, code, nc)))
    (fun ((bits, code, nc) : Int32 × UInt16 × Array UInt16) => do
      let bc : UInt16 ← Ptr.index bl_count (bits - 1).toInt
      let code : UInt16 := ((code.toUInt32 + bc.toUInt32) <<< 1).toUInt16
      let nc ← lset nc bits code
      pure (bits + 1, code, nc))
    (1, 0, next_code)
  let _ ← cwhile
    (fun ((n, nc) : Int32 × Array UInt16) => pure (n <= max_code, (n, nc)))
    (fun ((n, nc) : Int32 × Array UInt16) => do
      let len : Int32 := (← ctDl tree n.toInt).toUInt32.toInt32
      if len == 0 then
        return (← chkI32 (n.toInt + 1), nc)
      let v ← lget nc len
      let nc ← lset nc len (v + 1)
      ctSetFc tree n.toInt (← bi_reverse v len)
      pure (← chkI32 (n.toInt + 1), nc))
    (0, next_code)

/-- `static void build_tree(deflate_state *s, tree_desc *desc)` (`trees.c:165-271`). -/
def build_tree (st : StatePtr) (desc : DescSel) : M Unit := do
  let tree ← descDynTree st desc
  let stree := (← descStat st desc).static_tree
  let elems := (← descStat st desc).elems
  let mut max_code : Int32 := -1
  let mut node : Int32 := 0
  let mut nleaves : Int32 := 0
  let li : Int32 := 0
  let ihead : Int32 := 0
  let itail : Int32 := 0
  let leaves ← pqLeavesP st
  let scratch ← pqScratchP st
  let mut sorted := leaves
  let mut internals := scratch
  let count_lo : Array UInt16 := Array.replicate 257 0
  let count_hi : Array UInt16 := Array.replicate 257 0
  let (_, nl, mc, count_lo, count_hi) ← cwhile
    (fun ((n, nl, mc, clo, chi) : Int32 × Int32 × Int32 × Array UInt16 × Array UInt16) =>
      pure (n < elems, (n, nl, mc, clo, chi)))
    (fun ((n, nl, mc, clo, chi) : Int32 × Int32 × Int32 × Array UInt16 × Array UInt16) => do
      let freq ← ctFc tree n.toInt
      if freq != 0 then
        dwSet leaves nl.toInt (pq_pack freq.toUInt32 n)
        let nl ← chkI32 (nl.toInt + 1)
        let ilo := ((freq &&& 0xFF) + 1).toNat
        let clo ← aset clo ilo ((← aget clo ilo) + 1)
        let ihi := ((freq >>> 8) + 1).toNat
        let chi ← aset chi ihi ((← aget chi ihi) + 1)
        pure (n + 1, nl, n, clo, chi)
      else
        ctSetDl tree n.toInt 0
        pure (n + 1, nl, mc, clo, chi))
    (0, nleaves, max_code, count_lo, count_hi)
  nleaves := nl
  max_code := mc
  -- force at least two codes of non zero frequency
  let (nl, mc, nd) ← cwhile
    (fun ((nl, mc, nd) : Int32 × Int32 × Int32) => pure (nl < 2, (nl, mc, nd)))
    (fun ((nl, mc, _) : Int32 × Int32 × Int32) => do
      let (mc, nd) := if mc < 2 then (mc + 1, mc + 1) else (mc, (0 : Int32))
      dwSet leaves nl.toInt (pq_pack 1 nd)
      let nl := nl + 1
      ctSetFc tree nd.toInt 1
      wrD st fun s => { s with opt_len := s.opt_len - 1 }
      match stree with
      | .null => pure ()
      | _ =>
        let l ← ctDl stree nd.toInt
        wrD st fun s => { s with static_len := s.static_len - l.toUInt32 }
      pure (nl, mc, nd))
    (nleaves, max_code, node)
  nleaves := nl
  max_code := mc
  node := nd
  wrD st fun s => desc.set s { desc.get s with max_code := max_code }
  -- Sort the leaves by packed entry.
  if nleaves == 2 then
    let l0 ← dwGet leaves 0
    let l1 ← dwGet leaves 1
    if l0 > l1 then
      let t := l0
      dwSet leaves 0 l1
      dwSet leaves 1 t
  else if (← aget count_hi 1).toUInt32.toInt32 == nleaves then
    let _ ← pq_radix_pass leaves scratch nleaves PQ_NODE_BITS.toInt32 count_lo
    sorted := scratch
    internals := leaves
  else
    let _ ← pq_radix_pass leaves scratch nleaves PQ_NODE_BITS.toInt32 count_lo
    let _ ← pq_radix_pass scratch leaves nleaves (PQ_NODE_BITS + 8).toInt32 count_hi
  -- Construct the Huffman tree by repeatedly combining the least two frequent nodes.
  node := elems
  let (_, _, _, _, nd) ← cwhile
    (fun ((merges, li, ihead, itail, node) : Int32 × Int32 × Int32 × Int32 × Int32) =>
      pure (merges > 0, (merges, li, ihead, itail, node)))
    (fun ((merges, li, ihead, itail, node) : Int32 × Int32 × Int32 × Int32 × Int32) => do
      let (en, li, ihead) ← pq_take sorted li nleaves internals ihead itail
      let (em, li, ihead) ← pq_take sorted li nleaves internals ihead itail
      let n := pq_node en
      let m := pq_node em
      let f : UInt16 := (pq_freq en + pq_freq em).toUInt16
      ctSetFc tree node.toInt f
      ctSetDl tree m.toInt node.toUInt32.toUInt16
      ctSetDl tree n.toInt node.toUInt32.toUInt16
      dwSet internals itail.toInt (pq_pack f.toUInt32 node)
      let itail ← chkI32 (itail.toInt + 1)
      let node ← chkI32 (node.toInt + 1)
      pure (merges - 1, li, ihead, itail, node))
    (nleaves - 1, li, ihead, itail, node)
  node := nd
  gen_bitlen st desc sorted nleaves (← chkI32 (node.toInt - 1))
  gen_codes tree max_code (← blCountP st)

/-- `static void scan_tree(deflate_state *s, ct_data *tree, int max_code)` (`trees.c:421-463`). -/
def scan_tree (st : StatePtr) (tree : CtPtr) (max_code : Int32) : M Unit := do
  let prevlen : Int32 := -1
  let nextlen : Int32 := (← ctDl tree 0).toUInt32.toInt32
  let count : UInt16 := 0
  let mut max_count : UInt16 := 7
  let mut min_count : UInt16 := 4
  if nextlen == 0 then
    max_count := 138
    min_count := 3
  ctSetDl tree (← chkI32 (max_code.toInt + 1)).toInt 0xffff
  let bltree ← blTreeP st
  let _ ← cwhile
    (fun (x : Int32 × Int32 × Int32 × UInt16 × UInt16 × UInt16) => pure (x.1 <= max_code, x))
    (fun ((n, prevlen, nextlen, count, max_count, min_count) :
        Int32 × Int32 × Int32 × UInt16 × UInt16 × UInt16) => do
      let curlen := nextlen
      let nextlen : Int32 := (← ctDl tree (n.toInt + 1)).toUInt32.toInt32
      let count := count + 1
      if count < max_count && curlen == nextlen then
        return (n + 1, prevlen, nextlen, count, max_count, min_count)
      else if count < min_count then
        let fr ← ctFc bltree curlen.toInt
        ctSetFc bltree curlen.toInt (fr + count)
      else if curlen != 0 then
        if curlen != prevlen then
          ctSetFc bltree curlen.toInt ((← ctFc bltree curlen.toInt) + 1)
        ctSetFc bltree REP_3_6 ((← ctFc bltree REP_3_6) + 1)
      else if count <= 10 then
        ctSetFc bltree REPZ_3_10 ((← ctFc bltree REPZ_3_10) + 1)
      else
        ctSetFc bltree REPZ_11_138 ((← ctFc bltree REPZ_11_138) + 1)
      let count : UInt16 := 0
      let prevlen := curlen
      let (max_count, min_count) : UInt16 × UInt16 :=
        if nextlen == 0 then (138, 3)
        else if curlen == nextlen then (6, 3)
        else (7, 4)
      pure (n + 1, prevlen, nextlen, count, max_count, min_count))
    ((0 : Int32), prevlen, nextlen, count, max_count, min_count)

/-- `static void send_tree(deflate_state *s, ct_data *tree, int max_code)` (`trees.c:469-529`). The local
`bi_buf` / `bi_valid` are threaded through the loop. -/
def send_tree (st : StatePtr) (tree : CtPtr) (max_code : Int32) : M Unit := do
  let prevlen : Int32 := -1
  let nextlen : Int32 := (← ctDl tree 0).toUInt32.toInt32
  let count : Int32 := 0
  let mut max_count : Int32 := 7
  let mut min_count : Int32 := 4
  if nextlen == 0 then
    max_count := 138
    min_count := 3
  let bi_valid : UInt32 := (← rdD st (·.bi_valid)).toUInt32
  let bi_buf : UInt64 ← rdD st (·.bi_buf)
  let (_, _, _, _, _, _, bi_buf, bi_valid) ← cwhile
    (fun (x : Int32 × Int32 × Int32 × Int32 × Int32 × Int32 × UInt64 × UInt32) => pure (x.1 <= max_code, x))
    (fun ((n, prevlen, nextlen, count, max_count, min_count, bi_buf, bi_valid) :
        Int32 × Int32 × Int32 × Int32 × Int32 × Int32 × UInt64 × UInt32) => do
      let bltree ← blTreeP st
      let curlen := nextlen
      let nextlen : Int32 := (← ctDl tree (n.toInt + 1)).toUInt32.toInt32
      let count ← chkI32 (count.toInt + 1)
      if count < max_count && curlen == nextlen then
        return (n + 1, prevlen, nextlen, count, max_count, min_count, bi_buf, bi_valid)
      let (bi_buf, bi_valid) ←
        if count < min_count then do
          let (_, bi_buf, bi_valid) ← cdoWhile
            (fun ((count, bi_buf, bi_valid) : Int32 × UInt64 × UInt32) => do
              let (bi_buf, bi_valid) ← send_code st curlen.toInt bltree bi_buf bi_valid
              pure (count, bi_buf, bi_valid))
            (fun ((count, bi_buf, bi_valid) : Int32 × UInt64 × UInt32) => do
              let count ← chkI32 (count.toInt - 1)
              pure (count != 0, (count, bi_buf, bi_valid)))
            (count, bi_buf, bi_valid)
          pure (bi_buf, bi_valid)
        else if curlen != 0 then do
          let mut count := count
          let mut bi_buf := bi_buf
          let mut bi_valid := bi_valid
          if curlen != prevlen then
            (bi_buf, bi_valid) ← send_code st curlen.toInt bltree bi_buf bi_valid
            count ← chkI32 (count.toInt - 1)
          (bi_buf, bi_valid) ← send_code st REP_3_6 bltree bi_buf bi_valid
          let v ← chkI32 (count.toInt - 3)
          send_bits st v.toInt64.toUInt64 2 bi_buf bi_valid
        else if count <= 10 then do
          let (bi_buf, bi_valid) ← send_code st REPZ_3_10 bltree bi_buf bi_valid
          let v ← chkI32 (count.toInt - 3)
          send_bits st v.toInt64.toUInt64 3 bi_buf bi_valid
        else do
          let (bi_buf, bi_valid) ← send_code st REPZ_11_138 bltree bi_buf bi_valid
          let v ← chkI32 (count.toInt - 11)
          send_bits st v.toInt64.toUInt64 7 bi_buf bi_valid
      let count : Int32 := 0
      let prevlen := curlen
      let (max_count, min_count) : Int32 × Int32 :=
        if nextlen == 0 then (138, 3)
        else if curlen == nextlen then (6, 3)
        else (7, 4)
      pure (n + 1, prevlen, nextlen, count, max_count, min_count, bi_buf, bi_valid))
    ((0 : Int32), prevlen, nextlen, count, max_count, min_count, bi_buf, bi_valid)
  wrD st fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 }

/-- `static int build_bl_tree(deflate_state *s)` (`trees.c:535-561`). -/
def build_bl_tree (st : StatePtr) : M Int32 := do
  scan_tree st (← dynLtreeP st) (← rdD st (·.l_desc.max_code))
  scan_tree st (← dynDtreeP st) (← rdD st (·.d_desc.max_code))
  build_tree st .bl_desc
  let (max_blindex, _) ← cwhile
    (fun ((mb, done) : Int32 × Bool) => pure (!done && mb >= 3, (mb, done)))
    (fun ((mb, _) : Int32 × Bool) => do
      let o ← tblGet bl_order mb.toInt.toNat
      if (← ctDl (← blTreeP st) o.toNat) != 0 then pure (mb, true)
      else pure (mb - 1, false))
    (BL_CODES.toInt32 - 1, false)
  wrD st fun s => { s with opt_len := s.opt_len + (3 * (max_blindex.toUInt32 + 1) + 5 + 5 + 4) }
  return max_blindex

/-- `static void send_all_trees(deflate_state *s, int lcodes, int dcodes, int blcodes)` (`trees.c:568-597`). -/
def send_all_trees (st : StatePtr) (lcodes dcodes blcodes : Int32) : M Unit := do
  let bi_valid : UInt32 := (← rdD st (·.bi_valid)).toUInt32
  let bi_buf : UInt64 ← rdD st (·.bi_buf)
  let (bi_buf, bi_valid) ← send_bits st (← chkI32 (lcodes.toInt - 257)).toInt64.toUInt64 5 bi_buf bi_valid
  let (bi_buf, bi_valid) ← send_bits st (← chkI32 (dcodes.toInt - 1)).toInt64.toUInt64 5 bi_buf bi_valid
  let (bi_buf, bi_valid) ← send_bits st (← chkI32 (blcodes.toInt - 4)).toInt64.toUInt64 4 bi_buf bi_valid
  let (_, bi_buf, bi_valid) ← cwhile
    (fun ((rank, bb, bv) : Int32 × UInt64 × UInt32) => pure (rank < blcodes, (rank, bb, bv)))
    (fun ((rank, bb, bv) : Int32 × UInt64 × UInt32) => do
      let o ← tblGet bl_order rank.toInt.toNat
      let len ← ctDl (← blTreeP st) o.toNat
      let (bb, bv) ← send_bits st len.toUInt64 3 bb bv
      pure (rank + 1, bb, bv))
    ((0 : Int32), bi_buf, bi_valid)
  wrD st fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 }
  send_tree st (← dynLtreeP st) (← chkI32 (lcodes.toInt - 1))
  send_tree st (← dynDtreeP st) (← chkI32 (dcodes.toInt - 1))

/-- `void Z_INTERNAL zng_tr_stored_block(deflate_state *s, unsigned char *buf, uint32_t stored_len, int last)`
(`trees.c:602-619`). The `memcpy` is under `if (stored_len)`, so a `NULL` `buf` with `stored_len == 0` never
reaches it. -/
def zng_tr_stored_block (st : StatePtr) (buf : BPtr) (stored_len : UInt32) (last : Int32) : M Unit := do
  zng_tr_emit_tree st STORED_BLOCK last
  zng_tr_emit_align st
  put_short st stored_len.toUInt16
  put_short st (~~~stored_len).toUInt16
  if stored_len != 0 then
    let pb ← (← rdD st (·.pending_buf)).get
    let dst ← pb.add (← rdD st (·.pending)).toNat
    Ptr.memcpy dst buf stored_len.toNat
    wrD st fun s => { s with pending := s.pending + stored_len }

/-- `void Z_INTERNAL zng_tr_flush_bits(deflate_state *s)` (`trees.c:841-862`). `s->bi_valid` is an `int32_t`;
each subtraction follows a test that keeps it in range (normalisation 4). -/
def zng_tr_flush_bits (st : StatePtr) : M Unit := do
  if (← rdD st (·.bi_valid)) >= 48 then
    put_uint32 st (← rdD st (·.bi_buf)).toUInt32
    put_short st ((← rdD st (·.bi_buf)) >>> 32).toUInt16
    wrD st fun s => { s with bi_buf := s.bi_buf >>> 48 }
    wrD st fun s => { s with bi_valid := s.bi_valid - 48 }
  else if (← rdD st (·.bi_valid)) >= 32 then
    put_uint32 st (← rdD st (·.bi_buf)).toUInt32
    wrD st fun s => { s with bi_buf := s.bi_buf >>> 32 }
    wrD st fun s => { s with bi_valid := s.bi_valid - 32 }
  if (← rdD st (·.bi_valid)) >= 16 then
    put_short st (← rdD st (·.bi_buf)).toUInt16
    wrD st fun s => { s with bi_buf := s.bi_buf >>> 16 }
    wrD st fun s => { s with bi_valid := s.bi_valid - 16 }
  if (← rdD st (·.bi_valid)) >= 8 then
    put_byte st (← rdD st (·.bi_buf)).toUInt8
    wrD st fun s => { s with bi_buf := s.bi_buf >>> 8 }
    wrD st fun s => { s with bi_valid := s.bi_valid - 8 }

/-- `void Z_INTERNAL zng_tr_align(deflate_state *s)` (`trees.c:625-629`). -/
def zng_tr_align (st : StatePtr) : M Unit := do
  zng_tr_emit_tree st STATIC_TREES 0
  zng_tr_emit_end_block st (.ref .static_ltree 0) 0
  zng_tr_flush_bits st

/-- The locals of the symbol loop of `compress_block`. -/
structure CBL where
  sx : UInt32
  bi_buf : UInt64
  bi_valid : UInt32
  pending : UInt32

/-- `static void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`
(`trees.c:723-797`), with the `OPTIMAL_CMP >= 32` and `OPTIMAL_CMP >= 64` branches. `zng_memread_4` /
`zng_memread_8` with `Z_U32_FROM_LE` / `Z_U64_FROM_LE` (identities on little-endian) are `memread4` / `memread8`;
`lc` (`int`) is converted to the `uint32_t` / `unsigned` parameter of `zng_assemble_dist`. -/
def compress_block (st : StatePtr) (ltree dtree : CtPtr) : M Unit := do
  let sx : UInt32 := 0
  let sym_next : UInt32 ← rdD st (·.sym_next)
  let sym_buf : BPtr ← (← rdD st (·.sym_buf)).get
  let bi_buf : UInt64 ← rdD st (·.bi_buf)
  let bi_valid : UInt32 := (← rdD st (·.bi_valid)).toUInt32
  let pending : UInt32 ← rdD st (·.pending)
  let l0 : CBL := ⟨sx, bi_buf, bi_valid, pending⟩
  let l ← if sym_next != 0 then
      cdoWhile
        (fun (l : CBL) => do
          let (bi_buf, bi_valid, pending) ← send_bits_flush st l.bi_buf l.bi_valid l.pending
          let dist_lc ← memread4 (← sym_buf.add l.sx.toNat)
          let dist : UInt32 := dist_lc &&& 0xffff
          let lc : Int32 := ((dist_lc >>> 16) &&& 0xff).toInt32
          let mut sx := l.sx + 3
          if dist == 0 then
            let bits : UInt64 := 0
            let nbits : UInt32 := 0
            let (bits, nbits) ← send_code_merge st lc.toInt ltree bits nbits
            let mut bits := bits
            let mut nbits := nbits
            if sx + 8 <= sym_next then
              let next_syms ← memread8 (← sym_buf.add sx.toNat)
              if next_syms.toUInt16 == 0 then
                (bits, nbits) ← send_code_merge st ((next_syms >>> 16) &&& 0xff).toUInt32.toNat ltree bits nbits
                sx := sx + 3
                if next_syms &&& LIT3_DIST1_MASK == 0 then
                  (bits, nbits) ← send_code_merge st ((next_syms >>> 40) &&& 0xff).toUInt32.toNat ltree bits nbits
                  sx := sx + 3
            let bi_buf := bi_buf ||| (← shl64 bits bi_valid)
            let bi_valid := bi_valid + nbits
            pure ⟨sx, bi_buf, bi_valid, pending⟩
          else
            let (match_bits, match_bits_len) ← zng_assemble_dist ltree dtree lc.toUInt32 dist
            let (bi_buf, bi_valid) ← send_bits_merge st match_bits match_bits_len bi_buf bi_valid
            pure ⟨sx, bi_buf, bi_valid, pending⟩)
        (fun (l : CBL) => pure (l.sx < sym_next, l))
        l0
    else pure l0
  wrD st fun s => { s with pending := l.pending }
  let (bi_buf, bi_valid) ← zng_emit_end_block st ltree 0 l.bi_buf l.bi_valid
  wrD st fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 }

/-- `static int detect_data_type(deflate_state *s)` (`trees.c:812-836`). `unsigned long block_mask` is 64-bit. -/
def detect_data_type (st : StatePtr) : M Int32 := do
  let ltree ← dynLtreeP st
  let (_, _, found) ← cwhile
    (fun ((n, bm, found) : Int32 × UInt64 × Bool) => pure (!found && n <= 31, (n, bm, found)))
    (fun ((n, bm, _) : Int32 × UInt64 × Bool) => do
      let hit ← if bm &&& 1 != 0 then do pure ((← ctFc ltree n.toInt) != 0) else pure false
      if hit then pure (n, bm, true) else pure (n + 1, bm >>> 1, false))
    ((0 : Int32), (0xf3ffc07f : UInt64), false)
  if found then
    return Z_BINARY
  let t ← if (← ctFc ltree 9) != 0 then pure true
    else do
      if (← ctFc ltree 10) != 0 then pure true
      else do pure ((← ctFc ltree 13) != 0)
  if t then
    return Z_TEXT
  let (_, found) ← cwhile
    (fun ((n, found) : Int32 × Bool) => pure (!found && n < LITERALS.toInt32, (n, found)))
    (fun ((n, _) : Int32 × Bool) => do
      if (← ctFc ltree n.toInt) != 0 then pure (n, true) else pure (n + 1, false))
    ((32 : Int32), false)
  if found then
    return Z_TEXT
  return Z_BINARY

/-- `void Z_INTERNAL zng_tr_flush_block(deflate_state *s, unsigned char *buf, uint32_t stored_len, int last)`
(`trees.c:635-713`). `cmpr_bits_add(s, s->static_len)` / `cmpr_bits_add(s, s->opt_len)` read the field. -/
def zng_tr_flush_block (st : StatePtr) (buf : BPtr) (stored_len : UInt32) (last : Int32) : M Unit := do
  let mut opt_lenb : UInt32 := 0
  let mut static_lenb : UInt32 := 0
  let mut max_blindex : Int32 := 0
  if (← rdD st (·.sym_next)) == 0 then
    static_lenb := 0
    opt_lenb := static_lenb
    wrD st fun s => { s with static_len := 7 }
  else if (← rdD st (·.level)) > 0 then
    let strm ← (← rdD st (·.strm)).get
    if (← rdZ strm (·.data_type)) == Z_UNKNOWN then
      let dt ← detect_data_type st
      let strm ← (← rdD st (·.strm)).get
      wrZ strm fun z => { z with data_type := dt }
    build_tree st .l_desc
    build_tree st .d_desc
    max_blindex ← build_bl_tree st
    opt_lenb := ((← rdD st (·.opt_len)) + 3 + 7) >>> 3
    static_lenb := ((← rdD st (·.static_len)) + 3 + 7) >>> 3
    if static_lenb <= opt_lenb || (← rdD st (·.strategy)) == Z_FIXED then
      opt_lenb := static_lenb
  else
    static_lenb := stored_len + 5
    opt_lenb := static_lenb
  let bufNonNull : Bool := match buf with | .null => false | _ => true
  if stored_len + 4 <= opt_lenb && bufNonNull then
    zng_tr_stored_block st buf stored_len last
  else if static_lenb == opt_lenb then
    zng_tr_emit_tree st STATIC_TREES last
    compress_block st (.ref .static_ltree 0) (.ref .static_dtree 0)
    let _ ← rdD st (·.static_len)
  else
    zng_tr_emit_tree st DYN_TREES last
    let lc ← chkI32 ((← rdD st (·.l_desc.max_code)).toInt + 1)
    let dc ← chkI32 ((← rdD st (·.d_desc.max_code)).toInt + 1)
    let bc ← chkI32 (max_blindex.toInt + 1)
    send_all_trees st lc dc bc
    compress_block st (← dynLtreeP st) (← dynDtreeP st)
    let _ ← rdD st (·.opt_len)
  init_block st
  if last != 0 then
    zng_tr_emit_align st

end ZlibNg.Trees
