import ZlibNgF.ZlibNg.«deflate.h»

/-!
# `trees_emit.h` — bit writer and symbol emitters of deflate (`ZlibNgF`)

Source: `zlib-ng/trees_emit.h`, verified configuration: no `ZLIB_DEBUG`, so `trace_bits`, `trace_code`, `Tracev`,
`Tracecv` and `Assert` are empty, `cmpr_bits_add(s, len)` / `sent_bits_add(s, bits)` are `Z_UNUSED(x)`
(`(void)(x)`: the operand is evaluated, which matters only when it reads memory, as `ltree[c].Len` in
`zng_tr_emit_lit`), and `cmpr_bits_align` / `sent_bits_align` are empty.

The macros `send_bits`, `send_bits_merge`, `send_bits_flush`, `send_code` and `send_code_merge` update the caller's
local variables `bi_buf`, `bi_valid` (and `pending`): here they are functions that take these values and return
their new values. The out-parameters `uint64_t *bi_buf`, `uint32_t *bi_valid` of the internal functions, and
`uint32_t *bits_len` of `zng_assemble_dist`, are passed by value and returned as extra results (normalisation 1).
The macro arguments `t_val` / `t_len` are converted by the macro itself (`(uint64_t)t_val`, `(uint32_t)t_len`); the
callers pass the converted values.
-/

set_option autoImplicit false

namespace ZlibNg.TreesEmit
open C ZlibNg.Inflate ZlibNg.Deflate

/-- `#define send_bits(s, t_val, t_len, bi_buf, bi_valid)` (`trees_emit.h:43-64`). `t_val` is `(uint64_t)t_val`,
`t_len` is `(uint32_t)t_len`. Returns `(bi_buf, bi_valid)`. -/
def send_bits (st : StatePtr) (t_val : UInt64) (t_len : UInt32) (bi_buf : UInt64) (bi_valid : UInt32) :
    M (UInt64 × UInt32) := do
  let val : UInt64 := t_val
  let len : UInt32 := t_len
  let mut total_bits : UInt32 := bi_valid + len
  let mut bi_buf := bi_buf ||| (← shl64 val bi_valid)
  if total_bits >= 64 then
    total_bits := total_bits - 64
    put_uint64 st bi_buf
    bi_buf ← shr64 (val >>> 1) (~~~bi_valid &&& 63)
  let bi_valid := total_bits
  return (bi_buf, bi_valid)

/-- `#define send_bits_merge(s, t_val, t_len, bi_buf, bi_valid)` (`trees_emit.h:68-74`). Returns
`(bi_buf, bi_valid)`. -/
def send_bits_merge (_st : StatePtr) (t_val : UInt64) (t_len : UInt32) (bi_buf : UInt64) (bi_valid : UInt32) :
    M (UInt64 × UInt32) := do
  let bi_buf := bi_buf ||| (← shl64 t_val bi_valid)
  let bi_valid := bi_valid + t_len
  return (bi_buf, bi_valid)

/-- `#define send_bits_flush(s, bi_buf, bi_valid, pending)` (`trees_emit.h:80-85`). Returns
`(bi_buf, bi_valid, pending)`. The 8-byte store at `s->pending_buf + pending` is `zng_memwrite_8`. -/
def send_bits_flush (st : StatePtr) (bi_buf : UInt64) (bi_valid : UInt32) (pending : UInt32) :
    M (UInt64 × UInt32 × UInt32) := do
  let pb ← (← rdD st (·.pending_buf)).get
  memwrite8 (← pb.add pending.toNat) bi_buf
  let pending := pending + (bi_valid >>> 3)
  let bi_buf ← shr64 bi_buf (bi_valid &&& ~~~7)
  let bi_valid := bi_valid &&& 7
  return (bi_buf, bi_valid, pending)

/-- `#define send_code(s, c, tree, bi_buf, bi_valid) send_bits(s, tree[c].Code, tree[c].Len, bi_buf, bi_valid)`
(`trees_emit.h:94-95`). Returns `(bi_buf, bi_valid)`. -/
def send_code (st : StatePtr) (c : Int) (tree : CtPtr) (bi_buf : UInt64) (bi_valid : UInt32) :
    M (UInt64 × UInt32) := do
  let code ← ctFc tree c
  let len ← ctDl tree c
  send_bits st code.toUInt64 len.toUInt32 bi_buf bi_valid

/-- `#define send_code_merge(s, c, tree, bi_buf, bi_valid) send_bits_merge(s, tree[c].Code, tree[c].Len, bi_buf,
bi_valid)` (`trees_emit.h:105-106`). Returns `(bi_buf, bi_valid)`. -/
def send_code_merge (st : StatePtr) (c : Int) (tree : CtPtr) (bi_buf : UInt64) (bi_valid : UInt32) :
    M (UInt64 × UInt32) := do
  let code ← ctFc tree c
  let len ← ctDl tree c
  send_bits_merge st code.toUInt64 len.toUInt32 bi_buf bi_valid

/-- `static inline void bi_windup(deflate_state *s)` (`trees_emit.h:112-133`). `s->bi_valid` is an `int32_t`;
`s->bi_valid - 1` is checked signed arithmetic. -/
def bi_windup (st : StatePtr) : M Unit := do
  if (← rdD st (·.bi_valid)) > 56 then
    put_uint64 st (← rdD st (·.bi_buf))
  else
    if (← rdD st (·.bi_valid)) > 24 then
      put_uint32 st (← rdD st (·.bi_buf)).toUInt32
      wrD st fun s => { s with bi_buf := s.bi_buf >>> 32 }
      wrD st fun s => { s with bi_valid := s.bi_valid - 32 }
    if (← rdD st (·.bi_valid)) > 8 then
      put_short st (← rdD st (·.bi_buf)).toUInt16
      wrD st fun s => { s with bi_buf := s.bi_buf >>> 16 }
      wrD st fun s => { s with bi_valid := s.bi_valid - 16 }
    if (← rdD st (·.bi_valid)) > 0 then
      put_byte st (← rdD st (·.bi_buf)).toUInt8
  let v ← chkI32 ((← rdD st (·.bi_valid)).toInt - 1)
  let bi_used := (v &&& 7) + 1
  wrD st fun s => { s with bi_used := bi_used, bi_buf := 0, bi_valid := 0 }

/-- `Z_FORCEINLINE static void zng_emit_lit(deflate_state *s, const ct_data *ltree, unsigned c, uint64_t *bi_buf,
uint32_t *bi_valid)` (`trees_emit.h:138-142`). Returns `(*bi_buf, *bi_valid)`. -/
def zng_emit_lit (st : StatePtr) (ltree : CtPtr) (c : UInt32) (bi_buf : UInt64) (bi_valid : UInt32) :
    M (UInt64 × UInt32) :=
  send_code st c.toNat ltree bi_buf bi_valid

/-- `Z_FORCEINLINE static uint64_t zng_assemble_dist(const ct_data *ltree, const ct_data *dtree, uint32_t lc,
uint32_t dist, uint32_t *bits_len)` (`trees_emit.h:148-194`). Returns `(match_bits, *bits_len)`. -/
def zng_assemble_dist (ltree dtree : CtPtr) (lc dist : UInt32) : M (UInt64 × UInt32) := do
  -- 1. Process Length Code
  let mut code : UInt8 ← tblGet zng_length_code lc.toNat
  let c : UInt32 := code.toUInt32 + LITERALS.toUInt32 + 1
  let mut match_bits : UInt64 := (← ctFc ltree c.toNat).toUInt64
  let mut match_bits_len : UInt32 := (← ctDl ltree c.toNat).toUInt32
  -- 2. Get extra bits count and mask
  let mut mask_ext : UInt32 := (← tblGet lmask_extra code.toNat).toUInt32
  let mut extra : UInt32 := mask_ext >>> 8
  match_bits := match_bits ||| (← shl64 (lc &&& mask_ext).toUInt64 match_bits_len)
  match_bits_len := match_bits_len + extra
  -- 3. Process Distance Code
  let dist := dist - 1
  code ← d_code dist
  match_bits := match_bits ||| (← shl64 (← ctFc dtree code.toNat).toUInt64 match_bits_len)
  match_bits_len := match_bits_len + (← ctDl dtree code.toNat).toUInt32
  -- 4. Get extra bits count and mask
  mask_ext ← tblGet dmask_extra code.toNat
  extra := mask_ext >>> 16
  match_bits := match_bits ||| (← shl64 (dist &&& mask_ext).toUInt64 match_bits_len)
  match_bits_len := match_bits_len + extra
  return (match_bits, match_bits_len)

/-- `static inline uint32_t zng_emit_dist(deflate_state *s, const ct_data *ltree, const ct_data *dtree, uint32_t lc,
uint32_t dist, uint64_t *bi_buf, uint32_t *bi_valid)` (`trees_emit.h:199-207`). Returns
`(result, *bi_buf, *bi_valid)`. -/
def zng_emit_dist (st : StatePtr) (ltree dtree : CtPtr) (lc dist : UInt32) (bi_buf : UInt64) (bi_valid : UInt32) :
    M (UInt32 × UInt64 × UInt32) := do
  let (match_bits, match_bits_len) ← zng_assemble_dist ltree dtree lc dist
  let (bi_buf, bi_valid) ← send_bits st match_bits match_bits_len bi_buf bi_valid
  return (match_bits_len, bi_buf, bi_valid)

/-- `static inline void zng_emit_end_block(deflate_state *s, const ct_data *ltree, const int last, uint64_t *bi_buf,
uint32_t *bi_valid)` (`trees_emit.h:212-218`). `last` is only `Z_UNUSED`. Returns `(*bi_buf, *bi_valid)`. -/
def zng_emit_end_block (st : StatePtr) (ltree : CtPtr) (_last : Int32) (bi_buf : UInt64) (bi_valid : UInt32) :
    M (UInt64 × UInt32) :=
  send_code st END_BLOCK ltree bi_buf bi_valid

/-- `static inline void zng_tr_emit_lit(deflate_state *s, const ct_data *ltree, unsigned c)`
(`trees_emit.h:223-230`). `cmpr_bits_add(s, ltree[c].Len)` evaluates `ltree[c].Len`. -/
def zng_tr_emit_lit (st : StatePtr) (ltree : CtPtr) (c : UInt32) : M Unit := do
  let bi_buf ← rdD st (·.bi_buf)
  let bi_valid := (← rdD st (·.bi_valid)).toUInt32
  let (bi_buf, bi_valid) ← zng_emit_lit st ltree c bi_buf bi_valid
  wrD st fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 }
  let _ ← ctDl ltree c.toNat

/-- `static inline void zng_tr_emit_dist(deflate_state *s, const ct_data *ltree, const ct_data *dtree, uint32_t lc,
uint32_t dist)` (`trees_emit.h:235-243`). -/
def zng_tr_emit_dist (st : StatePtr) (ltree dtree : CtPtr) (lc dist : UInt32) : M Unit := do
  let bi_buf ← rdD st (·.bi_buf)
  let bi_valid := (← rdD st (·.bi_valid)).toUInt32
  let (_bits, bi_buf, bi_valid) ← zng_emit_dist st ltree dtree lc dist bi_buf bi_valid
  wrD st fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 }

/-- `static inline void zng_tr_emit_tree(deflate_state *s, int type, const int last)` (`trees_emit.h:248-257`).
`(type << 1) + last` is signed `int` arithmetic: a negative `type` or an overflow faults. -/
def zng_tr_emit_tree (st : StatePtr) (type : Int32) (last : Int32) : M Unit := do
  let bi_valid := (← rdD st (·.bi_valid)).toUInt32
  let bi_buf ← rdD st (·.bi_buf)
  if type < 0 then ub "left shift of a negative int"
  let t ← chkI32 (type.toInt * 2)
  let header_bits : UInt32 := (← chkI32 (t.toInt + last.toInt)).toUInt32
  let (bi_buf, bi_valid) ← send_bits st header_bits.toUInt64 3 bi_buf bi_valid
  wrD st fun s => { s with bi_valid := bi_valid.toInt32, bi_buf := bi_buf }

/-- `static inline void zng_tr_emit_align(deflate_state *s)` (`trees_emit.h:262-265`). -/
def zng_tr_emit_align (st : StatePtr) : M Unit :=
  bi_windup st

/-- `static inline void zng_tr_emit_end_block(deflate_state *s, const ct_data *ltree, const int last)`
(`trees_emit.h:270-279`). -/
def zng_tr_emit_end_block (st : StatePtr) (ltree : CtPtr) (last : Int32) : M Unit := do
  let bi_buf ← rdD st (·.bi_buf)
  let bi_valid := (← rdD st (·.bi_valid)).toUInt32
  let (bi_buf, bi_valid) ← zng_emit_end_block st ltree last bi_buf bi_valid
  wrD st fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 }
  if last != 0 then
    zng_tr_emit_align st

end ZlibNg.TreesEmit
