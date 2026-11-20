import ZlibNgF.ZlibNg.«zbuild.h»
import ZlibNgF.ZlibNg.«crc32_p.h»

/-!
# `arch/generic/crc32_braid_c.c` — braided CRC-32 kernel (`ZlibNgF`)

Source: `zlib-ng/arch/generic/crc32_braid_c.c` and `zlib-ng/crc32_braid_p.h`, `CRC32_BRAID_FALLBACK` defined,
LP64 little-endian scalar build (`BRAID_N = 5`, `BRAID_W = 8`, `BYTE_ORDER == LITTLE_ENDIAN`, so
`Z_WORD_FROM_LE(x)` is `x`). The conversion `(z_word_t const *)buf` is checked for 8-byte alignment
(`Ptr.castAligned`); each `words[i]` is eight little-endian byte loads.
-/

set_option autoImplicit false

namespace ZlibNg.Crc32Braid
open C ZlibNg.Zbuild ZlibNg.Crc32Tbl ZlibNg.Crc32P

def BRAID_N : UInt64 := 5
def BRAID_W : UInt64 := 8
def BRAID_W_I32 : Int32 := 8

/-- Bounds-checked read `BRAID_TABLE[k][i]` (`crc_braid_table[8][256]`). -/
def braidTab (k i : Nat) : M UInt32 :=
  match crc_braid_table[k]? with
  | some row =>
    match row[i]? with
    | some v => pure v
    | none => ub "crc_braid_table column outside its array"
  | none => ub "crc_braid_table row outside its array"

/-- Read `words[wordIdx]` (`z_word_t const *words` on little-endian LP64). -/
def loadWordAt (words : BPtr) (wordIdx : Nat) : M UInt64 := do
  let base : Int := Int.ofNat (8 * wordIdx)
  let b0 ← index8 words base
  let b1 ← index8 words (base + 1)
  let b2 ← index8 words (base + 2)
  let b3 ← index8 words (base + 3)
  let b4 ← index8 words (base + 4)
  let b5 ← index8 words (base + 5)
  let b6 ← index8 words (base + 6)
  let b7 ← index8 words (base + 7)
  return b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- `static uint32_t crc_word(z_word_t data)` (`crc32_braid_c.c:50-55`, little-endian). -/
def crc_word (data : UInt64) : M UInt32 := do
  let (data, _) ← cwhile
    (fun ((data, k) : UInt64 × Int32) => pure (k < BRAID_W_I32, (data, k)))
    (fun ((data, k) : UInt64 × Int32) => do
      let t ← crcTab (data &&& 0xff)
      pure ((data >>> 8) ^^^ t.toUInt64, k + 1))
    (data, (0 : Int32))
  return data.toUInt32

/-- Braid loop state for `crc32_braid`. -/
structure BraidState where
  crc0 : UInt64
  crc1 : UInt64
  crc2 : UInt64
  crc3 : UInt64
  crc4 : UInt64
  words : BPtr
  blks : UInt64

/-- `Z_INTERNAL uint32_t crc32_braid(uint32_t crc, const uint8_t *buf, size_t len)` (`crc32_braid_c.c:68-211`). -/
def crc32_braid (crc : UInt32) (buf : BPtr) (len : UInt64) : M UInt32 := do
  let mut crc := ~~~crc
  let mut buf := buf
  let mut len := len
  if len >= BRAID_N * BRAID_W + BRAID_W - 1 then
    let align_diff := MIN (← ALIGN_DIFF buf BRAID_W) len
    if align_diff != 0 then
      crc ← crc32_copy_small crc .null buf align_diff 7 0
      len := len - align_diff
      buf ← buf.add (Int.ofNat align_diff.toNat)
    let blks : UInt64 := len / (BRAID_N * BRAID_W)
    len := len - blks * BRAID_N * BRAID_W
    let words ← Ptr.castAligned buf 8
    let st ← cwhile
      (fun (s : BraidState) =>
        let blks := s.blks - 1
        pure (blks != 0, { s with blks }))
      (fun (s : BraidState) => do
        let w0 ← loadWordAt s.words 0
        let w1 ← loadWordAt s.words 1
        let w2 ← loadWordAt s.words 2
        let w3 ← loadWordAt s.words 3
        let w4 ← loadWordAt s.words 4
        let word0 := s.crc0 ^^^ w0
        let word1 := s.crc1 ^^^ w1
        let word2 := s.crc2 ^^^ w2
        let word3 := s.crc3 ^^^ w3
        let word4 := s.crc4 ^^^ w4
        let words ← s.words.add 40
        let c0 ← braidTab 0 (word0 &&& 0xff).toNat
        let c1 ← braidTab 0 (word1 &&& 0xff).toNat
        let c2 ← braidTab 0 (word2 &&& 0xff).toNat
        let c3 ← braidTab 0 (word3 &&& 0xff).toNat
        let c4 ← braidTab 0 (word4 &&& 0xff).toNat
        let ((crc0, crc1, crc2, crc3, crc4), _) ← cwhile
          (fun ((acc, k) : (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) × Int32) =>
            pure (k < BRAID_W_I32, (acc, k)))
          (fun (((crc0, crc1, crc2, crc3, crc4), k) : (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) × Int32) => do
            let sh : UInt64 := (k.toInt.toNat * 8).toUInt64
            let kn := k.toInt.toNat
            let t0 ← braidTab kn ((word0 >>> sh) &&& 0xff).toNat
            let t1 ← braidTab kn ((word1 >>> sh) &&& 0xff).toNat
            let t2 ← braidTab kn ((word2 >>> sh) &&& 0xff).toNat
            let t3 ← braidTab kn ((word3 >>> sh) &&& 0xff).toNat
            let t4 ← braidTab kn ((word4 >>> sh) &&& 0xff).toNat
            pure ((crc0 ^^^ t0.toUInt64, crc1 ^^^ t1.toUInt64, crc2 ^^^ t2.toUInt64,
                   crc3 ^^^ t3.toUInt64, crc4 ^^^ t4.toUInt64), k + 1))
          ((c0.toUInt64, c1.toUInt64, c2.toUInt64, c3.toUInt64, c4.toUInt64), (1 : Int32))
        pure { s with crc0, crc1, crc2, crc3, crc4, words })
      { crc0 := crc.toUInt64, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words, blks }
    let lw0 ← loadWordAt st.words 0
    let lw1 ← loadWordAt st.words 1
    let lw2 ← loadWordAt st.words 2
    let lw3 ← loadWordAt st.words 3
    let lw4 ← loadWordAt st.words 4
    let comb0 ← crc_word (st.crc0 ^^^ lw0)
    let comb1 ← crc_word (st.crc1 ^^^ lw1 ^^^ comb0.toUInt64)
    let comb2 ← crc_word (st.crc2 ^^^ lw2 ^^^ comb1.toUInt64)
    let comb3 ← crc_word (st.crc3 ^^^ lw3 ^^^ comb2.toUInt64)
    let comb4 ← crc_word (st.crc4 ^^^ lw4 ^^^ comb3.toUInt64)
    let words ← st.words.add 40
    crc := comb4
    buf := words
  return ~~~(← crc32_copy_small crc .null buf len 39 0)

/-- `Z_INTERNAL uint32_t crc32_copy_braid(uint32_t crc, uint8_t *dst, const uint8_t *src, size_t len)`
(`crc32_braid_c.c:213-217`). -/
def crc32_copy_braid (crc : UInt32) (dst : BPtr) (src : BPtr) (len : UInt64) : M UInt32 := do
  let crc ← crc32_braid crc src len
  Ptr.memcpy dst src len.toNat
  return crc

end ZlibNg.Crc32Braid
