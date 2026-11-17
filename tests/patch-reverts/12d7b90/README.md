# 12d7b90: repeated `deflatePrime` writes past the pending buffer

- **Fix:** upstream commit `12d7b90980910fcd7713e58cedcca046acb5a55f`, "Check deflatePrime pending
  capacity" (Trail of Bits, TOB-ZLIB-013), in zlib 1.4.
- **Revert** (`revert.patch`, `lean.patch`): `deflatePrime` refuses only when
  `s->sym_buf < s->pending_out + ((Buf_size + 7) >> 3)` (the branch without `LIT_MEM`, as built); it
  no longer moves pending output to the buffer start nor compares the bytes it writes with the room
  left.
- **Calls** (`trigger.c`, `model.lean`): `deflateInit2` with `memLevel` 1 (a pending buffer of 512
  bytes); up to 300 calls `deflatePrime(16, 0x1234)`, stopping at the first that does not return
  `Z_OK`; `deflateEnd`. Without `deflate`, `pending_out` does not move, so the old check never
  refuses.
- **C:** with the revert, ASan reports a heap-buffer-overflow write in `bi_flush` (from
  `_tr_flush_bits`). Without it, no report: 256 calls succeed and the 257th returns `Z_BUF_ERROR`.
- **Model:** with the revert, `Fault.ub` "store outside its object". Without it, the line `trigger.c`
  prints.
- **Domain:** inside `Goal.deflatePrime_safety`: the stream is reached by `deflateInit2` and
  `deflatePrime` calls, and it has not started (`DeflateNotStarted`), which is the only argument
  premise of `deflatePrime`. Checked by reading the premises.
