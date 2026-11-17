# local-0001: `inflateCopy` compares pointers into different objects

- **Fix:** patch 0001 (`patches/0001-inflate-copy-pointer-equality.patch`), the change of upstream
  PR 1369, which the maintainer applied after zlib 1.4.
- **Revert** (`revert.patch`, `lean.patch`): `inflateCopy` tests
  `state->lencode >= state->codes && state->lencode <= state->codes + ENOUGH - 1` again and relocates
  `lencode` by its difference from `codes`.
- **Calls** (`trigger.c`, `model.lean`): `inflateInit`; `inflate` on a zlib stream of one fixed-code
  block with seven bytes of output room, so that it stops inside the block while `lencode` points to
  the static table `lenfix`; `inflateCopy`; `inflateEnd` of the source; `inflate` on the copy to
  the end.
- **C:** with the revert, ASan reports `invalid-pointer-pair` in `inflateCopy` (GCC; the pointer-pair
  check of clang reports a comparison inside `inflate` on both sources, so the case uses GCC).
  Without it, no report, and the copy decodes all 128 bytes.
- **Model:** with the revert, `Fault.ub` "comparison of pointers into different objects". Without it,
  the line `trigger.c` prints.
- **Domain:** inside `Goal.inflateCopy_safety`, third clause: the source is reached by `inflateInit`
  and `inflate` with the default allocator, and the destination is a distinct, readable record.
  Checked by reading the premises.
