# Skip inflateSync input search when avail_in is zero

## Problem

When `inflateSync()` runs on a stream with primed bits (`inflatePrime()`) and empty caller input (`strm->next_in == NULL`, `strm->avail_in == 0`), it still calls `syncsearch(&(state->have), strm->next_in, strm->avail_in)` and executes:

```c
strm->next_in += len;
```

Even when `len == 0`, evaluating `NULL + 0` is undefined behavior in ISO C17 §6.5.6p8.

## Fix

Skip the search when `strm->avail_in == 0` and advance `strm->next_in` only when `len != 0`:

```c
    if (strm->avail_in) {
        len = syncsearch(&(state->have), strm->next_in, strm->avail_in);
        strm->avail_in -= len;
        if (len)
            strm->next_in += len;
        strm->total_in += len;
    }
```

Add `inflate.sync_primed_bits_with_empty_input` in `test/test_inflate_sync.cc`.

## Testing

- Clang (`ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, ASan + UBSan + C pointer-pair) and Clang (`ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, ASan + UBSan): `inflate.sync_primed_bits_with_empty_input` passes in both builds (C sanitizers do not dynamically flag `NULL + 0`; the fix is verified by source inspection against ISO C17 §6.5.6p8).
