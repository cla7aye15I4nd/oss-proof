<!-- source-sha256: c53e4d2ecce327dd53039c327fe3bfff15afbf1c858586eae0bbb84a4446ae1f -->
# gzip extra 字段长度为 2^32 − 2 或 2^32 − 1 时的 `deflateBound`

对一个 gzip 流，如果它的头部由 `deflateSetHeader` 设置，且 `extra_len` 等于 2^32 − 2 或 2^32 − 1，`deflateBound` 返回的界大约小了 64 KiB。于是用这么多空间做一次 `deflate(Z_FINISH)` 调用会返回 `Z_OK`，违背了 `zlib.h` 关于这样的调用返回 `Z_STREAM_END` 的承诺。这是失信，不是内存错误。

`deflateBound` 把 `2 + s->gzhead->extra_len` 加到封装长度上。`extra_len` 的类型是 `uInt`，所以这个和按 32 位计算，对这两个长度回绕成 0 或 1。`deflate` 写出该字段的 `extra_len & 0xffff` 个字节（65534 或 65535）。

对 2^16 到 2^32 − 3 之间的 `extra_len`，界按 `extra_len` 个字节计，而 `deflate` 写得更少：界是保守的，不是错的。

## 到达它的调用

`zlib.h` 要求 `extra` 处有 `extra_len` 个字节可用，对 `extra_len` 没有规定上限。gzip 头部的 extra 字段最多容纳 65535 个字节，所以这两个长度是格式存不下的长度。

```c
deflateInit2(&s, level, Z_DEFLATED, 31, 8, Z_DEFAULT_STRATEGY);   /* gzip */
head.extra = extra;
head.extra_len = 0xffffffffu;        /* 或 0xfffffffeu */
deflateSetHeader(&s, &head);
bound = deflateBound(&s, n);         /* 2 + extra_len 回绕 */
deflate(&s, Z_FINISH);               /* 输出空间为 bound 个字节：返回 Z_OK */
```

## 证据

真实 C 上的一个 C 驱动程序（`tests/goals/deflate-bound/bound.c`，模式 `extra`）设置五个长度，调用 `deflateBound`，再用这么多空间调用带 `Z_FINISH` 的 `deflate`。恰好是上面两个长度失败：对 100 个输入字节，界是 125 和 126。`tests/goals/deflate-bound/run.sh` 只有在恰好这两个失败时才通过。

## 修复

无。没有补丁改变这个和。上游已知这种情形（[拉取请求 1360 中的讨论](https://github.com/madler/zlib/pull/1360)）。

## 与证明的关系

没有安全目标依赖这个界的值。这个值的规格（`WrapperLength`）按 32 位计算 `2 + extra_len`，与 C 和翻译相同。对头部由 `deflateSetHeader` 设置的流，陈述 `zlib.h` 这项承诺的命题需要一条排除这两个长度的前提。
