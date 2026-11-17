<!-- source-sha256: 19501e8a612a88dbb8400d3e0c527542542bd1f4a3c3ade1519c3ad87aa1ce39 -->
# zlib-f

用 Lean 4 写成、由机器检查的证明：zlib 中每个有文档的公开函数都是安全的。没有未定义行为，没有内存错误，没有泄漏，每个调用都返回。对每一个输入、每一种调用序列都成立。

对象是 zlib 1.4 在 x86_64 Linux 上的默认构建：86 个函数。每个证明都由 Lean 的内核检查。

## 证明了什么

- `inflate` 对每个输入都是安全的，无论调用者怎样把缓冲区拆分到多次调用中。
- `deflate` 对每个输入都是安全的，无论调用者怎样把缓冲区拆分到多次调用中。
- 其他每个有文档的函数都是安全的：`compress` 和 `uncompress`、校验和、从 `gzopen` 到 `gzclose` 的 gzip 文件接口，以及回调解码器 `inflateBack`。
- 默认 zlib 流的往返：给 `compress` 留出 `compressBound` 的空间时，`uncompress(compress(x)) = x`；在每次分配都成功时，先 `deflate` 再 `inflate`，在每一种调用序列下都得到原输入。

每条定理都写明它的前提。有些前提超出了 `zlib.h` 的要求：调用者的缓冲区互不重叠，使用默认分配器，gz 读取调用的终止需要读取预算低于 2^61 字节，一次 `inflateBack` 调用的输入少于 2^48 字节。[偏离记录](docs/deviations.md)按函数列出这些前提。

## 结论依靠什么

C 被逐条语句翻译成 Lean。C 能到达的每一种未定义行为，在翻译中都是一个故障，而定理说的是故障不会发生。翻译、内存模型和命题本身是被信任的，没有被证明：[可信基础](docs/trusted-base.md)共六项，逐项列出。差分测试把翻译与真实的 C 作比较；它们是两者一致的证据，不是证明。

## 在 zlib 中发现的问题

九个问题，每个都能通过有文档的调用到达：七个是未定义行为或内存错误，两个是 `deflateBound` 给出的界太小。六个补丁修复了其中八个；其中三个补丁就是已提交上游的修复。定理说的是打过补丁的源码。[发现](docs/findings.md)给出表格，[补丁](patches/README.md)说明每个补丁。

## 没有声称什么

这一往返之外的功能正确性。其他配置下的往返没有证明：其他压缩级别、策略、窗口大小和封装，预设字典，gzip 文件接口或 `inflateBack`。除了调用是安全的之外，没有定理说 `inflate` 对格式拒绝的流做什么。这些都不在计划内。同样不在范围内的还有：其他构建配置、自定义分配器，以及 `zlib.h` 列为未文档化的函数。

## 自己检查

```bash
lake build ZlibF
scripts/check-sorry.sh
```

第一条命令编译每个模块，于是 Lean 的内核检查每一个证明。如果源码中还留有 `sorry`（被承认而未证明的步骤），第二条命令就失败。最大的几个模块各需要 8 到 9 GB 内存。

## 延伸阅读

- [文档网站](https://www.dataisland.org/zlib-f/)
- [概览](https://www.dataisland.org/zlib-f/reference/docs/overview.html)：证明是怎样构建的
- [状态](https://www.dataisland.org/zlib-f/reference/docs/progress.html)：每项结论和每个函数
- [覆盖情况](https://www.dataisland.org/zlib-f/reference/docs/coverage.html)：每个函数对应的定理
- [可信基础](https://www.dataisland.org/zlib-f/reference/docs/trusted-base.html)：没有被检查的东西
