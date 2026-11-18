<!-- source-sha256: 912f8acb3459a74d1034619d98b3437b7bbf05a3fb2fb087a511d644ceb3ddc6 -->
# 7-Zip C SDK

验证对象：便携标量 x86_64 Linux LP64 配置下的官方 `7-Zip` 纯 C SDK（`C/7zArcIn.c`、`C/7zDec.c`、`C/Bcj2.c`、
`C/Ppmd7.c`、`C/Ppmd7Dec.c`、`C/LzmaDec.c`、`C/Lzma2Dec.c`）。

## 范围

- **`.7z` 容器与解码器有向无环图（`7zArcIn.c`、`7zDec.c`）：** 两阶段 `EncodedHeader` 解析、`CSzFolder` / `BindPairs`
  拓扑校验、`SubStreams` 切分与 `SzArEx_Extract` 固实文件夹缓存。
- **BCJ2 四流 x86 滤波器（`Bcj2.c`）：** 四路输入流同步推进与相对跳转地址重建。
- **PPMd7 上下文解码器与自定义子分配器（`Ppmd7.c`、`Ppmd7Dec.c`）：** 内存池分区不变量、`SplitBlock` / `GlueFreeBlocks`
  空闲链表与 32 位偏移指针上下文树。
- **LZMA 与 LZMA2 解码器（`LzmaDec.c`、`Lzma2Dec.c`）：** 环形字典索引、快速前瞻边界与分块状态重置。

## 当前已证明的内容

顶层状态机与内存池模型（`SevenZipF.Model`）以及严格 ISO C17 运行时未定义行为拒绝定理（`SevenZipF.Runtime`）已由
Lean 4 内核检查通过。C 源码的逐语句翻译与公开 C 入口函数的端到端安全性证明尚未完成。
