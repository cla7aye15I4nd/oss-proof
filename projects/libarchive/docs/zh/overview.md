<!-- source-sha256: 14f0f2e5030ea7e254a24e89ea2b74135d6a17fd3385ed8eefb96f815893bdba -->
# libarchive（RAR5 与 7-Zip）

验证对象：默认标量 x86_64 Linux LP64 配置下 `libarchive` 的 RAR5（`archive_read_support_format_rar5.c`）与
7-Zip（`archive_read_support_format_7zip.c`、`archive_ppmd7.c`）归档格式解码器。

## 范围

- **RAR5 解码器：** 变长整数（`vint`）头部解析、固实与分卷状态重置、四表霍夫曼位读取器严格推进、环形 LZSS 窗口索引，
  以及 E8/E8E9/Delta/ARM 解压后滤波器队列。
- **7-Zip 解码器：** 两阶段 `EncodedHeader` 引导、`Folder` / `BindPairs` 多解码器有向无环图端口守恒、固实
  `SubStreamsInfo` 解压大小边界与 PPMd7 子分配器。

## 当前已证明的内容

RAR5 与 7-Zip 解码器的顶层状态与不变量模型（`LibarchiveF.Model`）以及严格 ISO C17 运行时未定义行为拒绝定理
（`LibarchiveF.Runtime`）已由 Lean 4 内核检查通过。C 源码逐语句翻译与 `archive_read_*` 回调序列安全性证明尚未完成。
