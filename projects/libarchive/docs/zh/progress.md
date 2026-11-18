<!-- source-sha256: e06f396458ccd26410bc23af74f9f60b4970108eb8a31a235bd8f4920ddd05d2 -->
# 结论的状态

整体库验证状态：**未完成**。

| 领域 | 类别 | 状态 |
| --- | --- | --- |
| 严格 ISO C17 指针与 `memset` 未定义行为拒绝定理（`LibarchiveF.Runtime`） | 运行时模型 | 完成 |
| RAR5 表示不变量、固实跳过与清理保持性（`LibarchiveF.Model`） | 顶层模型 | 完成 |
| RAR5 滤波器节流无死锁与位读取器推进定理（`LibarchiveF.Model`） | 顶层模型 | 完成 |
| 7-Zip 文件夹有向无环图端口守恒、子流边界与 PPMd7 内存池初始化（`LibarchiveF.Model`） | 顶层模型 | 完成 |
| `archive_read_support_format_rar5.c` 翻译后 C 安全性 | 公开 C 接口 | 未完成 |
| `archive_read_support_format_7zip.c` 翻译后 C 安全性 | 公开 C 接口 | 未完成 |
| `archive_ppmd7.c` 翻译后 C 安全性 | 公开 C 接口 | 未完成 |
