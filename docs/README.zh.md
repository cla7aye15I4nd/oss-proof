<!-- source-sha256: 118c7f2848a250580e227409a9e5a40dd64cad4b165e1aae5e018733984a3cf6 -->
# 文档

本页是文档的索引：从哪里读起，每一部分讲什么。这份文档说明关于 zlib 形式化验证了什么、假设了什么，以及证明是怎样进行的。[文档网站](https://www.dataisland.org/zlib-f/index.zh.html)展示的是同样的页面。

## 从哪里开始

- [总览](overview.md)：证明了什么、假设了什么，以及证明是怎样搭起来的。
- [结论的状态](progress.md)：每项结论、每个公开函数是完成还是未完成，以及哪些不在计划内。只有这一页说明状态。
- [按函数查覆盖情况](coverage.md)：每个函数的安全定理及其定义域。
- [偏离记录](deviations.md)：一次调用要满足什么才被定理覆盖，按函数列成核对清单。
- [完成的结论依靠什么](checking/README.md)：Lean 内核检查了什么，哪些是证据而不是证明。
- [可信基础](trusted-base.md)与[模型的限制](model-limits.md)：内核不检查什么，以及模型可能与 C 不同的地方。
- [术语表](glossary.md)：规格与证明中用到的术语。

## 阅读 zlib 文章 {#articles}

1. [基础压缩：LZ77 与 Huffman](articles/foundations.zh.md)。
2. [zlib 的实现与优化](articles/optimizations.zh.md)。
3. [zlib 的功能扩展：流式处理与校验](articles/features.zh.md)。

每篇文章都有英文版和中文版。这些文章讲解 zlib 本身；形式化验证使用下面独立的参考资料。

## 参考资料 {#reference}

- [规格](spec/README.md)：平台范围、安全性、输入范围、公开 API 契约、内部辅助函数契约与压缩字节的含义。
- [模型](design/README.md)：翻译、内存语义和外部输入输出。
- [证明](proof/README.md)：验证方法，以及各个 C 组件的论证。
- [为什么构建通过还不够](anti-cheating.md)：为什么证明能通过编译还不够，这些结论防范了什么。
- [发现](findings.md)：已确认的关于 zlib 的报告及其范围。
- [Sanitizer 报告](sanitizer-reports.md)：每个 sanitizer 复现，以及排除它的前提。
- [运行时结构](runtime-schema.md)：模型中各记录的字段与类型参考。
