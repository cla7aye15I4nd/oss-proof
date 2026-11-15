<!-- source-sha256: 9f36b0f415427014a9b548a6407422f6fb111ed9bc5e718202da38d5012b4752 -->
# 文档

这个目录存放文档网站的内容源码。本页说明从哪里读起，以及这些源码怎样变成网站。

[文档网站](https://www.dataisland.org/zlib-f/index.zh.html)是正式阅读入口。这里的文件是网站内容源码。网站只从 `main` 分支发布；推送到 `dev` 和拉取请求只构建并检查，不发布。因此网站可能落后于 `dev`。每个页面末尾写明它所构建自的提交和日期。

## 从哪里开始

- [总览](overview.md)：证明了什么、假设了什么，以及证明是怎样搭起来的。
- [结果与状态](progress.md#scope)：唯一记录状态的页面。三项计划内的安全结论，它们各自的层级（已检查、已登记、已验收）和对应的提交，以及哪些不在计划内。网站的首页和状态页展示同样的事实。
- [按函数查覆盖情况](coverage.md)：每个函数的安全定理及其定义域。
- [偏离记录](deviations.md)：一次调用要满足什么才被定理覆盖，按函数列成核对清单。
- [可信基础](trusted-base.md)与[模型的限制](model-limits.md)：内核不检查的六件事，以及模型的限制。
- [术语表](glossary.md)：规格与证明中用到的术语。
- [参与贡献](checking/contributing.md)：编号步骤与命令。

## 阅读 zlib 文章 {#articles}

1. [基础压缩：LZ77 与 Huffman](articles/foundations.zh.md)。
2. [zlib 的实现与优化](articles/optimizations.zh.md)。
3. [zlib 的功能扩展：流式处理与校验](articles/features.zh.md)。

每篇都有完整的中英文版本。算法系列讲解 zlib 本身；形式化验证使用下面独立的参考资料。

## 参考资料 {#reference}

- [规格](spec/README.md)：平台范围、安全性、输入范围、公开 API 契约、内部辅助函数契约与压缩字节的含义。
- [模型](design/README.md)：翻译、内存语义和外部输入输出。
- [实现论证](proof/README.md)：验证方法，以及各个 C 组件的详细论证。
- [检查指南](checking/README.md)：每项检查能确立什么，一项结论怎样成为已验收。
- [验证策略](anti-cheating.md)：验收套件能挡住哪些作弊方式。
- [证据索引](progress.md)：每个目标的命题、证明与依赖。

[发现](findings.md)记录已确认的报告及其范围。
[Sanitizer 报告](sanitizer-reports.md)列出每个 sanitizer 复现以及排除它的前提。
[运行时结构](runtime-schema.md)提供字段与类型参考。

## 历史 {#history}

`history/` 下的页面是带日期的记录，原样保留。它们描述的是写下它们的那个时候：其中的状态、数字和工时都不是现在的事实。现在的状态只记在[进度](progress.md)中。

- 证明骨架，即四个核心证明自顶向下的计划：[inflate](history/skeleton-inflate.md)、[deflate](history/skeleton-deflate.md)、[gzip 文件接口](history/skeleton-gz.md)、[回调解码器](history/skeleton-inflate-back.md)。
- 进度与总览：[进度检查点](history/progress-checkpoints.md)、[早先的工作顺序与准备情况说明](history/next-work-and-readiness.md)、[总览变更记录](history/overview-changelog.md)。
- 覆盖情况：[审查记录](history/coverage-review-record.md)、[早先的未完成项](history/coverage-open-items.md)。
- 规格：[规格审查记录](history/specification-review.md)、[安全与功能拆分的计划](history/safety-functional-split-plan.md)、[deflate 内部证明范围](history/deviations-internal-scopes.md)。
- 早先的目标 `DeflateCompletes` 的命题更正记录：[FINISH 之后出现新输入](history/deflate-completion-input.md)、[NULL 输出](history/deflate-completion-null-output.md)。
- 证明笔记：[早期证明笔记](history/proof-earlier-notes.md)、[早先关于功能证明需要什么的笔记](history/proof-functional-notes.md)、[早期论证与参考来源](history/references.md)。
- 锁文件时期的审查记录：[本地证明登记检查](history/registration-review.md)、[公开查询登记审查](history/query-registration-review.md)、[已审查的递归执行辅助声明](history/compiler-helper-review.md)。

## 构建与本地预览 {#local}

文章源码放在 `articles/`。网站构建、交互、样式和测试放在 `web/`。API 返回值表与完整契约一起写在 `spec/api/` 中。英文及相邻的 `.zh.md` 中文各自只维护一份，网页和函数视图由它们生成。
依赖和构建命令见网站指南 `web/README.md`。
