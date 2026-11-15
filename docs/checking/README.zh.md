<!-- source-sha256: 15a101c12c94570ec46499e4f4caa64cdc283b378590629bb8fe6f509d0eeeec -->
# 检查一个验证结论

构建通过只说明各模块能编译，并不说明 zlib 已被验证。本页说明每项检查运行什么、能证明什么、局限在哪里。要运行这些检查，请读[参与贡献](contributing.md)。当前状态与计划范围见[结果页](../progress.md#scope)。

## 两个层级

- **已检查。** 定理在 `dev` 上，且该提交上快速关卡为绿。Lean 内核已检查证明。日常工作在这一层级合并。
- **已验收。** 定理还列在 `tests/audit/theorems.txt` 中，且验收套件在某个具名提交上全部通过。只有已验收的结论才可作为最终结论报告。

## 两组检查

两组检查都是工作流 `.github/workflows/lean.yml` 中的作业。

```mermaid
flowchart LR
    P["推送到 dev"] --> G["快速关卡"]
    G --> C["已检查"]
    C --> M["里程碑批处理：登记、变异、进度视图"]
    M --> A["在具名提交上运行验收套件"]
    A --> R["已验收；main 接收 dev"]
```

### 快速关卡

每次推送到 `dev` 或 `main`、每个拉取请求都会运行它。它是合并的唯一关卡。

| 作业 | 步骤 | 什么会使它失败 |
| --- | --- | --- |
| `build` | 构建库和审计工具 | `ZlibF` 的某个模块不能编译；某个证明被内核拒绝。 |
| `build` | 构建差分驱动程序 | `tests/list.txt` 中的某个驱动程序不能针对翻译编译。驱动程序在这里构建，只在验收套件中运行。 |
| `build` | 被禁止的构造 | `ZlibF` 源码文本中出现 `native_decide`、`bv_decide`、`implemented_by`、`axiom`、`partial`、`unsafe`、`opaque` 或 `extern`。 |
| `build` | 没有 unsafe 或 partial 声明（`tests/audit/PartialCheck.lean`） | 编译后的声明被标为 unsafe 或 partial，而它不在编译器辅助声明清单（`tests/audit/compiler-helpers.txt`）中。 |
| `build` | 补丁可应用 | `patches/` 中的某个文件不能应用到固定版本 `zlib/` 的副本上。 |
| `no-sorry` | `scripts/check-sorry.sh` | Lean 源码中有 `sorry`。 |
| `no-sorry` | `scripts/check-strlit.py` | 翻译中的某个字符串字面量不在运行时的字符串表中。 |
| `no-sorry` | `scripts/check-spec-layers.py` | `ZlibF/Spec/Safety/` 或 `ZlibF/Spec/Public/` 下的模块导入了功能规范（`ZlibF/Spec/Functional/`，或旧路径 `ZlibF/Spec/Api*`、`ZlibF/Spec/Format*`），间接导入也算。脚本中有一张仍被允许的导入边的清单；该清单只能缩小。 |

快速关卡不读取登记表。快速关卡为绿，并不说明哪些目标已被证明。

### 验收套件

它每晚在 `main` 上运行，也可按需运行（`lean` 工作流的手动触发，可用于任何分支）。它有两个必需结果：`audit` 和 `difftest`。任何一个工作单元失败、被跳过或被取消，对应的结果就失败。

| 结果 | 工作单元 | 运行什么 |
| --- | --- | --- |
| `audit` | `audit_core` | `python3 scripts/verification.py specs`：公开函数清单、对整个库的全新内核复查、声明审计，以及下面的登记表规则。随后运行 `tests/verification/` 下对审计工具和脚本的测试，以及 `scripts/proof-progress.py --check`；进度视图过时时后者失败。 |
| `audit` | `audit_selftest`，两个分片 | `tests/audit/selftest.sh`：`tests/audit/cheats/` 中的每个文件（一个 `sorry`、一条公理、`native_decide`、`implemented_by`、不透明常量、partial 或 unsafe 定义、一个经典逻辑花招）都必须被审计工具拒绝。 |
| `audit` | `audit_mutants`，二十个分片 | `python3 scripts/verification.py mutants --shard-count 20 --shard-index N`：[证明变异](proof-mutants.md)。 |
| `difftest` | `diff_core` | `tests/run.sh`：翻译与打过补丁的 C 在相同输入上比较。然后在 AddressSanitizer 和 UndefinedBehaviorSanitizer 下构建 C，再比较一次。 |
| `difftest` | `diff_harness`，八个分片 | `tests/selftest.sh`：变异后的翻译必须让差分测试报告差异。 |

夜间运行变红时，先修复它再做新的验收工作，但它不阻塞证明工作。验收工作在里程碑时成批进行，不是每次改动都做。

**带判定复用的预检。**手动触发有一个输入 `reuse`。打开时，变异分片跳过这样的证明变异：其输入与某次已通过的执行逐字节相同；并输出运行了多少单元、复用了多少单元。此时结果以 `audit (pre-check, reused verdicts)` 的名称报告。它是给 `dev` 和各分支用的较快检查。它不是验收：已接受的结果需要在你指明的提交上做一次不带该输入的完整运行。夜间运行总是完整运行。[证明变异](proof-mutants.md#verdict-reuse)说明键覆盖什么。

`python3 scripts/verification.py final` 从干净构建开始，在一个进程中运行整个套件，以严格模式运行每个变异列表，并输出提交号。工作流 `verification-final` 由人工针对指定提交启动它。每晚的套件不运行它。

## `verification.py specs` 判定什么

脚本读取 `tests/audit/` 下的四个登记表。[公开目标](goals.md)说明这些登记表。

1. **清单。** `public-api.json` 中的函数恰好是固定版本 `zlib.h` 导出的函数。每个函数都有手册章节、翻译后的入口和功能目标。每个有文档的函数都有安全目标。清单中的各目标组与脚本中固定的列表相等。源码固定版本等于子模块提交，且子模块没有本地改动。
2. **全新内核。** `leanchecker --fresh ZlibF` 复查编译后的证明项。
3. **声明审计。** 审计工具（`tests/audit/Audit.lean`）读取编译后的模块。它拒绝公理、不透明常量、`implemented_by`、`extern`，以及不在编译器辅助声明清单中的 unsafe 或 partial 声明。每个定义和定理只能依赖 `propext`、`Classical.choice` 和 `Quot.sound`。`theorems.txt` 中的每个定理都存在、确实是定理，并且有文档字符串。每个 `Goal.*` 命题都列在 `goals.txt` 中。只有当某个已列出的定理的类型恰好就是目标时，该目标才算 PROVED。
4. **登记表一致。** `proved-goals.txt` 等于审计工具判定为 PROVED 的目标集合。每个必需目标要么是 PROVED，要么列在清单的 `open_safety` 中；列在 `open_safety` 中的目标不是 PROVED。
5. **只减不增规则。** 沿提交链，已登记的定理、已证明的目标、变异引用和冻结的变异行都不会消失，除非 `registry-removals.json` 中有带理由的条目。已经关闭的目标不会重新变成未完成。规则见[公开目标](goals.md#shrink-only-rules)。
6. **变异证据。** 针对单个公开函数的每个已证明目标都有函数变异。每个已证明的必需目标要么在 `public-mutants.json` 中有键，要么有固定证据（[证明变异](proof-mutants.md#which-goals-need-which-evidence)）。

## 这些检查能证明什么

| 检查 | 证据与局限 |
| --- | --- |
| 内核重放与公理审计 | 检查证明项及其依赖。只允许 `propext`、`Classical.choice` 和 `Quot.sound`。正确的证明仍可能回答了一个不完整的问题。 |
| 命题精确匹配 | 登记的定理的类型必须就是固定目标。多余的前提、相似的名字或抽象模型上的定理都不算数。目标说得够不够，由审查决定。 |
| 无占位符检查 | 拒绝 `sorry` 和 `AGENTS.md` 列出的其他被禁止的构造。 |
| 差分测试 | 把翻译后的执行与真实 C 比较，包括错误和分配失败。它们是忠实度的有限证据，不是证明。Sanitizer 运行扩展了这一证据。 |
| 审计与差分自测 | 故意破坏输入，要求检查机制发现变化。 |
| 证明变异 | 改变翻译函数的行为，要求该函数的证明拒绝它。敏感并不证明所有错误都被覆盖。 |

## 已知限制

- **检查工具本身是受信任的。** 审计工具（`tests/audit/*.lean`）、`scripts/`、`tests/audit/proofmut.sh`、`tests/audit/selftest.sh` 和变异脚本（`tests/proof-mutants/*.py`）靠对其差异的审查来保护，没有另一项检查来保护它们。
- **复用的判定与脚本一样受信任。** 预检相信键相符的已存储记录。存储在工作流缓存中；某个分支或 `main` 上的运行可以写入该分支上的预检所读取的存储。完整运行不读取任何存储。见[证明变异](proof-mutants.md#verdict-reuse)。
- **带理由的删除条目是经过审查的出口。** `tests/audit/registry-removals.json` 中带理由的条目可以为某一个名称解除只减不增规则。它在差异中可见。什么也不豁免的条目会被当作过时条目拒绝。
- **提交链从固定的下限提交开始。** 只减不增规则读取脚本中固定的两个提交之后的历史。在下限之后改写历史的强制推送会逃过这些规则。防范手段是禁止强制推送的分支保护。
- **`script:` 变异行靠阅读来检查。** 执行器防范坏变异的保护把第一个错误与该行的文件比较，而脚本行的文件就是脚本本身。见[证明变异](proof-mutants.md#known-limits)。
- **没有锁文件。** 定义、规范和定理陈述只由 git 跟踪，对它们的改动只体现在差异中。陈述是否说得足够、运行时是否代表 C、翻译是否与源码一致，都由审查决定。

[防止取巧的规则](../anti-cheating.md)说明验收套件防御什么、不防御什么。错误的陈述要纠正，不能绕过：见 `AGENTS.md`。

## 指南与记录

| 页面 | 用途 |
| --- | --- |
| [参与贡献](contributing.md) | 从克隆到已验收结论的编号步骤与命令。 |
| [公开目标](goals.md) | 登记表、必需目标集合和只减不增规则。 |
| [证明变异](proof-mutants.md) | 如何添加、运行并解读变异检查，以及它们的限制。 |

本目录其余页面是过去审查的带日期记录。它们保存证据和范围，不是当前流程，也不是当前缺陷清单。每一页开头都有说明，写明成文时间和此后的变化。

| 记录 | 内容 |
| --- | --- |
| [公开契约审查](contract-review.md) | 陈述层次、源码审查的更正与反例；成文于范围改为只做安全性之前。 |
| [本地登记审查](registration-review.md) | 已记录的本地登记检查当时证明了什么。 |
| [查询函数登记审查](query-registration-review.md) | 六个精确的公开查询及其变异证据。 |
| [编译器辅助函数审查](compiler-helper-review.md) | 生成的递归执行辅助函数及其逻辑对应物。 |
| [运行时审查](runtime-review.md) | 发现 R1–R13 与翻译问题 U1–U5，以及它们现在的状态。 |
| [堆表审查](runtime-tables-review.md) | 关于数组表和原地更新的发现 F1–F6，以及它们现在的状态。 |
