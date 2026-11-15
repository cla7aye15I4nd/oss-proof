<!-- source-sha256: fb49f0627f18b4005dd9d51d2d6d839e1ca4b999aebc1a9da64a9e0c40385331 -->
# 检查一个验证结论

构建全部通过，说明各模块能够编译，其中每个证明都经过了 Lean 内核的检查。它并不说明关于 zlib 的哪些命题已被证明。本页说明一个结果处于哪个层级，每项检查运行什么、能确立什么，以及它的局限在哪里。

要运行这些检查，请读[参与贡献](contributing.md)。要添加变异体，请读[证明变异体](proof-mutants.md)。各登记表的含义见[公开目标](goals.md)。

## 三个层级

每个层级都包含前一个层级。定义就是[术语表](../glossary.md#status)中的定义，措辞相同。

| 层级 | 成立的事实 | 在哪里看到 |
| --- | --- | --- |
| **已检查** | 定理在集成分支 `dev` 上，并且快速关卡在该提交上全部通过。Lean 内核检查过这个证明。 | 工作流 `lean` 在该提交上的 `build` 和 `no-sorry` 两项结果。 |
| **已登记** | 定理已检查，它的名字列在 `tests/audit/theorems.txt` 中，它证明的目标列在 `tests/audit/proved-goals.txt` 中。这两行是一个声明；检查“定理的类型与目标完全相同”的，是验收套件。 | 该提交上的这两个文件。[进度页的“目标证据”](../progress.md#target-evidence)中生成的表格列出每个目标对应的定理。 |
| **已验收** | 定理已登记，并且验收套件在某个具名提交上全部通过。只有已验收的结论才作为最终结论报告，而且总是带着那个提交。 | 工作流 `lean` 在该提交上的 `audit` 和 `difftest` 两项结果，以及[进度页“范围”一节](../progress.md#scope)中“验收套件在……上全部通过”那句话。 |

已验收的提交是 `bde170e9`（2026-11-15）：全部 63 个必需目标在该提交上已登记，验收套件在该提交上全部通过。如果某个目标的命题在更晚的提交上改动过，它的新形式是已登记，已验收的只是它在 `bde170e9` 上的形式。初始化函数的四个安全目标就是这种情况：提交 `101c6ab3` 把它们的范围扩大到 zlib.h 允许的每一次调用。保持最新的页面是[进度页](../progress.md#scope)。

没有已登记定理以它为类型的目标是**未证明**的。

```mermaid
flowchart LR
    P["推送到 dev"] --> G["快速关卡"]
    G --> C["已检查"]
    C --> M["里程碑批次：登记行、变异体、进度视图"]
    M --> R["已登记"]
    R --> A["在具名提交上运行验收套件"]
    A --> F["已验收；main 接收 dev"]
```

## 两组检查

两组检查都是工作流 `.github/workflows/lean.yml` 中的作业。

### 快速关卡

每次推送到 `dev` 或 `main`、每个拉取请求都会运行它。它是合并的唯一关卡。

| 作业 | 步骤 | 什么会让它失败 |
| --- | --- | --- |
| `build` | 构建库和审计工具 | `ZlibF` 中有模块无法编译。有证明被内核拒绝。 |
| `build` | 构建差分驱动程序 | `tests/list.txt` 中有驱动程序无法对着翻译编译。驱动程序在这里只构建，到验收套件中才运行。 |
| `build` | 禁用构造 | `ZlibF` 的源码文本中出现 `native_decide`、`bv_decide`、`implemented_by`、`axiom`、`partial`、`unsafe`、`opaque` 或 `extern`。 |
| `build` | 没有 unsafe 或 partial 声明（`tests/audit/PartialCheck.lean`） | 编译后的声明被标为 unsafe 或 partial，而它不是列出的编译器辅助声明（`tests/audit/compiler-helpers.txt`）。 |
| `build` | 补丁可以应用 | `patches/` 中有文件无法应用到固定的 `zlib/` 的副本上。 |
| `no-sorry` | `scripts/check-sorry.sh` | `ZlibF.lean` 或 `ZlibF/` 下出现 `sorry`。 |
| `no-sorry` | `scripts/check-strlit.py` | 翻译中的某个字符串字面量不在运行时的字符串表中。 |
| `no-sorry` | `scripts/check-spec-layers.py` | `ZlibF/Spec/Safety/` 或 `ZlibF/Spec/Public/` 下的模块导入了功能规格（`ZlibF/Spec/Functional/`，或旧路径 `ZlibF/Spec/Api*`、`ZlibF/Spec/Format*`），间接导入也算。脚本保存一份仍被允许的导入边的列表；列表中的条目可以删除，不可以新增。 |

快速关卡不读登记表。快速关卡全部通过，并不说明哪些目标已被证明。

### 验收套件

它每晚在 `main` 上运行，也可以按需运行（`lean` 工作流的手动触发，可用于任何分支）。它有两项必需的结果：`audit` 和 `difftest`。任何一个工作任务失败、被跳过或被取消，对应的结果就失败。

| 结果 | 工作任务 | 运行什么 |
| --- | --- | --- |
| `audit` | `audit_core` | `python3 scripts/verification.py specs`：函数清单检查、在全新内核中重新检查整个库、声明审计，以及下文的登记表规则。然后运行 `tests/verification/` 下针对审计器和脚本的测试，以及 `scripts/proof-progress.py --check`；进度视图过时时后者失败。 |
| `audit` | `audit_selftest`，两个分片 | `tests/audit/selftest.sh`：`tests/audit/cheats/` 中的每个文件（一个 `sorry`、一条公理、`native_decide`、`implemented_by`、一个 opaque 常量、一个 partial 或 unsafe 定义、一个经典逻辑的取巧）都必须被审计器拒绝。 |
| `audit` | `audit_mutants`，二十个分片 | `python3 scripts/verification.py mutants --shard-count 20 --shard-index N`：[证明变异体](proof-mutants.md)。 |
| `difftest` | `diff_core` | `tests/run.sh`：让翻译和打过补丁的 C 处理相同的输入。然后用 AddressSanitizer 和 UndefinedBehaviorSanitizer 构建 C，再做一遍。 |
| `difftest` | `diff_harness`，八个分片 | `tests/selftest.sh`：变异后的翻译必须让差分测试报告出差异。 |

夜间运行失败时，先修复它，再做新的验收工作。它不阻塞证明工作。验收工作在里程碑处成批完成，不是每次改动都做。

**带判定复用的预检。**手动触发有一个输入 `reuse`。打开时，变异分片跳过这样的证明变异：其输入与某次已通过的执行逐字节相同；并输出运行了多少单元、复用了多少单元。此时结果以 `audit (pre-check, reused verdicts)` 的名称报告。它是给 `dev` 和各分支用的较快检查。它不是验收：已接受的结果需要在你指明的提交上做一次不带该输入的完整运行。夜间运行总是完整运行。[证明变异体](proof-mutants.md#verdict-reuse)说明键覆盖什么。

### 单进程运行

`python3 scripts/verification.py final` 从一次干净的构建开始，在一个进程里运行下列各部分，并打印提交：

- `specs` 的各项检查；
- `scripts/check-sorry.sh` 和审计自测；
- 每个带键变异体的内核重放；
- 差分测试（普通构建和 sanitizer 构建），以及差分测试框架的自测；
- 三个列表目录中的每个变异体列表，使用严格模式。

它不运行 `tests/verification/` 下的 Python 测试，不检查进度视图，也不运行快速关卡中除 `check-sorry.sh` 以外的步骤（字符串字面量、规格分层、禁用构造、`PartialCheck.lean`、补丁可以应用）。工作流 `verification-final` 针对具名提交手动启动它。夜间套件不运行它。

## `verification.py specs` 判定什么

脚本读取 `tests/audit/` 下的登记表。[公开目标](goals.md)说明这些登记表。

1. **函数清单。**`public-api.json` 中的函数恰好就是固定的 `zlib.h` 导出的函数。默认构建中的每个函数都有手册小节、翻译后的入口和功能目标。只在 Windows 上存在的 `gzopen_w` 只有手册小节和一条理由。每个有文档的函数都有安全目标。清单文件中的目标分组与脚本里写定的列表相同。固定的源码提交等于子模块的提交，且子模块没有本地改动。
2. **全新内核。**`leanchecker --fresh ZlibF` 重新检查编译出的证明项。
3. **声明审计。**审计器（`tests/audit/Audit.lean`）读取编译后的模块。它拒绝公理、opaque 常量、`implemented_by`、`extern`，以及不在编译器辅助声明列表内的 unsafe 或 partial 声明。每个定义和定理只能依赖 `propext`、`Classical.choice` 和 `Quot.sound`。`theorems.txt` 中的每个定理都存在，确实是定理，并且有文档字符串。每个 `Goal.*` 命题都列在 `goals.txt` 中。只有当某个列出的定理的类型恰好是这个目标时，目标才算 PROVED。
4. **登记表一致。**`proved-goals.txt` 等于审计器判定为 PROVED 的目标集合。每个必需目标要么是 PROVED，要么列在清单文件的 `open_safety` 中；`open_safety` 中的目标不是 PROVED。
5. **不会悄悄消失。**沿提交链，任何已登记定理、已证明目标、变异体引用或冻结的变异体行，如果消失了，`registry-removals.json` 中必须有一条说明理由的条目。已经完成的目标不得重新列为未完成。规则见[公开目标](goals.md#shrink-only-rules)。
6. **变异体证据。**每个针对单个公开函数的已证明目标都有函数变异体。每个已证明的必需目标要么在 `public-mutants.json` 中有键，要么有固定证据（见[证明变异体](proof-mutants.md#which-goals-need-which-evidence)）。

## 这些检查确立什么

| 检查 | 证据与局限 |
| --- | --- |
| 内核重放与公理审计 | 检查证明项及其依赖。只允许 `propext`、`Classical.choice` 和 `Quot.sound`。证明正确，回答的问题仍可能不完整。 |
| 精确目标匹配 | 已登记定理的类型就是固定的目标。多出前提、名字相近，或是关于抽象模型的定理，都不算。目标说得够不够，由审查判断。 |
| 无占位符检查 | 拒绝 `sorry` 和 `AGENTS.md` 列出的其他禁用构造。 |
| 差分测试 | 把翻译后的执行与真实的 C 相比较，包括出错和分配失败的情形。它们是关于忠实性的有限证据，不是证明。sanitizer 运行扩充了这份证据。 |
| 审计自测与差分自测 | 故意破坏检查机制的输入，要求检查机制发现这一改动。 |
| 证明变异体 | 改变一个翻译后函数的行为，要求该函数的证明拒绝它。对一处修改敏感，并不证明每种错误都被覆盖。 |

## 已知局限

- **检查器是被信任的。**审计器（`tests/audit/*.lean`）、`scripts/`、`tests/audit/proofmut.sh`、`tests/audit/selftest.sh` 和变异脚本（`tests/proof-mutants/*.py`）靠对其差异的审查来保护，没有另一项检查。
- **复用的判定与脚本一样受信任。**预检相信键相符的已存储记录。存储在工作流缓存中；某个分支或 `main` 上的运行可以写入该分支上的预检所读取的存储。完整运行不读取任何存储。见[证明变异体](proof-mutants.md#verdict-reuse)。
- **说明理由的删除是经过审查的出口。**`tests/audit/registry-removals.json` 中带理由的条目，为一个名字解除一条防删除规则。它在差异中可见。什么也不豁免的条目会被当作过时条目拒绝。
- **提交链从固定的起点开始。**防删除规则读取脚本中固定的两个提交之后的历史。改写某个起点之后历史的强制推送能绕过这些规则。防御手段是禁止强制推送的分支保护。
- **`script:` 变异体行靠阅读来检查。**运行器防止坏变异体的办法，是把第一个错误与该行的文件相比较；对脚本行来说，这个文件就是脚本本身。见[证明变异体](proof-mutants.md#known-limits)。
- **没有锁文件。**定义、规格和定理命题只由 git 跟踪，所以对它们的改动只在差异中可见。命题说得够不够，运行时是否表示了 C，翻译是否与源码一致，都由审查判断。

[验证策略](../anti-cheating.md)说明验收套件防御什么、不防御什么。错误的命题要改正，不能绕过：见 `AGENTS.md`。

## 本目录中的页面

| 页面 | 用途 |
| --- | --- |
| [参与贡献](contributing.md) | 带编号的步骤和命令：每次改动、登记一个结果、运行验收。 |
| [公开目标](goals.md) | 登记表、63 个必需目标的集合，以及防止悄悄删除的规则。 |
| [证明变异体](proof-mutants.md) | 什么是变异体，附一个完整的例子；怎样添加、运行和解读；有哪些局限。 |
| [变异体证据记录](mutant-evidence.md) | 带日期的记录：各组目标的证据由哪些行承担，这些行在哪里被杀死。 |

有三页是带日期的源码审查记录。它们是关于审查当时的命题和运行时的证据，不是流程，也不是现有缺陷的列表。每页开头都有说明，写明它的写作时间；两份运行时记录的开头还有一张表，给出每项发现的状态。

| 记录 | 内容 |
| --- | --- |
| [公开契约审查](contract-review.md) | 对照 C 阅读功能契约时发现的更正和反例。 |
| [运行时审查](runtime-review.md) | 关于运行时模型的发现 R1–R13 和翻译问题 U1–U5。 |
| [堆表审查](runtime-tables-review.md) | 关于数组表示的表和原地更新的发现 F1–F6。 |

另有三份更早的记录，描述的是一个使用锁文件的流程，而本项目没有锁文件。它们保存在 `docs/history/` 下：[登记检查](../history/registration-review.md)、[查询登记审查](../history/query-registration-review.md)和[编译器辅助声明审查](../history/compiler-helper-review.md)。
