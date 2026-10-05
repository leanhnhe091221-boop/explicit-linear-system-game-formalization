# 验证记录与历史存档

[English overview](../README.md) | [中文首页](../README.zh.md)

## 当前结论的最小检查入口

**定义 → 策略与 Born 概率 → 相关性集合 → value → 二值博弈存在性定理 → Lean 检查。**

只核对一般非局域博弈的分离结论，请使用[中文最小检查指南](minimal-separation-check.zh.md)或 [English guide](minimal-separation-check.md)，并在仓库根目录运行：

```sh
lake --fail-fast build ThomGame.Construction.NonlocalGameSeparation
lake env lean scripts/CheckSeparation.lean
```

两个公共存在性定理都证明：存在有限博弈，其 payoff 只取 `0` 或 `1`，且相应的 `omegaQc = 1`、`omegaQ < 1`；其中一个版本使用一般 POVM。检查脚本还明确验证四个集合可取为非空。二值得分和非空性质均为结论，不是新增假设。

## 最新验证：二值得分已加入公共主定理（2026-10-04）

以下日志对应 `NonlocalGameSeparation.lean` 中两个公共定理都已包含
`∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1` 的版本。

| 检查 | 结果 | 日志 |
| --- | --- | --- |
| `lake --fail-fast build ThomGame.Construction.NonlocalGameSeparation` | 通过 | [定理模块构建](binary-separation-target-build-20261004.log) |
| `lake --fail-fast build` | 通过 | [完整构建](binary-separation-full-build-20261004.log) |
| `lake env lean scripts/CheckSeparation.lean` | 显式陈述、非空二值版本及递归公理检查通过 | [最小检查](binary-separation-check-20261004.log) |
| `lake env lean scripts/CheckMain.lean` | 两个公共定理的强化陈述及递归公理检查通过 | [主定理检查](binary-separation-main-check-20261004.log) |

两个修改后的公共主定理的公理依赖均仅含 `propext`、`Classical.choice`、`Quot.sound`。本阶段运行的是以上构建及专项递归审计；下面的 19,333 个定理全项目审计属于更早的存在性定理版本。

本次 README 整理只更新文档，没有重新运行 Lean 构建，也没有把历史日志标记为新验证。

## 历史阶段：一般存在性定理与首个最小入口（2026-10-04）

这一阶段引入了 `NonlocalGameSeparation`，公共定理尚未显式包含二值得分条件。随后加入的检查脚本已单独核对非空、二值的见证。它们保留为版本演进记录；当前结论应参考上方最新验证。

| 检查 | 当时结果 | 日志 |
| --- | --- | --- |
| 存在性定理模块构建 | 通过 | [模块构建](existence-target-build-20261004.log) |
| 完整构建 | 通过 | [完整构建](existence-full-build-20261004.log) |
| `CheckMain.lean` | 存在性定理类型与递归公理检查通过 | [主结论检查](existence-main-check-20261004.log) |
| `AuditAxioms.lean` | 19,333 个项目定理通过 | [全项目审计](existence-all-axioms-20261004.log) |
| 首个 `CheckSeparation.lean` | 非空二值版本及递归公理检查通过 | [最小入口初次验证](minimal-separation-check-20261004.log) |

## 历史阶段：经典值与显式量子缺口

这一阶段的入口是 `ThomGame.Construction.PaperValueCorollaries`。两个无额外假设的推论分别给出精确经典值和一般 POVM 下的显式量子缺口；证明来源见[数值推论说明](corollaries-proof-sources.md)。

| 检查 | 当时结果 | 日志 |
| --- | --- | --- |
| `PaperValueCorollaries` 模块构建 | 通过 | [集成构建](corollaries-integration-build.log) |
| 完整构建 | 通过 | [完整构建](corollaries-full-build.log) |
| `CheckCorollaries.lean` | 两个推论及递归公理检查通过 | [推论检查](corollaries-check.log) |
| `CheckPOVM.lean` | 通过 | [POVM 连接检查](corollaries-povm-check.log) |
| `CheckMain.lean` | 通过 | [原主结论检查](corollaries-main-check.log) |
| `AuditAxioms.lean` | 19,331 个项目定理通过 | [全项目审计](corollaries-all-axioms.log) |

[该阶段的机器可读记录](corollaries-validation.json) 保存当时的源码哈希、固定依赖和检查结果。历史核对确认当时原有 1,439 个核心及 POVM 模块未修改，并增加了 122 个证明及证书模块。这些数字描述该阶段，不是当前版本的文件清单或新审计结果。

## 历史阶段：原 POVM 版本（2026-10-03）

这一阶段以 `ThomGame.Construction.PaperPOVMGap` 为入口，验证了论文具体构造在一般 POVM 下的量子结论。

| 检查 | 当时结果 | 日志 |
| --- | --- | --- |
| `PaperPOVMGap` 模块构建 | 通过 | [集成构建](povm-resumed-build-20261003-153950.log) |
| 完整构建 | 通过 | [完整构建](povm-full-build.log) |
| `CheckPOVM.lean` | 通过 | [POVM 连接检查](povm-check.log) |
| `CheckMain.lean` | 通过 | [具体主定理检查](povm-main-check-20261003-153950.log) |
| `AuditAxioms.lean` | 17,942 个项目定理通过 | [全项目审计](povm-all-axioms.log) |

[该阶段的机器可读记录](povm-validation.json) 包含 1,447 个文件的历史 SHA-256，覆盖当时的 Lean 源码、检查脚本、依赖配置和原中文说明。其核对结果仅适用于当时的快照，不代表当前 README 或后来修改的文件仍与该哈希表相同。

## 如何理解这些记录

- 递归公理审计只允许 `propext`、`Classical.choice`、`Quot.sound`。具体范围由相应日志对应的脚本和导入确定。
- 记录中的 Windows 绝对路径是原验证环境的位置，不是构建依赖。
- 旧日志和 JSON 快照保留原样；当前状态与历史阶段分开说明。
- 部分构建日志包含风格提示，构建成功状态以日志中的退出结果为依据。
- 源码语义审阅、已有编译产物的检查与独立源码重建之间的区别，见[最小检查指南](minimal-separation-check.zh.md)。
