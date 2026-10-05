# 有限非局域博弈分离的 Lean 形式化

[English](README.md) | **简体中文**

本项目使用 Lean 4 / mathlib 证明：存在一个具有**二值输赢判定**的有限双人非局域博弈，使得

$$
\omega_q(G)<1=\omega_{qc}(G).
$$

量子值允许任意有限局部维数；对易算子值允许无限维 Hilbert 空间。两个公共存在性定理的结论均包含二值得分条件，且没有额外假设。

存在性证明通过**显式构造**完成：两个定理都以明确定义的 `ThomGame.Construction.paperGame` 为见证。若想查看这个博弈，请按下方的[构造阅读路径](#在哪里查看博弈的显式构造)阅读代码。

> [!IMPORTANT]
> **如果只想验证这个结论，请从下面的最小检查链条开始。**
> 人工核对博弈、测量、策略和 value 的定义及存在性陈述，然后运行两条验证命令。无需人工阅读具体构造和中间证明。

## 从这里开始：最小检查链条

**博弈 → POVM → 策略与 Born 概率 → 相关性集合 → value → 存在性定理 → Lean 检查。**

准备好固定版本的工具链和依赖后，在仓库根目录运行：

```sh
lake --fail-fast build ThomGame.Construction.NonlocalGameSeparation
lake env lean scripts/CheckSeparation.lean
```

新环境请先看[环境准备](#环境准备与完整项目检查)。[中文详细指南](validation/minimal-separation-check.zh.md)和 [English guide](validation/minimal-separation-check.md)说明了同一条最小路径。

### 1. 核对定义

这条路径直接使用一般 POVM 版本，其定义明确写出了测量模型和 Born 公式。

| 步骤 | 阅读位置 | 需要确认的数学含义 |
| --- | --- | --- |
| 博弈与得分 | [FiniteGame](ThomGame/Quantum/FiniteGame.lean#L13)，第 13–31 行 | 四个有限集合；非负且总和为 1 的问题分布；`[0,1]` 值的得分；对问题和回答求加权期望。 |
| 相关性数组 | [CorrelationTable](ThomGame/Quantum/Correlation.lean#L15) | 以双方问题和双方回答为索引的实数数组。 |
| 测量 | [POVM](ThomGame/Quantum/POVM.lean#L19)，第 19–26 行 | 有界正算子族，算子之和为恒等算子。 |
| 有限维策略 | [局部空间](ThomGame/Quantum/FiniteStrategy.lean#L13)，第 13–14 行；[FinitePOVMStrategy](ThomGame/Quantum/FinitePOVMStrategy.lean#L17)，第 17–39 行 | 任意正有限局部维数、张量积空间中的单位向量、本地 POVM 和张量积 Born 公式。 |
| 对易策略 | [CommutingPOVMStrategy](ThomGame/Quantum/CommutingPOVMStrategy.lean#L18)，第 18–35 行 | 完备复 Hilbert 空间、单位向量、POVM、跨玩家对易条件和相应 Born 公式。 |
| 允许的相关性 | [POVM 相关性集合](ThomGame/Quantum/POVMGameValue.lean#L17)，第 17–28 行 | 分别收集相应策略类别产生的全部相关性。 |
| value | [value](ThomGame/Quantum/GameValue.lean#L15)；[omegaQPOVM 与 omegaQcPOVM](ThomGame/Quantum/POVMGameValue.lean#L75)，第 75–79 行 | 在各自允许的相关性集合上，对期望得分取上确界。 |

得分和 value 对应以下公式：

$$
\operatorname{score}_G(p)=\sum_{x,y,a,b}\pi(x,y)V(x,y,a,b)p(a,b\mid x,y),
\qquad \omega_t(G)=\sup_{p\in C_t}\operatorname{score}_G(p).
$$

共享态与问题无关；每位玩家的测量只依赖自己的问题。局部维数没有统一上界。对易模型没有有限维限制，只要求跨玩家对易。详细指南说明了纯态约定，以及任意有限维 Hilbert 空间到坐标模型的已验证转换。

### 2. 核对最终陈述

`ThomGame.Quantum` 命名空间中的公共定理 [exists_finiteGame_povm_quantum_commuting_separation](ThomGame/Construction/NonlocalGameSeparation.lean#L28) 陈述如下：

```lean
∃ (X Y A B : Type) (_ : Fintype X) (_ : Fintype Y)
  (_ : Fintype A) (_ : Fintype B) (G : FiniteGame X Y A B),
  (∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1) ∧
  G.omegaQcPOVM = 1 ∧ G.omegaQPOVM < 1
```

二值得分是**已经证明的结论**的一部分。同一文件还给出 [exists_finiteGame_quantum_commuting_separation](ThomGame/Construction/NonlocalGameSeparation.lean#L13)，使用投影测量版本的 `omegaQ` 和 `omegaQc`。

[CheckSeparation.lean](scripts/CheckSeparation.lean) 明确核对公共 POVM 定理的陈述。其中的 `SeparationCheck.binary_separation` 还证明四个集合都可以取为非空。

### 3. 核对检查结果

检查脚本打印实际核心定义和最终陈述，省略展开的证明项，并递归检查其公理依赖；同时核对有限维坐标模型覆盖定理。允许的公理只有 `propext`、`Classical.choice`、`Quot.sound`。任何其他公理，包括 `sorryAx`，都会使检查失败。

成功时最后一行是：

```text
Separation check passed: explicit statements, nonempty binary game, and standard axioms only.
```

**已记录的结果：2026-10-04，在两个公共主定理加入二值得分条件后验证通过。** 参见[最小检查](validation/binary-separation-check-20261004.log)、[定理模块构建](validation/binary-separation-target-build-20261004.log)和[主定理检查](validation/binary-separation-main-check-20261004.log)。

人工确认定义表达了预期数学对象；Lean 检查形式命题。上述命令会复用已有 `.olean` 文件。若要从源码重建该结论依赖的本项目证明，可在没有本项目 `.lake/build` 的新源码副本中运行同样命令。[详细指南](validation/minimal-separation-check.zh.md)说明了验证范围。

## 在哪里查看博弈的显式构造

这个见证是一个线性系统博弈：Alice 收到一行并返回三个比特；Bob 收到该行中出现的一列并返回一个比特。当 Alice 的三个比特满足该行方程，且她对 Bob 所问列的回答与 Bob 的回答一致时，双方获胜。

1. [PaperGame.lean：`paperGame`](ThomGame/Construction/PaperGame.lean#L15) 将实际博弈定义为 `paperSystem.incidenceGame`，并给出具体的问题集和回答集类型。同文件的 `paperGame_weight` 和 `paperGame_payoff` 分别陈述问题分布和获胜条件。
2. [IncidenceGame.lean](ThomGame/Quantum/IncidenceGame.lean#L29) 定义 `incidenceWeight`、`incidencePayoff` 和 `incidenceGame`：在行与其出现列组成的关联对上均匀采样，定义二值输赢判定，再将它们组装成 `FiniteGame`。
3. [PaperOrderedSystem.lean：`paperSystem`](ThomGame/Construction/PaperOrderedSystem.lean#L12) 给出每行列索引按递增顺序排列的具体稀疏系统，并证明其矩阵和右端项分别是 `A` 和 `b`。
4. [MatrixData.lean](ThomGame/Construction/MatrixData.lean#L18) 定义 `A` 和 `b`；`sourceTriples` 与 `A_eq_one_iff` 指明矩阵元素，`b_formula` 指明右端项。若想继续查看底层构造，可追到 [Numbering.lean：`numberedSystem`](ThomGame/Construction/Numbering.lean#L108) 和 [Wheel.lean：`wheelFamily` 与 `system`](ThomGame/Construction/Wheel.lean#L70)。

## 环境准备与完整项目检查

安装 elan 和 Git 后，在仓库根目录运行：

```sh
lake exe cache get
```

项目固定使用 Lean `v4.35.0-rc3`，mathlib 固定为提交 `16efc2c756299924184fe015f6384ad6538d42c7`。参见 [lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml) 和 [lake-manifest.json](lake-manifest.json)。Mathlib 是唯一直接 Lean 包依赖。证书嵌入 Lean 源码；构建不需要论文 PDF、外部数据生成器或 Python。

如需执行最小分离检查之外的完整检查：

```sh
lake --fail-fast build
lake env lean scripts/CheckSeparation.lean
lake env lean scripts/CheckMain.lean
lake env lean scripts/CheckPOVM.lean
lake env lean scripts/CheckCorollaries.lean
lake env lean scripts/AuditAxioms.lean
```

[验证记录索引](validation/README.md)区分了最新二值分离定理的检查结果，以及更早的全项目审计和源码哈希快照。

## 其他结论

- [PaperPOVMGap.lean](ThomGame/Construction/PaperPOVMGap.lean)：`ThomGame.Construction.paper_main_results_povm` 将具体构造的中央元素结论与一般 POVM 下的 `ωq = ωqa < 1 = ωqc` 合并陈述。
- [PaperValueCorollaries.lean](ThomGame/Construction/PaperValueCorollaries.lean)：`paper_classical_value_corollary` 给出允许共享随机性的精确经典值；`paper_quantum_gap_corollary` 给出一般 POVM 量子缺口的显式界：

$$
\omega_c=1-\frac{1}{4251456},\qquad
0<2^{-2^{50003}}\le 1-\omega_q=\omega_{qc}-\omega_q\le\frac{1}{4251456}.
$$

[数值推论证明说明](validation/corollaries-proof-sources.md)记录这些推论的来源。它们属于上述最小阅读和验证路径之外的额外结论。

## 目录索引

| 位置 | 内容 |
| --- | --- |
| [ThomGame/Quantum](ThomGame/Quantum) | 博弈、测量、策略、相关性及 value 的定义。 |
| [NonlocalGameSeparation.lean](ThomGame/Construction/NonlocalGameSeparation.lean) | 两个带二值得分条件的公共存在性定理。 |
| [ThomGame.lean](ThomGame.lean) | 全项目导入入口。 |
| [scripts](scripts) | 专项检查与全项目公理审计。 |
| [validation](validation) | 详细检查指南、日志与注明版本阶段的历史记录。 |
