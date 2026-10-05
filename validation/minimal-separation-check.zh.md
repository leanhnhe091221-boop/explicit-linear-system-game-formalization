# 只检查非局域博弈分离结论

[English](minimal-separation-check.md) · **中文** · [返回项目说明](../README.zh.md)

目标是确认：存在有限、非空的问题集和回答集，以及取值为 0/1 的输赢判定，
使相应双人单轮 nonlocal game 满足 `omegaQcPOVM = 1` 且 `omegaQPOVM < 1`。
这里 q 允许任意有限局部维数和一般 POVM，qc 允许无限维的对易算子策略。

人工只需核对下面的定义和最终命题；构造和证明依赖交给 Lean 检查。
这是阅读范围的缩小，不是将整条证明的计算依赖删除。

## 最短运行路径

在 `formalization-clean` 根目录运行：

```powershell
lake --fail-fast build ThomGame.Construction.NonlocalGameSeparation
lake env lean scripts/CheckSeparation.lean
```

新环境先按[项目说明](../README.zh.md)安装指定的 Lean 工具链并取得依赖；
`lake exe cache get` 可取得 mathlib 缓存。该目标不要求构建全项目的额外数值推论。

[检查脚本](../scripts/CheckSeparation.lean)会打印下列核心定义和最后两个命题，
省略证明项；随后递归检查公理依赖。
成功时最后一行是：

```text
Separation check passed: explicit statements, nonempty binary game, and standard axioms only.
```

已有运行输出见[二值得分主定理检查日志（2026-10-04）](binary-separation-check-20261004.log)。

## 人工核对的定义

只需读表中定义所在的小段，不必读这些文件中后续的证明。

| 对象 | 源码位置 | 对应的数学内容 |
| --- | --- | --- |
| 博弈及期望得分 | [FiniteGame.lean](../ThomGame/Quantum/FiniteGame.lean)：`FiniteGame`、`answerScore`、`success` | 四个有限集合；联合问题分布非负且和为 1；得分在 `[0,1]` 中；`success` 是分布、得分、回答概率乘积之和 |
| 相关性数组 | [Correlation.lean](../ThomGame/Quantum/Correlation.lean)：`CorrelationTable` | `X → Y → A → B → ℝ`，表示给定问题 `x,y` 时回答 `a,b` 的概率 |
| POVM | [POVM.lean](../ThomGame/Quantum/POVM.lean)：`POVM` | 有界正算子族，算子和为恒等算子 |
| 有限维空间 | [FiniteStrategy.lean](../ThomGame/Quantum/FiniteStrategy.lean)：`LocalSpace`、`BipartiteSpace` | `LocalSpace d = ℂ^d`，`BipartiteSpace d e = ℂ^d ⊗ ℂ^e` |
| 有限维量子策略及 Born 公式 | [FinitePOVMStrategy.lean](../ThomGame/Quantum/FinitePOVMStrategy.lean)：`FinitePOVMStrategy`、`correlation` | 任意正自然数局部维数；单位向量；每个本地问题一个 POVM；`Re ⟨ψ, (E ⊗ F) ψ⟩` |
| 对易策略及 Born 公式 | [CommutingPOVMStrategy.lean](../ThomGame/Quantum/CommutingPOVMStrategy.lean)：`CommutingPOVMStrategy`、`correlation` | 完备复 Hilbert 空间；单位向量；POVM；跨玩家的所有效果算子对易；`Re ⟨ψ, E F ψ⟩` |
| 所有允许的相关性 | [POVMGameValue.lean](../ThomGame/Quantum/POVMGameValue.lean)：`povmQuantumCorrelations`、`povmCommutingCorrelations` | q 是所有有限维策略相关性的像；qc 对 Hilbert 空间及其上所有对易策略作存在量化 |
| 取值 | [GameValue.lean](../ThomGame/Quantum/GameValue.lean)：`value`；[POVMGameValue.lean](../ThomGame/Quantum/POVMGameValue.lean)：`omegaQPOVM`、`omegaQcPOVM` | `value K = sSup (success '' K)`；q 和 qc 分别使用上述两个集合 |

这些定义展开后的公式是

$$
\operatorname{score}_G(p)=\sum_{x,y,a,b}\pi(x,y)V(x,y,a,b)p(a,b\mid x,y),
\qquad
\omega_t(G)=\sup_{p\in C_t}\operatorname{score}_G(p).
$$

q 的关联满足
$p(a,b\mid x,y)=\operatorname{Re}\langle\psi,(E_a^x\otimes F_b^y)\psi\rangle$，
qc 的关联满足
$p(a,b\mid x,y)=\operatorname{Re}\langle\psi,E_a^xF_b^y\psi\rangle$。
`alice` 只依赖 `x`，`bob` 只依赖 `y`，共享态与问题无关。
qc 不要求同一玩家的不同问题对应的测量对易，也没有有限维条件。

可用文献中的纯态、POVM 表述作外部对照，例如
[Karamlou, MFCS 2025，第 2.2–2.3 节](https://drops.dagstuhl.de/storage/00lipics/lipics-vol345-mfcs2025/html/LIPIcs.MFCS.2025.61/LIPIcs.MFCS.2025.61.html)。
该文另为其完美策略讨论假定问题分布有满支撑；本项目允许任意联合分布，包括零权重问题对。

## 与常见定义约定的对应

- **正性：** `0 ≤ effect a` 使用 mathlib 有界算子的通常正算子序。
  `POVM.isPositive`、`POVM.selfAdjoint` 和 `POVM.quadratic_nonneg` 明确给出
  自伴性及非负二次型。必要时可继续查看 mathlib 的
  `Analysis/InnerProductSpace/Positive.lean` 中 `ContinuousLinearMap.IsPositive`。
- **任意有限维空间：** 维数由策略自身携带，没有统一上界。
  [`FinitePOVMStrategy.exists_coordinates`](../ThomGame/Quantum/FinitePOVMCoordinates.lean)
  已证明任意有限维复 Hilbert 空间上的
  POVM/单位向量策略都能转为此坐标模型，保持所有 Born 概率。
  检查脚本也审计这个定理，不需要阅读其证明。
- **纯态约定：** 这里采用单位向量形式。若从密度矩阵形式出发，可用通常的纯化解释
  它与有限维策略表述的对应；当前最小路径没有另外形式化或检查混态纯化定理。
- **Hilbert 空间的 universe：** qc 定义中量化 `H : Type`，没有有限维限制。
  这里不是声称已经形式证明跨所有 Lean universe 的搬运定理。
- **非空和二值输赢：** 公共 `FiniteGame` 允许 `[0,1]` 得分；
  [NonlocalGameSeparation.lean](../ThomGame/Construction/NonlocalGameSeparation.lean)
  中两个存在性主定理的结论均明确包含
  `∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1`。
  检查脚本中的 `SeparationCheck.binary_separation` 还明确给出四个集合非空。
  因而主定理本身就覆盖常见的 Boolean 输赢判定版本。

## 最终命题与证明验证

在 `ThomGame.Quantum` 命名空间内，公共 POVM 主定理的陈述是：

```lean
theorem exists_finiteGame_povm_quantum_commuting_separation :
    ∃ (X Y A B : Type) (_ : Fintype X) (_ : Fintype Y)
      (_ : Fintype A) (_ : Fintype B) (G : FiniteGame X Y A B),
      (∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1) ∧
      G.omegaQcPOVM = 1 ∧ G.omegaQPOVM < 1
```

同文件中的 `exists_finiteGame_quantum_commuting_separation` 也包含同样的二值条件，
但使用投影测量版本 `omegaQc`、`omegaQ`。两个公共定理都没有额外假设；
四个集合非空是下面检查脚本中加强命题明确添加并证明的结论。

`SeparationCheck.separation` 明确重述含二值得分条件的存在命题，并把项目已证明的
`ThomGame.Quantum.exists_finiteGame_povm_quantum_commuting_separation`
用作这个命题的证明。这样检查的是预期的类型，而不仅是查询一个名称。

`SeparationCheck.binary_separation` 用同一具体见证补上四个集合非空的条件。
它依然没有附加假设。读者只需看其陈述，不需阅读证明。

递归公理检查只允许 `propext`、`Classical.choice`、`Quot.sound`。
任何其他依赖公理，包括 `sorryAx`，都会使检查脚本报错退出。
这是对最终定理及其实际证明依赖的检查，因此不必为这个单一目标审计全部无关定理。

人工确认“定义就是所要讨论的数学对象”；Lean 确认“这个类型的命题有有效证明”。
公理检查本身不会替人判断定义的数学含义。
这一区分与 [Lean 官方的证明验证说明](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
一致。

通常使用上述两条命令，并信任指定版本的 Lean/mathlib 及它们的构建产物。
构建命令可以复用已有编译产物；Lean 运行检查脚本时会加载已有 `.olean`，
不会在每次导入时重新从源码检查依赖。
如果要从源码重建该结论依赖的本项目证明，可在没有本项目 `.lake/build` 的新源码副本中运行
同一构建命令，然后运行脚本。若还要对依赖库的缓存进行独立内核复核，
官方说明介绍了 `lean4checker` 等更强的路线；这不是上述最小检查的组成部分。

原始 `omegaQ`/`omegaQc` 使用投影测量，保留在公共存在定理中。
本路径直接审阅一般 POVM 的定义与结论，因此无需先审阅测量扩张证明。
