# 两个数值推论的证明来源和核验方式

本扩展对应 `explicit_game_gap_bound.pdf` 中的经典值及显式量子缺口。
补充材料为作者提供的 `explicit_game_gap_bound_complete.zip`；其 SHA-256 为
`ac8b2864bc5747be2006409b078d772fce5ba341ba1b0af4e49acb8d32b73732`。
原有 1,439 个核心及 POVM 模块保持原字节内容；定量引理及证书均放在新增模块中。

经典值使用原有的不可满足性定理给出上界，再构造一个只在唯一奇数右端行的一个
入射位置失败的确定性策略达到该上界。`ClassicalGameValue.lean` 将经典相关集定义为
确定性相关数组的凸包，因此该上界同时覆盖共享随机性的经典策略。

显式下界采用补充材料的有限定量路线。旧版本通过紧致性得到的正缺口没有被当作
具体常数的证明。新增路线分别处理有限根群的词收集、shear 的平方和证书、有限热迭代、
有限代数重建、no-drift 估计，以及从游戏策略到双群近似表示的定量转移。
弱谱隙始终以算子范数不超过一的测试矩阵上的二次型不等式使用。

## Netzer–Thom 证书

原始整数数据来自论文的公开附件：

- [RootOfP.txt](https://arxiv.org/src/1411.2488v1/anc/RootOfP.txt)，SHA-256
  `af8337124848f3053fef6b4805d2ff1ea3cc3e49a7352eeb82613944ee8bd372`。
- [Sl3ZComment.nb](https://arxiv.org/src/1411.2488v1/anc/Sl3ZComment.nb)，SHA-256
  `514f6f8db7ad2b866bcde6c51a6d6957e3b64a47c65771f349d721e096f57c58`。

这些文件只用于生成候选数据。构建仓库不下载附件，不运行 Python 或 Mathematica，
也不读取原 PDF 或 ZIP。用于证明的整数、有限词和路径已经包含在 Lean 源码中。

`NetzerThomGram.lean` 在 Lean 内核中逐行核验整个 121 × 121 Gram 矩阵。
`NetzerThomResidual.lean` 核验系数分组确实各包含一次全部 Gram 项及全部目标多项式项。
`NetzerThomResidualArithmetic.lean` 核验残差增广为零、绝对值总和不超过 9/400。
所有分数计算均为精确算术。

`ShearSignedRelatorArea.lean`、`ShearWeylCertificates.lean` 和
`ShearRankOneCertificates.lean` 从实际 shear 定义关系证明改写规则。
`NetzerThomWordChecker.lean` 给出路径检查器的可靠性证明；
`NetzerThomWords0.lean` 至 `NetzerThomWords21.lean` 逐批核验全部所需的有限路径。
每条路径至多四步，每一步的定义关系面积至多 60，总面积至多 240。
仅有整数矩阵乘积相等不足以通过该检查器。

`NetzerThomLifting.lean` 将这些已经核验的有限等式转移到实际复酉矩阵的归一化
Hilbert–Schmidt 范数，并证明平方和非负、残差下界和总提升误差上界。
这一步也由 Lean 证明，没有将外部数值计算或搜索结果作为公理。

## 依赖及语义

唯一直接 Lean 包依赖仍为固定版本的 mathlib。证书检查使用内核归约，
没有引入 `sorry`、额外公理或 `native_decide`。

最终游戏值使用此前已经建立的一般 POVM 定义。有限维量子值通过允许扩大局部维数的
测量扩张与原投影测量值相等；commuting 值使用已有完美投影策略作为 POVM 策略。
经典策略到量子策略的包含关系提供量子缺口的上界。

`validation/povm-validation.json` 保留为旧版本的历史验证记录。
新的构建、公理审计及哈希记录另行保存，避免将历史验证记录误解为新推论的核验结果。
