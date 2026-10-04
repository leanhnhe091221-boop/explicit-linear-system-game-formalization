module

public import ThomGame.Analysis.FiniteNoDriftConcentration

/-! A finite anchored no-drift theorem, using only the existing correction proofs. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable def finiteNoDriftError (ε K ν : ℝ) : ℝ :=
  14 * ε + 8 * Real.sqrt (60 * ε + 4 * (K * (2 * (26 * ε + Real.sqrt (26 * ε))) + ν))

variable {d : Nat} [NeZero d] (A D : StarSubalgebra ℂ (CMatrix d))
    (F : MatrixSubalgebraStarBlocks D)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hDA : D ≤ A)

theorem finiteNoDrift_corrected_concentration
    (U : UnitaryMatrix d) (hU : ∀ X ∈ D, U.val * X = X * U.val)
    {ε a : ℝ} (S : MatrixThomSpectralData A (matrixUnitaryPullbackAlgebra A U) D ε)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 2)
    (hBA : MatrixNearInclusion (matrixUnitaryPullbackAlgebra A U) A ε)
    (hX : hsNorm (matrixAnchoredBoundedScale D A F R hDA - (1 / 2 : ℂ) • 1) ≤ a) :
    let P := matrixUnitaryPullbackBlocks A U (matrixSubalgebraComplementaryBlocks A R)
    let hDB := matrixUnitaryPullback_contains_common A U D hDA hU
    let s := matrixAnchoredScaleCoefficients D A F R hDA
    S.retainedScaleConcentration P R hDB F s ≤ 60 * ε + 4 * a := by
  dsimp only
  have ht := finiteNoDrift_anchored_transport A D F R hDA U hU S hε hBA
  have hXm : hsNorm (U.valᴴ * matrixAnchoredBoundedScale D A F R hDA * U.val -
      (1 / 2 : ℂ) • 1) ≤ a := by
    rwa [hsNorm_unitaryPullback_sub_scalar]
  have hm := S.finite_scalar_concentration_transfer hε hsmall _ _ hXm ht.1
  have hp := S.finite_scalar_concentration_transfer hε hsmall _ _ hX ht.2
  change hsNorm _ + hsNorm _ ≤ _
  linarith

include F R hDA in
/-- Finite reverse near inclusion from a concrete Poincare anchor.
The conservative bound loses a square root compared to the manuscript, but is explicit. -/
theorem finiteNoDrift_reverse_inclusion
    {h : Nat} (U : Fin h → UnitaryMatrix d)
    (hU : ∀ j X, X ∈ D → (U j).val * X = X * (U j).val)
    {ε K ν : ℝ} (hε : 0 ≤ ε) (hsmall : ε < 1 / 2)
    (hBA : ∀ j, MatrixNearInclusion (matrixUnitaryPullbackAlgebra A (U j)) A ε)
    (hanchor : FiniteNoDriftAnchor A D U K ν) (j : Fin h) :
    MatrixNearInclusion A (matrixUnitaryPullbackAlgebra A (U j)) (finiteNoDriftError ε K ν) := by
  let S := fun j => Classical.choice (exists_matrixThomSpectralData A
    (matrixUnitaryPullbackAlgebra A (U j)) D hDA
    (matrixUnitaryPullback_contains_common A (U j) D hDA (hU j)) hε (hBA j))
  let P := matrixUnitaryPullbackBlocks A (U j) (matrixSubalgebraComplementaryBlocks A R)
  let hDB := matrixUnitaryPullback_contains_common A (U j) D hDA (hU j)
  let s := matrixAnchoredScaleCoefficients D A F R hDA
  let a := K * (2 * (26 * ε + Real.sqrt (26 * ε))) + ν
  let c := 60 * ε + 4 * a
  have hX := finiteNoDrift_anchored_concentration A D F R hDA U hU S hε hsmall.le hBA hanchor
  have hc : (S j).retainedScaleConcentration P R hDB F s ≤ c :=
    finiteNoDrift_corrected_concentration A D F R hDA (U j) (hU j) (S j) hε hsmall (hBA j) hX
  letI : NeZero (S j).cut.rank := ⟨Nat.ne_of_gt ((S j).cut_rank_pos hε hsmall)⟩
  have hr := matrixThom_reverseInclusion_center_near (S j) P R hDB F s
    (matrixAnchoredScaleCoefficients_pos D A F R hDA)
  have hrev : MatrixNearInclusion (S j).correctedTargetAlgebra (S j).correctedSourceAlgebra
      (4 * Real.sqrt c) := by
    intro X hXA hnorm
    obtain ⟨Y, hY, hXY⟩ := hr X hXA hnorm
    exact ⟨Y, hY, hXY.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (by norm_num))⟩
  have hf := (S j).finite_reverse_transfer hε hsmall.le (hBA j) (by positivity) hrev
  convert hf using 1 <;> dsimp [finiteNoDriftError, c, a] <;> ring

include hDA in
/-- The block decompositions required by the construction are chosen internally. -/
theorem finiteNoDrift_reverse
    {h : Nat} (U : Fin h → UnitaryMatrix d)
    (hU : ∀ j X, X ∈ D → (U j).val * X = X * (U j).val)
    {ε K ν : ℝ} (hε : 0 ≤ ε) (hsmall : ε < 1 / 2)
    (hBA : ∀ j, MatrixNearInclusion (matrixUnitaryPullbackAlgebra A (U j)) A ε)
    (hanchor : FiniteNoDriftAnchor A D U K ν) (j : Fin h) :
    MatrixNearInclusion A (matrixUnitaryPullbackAlgebra A (U j)) (finiteNoDriftError ε K ν) := by
  let F := Classical.choice (exists_matrixSubalgebraStarBlocks D)
  let R := Classical.choice (exists_matrixSubalgebraStarBlocks
    (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
  exact finiteNoDrift_reverse_inclusion A D F R hDA U hU hε hsmall hBA hanchor j

theorem finiteNoDriftError_small {ε ν : ℝ}
    (hε : 0 ≤ ε) (heps : ε ≤ 1 / (10 : ℝ) ^ 33)
    (hν : ν ≤ 1 / (10 : ℝ) ^ 27) :
    finiteNoDriftError ε (10 ^ 6) ν ≤ 1 / 1000 := by
  have hs : Real.sqrt (26 * ε) ≤ 1 / (10 : ℝ) ^ 15 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · norm_num at heps ⊢
      linarith
  have ht : Real.sqrt (60 * ε + 4 * ((10 : ℝ) ^ 6 *
      (2 * (26 * ε + Real.sqrt (26 * ε))) + ν)) ≤ 1 / 10000 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · norm_num at heps hs hν ⊢
      linarith
  unfold finiteNoDriftError
  norm_num at heps ht ⊢
  linarith

end ThomGame.Analysis
