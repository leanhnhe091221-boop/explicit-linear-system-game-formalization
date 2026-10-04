module

public import ThomGame.Analysis.MatrixInclusionSupportExpectation
public import ThomGame.Analysis.MatrixBoundedScaleCells

/-!
# Conditional expectation of arbitrary joint cell coefficients
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

theorem matrixInclusionCellScalar_expectation (c : Fin Q.count → Fin P.count → ℝ) :
    matrixTraceProjection B (matrixInclusionCellScalar B C P Q c) =
      matrixStarBlockScalar B P (fun i => ∑ j, matrixInclusionConditionalWeight B C P Q hBC j i * c j i) := by
  simp only [matrixInclusionCellScalar_sum, map_sum, map_smul,
    matrixInclusion_cell_expectation B C P Q hBC, smul_smul]
  simp only [matrixStarBlockScalar, matrixPartitionScalarSum, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem matrixBoundedScale_inclusion_expectation (a : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ j, 0 < a j) (hs : ∀ i, 0 < s i) :
    matrixTraceProjection B (matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixStarBlockScalar B P s)) =
      matrixStarBlockScalar B P (fun i => ∑ j, matrixInclusionConditionalWeight B C P Q hBC j i *
        boundedScaleScalar (a j) (s i)) := by
  rw [matrixBoundedScale_inclusionFormula B C P Q hBC a s ha hs,
    matrixInclusionCellScalar_expectation B C P Q hBC]

end ThomGame.Analysis
