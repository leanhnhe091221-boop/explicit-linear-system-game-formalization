module

public import ThomGame.Analysis.MatrixInclusionScaleCoefficients
public import ThomGame.Analysis.MatrixSubalgebraScale

/-!
# The actual scale ratio dominates the identity

The ratio is the product Delta_C Delta_B^{-1}. Expanding on actual
joint support cells proves its order bound and identifies its inverse.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

theorem matrixInclusionBlockScalars_product (a : Fin Q.count → ℝ) (b : Fin P.count → ℝ) :
    matrixStarBlockScalar C Q a * matrixStarBlockScalar B P b =
      ∑ j, ∑ i, ((a j * b i : ℝ) : ℂ) • matrixInclusionCell B C P Q j i := by
  simp only [matrixStarBlockScalar, matrixPartitionScalarSum, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.ofReal_mul, matrixInclusionCell]
  rw [Finset.sum_comm]
  simp only [mul_comm]

noncomputable def matrixInclusionScaleRatio : CMatrix d :=
  matrixSubalgebraScale C Q * (matrixSubalgebraScale B P)⁻¹

theorem matrixInclusionScaleRatio_expansion : matrixInclusionScaleRatio B C P Q =
    ∑ j, ∑ i, (matrixInclusionScaleCoefficient B C P Q j i : ℂ) • matrixInclusionCell B C P Q j i := by
  rw [matrixInclusionScaleRatio, matrixSubalgebraScale_inverse]
  exact matrixInclusionBlockScalars_product B C P Q _ _

include hBC in
theorem matrixInclusionScaleRatio_one_le : 1 ≤ matrixInclusionScaleRatio B C P Q := by
  have he : matrixInclusionScaleRatio B C P Q - 1 =
      ∑ j, ∑ i, ((matrixInclusionScaleCoefficient B C P Q j i - 1 : ℝ) : ℂ) •
        matrixInclusionCell B C P Q j i := by
    rw [matrixInclusionScaleRatio_expansion, ← matrixInclusionCell_sum B C P Q]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, Finset.sum_sub_distrib]
  apply sub_nonneg.mp
  rw [he]
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  by_cases hz : matrixInclusionCell B C P Q j i = 0
  · simp only [hz, smul_zero, le_refl]
  · have hc : (0 : ℝ) ≤ matrixInclusionScaleCoefficient B C P Q j i - 1 :=
      sub_nonneg.mpr (matrixInclusionScaleCoefficient_one_le B C P Q hBC j i hz)
    exact smul_nonneg (by exact_mod_cast hc) (matrixInclusionCell_projection B C P Q hBC j i).nonneg

include hBC in
theorem matrixInclusionScaleRatio_nonneg : 0 ≤ matrixInclusionScaleRatio B C P Q :=
  zero_le_one.trans (matrixInclusionScaleRatio_one_le B C P Q hBC)

include hBC in
theorem matrixInclusionScaleRatio_inverse : (matrixInclusionScaleRatio B C P Q)⁻¹ =
    (matrixSubalgebraScale C Q)⁻¹ * matrixSubalgebraScale B P := by
  rw [matrixInclusionScaleRatio, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (matrixSubalgebraScale_isUnit B P))]
  exact (matrixSubalgebraScale_inverse_commutes C Q _ (hBC (matrixSubalgebraScale_mem B P))).eq.symm

include hBC in
theorem matrixInclusionScaleRatio_inverse_expansion : (matrixInclusionScaleRatio B C P Q)⁻¹ =
    ∑ j, ∑ i, (((matrixInclusionScaleCoefficient B C P Q j i)⁻¹ : ℝ) : ℂ) • matrixInclusionCell B C P Q j i := by
  rw [matrixInclusionScaleRatio_inverse B C P Q hBC, matrixSubalgebraScale_inverse]
  have he := matrixInclusionBlockScalars_product B C P Q
    (fun j => (matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) / Q.size j)
    (fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity B P B.subtype i)
  simpa only [matrixSubalgebraScale, matrixInclusionScaleCoefficient, _root_.mul_inv_rev, inv_div, mul_comm] using he

end ThomGame.Analysis
