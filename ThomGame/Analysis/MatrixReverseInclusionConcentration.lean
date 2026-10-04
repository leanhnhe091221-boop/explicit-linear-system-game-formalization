module

public import ThomGame.Analysis.MatrixInclusionScaleDefectBound
public import ThomGame.Analysis.MatrixReverseInclusionScale

/-!
# Reverse near inclusion from bounded-scale concentration

Combining the quantitative defect bound with Lemma 4.1 controls the
entire target unit ball, not merely a selected finite set.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

include hBC in
theorem matrixReverseInclusion_center_error (M : CMatrix d) (hM : M.PosDef) (hMB : M ∈ B) :
    matrixNearInclusionError C B ≤
      4 * Real.sqrt (rectHSNorm d (matrixBoundedScale (matrixSubalgebraScale B P) M - (1 / 2 : ℂ) • 1) +
        rectHSNorm d (matrixBoundedScale (matrixSubalgebraScale C Q) M - (1 / 2 : ℂ) • 1)) := by
  apply (matrixReverseInclusion_scale_error B C P Q hBC).trans
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (matrixInclusionScaleRatio_trace_defect_nonneg B C P Q hBC d),
    Real.sq_sqrt (add_nonneg (rectHSNorm_nonneg _ _) (rectHSNorm_nonneg _ _))]
  linarith [matrixInclusionScaleRatio_defect_trace B C P Q hBC M hM hMB]

include hBC in
theorem matrixReverseInclusion_center_near (M : CMatrix d) (hM : M.PosDef) (hMB : M ∈ B) :
    MatrixNearInclusion C B
      (4 * Real.sqrt (rectHSNorm d (matrixBoundedScale (matrixSubalgebraScale B P) M - (1 / 2 : ℂ) • 1) +
        rectHSNorm d (matrixBoundedScale (matrixSubalgebraScale C Q) M - (1 / 2 : ℂ) • 1))) :=
  (matrixNearInclusion_iff_error_le C B _).mpr
    (matrixReverseInclusion_center_error B C P Q hBC M hM hMB)

end ThomGame.Analysis
