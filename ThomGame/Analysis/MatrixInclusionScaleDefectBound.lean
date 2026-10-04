module

public import ThomGame.Analysis.MatrixBoundedScaleDefectBound
public import ThomGame.Analysis.MatrixInclusionBoundedScaleOrder
public import ThomGame.Analysis.NormalizedTraceBounds

/-!
# Quantitative concentration of the actual inverse scale ratio

The norm estimate keeps any denominator. At the matrix dimension it
also bounds the normalized trace, including the zero-dimensional case.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixTraceReal_self_le_rectHSNorm {d : Nat} (X : CMatrix d) :
    matrixTraceReal d X ≤ rectHSNorm d X := by
  by_cases hd : d = 0
  · subst d
    have hx : X = 0 := Subsingleton.elim _ _
    simp only [hx, matrixTraceReal_zero, rectHSNorm_zero, le_refl]
  · let : NeZero d := ⟨hd⟩
    calc
      matrixTraceReal d X = (normalizedTrace X).re := (normalizedTrace_re X).symm
      _ ≤ ‖normalizedTrace X‖ := Complex.re_le_norm _
      _ ≤ rectHSNorm d X := norm_normalizedTrace_le_hsNorm X

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

include hBC in
theorem matrixInclusionScaleRatio_defect_norm (r : Nat) (M : CMatrix d)
    (hM : M.PosDef) (hMB : M ∈ B) :
    rectHSNorm r (1 - (matrixInclusionScaleRatio B C P Q)⁻¹) ≤
      8 * (rectHSNorm r (matrixBoundedScale (matrixSubalgebraScale B P) M - (1 / 2 : ℂ) • 1) +
        rectHSNorm r (matrixBoundedScale (matrixSubalgebraScale C Q) M - (1 / 2 : ℂ) • 1)) := by
  have hBM := matrixSubalgebraScale_commutes B P M hMB
  have hCM := matrixSubalgebraScale_commutes C Q M (hBC hMB)
  have hBCs := (matrixSubalgebraScale_commutes C Q _ (hBC (matrixSubalgebraScale_mem B P))).symm
  have hD0 := sub_nonneg.mpr (matrixInclusionScaleRatio_inverse_le_one B C P Q hBC)
  have hD1 : 1 - (matrixInclusionScaleRatio B C P Q)⁻¹ ≤ 1 :=
    sub_le_self _ (matrixInclusionScaleRatio_inverse_nonneg B C P Q hBC)
  have hX0 := (matrixBoundedScale_posDef (matrixSubalgebraScale_posDef B P) hM hBM).posSemidef.nonneg
  have hX1 := (matrixBoundedScale_one_sub_posDef (matrixSubalgebraScale_posDef B P) hM hBM).posSemidef.nonneg
  apply matrixRatioDefect_center_bound r _ _ _
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hD0).mpr hD1)
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hX1).mpr (sub_le_self _ hX0))
  rw [matrixInclusionScaleRatio_inverse B C P Q hBC]
  exact matrixBoundedScale_ratio_defect_identity (matrixSubalgebraScale_posDef B P)
    (matrixSubalgebraScale_posDef C Q) hM hBCs hBM hCM

include hBC in
theorem matrixInclusionScaleRatio_defect_trace (M : CMatrix d) (hM : M.PosDef) (hMB : M ∈ B) :
    matrixTraceReal d (1 - (matrixInclusionScaleRatio B C P Q)⁻¹) ≤
      8 * (rectHSNorm d (matrixBoundedScale (matrixSubalgebraScale B P) M - (1 / 2 : ℂ) • 1) +
        rectHSNorm d (matrixBoundedScale (matrixSubalgebraScale C Q) M - (1 / 2 : ℂ) • 1)) :=
  (matrixTraceReal_self_le_rectHSNorm _).trans
    (matrixInclusionScaleRatio_defect_norm B C P Q hBC d M hM hMB)

end ThomGame.Analysis
