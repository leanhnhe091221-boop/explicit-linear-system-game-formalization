module

public import ThomGame.Analysis.MatrixCommutingBoundedScale
public import ThomGame.Analysis.MatrixInclusionScaleTrace

/-!
# Ordered bounded scales of an actual subalgebra inclusion

The regularizer is any positive definite element of the smaller algebra.
It is not required to be central there.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

include hBC in
theorem matrixSubalgebraScale_le_of_inclusion :
    matrixSubalgebraScale B P ≤ matrixSubalgebraScale C Q := by
  have hc := matrixSubalgebraScale_commutes C Q _ (hBC (matrixSubalgebraScale_mem B P))
  have hi := matrixSubalgebraScale_inverse_commutes B P _ (matrixSubalgebraScale_mem B P)
  have hr : Commute (matrixInclusionScaleRatio B C P Q - 1) (matrixSubalgebraScale B P) :=
    (hc.mul_left hi).sub_left (Commute.one_left _)
  have hp := Commute.mul_nonneg
    (sub_nonneg.mpr (matrixInclusionScaleRatio_one_le B C P Q hBC))
    (matrixSubalgebraScale_nonneg B P) hr
  have he : (matrixInclusionScaleRatio B C P Q - 1) * matrixSubalgebraScale B P =
      matrixSubalgebraScale C Q - matrixSubalgebraScale B P := by
    rw [sub_mul, matrixInclusionScaleRatio, mul_assoc, matrixSubalgebraScale_inverse_mul, mul_one, one_mul]
  exact sub_nonneg.mp (he ▸ hp)

include hBC in
theorem matrixInclusionBoundedScale_order (M : CMatrix d) (hM : M.PosDef) (hMB : M ∈ B) :
    (matrixBoundedScale (matrixSubalgebraScale B P) M).PosDef ∧
    matrixBoundedScale (matrixSubalgebraScale B P) M ≤
      matrixBoundedScale (matrixSubalgebraScale C Q) M ∧
    (1 - matrixBoundedScale (matrixSubalgebraScale C Q) M).PosDef := by
  have hBM := matrixSubalgebraScale_commutes B P M hMB
  have hCM := matrixSubalgebraScale_commutes C Q M (hBC hMB)
  exact ⟨matrixBoundedScale_posDef (matrixSubalgebraScale_posDef B P) hM hBM,
    matrixBoundedScale_mono (matrixSubalgebraScale_posDef B P) (matrixSubalgebraScale_posDef C Q)
      hM hBM hCM (matrixSubalgebraScale_le_of_inclusion B C P Q hBC),
    matrixBoundedScale_one_sub_posDef (matrixSubalgebraScale_posDef C Q) hM hCM⟩

end ThomGame.Analysis
