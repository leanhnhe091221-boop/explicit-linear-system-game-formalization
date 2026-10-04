module

public import ThomGame.Analysis.MatrixInclusionMultiplicity

/-!
# Conditional probability weights from the actual Bratteli matrix
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

noncomputable def matrixInclusionConditionalWeight (j : Fin Q.count) (i : Fin P.count) : ℝ :=
  ((matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) *
    matrixInclusionMultiplicity B C P Q hBC j i) /
    matrixStarRepresentationMultiplicity B P B.subtype i

theorem matrixInclusionConditionalWeight_nonneg (j : Fin Q.count) (i : Fin P.count) :
    0 ≤ matrixInclusionConditionalWeight B C P Q hBC j i := by
  unfold matrixInclusionConditionalWeight
  positivity

theorem matrixInclusionConditionalWeight_sum (i : Fin P.count) :
    ∑ j, matrixInclusionConditionalWeight B C P Q hBC j i = 1 := by
  have he := matrixInclusionMultiplicity_column B C P Q hBC i
  have hc : (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) =
      ∑ j, (matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) *
        matrixInclusionMultiplicity B C P Q hBC j i := by exact_mod_cast he
  have hq : (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (matrixStarRepresentationMultiplicity_pos B P B.subtype Subtype.val_injective i))
  simp only [matrixInclusionConditionalWeight, ← Finset.sum_div, ← hc, div_self hq]

end ThomGame.Analysis
