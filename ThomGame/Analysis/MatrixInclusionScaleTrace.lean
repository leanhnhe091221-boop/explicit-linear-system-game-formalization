module

public import ThomGame.Analysis.MatrixInclusionScaleRatio

/-!
# The exact trace term in Thom's reverse-inclusion estimate

The inverse scale ratio is a positive contraction. Its trace is the
explicit Bratteli sum, retaining any chosen original denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixTraceReal_ofReal_smul {d : Nat} (r : Nat) (c : ℝ) (X : CMatrix d) :
    matrixTraceReal r ((c : ℂ) • X) = c * matrixTraceReal r X := by
  simp [matrixTraceReal, Matrix.trace_smul, mul_div_assoc]

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

include hBC in
theorem matrixInclusionScaleRatio_inverse_nonneg : 0 ≤ (matrixInclusionScaleRatio B C P Q)⁻¹ := by
  rw [matrixInclusionScaleRatio_inverse_expansion B C P Q hBC]
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  exact smul_nonneg (by exact_mod_cast (inv_nonneg.mpr (matrixInclusionScaleCoefficient_pos B C P Q j i).le))
    (matrixInclusionCell_projection B C P Q hBC j i).nonneg

include hBC in
theorem matrixInclusionScaleRatio_inverse_le_one : (matrixInclusionScaleRatio B C P Q)⁻¹ ≤ 1 := by
  have he : 1 - (matrixInclusionScaleRatio B C P Q)⁻¹ =
      ∑ j, ∑ i, ((1 - (matrixInclusionScaleCoefficient B C P Q j i)⁻¹ : ℝ) : ℂ) •
        matrixInclusionCell B C P Q j i := by
    rw [matrixInclusionScaleRatio_inverse_expansion B C P Q hBC, ← matrixInclusionCell_sum B C P Q]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, Finset.sum_sub_distrib]
  apply sub_nonneg.mp
  rw [he]
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  by_cases hz : matrixInclusionCell B C P Q j i = 0
  · simp only [hz, smul_zero, le_refl]
  · have hc := matrixInclusionScaleCoefficient_one_le B C P Q hBC j i hz
    have hinv : (matrixInclusionScaleCoefficient B C P Q j i)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hc
    exact smul_nonneg (by exact_mod_cast sub_nonneg.mpr hinv)
      (matrixInclusionCell_projection B C P Q hBC j i).nonneg

include hBC in
theorem matrixInclusionScaleRatio_inverse_trace (r : Nat) :
    matrixTraceReal r (matrixInclusionScaleRatio B C P Q)⁻¹ =
      (∑ j, ∑ i, (matrixInclusionMultiplicity B C P Q hBC j i : ℝ) * (P.size i : ℝ) ^ 2 *
        (matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) ^ 2 /
        ((matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) * Q.size j)) / r := by
  have hterm (j : Fin Q.count) (i : Fin P.count) :
      (matrixInclusionScaleCoefficient B C P Q j i)⁻¹ *
        ((P.size i : ℝ) * matrixStarRepresentationMultiplicity C Q C.subtype j *
          matrixInclusionMultiplicity B C P Q hBC j i) =
      (matrixInclusionMultiplicity B C P Q hBC j i : ℝ) * (P.size i : ℝ) ^ 2 *
        (matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) ^ 2 /
        ((matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) * Q.size j) := by
    have hp : (P.size i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (P.size_pos i))
    have hr : (Q.size j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Q.size_pos j))
    have hq : (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (matrixStarRepresentationMultiplicity_pos B P B.subtype Subtype.val_injective i))
    have hs : (matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (matrixStarRepresentationMultiplicity_pos C Q C.subtype Subtype.val_injective j))
    rw [matrixInclusionScaleCoefficient]
    field_simp
  rw [matrixInclusionScaleRatio_inverse_expansion B C P Q hBC]
  simp only [matrixTraceReal_sum, matrixTraceReal_ofReal_smul,
    matrixInclusionCell_trace B C P Q hBC, ← mul_div_assoc, hterm, Finset.sum_div]

include hBC in
theorem matrixInclusionScaleRatio_trace_defect_nonneg (r : Nat) :
    0 ≤ matrixTraceReal r (1 - (matrixInclusionScaleRatio B C P Q)⁻¹) :=
  matrixTraceReal_nonneg r (sub_nonneg.mpr (matrixInclusionScaleRatio_inverse_le_one B C P Q hBC))

end ThomGame.Analysis
