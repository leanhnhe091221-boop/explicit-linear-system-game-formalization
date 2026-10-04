module

public import ThomGame.Analysis.MatrixInclusionExpectationUnits
public import ThomGame.Analysis.MatrixInclusionScaleTrace

/-!
# The finite matrix-unit energy is the inverse scale trace

All sums run over the actual source and target blocks. The final
identity retains an arbitrary original normalization, including zero.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

theorem matrixInclusion_expectation_block_energy (r : Nat) (i : Fin P.count) (j : Fin Q.count) :
    (∑ c, ∑ f, rectHSNorm r
      (P.equiv (matrixBlockExpectation B (C.subtype (matrixStarBlockUnit C Q j c f))) i) ^ 2) =
      (P.size i : ℝ) ^ 2 *
        ((matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) /
          (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ)) ^ 2 *
        (matrixInclusionMultiplicity B C P Q hBC j i : ℝ) / r := by
  simp only [rectHSNorm_sq, ← Finset.sum_div]
  have hswap :
      (∑ c, ∑ f, ∑ a, ∑ b,
        ‖P.equiv (matrixBlockExpectation B (C.subtype (matrixStarBlockUnit C Q j c f))) i a b‖ ^ 2) =
      ∑ a, ∑ b, ∑ c, ∑ f,
        ‖P.equiv (matrixBlockExpectation B (C.subtype (matrixStarBlockUnit C Q j c f))) i a b‖ ^ 2 := by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun (x : Fin (Q.size j) × Fin (Q.size j))
        (y : Fin (P.size i) × Fin (P.size i)) =>
        ‖P.equiv (matrixBlockExpectation B
          (C.subtype (matrixStarBlockUnit C Q j x.1 x.2))) i y.1 y.2‖ ^ 2))
  rw [hswap]
  simp only [matrixInclusion_expectation_entry_energy B C P Q hBC,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem matrixInclusion_expectation_unit_energy (r : Nat) (j : Fin Q.count) :
    (∑ c, ∑ f, rectHSNorm r
      (matrixTraceProjection B (C.subtype (matrixStarBlockUnit C Q j c f))) ^ 2) =
      (∑ i, (matrixInclusionMultiplicity B C P Q hBC j i : ℝ) * (P.size i : ℝ) ^ 2 *
        (matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) ^ 2 /
        (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ)) / r := by
  simp_rw [matrixBlockExpectation_hsNorm_sq B P]
  have hswap :
      (∑ c, ∑ f, ∑ i, (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) *
        rectHSNorm r (P.equiv (matrixBlockExpectation B
          (C.subtype (matrixStarBlockUnit C Q j c f))) i) ^ 2) =
      ∑ i, (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) *
        (∑ c, ∑ f, rectHSNorm r (P.equiv (matrixBlockExpectation B
          (C.subtype (matrixStarBlockUnit C Q j c f))) i) ^ 2) := by
    simpa only [Fintype.sum_prod_type, Finset.mul_sum] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun (x : Fin (Q.size j) × Fin (Q.size j)) (i : Fin P.count) =>
        (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) *
          rectHSNorm r (P.equiv (matrixBlockExpectation B
            (C.subtype (matrixStarBlockUnit C Q j x.1 x.2))) i) ^ 2))
  rw [hswap]
  simp only [matrixInclusion_expectation_block_energy B C P Q hBC, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hq : (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (matrixStarRepresentationMultiplicity_pos B P B.subtype Subtype.val_injective i))
  rw [← mul_div_assoc]
  congr 1
  field_simp

include hBC in
theorem matrixInclusion_expectation_energy_scale_trace (r : Nat) :
    (∑ j, (Q.size j : ℝ)⁻¹ *
      (∑ c, ∑ f, rectHSNorm r
        (matrixTraceProjection B (C.subtype (matrixStarBlockUnit C Q j c f))) ^ 2)) =
      matrixTraceReal r (matrixInclusionScaleRatio B C P Q)⁻¹ := by
  rw [matrixInclusionScaleRatio_inverse_trace B C P Q hBC]
  simp only [matrixInclusion_expectation_unit_energy B C P Q hBC,
    Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end ThomGame.Analysis
