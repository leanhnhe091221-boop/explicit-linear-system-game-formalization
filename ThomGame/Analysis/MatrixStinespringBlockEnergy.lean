module

public import ThomGame.Analysis.MatrixBlockCommutantExpectation
public import ThomGame.Analysis.MatrixInclusionExpectationEnergy
public import ThomGame.Analysis.MatrixStinespringAveraging

/-!
# Exact Stinespring commutant variance for a nested pair

The range projection in the actual dilation has commutant variance
equal to the inverse-scale trace defect, at the original dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixBlockCommutantAverage_range_overlap (r : Nat)
    (A : StarSubalgebra ℂ (CMatrix d)) (P : MatrixSubalgebraStarBlocks A)
    (ρ : A →⋆ₐ[ℂ] CMatrix m) (V : Matrix (Fin m) (Fin d) ℂ) :
    matrixTraceReal r ((V * Vᴴ) * matrixBlockCommutantAverage A P ρ (V * Vᴴ)) =
      ∑ i, (P.size i : ℝ)⁻¹ *
        (∑ a, ∑ b, rectHSNorm r (Vᴴ * ρ (matrixStarBlockUnit A P i a b) * V) ^ 2) := by
  have hc (i : Fin P.count) : (P.size i : ℂ)⁻¹ = (((P.size i : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  simp only [matrixBlockCommutantAverage, Matrix.mul_sum, Matrix.mul_smul, hc,
    matrixTraceReal_sum, matrixTraceReal_ofReal_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [matrixBlockUnitSandwich, Matrix.mul_sum, matrixTraceReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← matrixStarRepresentationUnit_adjoint A P ρ i a b]
  exact matrixStinespring_range_overlap r V _

variable [NeZero d] [NeZero m]

theorem matrixStinespring_commutant_overlap_scale
    (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)
    (ρ : CMatrix d →⋆ₐ[ℂ] CMatrix m) (V : Matrix (Fin m) (Fin d) ℂ)
    (hE : ∀ X, Vᴴ * ρ X * V = matrixTraceProjection B X) :
    matrixTraceReal d ((V * Vᴴ) *
      matrixTraceProjection (StarSubalgebra.centralizer ℂ ((ρ.comp C.subtype).range : Set (CMatrix m)))
        (V * Vᴴ)) = matrixTraceReal d (matrixInclusionScaleRatio B C P Q)⁻¹ := by
  rw [← matrixBlockCommutantAverage_eq_expectation C Q (ρ.comp C.subtype),
    matrixBlockCommutantAverage_range_overlap]
  simp only [StarAlgHom.comp_apply, hE]
  exact matrixInclusion_expectation_energy_scale_trace B C P Q hBC d

theorem matrixStinespring_commutant_variance_scale
    (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)
    (ρ : CMatrix d →⋆ₐ[ℂ] CMatrix m) (V : Matrix (Fin m) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) (hE : ∀ X, Vᴴ * ρ X * V = matrixTraceProjection B X) :
    rectHSNorm d ((V * Vᴴ) -
      matrixTraceProjection (StarSubalgebra.centralizer ℂ ((ρ.comp C.subtype).range : Set (CMatrix m)))
        (V * Vᴴ)) ^ 2 = matrixTraceReal d (1 - (matrixInclusionScaleRatio B C P Q)⁻¹) := by
  have hp := matrixStinespring_range_projection V hV
  rw [matrixTraceProjection_projection_variance d _ hp, matrixTraceReal_sub,
    matrixTraceProjection_traceReal, matrixTraceProjection_traceReal_square d _ hp.isSelfAdjoint,
    matrixStinespring_range_trace V hV, matrixStinespring_commutant_overlap_scale B C P Q hBC ρ V hE,
    matrixTraceReal_sub]
  congr 1
  simp [matrixTraceReal, NeZero.ne d]

end ThomGame.Analysis
