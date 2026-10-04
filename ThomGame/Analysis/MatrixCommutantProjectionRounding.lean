module

public import ThomGame.Analysis.MatrixCommutantAveraging
public import ThomGame.Analysis.MatrixExpectationProjectionGeometry

/-!
# Averaging a projection and rounding the actual commutant expectation

A uniform lower bound on orbit overlap gives the variance bound with
constant one. The closed half cut has squared distance and trace error
at most twice that variance, and preserves every exact common commutation.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem matrixCommutantProjection_variance_le (r : Nat) (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsStarProjection P) (c : ℝ)
    (hbound : ∀ U : unitary A, matrixTraceReal r P - c ≤
      matrixTraceReal r (P * matrixUnitaryConjugation (matrixSubalgebraUnitary A U) P)) :
    rectHSNorm r (P - matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) P) ^ 2 ≤ c := by
  let f : CMatrix d →ₗ[ℝ] ℝ :=
    { toFun X := matrixTraceReal r (P * X)
      map_add' X Y := by rw [mul_add, matrixTraceReal_add]
      map_smul' t X := by
        rw [Matrix.mul_smul, matrixTraceReal_real_smul]
        rfl }
  have he := matrixCommutantProjection_linear_lower_bound A P f (matrixTraceReal r P - c) hbound
  change matrixTraceReal r P - c ≤ matrixTraceReal r
    (P * matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) P) at he
  rw [matrixTraceProjection_projection_variance r _ hP, matrixTraceReal_sub,
    matrixTraceProjection_traceReal, matrixTraceProjection_traceReal_square r _ hP.isSelfAdjoint]
  linarith

theorem exists_matrixCommutant_roundedProjection (r : Nat) (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsStarProjection P) (c : ℝ)
    (hbound : ∀ U : unitary A, matrixTraceReal r P - c ≤
      matrixTraceReal r (P * matrixUnitaryConjugation (matrixSubalgebraUnitary A U) P)) :
    ∃ h Q : CMatrix d,
      h = matrixTraceProjection (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) P ∧
      0 ≤ h ∧ h ≤ 1 ∧ matrixTraceReal r h = matrixTraceReal r P ∧
      matrixTraceReal r (h - h * h) = rectHSNorm r (P - h) ^ 2 ∧
      rectHSNorm r (P - h) ^ 2 ≤ c ∧
      Q = matrixHalfProjection h ∧ IsStarProjection Q ∧
      Q ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) ∧
      rectHSNorm r (P - Q) ^ 2 ≤ 2 * c ∧
      |matrixTraceReal r Q - matrixTraceReal r P| ≤ 2 * c ∧
      ∀ X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)),
        P * X = X * P → h * X = X * h ∧ Q * X = X * Q := by
  let C := StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))
  let h := matrixTraceProjection C P
  let Q := matrixHalfProjection h
  have hb := matrixTraceProjection_projection_bounds C hP
  have hv := matrixCommutantProjection_variance_le r A hP c hbound
  refine ⟨h, Q, rfl, hb.1, hb.2, matrixTraceProjection_traceReal r C P,
    (matrixTraceProjection_projection_variance r C hP).symm, hv, rfl,
    matrixHalfProjection_isStarProjection h, matrixHalfProjection_expectation_mem C P,
    (matrixHalfProjection_expectation_distance_le r C hP).trans (by linarith),
    (matrixHalfProjection_expectation_trace_error_le r C hP).trans (by linarith), ?_⟩
  intro X hX hPX
  have hh : h * X = X * h := matrixTraceProjection_preserves_commutation C P X hX hPX
  exact ⟨hh, (matrixHalfProjection_commute hb.1.isSelfAdjoint.isHermitian hh.symm).eq.symm⟩

end ThomGame.Analysis
