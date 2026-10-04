module

public import ThomGame.Analysis.MatrixInclusionConditionalWeights
public import ThomGame.Analysis.MatrixStarBlockScalarCoordinates
public import ThomGame.Analysis.MatrixBlockExpectationEntries
public import ThomGame.Analysis.MatrixInclusionCells

/-!
# Actual conditional expectation of central supports and joint cells
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

theorem matrixInclusion_support_trace_pairing (Y : B) (j : Fin Q.count) :
    (B.subtype Y * matrixStarBlockSupport C Q j).trace =
      (matrixStarRepresentationMultiplicity C Q C.subtype j : ℂ) *
        (matrixInclusionBlockRepresentation B C Q hBC j Y).trace := by
  rw [Matrix.trace_mul_comm, matrixStarBlockSupport_diagonal_sum]
  change ((∑ a, C.subtype (matrixStarBlockUnit C Q j a a)) *
    C.subtype (StarSubalgebra.inclusion hBC Y)).trace = _
  simp only [Matrix.sum_mul, Matrix.trace_sum, matrixStarRepresentation_unit_pairing,
    ← Finset.mul_sum]
  rfl

variable [NeZero d]

theorem matrixInclusion_support_expectation (j : Fin Q.count) :
    matrixTraceProjection B (matrixStarBlockSupport C Q j) =
      matrixStarBlockScalar B P (fun i => matrixInclusionConditionalWeight B C P Q hBC j i) := by
  suffices matrixBlockExpectation B (matrixStarBlockSupport C Q j) =
      matrixStarBlockScalarElement B P (fun i => matrixInclusionConditionalWeight B C P Q hBC j i) from
    congrArg B.subtype this
  apply P.equiv.injective
  change P.equiv (matrixBlockExpectation B (matrixStarBlockSupport C Q j)) =
    P.equiv (matrixStarBlockScalarElement B P (fun i => matrixInclusionConditionalWeight B C P Q hBC j i))
  funext i
  rw [matrixStarBlockScalarElement_equiv]
  ext a b
  rw [matrixBlockExpectation_entry,
    matrixInclusion_support_trace_pairing B C Q hBC, matrixStarRepresentation_unit_trace]
  classical
  by_cases hab : a = b
  · subst b
    simp only [ite_true, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      matrixInclusionConditionalWeight, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]
    rfl
  · simp only [ite_eq_right (Ne.symm hab), zero_div, Matrix.smul_apply, Matrix.one_apply_ne hab,
      smul_eq_mul, mul_zero]

theorem matrixInclusion_cell_expectation (j : Fin Q.count) (i : Fin P.count) :
    matrixTraceProjection B (matrixInclusionCell B C P Q j i) =
      (matrixInclusionConditionalWeight B C P Q hBC j i : ℂ) • matrixStarBlockSupport B P i := by
  rw [matrixInclusionCell, matrixTraceProjection_mul_right B _ _ (matrixStarBlockSupport_mem B P i),
    matrixInclusion_support_expectation B C P Q hBC]
  rw [(matrixStarBlockScalar_commutes B P _ _ (matrixStarBlockSupport_mem B P i)).eq,
    matrixStarBlockScalar_block]

end ThomGame.Analysis
