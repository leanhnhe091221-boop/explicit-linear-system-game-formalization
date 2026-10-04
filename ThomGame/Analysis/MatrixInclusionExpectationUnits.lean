module

public import ThomGame.Analysis.MatrixBlockExpectationEntries
public import ThomGame.Analysis.MatrixInclusionMultiplicity

/-!
# Trace expectation on the actual units of a containing algebra

The Bratteli multiplicities enter through the squared norms of the
restricted source matrix units, without choosing occurrence coordinates.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

omit [NeZero d] in
theorem matrixInclusion_unit_pairing (i : Fin P.count) (a b : Fin (P.size i))
    (j : Fin Q.count) (c f : Fin (Q.size j)) :
    (B.subtype (matrixStarBlockUnit B P i a b) *
      C.subtype (matrixStarBlockUnit C Q j c f)).trace =
      (matrixStarRepresentationMultiplicity C Q C.subtype j : ℂ) *
        matrixInclusionBlockRepresentation B C Q hBC j (matrixStarBlockUnit B P i a b) f c := by
  rw [Matrix.trace_mul_comm]
  exact matrixStarRepresentation_unit_pairing C Q C.subtype
    (StarSubalgebra.inclusion hBC (matrixStarBlockUnit B P i a b)) j c f

theorem matrixInclusion_expectation_unit_entry (i : Fin P.count) (a b : Fin (P.size i))
    (j : Fin Q.count) (c f : Fin (Q.size j)) :
    P.equiv (matrixBlockExpectation B (C.subtype (matrixStarBlockUnit C Q j c f))) i a b =
      ((matrixStarRepresentationMultiplicity C Q C.subtype j : ℂ) /
        (matrixStarRepresentationMultiplicity B P B.subtype i : ℂ)) *
        matrixInclusionBlockRepresentation B C Q hBC j (matrixStarBlockUnit B P i b a) f c := by
  rw [matrixBlockExpectation_entry, matrixInclusion_unit_pairing B C P Q hBC]
  ring

theorem matrixInclusion_expectation_entry_energy (i : Fin P.count) (a b : Fin (P.size i))
    (j : Fin Q.count) :
    (∑ c, ∑ f,
      ‖P.equiv (matrixBlockExpectation B (C.subtype (matrixStarBlockUnit C Q j c f))) i a b‖ ^ 2) =
      ((matrixStarRepresentationMultiplicity C Q C.subtype j : ℝ) /
        (matrixStarRepresentationMultiplicity B P B.subtype i : ℝ)) ^ 2 *
        (matrixInclusionMultiplicity B C P Q hBC j i : ℝ) := by
  have he := matrixStarRepresentation_unit_hsNorm_sq B P
    (matrixInclusionBlockRepresentation B C Q hBC j) 1 i b a
  rw [rectHSNorm_sq] at he
  simp only [Nat.cast_one, div_one] at he
  simp_rw [matrixInclusion_expectation_unit_entry B C P Q hBC, norm_mul, norm_div,
    Complex.norm_natCast, mul_pow]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm, he]
  rfl

end ThomGame.Analysis
