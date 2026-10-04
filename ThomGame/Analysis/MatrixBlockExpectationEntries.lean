module

public import ThomGame.Analysis.MatrixStarBlockTracePairing
public import ThomGame.Analysis.MatrixTraceProjection

/-!
# Entries of the actual trace expectation

The coefficient in a simple block is obtained by pairing with the
opposite matrix unit and dividing by its actual rank multiplicity.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A)

noncomputable def matrixBlockExpectation (X : CMatrix d) : A :=
  ⟨matrixTraceProjection A X, matrixTraceProjection_mem A X⟩

theorem matrixTraceProjection_unnormalized_pairing (X Y : CMatrix d) (hY : Y ∈ A) :
    (star Y * matrixTraceProjection A X).trace = (star Y * X).trace :=
  (div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne d) : (d : ℂ) ≠ 0)).mp
    (matrixTraceProjection_pairing A X Y hY)

theorem matrixBlockExpectation_entry (X : CMatrix d) (i : Fin P.count)
    (a b : Fin (P.size i)) :
    P.equiv (matrixBlockExpectation A X) i a b =
      (A.subtype (matrixStarBlockUnit A P i b a) * X).trace /
        (matrixStarRepresentationMultiplicity A P A.subtype i : ℂ) := by
  have he := matrixTraceProjection_unnormalized_pairing A X
    (A.subtype (matrixStarBlockUnit A P i a b)) (matrixStarBlockUnit A P i a b).property
  rw [← map_star, matrixStarBlockUnit_star] at he
  change (A.subtype (matrixStarBlockUnit A P i b a) *
    A.subtype (matrixBlockExpectation A X)).trace = _ at he
  rw [matrixStarRepresentation_unit_pairing] at he
  have hq : (matrixStarRepresentationMultiplicity A P A.subtype i : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (matrixStarRepresentationMultiplicity_pos A P A.subtype Subtype.val_injective i))
  exact (eq_div_iff hq).mpr ((mul_comm _ _).trans he)

theorem matrixBlockExpectation_hsNorm_sq (r : Nat) (X : CMatrix d) :
    rectHSNorm r (matrixTraceProjection A X) ^ 2 =
      ∑ i, (matrixStarRepresentationMultiplicity A P A.subtype i : ℝ) *
        rectHSNorm r (P.equiv (matrixBlockExpectation A X) i) ^ 2 :=
  matrixStarRepresentation_hsNorm_sq A P A.subtype r (matrixBlockExpectation A X)

end ThomGame.Analysis
