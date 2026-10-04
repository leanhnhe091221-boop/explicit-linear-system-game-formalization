module

public import ThomGame.Analysis.MatrixStarBlockScalars

/-!
# The scale operator of an actual finite matrix subalgebra

Its value on a block M_p tensor 1_q is p/q. The operator and its
reciprocal are positive, central, invertible elements of the algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d)) (P : MatrixSubalgebraStarBlocks A)

noncomputable def matrixSubalgebraScale : CMatrix d :=
  matrixStarBlockScalar A P (fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity A P A.subtype i)

theorem matrixSubalgebraScale_coefficient_pos (i : Fin P.count) :
    0 < (P.size i : ℝ) / matrixStarRepresentationMultiplicity A P A.subtype i :=
  div_pos (Nat.cast_pos.mpr (P.size_pos i))
    (Nat.cast_pos.mpr (matrixStarRepresentationMultiplicity_pos A P A.subtype Subtype.val_injective i))

theorem matrixSubalgebraScale_mem : matrixSubalgebraScale A P ∈ A := matrixStarBlockScalar_mem A P _

theorem matrixSubalgebraScale_commutes (X : CMatrix d) (hX : X ∈ A) :
    Commute (matrixSubalgebraScale A P) X := matrixStarBlockScalar_commutes A P _ X hX

theorem matrixSubalgebraScale_nonneg : 0 ≤ matrixSubalgebraScale A P :=
  matrixStarBlockScalar_nonneg A P _ (fun i => (matrixSubalgebraScale_coefficient_pos A P i).le)

theorem matrixSubalgebraScale_isUnit : IsUnit (matrixSubalgebraScale A P) :=
  matrixStarBlockScalar_isUnit A P _ (fun i => ne_of_gt (matrixSubalgebraScale_coefficient_pos A P i))

theorem matrixSubalgebraScale_posDef : (matrixSubalgebraScale A P).PosDef :=
  (Matrix.nonneg_iff_posSemidef.mp (matrixSubalgebraScale_nonneg A P)).posDef_iff_isUnit.mpr
    (matrixSubalgebraScale_isUnit A P)

theorem matrixSubalgebraScale_inverse : (matrixSubalgebraScale A P)⁻¹ =
    matrixStarBlockScalar A P (fun i => (matrixStarRepresentationMultiplicity A P A.subtype i : ℝ) / P.size i) := by
  rw [matrixSubalgebraScale, matrixStarBlockScalar_inverse A P _
    (fun i => ne_of_gt (matrixSubalgebraScale_coefficient_pos A P i))]
  simp only [inv_div]

theorem matrixSubalgebraScale_inverse_mem : (matrixSubalgebraScale A P)⁻¹ ∈ A := by
  rw [matrixSubalgebraScale_inverse]
  exact matrixStarBlockScalar_mem A P _

theorem matrixSubalgebraScale_inverse_nonneg : 0 ≤ (matrixSubalgebraScale A P)⁻¹ := by
  rw [matrixSubalgebraScale_inverse]
  exact matrixStarBlockScalar_nonneg A P _ (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem matrixSubalgebraScale_inverse_commutes (X : CMatrix d) (hX : X ∈ A) :
    Commute (matrixSubalgebraScale A P)⁻¹ X := by
  rw [matrixSubalgebraScale_inverse]
  exact matrixStarBlockScalar_commutes A P _ X hX

theorem matrixSubalgebraScale_mul_inverse : matrixSubalgebraScale A P * (matrixSubalgebraScale A P)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (matrixSubalgebraScale_isUnit A P))

theorem matrixSubalgebraScale_inverse_mul : (matrixSubalgebraScale A P)⁻¹ * matrixSubalgebraScale A P = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (matrixSubalgebraScale_isUnit A P))

end ThomGame.Analysis
