module

public import ThomGame.Analysis.MatrixAlgebraicRepresentationTrace
public import ThomGame.Analysis.MatrixStarBlockAction
public import ThomGame.Analysis.RectangularNormalizedTrace

/-!
# Block-entry trace pairing and exact HS weights

These formulas use the actual star representation and its rank
multiplicities, with an arbitrary original normalization r.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d)) (P : MatrixSubalgebraStarBlocks A)
    (ρ : A →⋆ₐ[ℂ] CMatrix m)

theorem matrixStarRepresentation_unit_trace (i : Fin P.count) (a b : Fin (P.size i)) :
    (ρ (matrixStarBlockUnit A P i a b)).trace =
      if a = b then (matrixStarRepresentationMultiplicity A P ρ i : ℂ) else 0 :=
  matrixAlgebraicRepresentation_unit_trace A P.toAlgebraic ρ.toAlgHom i a b

theorem matrixStarRepresentation_unit_pairing (X : A) (i : Fin P.count) (a b : Fin (P.size i)) :
    (ρ (matrixStarBlockUnit A P i a b) * ρ X).trace =
      (matrixStarRepresentationMultiplicity A P ρ i : ℂ) * P.equiv X i b a := by
  classical
  rw [Matrix.trace_mul_comm, ← map_mul, matrixStarBlockUnit_left_mul]
  simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul,
    matrixStarRepresentation_unit_trace, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_comm _ _

theorem matrixStarRepresentation_trace (X : A) :
    (ρ X).trace = ∑ i, (matrixStarRepresentationMultiplicity A P ρ i : ℂ) * (P.equiv X i).trace :=
  matrixAlgebraicRepresentation_trace A P.toAlgebraic ρ.toAlgHom X

theorem matrixStarRepresentation_unit_hsNorm_sq (r : Nat) (i : Fin P.count)
    (a b : Fin (P.size i)) :
    rectHSNorm r (ρ (matrixStarBlockUnit A P i a b)) ^ 2 =
      (matrixStarRepresentationMultiplicity A P ρ i : ℝ) / r := by
  rw [← matrixTraceReal_gram]
  change matrixTraceReal r (star (ρ (matrixStarBlockUnit A P i a b)) *
    ρ (matrixStarBlockUnit A P i a b)) = _
  rw [← map_star, ← map_mul, matrixStarBlockUnit_star,
    matrixAlgebraicBlockUnit_mul_same]
  simp only [matrixTraceReal, matrixStarRepresentation_unit_trace, ite_true,
    Complex.natCast_re]

theorem matrixStarRepresentation_hsNorm_sq (r : Nat) (X : A) :
    rectHSNorm r (ρ X) ^ 2 =
      ∑ i, (matrixStarRepresentationMultiplicity A P ρ i : ℝ) * rectHSNorm r (P.equiv X i) ^ 2 := by
  have he := matrixStarRepresentation_trace A P ρ (star X * X)
  simp only [map_mul, map_star, Pi.mul_apply, Pi.star_apply] at he
  rw [← matrixTraceReal_gram]
  change matrixTraceReal r (star (ρ X) * ρ X) = _
  unfold matrixTraceReal
  rw [he]
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc, ← matrixTraceReal_gram]
  rfl

end ThomGame.Analysis
