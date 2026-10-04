module

public import ThomGame.Analysis.MatrixSubalgebraStarBlocks
public import ThomGame.Analysis.MatrixAlgebraicFaithfulMultiplicity

/-!
# Star matrix units and actual representation multiplicities

The star-block structure is constructed in MatrixSubalgebraStarBlocks.
For any such structure, forgetting the star proof reuses the exact
algebraic multiplicity definitions and dimension theorems.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))

abbrev MatrixSubalgebraStarBlocks.toAlgebraic (P : MatrixSubalgebraStarBlocks A) :
    MatrixSubalgebraAlgebraicBlocks A := ⟨P.count, P.size, P.size_pos, P.equiv.toAlgEquiv⟩

variable (P : MatrixSubalgebraStarBlocks A)

noncomputable abbrev matrixStarBlockUnit (i : Fin P.count) (a b : Fin (P.size i)) : A :=
  matrixAlgebraicBlockUnit A P.toAlgebraic i a b

theorem matrixStarBlockUnit_star (i : Fin P.count) (a b : Fin (P.size i)) :
    star (matrixStarBlockUnit A P i a b) = matrixStarBlockUnit A P i b a := by
  change star (P.equiv.symm (Pi.single i (Matrix.single a b 1))) =
    P.equiv.symm (Pi.single i (Matrix.single b a 1))
  rw [← map_star]
  simp only [Pi.star_single, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

theorem matrixStarBlockUnit_mul (i : Fin P.count) (a b c f : Fin (P.size i)) :
    matrixStarBlockUnit A P i a b * matrixStarBlockUnit A P i c f =
      if b = c then matrixStarBlockUnit A P i a f else 0 :=
  matrixAlgebraicBlockUnit_mul_ite A P.toAlgebraic i a b c f

theorem matrixStarBlockUnit_mul_other (i j : Fin P.count) (hij : i ≠ j)
    (a b : Fin (P.size i)) (c f : Fin (P.size j)) :
    matrixStarBlockUnit A P i a b * matrixStarBlockUnit A P j c f = 0 :=
  matrixAlgebraicBlockUnit_mul_other A P.toAlgebraic i j hij a b c f

theorem matrixStarBlockUnit_total_diagonal_sum : ∑ i, ∑ a, matrixStarBlockUnit A P i a a = 1 :=
  matrixAlgebraicBlockUnit_total_diagonal_sum A P.toAlgebraic

theorem matrixStarRepresentationUnit_adjoint (ρ : A →⋆ₐ[ℂ] CMatrix m)
    (i : Fin P.count) (a b : Fin (P.size i)) :
    (ρ (matrixStarBlockUnit A P i a b))ᴴ = ρ (matrixStarBlockUnit A P i b a) := by
  change star (ρ (matrixStarBlockUnit A P i a b)) = _
  rw [← map_star, matrixStarBlockUnit_star]

theorem matrixStarRepresentationUnit_diagonal_projection (ρ : A →⋆ₐ[ℂ] CMatrix m)
    (i : Fin P.count) (a : Fin (P.size i)) : IsStarProjection (ρ (matrixStarBlockUnit A P i a a)) := by
  constructor
  · exact matrixAlgebraicRepresentation_diagonal_idempotent A P.toAlgebraic ρ.toAlgHom i a
  · exact matrixStarRepresentationUnit_adjoint A P ρ i a a

noncomputable abbrev matrixStarRepresentationMultiplicity (ρ : A →⋆ₐ[ℂ] CMatrix m) (i : Fin P.count) : Nat :=
  matrixAlgebraicRepresentationMultiplicity A P.toAlgebraic ρ.toAlgHom i

theorem matrixStarRepresentation_dimension (ρ : A →⋆ₐ[ℂ] CMatrix m) :
    m = ∑ i, P.size i * matrixStarRepresentationMultiplicity A P ρ i :=
  matrixAlgebraicRepresentation_dimension A P.toAlgebraic ρ.toAlgHom

theorem matrixStarRepresentationMultiplicity_pos (ρ : A →⋆ₐ[ℂ] CMatrix m)
    (hρ : Function.Injective ρ) (i : Fin P.count) : 0 < matrixStarRepresentationMultiplicity A P ρ i :=
  matrixAlgebraicRepresentationMultiplicity_pos A P.toAlgebraic ρ.toAlgHom hρ i

end ThomGame.Analysis
