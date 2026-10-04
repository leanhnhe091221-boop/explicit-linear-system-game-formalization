module

public import ThomGame.Analysis.MatrixAlgebraicRepresentationMultiplicity
public import ThomGame.Analysis.RectangularMatrixRankBounds

/-!
# Rank of an exact intertwiner is bounded by common multiplicities

Decomposing by the actual central supports gives the weighted minimum
bound used in Thom's multiplicity comparison. It applies to arbitrary
unital algebra representations, without assuming a chosen block basis.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem matrixAlgebraicIntertwiner_rank_le {d m n : Nat}
    (A : StarSubalgebra ℂ (CMatrix d)) (S : MatrixSubalgebraAlgebraicBlocks A)
    (ρ : A →ₐ[ℂ] CMatrix n) (σ : A →ₐ[ℂ] CMatrix m)
    (T : Matrix (Fin m) (Fin n) ℂ) (hT : ∀ X : A, T * ρ X = σ X * T) :
    T.rank ≤ ∑ i, S.size i * min (matrixAlgebraicRepresentationMultiplicity A S ρ i)
      (matrixAlgebraicRepresentationMultiplicity A S σ i) := by
  have hs : ∑ i, T * ρ (matrixAlgebraicBlockSupport A S i) = T := by
    rw [← Matrix.mul_sum, ← map_sum, matrixAlgebraicBlockSupport_sum, map_one, Matrix.mul_one]
  calc
    T.rank = (∑ i, T * ρ (matrixAlgebraicBlockSupport A S i)).rank := congrArg Matrix.rank hs.symm
    _ ≤ ∑ i, (T * ρ (matrixAlgebraicBlockSupport A S i)).rank := rectangularMatrix_rank_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hρ := Matrix.rank_mul_le_right T (ρ (matrixAlgebraicBlockSupport A S i))
      have hσ := Matrix.rank_mul_le_left (σ (matrixAlgebraicBlockSupport A S i)) T
      rw [← hT] at hσ
      rw [matrixAlgebraicRepresentation_support_rank] at hρ hσ
      by_cases h : matrixAlgebraicRepresentationMultiplicity A S ρ i ≤
          matrixAlgebraicRepresentationMultiplicity A S σ i
      · rw [min_eq_left h]
        exact hρ
      · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
        exact hσ

end ThomGame.Analysis
