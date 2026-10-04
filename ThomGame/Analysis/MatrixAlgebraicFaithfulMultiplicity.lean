module

public import ThomGame.Analysis.MatrixAlgebraicRepresentationMultiplicity

/-!
# Positive multiplicities of faithful representations

Faithfulness makes every diagonal block idempotent nonzero. In particular,
the original matrix inclusion has positive multiplicities and the sum
of the sizes of the simple blocks is at most the original dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

theorem matrixAlgebraicRepresentationMultiplicity_pos (ρ : A →ₐ[ℂ] CMatrix m)
    (hρ : Function.Injective ρ) (i : Fin S.count) :
    0 < matrixAlgebraicRepresentationMultiplicity A S ρ i := by
  apply matrixIdempotent_rank_pos (matrixAlgebraicRepresentation_diagonal_idempotent A S ρ i _)
  intro h
  have he : matrixAlgebraicBlockUnit A S i ⟨0, S.size_pos i⟩ ⟨0, S.size_pos i⟩ = 0 :=
    hρ (by simpa only [map_zero] using h)
  exact matrixAlgebraicBlockUnit_ne_zero A S i _ _ he

theorem matrixAlgebraicOriginalMultiplicity_pos (i : Fin S.count) :
    0 < matrixAlgebraicRepresentationMultiplicity A S A.subtype.toAlgHom i :=
  matrixAlgebraicRepresentationMultiplicity_pos A S A.subtype.toAlgHom Subtype.val_injective i

theorem matrixAlgebraicBlockSizes_sum_le : ∑ i, S.size i ≤ d := by
  calc
    ∑ i, S.size i ≤ ∑ i, S.size i * matrixAlgebraicRepresentationMultiplicity A S A.subtype.toAlgHom i := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_mul_of_pos_right _ (matrixAlgebraicOriginalMultiplicity_pos A S i)
    _ = d := (matrixAlgebraicRepresentation_dimension A S A.subtype.toAlgHom).symm

theorem matrixAlgebraicBlockCount_le : S.count ≤ d := by
  calc
    S.count = ∑ _ : Fin S.count, 1 := by simp
    _ ≤ ∑ i, S.size i := Finset.sum_le_sum (fun i _ => S.size_pos i)
    _ ≤ d := matrixAlgebraicBlockSizes_sum_le A S

end ThomGame.Analysis
