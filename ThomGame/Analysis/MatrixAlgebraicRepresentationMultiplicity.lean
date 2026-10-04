module

public import ThomGame.Analysis.MatrixAlgebraicBlockUnits
public import ThomGame.Analysis.MatrixIdempotentRanks

/-!
# Multiplicities from the ranks of actual representation matrices

For every unital representation of a constructed matrix subalgebra,
the multiplicity of a block is the rank of the image of its first
diagonal matrix unit. Trace cyclicity proves independence of the chosen
diagonal unit. The dimensions and the ranks of central supports are
then exact weighted sums, with no assumed block realization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A) (ρ : A →ₐ[ℂ] CMatrix m)

noncomputable def matrixAlgebraicRepresentationMultiplicity (i : Fin S.count) : Nat :=
  (ρ (matrixAlgebraicBlockUnit A S i ⟨0, S.size_pos i⟩ ⟨0, S.size_pos i⟩)).rank

theorem matrixAlgebraicRepresentation_diagonal_idempotent (i : Fin S.count) (a : Fin (S.size i)) :
    IsIdempotentElem (ρ (matrixAlgebraicBlockUnit A S i a a)) := by
  change ρ _ * ρ _ = ρ _
  rw [← map_mul, matrixAlgebraicBlockUnit_mul_same]

theorem matrixAlgebraicRepresentation_support_idempotent (i : Fin S.count) :
    IsIdempotentElem (ρ (matrixAlgebraicBlockSupport A S i)) := by
  change ρ _ * ρ _ = ρ _
  rw [← map_mul, matrixAlgebraicBlockSupport_mul_self]

theorem matrixAlgebraicRepresentation_diagonal_rank_eq (i : Fin S.count) (a b : Fin (S.size i)) :
    (ρ (matrixAlgebraicBlockUnit A S i a a)).rank =
      (ρ (matrixAlgebraicBlockUnit A S i b b)).rank := by
  apply matrixIdempotent_rank_eq_of_trace_eq
    (matrixAlgebraicRepresentation_diagonal_idempotent A S ρ i a)
    (matrixAlgebraicRepresentation_diagonal_idempotent A S ρ i b)
  have he := Matrix.trace_mul_comm
    (ρ (matrixAlgebraicBlockUnit A S i a b)) (ρ (matrixAlgebraicBlockUnit A S i b a))
  simpa only [← map_mul, matrixAlgebraicBlockUnit_mul_same] using he

theorem matrixAlgebraicRepresentation_diagonal_rank (i : Fin S.count) (a : Fin (S.size i)) :
    (ρ (matrixAlgebraicBlockUnit A S i a a)).rank =
      matrixAlgebraicRepresentationMultiplicity A S ρ i :=
  matrixAlgebraicRepresentation_diagonal_rank_eq A S ρ i a ⟨0, S.size_pos i⟩

theorem matrixAlgebraicRepresentation_support_rank (i : Fin S.count) :
    (ρ (matrixAlgebraicBlockSupport A S i)).rank =
      S.size i * matrixAlgebraicRepresentationMultiplicity A S ρ i := by
  have hs : ∑ a, ρ (matrixAlgebraicBlockUnit A S i a a) =
      ρ (matrixAlgebraicBlockSupport A S i) := by
    rw [← map_sum, matrixAlgebraicBlockUnit_diagonal_sum]
  have hsum : IsIdempotentElem (∑ a, ρ (matrixAlgebraicBlockUnit A S i a a)) := by
    rw [hs]
    exact matrixAlgebraicRepresentation_support_idempotent A S ρ i
  have he := matrixIdempotent_sum_rank (fun a => ρ (matrixAlgebraicBlockUnit A S i a a))
    (matrixAlgebraicRepresentation_diagonal_idempotent A S ρ i) hsum
  simpa only [hs, matrixAlgebraicRepresentation_diagonal_rank, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] using he

theorem matrixAlgebraicRepresentation_dimension :
    m = ∑ i, S.size i * matrixAlgebraicRepresentationMultiplicity A S ρ i := by
  have hs : ∑ i, ρ (matrixAlgebraicBlockSupport A S i) = 1 := by
    rw [← map_sum, matrixAlgebraicBlockSupport_sum, map_one]
  have hsum : IsIdempotentElem (∑ i, ρ (matrixAlgebraicBlockSupport A S i)) := by
    rw [hs]
    exact IsIdempotentElem.one
  have he := matrixIdempotent_sum_rank (fun i => ρ (matrixAlgebraicBlockSupport A S i))
    (matrixAlgebraicRepresentation_support_idempotent A S ρ) hsum
  simpa only [hs, Matrix.rank_one, Fintype.card_fin, matrixAlgebraicRepresentation_support_rank] using he

end ThomGame.Analysis
