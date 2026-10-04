module

public import ThomGame.Analysis.MatrixAlgebraicRepresentationMultiplicity
public import ThomGame.Analysis.MatrixAlgebraicBlockExpansion

/-!
# Actual representation traces in block coordinates

The trace weights are the ranks of the first diagonal matrix units.
Trace cyclicity kills the off-diagonal units, so no block realization
or prescribed multiplicity formula is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A) (ρ : A →ₐ[ℂ] CMatrix m)

theorem matrixAlgebraicRepresentation_unit_trace (i : Fin S.count) (a b : Fin (S.size i)) :
    (ρ (matrixAlgebraicBlockUnit A S i a b)).trace =
      if a = b then (matrixAlgebraicRepresentationMultiplicity A S ρ i : ℂ) else 0 := by
  classical
  by_cases h : a = b
  · subst b
    rw [ite_eq_left rfl, matrixIdempotent_trace_eq_rank
      (matrixAlgebraicRepresentation_diagonal_idempotent A S ρ i a),
      matrixAlgebraicRepresentation_diagonal_rank]
  · rw [ite_eq_right h]
    have he := Matrix.trace_mul_comm
      (ρ (matrixAlgebraicBlockUnit A S i a a)) (ρ (matrixAlgebraicBlockUnit A S i a b))
    simpa only [← map_mul, matrixAlgebraicBlockUnit_mul_same,
      matrixAlgebraicBlockUnit_mul_ne A S i a b a a (Ne.symm h), map_zero, Matrix.trace_zero] using he

theorem matrixAlgebraicRepresentation_trace (X : A) :
    (ρ X).trace = ∑ i, (matrixAlgebraicRepresentationMultiplicity A S ρ i : ℂ) * (S.equiv X i).trace := by
  classical
  have he : X = ∑ i, ∑ a, ∑ b, S.equiv X i a b • matrixAlgebraicBlockUnit A S i a b := by
    rw [← matrixAlgebraicBlocks_symm_expansion, S.equiv.symm_apply_apply]
  conv_lhs => rw [he]
  simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul,
    matrixAlgebraicRepresentation_unit_trace, smul_eq_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, mul_comm]

theorem matrixAlgebraicRepresentation_idempotent_rank (X : A) (hX : IsIdempotentElem X) :
    (ρ X).rank = ∑ i, matrixAlgebraicRepresentationMultiplicity A S ρ i * (S.equiv X i).rank := by
  have hρ : IsIdempotentElem (ρ X) := by
    change ρ X * ρ X = ρ X
    rw [← map_mul, hX.eq]
  have hi (i : Fin S.count) : IsIdempotentElem (S.equiv X i) := by
    change S.equiv X i * S.equiv X i = S.equiv X i
    have he := congrArg (fun Y : A => S.equiv Y i) hX.eq
    simpa only [map_mul, Pi.mul_apply] using he
  have he := matrixAlgebraicRepresentation_trace A S ρ X
  simp only [matrixIdempotent_trace_eq_rank hρ, matrixIdempotent_trace_eq_rank (hi _)] at he
  exact_mod_cast he

theorem matrixAlgebraicRepresentation_block_cut_rank (X : A) (hX : IsIdempotentElem X)
    (j : Fin S.count) :
    (ρ (matrixAlgebraicBlockSupport A S j * X)).rank =
      matrixAlgebraicRepresentationMultiplicity A S ρ j * (S.equiv X j).rank := by
  classical
  have hY : IsIdempotentElem (matrixAlgebraicBlockSupport A S j * X) :=
    IsIdempotentElem.mul_of_commute (matrixAlgebraicBlockSupport_commutes A S j X)
      (matrixAlgebraicBlockSupport_mul_self A S j) hX
  rw [matrixAlgebraicRepresentation_idempotent_rank A S ρ _ hY]
  simp only [map_mul, Pi.mul_apply, matrixAlgebraicBlockSupport_equiv, ite_mul,
    Matrix.one_mul, Matrix.zero_mul]
  simp only [apply_ite Matrix.rank, Matrix.rank_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end ThomGame.Analysis
