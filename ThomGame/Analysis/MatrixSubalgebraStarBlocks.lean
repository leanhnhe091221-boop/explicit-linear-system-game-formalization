module

public import ThomGame.Analysis.MatrixAlgebraicGramConjugation
public import ThomGame.Analysis.MatrixAlgebraicBlockExpansion

/-!
# Actual star-algebra block decomposition of a finite matrix subalgebra

The algebraic Wedderburn decomposition is corrected by the explicitly
constructed Gram-root conjugation. Expanding in matrix units proves
adjoint compatibility for every element, producing a genuine star
algebra equivalence without assuming the desired star decomposition.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)

noncomputable def matrixCorrectedBlockAlgEquiv :
    ((i : Fin S.count) → CMatrix (S.size i)) ≃ₐ[ℂ] A :=
  S.equiv.symm.trans (matrixAlgebraicGramConj A S)

theorem matrixCorrectedBlockAlgEquiv_expansion (X : (i : Fin S.count) → CMatrix (S.size i)) :
    matrixCorrectedBlockAlgEquiv A S X =
      ∑ i, ∑ a, ∑ b, X i a b • matrixAlgebraicGramConj A S (matrixAlgebraicBlockUnit A S i a b) := by
  change matrixAlgebraicGramConj A S (S.equiv.symm X) = _
  rw [matrixAlgebraicBlocks_symm_expansion]
  simp only [map_sum, map_smul]

theorem matrixCorrectedBlockAlgEquiv_star (X : (i : Fin S.count) → CMatrix (S.size i)) :
    matrixCorrectedBlockAlgEquiv A S (star X) = star (matrixCorrectedBlockAlgEquiv A S X) := by
  rw [matrixCorrectedBlockAlgEquiv_expansion, matrixCorrectedBlockAlgEquiv_expansion]
  simp only [Pi.star_apply, Matrix.star_apply, star_sum, star_smul, matrixAlgebraicGramConj_unit_star]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

noncomputable def matrixCorrectedBlockStarAlgEquiv :
    ((i : Fin S.count) → CMatrix (S.size i)) ≃⋆ₐ[ℂ] A :=
  StarAlgEquiv.ofAlgEquiv (matrixCorrectedBlockAlgEquiv A S) (matrixCorrectedBlockAlgEquiv_star A S)

theorem matrixCorrectedBlockStarAlgEquiv_single (i : Fin S.count) (a b : Fin (S.size i)) :
    matrixCorrectedBlockStarAlgEquiv A S (Pi.single i (Matrix.single a b 1)) =
      matrixAlgebraicGramConj A S (matrixAlgebraicBlockUnit A S i a b) := rfl

theorem exists_matrixSubalgebra_starAlgEquiv_pi_matrix :
    ∃ (n : Nat) (p : Fin n → Nat), (∀ i, 0 < p i) ∧
      Nonempty (A ≃⋆ₐ[ℂ] ((i : Fin n) → CMatrix (p i))) := by
  obtain ⟨P⟩ := exists_matrixSubalgebraAlgebraicBlocks A
  exact ⟨P.count, P.size, P.size_pos, ⟨(matrixCorrectedBlockStarAlgEquiv A P).symm⟩⟩

structure MatrixSubalgebraStarBlocks where
  count : Nat
  size : Fin count → Nat
  size_pos : ∀ i, 0 < size i
  equiv : A ≃⋆ₐ[ℂ] ((i : Fin count) → CMatrix (size i))

theorem exists_matrixSubalgebraStarBlocks : Nonempty (MatrixSubalgebraStarBlocks A) := by
  obtain ⟨n, p, hp, ⟨e⟩⟩ := exists_matrixSubalgebra_starAlgEquiv_pi_matrix A
  exact ⟨⟨n, p, hp, e⟩⟩

end ThomGame.Analysis
