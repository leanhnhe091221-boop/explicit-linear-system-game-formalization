module

public import ThomGame.Analysis.MatrixStarRepresentationBasis
public import ThomGame.Analysis.MatrixStarBlockAction
public import ThomGame.Analysis.MatrixStandardBlockRepresentation

/-!
# Actual unitary block realization of any finite-dimensional star representation

The constructed ambient unitary identifies the representation with
the standard direct sum of X_i tensor identity_q_i. The simple factors,
multiplicities, column reindexing and unitary are actual objects.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

noncomputable def matrixStarRepresentationStandard : A →⋆ₐ[ℂ] CMatrix m :=
  (matrixStarReindex (matrixStarBlockColumnEquiv A P ρ)).toStarAlgHom.comp
    ((matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ)).comp P.equiv.toStarAlgHom)

theorem matrixStarRepresentationStandard_apply (X : A) :
    matrixStarRepresentationStandard A P ρ X =
      Matrix.reindex (matrixStarBlockColumnEquiv A P ρ) (matrixStarBlockColumnEquiv A P ρ)
        (matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) (P.equiv X)) := rfl

theorem matrixStarRepresentationFrame_intertwines (X : A) :
    ρ X * matrixStarRepresentationFrame A P ρ = matrixStarRepresentationFrame A P ρ *
      matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) (P.equiv X) := by
  ext r ⟨i, a, k⟩
  rw [matrix_mul_standardBlock_column]
  have he := congrArg (fun F : Matrix (Fin m) (Fin (matrixStarRepresentationMultiplicity A P ρ i)) ℂ => F r k)
    (matrixStarBlockFrame_action A P ρ X i a)
  simpa only [matrixStarRepresentationFrame, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_comm] using he

theorem matrixStarRepresentationBasis_intertwines (X : A) :
    ρ X * matrixStarRepresentationBasis A P ρ =
      matrixStarRepresentationBasis A P ρ * matrixStarRepresentationStandard A P ρ X := by
  change Matrix.reindex (Equiv.refl (Fin m)) (Equiv.refl (Fin m)) (ρ X) *
      Matrix.reindex (Equiv.refl (Fin m)) (matrixStarBlockColumnEquiv A P ρ) (matrixStarRepresentationFrame A P ρ) =
    Matrix.reindex (Equiv.refl (Fin m)) (matrixStarBlockColumnEquiv A P ρ) (matrixStarRepresentationFrame A P ρ) *
      Matrix.reindex (matrixStarBlockColumnEquiv A P ρ) (matrixStarBlockColumnEquiv A P ρ)
        (matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) (P.equiv X))
  rw [matrixReindex_mul, matrixReindex_mul, matrixStarRepresentationFrame_intertwines]

theorem matrixStarRepresentationBasis_conjugates (X : A) :
    (matrixStarRepresentationBasis A P ρ)ᴴ * ρ X * matrixStarRepresentationBasis A P ρ =
      matrixStarRepresentationStandard A P ρ X := by
  rw [Matrix.mul_assoc, matrixStarRepresentationBasis_intertwines, ← Matrix.mul_assoc,
    matrixStarRepresentationBasis_initial, Matrix.one_mul]

theorem matrixStarRepresentationBasis_recovers (X : A) :
    ρ X = matrixStarRepresentationBasis A P ρ * matrixStarRepresentationStandard A P ρ X *
      (matrixStarRepresentationBasis A P ρ)ᴴ := by
  rw [← matrixStarRepresentationBasis_intertwines, Matrix.mul_assoc,
    matrixStarRepresentationBasis_final, Matrix.mul_one]

theorem exists_matrixStarRepresentation_unitary_blocks (ρ : A →⋆ₐ[ℂ] CMatrix m) :
    ∃ (P : MatrixSubalgebraStarBlocks A)
      (e : MatrixStarBlockColumnIndex A P ρ ≃ Fin m) (U : UnitaryMatrix m),
      m = ∑ i, P.size i * matrixStarRepresentationMultiplicity A P ρ i ∧
      ∀ X : A, U.valᴴ * ρ X * U.val = Matrix.reindex e e
        (matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P ρ) (P.equiv X)) := by
  obtain ⟨Q⟩ := exists_matrixSubalgebraStarBlocks A
  exact ⟨Q, matrixStarBlockColumnEquiv A Q ρ, matrixStarRepresentationUnitary A Q ρ,
    matrixStarRepresentation_dimension A Q ρ, matrixStarRepresentationBasis_conjugates A Q ρ⟩

theorem exists_matrixSubalgebra_unitary_blocks :
    ∃ (P : MatrixSubalgebraStarBlocks A)
      (e : MatrixStarBlockColumnIndex A P A.subtype ≃ Fin d) (U : UnitaryMatrix d),
      (∀ i, 0 < matrixStarRepresentationMultiplicity A P A.subtype i) ∧
      d = ∑ i, P.size i * matrixStarRepresentationMultiplicity A P A.subtype i ∧
      ∀ X : A, U.valᴴ * (X : CMatrix d) * U.val = Matrix.reindex e e
        (matrixStandardBlockRepresentation P.size (matrixStarRepresentationMultiplicity A P A.subtype) (P.equiv X)) := by
  obtain ⟨Q, e, U, hd, he⟩ := exists_matrixStarRepresentation_unitary_blocks A A.subtype
  exact ⟨Q, e, U, matrixStarRepresentationMultiplicity_pos A Q A.subtype Subtype.val_injective, hd, he⟩

end ThomGame.Analysis
