module

public import ThomGame.Analysis.MatrixStarBlockFrames

/-!
# An actual ambient unitary from the block frames

Columns are indexed by a block, a simple-module coordinate, and a
multiplicity coordinate. The already proved dimension identity gives
exactly m columns. Their sum of range projections is the identity, so
reindexing the columns gives an actual m by m unitary matrix.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)

abbrev MatrixStarBlockColumnIndex :=
  Σ i : Fin P.count, Fin (P.size i) × Fin (matrixStarRepresentationMultiplicity A P ρ i)

noncomputable def matrixStarRepresentationFrame : Matrix (Fin m) (MatrixStarBlockColumnIndex A P ρ) ℂ :=
  fun r c => matrixStarBlockFrame A P ρ c.1 c.2.1 r c.2.2

theorem matrixStarRepresentationFrame_final :
    matrixStarRepresentationFrame A P ρ * (matrixStarRepresentationFrame A P ρ)ᴴ = 1 := by
  ext r s
  have he := congrArg (fun X : CMatrix m => X r s) (matrixStarBlockFrames_final_sum A P ρ)
  simpa only [matrixStarRepresentationFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sigma, Fintype.sum_prod_type, Matrix.sum_apply] using he

theorem matrixStarBlockColumnIndex_card : Fintype.card (MatrixStarBlockColumnIndex A P ρ) = m := by
  simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] using
    (matrixStarRepresentation_dimension A P ρ).symm

noncomputable def matrixStarBlockColumnEquiv : MatrixStarBlockColumnIndex A P ρ ≃ Fin m :=
  Fintype.equivFinOfCardEq (matrixStarBlockColumnIndex_card A P ρ)

noncomputable def matrixStarRepresentationBasis : CMatrix m :=
  Matrix.reindex (Equiv.refl (Fin m)) (matrixStarBlockColumnEquiv A P ρ) (matrixStarRepresentationFrame A P ρ)

theorem matrixStarRepresentationBasis_final :
    matrixStarRepresentationBasis A P ρ * (matrixStarRepresentationBasis A P ρ)ᴴ = 1 := by
  rw [matrixStarRepresentationBasis, Matrix.conjTranspose_reindex, matrixReindex_mul,
    matrixStarRepresentationFrame_final]
  rfl

theorem matrixStarRepresentationBasis_initial :
    (matrixStarRepresentationBasis A P ρ)ᴴ * matrixStarRepresentationBasis A P ρ = 1 :=
  mul_eq_one_comm.mp (matrixStarRepresentationBasis_final A P ρ)

noncomputable def matrixStarRepresentationUnitary : UnitaryMatrix m :=
  ⟨matrixStarRepresentationBasis A P ρ,
    matrixStarRepresentationBasis_initial A P ρ, matrixStarRepresentationBasis_final A P ρ⟩

theorem matrixStarRepresentationBasis_column (r : Fin m) (c : MatrixStarBlockColumnIndex A P ρ) :
    matrixStarRepresentationBasis A P ρ r (matrixStarBlockColumnEquiv A P ρ c) =
      matrixStarBlockFrame A P ρ c.1 c.2.1 r c.2.2 := by
  change matrixStarRepresentationFrame A P ρ r
    ((matrixStarBlockColumnEquiv A P ρ).symm (matrixStarBlockColumnEquiv A P ρ c)) = _
  rw [Equiv.symm_apply_apply]
  rfl

end ThomGame.Analysis
