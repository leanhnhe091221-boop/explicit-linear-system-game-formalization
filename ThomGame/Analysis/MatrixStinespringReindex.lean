module

public import ThomGame.Analysis.MatrixRelativeStinespring
public import ThomGame.Analysis.MatrixBlockReindex

/-!
# Fin-indexed relative Stinespring data

Only the dilation coordinates are reindexed. Compression, exact
intertwining and the original normalization remain unchanged.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ ν ι' κ' ν' : Type*}
  [Fintype ι] [Fintype κ] [Fintype ν] [Fintype ι'] [Fintype κ'] [Fintype ν']

omit [Fintype ι] [Fintype ν] [Fintype ι'] [Fintype ν'] in
theorem matrixReindex_mul (e : ι ≃ ι') (f : κ ≃ κ') (g : ν ≃ ν')
    (X : Matrix ι κ ℂ) (Y : Matrix κ ν ℂ) :
    Matrix.reindex e f X * Matrix.reindex f g Y = Matrix.reindex e g (X * Y) :=
  Matrix.reindexLinearEquiv_mul ℂ ℂ e f g X Y

noncomputable def matrixStarReindex [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι' ι' ℂ where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e
  map_smul' _ _ := rfl
  map_star' X := (Matrix.conjTranspose_reindex e e X).symm

variable {d : Nat}

theorem matrixDiagonalRepresentation_injective (κ : Type*) [Fintype κ] [DecidableEq κ] [Nonempty κ] :
    Function.Injective (matrixDiagonalRepresentation κ d) := by
  intro X Y h
  obtain ⟨k⟩ := ‹Nonempty κ›
  ext i j
  have he := congrArg (fun Z : Matrix (Fin d × κ) (Fin d × κ) ℂ => Z (i, k) (j, k)) h
  simpa only [matrixDiagonalRepresentation_apply, ite_true] using he

theorem exists_matrixRelativeStinespring_fin [NeZero d] (A : StarSubalgebra ℂ (CMatrix d)) :
    ∃ ρ σ : CMatrix d →⋆ₐ[ℂ] CMatrix (d * (d * d)),
      Function.Injective ρ ∧ (∀ X Y, ρ X * σ Y = σ Y * ρ X) ∧
      ∃ V : Matrix (Fin (d * (d * d))) (Fin d) ℂ,
        Vᴴ * V = 1 ∧
        (∀ X, Vᴴ * ρ X * V = matrixTraceProjection A X) ∧
        (∀ X ∈ A, ρ X * V = V * X) ∧
        ∀ Y ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)), σ Y * V = V * Y := by
  obtain ⟨W, hW, hE, hA, hC, _⟩ := exists_matrixRelativeStinespring A
  let e : (Fin d × (Fin d × Fin d)) ≃ Fin (d * (d * d)) :=
    (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv
  let T := matrixStarReindex e
  let ρ := T.toStarAlgHom.comp (matrixDiagonalRepresentation (Fin d × Fin d) d)
  let σ := T.toStarAlgHom.comp (matrixChoiRightRepresentation d)
  let V := Matrix.reindex e (Equiv.refl (Fin d)) W
  have hρ : Function.Injective ρ := T.injective.comp (matrixDiagonalRepresentation_injective (Fin d × Fin d))
  have hcomm (X Y : CMatrix d) : ρ X * σ Y = σ Y * ρ X := by
    change T (matrixDiagonalRepresentation (Fin d × Fin d) d X) * T (matrixChoiRightRepresentation d Y) =
      T (matrixChoiRightRepresentation d Y) * T (matrixDiagonalRepresentation (Fin d × Fin d) d X)
    rw [← map_mul, ← map_mul, matrixChoi_representations_commute]
  have hVi : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_reindex, matrixReindex_mul, hW]
    rfl
  have hVE (X : CMatrix d) : Vᴴ * ρ X * V = matrixTraceProjection A X := by
    change (Matrix.reindex e (Equiv.refl (Fin d)) W)ᴴ *
      Matrix.reindex e e (matrixDiagonalRepresentation (Fin d × Fin d) d X) *
        Matrix.reindex e (Equiv.refl (Fin d)) W = _
    rw [Matrix.conjTranspose_reindex, matrixReindex_mul, matrixReindex_mul, hE]
    rfl
  refine ⟨ρ, σ, hρ, hcomm, V, hVi, hVE, ?_, ?_⟩
  · intro X hX
    change Matrix.reindex e e (matrixDiagonalRepresentation (Fin d × Fin d) d X) *
      Matrix.reindex e (Equiv.refl (Fin d)) W =
        Matrix.reindex e (Equiv.refl (Fin d)) W * Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) X
    rw [matrixReindex_mul, matrixReindex_mul, hA X hX]
  · intro Y hY
    change Matrix.reindex e e (matrixChoiRightRepresentation d Y) *
      Matrix.reindex e (Equiv.refl (Fin d)) W =
        Matrix.reindex e (Equiv.refl (Fin d)) W * Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) Y
    rw [matrixReindex_mul, matrixReindex_mul, hC Y hY]

end ThomGame.Analysis
