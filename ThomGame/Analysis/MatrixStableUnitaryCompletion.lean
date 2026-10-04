module

public import ThomGame.Analysis.MatrixPartialIsometryComplementFrames
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Unitary completion on exactly the two complementary spaces

The block matrix [W Fq; Fp* 0] is a two-sided isometry. Its row and
column dimensions coincide, so reindexing gives an actual unitary matrix.
No extra full-dimensional summand is introduced.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

noncomputable def matrixStableCompletionBlocks (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    Matrix (Fin m ⊕ Fin (1 - Wᴴ * W).rank) (Fin d ⊕ Fin (1 - W * Wᴴ).rank) ℂ :=
  Matrix.fromBlocks W (matrixProjectionFinFrame (matrixPartialIsometry_final_projection hW).one_sub)
    (matrixProjectionFinFrame hW.one_sub)ᴴ 0

theorem matrixStableCompletionBlocks_initial (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    (matrixStableCompletionBlocks W hW)ᴴ * matrixStableCompletionBlocks W hW = 1 := by
  have hz := matrixPartialIsometry_final_complement_frame_zero W hW
  have hzs := congrArg Matrix.conjTranspose hz
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] at hzs
  simp only [matrixStableCompletionBlocks, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, hz, hzs,
    matrixProjectionFinFrame_initial, matrixProjectionFinFrame_final, add_sub_cancel,
    Matrix.fromBlocks_one]

theorem matrixStableCompletionBlocks_final (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    matrixStableCompletionBlocks W hW * (matrixStableCompletionBlocks W hW)ᴴ = 1 := by
  have hz := matrixPartialIsometry_initial_complement_frame_zero W hW
  have hzs := congrArg Matrix.conjTranspose hz
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero] at hzs
  simp only [matrixStableCompletionBlocks, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, hz, hzs,
    matrixProjectionFinFrame_initial, matrixProjectionFinFrame_final, add_sub_cancel,
    Matrix.fromBlocks_one]

noncomputable def matrixStableCompletionColumnEquiv (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    (Fin d ⊕ Fin (1 - W * Wᴴ).rank) ≃ Fin (m + (1 - Wᴴ * W).rank) :=
  finSumFinEquiv.trans (finCongr (matrixPartialIsometry_stable_dimension_eq W hW))

noncomputable def matrixStableCompletionUnitary (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) : UnitaryMatrix (m + (1 - Wᴴ * W).rank) :=
  ⟨Matrix.reindex finSumFinEquiv (matrixStableCompletionColumnEquiv W hW)
    (matrixStableCompletionBlocks W hW), by
    constructor
    · change (Matrix.reindex _ _ _)ᴴ * Matrix.reindex _ _ _ = 1
      rw [Matrix.conjTranspose_reindex, matrixReindex_mul, matrixStableCompletionBlocks_initial]
      exact Matrix.submatrix_one _ (Equiv.injective _)
    · change Matrix.reindex _ _ _ * (Matrix.reindex _ _ _)ᴴ = 1
      rw [Matrix.conjTranspose_reindex, matrixReindex_mul, matrixStableCompletionBlocks_final]
      exact Matrix.submatrix_one _ (Equiv.injective _)⟩

theorem matrixStableCompletionUnitary_apply (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    (matrixStableCompletionUnitary W hW).val =
      Matrix.reindex finSumFinEquiv (matrixStableCompletionColumnEquiv W hW)
        (matrixStableCompletionBlocks W hW) := rfl

end ThomGame.Analysis
