module

public import ThomGame.Analysis.MatrixProjectionFrames
public import ThomGame.Analysis.MatrixStinespringReindex

/-!
# Fin-indexed orthonormal frames for actual projection ranges

The column count is exactly the rank of the projection, including rank zero.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def matrixProjectionFinFrame {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    Matrix ι (Fin P.rank) ℂ := by
  classical
  exact Matrix.reindex (Equiv.refl ι)
    (Fintype.equivFinOfCardEq hP.isSelfAdjoint.isHermitian.rank_eq_card_non_zero_eigs.symm)
    (matrixProjectionFrame hP)

theorem matrixProjectionFinFrame_initial {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    (matrixProjectionFinFrame hP)ᴴ * matrixProjectionFinFrame hP = 1 := by
  classical
  rw [matrixProjectionFinFrame, Matrix.conjTranspose_reindex, matrixReindex_mul,
    matrixProjectionFrame_initial]
  exact Matrix.submatrix_one _ (Equiv.injective _)

theorem matrixProjectionFinFrame_final {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    matrixProjectionFinFrame hP * (matrixProjectionFinFrame hP)ᴴ = P := by
  classical
  rw [matrixProjectionFinFrame, Matrix.conjTranspose_reindex, matrixReindex_mul,
    matrixProjectionFrame_final]
  rfl

end ThomGame.Analysis
