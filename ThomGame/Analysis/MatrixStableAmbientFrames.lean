module

public import ThomGame.Analysis.MatrixStableUnitaryCompletion
public import ThomGame.Analysis.MatrixFrameCompression

/-!
# Isometric embeddings into the same stably enlarged ambient matrix space

The source frame is the unitary completion applied to the original
coordinate inclusion. The target frame is the standard coordinate
inclusion, and their overlap is precisely the original partial isometry.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

noncomputable def matrixStableSourceFrame (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) : Matrix (Fin (m + (1 - Wᴴ * W).rank)) (Fin d) ℂ :=
  Matrix.reindex finSumFinEquiv (Equiv.refl _)
    (Matrix.fromRows W (matrixProjectionFinFrame hW.one_sub)ᴴ)

noncomputable def matrixStableTargetFrame (W : Matrix (Fin m) (Fin d) ℂ) :
    Matrix (Fin (m + (1 - Wᴴ * W).rank)) (Fin m) ℂ :=
  Matrix.reindex finSumFinEquiv (Equiv.refl _)
    (Matrix.fromRows (1 : CMatrix m) (0 : Matrix (Fin (1 - Wᴴ * W).rank) (Fin m) ℂ))

noncomputable def matrixStableSourceCoordinateFrame (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) : Matrix (Fin (m + (1 - Wᴴ * W).rank)) (Fin d) ℂ :=
  Matrix.reindex (matrixStableCompletionColumnEquiv W hW) (Equiv.refl _)
    (Matrix.fromRows (1 : CMatrix d) (0 : Matrix (Fin (1 - W * Wᴴ).rank) (Fin d) ℂ))

theorem matrixStableSourceFrame_initial (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    (matrixStableSourceFrame W hW)ᴴ * matrixStableSourceFrame W hW = 1 := by
  rw [matrixStableSourceFrame, Matrix.conjTranspose_reindex, matrixReindex_mul,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.fromCols_mul_fromRows, matrixProjectionFinFrame_final, add_sub_cancel]
  rfl

theorem matrixStableTargetFrame_initial (W : Matrix (Fin m) (Fin d) ℂ) :
    (matrixStableTargetFrame W)ᴴ * matrixStableTargetFrame W = 1 := by
  rw [matrixStableTargetFrame, Matrix.conjTranspose_reindex, matrixReindex_mul,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero,
    Matrix.one_mul, add_zero]
  rfl

theorem matrixStableSourceFrame_eq_unitary (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    (matrixStableCompletionUnitary W hW).val * matrixStableSourceCoordinateFrame W hW =
      matrixStableSourceFrame W hW := by
  rw [matrixStableCompletionUnitary_apply, matrixStableSourceCoordinateFrame, matrixReindex_mul]
  simp only [matrixStableCompletionBlocks, Matrix.fromBlocks_mul_fromRows,
    Matrix.mul_one, Matrix.mul_zero, add_zero, matrixStableSourceFrame]

theorem matrixStableFrames_overlap (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    (matrixStableTargetFrame W)ᴴ * matrixStableSourceFrame W hW = W := by
  rw [matrixStableTargetFrame, matrixStableSourceFrame, Matrix.conjTranspose_reindex,
    matrixReindex_mul, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.one_mul,
    Matrix.zero_mul, add_zero]
  rfl

theorem matrixStableFrames_support_match (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    matrixStableSourceFrame W hW * (Wᴴ * W) = matrixStableTargetFrame W * W := by
  have hz : (matrixProjectionFinFrame hW.one_sub)ᴴ * (Wᴴ * W) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      matrixPartialIsometry_initial_complement_frame_zero W hW,
      Matrix.conjTranspose_zero, Matrix.zero_mul]
  change Matrix.reindex finSumFinEquiv (Equiv.refl (Fin d)) _ *
      Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) (Wᴴ * W) =
    Matrix.reindex finSumFinEquiv (Equiv.refl (Fin m)) _ *
      Matrix.reindex (Equiv.refl (Fin m)) (Equiv.refl (Fin d)) W
  rw [matrixReindex_mul, matrixReindex_mul]
  simp only [Matrix.fromRows_mul, matrixPartialIsometry_mul_initial hW, hz,
    Matrix.one_mul, Matrix.zero_mul]

theorem matrixStableFrames_adjoint_support_match (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    matrixStableSourceFrame W hW * Wᴴ = matrixStableTargetFrame W * (W * Wᴴ) := by
  have hp : (Wᴴ * W) * Wᴴ = Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose (matrixPartialIsometry_mul_initial hW)
  calc
    _ = matrixStableSourceFrame W hW * ((Wᴴ * W) * Wᴴ) := by rw [hp]
    _ = _ := by rw [← Matrix.mul_assoc, matrixStableFrames_support_match, Matrix.mul_assoc]

end ThomGame.Analysis
