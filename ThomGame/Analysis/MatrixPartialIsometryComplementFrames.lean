module

public import ThomGame.Analysis.MatrixProjectionFinFrame
public import ThomGame.Analysis.MatrixProjectionRankSums
public import ThomGame.Analysis.MatrixPartialIsometryCorners

/-!
# Actual orthonormal frames for the two missing supports

The frame sizes equal the complementary ranks. The original partial
isometry annihilates its initial complementary frame, and its adjoint
annihilates the final complementary frame.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype κ] in
theorem matrixProjectionFinFrame_left_support {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    P * matrixProjectionFinFrame hP = matrixProjectionFinFrame hP := by
  conv_lhs => lhs; rw [← matrixProjectionFinFrame_final hP]
  rw [Matrix.mul_assoc, matrixProjectionFinFrame_initial, Matrix.mul_one]

omit [Fintype κ] in
theorem matrixProjectionFinFrame_mul_zero {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (Z : Matrix κ ι ℂ) (hZ : Z * P = 0) : Z * matrixProjectionFinFrame hP = 0 := by
  calc
    _ = Z * (P * matrixProjectionFinFrame hP) := by rw [matrixProjectionFinFrame_left_support]
    _ = 0 := by rw [← Matrix.mul_assoc, hZ, Matrix.zero_mul]

variable {d m : Nat}

theorem matrixPartialIsometry_initial_complement_frame_zero (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    W * matrixProjectionFinFrame hW.one_sub = 0 := by
  apply matrixProjectionFinFrame_mul_zero
  rw [Matrix.mul_sub, Matrix.mul_one, matrixPartialIsometry_mul_initial hW, sub_self]

theorem matrixPartialIsometry_final_complement_frame_zero (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    Wᴴ * matrixProjectionFinFrame (matrixPartialIsometry_final_projection hW).one_sub = 0 := by
  apply matrixProjectionFinFrame_mul_zero
  have hs : Wᴴ * (W * Wᴴ) = Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose (matrixPartialIsometry_mul_initial hW)
  rw [Matrix.mul_sub, Matrix.mul_one, hs, sub_self]

theorem matrixPartialIsometry_stable_dimension_eq (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) :
    d + (1 - W * Wᴴ).rank = m + (1 - Wᴴ * W).rank := by
  have hi := matrixProjection_rank_one_sub_add hW
  have hf := matrixProjection_rank_one_sub_add (matrixPartialIsometry_final_projection hW)
  rw [Matrix.rank_conjTranspose_mul_self, Fintype.card_fin] at hi
  rw [Matrix.rank_self_mul_conjTranspose, Fintype.card_fin] at hf
  omega

end ThomGame.Analysis
