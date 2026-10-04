module

public import ThomGame.Analysis.MatrixSubalgebraCorners
public import ThomGame.Analysis.MatrixProjectionIsometry

/-!
# Algebraic transport on the actual supports of a partial isometry
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixPartialIsometry_sandwich_support (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (X : CMatrix d) :
    (W * Wᴴ) * (W * X * Wᴴ) = W * X * Wᴴ ∧
      (W * X * Wᴴ) * (W * Wᴴ) = W * X * Wᴴ := by
  have hleft : (W * Wᴴ) * W = W := by
    rw [Matrix.mul_assoc]
    exact matrixPartialIsometry_mul_initial hW
  have hright : Wᴴ * (W * Wᴴ) = Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (matrixPartialIsometry_final_projection hW).isSelfAdjoint.isHermitian.eq] using
      congrArg Matrix.conjTranspose hleft
  constructor
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hleft]
  · rw [Matrix.mul_assoc (W * X), hright]

theorem matrixSandwich_inverse_of_support (W : Matrix (Fin m) (Fin d) ℂ) (X : CMatrix d)
    (hL : (Wᴴ * W) * X = X) (hR : X * (Wᴴ * W) = X) :
    Wᴴ * (W * X * Wᴴ) * W = X := by
  calc
    _ = ((Wᴴ * W) * X) * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hL, hR]

theorem matrixSandwich_mul_of_support (W : Matrix (Fin m) (Fin d) ℂ) (X Y : CMatrix d)
    (hY : (Wᴴ * W) * Y = Y) :
    (W * X * Wᴴ) * (W * Y * Wᴴ) = W * (X * Y) * Wᴴ := by
  calc
    _ = W * X * ((Wᴴ * W) * Y) * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hY]; simp only [Matrix.mul_assoc]

theorem matrixSandwich_star (W : Matrix (Fin m) (Fin d) ℂ) (X : CMatrix d) :
    (W * X * Wᴴ)ᴴ = W * Xᴴ * Wᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end ThomGame.Analysis
