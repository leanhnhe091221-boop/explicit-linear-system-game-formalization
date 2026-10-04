module

public import ThomGame.Analysis.MatrixPolarSupport

/-!
# Exact star intertwining is preserved by rectangular polar decomposition

Both the original and adjoint intertwining relations are used to
commute the source action with X*X and its functional calculus.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem matrixRectPolar_exact_intertwining (X : Matrix ι κ ℂ)
    (A : Matrix κ κ ℂ) (B : Matrix ι ι ℂ)
    (h : X * A = B * X) (hs : X * Aᴴ = Bᴴ * X) :
    matrixRectPolar X * A = B * matrixRectPolar X := by
  have ha := congrArg Matrix.conjTranspose hs
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at ha
  have hg : (Xᴴ * X) * A = A * (Xᴴ * X) := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← ha, Matrix.mul_assoc]
  have habs : matrixRectAbs X * A = A * matrixRectAbs X := by
    rw [matrixRectAbs, matrixSqrt_eq_real_cfc (Matrix.posSemidef_conjTranspose_mul_self X).nonneg]
    exact matrix_cfc_intertwine (Matrix.isHermitian_conjTranspose_mul_self X)
      (Matrix.isHermitian_conjTranspose_mul_self X) Real.sqrt A hg
  have hi := matrix_cfc_intertwine (matrixRectAbs_isHermitian X) (matrixRectAbs_isHermitian X)
    (fun t : ℝ => t⁻¹) A habs
  change matrixRealInv (matrixRectAbs X) * A = A * matrixRealInv (matrixRectAbs X) at hi
  rw [matrixRectPolar, Matrix.mul_assoc, hi, ← Matrix.mul_assoc, h, Matrix.mul_assoc]

end ThomGame.Analysis
