module

public import ThomGame.Analysis.MatrixPolarDilation
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The two supports of a rectangular polar factor

Both supports, both absolute-value factorizations, and their ranks are
identified with actual matrices. A lower bound on the initial support
transfers to the final support by conjugating with the polar factor.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrixRectPolar_final (X : Matrix ι κ ℂ) :
    matrixRectPolar X * (matrixRectPolar X)ᴴ = matrixRealSupport (matrixRectAbs Xᴴ) := by
  have he := matrixRectPolar_initial Xᴴ
  simpa only [matrixRectPolar_conjTranspose, Matrix.conjTranspose_conjTranspose] using he

theorem matrixRectPolar_abs_conjugate (X : Matrix ι κ ℂ) :
    matrixRectPolar X * matrixRectAbs X * (matrixRectPolar X)ᴴ = matrixRectAbs Xᴴ := by
  have he := congrArg Matrix.conjTranspose (matrixRectPolar_mul_abs Xᴴ)
  simp only [Matrix.conjTranspose_mul, (matrixRectAbs_isHermitian Xᴴ).eq,
    matrixRectPolar_conjTranspose, Matrix.conjTranspose_conjTranspose] at he
  calc
    _ = X * (matrixRectPolar X)ᴴ := by rw [matrixRectPolar_mul_abs]
    _ = (matrixRectAbs Xᴴ * matrixRectPolar X) * (matrixRectPolar X)ᴴ :=
      congrArg (fun Z : Matrix ι κ ℂ => Z * (matrixRectPolar X)ᴴ) he.symm
    _ = _ := by rw [Matrix.mul_assoc, matrixRectPolar_final,
      mul_matrixRealSupport (matrixRectAbs_isHermitian Xᴴ)]

theorem matrixRectPolar_support_conjugate (X : Matrix ι κ ℂ) :
    matrixRectPolar X * matrixRealSupport (matrixRectAbs X) * (matrixRectPolar X)ᴴ =
      matrixRealSupport (matrixRectAbs Xᴴ) := by
  rw [matrixRectPolar_mul_support, matrixRectPolar_final]

omit [DecidableEq ι] in
theorem matrixRectPolar_rank (X : Matrix ι κ ℂ) : (matrixRectPolar X).rank = X.rank := by
  apply le_antisymm
  · exact Matrix.rank_mul_le_left X _
  · calc
      X.rank = (matrixRectPolar X * matrixRectAbs X).rank := by rw [matrixRectPolar_mul_abs]
      _ ≤ (matrixRectPolar X).rank := Matrix.rank_mul_le_left _ _

omit [DecidableEq ι] in
theorem matrixRectPolar_initial_rank (X : Matrix ι κ ℂ) :
    (matrixRealSupport (matrixRectAbs X)).rank = X.rank := by
  rw [← matrixRectPolar_initial, Matrix.rank_conjTranspose_mul_self, matrixRectPolar_rank]

omit [DecidableEq κ] in
theorem matrixRectPolar_final_rank (X : Matrix ι κ ℂ) :
    (matrixRealSupport (matrixRectAbs Xᴴ)).rank = X.rank := by
  rw [matrixRectPolar_initial_rank, Matrix.rank_conjTranspose]

theorem matrixRectAbs_support_lower_adjoint (X : Matrix ι κ ℂ) (b : ℝ)
    (hX : b • matrixRealSupport (matrixRectAbs X) ≤ matrixRectAbs X) :
    b • matrixRealSupport (matrixRectAbs Xᴴ) ≤ matrixRectAbs Xᴴ := by
  have he := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hX)).mul_mul_conjTranspose_same
    (matrixRectPolar X)
  apply sub_nonneg.mp
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    matrixRectPolar_abs_conjugate, matrixRectPolar_support_conjugate] using he.nonneg

end ThomGame.Analysis
