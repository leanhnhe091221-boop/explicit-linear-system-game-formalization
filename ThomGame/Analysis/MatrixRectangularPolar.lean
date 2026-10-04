module

public import ThomGame.Analysis.MatrixSupportInverse

/-!
# Actual rectangular polar decomposition

The polar factor is X times the spectral generalized inverse of |X|.
Its initial projection is the support of |X| and its final Gram matrix
is a projection. All statements allow a nontrivial kernel.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

noncomputable def matrixRectPolar (X : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  X * matrixRealInv (matrixRectAbs X)

theorem matrixRectAbs_isHermitian (X : Matrix ι κ ℂ) :
    Matrix.IsHermitian (matrixRectAbs X) := (matrixRectAbs_nonneg X).isSelfAdjoint

theorem matrix_mul_absSupport (X : Matrix ι κ ℂ) :
    X * matrixRealSupport (matrixRectAbs X) = X := by
  let P := matrixRealSupport (matrixRectAbs X)
  have hP : IsStarProjection P := matrixRealSupport_isStarProjection (matrixRectAbs X)
  have hPA : (1 - P) * matrixRectAbs X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, matrixRealSupport_mul (matrixRectAbs_isHermitian X), sub_self]
  have hz : X * (1 - P) = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [Matrix.conjTranspose_mul, hP.one_sub.isSelfAdjoint.isHermitian.eq]
    calc
      _ = (1 - P) * (Xᴴ * X) * (1 - P) := by simp only [Matrix.mul_assoc]
      _ = (1 - P) * (matrixRectAbs X * matrixRectAbs X) * (1 - P) := by
        rw [matrixRectAbs_mul_self]
      _ = 0 := by rw [← Matrix.mul_assoc (1 - P), hPA, Matrix.zero_mul, Matrix.zero_mul]
  have he : X - X * P = 0 := by simpa only [Matrix.mul_sub, Matrix.mul_one] using hz
  exact (sub_eq_zero.mp he).symm

theorem matrixRectPolar_mul_abs (X : Matrix ι κ ℂ) :
    matrixRectPolar X * matrixRectAbs X = X := by
  rw [matrixRectPolar, Matrix.mul_assoc,
    matrixRealInv_mul (matrixRectAbs_isHermitian X), matrix_mul_absSupport]

theorem matrixRectPolar_initial (X : Matrix ι κ ℂ) :
    (matrixRectPolar X)ᴴ * matrixRectPolar X = matrixRealSupport (matrixRectAbs X) := by
  rw [matrixRectPolar, Matrix.conjTranspose_mul,
    (matrixRealInv_isSelfAdjoint (matrixRectAbs X)).isHermitian.eq]
  calc
    _ = matrixRealInv (matrixRectAbs X) * (Xᴴ * X) * matrixRealInv (matrixRectAbs X) := by
      simp only [Matrix.mul_assoc]
    _ = matrixRealInv (matrixRectAbs X) * (matrixRectAbs X * matrixRectAbs X) *
        matrixRealInv (matrixRectAbs X) := by rw [matrixRectAbs_mul_self]
    _ = matrixRealSupport (matrixRectAbs X) := by
      rw [← Matrix.mul_assoc _ (matrixRectAbs X), matrixRealInv_mul (matrixRectAbs_isHermitian X),
        matrixRealSupport_mul (matrixRectAbs_isHermitian X),
        mul_matrixRealInv (matrixRectAbs_isHermitian X)]

theorem matrixRectPolar_mul_support (X : Matrix ι κ ℂ) :
    matrixRectPolar X * matrixRealSupport (matrixRectAbs X) = matrixRectPolar X := by
  rw [matrixRectPolar, Matrix.mul_assoc, matrixRealInv_mul_support]

theorem matrixRectPolar_partial_isometry (X : Matrix ι κ ℂ) :
    matrixRectPolar X * (matrixRectPolar X)ᴴ * matrixRectPolar X = matrixRectPolar X := by
  rw [Matrix.mul_assoc, matrixRectPolar_initial, matrixRectPolar_mul_support]

theorem matrixRectPolar_initial_projection (X : Matrix ι κ ℂ) :
    IsStarProjection ((matrixRectPolar X)ᴴ * matrixRectPolar X) := by
  rw [matrixRectPolar_initial]
  exact matrixRealSupport_isStarProjection _

theorem matrixRectPolar_final_projection (X : Matrix ι κ ℂ) :
    IsStarProjection (matrixRectPolar X * (matrixRectPolar X)ᴴ) := by
  constructor
  · change (matrixRectPolar X * (matrixRectPolar X)ᴴ) *
      (matrixRectPolar X * (matrixRectPolar X)ᴴ) = _
    rw [← Matrix.mul_assoc, matrixRectPolar_partial_isometry]
  · show (matrixRectPolar X * (matrixRectPolar X)ᴴ)ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem matrixRectPolar_final_mul (X : Matrix ι κ ℂ) :
    (matrixRectPolar X * (matrixRectPolar X)ᴴ) * X = X := by
  calc
    _ = (matrixRectPolar X * (matrixRectPolar X)ᴴ) *
        (matrixRectPolar X * matrixRectAbs X) := by rw [matrixRectPolar_mul_abs]
    _ = X := by rw [← Matrix.mul_assoc, matrixRectPolar_partial_isometry, matrixRectPolar_mul_abs]

end ThomGame.Analysis
