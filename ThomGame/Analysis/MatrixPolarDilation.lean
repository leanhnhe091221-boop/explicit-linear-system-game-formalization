module

public import ThomGame.Analysis.MatrixRectangularPolar
public import ThomGame.Analysis.MatrixExactIntertwiner
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Polar factors and self-adjoint dilations

The rectangular polar factor is the off-diagonal block of the sign of
the self-adjoint dilation. This connects the actual construction to
Hilbert--Schmidt functional-calculus estimates.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrix_cfc_blockDiagonal {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) (f : ℝ → ℝ) :
    cfc f (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (cfc f A) 0 0 (cfc f B) := by
  have hM : Matrix.IsHermitian (Matrix.fromBlocks A 0 0 B) := hA.fromBlocks (by simp) hB
  have h₁ := matrix_cfc_intertwine hM hA f
    (Matrix.fromRows 1 (0 : Matrix κ ι ℂ)) (by
      simp [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul])
  have h₂ := matrix_cfc_intertwine hM hB f
    (Matrix.fromRows (0 : Matrix ι κ ℂ) 1) (by
      simp [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul])
  rw [← Matrix.fromBlocks_toBlocks (cfc f (Matrix.fromBlocks A 0 0 B))] at h₁ h₂
  simp only [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h₁ h₂
  ext (i | i) (j | j)
  · exact congrFun (congrFun h₁ (Sum.inl i)) j
  · exact congrFun (congrFun h₂ (Sum.inl i)) j
  · exact congrFun (congrFun h₁ (Sum.inr i)) j
  · exact congrFun (congrFun h₂ (Sum.inr i)) j

theorem matrixSqrt_eq_real_cfc {A : Matrix ι ι ℂ} (hA : 0 ≤ A) :
    CFC.sqrt A = cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA, cfcₙ_eq_cfc]

theorem matrixRectAbs_intertwine (X : Matrix ι κ ℂ) :
    matrixRectAbs Xᴴ * X = X * matrixRectAbs X := by
  rw [matrixRectAbs, Matrix.conjTranspose_conjTranspose, matrixRectAbs,
    matrixSqrt_eq_real_cfc (Matrix.posSemidef_self_mul_conjTranspose X).nonneg,
    matrixSqrt_eq_real_cfc (Matrix.posSemidef_conjTranspose_mul_self X).nonneg]
  exact matrix_cfc_intertwine (Matrix.isHermitian_mul_conjTranspose_self X)
    (Matrix.isHermitian_conjTranspose_mul_self X) Real.sqrt X (Matrix.mul_assoc _ _ _)

theorem matrixRectPolar_eq_left (X : Matrix ι κ ℂ) :
    matrixRectPolar X = matrixRealInv (matrixRectAbs Xᴴ) * X := by
  exact (matrix_cfc_intertwine (matrixRectAbs_isHermitian Xᴴ) (matrixRectAbs_isHermitian X)
    (fun t => t⁻¹) X (matrixRectAbs_intertwine X)).symm

theorem matrixRectPolar_conjTranspose (X : Matrix ι κ ℂ) :
    matrixRectPolar Xᴴ = (matrixRectPolar X)ᴴ := by
  rw [matrixRectPolar_eq_left, matrixRectPolar, Matrix.conjTranspose_mul,
    (matrixRealInv_isSelfAdjoint _).isHermitian.eq]
  rw [Matrix.conjTranspose_conjTranspose]

noncomputable def matrixRealSign (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun t : ℝ => t * |t|⁻¹) A

theorem matrixRealSign_eq_mul_inv_abs {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    matrixRealSign A = A * matrixRealInv (cfc (abs : ℝ → ℝ) A) := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id ℝ A
  rw [matrixRealSign, cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _), hid, matrixRealInv,
    cfc_comp' (fun t : ℝ => t⁻¹) abs A
      ((A.finite_real_spectrum.image abs).continuousOn _)
      (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint]

theorem matrixSelfAdjointDilation_sign (X : Matrix ι κ ℂ) :
    matrixRealSign (matrixSelfAdjointDilation X) =
      matrixSelfAdjointDilation (matrixRectPolar X) := by
  rw [matrixRealSign_eq_mul_inv_abs (matrixSelfAdjointDilation_isHermitian X),
    matrixSelfAdjointDilation_cfc_abs, matrixRealInv,
    matrix_cfc_blockDiagonal (matrixRectAbs_isHermitian Xᴴ) (matrixRectAbs_isHermitian X)]
  simp only [matrixSelfAdjointDilation, Matrix.fromBlocks_multiply, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, add_zero]
  change Matrix.fromBlocks 0 (matrixRectPolar X) (matrixRectPolar Xᴴ) 0 = _
  rw [matrixRectPolar_conjTranspose]

end ThomGame.Analysis
