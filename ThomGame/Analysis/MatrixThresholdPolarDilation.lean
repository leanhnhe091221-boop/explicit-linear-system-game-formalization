module

public import ThomGame.Analysis.MatrixThresholdPolar
public import ThomGame.Analysis.SignedSpectralCoarea

/-!
# Threshold polar factors as signed functions of the actual dilation

The threshold construction respects adjoints and changes of basis.
Its self-adjoint dilation equals the signed spectral threshold of
the original dilation, also when the matrix has a kernel.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrixRectAbs_polar_intertwine (X : Matrix ι κ ℂ) :
    matrixRectAbs Xᴴ * matrixRectPolar X = matrixRectPolar X * matrixRectAbs X := by
  rw [matrixRectPolar_mul_abs, matrixRectPolar, ← Matrix.mul_assoc, matrixRectAbs_intertwine,
    Matrix.mul_assoc, mul_matrixRealInv (matrixRectAbs_isHermitian X), matrix_mul_absSupport]

theorem matrixThresholdPolar_conjTranspose (X : Matrix ι κ ℂ) (b : ℝ) :
    matrixThresholdPolar Xᴴ b = (matrixThresholdPolar X b)ᴴ := by
  have he := matrix_cfc_intertwine (matrixRectAbs_isHermitian Xᴴ) (matrixRectAbs_isHermitian X)
    (spectralStep b) (matrixRectPolar X) (matrixRectAbs_polar_intertwine X)
  have hQ := (matrixUpperSpectralProjection_projection (matrixRectAbs X) b).isSelfAdjoint.isHermitian.eq
  have hQ' := (matrixUpperSpectralProjection_projection (matrixRectAbs Xᴴ) b).isSelfAdjoint.isHermitian.eq
  change matrixUpperSpectralProjection (matrixRectAbs Xᴴ) b * matrixRectPolar X =
    matrixRectPolar X * matrixUpperSpectralProjection (matrixRectAbs X) b at he
  simpa only [matrixThresholdPolar, matrixRectPolar_conjTranspose, Matrix.conjTranspose_mul, hQ, hQ'] using
    congrArg Matrix.conjTranspose he

theorem matrixSelfAdjointDilation_thresholdPolar (X : Matrix ι κ ℂ) (b : ℝ) :
    cfc (signedSpectralStep b) (matrixSelfAdjointDilation X) =
      matrixSelfAdjointDilation (matrixThresholdPolar X b) := by
  let D := matrixSelfAdjointDilation X
  have hD := matrixSelfAdjointDilation_isHermitian X
  have he : cfc (signedSpectralStep b) D =
      matrixRealSign D * cfc (spectralStep b) (cfc (abs : ℝ → ℝ) D) := by
    change cfc (fun t : ℝ => (t * |t|⁻¹) * spectralStep b |t|) D = _
    rw [cfc_mul _ _ D (D.finite_real_spectrum.continuousOn _)
      (D.finite_real_spectrum.continuousOn _),
      cfc_comp' (spectralStep b) abs D ((D.finite_real_spectrum.image abs).continuousOn _)
        (D.finite_real_spectrum.continuousOn _) hD.isSelfAdjoint]
    rfl
  rw [he, matrixSelfAdjointDilation_sign, matrixSelfAdjointDilation_cfc_abs,
    matrix_cfc_blockDiagonal (matrixRectAbs_isHermitian Xᴴ) (matrixRectAbs_isHermitian X)]
  simp only [matrixSelfAdjointDilation, Matrix.fromBlocks_multiply, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, add_zero]
  rw [← matrixRectPolar_conjTranspose]
  change Matrix.fromBlocks 0 (matrixThresholdPolar X b) (matrixThresholdPolar Xᴴ b) 0 = _
  rw [matrixThresholdPolar_conjTranspose]

theorem matrixThresholdPolar_unitary_left (V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι κ ℂ) (b : ℝ) :
    matrixThresholdPolar (V.val * X) b = V.val * matrixThresholdPolar X b := by
  rw [matrixThresholdPolar, matrixRectPolar_unitary_left, matrixRectAbs_unitary_left, Matrix.mul_assoc]
  rfl

omit [DecidableEq ι] in
theorem matrixThresholdPolar_unitary_right (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) (b : ℝ) :
    matrixThresholdPolar (X * U.val) b = matrixThresholdPolar X b * U.val := by
  have he := matrix_cfc_intertwine (matrixRectAbs_isHermitian X)
    (matrixRectAbs_isHermitian (X * U.val)) (spectralStep b) U.val
    (matrixRectAbs_unitary_right_intertwine U X)
  rw [matrixThresholdPolar, matrixRectPolar_unitary_right, matrixUpperSpectralProjection,
    Matrix.mul_assoc, ← he, ← Matrix.mul_assoc]
  rfl

end ThomGame.Analysis
