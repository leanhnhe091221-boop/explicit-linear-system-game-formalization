module

public import ThomGame.Analysis.MatrixFrameScalarExtension
public import ThomGame.Analysis.MatrixFrameStabilizationBounds

/-!
# Compression and lifting for two successive scalar corner extensions

The two small complementary corners may carry different scalars. The
compression to the original retained algebra is nevertheless exact.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {m d k : Nat} (J : Matrix (Fin m) (Fin d) ℂ) (G : Matrix (Fin d) (Fin k) ℂ)

theorem matrixFrame_composition_initial (hJ : Jᴴ * J = 1) (hG : Gᴴ * G = 1) :
    (J * G)ᴴ * (J * G) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    _ = Gᴴ * (Jᴴ * J) * G := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hJ, Matrix.mul_one, hG]

theorem matrixFrameLift_composition (X : CMatrix k) :
    matrixFrameLift (J * G) X = matrixFrameLift J (matrixFrameLift G X) := by
  simp only [matrixFrameLift, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem matrixFrameCompression_composition (Y : CMatrix m) :
    (J * G)ᴴ * Y * (J * G) = Gᴴ * (Jᴴ * Y * J) * G := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem matrixNestedFrameScalar_lift_mem (A : StarSubalgebra ℂ (CMatrix k))
    (hJ : Jᴴ * J = 1) (hG : Gᴴ * G = 1) (X : CMatrix k) (hX : X ∈ A) :
    matrixFrameLift (J * G) X ∈
      matrixFrameScalarAlgebra (matrixFrameScalarAlgebra A G hG) J hJ := by
  rw [matrixFrameLift_composition]
  exact matrixFrameScalarAlgebra_lift_mem _ J hJ _
    (matrixFrameScalarAlgebra_lift_mem A G hG X hX)

theorem matrixNestedFrameScalar_compression_mem (A : StarSubalgebra ℂ (CMatrix k))
    (hJ : Jᴴ * J = 1) (hG : Gᴴ * G = 1) (Y : CMatrix m)
    (hY : Y ∈ matrixFrameScalarAlgebra (matrixFrameScalarAlgebra A G hG) J hJ) :
    (J * G)ᴴ * Y * (J * G) ∈ A := by
  rw [matrixFrameCompression_composition]
  exact matrixFrameScalarAlgebra_compression_mem A G hG _
    (matrixFrameScalarAlgebra_compression_mem _ J hJ Y hY)

end ThomGame.Analysis
