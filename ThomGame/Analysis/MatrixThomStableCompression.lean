module

public import ThomGame.Analysis.MatrixThomStableAlgebras
public import ThomGame.Analysis.RectangularCompressionTraceLoss

/-!
# Removing the added corners in Thom's stable matrix space

Compression recovers contractions in the original component. Its uniform
HS error is controlled by the added dimensions with denominator d.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixFrame_complement_trace {n m : Nat} (r : Nat)
    (F : Matrix (Fin n) (Fin m) ℂ) (hF : Fᴴ * F = 1) :
    matrixTraceReal r (1 - F * Fᴴ) = ((n : ℝ) - m) / r := by
  rw [matrixTraceReal_sub, ← matrixFrameLift_one F, matrixFrameLift_trace r hF]
  simp [matrixTraceReal, sub_div]

theorem matrixFrame_compression_loss_sq {n m : Nat} (r : Nat)
    (F : Matrix (Fin n) (Fin m) ℂ) (hF : Fᴴ * F = 1)
    (Z : CMatrix n) (hZ : matrixOpNorm Z ≤ 1) :
    rectHSNorm r (Z - matrixFrameLift F (Fᴴ * Z * F)) ^ 2 ≤
      2 * matrixTraceReal r (1 - F * Fᴴ) := by
  rw [matrixFrameLift_compression]
  exact rectHSNorm_projection_compression_loss_sq r _ Z (matrixFrame_final_projection F hF) hZ

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.stableSourceFrame_complement_trace
    (S : MatrixThomSpectralData A B D ε) :
    matrixTraceReal d (1 - S.stableSourceFrame * S.stableSourceFrameᴴ) ≤ 4 * ε ^ 2 := by
  rw [matrixFrame_complement_trace d S.stableSourceFrame S.stableSourceFrame_initial]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (NeZero.pos d))).mpr
  exact (le_abs_self _).trans S.stableDim_error

theorem MatrixThomSpectralData.stableTargetFrame_complement_trace
    (S : MatrixThomSpectralData A B D ε) :
    matrixTraceReal d (1 - S.stableTargetFrame * S.stableTargetFrameᴴ) ≤ 2 * ε ^ 2 := by
  rw [matrixFrame_complement_trace d S.stableTargetFrame S.stableTargetFrame_initial]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (NeZero.pos d))).mpr
  change ((S.cut.rank + (1 - S.cutPolarᴴ * S.cutPolar).rank : Nat) : ℝ) - S.cut.rank ≤ _
  rw [Nat.cast_add, add_sub_cancel_left]
  exact S.cutPolar_initial_complement_rank

theorem MatrixThomSpectralData.stableSourceFrame_compression_loss
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε)
    (Z : CMatrix S.stableDim) (hZ : matrixOpNorm Z ≤ 1) :
    rectHSNorm d (Z - matrixFrameLift S.stableSourceFrame
      (S.stableSourceFrameᴴ * Z * S.stableSourceFrame)) ≤ 2 * Real.sqrt 2 * ε := by
  have he := matrixFrame_compression_loss_sq d S.stableSourceFrame S.stableSourceFrame_initial Z hZ
  have ht := S.stableSourceFrame_complement_trace
  have hp : 0 ≤ 2 * Real.sqrt 2 * ε := mul_nonneg (by positivity) hε
  have hs : (2 * Real.sqrt 2 * ε) ^ 2 = 8 * ε ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  nlinarith [rectHSNorm_nonneg d (Z - matrixFrameLift S.stableSourceFrame
    (S.stableSourceFrameᴴ * Z * S.stableSourceFrame))]

theorem MatrixThomSpectralData.stableTargetFrame_compression_loss
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε)
    (Z : CMatrix S.stableDim) (hZ : matrixOpNorm Z ≤ 1) :
    rectHSNorm d (Z - matrixFrameLift S.stableTargetFrame
      (S.stableTargetFrameᴴ * Z * S.stableTargetFrame)) ≤ 2 * ε := by
  have he := matrixFrame_compression_loss_sq d S.stableTargetFrame S.stableTargetFrame_initial Z hZ
  have ht := S.stableTargetFrame_complement_trace
  nlinarith [rectHSNorm_nonneg d (Z - matrixFrameLift S.stableTargetFrame
    (S.stableTargetFrameᴴ * Z * S.stableTargetFrame))]

end ThomGame.Analysis
