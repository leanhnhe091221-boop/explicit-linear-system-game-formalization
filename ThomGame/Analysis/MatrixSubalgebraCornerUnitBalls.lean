module

public import ThomGame.Analysis.MatrixPartialIsometryCornerNorms
public import ThomGame.Analysis.RectangularCompressionTraceLoss

/-!
# Unit balls of actual support corners

Compression maps the algebra unit ball onto the corner unit ball.
Every corner contraction is already a contraction in the original algebra,
and compression has a uniform HS error controlled by the deleted trace.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrixProjection_compression_opNorm_le (P X : CMatrix d) (hP : IsStarProjection P) :
    matrixOpNorm (P * X * P) ≤ matrixOpNorm X := by
  change ‖P * X * P‖ ≤ ‖X‖
  have hPP : IsStarProjection (Pᴴ * P) := by
    rw [hP.isSelfAdjoint.isHermitian.eq, hP.isIdempotentElem.eq]
    exact hP
  simpa only [hP.isSelfAdjoint.isHermitian.eq] using
    matrixPartialIsometry_sandwich_norm_le P hPP X

theorem matrixSubalgebraCorner_unitBall_compression_image (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsStarProjection P) (hPA : P ∈ A) :
    (fun X : CMatrix d => P * X * P) '' {X : CMatrix d | X ∈ A ∧ matrixOpNorm X ≤ 1} =
      {Y : CMatrix d | Y ∈ matrixSubalgebraCorner A P hP ∧ matrixOpNorm Y ≤ 1} := by
  ext Y
  constructor
  · rintro ⟨X, ⟨hX, hn⟩, rfl⟩
    exact ⟨matrixSubalgebraCorner_compression_mem A hP hPA X hX,
      (matrixProjection_compression_opNorm_le P X hP).trans hn⟩
  · rintro ⟨hY, hn⟩
    exact ⟨Y, ⟨hY.1, hn⟩, matrixSubalgebraCorner_compression_eq A hP Y hY⟩

theorem matrixSubalgebraCorner_unitBall_approximation (r : Nat) (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsStarProjection P) (hPA : P ∈ A)
    (X : CMatrix d) (hX : X ∈ A) (hn : matrixOpNorm X ≤ 1) :
    ∃ Y : CMatrix d, Y ∈ matrixSubalgebraCorner A P hP ∧ matrixOpNorm Y ≤ 1 ∧
      rectHSNorm r (X - Y) ≤ Real.sqrt (2 * matrixTraceReal r (1 - P)) := by
  exact ⟨P * X * P, matrixSubalgebraCorner_compression_mem A hP hPA X hX,
    (matrixProjection_compression_opNorm_le P X hP).trans hn,
    rectHSNorm_projection_compression_loss r P X hP hn⟩

end ThomGame.Analysis
