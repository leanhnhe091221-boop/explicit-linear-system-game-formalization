module

public import ThomGame.Analysis.MatrixThomStableAlgebras
public import ThomGame.Analysis.MatrixThomStableNearInclusion

/-!
# The common stable frames as an explicit unitary intertwining error

The original operator is extended by zero in its coordinate frame.
The same constructed unitary completion is used for every operator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)

theorem MatrixThomSpectralData.stableSourceFrameLift_unitary (X : CMatrix d) :
    matrixFrameLift S.stableSourceFrame X =
      S.stableUnitary.val * matrixFrameLift S.stableSourceCoordinateFrame X * S.stableUnitary.valᴴ := by
  rw [matrixFrameLift, ← S.stableSourceFrame_eq_unitary]
  simp only [Matrix.conjTranspose_mul, matrixFrameLift, Matrix.mul_assoc]

theorem MatrixThomSpectralData.stableUnitary_transport_norm (r : Nat)
    (X : CMatrix d) (Y : CMatrix S.cut.rank) :
    rectHSNorm r (matrixFrameLift S.stableTargetFrame Y * S.stableUnitary.val -
      S.stableUnitary.val * matrixFrameLift S.stableSourceCoordinateFrame X) =
      rectHSNorm r (matrixFrameLift S.stableSourceFrame X - matrixFrameLift S.stableTargetFrame Y) := by
  have he : (matrixFrameLift S.stableTargetFrame Y * S.stableUnitary.val -
      S.stableUnitary.val * matrixFrameLift S.stableSourceCoordinateFrame X) * (S.stableUnitary⁻¹).val =
      matrixFrameLift S.stableTargetFrame Y - matrixFrameLift S.stableSourceFrame X := by
    change (_ - _) * S.stableUnitary.valᴴ = _
    have hU : S.stableUnitary.val * S.stableUnitary.valᴴ = 1 := S.stableUnitary.prop.2
    rw [Matrix.sub_mul, Matrix.mul_assoc (matrixFrameLift S.stableTargetFrame Y),
      hU, Matrix.mul_one, S.stableSourceFrameLift_unitary X]
  calc
    _ = rectHSNorm r ((matrixFrameLift S.stableTargetFrame Y * S.stableUnitary.val -
        S.stableUnitary.val * matrixFrameLift S.stableSourceCoordinateFrame X) * (S.stableUnitary⁻¹).val) :=
      (rectHSNorm_mul_unitary r _ S.stableUnitary⁻¹).symm
    _ = _ := by rw [he, rectHSNorm_sub_comm]

theorem MatrixThomSpectralData.stableUnitary_transport_normalized_le
    (X : CMatrix d) (Y : CMatrix S.cut.rank) :
    rectHSNorm S.stableDim (matrixFrameLift S.stableTargetFrame Y * S.stableUnitary.val -
      S.stableUnitary.val * matrixFrameLift S.stableSourceCoordinateFrame X) ≤
      rectHSNorm d (matrixFrameLift S.stableSourceFrame X - matrixFrameLift S.stableTargetFrame Y) := by
  rw [S.stableUnitary_transport_norm]
  exact rectHSNorm_antitone_denominator (NeZero.pos d) S.le_stableDim _

end ThomGame.Analysis
