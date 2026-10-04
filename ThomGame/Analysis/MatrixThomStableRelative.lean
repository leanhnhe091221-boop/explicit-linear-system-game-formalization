module

public import ThomGame.Analysis.MatrixThomStableSupport

/-!
# Exact agreement of the common algebra on the stable support

The two actual embeddings of D commute with the common support and agree
after compression to it. This uses the original polar intertwiner; no
equivariance is imposed on the rest of the unitary completion.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.stableSupport_commutes_original_common
    (S : MatrixThomSpectralData A B D ε) (hDB : D ≤ B) (X : D) :
    S.stableSupport * matrixFrameLift S.stableSourceFrame (X : CMatrix d) =
      matrixFrameLift S.stableSourceFrame (X : CMatrix d) * S.stableSupport := by
  change matrixFrameLift S.stableSourceFrame _ * matrixFrameLift S.stableSourceFrame _ =
    matrixFrameLift S.stableSourceFrame _ * matrixFrameLift S.stableSourceFrame _
  rw [matrixFrameLift_mul S.stableSourceFrame_initial, matrixFrameLift_mul S.stableSourceFrame_initial,
    (S.cutPolar_common_supports hDB X).1]

theorem MatrixThomSpectralData.stableSupport_commutes_corrected_common
    (S : MatrixThomSpectralData A B D ε) (hDB : D ≤ B) (X : D) :
    S.stableSupport * matrixFrameLift S.stableTargetFrame (S.cutSourceRepresentation ⟨X, hDB X.property⟩) =
      matrixFrameLift S.stableTargetFrame (S.cutSourceRepresentation ⟨X, hDB X.property⟩) * S.stableSupport := by
  rw [S.stableSupport_target, matrixFrameLift_mul S.stableTargetFrame_initial,
    matrixFrameLift_mul S.stableTargetFrame_initial, (S.cutPolar_common_supports hDB X).2]

theorem MatrixThomSpectralData.stable_common_corner_agreement
    (S : MatrixThomSpectralData A B D ε) (hDB : D ≤ B) (X : D) :
    S.stableSupport * matrixFrameLift S.stableSourceFrame (X : CMatrix d) * S.stableSupport =
      S.stableSupport * matrixFrameLift S.stableTargetFrame
        (S.cutSourceRepresentation ⟨X, hDB X.property⟩) * S.stableSupport := by
  let W := S.cutPolar
  let Y := S.cutSourceRepresentation ⟨X, hDB X.property⟩
  have hW : (W * Wᴴ) * W = W := by
    rw [Matrix.mul_assoc]
    exact matrixPartialIsometry_mul_initial S.cutPolar_partialIsometry.1
  have hYX : Y * W = W * (X : CMatrix d) := S.cutPolar_common_intertwines hDB X
  have hc : (W * Wᴴ) * Y * (W * Wᴴ) = W * (X : CMatrix d) * Wᴴ := by
    calc
      _ = (W * Wᴴ) * (Y * W) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = (W * Wᴴ) * (W * (X : CMatrix d)) * Wᴴ := by rw [hYX]
      _ = _ := by rw [← Matrix.mul_assoc (W * Wᴴ) W, hW]
  have hs : S.stableSupport * matrixFrameLift S.stableSourceFrame (X : CMatrix d) * S.stableSupport =
      matrixFrameLift S.stableSourceFrame ((Wᴴ * W) * (X : CMatrix d) * (Wᴴ * W)) := by
    change matrixFrameLift S.stableSourceFrame _ * matrixFrameLift S.stableSourceFrame _ *
      matrixFrameLift S.stableSourceFrame _ = _
    rw [matrixFrameLift_mul S.stableSourceFrame_initial, matrixFrameLift_mul S.stableSourceFrame_initial]
  have ht : S.stableSupport * matrixFrameLift S.stableTargetFrame Y * S.stableSupport =
      matrixFrameLift S.stableTargetFrame ((W * Wᴴ) * Y * (W * Wᴴ)) := by
    rw [S.stableSupport_target, matrixFrameLift_mul S.stableTargetFrame_initial,
      matrixFrameLift_mul S.stableTargetFrame_initial]
  change _ = S.stableSupport * matrixFrameLift S.stableTargetFrame Y * S.stableSupport
  rw [hs, ht, hc]
  exact matrixStableFrames_source_corner S.cutPolar S.cutPolar_partialIsometry.1 (X : CMatrix d)

end ThomGame.Analysis
