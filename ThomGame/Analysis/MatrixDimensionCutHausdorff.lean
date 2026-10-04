module

public import ThomGame.Analysis.MatrixSubalgebraDimensionCut
public import ThomGame.Analysis.MatrixFrameScalarExtension
public import ThomGame.Analysis.MatrixUnitBallHausdorff

/-!
# Unit-ball approximation after the algebraic dimension cut

Lift the compressed algebra back to its actual support and add scalars
on the complement. The two entire unit balls have Hausdorff distance at
most twice the square root of twice the lost trace, in any fixed original
normalization. The proof uses actual contraction lifts in the reverse direction.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {m d : Nat} {A : StarSubalgebra ℂ (CMatrix m)} (S : MatrixSubalgebraDimensionCut A d)

noncomputable def matrixDimensionCutLiftedAlgebra : StarSubalgebra ℂ (CMatrix m) :=
  matrixFrameScalarAlgebra S.algebra S.frame S.initial

theorem matrixDimensionCut_compression_loss (r : Nat) (X : CMatrix m) (hn : matrixOpNorm X ≤ 1) :
    rectHSNorm r (X - matrixFrameLift S.frame (S.frameᴴ * X * S.frame)) ≤
      Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) := by
  rw [matrixFrameLift_compression]
  exact rectHSNorm_projection_compression_loss r _ X (matrixFrame_final_projection S.frame S.initial) hn

theorem matrixDimensionCut_forward_approximation (r : Nat) (X : CMatrix m)
    (hX : X ∈ A) (hn : matrixOpNorm X ≤ 1) :
    ∃ Y ∈ matrixDimensionCutLiftedAlgebra S, matrixOpNorm Y ≤ 1 ∧
      rectHSNorm r (X - Y) ≤ Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) := by
  refine ⟨matrixFrameLift S.frame (S.frameᴴ * X * S.frame),
    matrixFrameScalarAlgebra_lift_mem S.algebra S.frame S.initial _ (S.compression_mem X hX), ?_,
    matrixDimensionCut_compression_loss S r X hn⟩
  rw [matrixFrameLift_opNorm S.frame S.initial]
  exact (matrixFrameCompression_opNorm_le S.frame S.initial X).trans hn

theorem matrixDimensionCut_reverse_approximation (r : Nat) (Y : CMatrix m)
    (hY : Y ∈ matrixDimensionCutLiftedAlgebra S) (hn : matrixOpNorm Y ≤ 1) :
    ∃ X ∈ A, matrixOpNorm X ≤ 1 ∧
      rectHSNorm r (Y - X) ≤ 2 * Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) := by
  have hc := matrixFrameScalarAlgebra_compression_mem S.algebra S.frame S.initial Y hY
  have hcn := (matrixFrameCompression_opNorm_le S.frame S.initial Y).trans hn
  obtain ⟨X, hX, hnX, he⟩ := S.contraction_lift _ hc hcn
  refine ⟨X, hX, hnX, ?_⟩
  have h₁ := matrixDimensionCut_compression_loss S r Y hn
  have h₂ := matrixDimensionCut_compression_loss S r X hnX
  rw [he] at h₂
  calc
    _ = rectHSNorm r ((Y - matrixFrameLift S.frame (S.frameᴴ * Y * S.frame)) +
        (matrixFrameLift S.frame (S.frameᴴ * Y * S.frame) - X)) := by congr 1; abel
    _ ≤ rectHSNorm r (Y - matrixFrameLift S.frame (S.frameᴴ * Y * S.frame)) +
        rectHSNorm r (matrixFrameLift S.frame (S.frameᴴ * Y * S.frame) - X) := rectHSNorm_add_le _ _ _
    _ ≤ _ := by rw [rectHSNorm_sub_comm r _ X]; linarith

theorem matrixDimensionCut_hausdorffEDist_bound (r : Nat) [NeZero r] :
    Metric.hausdorffEDist (matrixHSUnitBall r A) (matrixHSUnitBall r (matrixDimensionCutLiftedAlgebra S)) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ))) := by
  apply matrixHSUnitBall_hausdorffEDist_le r A (matrixDimensionCutLiftedAlgebra S)
  · intro X hX hn
    obtain ⟨Y, hY, hnY, he⟩ := matrixDimensionCut_forward_approximation S r X hX hn
    exact ⟨Y, hY, hnY, by linarith [Real.sqrt_nonneg (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ))]⟩
  · exact matrixDimensionCut_reverse_approximation S r

theorem matrixDimensionCut_hausdorff_bound (r : Nat) [NeZero r] :
    matrixHSUnitBallHausdorff r A (matrixDimensionCutLiftedAlgebra S) ≤
      2 * Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (matrixDimensionCut_hausdorffEDist_bound S r)

end ThomGame.Analysis
