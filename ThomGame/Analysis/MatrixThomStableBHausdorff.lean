module

public import ThomGame.Analysis.MatrixThomStableBApproximation
public import ThomGame.Analysis.MatrixThomStableAHausdorff

/-!
# The B Hausdorff estimate in Thom (3.4)

This is the actual Hausdorff distance of the entire operator-norm unit
balls, in the common stable matrix space and with denominator d.
Extended-distance finiteness is proved before passing to real distances.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.stable_B_hausdorffEDist_bound
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    Metric.hausdorffEDist (matrixHSUnitBall d (S.stableOriginalAlgebra B))
      (matrixHSUnitBall d (S.stableCorrectedAlgebra S.correctedSourceAlgebra)) ≤
        ENNReal.ofReal ((6 + 5 * Real.sqrt 2) * ε) :=
  matrixHSUnitBall_hausdorffEDist_le d _ _
    (S.stable_B_forward_contraction hε hBA) (S.stable_B_reverse_contraction hε hBA)

theorem MatrixThomSpectralData.stable_B_hausdorffEDist_finite
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    Metric.hausdorffEDist (matrixHSUnitBall d (S.stableOriginalAlgebra B))
      (matrixHSUnitBall d (S.stableCorrectedAlgebra S.correctedSourceAlgebra)) < ⊤ :=
  lt_of_le_of_lt (S.stable_B_hausdorffEDist_bound hε hBA) ENNReal.ofReal_lt_top

theorem MatrixThomSpectralData.stable_B_hausdorff_bound
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    matrixHSUnitBallHausdorff d (S.stableOriginalAlgebra B)
      (S.stableCorrectedAlgebra S.correctedSourceAlgebra) ≤ (6 + 5 * Real.sqrt 2) * ε :=
  ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by positivity) hε)
    (S.stable_B_hausdorffEDist_bound hε hBA)

theorem MatrixThomSpectralData.stable_AB_hausdorff_bound
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    matrixHSUnitBallHausdorff d (S.stableOriginalAlgebra B)
        (S.stableCorrectedAlgebra S.correctedSourceAlgebra) +
      matrixHSUnitBallHausdorff d (S.stableOriginalAlgebra A)
        (S.stableCorrectedAlgebra S.correctedTargetAlgebra) ≤
      (6 + 5 * Real.sqrt 2 + 2 * Real.sqrt 3) * ε := by
  linarith [S.stable_B_hausdorff_bound hε hBA, S.stable_A_hausdorff_bound hε]

end ThomGame.Analysis
