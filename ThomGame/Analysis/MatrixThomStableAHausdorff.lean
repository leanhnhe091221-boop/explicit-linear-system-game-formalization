module

public import ThomGame.Analysis.MatrixThomStableSupport
public import ThomGame.Analysis.MatrixUnitBallHausdorff

/-!
# Hausdorff comparison of the two actual stable A algebras

Both unital algebras live in M_N, with scalars on their added corners.
Their entire operator-norm unit balls are close in the actual HS metric
with denominator d. This establishes the A comparison in (3.4).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.stable_A_hausdorffEDist_finite (S : MatrixThomSpectralData A B D ε) :
    Metric.hausdorffEDist (matrixHSUnitBall d (S.stableOriginalAlgebra A))
      (matrixHSUnitBall d (S.stableCorrectedAlgebra S.correctedTargetAlgebra)) < ⊤ :=
  lt_of_le_of_lt (matrixCommonCompression_hausdorffEDist_bound d _ _ S.stableSupport
    S.stableSupport_projection S.stableSupport_source_compression S.stableSupport_target_compression)
    ENNReal.ofReal_lt_top

theorem MatrixThomSpectralData.stable_A_hausdorff_trace_bound (S : MatrixThomSpectralData A B D ε) :
    matrixHSUnitBallHausdorff d (S.stableOriginalAlgebra A)
      (S.stableCorrectedAlgebra S.correctedTargetAlgebra) ≤
        Real.sqrt (2 * matrixTraceReal d (1 - S.stableSupport)) :=
  matrixCommonCompression_hausdorff_bound d _ _ S.stableSupport S.stableSupport_projection
    S.stableSupport_source_compression S.stableSupport_target_compression

theorem MatrixThomSpectralData.stable_A_hausdorff_bound
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) :
    matrixHSUnitBallHausdorff d (S.stableOriginalAlgebra A)
      (S.stableCorrectedAlgebra S.correctedTargetAlgebra) ≤ 2 * Real.sqrt 3 * ε := by
  apply S.stable_A_hausdorff_trace_bound.trans
  have hp : 0 ≤ 2 * Real.sqrt 3 * ε := mul_nonneg (by positivity) hε
  have hs : (2 * Real.sqrt 3 * ε) ^ 2 = 12 * ε ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have he : 2 * matrixTraceReal d (1 - S.stableSupport) ≤ (2 * Real.sqrt 3 * ε) ^ 2 := by
    rw [hs]
    linarith [S.stableSupport_complement_trace]
  simpa only [Real.sqrt_sq hp] using Real.sqrt_le_sqrt he

end ThomGame.Analysis
