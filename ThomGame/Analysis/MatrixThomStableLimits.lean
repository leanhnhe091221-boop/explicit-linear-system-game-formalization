module

public import ThomGame.Analysis.MatrixThomStableAHausdorff

/-!
# Negligible stabilization and actual A-unit-ball Hausdorff convergence

The same constructed unitary identifications have N/d tending to one,
an asymptotically full common support, and Hausdorff distance tending to
zero between the scalar-extended A algebras.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n)) {L : Filter ι}

theorem matrixThom_stable_dimension_ratio_tendsto (hε : Filter.Tendsto ε L (𝓝 0)) :
    Filter.Tendsto (fun n => ((S n).stableDim : ℝ) / dims n) L (𝓝 1) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun n => abs_nonneg _) (fun n => (S n).stableDim_ratio_bound)
    (by simpa using (hε.pow 2).const_mul 4)

theorem matrixThom_stable_complement_trace_tendsto (hε : Filter.Tendsto ε L (𝓝 0)) :
    Filter.Tendsto (fun n => matrixTraceReal (dims n) (1 - (S n).stableSupport)) L (𝓝 0) := by
  exact squeeze_zero (fun n => matrixTraceReal_nonneg _ (S n).stableSupport_projection.one_sub.nonneg)
    (fun n => (S n).stableSupport_complement_trace)
    (by simpa using (hε.pow 2).const_mul 6)

theorem matrixThom_stable_A_hausdorff_tendsto (hε : Filter.Tendsto ε L (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n) :
    Filter.Tendsto (fun n => matrixHSUnitBallHausdorff (dims n) ((S n).stableOriginalAlgebra (A n))
      ((S n).stableCorrectedAlgebra (S n).correctedTargetAlgebra)) L (𝓝 0) := by
  exact squeeze_zero (fun n => matrixHSUnitBallHausdorff_nonneg _ _ _)
    (fun n => (S n).stable_A_hausdorff_bound (hε0 n))
    (by simpa using hε.const_mul (2 * Real.sqrt 3))

end ThomGame.Analysis
