module

public import ThomGame.Analysis.MatrixThomExactIntertwinerSupports

/-!
# Full-rank limits for the actual exact B-intertwiners

The same chosen matrices have vanishing displacement, asymptotically
full rank and polar support complements of vanishing original trace.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n))
    {L : Filter ι}

theorem matrixThom_exact_intertwiner_distance_tendsto (hε : Filter.Tendsto ε L (𝓝 0)) :
    Filter.Tendsto (fun n => rectHSNorm (dims n)
      ((S n).cutFrame * (S n).exactIntertwiner (hε0 n) (hBA n) - (S n).isometry)) L (𝓝 0) := by
  exact squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => ((S n).exactIntertwiner_spec (hε0 n) (hBA n)).2.1)
    (by simpa using hε.const_mul (2 * Real.sqrt 2))

theorem matrixThom_exact_intertwiner_rank_ratio_tendsto (hε : Filter.Tendsto ε L (𝓝 0)) :
    Filter.Tendsto (fun n => (((S n).exactIntertwiner (hε0 n) (hBA n)).rank : ℝ) / dims n) L (𝓝 1) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun n => abs_nonneg _)
    (fun n => (S n).exactIntertwiner_rank_ratio_bound (hε0 n) (hBA n))
    (by simpa using (hε.pow 2).const_mul 8)

theorem matrixThom_exact_intertwiner_complement_traces_tendsto (hε : Filter.Tendsto ε L (𝓝 0)) :
    let U := fun n => (S n).exactPolarIntertwiner (hε0 n) (hBA n)
    Filter.Tendsto (fun n => matrixTraceReal (dims n) (1 - (U n)ᴴ * U n)) L (𝓝 0) ∧
      Filter.Tendsto (fun n => matrixTraceReal (dims n) (1 - U n * (U n)ᴴ)) L (𝓝 0) := by
  dsimp only
  constructor
  · exact squeeze_zero (fun n => matrixTraceReal_nonneg _
        ((S n).exactPolarIntertwiner_supports (hε0 n) (hBA n)).1.one_sub.nonneg)
      (fun n => ((S n).exactPolarIntertwiner_complement_traces (hε0 n) (hBA n)).1)
      (by simpa using (hε.pow 2).const_mul 8)
  · exact squeeze_zero (fun n => matrixTraceReal_nonneg _
        ((S n).exactPolarIntertwiner_supports (hε0 n) (hBA n)).2.1.one_sub.nonneg)
      (fun n => ((S n).exactPolarIntertwiner_complement_traces (hε0 n) (hBA n)).2)
      (by simpa using (hε.pow 2).const_mul 10)

end ThomGame.Analysis
