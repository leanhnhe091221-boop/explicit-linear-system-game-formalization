module

public import ThomGame.Analysis.MatrixThomCompressedCorrection

/-!
# Asymptotically full spectral ranges and support corners

The dimension ratio and both deleted traces converge along the given
filter. Every contraction sequence satisfies the same intertwining limit.
All errors and traces use the original dimensions, not the corrected ones.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    {L : Filter ι}

theorem matrixThom_cut_dimension_ratio_tendsto (hε : Filter.Tendsto ε L (𝓝 0)) :
    Filter.Tendsto (fun n => ((S n).cut.rank : ℝ) / dims n) L (𝓝 1) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun n => abs_nonneg _) (fun n => (S n).dimension_error)
    (by simpa using (hε.pow 2).const_mul 2)

theorem matrixThom_cut_complement_traces_tendsto (hε : Filter.Tendsto ε L (𝓝 0)) :
    Filter.Tendsto (fun n => matrixTraceReal (dims n) (1 - (S n).cutPolarᴴ * (S n).cutPolar)) L (𝓝 0) ∧
      Filter.Tendsto (fun n => matrixTraceReal (dims n) (1 - (S n).cutPolar * (S n).cutPolarᴴ)) L (𝓝 0) := by
  constructor
  · exact squeeze_zero (fun n => matrixTraceReal_nonneg _ (S n).cutPolar_partialIsometry.1.one_sub.nonneg)
      (fun n => (S n).cutPolar_complement_trace_bounds.1)
      (by simpa using (hε.pow 2).const_mul 2)
  · exact squeeze_zero (fun n => matrixTraceReal_nonneg _ (S n).cutPolar_partialIsometry.2.one_sub.nonneg)
      (fun n => (S n).cutPolar_complement_trace_bounds.2)
      (by simpa using (hε.pow 2).const_mul 4)

theorem matrixThom_cut_intertwining_tendsto (hε : Filter.Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n))
    (X : (n : ι) → B n) (hX : ∀ n, matrixOpNorm (X n : CMatrix (dims n)) ≤ 1) :
    Filter.Tendsto (fun n => rectHSNorm (dims n)
      ((S n).cutSourceRepresentation (X n) * (S n).cutPolar -
        (S n).cutPolar * (X n : CMatrix (dims n)))) L (𝓝 0) := by
  exact squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => (S n).cutPolar_intertwining_bound (hε0 n) (hBA n) (X n) (hX n))
    (by simpa using hε.const_mul (4 + Real.sqrt 2))

end ThomGame.Analysis
