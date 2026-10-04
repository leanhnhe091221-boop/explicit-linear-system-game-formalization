module

public import ThomGame.Analysis.MatrixReverseInclusionConcentration

/-!
# Filter limits from two bounded scales concentrating at one half

The hypotheses are precisely the remaining concentration input to
Thom's argument. Neither spectral bounds on the regularizer nor a
joint spectral measure are assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat)
    (B C : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (P : (n : ι) → MatrixSubalgebraStarBlocks (B n))
    (Q : (n : ι) → MatrixSubalgebraStarBlocks (C n)) (hBC : ∀ n, B n ≤ C n)
    (M : (n : ι) → CMatrix (dims n)) (hM : ∀ n, (M n).PosDef) (hMB : ∀ n, M n ∈ B n)

include hBC hM hMB in
theorem matrixInclusionScaleRatio_defect_norm_tendsto (r : ι → Nat) (L : Filter ι)
    (hc : Tendsto (fun n =>
      rectHSNorm (r n) (matrixBoundedScale (matrixSubalgebraScale (B n) (P n)) (M n) - (1 / 2 : ℂ) • 1) +
      rectHSNorm (r n) (matrixBoundedScale (matrixSubalgebraScale (C n) (Q n)) (M n) - (1 / 2 : ℂ) • 1))
      L (𝓝 0)) :
    Tendsto (fun n => rectHSNorm (r n) (1 - (matrixInclusionScaleRatio (B n) (C n) (P n) (Q n))⁻¹))
      L (𝓝 0) := by
  have hb := (tendsto_const_nhds (x := (8 : ℝ))).mul hc
  exact squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => matrixInclusionScaleRatio_defect_norm (B n) (C n) (P n) (Q n) (hBC n) (r n)
      (M n) (hM n) (hMB n)) (by simpa only [mul_zero] using hb)

include hBC hM hMB in
theorem matrixInclusionScaleRatio_defect_trace_tendsto (L : Filter ι)
    (hc : Tendsto (fun n =>
      rectHSNorm (dims n) (matrixBoundedScale (matrixSubalgebraScale (B n) (P n)) (M n) - (1 / 2 : ℂ) • 1) +
      rectHSNorm (dims n) (matrixBoundedScale (matrixSubalgebraScale (C n) (Q n)) (M n) - (1 / 2 : ℂ) • 1))
      L (𝓝 0)) :
    Tendsto (fun n => matrixTraceReal (dims n) (1 - (matrixInclusionScaleRatio (B n) (C n) (P n) (Q n))⁻¹))
      L (𝓝 0) := by
  exact squeeze_zero (fun n => matrixInclusionScaleRatio_trace_defect_nonneg (B n) (C n) (P n) (Q n) (hBC n) _)
    (fun n => matrixTraceReal_self_le_rectHSNorm _)
    (matrixInclusionScaleRatio_defect_norm_tendsto dims B C P Q hBC M hM hMB dims L hc)

include hBC hM hMB in
theorem matrixReverseInclusion_center_tendsto [∀ n, NeZero (dims n)] (L : Filter ι)
    (hc : Tendsto (fun n =>
      rectHSNorm (dims n) (matrixBoundedScale (matrixSubalgebraScale (B n) (P n)) (M n) - (1 / 2 : ℂ) • 1) +
      rectHSNorm (dims n) (matrixBoundedScale (matrixSubalgebraScale (C n) (Q n)) (M n) - (1 / 2 : ℂ) • 1))
      L (𝓝 0)) : Tendsto (fun n => matrixNearInclusionError (C n) (B n)) L (𝓝 0) := by
  have hb := (tendsto_const_nhds (x := (4 : ℝ))).mul hc.sqrt
  exact squeeze_zero (fun n => matrixNearInclusionError_nonneg (C n) (B n))
    (fun n => matrixReverseInclusion_center_error (B n) (C n) (P n) (Q n) (hBC n) (M n) (hM n) (hMB n))
    (by simpa only [Real.sqrt_zero, mul_zero] using hb)

end ThomGame.Analysis
