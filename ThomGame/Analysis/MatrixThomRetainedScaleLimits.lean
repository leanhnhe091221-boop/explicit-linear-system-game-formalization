module

public import ThomGame.Analysis.MatrixThomRetainedScaleBounds

/-!
# Convergence of actual corrected bounded scales

Along any filter, vanishing near-inclusion error makes both actual
raw-to-corrected errors vanish at the original normalization. The
common positive scalar, all block choices and all dimensions may vary.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (P : (n : ι) → MatrixSubalgebraStarBlocks (B n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    (hDB : ∀ n, D n ≤ B n) (F : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (s : (n : ι) → Fin (F n).count → ℝ) (hs : ∀ n i, 0 < s n i)

include hs in
theorem matrixThom_retainedSourceScale_tendsto (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    Tendsto (fun n => rectHSNorm (dims n)
      (matrixBoundedScale ((S n).retainedSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)) -
        matrixBoundedScale ((S n).rawSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))))
      L (𝓝 0) := by
  have hb : Tendsto (fun n => 18 * ε n ^ 2) L (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using tendsto_const_nhds.mul (hε.pow 2)
  have he := squeeze_zero (fun n => sq_nonneg (rectHSNorm (dims n)
      (matrixBoundedScale ((S n).retainedSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)) -
        matrixBoundedScale ((S n).rawSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)))))
    (fun n => matrixThom_retainedSourceScale_error (S n) (P n) (hDB n) (F n) (s n) (hs n) (hε0 n) (hBA n)) hb
  simpa only [Real.sqrt_sq (rectHSNorm_nonneg _ _), Real.sqrt_zero] using he.sqrt

include hs in
theorem matrixThom_retainedTargetScale_tendsto (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) :
    Tendsto (fun n => rectHSNorm (dims n)
      (matrixBoundedScale ((S n).rawTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)) -
        matrixBoundedScale ((S n).retainedTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))))
      L (𝓝 0) := by
  have hb : Tendsto (fun n => 6 * ε n ^ 2) L (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using tendsto_const_nhds.mul (hε.pow 2)
  have he := squeeze_zero (fun n => sq_nonneg (rectHSNorm (dims n)
      (matrixBoundedScale ((S n).rawTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)) -
        matrixBoundedScale ((S n).retainedTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)))))
    (fun n => matrixThom_retainedTargetScale_error (S n) (R n) (hDB n) (F n) (s n) (hs n)) hb
  simpa only [Real.sqrt_sq (rectHSNorm_nonneg _ _), Real.sqrt_zero] using he.sqrt

include hs in
theorem matrixThom_retainedScale_tendsto (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    Tendsto (fun n => rectHSNorm (dims n)
      (matrixBoundedScale ((S n).retainedSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)) -
        matrixBoundedScale ((S n).rawSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))) +
      rectHSNorm (dims n)
      (matrixBoundedScale ((S n).rawTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)) -
        matrixBoundedScale ((S n).retainedTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))))
      L (𝓝 0) := by
  simpa only [add_zero] using
    (matrixThom_retainedSourceScale_tendsto dims S P hDB F s hs L hε hε0 hBA).add
      (matrixThom_retainedTargetScale_tendsto dims S R hDB F s hs L hε)

end ThomGame.Analysis
