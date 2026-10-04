module

public import ThomGame.Analysis.MatrixThomBoundedScaleStableBounds
public import ThomGame.Analysis.MatrixThomStableUnitaryTransport

/-!
# Simultaneous stable transport of both actual corrected bounded scales

The result is in the explicit unitary form and the common enlarged
space's own normalized norm. It is proved from the original-denominator
estimates, for the same correction at every coordinate.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (P : (n : ι) → MatrixSubalgebraStarBlocks (B n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    (hDB : ∀ n, D n ≤ B n) (F : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (s : (n : ι) → Fin (F n).count → ℝ) (hs : ∀ n i, 0 < s n i)

include hs in
theorem matrixThom_sourceBoundedScale_stable_tendsto (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    Tendsto (fun n => rectHSNorm (dims n)
      (matrixFrameLift (S n).stableSourceFrame
          (matrixBoundedScale (matrixSubalgebraScale (B n) (P n)) (matrixStarBlockScalar (D n) (F n) (s n))) -
        matrixFrameLift (S n).stableTargetFrame
          (matrixBoundedScale ((S n).retainedSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)))))
      L (𝓝 0) := by
  have hc : Tendsto (fun _ : ι => (6 + 3 * Real.sqrt 2 : ℝ)) L (𝓝 (6 + 3 * Real.sqrt 2)) := tendsto_const_nhds
  have hb := (hc.mul hε).add
    (matrixThom_retainedSourceScale_tendsto dims S P hDB F s hs L hε hε0 hBA)
  have hb' : Tendsto (fun n => (6 + 3 * Real.sqrt 2) * ε n + rectHSNorm (dims n)
      (matrixBoundedScale ((S n).retainedSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)) -
        matrixBoundedScale ((S n).rawSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))))
      L (𝓝 0) := by simpa only [mul_zero, add_zero] using hb
  exact squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => (S n).sourceBoundedScale_stable_bound (P n) (hDB n) (F n) (s n) (hs n) (hε0 n) (hBA n)) hb'

include hs in
theorem matrixThom_targetBoundedScale_stable_tendsto (hDA : ∀ n, D n ≤ A n)
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n) :
    Tendsto (fun n => rectHSNorm (dims n)
      (matrixFrameLift (S n).stableSourceFrame
          (matrixBoundedScale (matrixSubalgebraComplementaryScale (A n) (R n)) (matrixStarBlockScalar (D n) (F n) (s n))) -
        matrixFrameLift (S n).stableTargetFrame
          (matrixBoundedScale ((S n).retainedTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)))))
      L (𝓝 0) := by
  have hc : Tendsto (fun _ : ι => (2 + 2 * Real.sqrt 2 : ℝ)) L (𝓝 (2 + 2 * Real.sqrt 2)) := tendsto_const_nhds
  have hb := (hc.mul hε).add
    (matrixThom_retainedTargetScale_tendsto dims S R hDB F s hs L hε)
  have hb' : Tendsto (fun n => (2 + 2 * Real.sqrt 2) * ε n + rectHSNorm (dims n)
      (matrixBoundedScale ((S n).rawTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n)) -
        matrixBoundedScale ((S n).retainedTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))))
      L (𝓝 0) := by simpa only [mul_zero, add_zero] using hb
  exact squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => (S n).targetBoundedScale_stable_bound (R n) (hDB n) (F n) (s n) (hs n) (hDA n) (hε0 n)) hb'

include hs in
theorem matrixThom_boundedScale_common_unitary_tendsto (hDA : ∀ n, D n ≤ A n)
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    Tendsto (fun n =>
      rectHSNorm (S n).stableDim
        (matrixFrameLift (S n).stableTargetFrame
            (matrixBoundedScale ((S n).retainedSourceScale (P n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))) *
              (S n).stableUnitary.val -
          (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame
            (matrixBoundedScale (matrixSubalgebraScale (B n) (P n)) (matrixStarBlockScalar (D n) (F n) (s n)))) +
      rectHSNorm (S n).stableDim
        (matrixFrameLift (S n).stableTargetFrame
            (matrixBoundedScale ((S n).retainedTargetScale (R n)) ((S n).commonPositiveScalar (hDB n) (F n) (s n))) *
              (S n).stableUnitary.val -
          (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame
            (matrixBoundedScale (matrixSubalgebraComplementaryScale (A n) (R n)) (matrixStarBlockScalar (D n) (F n) (s n)))))
      L (𝓝 0) := by
  have hb := (matrixThom_sourceBoundedScale_stable_tendsto dims S P hDB F s hs L hε hε0 hBA).add
    (matrixThom_targetBoundedScale_stable_tendsto dims S R hDB F s hs hDA L hε hε0)
  apply squeeze_zero (fun n => add_nonneg (rectHSNorm_nonneg _ _) (rectHSNorm_nonneg _ _))
    (fun n => add_le_add ((S n).stableUnitary_transport_normalized_le _ _)
      ((S n).stableUnitary_transport_normalized_le _ _))
  simpa only [add_zero] using hb

end ThomGame.Analysis
