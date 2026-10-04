module

public import ThomGame.Analysis.MatrixOrderedTraceStability
public import ThomGame.Analysis.MatrixThomStableUnitaryTransport
public import ThomGame.Analysis.MatrixThomStableLimits

/-!
# No drift under the same ordered Thom transport

Equal original traces and the corrected order imply equality in the
original normalized 2-norm limit. The dimension factor is proved from
the same correction and is not silently discarded.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (a b : (n : ι) → CMatrix (dims n)) (x y : (n : ι) → CMatrix (S n).cut.rank)

theorem matrixThom_ordered_transport_tendsto
    (hx : ∀ n, 0 ≤ x n) (hxy : ∀ n, x n ≤ y n) (hy : ∀ n, y n ≤ 1)
    (htrace : ∀ n, (a n).trace = (b n).trace) (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (htransport : Tendsto (fun n =>
      rectHSNorm (S n).stableDim
        (matrixFrameLift (S n).stableTargetFrame (x n) * (S n).stableUnitary.val -
          (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame (a n)) +
      rectHSNorm (S n).stableDim
        (matrixFrameLift (S n).stableTargetFrame (y n) * (S n).stableUnitary.val -
          (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame (b n)))
      L (𝓝 0)) :
    Tendsto (fun n => hsNorm (a n - b n)) L (𝓝 0) := by
  let e := fun n =>
    rectHSNorm (S n).stableDim (matrixFrameLift (S n).stableSourceFrame (a n) -
      matrixFrameLift (S n).stableTargetFrame (x n)) +
    rectHSNorm (S n).stableDim (matrixFrameLift (S n).stableSourceFrame (b n) -
      matrixFrameLift (S n).stableTargetFrame (y n))
  have he : Tendsto e L (𝓝 0) := htransport.congr' (Eventually.of_forall fun n => by
    rw [(S n).stableUnitary_transport_norm, (S n).stableUnitary_transport_norm])
  have hb : Tendsto (fun n => e n + Real.sqrt (e n)) L (𝓝 0) := by
    simpa only [Real.sqrt_zero, add_zero] using he.add he.sqrt
  have hn : Tendsto (fun n => rectHSNorm (S n).stableDim (a n - b n)) L (𝓝 0) :=
    squeeze_zero (fun n => rectHSNorm_nonneg _ _)
      (fun n => matrixFrame_ordered_equalTrace_distance (S n).stableSourceFrame (S n).stableTargetFrame
        (S n).stableSourceFrame_initial (S n).stableTargetFrame_initial (a n) (b n) (x n) (y n)
        (hx n) (hxy n) (hy n) (htrace n)) hb
  have hp := (matrixThom_stable_dimension_ratio_tendsto dims S hε).sqrt.mul hn
  have hp' : Tendsto (fun n => Real.sqrt (((S n).stableDim : ℝ) / dims n) *
      rectHSNorm (S n).stableDim (a n - b n)) L (𝓝 0) := by
    simpa only [Real.sqrt_one, mul_zero] using hp
  apply hp'.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    exact (rectHSNorm_rescale (NeZero.pos (dims n))
      ((NeZero.pos (dims n)).trans_le (S n).le_stableDim) (a n - b n)).symm

end ThomGame.Analysis
