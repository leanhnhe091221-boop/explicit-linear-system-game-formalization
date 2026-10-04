module

public import ThomGame.Analysis.MatrixThomStableBHausdorff
public import ThomGame.Analysis.MatrixThomStableLimits

/-!
# Thom (3.4) for the same constructed stable identification

The sum of both actual unit-ball Hausdorff distances tends to zero along
any filter for which the near-inclusion error tends to zero. Dimensions
of the original and corrected spaces need not be equal.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n)) {L : Filter ι}

theorem matrixThom_stable_B_hausdorff_tendsto (hε : Filter.Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    Filter.Tendsto (fun n => matrixHSUnitBallHausdorff (dims n) ((S n).stableOriginalAlgebra (B n))
      ((S n).stableCorrectedAlgebra (S n).correctedSourceAlgebra)) L (𝓝 0) := by
  exact squeeze_zero (fun n => matrixHSUnitBallHausdorff_nonneg _ _ _)
    (fun n => (S n).stable_B_hausdorff_bound (hε0 n) (hBA n))
    (by simpa using hε.const_mul (6 + 5 * Real.sqrt 2))

theorem matrixThom_stable_AB_hausdorff_tendsto (hε : Filter.Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    Filter.Tendsto (fun n =>
      matrixHSUnitBallHausdorff (dims n) ((S n).stableOriginalAlgebra (B n))
          ((S n).stableCorrectedAlgebra (S n).correctedSourceAlgebra) +
        matrixHSUnitBallHausdorff (dims n) ((S n).stableOriginalAlgebra (A n))
          ((S n).stableCorrectedAlgebra (S n).correctedTargetAlgebra)) L (𝓝 0) := by
  simpa using (matrixThom_stable_B_hausdorff_tendsto dims S hε hε0 hBA).add
    (matrixThom_stable_A_hausdorff_tendsto dims S hε hε0)

end ThomGame.Analysis
