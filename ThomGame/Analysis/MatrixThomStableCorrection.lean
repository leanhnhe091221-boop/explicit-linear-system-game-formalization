module

public import ThomGame.Analysis.MatrixThomStableFiniteEquality
public import ThomGame.Analysis.MatrixThomStableHausdorffLimits
public import ThomGame.Analysis.MatrixThomStableRelative

/-!
# Stable Hausdorff correction from the original near inclusion

The data are constructed from the actual trace expectation, Stinespring
dilation and spectral cutoff. This packages (3.4), the stable internal
equalities and the common-algebra assertion. It does not assert the
finite block decompositions or the multiplicity estimate (3.3).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem exists_matrixThomStableCorrection {d : Nat} [NeZero d]
    (A B D : StarSubalgebra ℂ (CMatrix d)) (hDA : D ≤ A) (hDB : D ≤ B)
    {ε : ℝ} (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    ∃ S : MatrixThomSpectralData A B D ε,
      S.stableCorrectedAlgebra S.correctedSourceAlgebra ≤ S.stableCorrectedAlgebra S.correctedTargetAlgebra ∧
      |(S.stableDim : ℝ) / d - 1| ≤ 4 * ε ^ 2 ∧
      matrixTraceReal d (1 - S.stableSupport) ≤ 6 * ε ^ 2 ∧
      matrixHSUnitBallHausdorff d (S.stableOriginalAlgebra B)
          (S.stableCorrectedAlgebra S.correctedSourceAlgebra) +
        matrixHSUnitBallHausdorff d (S.stableOriginalAlgebra A)
          (S.stableCorrectedAlgebra S.correctedTargetAlgebra) ≤
        (6 + 5 * Real.sqrt 2 + 2 * Real.sqrt 3) * ε ∧
      ∀ X : D,
        S.stableSupport * matrixFrameLift S.stableSourceFrame (X : CMatrix d) * S.stableSupport =
          S.stableSupport * matrixFrameLift S.stableTargetFrame
            (S.cutSourceRepresentation ⟨X, hDB X.property⟩) * S.stableSupport := by
  obtain ⟨S⟩ := exists_matrixThomSpectralData A B D hDA hDB hε hBA
  exact ⟨S, S.stableCorrected_inclusion, S.stableDim_ratio_bound, S.stableSupport_complement_trace,
    S.stable_AB_hausdorff_bound hε hBA, S.stable_common_corner_agreement hDB⟩

theorem exists_matrixThomStableHausdorffCorrection {ι : Type*}
    (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (hDA : ∀ n, D n ≤ A n) (hDB : ∀ n, D n ≤ B n)
    {ε : ι → ℝ} {L : Filter ι} (hε : Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    ∃ S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n),
      (∀ n, (S n).stableCorrectedAlgebra (S n).correctedSourceAlgebra ≤
        (S n).stableCorrectedAlgebra (S n).correctedTargetAlgebra) ∧
      Tendsto (fun n => ((S n).stableDim : ℝ) / dims n) L (𝓝 1) ∧
      Tendsto (fun n => matrixTraceReal (dims n) (1 - (S n).stableSupport)) L (𝓝 0) ∧
      Tendsto (fun n =>
        matrixHSUnitBallHausdorff (dims n) ((S n).stableOriginalAlgebra (B n))
            ((S n).stableCorrectedAlgebra (S n).correctedSourceAlgebra) +
          matrixHSUnitBallHausdorff (dims n) ((S n).stableOriginalAlgebra (A n))
            ((S n).stableCorrectedAlgebra (S n).correctedTargetAlgebra)) L (𝓝 0) ∧
      matrixInternalQuotient (fun n => (S n).stableDim) (fun n => (S n).stableOriginalAlgebra (A n)) L =
        matrixInternalQuotient (fun n => (S n).stableDim)
          (fun n => (S n).stableCorrectedAlgebra (S n).correctedTargetAlgebra) L ∧
      matrixInternalQuotient (fun n => (S n).stableDim) (fun n => (S n).stableOriginalAlgebra (B n)) L =
        matrixInternalQuotient (fun n => (S n).stableDim)
          (fun n => (S n).stableCorrectedAlgebra (S n).correctedSourceAlgebra) L ∧
      ∀ n (X : D n),
        (S n).stableSupport * matrixFrameLift (S n).stableSourceFrame (X : CMatrix (dims n)) *
            (S n).stableSupport =
          (S n).stableSupport * matrixFrameLift (S n).stableTargetFrame
            ((S n).cutSourceRepresentation ⟨X, hDB n X.property⟩) * (S n).stableSupport := by
  let S n := Classical.choice (exists_matrixThomSpectralData (A n) (B n) (D n)
    (hDA n) (hDB n) (hε0 n) (hBA n))
  exact ⟨S, fun n => (S n).stableCorrected_inclusion,
    matrixThom_stable_dimension_ratio_tendsto dims S hε,
    matrixThom_stable_complement_trace_tendsto dims S hε,
    matrixThom_stable_AB_hausdorff_tendsto dims S hε hε0 hBA,
    matrixThom_stable_A_internal_eq dims S hε hε0,
    matrixThom_stable_B_internal_eq dims S hε hε0 hBA,
    fun n => (S n).stable_common_corner_agreement (hDB n)⟩

end ThomGame.Analysis
