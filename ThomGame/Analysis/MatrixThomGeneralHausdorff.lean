module

public import ThomGame.Analysis.MatrixThomGeneralRelative

/-!
# Hausdorff convergence for the original unmodified input algebras

The original and modified source algebras agree on a filter-large set,
so the same frames satisfy (3.4) for the original input. Both Hausdorff
extended distances are genuinely finite at every coordinate.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixHSUnitBall_hausdorffEDist_finite {r n : Nat} [NeZero r] [NeZero n]
    (A B : StarSubalgebra ℂ (CMatrix n)) :
    Metric.hausdorffEDist (matrixHSUnitBall r A) (matrixHSUnitBall r B) < ⊤ := by
  have hb (X : CMatrix n) (hn : matrixOpNorm X ≤ 1) : rectHSNorm r X ≤ Real.sqrt ((n : ℝ) / r) := by
    rw [rectHSNorm_rescale (NeZero.pos r) (NeZero.pos n), rectHSNorm_eq_hsNorm]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left ((hsNorm_le_matrixOpNorm X).trans hn) (Real.sqrt_nonneg _)
  apply lt_of_le_of_lt (matrixHSUnitBall_hausdorffEDist_le r A B (ε := Real.sqrt ((n : ℝ) / r)) ?_ ?_)
    ENNReal.ofReal_lt_top
  · intro X _ hn
    exact ⟨0, B.zero_mem, by simp [matrixOpNorm], by simpa only [sub_zero] using hb X hn⟩
  · intro X _ hn
    exact ⟨0, A.zero_mem, by simp [matrixOpNorm], by simpa only [sub_zero] using hb X hn⟩

variable {ι : Type*} (dims : ι → Nat) [∀ i, NeZero (dims i)]
    {A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))} {ε : ι → ℝ}
    (S : MatrixThomModifiedData dims A B D ε)

theorem matrixThomModified_hausdorffEDist_finite (i : ι)
    (C : StarSubalgebra ℂ (CMatrix (dims i))) (C' : StarSubalgebra ℂ (CMatrix (S i).cut.rank)) :
    Metric.hausdorffEDist (matrixHSUnitBall (dims i) ((S i).stableOriginalAlgebra C))
      (matrixHSUnitBall (dims i) ((S i).stableCorrectedAlgebra C')) < ⊤ := by
  let : NeZero (S i).stableDim := ⟨Nat.ne_of_gt ((NeZero.pos (dims i)).trans_le (S i).le_stableDim)⟩
  exact matrixHSUnitBall_hausdorffEDist_finite _ _

theorem matrixThomModified_AB_hausdorff_tendsto (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (hε0 : ∀ i, 0 ≤ ε i) (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) :
    Tendsto (fun i =>
      matrixHSUnitBallHausdorff (dims i) ((S i).stableOriginalAlgebra (B i))
          ((S i).stableCorrectedAlgebra (S i).correctedSourceAlgebra) +
        matrixHSUnitBallHausdorff (dims i) ((S i).stableOriginalAlgebra (A i))
          ((S i).stableCorrectedAlgebra (S i).correctedTargetAlgebra)) L (𝓝 0) := by
  have ht := matrixThom_stable_AB_hausdorff_tendsto dims S (matrixSmallError_tendsto ε L hε)
    (matrixSmallError_nonneg ε hε0) (matrixSmallError_nearInclusion dims A B ε hBA)
  apply ht.congr'
  apply (matrixSmallError_eventually_lt_half ε L hε).mono
  intro i hi
  dsimp only
  have hA := congrArg (fun C : StarSubalgebra ℂ (CMatrix (dims i)) => (S i).stableOriginalAlgebra C)
    (matrixSmallErrorAlgebra_eq dims A ε hi)
  have hB := congrArg (fun C : StarSubalgebra ℂ (CMatrix (dims i)) => (S i).stableOriginalAlgebra C)
    (matrixSmallErrorAlgebra_eq dims B ε hi)
  rw [hA, hB]

end ThomGame.Analysis
