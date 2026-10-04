module

public import ThomGame.Analysis.MatrixThomSourceScaleTransport
public import ThomGame.Analysis.MatrixThomTargetScaleTransport
public import ThomGame.Analysis.MatrixThomRetainedScaleLimits

/-!
# Corrected bounded scales in the same stable ambient space

The two estimates use the same source frame, target frame, partial
isometry and unitary completion. The rank-change errors are retained
explicitly so their established convergence applies directly.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

theorem matrixFrameLift_distance_triangle {d m n : Nat} (r : Nat)
    (E : Matrix (Fin n) (Fin d) ℂ) (F : Matrix (Fin n) (Fin m) ℂ) (hF : Fᴴ * F = 1)
    (X : CMatrix d) (Y Z : CMatrix m) :
    rectHSNorm r (matrixFrameLift E X - matrixFrameLift F Z) ≤
      rectHSNorm r (matrixFrameLift E X - matrixFrameLift F Y) + rectHSNorm r (Y - Z) := by
  have he : matrixFrameLift E X - matrixFrameLift F Z =
      (matrixFrameLift E X - matrixFrameLift F Y) + (matrixFrameLift F Y - matrixFrameLift F Z) := by abel
  rw [he]
  have h := rectHSNorm_add_le r (matrixFrameLift E X - matrixFrameLift F Y)
    (matrixFrameLift F Y - matrixFrameLift F Z)
  have hFdist : rectHSNorm r (matrixFrameLift F Y - matrixFrameLift F Z) = rectHSNorm r (Y - Z) := by
    rw [← matrixFrameLift_sub, matrixFrameLift_hsNorm r hF]
  rw [hFdist] at h
  exact h

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)
    (P : MatrixSubalgebraStarBlocks B)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i)

include hs in
theorem MatrixThomSpectralData.sourceBoundedScale_stable_bound
    (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    rectHSNorm d (matrixFrameLift S.stableSourceFrame
        (matrixBoundedScale (matrixSubalgebraScale B P) (matrixStarBlockScalar D F s)) -
      matrixFrameLift S.stableTargetFrame
        (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s))) ≤
      (6 + 3 * Real.sqrt 2) * ε + rectHSNorm d
        (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s) -
          matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s)) := by
  have h := matrixFrameLift_distance_triangle d S.stableSourceFrame S.stableTargetFrame
    S.stableTargetFrame_initial
    (matrixBoundedScale (matrixSubalgebraScale B P) (matrixStarBlockScalar D F s))
    (matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s))
    (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s))
  have hb := S.sourceRawBoundedScale_stable_distance F P hDB s hs hε hBA
  rw [rectHSNorm_sub_comm d
    (matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s))] at h
  exact h.trans (add_le_add hb le_rfl)

include hs in
theorem MatrixThomSpectralData.targetBoundedScale_stable_bound (hDA : D ≤ A) (hε : 0 ≤ ε) :
    rectHSNorm d (matrixFrameLift S.stableSourceFrame
        (matrixBoundedScale (matrixSubalgebraComplementaryScale A R) (matrixStarBlockScalar D F s)) -
      matrixFrameLift S.stableTargetFrame
        (matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s))) ≤
      (2 + 2 * Real.sqrt 2) * ε + rectHSNorm d
        (matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s) -
          matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s)) := by
  have h := matrixFrameLift_distance_triangle d S.stableSourceFrame S.stableTargetFrame
    S.stableTargetFrame_initial
    (matrixBoundedScale (matrixSubalgebraComplementaryScale A R) (matrixStarBlockScalar D F s))
    (matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s))
    (matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s))
  exact h.trans (add_le_add (S.targetRawBoundedScale_stable_distance R hDB F s hs hDA hε) le_rfl)

end ThomGame.Analysis
