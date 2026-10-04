module

public import ThomGame.Analysis.MatrixSubalgebraComplementaryScale
public import ThomGame.Analysis.MatrixThomRawScalePositivity
public import ThomGame.Analysis.MatrixThomStableBApproximation

/-!
# Exact target-scale intertwining by the same Thom partial isometry

The original scale is written in the actual labelled complementary
blocks of A'. Both it and the common positive scalar are intertwined
exactly, even though their norms need not be uniformly bounded.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i)

include hs in
theorem MatrixThomSpectralData.targetRawBoundedScale_intertwines :
    matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s) * S.cutPolar =
      S.cutPolar * matrixBoundedScale (matrixSubalgebraComplementaryScale A R) (matrixStarBlockScalar D F s) := by
  apply matrixBoundedScale_intertwines_posDef _ _ _ _ S.cutPolar
    (S.rawTargetScale_posDef R) (S.commonPositiveScalar_posDef hDB F s hs)
    (matrixSubalgebraComplementaryScale_posDef A R) (matrixStarBlockScalar_posDef D F hs)
  · exact S.cutPolar_commutant_intertwines (matrixStarBlockScalarElement _ R _)
  · exact S.cutPolar_common_intertwines hDB (matrixStarBlockScalarElement D F s)

include hs in
theorem MatrixThomSpectralData.targetRawBoundedScale_norm :
    matrixOpNorm (matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s)) ≤ 1 := by
  change matrixOpNorm (matrixBoundedScale (S.cutCommutantRepresentation (matrixStarBlockScalarElement _ R _))
    (S.commonPositiveScalar hDB F s)) ≤ 1
  rw [← matrixStarRepresentationRetainedComplementary_scalar, S.commonPositiveScalar_retained hDB F s]
  apply matrixBoundedScale_inclusion_norm _ _ _ _ (S.commonRetainedRange_le_target R hDB F)
  · intro i
    exact matrixSubalgebraComplementaryScale_coefficient_pos A R _
  · intro i
    exact hs _

include hs in
theorem MatrixThomSpectralData.targetRawBoundedScale_stable_distance (hDA : D ≤ A) (hε : 0 ≤ ε) :
    rectHSNorm d (matrixFrameLift S.stableSourceFrame
        (matrixBoundedScale (matrixSubalgebraComplementaryScale A R) (matrixStarBlockScalar D F s)) -
      matrixFrameLift S.stableTargetFrame
        (matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s))) ≤
      (2 + 2 * Real.sqrt 2) * ε := by
  let X := matrixBoundedScale (matrixSubalgebraComplementaryScale A R) (matrixStarBlockScalar D F s)
  let Y := matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s)
  have hX : matrixOpNorm X ≤ 1 := matrixSubalgebraComplementaryScale_bounded_norm A R D F hDA s hs
  have hY : matrixOpNorm Y ≤ 1 := S.targetRawBoundedScale_norm R hDB F s hs
  have he := matrixStableFrames_distance_bound d S.cutPolar S.cutPolar_partialIsometry.1 X Y
  have hi : Y * S.cutPolar - S.cutPolar * X = 0 := sub_eq_zero.mpr
    (S.targetRawBoundedScale_intertwines R hDB F s hs)
  rw [hi, rectHSNorm_zero, add_zero] at he
  have ha := S.cutPolar_source_compression_loss hε X hX
  have hb := S.cutPolar_target_compression_loss hε Y hY
  exact he.trans (by linarith)

end ThomGame.Analysis
