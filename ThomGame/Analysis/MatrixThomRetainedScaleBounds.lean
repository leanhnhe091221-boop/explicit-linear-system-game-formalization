module

public import ThomGame.Analysis.MatrixThomRetainedScales

/-!
# Quantitative raw-to-corrected bounded scales for the actual correction

The same common positive scalar is used on both corrected algebras.
The squared errors, normalized by the original dimension, are at most
18 epsilon^2 and 6 epsilon^2. No uniform spectral bounds on that scalar
or its inverse occur in the estimates.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)
    (P : MatrixSubalgebraStarBlocks B)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i)

include hs in
theorem matrixThom_retainedSourceScale_error (hε0 : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    rectHSNorm d
      (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s) -
        matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s)) ^ 2 ≤ 18 * ε ^ 2 := by
  have he := matrixStarRepresentationRetained_scaleChange B P S.cutSourceRepresentation
    (matrixStarRepresentationBlocks D F (S.commonRepresentation hDB)).range
    (matrixStarRepresentationRetainedBlocks D F (S.commonRepresentation hDB))
    (fun i => s (matrixStarRepresentationRetainedLabel D F (S.commonRepresentation hDB) i))
    (fun i => hs _) (S.commonRetainedRange_le_source P hDB F) d
    (matrixStarRepresentationMultiplicity B P B.subtype)
    (matrixStarRepresentationMultiplicity_pos B P B.subtype Subtype.val_injective)
  rw [← S.commonPositiveScalar_retained hDB F s] at he
  have hb := matrixThom_source_multiplicity_bound S P.toAlgebraic hε0 hBA
  apply he.trans
  simpa only [matrixAlgebraicMultiplicityDistance, abs_sub_comm] using hb

include hs in
theorem matrixThom_retainedTargetScale_error :
    rectHSNorm d
      (matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s) -
        matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s)) ^ 2 ≤ 6 * ε ^ 2 := by
  have he := matrixStarRepresentationRetainedComplementary_scaleChange _ R S.cutCommutantRepresentation
    (matrixStarRepresentationBlocks D F (S.commonRepresentation hDB)).range
    (matrixStarRepresentationRetainedBlocks D F (S.commonRepresentation hDB))
    (fun i => s (matrixStarRepresentationRetainedLabel D F (S.commonRepresentation hDB) i))
    (fun i => hs _) (S.commonRetainedRange_le_target R hDB F) d
    (matrixStarRepresentationMultiplicity _ R (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).subtype)
    (matrixStarRepresentationMultiplicity_pos _ R _ Subtype.val_injective)
  rw [← S.commonPositiveScalar_retained hDB F s] at he
  have hb := matrixThom_commutant_multiplicity_bound S R.toAlgebraic
  apply he.trans
  simpa only [matrixAlgebraicMultiplicityDistance, abs_sub_comm] using hb

include hs in
theorem matrixThom_retainedScale_error_sum (hε0 : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    rectHSNorm d
      (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s) -
        matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s)) ^ 2 +
    rectHSNorm d
      (matrixBoundedScale (S.rawTargetScale R) (S.commonPositiveScalar hDB F s) -
        matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s)) ^ 2 ≤ 24 * ε ^ 2 := by
  linarith [matrixThom_retainedSourceScale_error S P hDB F s hs hε0 hBA,
    matrixThom_retainedTargetScale_error S R hDB F s hs]

end ThomGame.Analysis
