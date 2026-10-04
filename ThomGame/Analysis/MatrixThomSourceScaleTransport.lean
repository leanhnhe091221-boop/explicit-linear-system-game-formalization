module

public import ThomGame.Analysis.MatrixSubalgebraBoundedScaleTransport
public import ThomGame.Analysis.MatrixThomRawScalePositivity
public import ThomGame.Analysis.MatrixThomStableBApproximation

/-!
# Exact representation and common stable transport of the source scale
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (D B : StarSubalgebra ℂ (CMatrix d))
    (F : MatrixSubalgebraStarBlocks D) (P : MatrixSubalgebraStarBlocks B)
    (hDB : D ≤ B) (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i)

noncomputable def matrixSubalgebraBoundedScaleElement : B :=
  ⟨matrixBoundedScale (matrixSubalgebraScale B P) (matrixStarBlockScalar D F s),
    matrixBoundedScale_inclusion_mem D B F P hDB _ s (matrixSubalgebraScale_coefficient_pos B P) hs⟩

theorem matrixSubalgebraBoundedScaleElement_norm :
    matrixOpNorm (matrixSubalgebraBoundedScaleElement D B F P hDB s hs : CMatrix d) ≤ 1 :=
  matrixBoundedScale_inclusion_norm D B F P hDB _ s (matrixSubalgebraScale_coefficient_pos B P) hs

variable [NeZero d] {D B} {A : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)

theorem MatrixThomSpectralData.sourceBoundedScale_map :
    S.cutSourceRepresentation (matrixSubalgebraBoundedScaleElement D B F P hDB s hs) =
      matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s) := by
  apply matrixSubalgebraBoundedScale_map B S.cutSourceRepresentation
    (matrixStarBlockScalarElement B P (fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity B P B.subtype i))
    (StarSubalgebra.inclusion hDB (matrixStarBlockScalarElement D F s))
    (matrixSubalgebraBoundedScaleElement D B F P hDB s hs) rfl
  · exact ((matrixSubalgebraScale_posDef B P).add (matrixStarBlockScalar_posDef D F hs)).isUnit
  · exact ((S.rawSourceScale_posDef P).add (S.commonPositiveScalar_posDef hDB F s hs)).isUnit

include hs in
theorem MatrixThomSpectralData.sourceRawBoundedScale_stable_distance
    (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    rectHSNorm d (matrixFrameLift S.stableSourceFrame
        (matrixBoundedScale (matrixSubalgebraScale B P) (matrixStarBlockScalar D F s)) -
      matrixFrameLift S.stableTargetFrame
        (matrixBoundedScale (S.rawSourceScale P) (S.commonPositiveScalar hDB F s))) ≤
      (6 + 3 * Real.sqrt 2) * ε := by
  have h := S.stable_B_lift_distance hε hBA (matrixSubalgebraBoundedScaleElement D B F P hDB s hs)
    (matrixSubalgebraBoundedScaleElement_norm D B F P hDB s hs)
  rw [S.sourceBoundedScale_map F P hDB s hs] at h
  exact h

end ThomGame.Analysis
