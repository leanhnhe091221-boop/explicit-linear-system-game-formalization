module

public import ThomGame.Analysis.MatrixInclusionBoundedScaleOrder
public import ThomGame.Analysis.MatrixThomRetainedScales

/-!
# The actual corrected order relation (4.4)

Both scales use the retained positive blocks of the same correction and
the common representation of the original positive regularizer.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)
    (P : MatrixSubalgebraStarBlocks B)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))

theorem MatrixThomSpectralData.retainedRange_le :
    (matrixStarRepresentationBlocks B P S.cutSourceRepresentation).range ≤
      (matrixStarRepresentationComplementary _ R S.cutCommutantRepresentation).range := by
  rw [← matrixStarRepresentation_range_eq_blocks, ← matrixStarRepresentation_commutant_eq]
  exact S.correctedSourceAlgebra_le_target

theorem MatrixThomSpectralData.retainedScale_le :
    S.retainedSourceScale P ≤ S.retainedTargetScale R :=
  matrixSubalgebraScale_le_of_inclusion _ _ _ _ (S.retainedRange_le P R)

variable (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)

theorem MatrixThomSpectralData.commonPositiveScalar_mem_retainedSource (s : Fin F.count → ℝ) :
    S.commonPositiveScalar hDB F s ∈
      (matrixStarRepresentationBlocks B P S.cutSourceRepresentation).range := by
  rw [S.commonPositiveScalar_retained hDB F s]
  exact S.commonRetainedRange_le_source P hDB F (matrixStarBlockScalar_mem _ _ _)

theorem matrixThom_boundedScale_order (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i) :
    (matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s)).PosDef ∧
    matrixBoundedScale (S.retainedSourceScale P) (S.commonPositiveScalar hDB F s) ≤
      matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s) ∧
    (1 - matrixBoundedScale (S.retainedTargetScale R) (S.commonPositiveScalar hDB F s)).PosDef :=
  matrixInclusionBoundedScale_order _ _ _ _ (S.retainedRange_le P R) _
    (S.commonPositiveScalar_posDef hDB F s hs) (S.commonPositiveScalar_mem_retainedSource P hDB F s)

end ThomGame.Analysis
