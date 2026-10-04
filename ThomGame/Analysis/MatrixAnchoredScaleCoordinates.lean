module

public import ThomGame.Analysis.MatrixComplementaryStarBlocks
public import ThomGame.Analysis.MatrixUnitaryPullbackBlocks
public import ThomGame.Analysis.MatrixSubalgebraConditionalMedian

/-!
# Conditional median and bounded scale with the actual common block labels

The original algebra uses the complementary blocks of its specified
commutant decomposition. Its unitary pullbacks use those same labels.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] (D A : StarSubalgebra ℂ (CMatrix d))
    (F : MatrixSubalgebraStarBlocks D)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hDA : D ≤ A)

noncomputable def matrixAnchoredScaleCoefficients : Fin F.count → ℝ :=
  matrixConditionalScaleMedianCoefficients D A F (matrixSubalgebraComplementaryBlocks A R) hDA
    (fun i => ((matrixSubalgebraComplementaryBlocks A R).size i : ℝ) /
      matrixStarRepresentationMultiplicity A (matrixSubalgebraComplementaryBlocks A R) A.subtype i)
    (matrixSubalgebraScale_coefficient_pos A (matrixSubalgebraComplementaryBlocks A R))

theorem matrixAnchoredScaleCoefficients_pos (i : Fin F.count) :
    0 < matrixAnchoredScaleCoefficients D A F R hDA i :=
  matrixConditionalScaleMedianCoefficients_pos D A F (matrixSubalgebraComplementaryBlocks A R) hDA _ _ i

noncomputable def matrixAnchoredBoundedScale : CMatrix d :=
  matrixBoundedScale (matrixSubalgebraComplementaryScale A R)
    (matrixStarBlockScalar D F (matrixAnchoredScaleCoefficients D A F R hDA))

theorem matrixAnchoredBoundedScale_eq_median :
    matrixAnchoredBoundedScale D A F R hDA =
      matrixBoundedScale (matrixSubalgebraScale A (matrixSubalgebraComplementaryBlocks A R))
        (matrixSubalgebraConditionalMedian D A F (matrixSubalgebraComplementaryBlocks A R) hDA) := by
  rw [matrixSubalgebraComplementaryBlocks_scale]
  rfl

theorem matrixAnchoredBoundedScale_spec :
    (matrixAnchoredBoundedScale D A F R hDA).PosDef ∧
      (1 - matrixAnchoredBoundedScale D A F R hDA).PosDef ∧
      matrixAnchoredBoundedScale D A F R hDA ∈ A ∧
      matrixOpNorm (matrixAnchoredBoundedScale D A F R hDA) ≤ 1 := by
  rw [matrixAnchoredBoundedScale_eq_median]
  have h := matrixSubalgebraConditionalMedian_bounded_spec D A F (matrixSubalgebraComplementaryBlocks A R) hDA
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem matrixAnchoredBoundedScale_expectation :
    matrixTraceProjection D (matrixAnchoredBoundedScale D A F R hDA) = (1 / 2 : ℂ) • (1 : CMatrix d) := by
  rw [matrixAnchoredBoundedScale_eq_median]
  exact matrixSubalgebraConditionalMedian_expectation D A F (matrixSubalgebraComplementaryBlocks A R) hDA

theorem matrixAnchoredBoundedScale_pullback (U : UnitaryMatrix d)
    (hU : ∀ X ∈ D, U.val * X = X * U.val) :
    matrixBoundedScale (matrixSubalgebraScale _
      (matrixUnitaryPullbackBlocks A U (matrixSubalgebraComplementaryBlocks A R)))
      (matrixStarBlockScalar D F (matrixAnchoredScaleCoefficients D A F R hDA)) =
      U.valᴴ * matrixAnchoredBoundedScale D A F R hDA * U.val := by
  have h := matrixUnitaryPullbackBlocks_boundedScale A U (matrixSubalgebraComplementaryBlocks A R)
    (matrixStarBlockScalar D F (matrixAnchoredScaleCoefficients D A F R hDA))
    (matrixStarBlockScalar_posDef D F (matrixAnchoredScaleCoefficients_pos D A F R hDA))
    (hU _ (matrixStarBlockScalar_mem D F _))
  rw [matrixSubalgebraComplementaryBlocks_scale] at h
  exact h

end ThomGame.Analysis
