module

public import ThomGame.Analysis.MatrixInclusionCellExpectation
public import ThomGame.Analysis.FiniteWeightedScaleMedian

/-!
# The actual conditional median of a central positive matrix scale

Each source simple block uses the probability weights of the actual
inclusion. The resulting positive central matrix makes the conditional
expectation of the bounded scale exactly one half of the identity.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)
    (a : Fin Q.count → ℝ) (ha : ∀ j, 0 < a j)

noncomputable def matrixConditionalScaleMedianCoefficients (i : Fin P.count) : ℝ :=
  weightedScaleMedian (fun j => matrixInclusionConditionalWeight B C P Q hBC j i) a
    (fun j => matrixInclusionConditionalWeight_nonneg B C P Q hBC j i)
    (matrixInclusionConditionalWeight_sum B C P Q hBC i) ha

theorem matrixConditionalScaleMedianCoefficients_pos (i : Fin P.count) :
    0 < matrixConditionalScaleMedianCoefficients B C P Q hBC a ha i :=
  weightedScaleMedian_pos _ _ _ _ _

theorem matrixConditionalScaleMedianCoefficients_mean (i : Fin P.count) :
    (∑ j, matrixInclusionConditionalWeight B C P Q hBC j i *
      boundedScaleScalar (a j) (matrixConditionalScaleMedianCoefficients B C P Q hBC a ha i)) = 1 / 2 :=
  weightedScaleMedian_mean _ _ _ _ _

noncomputable def matrixConditionalScaleMedian : CMatrix d :=
  matrixStarBlockScalar B P (matrixConditionalScaleMedianCoefficients B C P Q hBC a ha)

theorem matrixConditionalScaleMedian_posDef : (matrixConditionalScaleMedian B C P Q hBC a ha).PosDef :=
  matrixStarBlockScalar_posDef B P (matrixConditionalScaleMedianCoefficients_pos B C P Q hBC a ha)

theorem matrixConditionalScaleMedian_mem : matrixConditionalScaleMedian B C P Q hBC a ha ∈ B :=
  matrixStarBlockScalar_mem B P _

theorem matrixConditionalScaleMedian_commutes (Y : CMatrix d) (hY : Y ∈ B) :
    Commute (matrixConditionalScaleMedian B C P Q hBC a ha) Y :=
  matrixStarBlockScalar_commutes B P _ Y hY

theorem matrixConditionalScaleMedian_bounded_posDef :
    (matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixConditionalScaleMedian B C P Q hBC a ha)).PosDef :=
  matrixBoundedScale_inclusion_posDef B C P Q hBC a _ ha
    (matrixConditionalScaleMedianCoefficients_pos B C P Q hBC a ha)

theorem matrixConditionalScaleMedian_bounded_one_sub_posDef :
    (1 - matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixConditionalScaleMedian B C P Q hBC a ha)).PosDef :=
  matrixBoundedScale_inclusion_one_sub_posDef B C P Q hBC a _ ha
    (matrixConditionalScaleMedianCoefficients_pos B C P Q hBC a ha)

theorem matrixConditionalScaleMedian_bounded_mem :
    matrixBoundedScale (matrixStarBlockScalar C Q a) (matrixConditionalScaleMedian B C P Q hBC a ha) ∈ C :=
  matrixBoundedScale_inclusion_mem B C P Q hBC a _ ha
    (matrixConditionalScaleMedianCoefficients_pos B C P Q hBC a ha)

theorem matrixConditionalScaleMedian_bounded_commutes (Y : CMatrix d) (hY : Y ∈ B) :
    Commute (matrixBoundedScale (matrixStarBlockScalar C Q a)
      (matrixConditionalScaleMedian B C P Q hBC a ha)) Y :=
  matrixBoundedScale_inclusion_commutes B C P Q hBC a _ ha
    (matrixConditionalScaleMedianCoefficients_pos B C P Q hBC a ha) Y hY

theorem matrixConditionalScaleMedian_bounded_norm :
    matrixOpNorm (matrixBoundedScale (matrixStarBlockScalar C Q a)
      (matrixConditionalScaleMedian B C P Q hBC a ha)) ≤ 1 := by
  have hx := Matrix.nonneg_iff_posSemidef.mpr
    (matrixConditionalScaleMedian_bounded_posDef B C P Q hBC a ha).posSemidef
  have hxc := Matrix.nonneg_iff_posSemidef.mpr
    (matrixConditionalScaleMedian_bounded_one_sub_posDef B C P Q hBC a ha).posSemidef
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hx).mpr (sub_nonneg.mp hxc)

variable [NeZero d]

theorem matrixConditionalScaleMedian_expectation :
    matrixTraceProjection B (matrixBoundedScale (matrixStarBlockScalar C Q a)
      (matrixConditionalScaleMedian B C P Q hBC a ha)) = (1 / 2 : ℂ) • (1 : CMatrix d) := by
  rw [matrixConditionalScaleMedian, matrixBoundedScale_inclusion_expectation B C P Q hBC a _ ha
    (matrixConditionalScaleMedianCoefficients_pos B C P Q hBC a ha)]
  simp only [matrixConditionalScaleMedianCoefficients_mean B C P Q hBC a ha,
    matrixStarBlockScalar_const, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

end ThomGame.Analysis
