module

public import ThomGame.Analysis.MatrixConditionalScaleMedian
public import ThomGame.Analysis.StarSubalgebraCenter

/-!
# Thom's conditional median for the actual subalgebra scale

The block sizes and multiplicities here belong to the given matrix
subalgebra. No conditional expectation or median property is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (D A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks D) (Q : MatrixSubalgebraStarBlocks A) (hDA : D ≤ A)

noncomputable def matrixSubalgebraConditionalMedian : CMatrix d :=
  matrixConditionalScaleMedian D A P Q hDA
    (fun j => (Q.size j : ℝ) / matrixStarRepresentationMultiplicity A Q A.subtype j)
    (matrixSubalgebraScale_coefficient_pos A Q)

theorem matrixSubalgebraConditionalMedian_posDef : (matrixSubalgebraConditionalMedian D A P Q hDA).PosDef :=
  matrixConditionalScaleMedian_posDef D A P Q hDA _ _

theorem matrixSubalgebraConditionalMedian_center :
    matrixSubalgebraConditionalMedian D A P Q hDA ∈ starSubalgebraCenter D := by
  apply (mem_starSubalgebraCenter_iff D _).mpr
  refine ⟨matrixConditionalScaleMedian_mem D A P Q hDA _ _, ?_⟩
  intro Y hY
  exact (matrixConditionalScaleMedian_commutes D A P Q hDA _ _ Y hY).eq.symm

theorem matrixSubalgebraConditionalMedian_bounded_spec :
    let X := matrixBoundedScale (matrixSubalgebraScale A Q) (matrixSubalgebraConditionalMedian D A P Q hDA)
    X.PosDef ∧ (1 - X).PosDef ∧ X ∈ A ∧ matrixOpNorm X ≤ 1 ∧ ∀ Y ∈ D, Commute X Y := by
  exact ⟨matrixConditionalScaleMedian_bounded_posDef D A P Q hDA _ _,
    matrixConditionalScaleMedian_bounded_one_sub_posDef D A P Q hDA _ _,
    matrixConditionalScaleMedian_bounded_mem D A P Q hDA _ _,
    matrixConditionalScaleMedian_bounded_norm D A P Q hDA _ _,
    matrixConditionalScaleMedian_bounded_commutes D A P Q hDA _ _⟩

variable [NeZero d]

theorem matrixSubalgebraConditionalMedian_expectation :
    matrixTraceProjection D (matrixBoundedScale (matrixSubalgebraScale A Q)
      (matrixSubalgebraConditionalMedian D A P Q hDA)) = (1 / 2 : ℂ) • (1 : CMatrix d) :=
  matrixConditionalScaleMedian_expectation D A P Q hDA _ _

theorem matrixSubalgebraConditionalMedian_corner_expectation (e : CMatrix d) (he : e ∈ D) :
    matrixTraceProjection D (e * matrixBoundedScale (matrixSubalgebraScale A Q)
      (matrixSubalgebraConditionalMedian D A P Q hDA)) = (1 / 2 : ℂ) • e := by
  rw [matrixTraceProjection_mul_left D e _ he, matrixSubalgebraConditionalMedian_expectation,
    Matrix.mul_smul, Matrix.mul_one]

include hDA in
theorem exists_matrixSubalgebraConditionalMedian :
    ∃ M : CMatrix d, M ∈ starSubalgebraCenter D ∧ M.PosDef ∧
      let X := matrixBoundedScale (matrixSubalgebraScale A Q) M
      X.PosDef ∧ (1 - X).PosDef ∧ X ∈ A ∧ matrixOpNorm X ≤ 1 ∧
        (∀ Y ∈ D, Commute X Y) ∧ matrixTraceProjection D X = (1 / 2 : ℂ) • (1 : CMatrix d) := by
  obtain ⟨R⟩ := exists_matrixSubalgebraStarBlocks D
  have hs := matrixSubalgebraConditionalMedian_bounded_spec D A R Q hDA
  exact ⟨matrixSubalgebraConditionalMedian D A R Q hDA,
    matrixSubalgebraConditionalMedian_center D A R Q hDA,
    matrixSubalgebraConditionalMedian_posDef D A R Q hDA,
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2,
    matrixSubalgebraConditionalMedian_expectation D A R Q hDA⟩

end ThomGame.Analysis
