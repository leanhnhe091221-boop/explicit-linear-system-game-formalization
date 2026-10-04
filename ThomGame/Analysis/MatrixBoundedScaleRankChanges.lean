module

public import ThomGame.Analysis.MatrixBoundedScalePerturbation

/-!
# The two weighted rank-change bounds for bounded scales

Changing simple sizes or representation multiplicities has exactly
the weighted error used after Thom (4.5), at any original denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (D A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks D) (Q : MatrixSubalgebraStarBlocks A) (hDA : D ≤ A)
    (s : Fin P.count → ℝ) (hs : ∀ i, 0 < s i)

include hDA hs in
theorem matrixBoundedScale_sizeChange (r : Nat) (old : Fin Q.count → Nat) (hold : ∀ j, 0 < old j) :
    rectHSNorm r
      (matrixBoundedScale (matrixStarBlockScalar A Q (fun j => (old j : ℝ) /
        matrixStarRepresentationMultiplicity A Q A.subtype j)) (matrixStarBlockScalar D P s) -
      matrixBoundedScale (matrixSubalgebraScale A Q) (matrixStarBlockScalar D P s)) ^ 2 ≤
      (∑ j, (matrixStarRepresentationMultiplicity A Q A.subtype j : ℝ) * |(old j : ℝ) - Q.size j|) / r := by
  have hq (j : Fin Q.count) : 0 < (matrixStarRepresentationMultiplicity A Q A.subtype j : ℝ) :=
    Nat.cast_pos.mpr (matrixStarRepresentationMultiplicity_pos A Q A.subtype Subtype.val_injective j)
  have hp (j : Fin Q.count) : 0 < (Q.size j : ℝ) := Nat.cast_pos.mpr (Q.size_pos j)
  have he := matrixBoundedScale_targetPerturbation_rank_bound D A P Q hDA r
    (fun j => (old j : ℝ) / matrixStarRepresentationMultiplicity A Q A.subtype j)
    (fun j => (Q.size j : ℝ) / matrixStarRepresentationMultiplicity A Q A.subtype j) s
    (fun j => div_pos (Nat.cast_pos.mpr (hold j)) (hq j))
    (matrixSubalgebraScale_coefficient_pos A Q) hs
  apply he.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hf : ((old j : ℝ) / matrixStarRepresentationMultiplicity A Q A.subtype j) /
      ((Q.size j : ℝ) / matrixStarRepresentationMultiplicity A Q A.subtype j) - 1 =
      ((old j : ℝ) - Q.size j) / Q.size j := by
    field_simp [ne_of_gt (hq j), ne_of_gt (hp j)]
  rw [hf, abs_div, abs_of_pos (hp j)]
  field_simp [ne_of_gt (hp j)]

include hDA hs in
theorem matrixBoundedScale_multiplicityChange (r : Nat) (old : Fin Q.count → Nat) (hold : ∀ j, 0 < old j) :
    rectHSNorm r
      (matrixBoundedScale (matrixSubalgebraScale A Q) (matrixStarBlockScalar D P s) -
      matrixBoundedScale (matrixStarBlockScalar A Q (fun j => (Q.size j : ℝ) / old j))
        (matrixStarBlockScalar D P s)) ^ 2 ≤
      (∑ j, (Q.size j : ℝ) * |(old j : ℝ) - matrixStarRepresentationMultiplicity A Q A.subtype j|) / r := by
  have hq (j : Fin Q.count) : 0 < (matrixStarRepresentationMultiplicity A Q A.subtype j : ℝ) :=
    Nat.cast_pos.mpr (matrixStarRepresentationMultiplicity_pos A Q A.subtype Subtype.val_injective j)
  have hp (j : Fin Q.count) : 0 < (Q.size j : ℝ) := Nat.cast_pos.mpr (Q.size_pos j)
  have ho (j : Fin Q.count) : 0 < (old j : ℝ) := Nat.cast_pos.mpr (hold j)
  have he := matrixBoundedScale_targetPerturbation_rank_bound D A P Q hDA r
    (fun j => (Q.size j : ℝ) / matrixStarRepresentationMultiplicity A Q A.subtype j)
    (fun j => (Q.size j : ℝ) / old j) s (matrixSubalgebraScale_coefficient_pos A Q)
    (fun j => div_pos (hp j) (ho j)) hs
  apply he.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hf : ((Q.size j : ℝ) / matrixStarRepresentationMultiplicity A Q A.subtype j) /
      ((Q.size j : ℝ) / old j) - 1 =
      ((old j : ℝ) - matrixStarRepresentationMultiplicity A Q A.subtype j) /
        matrixStarRepresentationMultiplicity A Q A.subtype j := by
    field_simp [ne_of_gt (hq j), ne_of_gt (hp j), ne_of_gt (ho j)]
  rw [hf, abs_div, abs_of_pos (hq j)]
  field_simp [ne_of_gt (hq j)]

end ThomGame.Analysis
