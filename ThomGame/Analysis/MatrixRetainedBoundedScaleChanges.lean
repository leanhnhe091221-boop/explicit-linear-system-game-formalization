module

public import ThomGame.Analysis.MatrixRetainedComplementaryMultiplicity
public import ThomGame.Analysis.MatrixBoundedScaleRankChanges

/-!
# Bounded-scale errors on the actual retained representations

The scalar rank-change bounds now apply to the actual representation
and its commutant, with discarded blocks omitted only on the left.
The right side retains all original labels and any chosen denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem matrixRetainedBlock_sum_le {n : Nat} (keep : Fin n → Prop) [DecidablePred keep]
    (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f (matrixRetainedBlockLabel keep i)) ≤ ∑ i, f i := by
  classical
  rw [← Finset.sum_image (fun i _ j _ h => matrixRetainedBlockLabel_injective keep h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hf i)

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks A) (ρ : A →⋆ₐ[ℂ] CMatrix m)
    (D : StarSubalgebra ℂ (CMatrix m)) (F : MatrixSubalgebraStarBlocks D)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i)

include hs in
theorem matrixStarRepresentationRetained_scaleChange
    (hD : D ≤ (matrixStarRepresentationBlocks A P ρ).range)
    (r : Nat) (old : Fin P.count → Nat) (hold : ∀ i, 0 < old i) :
    rectHSNorm r
      (matrixBoundedScale (matrixSubalgebraScale _ (matrixStarRepresentationRetainedBlocks A P ρ))
        (matrixStarBlockScalar D F s) -
      matrixBoundedScale (ρ (matrixStarBlockScalarElement A P (fun i => (P.size i : ℝ) / old i)))
        (matrixStarBlockScalar D F s)) ^ 2 ≤
      (∑ i, (P.size i : ℝ) * |(old i : ℝ) - matrixStarRepresentationMultiplicity A P ρ i|) / r := by
  let Q := matrixStarRepresentationRetainedBlocks A P ρ
  have he := matrixBoundedScale_multiplicityChange D _ F Q hD s hs r
    (fun i => old (matrixStarRepresentationRetainedLabel A P ρ i))
    (fun i => hold (matrixStarRepresentationRetainedLabel A P ρ i))
  have hraw : matrixStarBlockScalar _ Q
      (fun i => (Q.size i : ℝ) / old (matrixStarRepresentationRetainedLabel A P ρ i)) =
      ρ (matrixStarBlockScalarElement A P (fun i => (P.size i : ℝ) / old i)) := by
    exact matrixStarRepresentationRetainedBlocks_scalar A P ρ (fun i => (P.size i : ℝ) / old i)
  rw [hraw] at he
  apply he.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
  have hb := matrixRetainedBlock_sum_le (fun i => 0 < matrixStarRepresentationMultiplicity A P ρ i)
    (fun i => (P.size i : ℝ) * |(old i : ℝ) - matrixStarRepresentationMultiplicity A P ρ i|)
    (fun i => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  change (∑ i, (P.size (matrixStarRepresentationRetainedLabel A P ρ i) : ℝ) *
    |(old (matrixStarRepresentationRetainedLabel A P ρ i) : ℝ) -
      matrixStarRepresentationMultiplicity _ (matrixStarRepresentationRetainedBlocks A P ρ)
        (matrixStarRepresentationBlocks A P ρ).range.subtype i|) ≤ _
  simp only [matrixStarRepresentationRetainedBlocks_multiplicity]
  exact hb

include hs in
theorem matrixStarRepresentationRetainedComplementary_scaleChange
    (hD : D ≤ (matrixStarRepresentationComplementary A P ρ).range)
    (r : Nat) (old : Fin P.count → Nat) (hold : ∀ i, 0 < old i) :
    rectHSNorm r
      (matrixBoundedScale (ρ (matrixStarBlockScalarElement A P (fun i => (old i : ℝ) / P.size i)))
        (matrixStarBlockScalar D F s) -
      matrixBoundedScale (matrixSubalgebraScale _ (matrixStarRepresentationRetainedComplementaryBlocks A P ρ))
        (matrixStarBlockScalar D F s)) ^ 2 ≤
      (∑ i, (P.size i : ℝ) * |(old i : ℝ) - matrixStarRepresentationMultiplicity A P ρ i|) / r := by
  let Q := matrixStarRepresentationRetainedComplementaryBlocks A P ρ
  have he := matrixBoundedScale_sizeChange D _ F Q hD s hs r
    (fun i => old (matrixStarRepresentationRetainedLabel A P ρ i))
    (fun i => hold (matrixStarRepresentationRetainedLabel A P ρ i))
  have hraw : matrixStarBlockScalar _ Q
      (fun i => (old (matrixStarRepresentationRetainedLabel A P ρ i) : ℝ) /
        matrixStarRepresentationMultiplicity _ Q (matrixStarRepresentationComplementary A P ρ).range.subtype i) =
      ρ (matrixStarBlockScalarElement A P (fun i => (old i : ℝ) / P.size i)) := by
    simp only [Q, matrixStarRepresentationRetainedComplementary_multiplicity]
    exact matrixStarRepresentationRetainedComplementary_scalar A P ρ (fun i => (old i : ℝ) / P.size i)
  rw [hraw] at he
  apply he.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
  have hb := matrixRetainedBlock_sum_le (fun i => 0 < matrixStarRepresentationMultiplicity A P ρ i)
    (fun i => (P.size i : ℝ) * |(old i : ℝ) - matrixStarRepresentationMultiplicity A P ρ i|)
    (fun i => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  simp only [Q, matrixStarRepresentationRetainedComplementary_multiplicity]
  exact hb

end ThomGame.Analysis
