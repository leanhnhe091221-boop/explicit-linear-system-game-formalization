module

public import ThomGame.Analysis.FiniteAverageIntertwining
public import Mathlib.GroupTheory.Index

/-! A quantitative bound when only one subgroup supports a projected orbit average. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {G H : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finiteAverage_support_bound (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (T : H →L[ℂ] H)
    (K : Subgroup G) (x : H)
    (hzero : ∀ g, g ∉ K → T (ρ g x) = 0)
    (hbound : ∀ g, g ∈ K → ‖T (ρ g x)‖ ≤ ‖x‖) :
    ‖T (finiteUnitaryAverage ρ x)‖ ≤ (K.index : ℝ)⁻¹ * ‖x‖ := by
  classical
  have hk : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hi : (Fintype.card K : ℝ) * (K.index : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using K.card_mul_index)
  have hratio : (Fintype.card G : ℝ)⁻¹ * (Fintype.card K : ℝ) = (K.index : ℝ)⁻¹ := by
    rw [← hi, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hk, mul_one]
  calc
    ‖T (finiteUnitaryAverage ρ x)‖ = (Fintype.card G : ℝ)⁻¹ * ‖∑ g : G, T (ρ g x)‖ := by
      rw [finiteUnitaryAverage_apply, map_smul, map_sum, norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖T (ρ g x)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, if g ∈ K then ‖x‖ else 0 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro g _
      by_cases hg : g ∈ K
      · simpa only [ite_eq_left hg] using hbound g hg
      · simp only [ite_eq_right hg, hzero g hg, norm_zero, le_refl]
    _ = (Fintype.card G : ℝ)⁻¹ * ((Fintype.card K : ℝ) * ‖x‖) := by
      congr 1
      rw [← Finset.sum_filter, Finset.sum_subtype (p := fun g => g ∈ K) (F := inferInstance) _ (by simp)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by rw [← mul_assoc, hratio]

end ThomGame.Analysis
