module

public import ThomGame.Analysis.FiniteUnitaryAverage
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Exact displacement energy for a finite unitary group

The sum of squared displacements is twice the group order times the
squared distance to the actual fixed-space projection. This supplies
the quantitative link between almost invariant vectors and root-group
fixed spaces, with no dimension restriction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {G H : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finiteUnitary_sum_eq_card_average (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    ∑ g : G, ρ g x = (Fintype.card G : ℂ) • finiteUnitaryAverage ρ x := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Fintype.card_pos))
  rw [finiteUnitaryAverage_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem finiteUnitaryAverage_residual_zero (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    finiteUnitaryAverage ρ (x - finiteUnitaryAverage ρ x) = 0 := by
  rw [map_sub, finiteUnitaryAverage_of_invariant ρ _ (finiteUnitaryAverage_invariant ρ x), sub_self]

theorem finiteUnitary_displacement_residual (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (g : G) :
    ρ g (x - finiteUnitaryAverage ρ x) - (x - finiteUnitaryAverage ρ x) = ρ g x - x := by
  rw [map_sub, finiteUnitaryAverage_invariant ρ x g, sub_sub_sub_cancel_right]

theorem finiteUnitary_energy_identity (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    ∑ g : G, ‖ρ g x - x‖ ^ 2 =
      (2 * (Fintype.card G : ℝ)) * ‖x - finiteUnitaryAverage ρ x‖ ^ 2 := by
  let y := x - finiteUnitaryAverage ρ x
  have hsum : ∑ g : G, ρ g y = 0 := by
    rw [finiteUnitary_sum_eq_card_average, finiteUnitaryAverage_residual_zero, smul_zero]
  have hinner : ∑ g : G, (inner ℂ y (ρ g y)).re = 0 := by
    rw [← Complex.re_sum, ← inner_sum, hsum, inner_zero_right, Complex.zero_re]
  have hterm (g : G) : ‖ρ g y - y‖ ^ 2 = 2 * ‖y‖ ^ 2 - 2 * (inner ℂ y (ρ g y)).re := by
    rw [norm_sub_sq (𝕜 := ℂ), (ρ g).norm_map, inner_re_symm]
    change ‖y‖ ^ 2 - 2 * (inner ℂ y (ρ g y)).re + ‖y‖ ^ 2 =
      2 * ‖y‖ ^ 2 - 2 * (inner ℂ y (ρ g y)).re
    ring
  calc
    ∑ g : G, ‖ρ g x - x‖ ^ 2 = ∑ g : G, ‖ρ g y - y‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [finiteUnitary_displacement_residual]
    _ = ∑ g : G, (2 * ‖y‖ ^ 2 - 2 * (inner ℂ y (ρ g y)).re) := by simp_rw [hterm]
    _ = (2 * (Fintype.card G : ℝ)) * ‖y‖ ^ 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum, hinner,
        mul_zero, sub_zero, nsmul_eq_mul]
      ring

theorem finiteUnitary_residual_sq_le (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (ε : ℝ)
    (hmove : ∀ g : G, ‖ρ g x - x‖ ≤ ε) :
    2 * ‖x - finiteUnitaryAverage ρ x‖ ^ 2 ≤ ε ^ 2 := by
  have hsum : ∑ g : G, ‖ρ g x - x‖ ^ 2 ≤ (Fintype.card G : ℝ) * ε ^ 2 := by
    calc
      _ ≤ ∑ _g : G, ε ^ 2 := Finset.sum_le_sum (fun g _ => pow_le_pow_left₀ (norm_nonneg _) (hmove g) 2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [finiteUnitary_energy_identity] at hsum
  have hc : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith

end ThomGame.Analysis
