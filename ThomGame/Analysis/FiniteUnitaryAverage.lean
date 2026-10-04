module

public import ThomGame.Analysis.HilbertUnitaryInvariants
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Finite unitary group averages are the actual orthogonal projection

The representation acts by genuine complex linear isometries on any
Hilbert space. No injectivity, dimension bound, or averaging axiom is
used. The finite average is identified with the invariant projection.
-/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {G H : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteUnitaryAverage (ρ : G →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g : H →L[ℂ] H)

theorem finiteUnitaryAverage_apply (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    finiteUnitaryAverage ρ x = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g x := by
  simp only [finiteUnitaryAverage, smul_apply, sum_apply]
  rfl

theorem finiteUnitaryAverage_invariant (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    finiteUnitaryAverage ρ x ∈ hilbertUnitaryInvariants ρ := by
  intro h
  rw [finiteUnitaryAverage_apply, map_smul, map_sum]
  simp only [← hilbertUnitary_apply_mul]
  congr 1
  simpa using Equiv.sum_comp (Equiv.mulLeft h) (fun g => ρ g x)

theorem finiteUnitaryAverage_of_invariant (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hx : x ∈ hilbertUnitaryInvariants ρ) : finiteUnitaryAverage ρ x = x := by
  change ∀ g, ρ g x = x at hx
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Fintype.card_pos))
  rw [finiteUnitaryAverage_apply]
  simp only [hx, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem finiteUnitaryAverage_inner_fixed (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hx : x ∈ hilbertUnitaryInvariants ρ) (y : H) :
    inner ℂ x (finiteUnitaryAverage ρ y) = inner ℂ x y := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Fintype.card_pos))
  rw [finiteUnitaryAverage_apply, inner_smul_right, inner_sum]
  simp only [hilbertUnitary_inner_fixed_left ρ x hx, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, inv_mul_cancel_left₀ hc]

theorem finiteUnitaryAverage_residual_orthogonal (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    x - finiteUnitaryAverage ρ x ∈ (hilbertUnitaryInvariants ρ)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  rw [inner_sub_right, finiteUnitaryAverage_inner_fixed ρ y hy, sub_self]

variable [CompleteSpace H]

theorem finiteUnitaryAverage_eq_projection (ρ : G →* (H ≃ₗᵢ[ℂ] H)) :
    finiteUnitaryAverage ρ = (hilbertUnitaryInvariants ρ).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact ((hilbertUnitaryInvariants ρ).eq_starProjection_of_mem_orthogonal
    (finiteUnitaryAverage_invariant ρ x) (finiteUnitaryAverage_residual_orthogonal ρ x)).symm

theorem finiteUnitaryAverage_isStarProjection (ρ : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsStarProjection (finiteUnitaryAverage ρ) := by
  rw [finiteUnitaryAverage_eq_projection]
  exact isStarProjection_starProjection

theorem finiteUnitaryAverage_norm_le (ρ : G →* (H ≃ₗᵢ[ℂ] H)) : ‖finiteUnitaryAverage ρ‖ ≤ 1 := by
  rw [finiteUnitaryAverage_eq_projection]
  exact Submodule.starProjection_norm_le _

theorem finiteUnitaryAverage_eq_self_iff (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    finiteUnitaryAverage ρ x = x ↔ x ∈ hilbertUnitaryInvariants ρ := by
  rw [finiteUnitaryAverage_eq_projection]
  exact Submodule.starProjection_eq_self_iff

end ThomGame.Analysis
