module

public import ThomGame.Analysis.PrimeFiveCoverRootAngles
public import ThomGame.Analysis.ThreeProjectionGap

/-! The unconditional global root-projection gap for the actual prime-five covers. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor PrimeFiveRankThreeCover
open scoped BigOperators

def primeFiveRootGap : ℝ := 1 - 2 * (Real.sqrt 5)⁻¹

theorem primeFiveRootGap_pos : 0 < primeFiveRootGap := by
  have h := primeFive_angle_lt_half
  dsimp only [primeFiveRootGap]
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coverRootLaplacian (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  projectionLaplacian (coverRootAverage d ρ)

theorem coverRootAverage_eqLocus (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    (coverRootAverage d ρ c).eqLocus (1 : H →L[ℂ] H) =
      hilbertUnitaryInvariants (ρ.comp (rootSubgroup d (cyclicRoot c)).subtype) := by
  ext x
  change coverRootAverage d ρ c x = x ↔ _
  rw [coverRootAverage, finiteSubgroupAverage_eq_projection]
  exact Submodule.starProjection_eq_self_iff

theorem coverRootLaplacian_nonneg (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) :
    0 ≤ coverRootLaplacian d ρ :=
  projectionLaplacian_nonneg _ (coverRootAverage_isStarProjection d ρ)

theorem coverRootLaplacian_ker (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) :
    (coverRootLaplacian d ρ).ker = hilbertUnitaryInvariants ρ := by
  rw [coverRootLaplacian, projectionLaplacian_ker _ (coverRootAverage_isStarProjection d ρ)]
  simp_rw [coverRootAverage_eqLocus]
  exact (cover_invariants_eq_cyclic_invariants d ρ).symm

theorem coverRootLaplacian_energy (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    (inner ℂ x (coverRootLaplacian d ρ x)).re = ∑ c : Axis, ‖x - coverRootAverage d ρ c x‖ ^ 2 :=
  projectionLaplacian_energy _ (coverRootAverage_isStarProjection d ρ) x

theorem coverRootLaplacian_polynomial (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) :
    primeFiveRootGap • coverRootLaplacian d ρ ≤ coverRootLaplacian d ρ * coverRootLaplacian d ρ :=
  threeProjectionLaplacian_polynomial (coverRootAverage d ρ) (coverPairAverage d ρ)
    (coverRootAverage_isStarProjection d ρ) (coverPairAverage_isStarProjection d ρ)
    (coverRootAverage_mul_pairAverage d ρ) (coverNextRootAverage_mul_pairAverage d ρ)
    (Real.sqrt 5)⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg 5)) (coverRootAverage_pair_angle d ρ)

theorem coverRootLaplacian_gap (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    primeFiveRootGap * ‖x‖ ^ 2 ≤ ∑ c : Axis, ‖x - coverRootAverage d ρ c x‖ ^ 2 := by
  rw [← coverRootLaplacian_ker d ρ] at hx
  rw [← coverRootLaplacian_energy]
  exact positive_polynomial_gap _ (coverRootLaplacian_nonneg d ρ) primeFiveRootGap
    (coverRootLaplacian_polynomial d ρ) x hx

omit [CompleteSpace H] in
theorem coverRootAverage_residual_sq_le (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H))
    (c : Axis) (x : H) (ε : ℝ)
    (hmove : ∀ g : rootSubgroup d (cyclicRoot c), ‖ρ g.val x - x‖ ≤ ε) :
    2 * ‖x - coverRootAverage d ρ c x‖ ^ 2 ≤ ε ^ 2 := by
  let := Fintype.ofFinite (rootSubgroup d (cyclicRoot c))
  exact finiteUnitary_residual_sq_le (ρ.comp (rootSubgroup d (cyclicRoot c)).subtype) x ε hmove

theorem coverRootLaplacian_displacement_gap (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) (ε : ℝ)
    (hmove : ∀ c : Axis, ∀ g : rootSubgroup d (cyclicRoot c), ‖ρ g.val x - x‖ ≤ ε) :
    2 * primeFiveRootGap * ‖x‖ ^ 2 ≤ 3 * ε ^ 2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun c _ => coverRootAverage_residual_sq_le d ρ c x ε (hmove c))
  rw [← Finset.mul_sum] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hs
  have hg := coverRootLaplacian_gap d ρ x hx
  linarith

end ThomGame.Analysis
