module

public import ThomGame.Analysis.IntegerHeisenbergUnitaryAngle
public import ThomGame.Groups.IntegralShearRootSubgroups

/-! The Heisenberg angle for the actual infinite integer root subgroups. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor IntegralShear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rootSubgroup_invariants_eq (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) :
    hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype) = unitaryFixedSpace (ρ (of r)) := by
  ext ξ
  constructor
  · intro hξ
    exact hξ ⟨of r, of_mem_rootSubgroup r⟩
  · intro hξ g
    obtain ⟨m, hm⟩ := (mem_rootSubgroup r g.val).mp g.property
    change ρ g.val ξ = ξ
    rw [← hm]
    exact (hilbertVectorStabilizer ρ ξ).zpow_mem
      (show of r ∈ hilbertVectorStabilizer ρ ξ from hξ) m

theorem rootPair_unitary_heisenberg_relation (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) :
    ρ (of r) * ρ (of (right r)) = ρ (of (right r)) * ρ (of (across r)) * ρ (of r) := by
  simpa only [map_mul] using congrArg ρ (of_heisenberg_relation r)

theorem rootPair_unitary_center_commute (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) :
    Commute (ρ (of r)) (ρ (of (across r))) :=
  (of_commute r (across r) (by revert r; decide +kernel)).map ρ

variable [CompleteSpace H]

theorem integralRootPair_angle_sq (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (v u : H) (hv : v ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype))
    (hu : u ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (right r)).subtype))
    (hvZ : v ∈ (hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype))ᗮ) :
    ‖inner ℂ v u‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [rootSubgroup_invariants_eq] at hv hu hvZ
  have h := unitaryHeisenberg_angle_sq (ρ (of (right r))) (ρ (of r)) (ρ (of (across r)))
    (rootPair_unitary_heisenberg_relation ρ r) (rootPair_unitary_center_commute ρ r) u v hu hv hvZ
  rw [norm_inner_symm] at h
  convert h using 1
  ring

theorem integralRootPair_angle (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (v u : H) (hv : v ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype))
    (hu : u ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (right r)).subtype))
    (hvZ : v ∈ (hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype))ᗮ) :
    ‖inner ℂ v u‖ ≤ (Real.sqrt 2)⁻¹ * ‖v‖ * ‖u‖ := by
  rw [rootSubgroup_invariants_eq] at hv hu hvZ
  have h := unitaryHeisenberg_angle (ρ (of (right r))) (ρ (of r)) (ρ (of (across r)))
    (rootPair_unitary_heisenberg_relation ρ r) (rootPair_unitary_center_commute ρ r) u v hu hv hvZ
  rw [norm_inner_symm] at h
  convert h using 1
  ring

theorem integralRootPair_sum_sq_le (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (v u : H) (hv : v ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype))
    (hu : u ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (right r)).subtype))
    (hvZ : v ∈ (hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype))ᗮ) :
    ‖v + u‖ ^ 2 ≤ (1 + (Real.sqrt 2)⁻¹) * (‖v‖ ^ 2 + ‖u‖ ^ 2) := by
  have h := (Complex.re_le_norm (inner ℂ v u)).trans (integralRootPair_angle ρ r v u hv hu hvZ)
  have hn := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (2 : ℝ))) (sq_nonneg (‖v‖ - ‖u‖))
  rw [norm_add_sq (𝕜 := ℂ)]
  change ‖v‖ ^ 2 + 2 * (inner ℂ v u).re + ‖u‖ ^ 2 ≤ _
  nlinarith

theorem integralRootPair_central_free_angle (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (hZ : hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype) = ⊥)
    (v u : H) (hv : v ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype))
    (hu : u ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (right r)).subtype)) :
    ‖inner ℂ v u‖ ≤ (Real.sqrt 2)⁻¹ * ‖v‖ * ‖u‖ := by
  apply integralRootPair_angle ρ r v u hv hu
  rw [hZ, Submodule.bot_orthogonal_eq_top]
  trivial

theorem integralRootPair_central_free_four_sum_sq_le (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (hZ : hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype) = ⊥)
    (a b c d : H)
    (ha : a ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype))
    (hb : b ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype))
    (hc : c ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype))
    (hd : d ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (right r)).subtype)) :
    ‖a + b + c + d‖ ^ 2 ≤
      (1 + (Real.sqrt 2)⁻¹) * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  rw [hZ, Submodule.mem_bot] at ha hb
  subst a
  subst b
  have h := integralRootPair_sum_sq_le ρ r c d hc hd (by
    rw [hZ, Submodule.bot_orthogonal_eq_top]
    trivial)
  simpa only [zero_add, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h

end ThomGame.Analysis
