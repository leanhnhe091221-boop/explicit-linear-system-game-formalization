module

public import ThomGame.Analysis.HilbertNormalInvariants

/-! Orthogonal projection onto normal-subgroup invariants commutes with the full unitary action. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertUnitary_submodule_map (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (S : Submodule ℂ H)
    (hS : ∀ g : G, ∀ x ∈ S, ρ g x ∈ S) (g : G) :
    S.map (ρ g).toLinearEquiv.toLinearMap = S := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hS g x hx
  · intro x hx
    refine ⟨ρ g⁻¹ x, hS g⁻¹ x hx, ?_⟩
    change ρ g (ρ g⁻¹ x) = x
    rw [← hilbertUnitary_apply_mul, mul_inv_cancel, map_one]
    rfl

variable [CompleteSpace H]

omit [CompleteSpace H] in
theorem hilbertUnitary_projection_commute (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (S : Submodule ℂ H)
    [CompleteSpace S] (hS : ∀ g : G, ∀ x ∈ S, ρ g x ∈ S) (g : G) (x : H) :
    ρ g (S.starProjection x) = S.starProjection (ρ g x) := by
  have h := Submodule.starProjection_map_apply (ρ g) S (ρ g x)
  simpa only [hilbertUnitary_submodule_map ρ S hS g, (ρ g).symm_apply_apply] using h.symm

def normalInvariantVector (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) (x : H) :
    hilbertUnitaryInvariants (ρ.comp N.subtype) :=
  ⟨(hilbertUnitaryInvariants (ρ.comp N.subtype)).starProjection x,
    (hilbertUnitaryInvariants (ρ.comp N.subtype)).starProjection_apply_mem x⟩

theorem normalInvariantVector_displacement_le (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal]
    (g : G) (x : H) : ‖ρ g (normalInvariantVector ρ N x).val - (normalInvariantVector ρ N x).val‖ ≤ ‖ρ g x - x‖ := by
  change ‖ρ g ((hilbertUnitaryInvariants (ρ.comp N.subtype)).starProjection x) -
    (hilbertUnitaryInvariants (ρ.comp N.subtype)).starProjection x‖ ≤ _
  rw [hilbertUnitary_projection_commute ρ _ (normalInvariants_stable ρ N), ← map_sub]
  exact Submodule.norm_starProjection_apply_le _ _

theorem normalInvariantVector_orthogonal (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal]
    (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    normalInvariantVector ρ N x ∈ (hilbertUnitaryInvariants (normalQuotientRepresentation ρ N))ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro v hv
  have hvG := (normalQuotientRepresentation_invariant_iff ρ N v).mp hv
  change inner ℂ v.val ((hilbertUnitaryInvariants (ρ.comp N.subtype)).starProjection x) = 0
  rw [← (hilbertUnitaryInvariants (ρ.comp N.subtype)).inner_starProjection_left_eq_right,
    (hilbertUnitaryInvariants (ρ.comp N.subtype)).starProjection_eq_self_iff.mpr v.property]
  exact (Submodule.mem_orthogonal _ _).mp hx v.val hvG

theorem normalInvariantResidual_orthogonal (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) (x : H) :
    x - (normalInvariantVector ρ N x).val ∈ (hilbertUnitaryInvariants (ρ.comp N.subtype))ᗮ :=
  (hilbertUnitaryInvariants (ρ.comp N.subtype)).sub_starProjection_mem_orthogonal x

theorem normalInvariantResidual_displacement (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G)
    (n : N) (x : H) :
    ρ n.val (x - (normalInvariantVector ρ N x).val) - (x - (normalInvariantVector ρ N x).val) = ρ n.val x - x := by
  rw [map_sub]
  have hfix : ρ n.val (normalInvariantVector ρ N x).val = (normalInvariantVector ρ N x).val :=
    (normalInvariantVector ρ N x).property n
  rw [hfix, sub_sub_sub_cancel_right]

end ThomGame.Analysis
