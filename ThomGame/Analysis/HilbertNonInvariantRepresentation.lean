module

public import ThomGame.Analysis.HilbertNormalInvariants

/-! The actual restriction to the orthogonal complement of global invariant vectors. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertUnitaryInvariantOrthogonal_stable (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (g : G) (x : H)
    (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) : ρ g x ∈ (hilbertUnitaryInvariants ρ)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro v hv
  rw [hilbertUnitary_inner_fixed_left ρ v hv g]
  exact (Submodule.mem_orthogonal _ _).mp hx v hv

def hilbertNonInvariantRepresentation (ρ : G →* (H ≃ₗᵢ[ℂ] H)) :
    G →* ((hilbertUnitaryInvariants ρ)ᗮ ≃ₗᵢ[ℂ] (hilbertUnitaryInvariants ρ)ᗮ) :=
  hilbertUnitaryRestriction ρ _ (hilbertUnitaryInvariantOrthogonal_stable ρ)

theorem hilbertNonInvariantRepresentation_apply (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (g : G)
    (x : (hilbertUnitaryInvariants ρ)ᗮ) :
    (hilbertNonInvariantRepresentation ρ g x : H) = ρ g (x : H) := rfl

theorem hilbertNonInvariantRepresentation_invariants (ρ : G →* (H ≃ₗᵢ[ℂ] H)) :
    hilbertUnitaryInvariants (hilbertNonInvariantRepresentation ρ) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hxG : (x : H) ∈ hilbertUnitaryInvariants ρ := by
    intro g
    exact congrArg Subtype.val (hx g)
  have hzero := (Submodule.mem_orthogonal _ _).mp x.property (x : H) hxG
  have hxzero : (x : H) = 0 := inner_self_eq_zero.mp hzero
  rw [Submodule.mem_bot]
  exact Subtype.ext hxzero

end ThomGame.Analysis
