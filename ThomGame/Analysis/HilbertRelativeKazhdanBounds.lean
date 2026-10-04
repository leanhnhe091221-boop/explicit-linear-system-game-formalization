module

public import ThomGame.Analysis.HilbertKazhdanBounds

/-! Relative Kazhdan bounds for the actual invariant space of a subgroup homomorphism. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

universe u v w z

def HilbertRelativeKazhdanBound {G : Type v} [Group G] {N : Type w} [Group N]
    (ι : N →* G) (S : Finset G) (κ : ℝ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ξ : H), ξ ∈ (hilbertUnitaryInvariants (ρ.comp ι))ᗮ →
      ∃ g ∈ S, κ * ‖ξ‖ ≤ ‖ρ g ξ - ξ‖

variable {G : Type v} [Group G] {N : Type w} [Group N] {K : Type z} [Group K]

theorem hilbertRelativeKazhdanBound_image (ι : N →* G) (S : Finset G) (κ : ℝ)
    (hS : HilbertRelativeKazhdanBound.{u} ι S κ) (f : G →* K) :
    letI := Classical.decEq K
    HilbertRelativeKazhdanBound.{u} (f.comp ι) (S.image f) κ := by
  classical
  intro H _ _ _ ρ ξ hξ
  obtain ⟨g, hg, hgap⟩ := hS H (ρ.comp f) ξ hξ
  exact ⟨f g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, hgap⟩

theorem hilbertRelativeKazhdanBound_nonzero_invariant (ι : N →* G) (S : Finset G) (κ : ℝ)
    (hS : HilbertRelativeKazhdanBound.{u} ι S κ)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hmove : ∀ g ∈ S, ‖ρ g ξ - ξ‖ < κ) :
    ∃ η : H, η ≠ 0 ∧ η ∈ hilbertUnitaryInvariants (ρ.comp ι) := by
  by_contra h
  have hzero : ∀ η ∈ hilbertUnitaryInvariants (ρ.comp ι), η = (0 : H) := by
    intro η hη
    by_contra hη0
    exact h ⟨η, hη0, hη⟩
  have horth : ξ ∈ (hilbertUnitaryInvariants (ρ.comp ι))ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro η hη
    rw [hzero η hη, inner_zero_left]
  obtain ⟨g, hg, hgap⟩ := hS H ρ ξ horth
  rw [hξ, mul_one] at hgap
  exact (not_lt_of_ge hgap) (hmove g hg)

end ThomGame.Analysis
