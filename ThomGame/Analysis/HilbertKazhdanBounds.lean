module

public import ThomGame.Analysis.CoverKazhdanQuotient

/-! A finite Kazhdan bound quantifies over all complete complex Hilbert representations. -/

@[expose] public section
namespace ThomGame.Analysis

universe u v w

def HilbertKazhdanBound {G : Type v} [Group G] (S : Finset G) (κ : ℝ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ξ : H), ξ ∈ (hilbertUnitaryInvariants ρ)ᗮ →
      ∃ g ∈ S, κ * ‖ξ‖ ≤ ‖ρ g ξ - ξ‖

def HasFiniteHilbertKazhdanSet (G : Type v) [Group G] : Prop :=
  ∃ S : Finset G, ∃ κ : ℝ, 0 < κ ∧ HilbertKazhdanBound.{u} S κ

variable {G : Type v} [Group G] {K : Type w} [Group K]

theorem hilbertKazhdanBound_image (S : Finset G) (κ : ℝ) (hS : HilbertKazhdanBound.{u} S κ)
    (f : G →* K) (hf : Function.Surjective f) :
    letI := Classical.decEq K
    HilbertKazhdanBound.{u} (S.image f) κ := by
  classical
  intro H _ _ _ ρ ξ hξ
  rw [← hilbertUnitaryInvariants_comp_surjective ρ f hf] at hξ
  obtain ⟨g, hg, hmove⟩ := hS H (ρ.comp f) ξ hξ
  exact ⟨f g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, hmove⟩

theorem hasFiniteHilbertKazhdanSet_surjective (hG : HasFiniteHilbertKazhdanSet.{u} G)
    (f : G →* K) (hf : Function.Surjective f) : HasFiniteHilbertKazhdanSet.{u} K := by
  classical
  obtain ⟨S, κ, hκ, hS⟩ := hG
  exact ⟨S.image f, κ, hκ, hilbertKazhdanBound_image S κ hS f hf⟩

theorem hilbertKazhdanBound_nonzero_invariant (S : Finset G) (κ : ℝ) (hS : HilbertKazhdanBound.{u} S κ)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hmove : ∀ g ∈ S, ‖ρ g ξ - ξ‖ < κ) : ∃ v : H, v ≠ 0 ∧ v ∈ hilbertUnitaryInvariants ρ := by
  by_contra h
  have hz : ∀ v ∈ hilbertUnitaryInvariants ρ, v = (0 : H) := by
    intro v hv
    by_contra hv0
    exact h ⟨v, hv0, hv⟩
  have horth : ξ ∈ (hilbertUnitaryInvariants ρ)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    rw [hz v hv, inner_zero_left]
  obtain ⟨g, hg, hgmove⟩ := hS H ρ ξ horth
  rw [hξ, mul_one] at hgmove
  exact (not_lt_of_ge hgmove) (hmove g hg)

end ThomGame.Analysis
