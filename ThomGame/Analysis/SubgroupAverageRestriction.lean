module

public import ThomGame.Analysis.FiniteSubgroupAverage

/-! Subgroup averages agree with the corresponding averages in a containing subgroup. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertUnitaryInvariants_subgroupOf (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    {A L : Subgroup G} (hAL : A ≤ L) :
    hilbertUnitaryInvariants ((ρ.comp L.subtype).comp (A.subgroupOf L).subtype) =
      hilbertUnitaryInvariants (ρ.comp A.subtype) := by
  ext x
  constructor
  · intro hx a
    exact hx ⟨⟨a.val, hAL a.property⟩, a.property⟩
  · intro hx a
    exact hx ⟨a.val.val, a.property⟩

theorem hilbertUnitaryInvariants_top (ρ : G →* (H ≃ₗᵢ[ℂ] H)) :
    hilbertUnitaryInvariants (ρ.comp (⊤ : Subgroup G).subtype) = hilbertUnitaryInvariants ρ := by
  ext x
  constructor
  · intro hx g
    exact hx ⟨g, Subgroup.mem_top g⟩
  · intro hx g
    exact hx g.val

variable [CompleteSpace H]

theorem finiteSubgroupAverage_subgroupOf (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    {A L : Subgroup G} [Finite A] [Finite L] (hAL : A ≤ L) :
    finiteSubgroupAverage (ρ.comp L.subtype) (A.subgroupOf L) = finiteSubgroupAverage ρ A := by
  simp only [finiteSubgroupAverage_eq_projection,
    hilbertUnitaryInvariants_subgroupOf ρ hAL]

theorem finiteSubgroupAverage_restrict_top (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (L : Subgroup G) [Finite L] :
    finiteSubgroupAverage (ρ.comp L.subtype) ⊤ = finiteSubgroupAverage ρ L := by
  simp only [finiteSubgroupAverage_eq_projection,
    hilbertUnitaryInvariants_top]

end ThomGame.Analysis
