module

public import ThomGame.Analysis.PrimeFiveCoverKazhdan

/-! The explicit cover Kazhdan constant descends through every actual surjective homomorphism. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open PrimeFiveRankThreeCover

variable {G K H : Type*} [Group G] [Group K]

def coverQuotientGeneratingSet (d : Nat) (f : Cover d →* G) : Finset G := by
  classical
  exact (rootGeneratingSet d).image f

theorem finiteGeneratingSet_image_generates (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤) (f : G →* K) (hf : Function.Surjective f) :
    letI := Classical.decEq K
    Subgroup.closure (S.image f : Set K) = ⊤ := by
  classical
  rw [Finset.coe_image, ← MonoidHom.map_closure, hS]
  exact Subgroup.map_top_of_surjective f hf

theorem coverQuotientGeneratingSet_generates (d : Nat) (f : Cover d →* G) (hf : Function.Surjective f) :
    Subgroup.closure (coverQuotientGeneratingSet d f : Set G) = ⊤ :=
  finiteGeneratingSet_image_generates (rootGeneratingSet d) (rootGeneratingSet_generates d) f hf

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertUnitaryInvariants_comp_surjective (ρ : K →* (H ≃ₗᵢ[ℂ] H))
    (f : G →* K) (hf : Function.Surjective f) :
    hilbertUnitaryInvariants (ρ.comp f) = hilbertUnitaryInvariants ρ := by
  ext x
  constructor
  · intro hx g
    obtain ⟨h, rfl⟩ := hf g
    exact hx h
  · intro hx g
    exact hx (f g)

variable [CompleteSpace H]

theorem coverQuotientGeneratingSet_displacement (d : Nat) (f : Cover d →* G) (hf : Function.Surjective f)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    ∃ g ∈ coverQuotientGeneratingSet d f, primeFiveKazhdanConstant * ‖x‖ ≤ ‖ρ g x - x‖ := by
  classical
  rw [← hilbertUnitaryInvariants_comp_surjective ρ f hf] at hx
  obtain ⟨g, hg, hbound⟩ := coverRootGeneratingSet_displacement d (ρ.comp f) x hx
  exact ⟨f g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, hbound⟩

theorem coverQuotientGeneratingSet_nonzero_invariant (d : Nat) (f : Cover d →* G) (hf : Function.Surjective f)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : ‖x‖ = 1)
    (hmove : ∀ g ∈ coverQuotientGeneratingSet d f, ‖ρ g x - x‖ < primeFiveKazhdanConstant) :
    ∃ v : H, v ≠ 0 ∧ v ∈ hilbertUnitaryInvariants ρ := by
  classical
  obtain ⟨v, hv, hinv⟩ := coverRootGeneratingSet_nonzero_invariant d (ρ.comp f) x hx
    (fun g hg => hmove (f g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
  rw [hilbertUnitaryInvariants_comp_surjective ρ f hf] at hinv
  exact ⟨v, hv, hinv⟩

end ThomGame.Analysis
