module

public import ThomGame.Analysis.CoverKazhdanQuotient
public import ThomGame.Groups.CompressorCoverSurjections

/-!
# Unconditional finite Kazhdan sets for the actual N and H inside Q

These are the images of the finite cover root sets under the already
constructed surjections. No spectral-gap hypothesis is imposed.
-/

@[expose] public noncomputable section
namespace ThomGame.Compressor

open Analysis

def elementaryKazhdanSet : Finset elementarySubgroup := coverQuotientGeneratingSet 6 coverToElementary

def positiveKazhdanSet : Finset positiveSubgroup := coverQuotientGeneratingSet 3 coverToPositive

theorem elementaryKazhdanSet_generates : Subgroup.closure (elementaryKazhdanSet : Set elementarySubgroup) = ⊤ :=
  coverQuotientGeneratingSet_generates 6 coverToElementary coverToElementary_surjective

theorem positiveKazhdanSet_generates : Subgroup.closure (positiveKazhdanSet : Set positiveSubgroup) = ⊤ :=
  coverQuotientGeneratingSet_generates 3 coverToPositive coverToPositive_surjective

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem elementaryKazhdanSet_displacement (ρ : elementarySubgroup →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    ∃ g ∈ elementaryKazhdanSet, primeFiveKazhdanConstant * ‖x‖ ≤ ‖ρ g x - x‖ :=
  coverQuotientGeneratingSet_displacement 6 coverToElementary coverToElementary_surjective ρ x hx

theorem positiveKazhdanSet_displacement (ρ : positiveSubgroup →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    ∃ g ∈ positiveKazhdanSet, primeFiveKazhdanConstant * ‖x‖ ≤ ‖ρ g x - x‖ :=
  coverQuotientGeneratingSet_displacement 3 coverToPositive coverToPositive_surjective ρ x hx

theorem elementaryKazhdanSet_nonzero_invariant (ρ : elementarySubgroup →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : ‖x‖ = 1)
    (hmove : ∀ g ∈ elementaryKazhdanSet, ‖ρ g x - x‖ < primeFiveKazhdanConstant) :
    ∃ v : H, v ≠ 0 ∧ v ∈ hilbertUnitaryInvariants ρ :=
  coverQuotientGeneratingSet_nonzero_invariant 6 coverToElementary coverToElementary_surjective ρ x hx hmove

theorem positiveKazhdanSet_nonzero_invariant (ρ : positiveSubgroup →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : ‖x‖ = 1)
    (hmove : ∀ g ∈ positiveKazhdanSet, ‖ρ g x - x‖ < primeFiveKazhdanConstant) :
    ∃ v : H, v ≠ 0 ∧ v ∈ hilbertUnitaryInvariants ρ :=
  coverQuotientGeneratingSet_nonzero_invariant 3 coverToPositive coverToPositive_surjective ρ x hx hmove

end ThomGame.Compressor
