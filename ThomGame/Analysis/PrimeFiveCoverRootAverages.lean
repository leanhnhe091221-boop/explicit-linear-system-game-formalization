module

public import ThomGame.Analysis.FiniteSubgroupAverage
public import ThomGame.Groups.PrimeFiveCoverPairStructure

/-!
# Actual invariant projections for the three cover root groups

Finiteness and generation have already been proved from the cover's
relations. This file supplies the genuine projections and their nested
pair identities for arbitrary unitary representations of that cover.
The uniform angle estimate is proved downstream in PrimeFiveCoverRootAngles.
-/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor PrimeFiveRankThreeCover

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def coverRootAverage (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) : H →L[ℂ] H :=
  finiteSubgroupAverage ρ (rootSubgroup d (cyclicRoot c))

def coverPairAverage (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) : H →L[ℂ] H :=
  finiteSubgroupAverage ρ (pairSubgroup d (cyclicRoot c))

theorem cover_invariants_eq_cyclic_invariants (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) :
    hilbertUnitaryInvariants ρ =
      ⨅ c : Axis, hilbertUnitaryInvariants (ρ.comp (rootSubgroup d (cyclicRoot c)).subtype) :=
  hilbertUnitaryInvariants_of_iSup ρ _ (cyclicRootSubgroups_generate d)

theorem coverRootAverage_mul_pairAverage (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    coverRootAverage d ρ c * coverPairAverage d ρ c = coverPairAverage d ρ c := by
  apply finiteSubgroupAverage_mul_of_le
  rw [cyclic_pairSubgroup]
  exact le_sup_left

theorem coverNextRootAverage_mul_pairAverage (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    coverRootAverage d ρ (finRotate 3 c) * coverPairAverage d ρ c = coverPairAverage d ρ c := by
  apply finiteSubgroupAverage_mul_of_le
  rw [cyclic_pairSubgroup]
  exact le_sup_right

variable [CompleteSpace H]

theorem coverRootAverage_isStarProjection (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    IsStarProjection (coverRootAverage d ρ c) := finiteSubgroupAverage_isStarProjection ρ _

theorem coverPairAverage_isStarProjection (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    IsStarProjection (coverPairAverage d ρ c) := finiteSubgroupAverage_isStarProjection ρ _

theorem coverPairAverage_mul_rootAverage (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    coverPairAverage d ρ c * coverRootAverage d ρ c = coverPairAverage d ρ c := by
  apply finiteSubgroupAverage_mul_of_ge
  rw [cyclic_pairSubgroup]
  exact le_sup_left

theorem coverPairAverage_mul_nextRootAverage (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    coverPairAverage d ρ c * coverRootAverage d ρ (finRotate 3 c) = coverPairAverage d ρ c := by
  apply finiteSubgroupAverage_mul_of_ge
  rw [cyclic_pairSubgroup]
  exact le_sup_right

end ThomGame.Analysis
