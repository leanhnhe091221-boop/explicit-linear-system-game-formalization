module

public import ThomGame.Analysis.FiniteUnitaryEnergy

/-! Actual orthogonal averages over finite subgroups, including nested subgroups. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteSubgroupAverage (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup G) [Finite K] : H →L[ℂ] H :=
  letI := Fintype.ofFinite K
  finiteUnitaryAverage (ρ.comp K.subtype)

theorem finiteSubgroupAverage_invariant (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup G) [Finite K] (x : H) :
    finiteSubgroupAverage ρ K x ∈ hilbertUnitaryInvariants (ρ.comp K.subtype) := by
  let := Fintype.ofFinite K
  exact finiteUnitaryAverage_invariant (ρ.comp K.subtype) x

theorem finiteSubgroupAverage_of_invariant (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup G) [Finite K] (x : H)
    (hx : x ∈ hilbertUnitaryInvariants (ρ.comp K.subtype)) : finiteSubgroupAverage ρ K x = x := by
  let := Fintype.ofFinite K
  exact finiteUnitaryAverage_of_invariant (ρ.comp K.subtype) x hx

theorem hilbertUnitaryInvariants_subgroup_mono (ρ : G →* (H ≃ₗᵢ[ℂ] H)) {K L : Subgroup G} (hKL : K ≤ L) :
    hilbertUnitaryInvariants (ρ.comp L.subtype) ≤ hilbertUnitaryInvariants (ρ.comp K.subtype) := by
  intro x hx k
  exact hx ⟨k.val, hKL k.property⟩

theorem finiteSubgroupAverage_mul_of_le (ρ : G →* (H ≃ₗᵢ[ℂ] H)) {K L : Subgroup G}
    [Finite K] [Finite L] (hKL : K ≤ L) :
    finiteSubgroupAverage ρ K * finiteSubgroupAverage ρ L = finiteSubgroupAverage ρ L := by
  apply ContinuousLinearMap.ext
  intro x
  exact finiteSubgroupAverage_of_invariant ρ K _
    (hilbertUnitaryInvariants_subgroup_mono ρ hKL (finiteSubgroupAverage_invariant ρ L x))

theorem finiteSubgroupAverage_energy (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup G) [Finite K] (x : H) :
    letI := Fintype.ofFinite K
    ∑ g : K, ‖ρ g.val x - x‖ ^ 2 = (2 * (Nat.card K : ℝ)) * ‖x - finiteSubgroupAverage ρ K x‖ ^ 2 := by
  let := Fintype.ofFinite K
  simpa only [Nat.card_eq_fintype_card, finiteSubgroupAverage, MonoidHom.comp_apply,
    Subgroup.coe_subtype] using
    finiteUnitary_energy_identity (ρ.comp K.subtype) x

variable [CompleteSpace H]

theorem finiteSubgroupAverage_eq_projection (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup G) [Finite K] :
    finiteSubgroupAverage ρ K = (hilbertUnitaryInvariants (ρ.comp K.subtype)).starProjection := by
  let := Fintype.ofFinite K
  exact finiteUnitaryAverage_eq_projection (ρ.comp K.subtype)

theorem finiteSubgroupAverage_isStarProjection (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup G) [Finite K] :
    IsStarProjection (finiteSubgroupAverage ρ K) := by
  rw [finiteSubgroupAverage_eq_projection]
  exact isStarProjection_starProjection

theorem finiteSubgroupAverage_norm_le (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup G) [Finite K] :
    ‖finiteSubgroupAverage ρ K‖ ≤ 1 := by
  rw [finiteSubgroupAverage_eq_projection]
  exact Submodule.starProjection_norm_le _

theorem finiteSubgroupAverage_mul_of_ge (ρ : G →* (H ≃ₗᵢ[ℂ] H)) {K L : Subgroup G}
    [Finite K] [Finite L] (hKL : K ≤ L) :
    finiteSubgroupAverage ρ L * finiteSubgroupAverage ρ K = finiteSubgroupAverage ρ L := by
  have h := congrArg star (finiteSubgroupAverage_mul_of_le ρ hKL)
  simpa only [star_mul, (finiteSubgroupAverage_isStarProjection ρ K).isSelfAdjoint.star_eq,
    (finiteSubgroupAverage_isStarProjection ρ L).isSelfAdjoint.star_eq] using h

end ThomGame.Analysis
