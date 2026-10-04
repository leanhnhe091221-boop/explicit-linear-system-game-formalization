module

public import ThomGame.Groups.FinitePrimeFivePairStructure
public import ThomGame.Analysis.FiniteClassTwoAngle
public import ThomGame.Analysis.StarProjectionPairGap

/-! The exact finite pair polynomial with rational gap 11/20. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators
open FinitePrimeFivePair

variable {r : ℕ}

def pairLeftEquiv : (Fin r → ZMod 5) ≃ leftSubgroup r :=
  Equiv.ofBijective (fun α => ⟨leftVector α, leftVector_mem α⟩) (by
    constructor
    · intro α β he
      exact congrArg FinitePrimeFivePair.left (congrArg Subtype.val he)
    · rintro ⟨g, hg⟩
      obtain ⟨α, rfl⟩ := hg
      exact ⟨α.toAdd, rfl⟩)

def pairRightEquiv : (Fin r → ZMod 5) ≃ rightSubgroup r :=
  Equiv.ofBijective (fun α => ⟨rightVector α, rightVector_mem α⟩) (by
    constructor
    · intro α β he
      exact congrArg FinitePrimeFivePair.right (congrArg Subtype.val he)
    · rintro ⟨g, hg⟩
      obtain ⟨α, rfl⟩ := hg
      exact ⟨α.toAdd, rfl⟩)

theorem primeFive_angle_le_nine_twentieths : (Real.sqrt 5)⁻¹ ≤ (9/20:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num)
  rw [← one_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def pairLeftAverage (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  finiteSubgroupAverage ρ (leftSubgroup r)
def pairRightAverage (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  finiteSubgroupAverage ρ (rightSubgroup r)

theorem finitePair_residual_polynomial (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) :
    (11/20:ℝ) • ((1 - pairLeftAverage ρ) + (1 - pairRightAverage ρ)) ≤
      ((1 - pairLeftAverage ρ) + (1 - pairRightAverage ρ)) *
        ((1 - pairLeftAverage ρ) + (1 - pairRightAverage ρ)) := by
  have ha := finiteClassTwo_pair_angle (p := 5) commutator_le_center ρ
    (rightSubgroup r) (leftSubgroup r) (by rw [sup_comm, left_sup_right])
    right_commutative left_commutative (FinitePrimeFivePair.isPGroup.to_subgroup _)
  have hh := starProjection_pair_residual_polynomial
    (finiteSubgroupAverage_isStarProjection ρ (leftSubgroup r))
    (finiteSubgroupAverage_isStarProjection ρ (rightSubgroup r))
    (finiteSubgroupAverage_isStarProjection ρ ⊤)
    (finiteSubgroupAverage_mul_of_le ρ le_top) (finiteSubgroupAverage_mul_of_le ρ le_top)
    (9/20) (by norm_num) (ha.trans primeFive_angle_le_nine_twentieths)
  norm_num only [show (1:ℝ)-9/20=11/20 by norm_num] at hh
  exact hh

theorem finiteSubgroupAverage_equiv_apply {F I : Type*} [Group F] [Fintype I]
    (ρ : F →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup F) [Finite K] (e : I ≃ K) (x : H) :
    finiteSubgroupAverage ρ K x = (Fintype.card I : ℂ)⁻¹ • ∑ i, ρ (e i).val x := by
  letI := Fintype.ofFinite K
  rw [finiteSubgroupAverage, finiteUnitaryAverage_apply]
  rw [← Fintype.card_congr e]
  congr 1
  exact (Equiv.sum_comp e (fun k : K => ρ k.val x)).symm

theorem pairLeftAverage_apply (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    pairLeftAverage ρ x = (5 ^ r : ℂ)⁻¹ • ∑ α : Fin r → ZMod 5, ρ (leftVector α) x := by
  rw [pairLeftAverage, finiteSubgroupAverage_equiv_apply ρ _ pairLeftEquiv]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rfl

theorem pairRightAverage_apply (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    pairRightAverage ρ x = (5 ^ r : ℂ)⁻¹ • ∑ α : Fin r → ZMod 5, ρ (rightVector α) x := by
  rw [pairRightAverage, finiteSubgroupAverage_equiv_apply ρ _ pairRightEquiv]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rfl

end ThomGame.Analysis
