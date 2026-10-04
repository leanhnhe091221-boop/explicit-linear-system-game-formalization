module

public import ThomGame.Analysis.FiniteClassTwoAngle
public import ThomGame.Analysis.SubgroupAverageRestriction
public import ThomGame.Analysis.PrimeFiveCoverRootAverages

/-! The genuine uniform root-pair angle estimate for every prime-five cover representation. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor PrimeFiveRankThreeCover
open scoped IsMulCommutative

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem subgroupOf_commutes {G : Type*} [Group G] (K L : Subgroup G) [IsMulCommutative K] :
    ∀ a ∈ K.subgroupOf L, ∀ b ∈ K.subgroupOf L, Commute a b := by
  intro a ha b hb
  change a * b = b * a
  apply Subtype.ext
  change a.val * b.val = b.val * a.val
  exact congrArg (fun k : K => k.val) (mul_comm (⟨a.val, ha⟩ : K) ⟨b.val, hb⟩)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coverRootAverage_pair_angle (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    ‖coverRootAverage d ρ c * coverRootAverage d ρ (finRotate 3 c) - coverPairAverage d ρ c‖ ≤
      (Real.sqrt 5)⁻¹ := by
  let P := pairSubgroup d (cyclicRoot c)
  let K := rootSubgroup d (cyclicRoot c)
  let L := rootSubgroup d (cyclicRoot (finRotate 3 c))
  have hP : P = K ⊔ L := cyclic_pairSubgroup d c
  have hK : K ≤ P := hP ▸ le_sup_left
  have hL : L ≤ P := hP ▸ le_sup_right
  have hgen : L.subgroupOf P ⊔ K.subgroupOf P = ⊤ := by
    rw [sup_comm, ← Subgroup.subgroupOf_sup hK hL, ← hP, Subgroup.subgroupOf_self]
  have hpK : IsPGroup 5 (K.subgroupOf P) :=
    (pairSubgroup_isPGroup d (cyclicRoot c)).to_subgroup (K.subgroupOf P)
  have h := finiteClassTwo_pair_angle
    ((canonicalModel d).pairSubgroup_commutator_le_center (cyclicRoot c))
    (ρ.comp P.subtype) (L.subgroupOf P) (K.subgroupOf P) hgen
    (subgroupOf_commutes L P) (subgroupOf_commutes K P) hpK
  rw [finiteSubgroupAverage_subgroupOf ρ hK, finiteSubgroupAverage_subgroupOf ρ hL,
    finiteSubgroupAverage_restrict_top] at h
  exact h

theorem coverRootAverage_reverse_pair_angle (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    ‖coverRootAverage d ρ (finRotate 3 c) * coverRootAverage d ρ c - coverPairAverage d ρ c‖ ≤
      (Real.sqrt 5)⁻¹ := by
  have hstar : star (coverRootAverage d ρ c * coverRootAverage d ρ (finRotate 3 c) - coverPairAverage d ρ c) =
      coverRootAverage d ρ (finRotate 3 c) * coverRootAverage d ρ c - coverPairAverage d ρ c := by
    rw [star_sub, star_mul, (coverRootAverage_isStarProjection d ρ c).isSelfAdjoint.star_eq,
      (coverRootAverage_isStarProjection d ρ (finRotate 3 c)).isSelfAdjoint.star_eq,
      (coverPairAverage_isStarProjection d ρ c).isSelfAdjoint.star_eq]
  rw [← hstar, ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
  exact coverRootAverage_pair_angle d ρ c

theorem primeFive_angle_lt_half : (Real.sqrt 5)⁻¹ < (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ) < Real.sqrt 5 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    have hn := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) h2

theorem coverRootAverage_pair_angle_lt_half (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H)) (c : Axis) :
    ‖coverRootAverage d ρ c * coverRootAverage d ρ (finRotate 3 c) - coverPairAverage d ρ c‖ < (1 / 2 : ℝ) :=
  (coverRootAverage_pair_angle d ρ c).trans_lt primeFive_angle_lt_half

end ThomGame.Analysis
