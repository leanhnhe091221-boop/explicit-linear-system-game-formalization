module

public import ThomGame.Analysis.CentralCharacterTrivialPart
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The uniform two-subgroup angle bound for finite class-two groups. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped IsMulCommutative

variable {G H : Type*} [Group G] [Finite G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finiteClassTwo_pair_angle_sq {p : Nat} [Fact p.Prime]
    (hC : _root_.commutator G ≤ Subgroup.center G) (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A B : Subgroup G) (hgen : A ⊔ B = ⊤)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, Commute a a') (hB : ∀ b ∈ B, ∀ b' ∈ B, Commute b b')
    (hpB : IsPGroup p B) (x : H) :
    ‖(finiteSubgroupAverage ρ B * finiteSubgroupAverage ρ A - finiteSubgroupAverage ρ ⊤) x‖ ^ 2 ≤
      (p : ℝ)⁻¹ * ‖x‖ ^ 2 := by
  let : IsMulCommutative (_root_.commutator G) := ⟨⟨fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.mp (hC a.property) b.val).symm)⟩⟩
  let := Fintype.ofFinite (_root_.commutator G)
  let τ := ρ.comp (_root_.commutator G).subtype
  let T := finiteSubgroupAverage ρ B * finiteSubgroupAverage ρ A - finiteSubgroupAverage ρ ⊤
  apply finiteCharacterDecomposition_bound τ T _ (p : ℝ)⁻¹ _ x
  · intro z y
    change finiteSubgroupAverage ρ B (finiteSubgroupAverage ρ A (ρ z.val y)) -
        finiteSubgroupAverage ρ ⊤ (ρ z.val y) =
      ρ z.val (finiteSubgroupAverage ρ B (finiteSubgroupAverage ρ A y) - finiteSubgroupAverage ρ ⊤ y)
    rw [map_sub, finiteSubgroupAverage_central_commute ρ A z.val (hC z.property),
      finiteSubgroupAverage_central_commute ρ B z.val (hC z.property),
      finiteSubgroupAverage_central_commute ρ ⊤ z.val (hC z.property)]
  · intro χ y hy
    let κ := finiteGroupCharacterHom χ
    have hchar : ∀ z : _root_.commutator G, ρ z.val y = κ z • y := hy
    change ‖finiteSubgroupAverage ρ B (finiteSubgroupAverage ρ A y) - finiteSubgroupAverage ρ ⊤ y‖ ^ 2 ≤ _
    by_cases hκ : κ = 1
    · have htrivial : ∀ z : _root_.commutator G, ρ z.val y = y := by
        simpa only [hκ, MonoidHom.one_apply, one_smul] using hchar
      rw [finiteAverage_trivial_character_product hC ρ A B hgen y htrivial, sub_self, norm_zero, zero_pow (by decide)]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sq_nonneg ‖y‖)
    · rw [finiteAverage_global_eq_zero_of_nontrivial_character hC ρ κ hκ y hchar, sub_zero]
      exact (centralCharacter_prime_angle_sq hC ρ κ hκ A B hgen hA hB hpB _
        (finiteSubgroupAverage_preserves_central_character hC ρ κ A y hchar)
        (finiteSubgroupAverage_invariant ρ A y)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
            (finiteSubgroupAverage_apply_norm_le ρ A y) 2) (inv_nonneg.mpr (Nat.cast_nonneg _)))

theorem finiteClassTwo_pair_angle {p : Nat} [Fact p.Prime]
    (hC : _root_.commutator G ≤ Subgroup.center G) (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A B : Subgroup G) (hgen : A ⊔ B = ⊤)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, Commute a a') (hB : ∀ b ∈ B, ∀ b' ∈ B, Commute b b')
    (hpB : IsPGroup p B) :
    ‖finiteSubgroupAverage ρ B * finiteSubgroupAverage ρ A - finiteSubgroupAverage ρ ⊤‖ ≤
      (Real.sqrt p)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro x
  have hsq := finiteClassTwo_pair_angle_sq hC ρ A B hgen hA hB hpB x
  have hsqrt : ((Real.sqrt (p : ℝ))⁻¹ * ‖x‖) ^ 2 = (p : ℝ)⁻¹ * ‖x‖ ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (norm_nonneg _))).mp
    (hsqrt ▸ hsq)

end ThomGame.Analysis
