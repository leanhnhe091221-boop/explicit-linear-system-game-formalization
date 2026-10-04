module

public import ThomGame.Analysis.CentralCharacterCancellation
public import ThomGame.Analysis.FiniteAverageSupportBound

/-! Quantitative root-pair estimates on each nontrivial commutator-character component. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem centralCharacter_sandwich_bound (hC : _root_.commutator G ≤ Subgroup.center G)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (κ : _root_.commutator G →* ℂ)
    (A B : Subgroup G) [Finite A] [Finite B] (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x)
    (hA : x ∈ hilbertUnitaryInvariants (ρ.comp A.subtype)) :
    ‖finiteSubgroupAverage ρ A (finiteSubgroupAverage ρ B x)‖ ≤
      ((commutatorCharacterAnnihilator hC κ A B).index : ℝ)⁻¹ * ‖x‖ := by
  let := Fintype.ofFinite B
  apply finiteAverage_support_bound (ρ.comp B.subtype) (finiteSubgroupAverage ρ A)
    (commutatorCharacterAnnihilator hC κ A B) x
  · intro b hb
    exact finiteAverage_translate_vanishes hC ρ κ A B x hx hA b hb
  · intro b hb
    change ‖finiteSubgroupAverage ρ A (ρ b.val x)‖ ≤ ‖x‖
    rw [finiteAverage_translate_fixed hC ρ κ A B x hx hA b hb, (ρ b.val).norm_map]

theorem centralCharacter_average_norm_sq (hC : _root_.commutator G ≤ Subgroup.center G)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (κ : _root_.commutator G →* ℂ)
    (A B : Subgroup G) [Finite A] [Finite B] (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x)
    (hA : x ∈ hilbertUnitaryInvariants (ρ.comp A.subtype)) :
    ‖finiteSubgroupAverage ρ B x‖ ^ 2 ≤
      ((commutatorCharacterAnnihilator hC κ A B).index : ℝ)⁻¹ * ‖x‖ ^ 2 := by
  calc
    _ = (inner ℂ x (finiteSubgroupAverage ρ B x)).re := finiteSubgroupAverage_norm_sq ρ B x
    _ = (inner ℂ x (finiteSubgroupAverage ρ A (finiteSubgroupAverage ρ B x))).re :=
      (congrArg Complex.re (finiteSubgroupAverage_inner_fixed ρ A x hA _)).symm
    _ ≤ ‖x‖ * ‖finiteSubgroupAverage ρ A (finiteSubgroupAverage ρ B x)‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖x‖ * (((commutatorCharacterAnnihilator hC κ A B).index : ℝ)⁻¹ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (centralCharacter_sandwich_bound hC ρ κ A B x hx hA) (norm_nonneg x)
    _ = _ := by rw [mul_left_comm, ← pow_two]

theorem centralCharacter_prime_angle_sq {p : Nat} [Fact p.Prime]
    (hC : _root_.commutator G ≤ Subgroup.center G)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (κ : _root_.commutator G →* ℂ) (hκ : κ ≠ 1)
    (A B : Subgroup G) [Finite A] [Finite B] (hgen : A ⊔ B = ⊤)
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, Commute a a') (hBcomm : ∀ b ∈ B, ∀ b' ∈ B, Commute b b')
    (hB : IsPGroup p B) (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x)
    (hAx : x ∈ hilbertUnitaryInvariants (ρ.comp A.subtype)) :
    ‖finiteSubgroupAverage ρ B x‖ ^ 2 ≤ (p : ℝ)⁻¹ * ‖x‖ ^ 2 := by
  have hindex := commutatorCharacterAnnihilator_index hC κ A B hB
    (commutatorCharacterAnnihilator_ne_top hC A B hgen hAcomm hBcomm κ hκ)
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hle : (p : ℝ) ≤ (commutatorCharacterAnnihilator hC κ A B).index := by exact_mod_cast hindex
  exact (centralCharacter_average_norm_sq hC ρ κ A B x hx hAx).trans
    (mul_le_mul_of_nonneg_right (inv_anti₀ hp hle) (sq_nonneg ‖x‖))

end ThomGame.Analysis
