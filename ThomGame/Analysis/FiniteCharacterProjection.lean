module

public import ThomGame.Analysis.FiniteCharacterAverage

/-! The Fourier averages are mutually orthogonal projections on actual character spaces. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {C H : Type*} [CommGroup C] [Fintype C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteCharacterSpace (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C) : Submodule ℂ H where
  carrier := {x | ∀ c, ρ c x = finiteGroupCharacterHom χ c • x}
  zero_mem' := by intro c; simp
  add_mem' := by intro x y hx hy c; rw [map_add, hx c, hy c, smul_add]
  smul_mem' := by intro a x hx c; rw [map_smul, hx c, smul_comm]

omit [Fintype C] in
theorem finiteCharacterSpace_isClosed (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C) :
    IsClosed (finiteCharacterSpace ρ χ : Set H) := by
  change IsClosed {x : H | ∀ c, ρ c x = finiteGroupCharacterHom χ c • x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun c => isClosed_eq (ρ c).continuous (continuous_const.smul continuous_id))

instance [CompleteSpace H] (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C) :
    CompleteSpace (finiteCharacterSpace ρ χ) := (finiteCharacterSpace_isClosed ρ χ).completeSpace_coe

theorem finiteCharacter_inner_eigen_left (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C)
    (x : H) (hx : x ∈ finiteCharacterSpace ρ χ) (c : C) (y : H) :
    inner ℂ x (ρ c y) = finiteGroupCharacterHom χ c * inner ℂ x y := by
  have h := (ρ c).inner_map_map x y
  rw [hx c, inner_smul_left, finiteGroupCharacterHom_conj] at h
  calc
    inner ℂ x (ρ c y) = finiteGroupCharacterHom χ c *
        ((finiteGroupCharacterHom χ c)⁻¹ * inner ℂ x (ρ c y)) := by
      rw [mul_inv_cancel_left₀ (finiteGroupCharacterHom_ne_zero χ c)]
    _ = _ := by rw [h]

theorem finiteCharacterSpace_orthogonal (ρ : C →* (H ≃ₗᵢ[ℂ] H))
    {χ ψ : FiniteGroupCharacter C} (hχψ : χ ≠ ψ) (x y : H)
    (hx : x ∈ finiteCharacterSpace ρ χ) (hy : y ∈ finiteCharacterSpace ρ ψ) : inner ℂ x y = 0 := by
  by_contra hxy
  apply hχψ
  apply finiteGroupCharacterHom_injective
  apply MonoidHom.ext
  intro c
  have h := finiteCharacter_inner_eigen_left ρ χ x hx c y
  rw [hy c, inner_smul_right] at h
  exact (mul_right_cancel₀ hxy h).symm

theorem finiteCharacterAverage_inner_eigen (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C)
    (x : H) (hx : x ∈ finiteCharacterSpace ρ χ) (y : H) :
    inner ℂ x (finiteCharacterAverage ρ χ y) = inner ℂ x y := by
  have hc : (Fintype.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  rw [finiteCharacterAverage_apply, inner_smul_right, inner_sum]
  simp only [inner_smul_right, finiteCharacter_inner_eigen_left ρ χ x hx,
    finiteGroupCharacterHom_inv, inv_mul_cancel_left₀ (finiteGroupCharacterHom_ne_zero χ _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hc]

theorem finiteCharacterAverage_residual_orthogonal (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C)
    (x : H) : x - finiteCharacterAverage ρ χ x ∈ (finiteCharacterSpace ρ χ)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  rw [inner_sub_right, finiteCharacterAverage_inner_eigen ρ χ y hy, sub_self]

theorem finiteCharacterAverage_orthogonal (ρ : C →* (H ≃ₗᵢ[ℂ] H))
    {χ ψ : FiniteGroupCharacter C} (hχψ : χ ≠ ψ) (x y : H) :
    inner ℂ (finiteCharacterAverage ρ χ x) (finiteCharacterAverage ρ ψ y) = 0 :=
  finiteCharacterSpace_orthogonal ρ hχψ _ _ (finiteCharacterAverage_eigen ρ χ x)
    (finiteCharacterAverage_eigen ρ ψ y)

variable [CompleteSpace H]

theorem finiteCharacterAverage_eq_projection (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C) :
    finiteCharacterAverage ρ χ = (finiteCharacterSpace ρ χ).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact ((finiteCharacterSpace ρ χ).eq_starProjection_of_mem_orthogonal
    (finiteCharacterAverage_eigen ρ χ x) (finiteCharacterAverage_residual_orthogonal ρ χ x)).symm

theorem finiteCharacterAverage_isStarProjection (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C) :
    IsStarProjection (finiteCharacterAverage ρ χ) := by
  rw [finiteCharacterAverage_eq_projection]
  exact isStarProjection_starProjection

end ThomGame.Analysis
