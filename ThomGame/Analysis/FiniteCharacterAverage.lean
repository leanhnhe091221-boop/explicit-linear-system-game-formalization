module

public import ThomGame.Analysis.FiniteGroupCharacters
public import ThomGame.Analysis.FiniteUnitaryAverage

/-! Actual Fourier projections for a finite abelian group acting unitarily. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {C H : Type*} [CommGroup C] [Fintype C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteCharacterAverage (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C) : H →L[ℂ] H :=
  (Fintype.card C : ℂ)⁻¹ • ∑ c : C, finiteGroupCharacterHom χ c⁻¹ • (ρ c : H →L[ℂ] H)

theorem finiteCharacterAverage_apply (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C) (x : H) :
    finiteCharacterAverage ρ χ x =
      (Fintype.card C : ℂ)⁻¹ • ∑ c : C, finiteGroupCharacterHom χ c⁻¹ • ρ c x := by
  simp only [finiteCharacterAverage, smul_apply, sum_apply]
  rfl

theorem finiteCharacterAverage_trivial (ρ : C →* (H ≃ₗᵢ[ℂ] H)) :
    finiteCharacterAverage ρ 0 = finiteUnitaryAverage ρ := by
  simp only [finiteCharacterAverage, finiteGroupCharacterHom_trivial, one_smul, finiteUnitaryAverage]

theorem finiteCharacterAverage_eigen (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C)
    (x : H) (c : C) :
    ρ c (finiteCharacterAverage ρ χ x) = finiteGroupCharacterHom χ c • finiteCharacterAverage ρ χ x := by
  rw [finiteCharacterAverage_apply, map_smul, map_sum, smul_comm]
  congr 1
  simp only [map_smul, ← hilbertUnitary_apply_mul, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulLeft c)
    (fun a : C => finiteGroupCharacterHom χ c • (finiteGroupCharacterHom χ a⁻¹ • ρ a x))
  rw [← h]
  apply Finset.sum_congr rfl
  intro a _
  change finiteGroupCharacterHom χ a⁻¹ • ρ (c * a) x =
    finiteGroupCharacterHom χ c • (finiteGroupCharacterHom χ (c * a)⁻¹ • ρ (c * a) x)
  rw [smul_smul, mul_inv_rev, (finiteGroupCharacterHom χ).map_mul a⁻¹ c⁻¹,
    finiteGroupCharacterHom_inv χ c, mul_left_comm,
    mul_inv_cancel₀ (finiteGroupCharacterHom_ne_zero χ c), mul_one]

theorem finiteCharacterAverage_of_eigen (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C)
    (x : H) (hx : ∀ c, ρ c x = finiteGroupCharacterHom χ c • x) : finiteCharacterAverage ρ χ x = x := by
  have hc : (Fintype.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  rw [finiteCharacterAverage_apply]
  simp only [hx, finiteGroupCharacterHom_inv, smul_smul,
    inv_mul_cancel₀ (finiteGroupCharacterHom_ne_zero χ _), one_smul,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem finiteCharacterAverage_sum (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    ∑ χ : FiniteGroupCharacter C, finiteCharacterAverage ρ χ x = x := by
  classical
  have hc : (Fintype.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  simp only [finiteCharacterAverage_apply, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, finiteGroupCharacterHom_sum, inv_eq_one,
    ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    map_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rfl

theorem finiteCharacterAverage_commute (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (χ : FiniteGroupCharacter C)
    (T : H →L[ℂ] H) (hT : ∀ c x, T (ρ c x) = ρ c (T x)) (x : H) :
    T (finiteCharacterAverage ρ χ x) = finiteCharacterAverage ρ χ (T x) := by
  simp only [finiteCharacterAverage_apply, map_smul, map_sum, hT]

end ThomGame.Analysis
