module

public import ThomGame.Analysis.FiniteCharacterProjection
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-! Finite orthogonal character decomposition, including norm bounds for commuting operators. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {C H : Type*} [CommGroup C] [Fintype C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finiteCharacterSpace_orthogonalFamily (ρ : C →* (H ≃ₗᵢ[ℂ] H)) :
    OrthogonalFamily ℂ (fun χ : FiniteGroupCharacter C => finiteCharacterSpace ρ χ)
      (fun χ => (finiteCharacterSpace ρ χ).subtypeₗᵢ) := by
  intro χ ψ hχψ x y
  exact finiteCharacterSpace_orthogonal ρ hχψ x.val y.val x.property y.property

theorem finiteCharacterSpace_norm_sum (ρ : C →* (H ≃ₗᵢ[ℂ] H))
    (x : FiniteGroupCharacter C → H) (hx : ∀ χ, x χ ∈ finiteCharacterSpace ρ χ) :
    ‖∑ χ, x χ‖ ^ 2 = ∑ χ, ‖x χ‖ ^ 2 :=
  (finiteCharacterSpace_orthogonalFamily ρ).norm_sum (fun χ => ⟨x χ, hx χ⟩) Finset.univ

theorem finiteCharacterAverage_norm_decomposition (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    ∑ χ : FiniteGroupCharacter C, ‖finiteCharacterAverage ρ χ x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [← finiteCharacterSpace_norm_sum ρ _ (fun χ => finiteCharacterAverage_eigen ρ χ x),
    finiteCharacterAverage_sum]

omit [Fintype C] in
theorem finiteCharacterSpace_map_mem (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (T : H →L[ℂ] H)
    (hT : ∀ c x, T (ρ c x) = ρ c (T x)) (χ : FiniteGroupCharacter C)
    (x : H) (hx : x ∈ finiteCharacterSpace ρ χ) : T x ∈ finiteCharacterSpace ρ χ := by
  intro c
  rw [← hT c x, hx c, map_smul]

theorem finiteCharacterDecomposition_bound (ρ : C →* (H ≃ₗᵢ[ℂ] H)) (T : H →L[ℂ] H)
    (hT : ∀ c x, T (ρ c x) = ρ c (T x)) (b : ℝ)
    (hbound : ∀ χ x, x ∈ finiteCharacterSpace ρ χ → ‖T x‖ ^ 2 ≤ b * ‖x‖ ^ 2) (x : H) :
    ‖T x‖ ^ 2 ≤ b * ‖x‖ ^ 2 := by
  calc
    ‖T x‖ ^ 2 = ‖∑ χ : FiniteGroupCharacter C, T (finiteCharacterAverage ρ χ x)‖ ^ 2 := by
      rw [← map_sum, finiteCharacterAverage_sum]
    _ = ∑ χ : FiniteGroupCharacter C, ‖T (finiteCharacterAverage ρ χ x)‖ ^ 2 :=
      finiteCharacterSpace_norm_sum ρ _ (fun χ => finiteCharacterSpace_map_mem ρ T hT χ _
        (finiteCharacterAverage_eigen ρ χ x))
    _ ≤ ∑ χ : FiniteGroupCharacter C, b * ‖finiteCharacterAverage ρ χ x‖ ^ 2 :=
      Finset.sum_le_sum (fun χ _ => hbound χ _ (finiteCharacterAverage_eigen ρ χ x))
    _ = b * ‖x‖ ^ 2 := by rw [← Finset.mul_sum, finiteCharacterAverage_norm_decomposition]

end ThomGame.Analysis
