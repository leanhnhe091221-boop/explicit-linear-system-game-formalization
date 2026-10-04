module

public import ThomGame.Analysis.FiniteIsometryAverage
public import ThomGame.Analysis.FinitePrimeFivePairPolynomial

/-! The two symmetrized root averages are close to exact subgroup projections
inside the finite regular dilation. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators
open FinitePrimeFivePair
variable {r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem leftVector_neg (α : Fin r → ZMod 5) : leftVector (-α) = (leftVector α)⁻¹ := by
  ext <;> simp [leftVector]
theorem rightVector_neg (α : Fin r → ZMod 5) : rightVector (-α) = (rightVector α)⁻¹ := by
  ext <;> simp [rightVector]

theorem pairLeftAverage_eq_average (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) :
    pairLeftAverage ρ = finiteIsometryAverage (fun α : Fin r → ZMod 5 => ρ (leftVector α)) := by
  ext x
  rw [pairLeftAverage_apply, finiteIsometryAverage_apply]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

theorem pairRightAverage_eq_average (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) :
    pairRightAverage ρ = finiteIsometryAverage (fun α : Fin r → ZMod 5 => ρ (rightVector α)) := by
  ext x
  rw [pairRightAverage_apply, finiteIsometryAverage_apply]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

theorem pairLeftAverage_eq_inv_average (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) :
    pairLeftAverage ρ = finiteIsometryAverage (fun α : Fin r → ZMod 5 => ρ (leftVector α)⁻¹) := by
  rw [pairLeftAverage_eq_average]
  ext x
  simp only [finiteIsometryAverage_apply]
  congr 1
  simp only [← leftVector_neg]
  exact (Equiv.sum_comp (Equiv.neg _) (fun α : Fin r → ZMod 5 => ρ (leftVector α) x)).symm

theorem pairRightAverage_eq_inv_average (ρ : FinitePrimeFivePair r →* (H ≃ₗᵢ[ℂ] H)) :
    pairRightAverage ρ = finiteIsometryAverage (fun α : Fin r → ZMod 5 => ρ (rightVector α)⁻¹) := by
  rw [pairRightAverage_eq_average]
  ext x
  simp only [finiteIsometryAverage_apply]
  congr 1
  simp only [← rightVector_neg]
  exact (Equiv.sum_comp (Equiv.neg _) (fun α : Fin r → ZMod 5 => ρ (rightVector α) x)).symm

theorem finitePair_left_average_intertwining (U : FinitePrimeFivePair r → H ≃ₗᵢ[ℂ] H)
    (x : H) {η : ℝ} (hη : 0 ≤ η)
    (hmul : ∀ g k, ‖U g (U k x) - U (g*k) x‖ ≤ η)
    (hinv : ∀ g k, ‖U g ((U k).symm x) - U (g*k⁻¹) x‖ ≤ η) :
    ‖finiteDilation U (finiteIsometrySymmetricAverage (fun α => U (leftVector α)) x) -
      pairLeftAverage finiteRegularAction (finiteDilation U x)‖ ≤ η := by
  apply isometry_symmetric_average_intertwining
  · rw [pairLeftAverage_eq_average]
    exact finiteDilation_average U leftVector x hη (fun g i => hmul g _)
  · rw [pairLeftAverage_eq_inv_average]
    apply isometry_average_intertwining
    intro α
    exact finiteDilation_intertwining_to U (leftVector α)⁻¹ (U (leftVector α)).symm x hη
      (fun g => hinv g _)

theorem finitePair_right_average_intertwining (U : FinitePrimeFivePair r → H ≃ₗᵢ[ℂ] H)
    (x : H) {η : ℝ} (hη : 0 ≤ η)
    (hmul : ∀ g k, ‖U g (U k x) - U (g*k) x‖ ≤ η)
    (hinv : ∀ g k, ‖U g ((U k).symm x) - U (g*k⁻¹) x‖ ≤ η) :
    ‖finiteDilation U (finiteIsometrySymmetricAverage (fun α => U (rightVector α)) x) -
      pairRightAverage finiteRegularAction (finiteDilation U x)‖ ≤ η := by
  apply isometry_symmetric_average_intertwining
  · rw [pairRightAverage_eq_average]
    exact finiteDilation_average U rightVector x hη (fun g i => hmul g _)
  · rw [pairRightAverage_eq_inv_average]
    apply isometry_average_intertwining
    intro α
    exact finiteDilation_intertwining_to U (rightVector α)⁻¹ (U (rightVector α)).symm x hη
      (fun g => hinv g _)

end ThomGame.Analysis
