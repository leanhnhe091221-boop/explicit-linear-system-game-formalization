module

public import ThomGame.Analysis.FiniteRegularDilation

/-! Finite averages of isometries and transfer through the regular dilation. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators
variable {I H K : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def finiteIsometryAverage (U : I → H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  (Fintype.card I : ℂ)⁻¹ • ∑ i, (U i : H →L[ℂ] H)

theorem finiteIsometryAverage_apply (U : I → H ≃ₗᵢ[ℂ] H) (x : H) :
    finiteIsometryAverage U x = (Fintype.card I : ℂ)⁻¹ • ∑ i, U i x := by
  simp only [finiteIsometryAverage, smul_apply, sum_apply]
  rfl

theorem norm_finite_average_le (f : I → K) {η : ℝ} (hf : ∀ i, ‖f i‖ ≤ η) :
    ‖(Fintype.card I : ℂ)⁻¹ • ∑ i, f i‖ ≤ η := by
  have hN : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, ‖f i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN.le)
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ _i : I, η :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hf i)) (inv_nonneg.mpr hN.le)
    _ = η := by simp [ne_of_gt hN]

theorem finiteIsometryAverage_norm_apply (U : I → H ≃ₗᵢ[ℂ] H) (x : H) :
    ‖finiteIsometryAverage U x‖ ≤ ‖x‖ := by
  rw [finiteIsometryAverage_apply]
  exact norm_finite_average_le _ (fun i => le_of_eq ((U i).norm_map x))

theorem finiteIsometryAverage_norm (U : I → H ≃ₗᵢ[ℂ] H) : ‖finiteIsometryAverage U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using finiteIsometryAverage_norm_apply U x

theorem isometry_average_intertwining (S : H →ₗᵢ[ℂ] K)
    (U : I → H ≃ₗᵢ[ℂ] H) (V : I → K ≃ₗᵢ[ℂ] K) (x : H)
    {η : ℝ} (he : ∀ i, ‖S (U i x) - V i (S x)‖ ≤ η) :
    ‖S (finiteIsometryAverage U x) - finiteIsometryAverage V (S x)‖ ≤ η := by
  have hid : S (finiteIsometryAverage U x) - finiteIsometryAverage V (S x) =
      (Fintype.card I : ℂ)⁻¹ • ∑ i, (S (U i x) - V i (S x)) := by
    simp only [finiteIsometryAverage_apply, map_smul, map_sum, Finset.sum_sub_distrib, smul_sub]
  rw [hid]
  exact norm_finite_average_le _ he

theorem finiteDilation_average {F : Type*} [Group F] [Fintype F]
    (U : F → H ≃ₗᵢ[ℂ] H) (w : I → F) (x : H) {η : ℝ} (hη : 0 ≤ η)
    (hmul : ∀ g i, ‖U g (U (w i) x) - U (g * w i) x‖ ≤ η) :
    ‖finiteDilation U (finiteIsometryAverage (fun i => U (w i)) x) -
      finiteIsometryAverage (fun i => finiteRegularAction (w i)) (finiteDilation U x)‖ ≤ η :=
  isometry_average_intertwining _ _ _ _ (fun i => finiteDilation_intertwining U _ x hη (fun g => hmul g i))

def finiteIsometrySymmetricAverage (U : I → H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  (1/2:ℂ) • (finiteIsometryAverage U + finiteIsometryAverage (fun i => (U i).symm))

theorem finiteIsometrySymmetricAverage_apply (U : I → H ≃ₗᵢ[ℂ] H) (x : H) :
    finiteIsometrySymmetricAverage U x =
      (1/2:ℂ) • (finiteIsometryAverage U x + finiteIsometryAverage (fun i => (U i).symm) x) := by
  simp only [finiteIsometrySymmetricAverage, smul_apply, add_apply]

theorem finiteIsometrySymmetricAverage_norm_apply (U : I → H ≃ₗᵢ[ℂ] H) (x : H) :
    ‖finiteIsometrySymmetricAverage U x‖ ≤ ‖x‖ := by
  rw [finiteIsometrySymmetricAverage_apply, norm_smul]
  have hn := norm_add_le (finiteIsometryAverage U x) (finiteIsometryAverage (fun i => (U i).symm) x)
  have h₁ := finiteIsometryAverage_norm_apply U x
  have h₂ := finiteIsometryAverage_norm_apply (fun i => (U i).symm) x
  norm_num
  linarith

theorem isometry_symmetric_average_intertwining (S : H →ₗᵢ[ℂ] K)
    (U : I → H ≃ₗᵢ[ℂ] H) (P : K →L[ℂ] K) (x : H) {η : ℝ}
    (he : ‖S (finiteIsometryAverage U x) - P (S x)‖ ≤ η)
    (he' : ‖S (finiteIsometryAverage (fun i => (U i).symm) x) - P (S x)‖ ≤ η) :
    ‖S (finiteIsometrySymmetricAverage U x) - P (S x)‖ ≤ η := by
  have hid : S (finiteIsometrySymmetricAverage U x) - P (S x) =
      (1/2:ℂ) • ((S (finiteIsometryAverage U x) - P (S x)) +
        (S (finiteIsometryAverage (fun i => (U i).symm) x) - P (S x))) := by
    simp only [finiteIsometrySymmetricAverage_apply, map_smul, map_add, smul_add, smul_sub]
    module
  rw [hid, norm_smul]
  norm_num
  have hh := (norm_add_le _ _).trans (add_le_add he he')
  linarith

end ThomGame.Analysis
