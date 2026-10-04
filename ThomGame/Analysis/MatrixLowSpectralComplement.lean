module

public import ThomGame.Analysis.MatrixALTSelectionIncrement

/-!
# The squared-moment bound outside a closed low spectral interval

Scalar functional calculus gives 1-b <= s^(-2) S^2. Pairing this
operator inequality with projections yields the weighted trace
estimate used in ALT (4.11).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrixClosedLowSpectralCut_complement_le_square {S : CMatrix d}
    (hS : 0 ≤ S) {s : ℝ} (hs : 0 < s) :
    1 - matrixClosedLowSpectralCut S s ≤ (s⁻¹) ^ 2 • S ^ 2 := by
  have hleft : 1 - matrixClosedLowSpectralCut S s =
      cfc (fun t : ℝ => 1 - if 0 ≤ t ∧ t ≤ s then 1 else 0) S := by
    rw [cfc_sub (fun _ : ℝ => 1) _ S (S.finite_real_spectrum.continuousOn _)
      (S.finite_real_spectrum.continuousOn _), cfc_const_one ℝ S hS.isSelfAdjoint]
    rfl
  have hright : cfc (fun t : ℝ => t ^ 2) S = S ^ 2 := by
    rw [cfc_pow (fun t : ℝ => t) 2 S (S.finite_real_spectrum.continuousOn _), cfc_id' ℝ S hS.isSelfAdjoint]
  rw [hleft, ← hright, ← cfc_const_mul _ _ S (S.finite_real_spectrum.continuousOn _)]
  apply cfc_mono _ (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _)
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hS ht
  by_cases hts : t ≤ s
  · simp only [ht0, hts, and_self, ite_true, sub_self]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · simp only [hts, and_false, ite_false, sub_zero]
    have he := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hs.le ht0).mpr (le_of_not_ge hts)) (sq_nonneg s⁻¹)
    simpa only [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow] using he

theorem matrixTraceReal_lowCut_complement_mul_le {S Q : CMatrix d}
    (hS : 0 ≤ S) (hQ : IsStarProjection Q) {s : ℝ} (hs : 0 < s) :
    matrixTraceReal d ((1 - matrixClosedLowSpectralCut S s) * Q) ≤
      (s⁻¹) ^ 2 * matrixTraceReal d (S ^ 2 * Q) := by
  have he := matrixTraceReal_projection_mul_mono d hQ
    (matrixClosedLowSpectralCut_complement_le_square hS hs)
  simpa only [Matrix.mul_smul, matrixTraceReal_real_smul,
    matrixTraceReal_mul_comm d Q] using he

theorem matrixTraceReal_lowCut_complement_sum_le {μ : Type*} [Fintype μ]
    (S Q : μ → CMatrix d) (hS : ∀ i, 0 ≤ S i) (hQ : ∀ i, IsStarProjection (Q i))
    {κ η : ℝ} (hκ : 0 < κ) (hweight : (∑ i, matrixTraceReal d ((S i) ^ 2 * Q i)) ≤ 3 * η) :
    (∑ i, matrixTraceReal d ((1 - matrixClosedLowSpectralCut (S i) (κ / 512)) * Q i)) ≤
      3 * (512 / κ) ^ 2 * η := by
  have he := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    matrixTraceReal_lowCut_complement_mul_le (hS i) (hQ i) (div_pos hκ (by norm_num : (0 : ℝ) < 512))
  rw [← Finset.mul_sum, inv_div] at he
  have hh := mul_le_mul_of_nonneg_left hweight (sq_nonneg (512 / κ))
  exact he.trans (by nlinarith only [hh])

end ThomGame.Analysis
