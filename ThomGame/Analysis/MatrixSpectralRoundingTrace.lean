module

public import ThomGame.Analysis.MatrixProjectionRankTrace
public import ThomGame.Analysis.SpectralRestrictedCoarea

/-!
# Positive trace lost by spectral rounding

For a positive contraction A, cutting at s loses at most s times
rank(A)/d in positive-part trace. This is the actual rounding-error
estimate used in the coverage proof of ALT Lemma 3.3.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

theorem real_spectral_rounding_posPart_le_rank_weight {s x : ℝ}
    (hs : 0 ≤ s) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    max (x - spectralStep s x) 0 ≤ s * (if x = 0 then (0 : ℝ) else 1) := by
  by_cases hx : x = 0
  · subst x
    simp only [ite_true, mul_zero, zero_sub]
    exact max_le (neg_nonpos.mpr (spectralStep_nonneg s 0)) le_rfl
  · rw [ite_eq_right_iff.mpr (by simp [hx]), mul_one]
    by_cases hsx : s ≤ x
    · simp only [spectralStep, hsx, ite_true, max_eq_right (sub_nonpos.mpr hx1)]
      exact hs
    · simp only [spectralStep, hsx, ite_false, sub_zero, max_eq_left hx0]
      exact le_of_not_ge hsx

variable {d : Nat} {A P : CMatrix d}

theorem matrix_spectral_rounding_posPart_cfc (hA : Matrix.IsHermitian A) (s : ℝ) :
    (A - matrixSpectralCut A s)⁺ = cfc (fun t : ℝ => max (t - spectralStep s t) 0) A := by
  have hi : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  have he : cfc (fun t : ℝ => t - spectralStep s t) A = A - matrixSpectralCut A s := by
    rw [cfc_sub (fun t : ℝ => t) (spectralStep s) A continuous_id.continuousOn
      (A.finite_real_spectrum.continuousOn _), hi]
    rfl
  rw [matrix_posPart_eq_cfc, ← he]
  exact (cfc_comp' (fun t : ℝ => max t 0) (fun t : ℝ => t - spectralStep s t) A
    (by fun_prop) (A.finite_real_spectrum.continuousOn _) hA).symm

theorem matrix_spectral_rounding_posPart_trace_le (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    {s : ℝ} (hs : 0 ≤ s) :
    (normalizedTrace (A - matrixSpectralCut A s)⁺).re ≤ s * ((A.rank : ℝ) / d) := by
  have hA := hA0.isSelfAdjoint.isHermitian
  rw [matrix_spectral_rounding_posPart_cfc hA, matrix_cfc_trace hA,
    matrix_rank_eq_nonzero_eigenvalue_sum hA, ← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  apply Finset.sum_le_sum
  intro i _
  exact real_spectral_rounding_posPart_le_rank_weight hs
    (spectrum_nonneg_of_nonneg hA0 (hA.eigenvalues_mem_spectrum_real i))
    ((CFC.le_one_iff (R := ℝ) A hA).mp hA1 _ (hA.eigenvalues_mem_spectrum_real i))

theorem matrix_spectral_rounding_posPart_trace_le_projection (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hP : IsStarProjection P) (hrank : A.rank ≤ P.rank) {s : ℝ} (hs : 0 ≤ s) :
    (normalizedTrace (A - matrixSpectralCut A s)⁺).re ≤ s * (normalizedTrace P).re := by
  apply (matrix_spectral_rounding_posPart_trace_le hA0 hA1 hs).trans
  rw [matrixProjection_trace_eq_rank hP]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr hrank) (Nat.cast_nonneg d)) hs

theorem matrixSpectralCut_le_scaled (hA0 : 0 ≤ A) {s : ℝ} (hs : 0 < s) :
    matrixSpectralCut A s ≤ s⁻¹ • A := by
  have hA := hA0.isSelfAdjoint
  have hi : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  have he : s⁻¹ • A = cfc (fun t : ℝ => s⁻¹ * t) A := by
    rw [cfc_const_mul s⁻¹ (fun t : ℝ => t) A continuous_id.continuousOn, hi]
  rw [he]
  apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (by fun_prop)
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hA0 ht
  have hb := spectralStep_mul_le s t ht0
  rw [mul_comm s⁻¹ t, ← div_eq_mul_inv]
  exact (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hb)

end ThomGame.Analysis
