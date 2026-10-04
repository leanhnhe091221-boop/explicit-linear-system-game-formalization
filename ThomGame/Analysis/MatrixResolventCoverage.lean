module

public import ThomGame.Analysis.MatrixResolventFamilies

/-!
# Endpoint estimates for the resolvent coverage bound

The initial projection contributes at most its trace. For lambda equal
to gamma squared, the final resolvent contributes at most the low
spectral mass plus gamma. Together with a given rounding-error bound,
these prove the numerical coverage estimate in ALT (3.4).
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {S P : CMatrix d} {lam γ : ℝ}

theorem matrixPositiveResolvent_self_mul_eq_cfc (lam : ℝ) (hS : IsSelfAdjoint S) :
    S * matrixPositiveResolvent lam S = cfc (fun t : ℝ => t * (lam + t)⁻¹) S := by
  have hi : cfc (fun t : ℝ => t) S = S := cfc_id' ℝ S hS
  unfold matrixPositiveResolvent
  nth_rw 1 [← hi]
  exact (cfc_mul (fun t : ℝ => t) (fun t : ℝ => (lam + t)⁻¹) S
    continuous_id.continuousOn (S.finite_real_spectrum.continuousOn _)).symm

theorem matrixPositiveResolvent_projection_missing_le (hlam : 0 < lam) (hP : IsStarProjection P) :
    1 - lam • matrixPositiveResolvent lam P ≤ P := by
  rw [← matrixPositiveResolvent_self_mul hlam hP.nonneg,
    matrixPositiveResolvent_self_mul_eq_cfc lam hP.isSelfAdjoint]
  have hi : cfc (fun t : ℝ => t) P = P := cfc_id' ℝ P hP.isSelfAdjoint
  nth_rw 2 [← hi]
  apply cfc_mono _ (P.finite_real_spectrum.continuousOn _) continuous_id.continuousOn
  intro t ht
  have ht01 := hP.isIdempotentElem.spectrum_subset ℝ ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht01
  rcases ht01 with rfl | rfl
  · simp
  · simp only [one_mul, id_eq]
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (by linarith : 1 ≤ lam + 1)

theorem real_resolvent_low_cut_bound (hγ : 0 < γ) {t : ℝ} (ht : 0 ≤ t) :
    γ ^ 2 * (γ ^ 2 + t)⁻¹ ≤ 1 - spectralStep γ t + γ := by
  have hd : 0 < γ ^ 2 + t := add_pos_of_pos_of_nonneg (sq_pos_of_pos hγ) ht
  rw [← div_eq_mul_inv, div_le_iff₀ hd]
  by_cases hgt : γ ≤ t
  · rw [spectralStep, ite_eq_left_iff.mpr (by simp [hgt])]
    have hp := mul_le_mul_of_nonneg_left hgt hγ.le
    nlinarith [mul_nonneg hγ.le (sq_nonneg γ)]
  · simp only [spectralStep, hgt, ite_false]
    nlinarith [mul_nonneg hγ.le ht, mul_nonneg hγ.le (sq_nonneg γ)]

theorem matrixPositiveResolvent_scaled_low_cut_le (hγ : 0 < γ) (hS : 0 ≤ S) :
    γ ^ 2 • matrixPositiveResolvent (γ ^ 2) S ≤
      (1 - matrixSpectralCut S γ) + γ • (1 : CMatrix d) := by
  have he : cfc (fun t : ℝ => 1 - spectralStep γ t + γ) S =
      (1 - matrixSpectralCut S γ) + γ • (1 : CMatrix d) := by
    rw [cfc_add_const γ (fun t : ℝ => 1 - spectralStep γ t) S
      (S.finite_real_spectrum.continuousOn _) hS.isSelfAdjoint,
      cfc_sub (fun _ : ℝ => 1) (spectralStep γ) S continuous_const.continuousOn
        (S.finite_real_spectrum.continuousOn _), cfc_const_one ℝ S hS.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
    rfl
  rw [← he, matrixPositiveResolvent,
    ← cfc_const_mul (γ ^ 2) (fun t : ℝ => (γ ^ 2 + t)⁻¹) S (S.finite_real_spectrum.continuousOn _)]
  exact cfc_mono (fun _ ht => real_resolvent_low_cut_bound hγ (spectrum_nonneg_of_nonneg hS ht))
    (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _)

theorem matrixPositiveResolvent_low_cut_trace_le [NeZero d] (hγ : 0 < γ) (hS : 0 ≤ S) :
    (normalizedTrace (γ ^ 2 • matrixPositiveResolvent (γ ^ 2) S)).re ≤
      (normalizedTrace (1 - matrixSpectralCut S γ)).re + γ := by
  have he := normalizedTrace_re_mono (matrixPositiveResolvent_scaled_low_cut_le hγ hS)
  rw [normalizedTrace_add, Complex.add_re] at he
  have hs : (normalizedTrace (γ • (1 : CMatrix d))).re = γ := by
    change (normalizedTrace ((γ : ℂ) • (1 : CMatrix d))).re = _
    rw [normalizedTrace_smul, normalizedTrace_one, mul_one, Complex.ofReal_re]
  simpa only [hs] using he

theorem matrixResolventFamily_coverage_of_rounding [NeZero d] (hγ : 0 < γ)
    {P : CMatrix d} (hP : IsStarProjection P) (F : Nat → CMatrix d)
    (hF : ∀ i, IsStarProjection (F i)) (n : Nat) (Q : Fin n → CMatrix d)
    (hQ : ∀ i, IsStarProjection (Q i))
    (herr : (∑ i : Fin n,
      (normalizedTrace (matrixResolventDifferenceFamily (γ ^ 2) P F i - Q i)⁺).re) ≤ 6 * γ) :
    matrixFamilyCoverageDefect Q ≤ (normalizedTrace P).re +
      (normalizedTrace (1 - matrixSpectralCut (matrixProjectionPartialSum P F n) γ)).re + 7 * γ := by
  have hc := matrixResolventDifferenceFamily_coverage_bound (sq_pos_of_pos hγ) hP.nonneg F hF n Q hQ
  have hstart := normalizedTrace_re_mono
    (matrixPositiveResolvent_projection_missing_le (sq_pos_of_pos hγ) hP)
  have hend := matrixPositiveResolvent_low_cut_trace_le hγ
    (matrixProjectionPartialSum_nonneg hP.nonneg F hF n)
  linarith

end ThomGame.Analysis
