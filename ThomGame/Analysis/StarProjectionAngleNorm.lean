module

public import ThomGame.Analysis.PositiveOperatorEstimates

/-! A sharp norm estimate for the sum of two genuine orthogonal projections. -/

@[expose] public section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem starProjection_apply_apply {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    P (P x) = P x := DFunLike.congr_fun hP.isIdempotentElem.eq x

theorem starProjection_inner_symm {P : H →L[ℂ] H} (hP : IsStarProjection P) (x y : H) :
    inner ℂ (P x) y = inner ℂ x (P y) :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp hP.nonneg).inner_left_eq_inner_right x y

theorem starProjection_norm_sq {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ^ 2 = (inner ℂ x (P x)).re := by
  calc
    ‖P x‖ ^ 2 = (inner ℂ (P x) (P x)).re := by
      simpa only [RCLike.re_to_complex] using (norm_sq_eq_re_inner (𝕜 := ℂ) (P x))
    _ = (inner ℂ x (P (P x))).re := congrArg Complex.re (starProjection_inner_symm hP x (P x))
    _ = (inner ℂ x (P x)).re := by rw [starProjection_apply_apply hP]

theorem starProjection_cross_inner_le {P Q : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (c : ℝ) (hPQ : ‖P * Q‖ ≤ c) (x : H) :
    (inner ℂ (P x) (Q x)).re ≤ c * ‖P x‖ * ‖Q x‖ := by
  have he : inner ℂ (P x) (Q x) = inner ℂ (P x) ((P * Q) (Q x)) := by
    rw [mul_apply_eq_comp, starProjection_apply_apply hQ]
    rw [← starProjection_inner_symm hP, starProjection_apply_apply hP]
  rw [he]
  calc
    (inner ℂ (P x) ((P * Q) (Q x))).re ≤ ‖P x‖ * ‖(P * Q) (Q x)‖ :=
      re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖P x‖ * (c * ‖Q x‖) := mul_le_mul_of_nonneg_left
      (((P * Q).le_opNorm (Q x)).trans (mul_le_mul_of_nonneg_right hPQ (norm_nonneg _)))
      (norm_nonneg _)
    _ = c * ‖P x‖ * ‖Q x‖ := by ring

theorem starProjection_add_norm_le {P Q : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (c : ℝ) (hc : 0 ≤ c) (hPQ : ‖P * Q‖ ≤ c) : ‖P + Q‖ ≤ 1 + c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro x
  have hcross := starProjection_cross_inner_le hP hQ c hPQ x
  have hsq : ‖(P + Q) x‖ ^ 2 ≤ (1 + c) * (‖P x‖ ^ 2 + ‖Q x‖ ^ 2) := by
    rw [add_apply, norm_add_sq (𝕜 := ℂ)]
    have hnonneg := mul_nonneg hc (sq_nonneg (‖P x‖ - ‖Q x‖))
    change ‖P x‖ ^ 2 + 2 * (inner ℂ (P x) (Q x)).re + ‖Q x‖ ^ 2 ≤ _
    nlinarith
  have hpair : ‖P x‖ ^ 2 + ‖Q x‖ ^ 2 = (inner ℂ x ((P + Q) x)).re := by
    rw [add_apply, inner_add_right, Complex.add_re,
      starProjection_norm_sq hP, starProjection_norm_sq hQ]
  rw [hpair] at hsq
  have hbound := mul_le_mul_of_nonneg_left
    (re_inner_le_norm (𝕜 := ℂ) x ((P + Q) x)) (by linarith : 0 ≤ 1 + c)
  have hfinal : ‖(P + Q) x‖ ^ 2 ≤ ((1 + c) * ‖x‖) * ‖(P + Q) x‖ := by
    exact hsq.trans (by simpa only [mul_assoc, RCLike.re_to_complex] using hbound)
  by_cases hz : ‖(P + Q) x‖ = 0
  · rw [hz]
    exact mul_nonneg (by linarith) (norm_nonneg _)
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp
      (by nlinarith [hfinal])

end ThomGame.Analysis
