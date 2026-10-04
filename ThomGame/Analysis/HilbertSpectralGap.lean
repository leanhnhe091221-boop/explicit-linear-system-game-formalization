module

public import ThomGame.Analysis.InvariantMeanProjection
public import ThomGame.Analysis.PositiveOperatorEstimates

/-!
# Geometric power estimates from a Hilbert spectral gap

A positive contraction with a gap on the orthogonal complement of its
fixed space converges geometrically to the fixed-space projection.
Positivity gives the sharp constant one also for differences of powers.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (T : H →L[ℂ] H)

theorem meanProjection_isStarProjection : IsStarProjection (meanProjection T) :=
  isStarProjection_starProjection

theorem mul_meanProjection : T * meanProjection T = meanProjection T := by
  apply ContinuousLinearMap.ext
  intro x
  exact meanProjection_fixed T x

theorem meanProjection_mul (hs : IsSelfAdjoint T) : meanProjection T * T = meanProjection T := by
  have he := congrArg star (mul_meanProjection T)
  simpa only [star_mul, (meanProjection_isStarProjection T).isSelfAdjoint.star_eq, hs.star_eq] using he

theorem meanProjection_residual_compression (hs : IsSelfAdjoint T) :
    star (1 - meanProjection T) * T * (1 - meanProjection T) = T - meanProjection T := by
  rw [star_sub, star_one, (meanProjection_isStarProjection T).isSelfAdjoint.star_eq,
    sub_mul, one_mul, meanProjection_mul T hs, mul_sub, mul_one, sub_mul, mul_meanProjection,
    (meanProjection_isStarProjection T).isIdempotentElem.eq, sub_self, sub_zero]

theorem meanProjection_residual_nonneg (hT : 0 ≤ T) : 0 ≤ T - meanProjection T := by
  rw [← meanProjection_residual_compression T (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint]
  exact star_left_conjugate_nonneg hT _

theorem meanProjection_residual_pairing (hs : IsSelfAdjoint T) (x : H) :
    inner ℂ x ((T - meanProjection T) x) =
      inner ℂ (x - meanProjection T x) (T (x - meanProjection T x)) := by
  rw [← meanProjection_residual_compression T hs, mul_apply_eq_comp, mul_apply_eq_comp]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem meanProjection_complement_norm_le (x : H) : ‖x - meanProjection T x‖ ≤ ‖x‖ := by
  change ‖x - (T.eqLocus (1 : H →L[ℂ] H)).starProjection x‖ ≤ ‖x‖
  rw [← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_starProjection_apply_le _ x

theorem meanProjection_residual_norm_le (hT : 0 ≤ T) (κ : ℝ) (hκ : κ ≤ 1)
    (hgap : ∀ ξ ∈ (T.eqLocus (1 : H →L[ℂ] H))ᗮ,
      κ * ‖ξ‖ ^ 2 ≤ (inner ℂ ξ ((1 - T) ξ)).re) :
    ‖T - meanProjection T‖ ≤ 1 - κ := by
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint
  have hres := meanProjection_residual_nonneg T hT
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sub_nonneg.mpr hκ) hres).mpr
  apply ContinuousLinearMap.le_def.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨((by rfl : IsSelfAdjoint (1 - κ)).algebraMap (H →L[ℂ] H)).sub
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hres).isSelfAdjoint, ?_⟩
  intro x
  have hg := hgap (x - meanProjection T x)
    ((T.eqLocus (1 : H →L[ℂ] H)).sub_starProjection_mem_orthogonal x)
  have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (meanProjection_complement_norm_le T x)
  have hh (ξ : H) : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) ξ
  rw [sub_apply, one_apply_eq_self, inner_sub_right, Complex.sub_re, hh] at hg
  have hb : (inner ℂ x ((T - meanProjection T) x)).re ≤ (1 - κ) * ‖x‖ ^ 2 := by
    rw [meanProjection_residual_pairing T hs]
    exact (by linarith : (inner ℂ (x - meanProjection T x) (T (x - meanProjection T x))).re ≤
      (1 - κ) * ‖x - meanProjection T x‖ ^ 2).trans
        (mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hκ))
  change 0 ≤ (inner ℂ ((algebraMap ℝ (H →L[ℂ] H) (1 - κ) - (T - meanProjection T)) x) x).re
  rw [← RCLike.re_to_complex, inner_re_symm, RCLike.re_to_complex]
  simpa only [sub_apply, inner_sub_right, Complex.sub_re, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, ← Complex.coe_smul, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hh, sub_nonneg] using hb

theorem meanProjection_residual_pow (hs : IsSelfAdjoint T) (j : Nat) (hj : 0 < j) :
    (T - meanProjection T) ^ j = T ^ j - meanProjection T := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  clear hj
  have hpow (m : Nat) : meanProjection T * T ^ (m + 1) = meanProjection T := by
    induction m with
    | zero => simpa only [Nat.zero_add, pow_one] using meanProjection_mul T hs
    | succ m ihm => rw [pow_succ, ← mul_assoc, ihm, meanProjection_mul T hs]
  induction n with
  | zero => simp only [pow_one]
  | succ n ih =>
      rw [pow_succ', ih, sub_mul, mul_sub, mul_sub, mul_meanProjection, hpow,
        (meanProjection_isStarProjection T).isIdempotentElem.eq, sub_self, sub_zero, ← pow_succ']

theorem spectralGap_pow_sub_projection_norm_le (hT : 0 ≤ T) (κ : ℝ) (hκ : κ ≤ 1)
    (hgap : ∀ ξ ∈ (T.eqLocus (1 : H →L[ℂ] H))ᗮ,
      κ * ‖ξ‖ ^ 2 ≤ (inner ℂ ξ ((1 - T) ξ)).re) (j : Nat) :
    ‖T ^ j - meanProjection T‖ ≤ (1 - κ) ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, pow_zero]
    change ‖1 - (T.eqLocus (1 : H →L[ℂ] H)).starProjection‖ ≤ 1
    rw [← Submodule.starProjection_orthogonal']
    exact Submodule.starProjection_norm_le _
  · rw [← meanProjection_residual_pow T (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint j hj]
    exact (norm_pow_le' _ hj).trans (pow_le_pow_left₀ (norm_nonneg _)
      (meanProjection_residual_norm_le T hT κ hκ hgap) j)

theorem spectralGap_pow_sub_pow_norm_le (hT : 0 ≤ T) (κ : ℝ) (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hgap : ∀ ξ ∈ (T.eqLocus (1 : H →L[ℂ] H))ᗮ,
      κ * ‖ξ‖ ^ 2 ≤ (inner ℂ ξ ((1 - T) ξ)).re) (j k : Nat) (hj : 0 < j) (hjk : j ≤ k) :
    ‖T ^ k - T ^ j‖ ≤ (1 - κ) ^ j := by
  let S := T - meanProjection T
  have hS : 0 ≤ S := meanProjection_residual_nonneg T hT
  have hSn : ‖S‖ ≤ 1 - κ := meanProjection_residual_norm_le T hT κ hκ₁ hgap
  have hS₁ : S ≤ 1 := by
    have he := (CStarAlgebra.norm_le_iff_le_algebraMap S zero_le_one hS).mp (hSn.trans (by linarith))
    simpa only [map_one] using he
  have hanti := CStarAlgebra.pow_antitone hS₁ hS hjk
  have hle : ‖S ^ k - S ^ j‖ ≤ ‖S ^ j‖ := by
    rw [norm_sub_rev]
    exact CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (sub_le_self _ (CStarAlgebra.pow_nonneg S k hS)) (sub_nonneg.mpr hanti)
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint
  have he : S ^ k - S ^ j = T ^ k - T ^ j := by
    dsimp only [S]
    rw [meanProjection_residual_pow T hs k (hj.trans_le hjk), meanProjection_residual_pow T hs j hj,
      sub_sub_sub_cancel_right]
  rw [← he]
  exact hle.trans ((norm_pow_le' _ hj).trans (pow_le_pow_left₀ (norm_nonneg _) hSn j))

end ThomGame.Analysis
