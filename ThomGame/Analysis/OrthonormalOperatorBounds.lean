module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Operator norm bounds from actual orthonormal coordinates

Coordinate estimates are squared and summed using Parseval, so there
is no loss depending on the dimension or number of eigenvectors.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped InnerProductSpace BigOperators

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]

theorem orthonormal_operator_norm_le (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H)
    (r : ℝ) (hr : 0 ≤ r)
    (hcoeff : ∀ i x, ‖inner ℂ (b i) (T x)‖ ≤ r * ‖inner ℂ (b i) x‖) : ‖T‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp
  rw [mul_pow, ← b.sum_sq_norm_inner_right (T x), ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mpr (hcoeff i x)

theorem symmetric_eigenbasis_norm_le (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H)
    (hT : T.toLinearMap.IsSymmetric) (lam : ι → ℝ)
    (heigen : ∀ i, T (b i) = (lam i : ℂ) • b i) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ i, |lam i| ≤ r) : ‖T‖ ≤ r := by
  apply orthonormal_operator_norm_le b T r hr
  intro i x
  have he : inner ℂ (b i) (T x) = (lam i : ℂ) * inner ℂ (b i) x := by
    have ht := hT (b i) x
    change inner ℂ (T (b i)) x = inner ℂ (b i) (T x) at ht
    rw [heigen, inner_smul_left, Complex.conj_ofReal] at ht
    exact ht.symm
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg _)

theorem symmetric_eigenbasis_sub_lineProjection_norm_le (b : OrthonormalBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric) (lam : ι → ℝ)
    (heigen : ∀ i, T (b i) = (lam i : ℂ) • b i) (j : ι) (r : ℝ) (hr : 0 ≤ r)
    (hj : |lam j - 1| ≤ r) (hother : ∀ i, i ≠ j → |lam i| ≤ r) :
    ‖T - (ℂ ∙ b j).starProjection‖ ≤ r := by
  classical
  apply orthonormal_operator_norm_le b _ r hr
  intro i x
  have he : inner ℂ (b i) (T x) = (lam i : ℂ) * inner ℂ (b i) x := by
    have ht := hT (b i) x
    change inner ℂ (T (b i)) x = inner ℂ (b i) (T x) at ht
    rw [heigen, inner_smul_left, Complex.conj_ofReal] at ht
    exact ht.symm
  have hp : (ℂ ∙ b j).starProjection x = inner ℂ (b j) x • b j := by
    rw [Submodule.starProjection_singleton]
    change (inner ℂ (b j) x / ((‖b j‖ ^ 2 : ℝ) : ℂ)) • b j = _
    rw [b.norm_eq_one]
    norm_num
  rw [sub_apply, inner_sub_right, he, hp, inner_smul_right]
  by_cases hij : i = j
  · subst i
    rw [b.inner_eq_one, mul_one, ← sub_one_mul]
    have hb : ‖(lam j : ℂ) - 1‖ ≤ r := by
      simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hj
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · rw [b.inner_eq_zero hij, mul_zero, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hother i hij) (norm_nonneg _)

end ThomGame.Analysis
