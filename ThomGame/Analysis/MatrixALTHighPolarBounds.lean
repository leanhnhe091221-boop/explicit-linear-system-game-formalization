module

public import ThomGame.Analysis.MatrixPolarFourthMomentDistance

/-!
# Explicit constants for the polar completion of a high eigenvector

For rho <= 1/4, the genuine scalar error sigma <= rho^4 leaves a
fourth-moment coefficient at least 1-2rho >= 1/2. Polar completion
then costs at most 4rho times the normalized mass in squared norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

theorem alt_high_eigenvalue_gap (rho sigma lam : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 4)
    (hsigma : sigma ≤ rho ^ 4) (hhigh : 1 - rho ≤ lam) :
    1 - 2 * rho ≤ lam ^ 2 - sigma ∧ 1 / 2 ≤ lam ^ 2 - sigma := by
  have hsq : rho ^ 2 ≤ 1 := by nlinarith
  have hfour : rho ^ 4 ≤ rho ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg rho)]
  have hl : 0 ≤ 1 - rho := by linarith
  have he := pow_le_pow_left₀ hl hhigh 2
  constructor <;> nlinarith

variable {d : Nat} [NeZero d]

theorem matrixPolarCompletion_high_distance (P Q X U : CMatrix d)
    (hU : IsStarProjection (star U * U)) (hpair : star U * X = matrixRectAbs X)
    (hrank : (star U * U).rank = min P.rank Q.rank)
    (hnorm : hsNorm X ^ 2 = ((max P.rank Q.rank : Nat) : ℝ) / d)
    (lam sigma rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 4)
    (hsigma : sigma ≤ rho ^ 4) (hhigh : 1 - rho ≤ lam)
    (hmoment : (lam ^ 2 - sigma) * hsNorm (star X * X) ^ 2 ≤ hsNorm X ^ 2) :
    hsNorm (U - X) ^ 2 ≤ 4 * rho * hsNorm X ^ 2 := by
  obtain ⟨hgap, hhalf⟩ := alt_high_eigenvalue_gap rho sigma lam hrho hsmall hsigma hhigh
  have ha : 0 ≤ lam ^ 2 - sigma := by linarith
  have ht : ((star U * U).rank : ℝ) / d ≤ hsNorm X ^ 2 := by
    rw [hrank, hnorm]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (min_le_max : min P.rank Q.rank ≤ max P.rank Q.rank)) (Nat.cast_nonneg d)
  have hb := matrixPolarCompletion_fourth_distance X U hU hpair
  have he : hsNorm (U - X) ^ 2 ≤ hsNorm (star X * X) ^ 2 - hsNorm X ^ 2 := by linarith
  have he' := mul_le_mul_of_nonneg_left he ha
  have hl := mul_le_mul_of_nonneg_right hhalf (sq_nonneg (hsNorm (U - X)))
  have hg := mul_le_mul_of_nonneg_right hgap (sq_nonneg (hsNorm X))
  nlinarith only [he', hl, hg, hmoment]

omit [NeZero d] in
theorem matrixUCP_near_eigenvector_fixed_error (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Y, normalizedTrace (F Y) = normalizedTrace Y)
    (X U : CMatrix d) (lam rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1)
    (heigen : F X = (lam : ℂ) • X) (hlam : |lam - 1| ≤ rho)
    (hdistance : hsNorm (U - X) ^ 2 ≤ 4 * rho * hsNorm X ^ 2) :
    hsNorm (F U - U) ^ 2 ≤ 36 * rho * hsNorm X ^ 2 := by
  have he : F U - U = F (U - X) + (F X - X) + (X - U) := by
    rw [map_sub]
    abel
  have hm : hsNorm (F X - X) ≤ rho * hsNorm X := by
    have heX : F X - X = ((lam - 1 : ℝ) : ℂ) • X := by
      rw [heigen, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rw [heX, hsNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hlam (hsNorm_nonneg X)
  have hb : hsNorm (F U - U) ≤ 2 * hsNorm (U - X) + rho * hsNorm X := by
    rw [he]
    have h1 := hsNorm_add_le (F (U - X) + (F X - X)) (X - U)
    have h2 := hsNorm_add_le (F (U - X)) (F X - X)
    have h3 := matrixUCP_hsNorm_le F hF htrace (U - X)
    rw [hsNorm_sub_comm X U] at h1
    linarith
  have hs := pow_le_pow_left₀ (hsNorm_nonneg _) hb 2
  have hr : rho ^ 2 ≤ rho := by nlinarith
  have hmass := mul_le_mul_of_nonneg_right hr (sq_nonneg (hsNorm X))
  nlinarith [sq_nonneg (2 * hsNorm (U - X) - rho * hsNorm X),
    mul_nonneg hrho (sq_nonneg (hsNorm X))]

end ThomGame.Analysis
