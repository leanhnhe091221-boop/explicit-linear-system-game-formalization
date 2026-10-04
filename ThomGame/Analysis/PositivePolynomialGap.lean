module

public import ThomGame.Analysis.PositiveOperatorEstimates

/-!
# A spectral gap from a positive quadratic polynomial

For a positive operator L, the inequality a L ≤ L² implies the quadratic
form gap a ‖x‖² ≤ ⟨x,Lx⟩ on the orthogonal complement of its kernel.
The proof first works on the range and then passes to its closure.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_polynomial_gap_on_range (L : H →L[ℂ] H) (hL : 0 ≤ L)
    (a : ℝ) (hgap : a • L ≤ L * L) (x : H) :
    a * ‖L x‖ ^ 2 ≤ (inner ℂ (L x) (L (L x))).re := by
  have hc : Commute L (L * L - a • L) := by
    change L * (L * L - a • L) = (L * L - a • L) * L
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  have hp := Commute.mul_nonneg hL (sub_nonneg.mpr hgap) hc
  rw [mul_sub, mul_smul_comm] at hp
  have h := operator_re_inner_mono (sub_nonneg.mp hp) x
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp hL).inner_left_eq_inner_right
  simp only [mul_apply_eq_comp, smul_apply, ← Complex.coe_smul, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  rw [← hs x (L x), ← hs x (L (L x))] at h
  have he : (inner ℂ (L x) (L x)).re = ‖L x‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (L x)
  simpa only [he] using h

theorem positive_polynomial_gap (L : H →L[ℂ] H) (hL : 0 ≤ L)
    (a : ℝ) (hgap : a • L ≤ L * L) (x : H) (hx : x ∈ L.kerᗮ) :
    a * ‖x‖ ^ 2 ≤ (inner ℂ x (L x)).re := by
  have hs : L.adjoint = L := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hL).isSelfAdjoint.star_eq
  rw [ContinuousLinearMap.orthogonal_ker, hs] at hx
  have hclosed : IsClosed {y : H | a * ‖y‖ ^ 2 ≤ (inner ℂ y (L y)).re} :=
    isClosed_le (by fun_prop) (by fun_prop)
  apply closure_minimal (t := {y : H | a * ‖y‖ ^ 2 ≤ (inner ℂ y (L y)).re}) ?_ hclosed hx
  rintro y ⟨z, rfl⟩
  exact positive_polynomial_gap_on_range L hL a hgap z

end ThomGame.Analysis
