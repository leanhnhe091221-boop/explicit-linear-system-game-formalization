module

public import ThomGame.Analysis.MatrixUCPTraceBounds
public import ThomGame.Analysis.MatrixOffDiagonalPairing
public import ThomGame.Analysis.MatrixRankOneCorners
public import ThomGame.Analysis.MatrixResolventDifferenceBounds

/-!
# Fourth moments of eigenvectors in a scalar-mixing corner

The operator Schwarz inequality and the actual scalar-corner error give
ALT (5.4)'s fourth-moment bound. All moments are computed with the
original ambient normalized trace, even for unequal corner dimensions.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat}

theorem matrixUCP_eigenvector_gram_le (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (lam : ℝ) (X : CMatrix d) (heigen : F X = (lam : ℂ) • X) :
    ((lam ^ 2 : ℝ) : ℂ) • (star X * X) ≤ F (star X * X) := by
  have he : star (F X) * F X = ((lam ^ 2 : ℝ) : ℂ) • (star X * X) := by
    rw [heigen]
    simp only [star_smul, Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, mul_smul_comm, smul_smul, pow_two, Complex.ofReal_mul]
  rw [← he]
  exact completelyPositiveMap_schwarz F hF X

variable [NeZero d]

theorem matrix_positive_corner_moment_bound (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (Q Y : CMatrix d) (hY : 0 ≤ Y) (hYQ : Y * Q = Y)
    (c sigma : ℝ) (horder : (c : ℂ) • Y ≤ F Y)
    (herror : hsNorm (F Y - Q) ≤ sigma * hsNorm Y) :
    (c - sigma) * hsNorm Y ^ 2 ≤ (normalizedTrace Y).re := by
  have hb : (normalizedTrace (Y * (F Y - Q))).re ≤ sigma * hsNorm Y ^ 2 := by
    calc
      _ ≤ |(normalizedTrace (Y * (F Y - Q))).re| := le_abs_self _
      _ ≤ hsNorm Y * hsNorm (F Y - Q) := by
        simpa only [hY.isSelfAdjoint.star_eq] using abs_normalizedTrace_pairing_re_le Y (F Y - Q)
      _ ≤ hsNorm Y * (sigma * hsNorm Y) := mul_le_mul_of_nonneg_left herror (hsNorm_nonneg _)
      _ = _ := by ring
  have ho := normalizedTrace_mul_re_mono hY horder
  have hsq : (normalizedTrace (Y * Y)).re = hsNorm Y ^ 2 := by
    simpa only [hY.isSelfAdjoint.star_eq, Complex.ofReal_re] using congrArg Complex.re (normalizedTrace_gram Y)
  rw [mul_smul_comm, normalizedTrace_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hsq] at ho
  rw [mul_sub, normalizedTrace_sub, Complex.sub_re, hYQ] at hb
  linarith only [hb, ho]

theorem matrixUCP_corner_fourth_moment (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (Q : CMatrix d) (hQ : IsStarProjection Q) (hne : Q ≠ 0) (lam sigma : ℝ)
    (hcorner : ∀ Y : CMatrix d, Q * Y = Y → Y * Q = Y →
      hsNorm (F Y - (normalizedTrace Y / normalizedTrace Q) • Q) ≤ sigma * hsNorm Y)
    (X : CMatrix d) (hright : X * Q = X)
    (hmass : normalizedTrace (star X * X) = normalizedTrace Q)
    (heigen : F X = (lam : ℂ) • X) :
    (lam ^ 2 - sigma) * hsNorm (star X * X) ^ 2 ≤ hsNorm X ^ 2 := by
  have hs : Q * star X = star X := by
    simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using congrArg star hright
  have hl : Q * (star X * X) = star X * X := by rw [← mul_assoc, hs]
  have hr : (star X * X) * Q = star X * X := by rw [mul_assoc, hright]
  have hb := hcorner (star X * X) hl hr
  rw [hmass, div_self (normalizedTrace_projection_ne_zero hQ hne), one_smul] at hb
  have he := matrix_positive_corner_moment_bound F.toLinearMap Q (star X * X)
    (star_mul_self_nonneg X) hr (lam ^ 2) sigma
    (matrixUCP_eigenvector_gram_le F hF lam X heigen) hb
  simpa only [normalizedTrace_gram, Complex.ofReal_re] using he

theorem matrix_corner_trace_sq_le (P Y : CMatrix d) (hP : IsStarProjection P)
    (hleft : P * Y = Y) :
    (normalizedTrace Y).re ^ 2 ≤ (normalizedTrace P).re * hsNorm Y ^ 2 := by
  have hb := abs_normalizedTrace_pairing_re_le P Y
  rw [hP.isSelfAdjoint.star_eq, hleft] at hb
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simpa only [sq_abs, mul_pow, hsNorm_projection_sq hP] using hs

end ThomGame.Analysis
