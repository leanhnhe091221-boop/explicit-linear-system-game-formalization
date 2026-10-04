module

public import ThomGame.Analysis.MatrixPolarMinRankCompletion
public import ThomGame.Analysis.MatrixPolarCompletionDistance
public import ThomGame.Analysis.MatrixUCPRectangularMoments

/-!
# Fourth-moment distance to an actual completed polar factor

The scalar inequality 3s^2 <= s^4 + 2s for s >= 0 is transported
through the actual matrix functional calculus. Combined with the
exact polar pairing, it controls the distance including kernel
completion and unequal prescribed corner ranks.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrix_positive_fourth_moment_order (A : CMatrix d) (hA : 0 ≤ A) :
    (3 : ℝ) • A ^ 2 ≤ A ^ 4 + (2 : ℝ) • A := by
  have hm : cfc (fun t : ℝ => 3 * t ^ 2) A ≤ cfc (fun t : ℝ => t ^ 4 + 2 * t) A := by
    apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
    intro t ht
    have hp : 0 ≤ t := spectrum_nonneg_of_nonneg hA ht
    nlinarith [mul_nonneg (mul_nonneg hp (show 0 ≤ t + 2 by linarith)) (sq_nonneg (t - 1))]
  rw [cfc_const_mul _ _ A (A.finite_real_spectrum.continuousOn _),
    cfc_add A (fun t : ℝ => t ^ 4) (fun t : ℝ => 2 * t)
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
    cfc_const_mul _ _ A (A.finite_real_spectrum.continuousOn _),
    cfc_pow_id (R := ℝ) A 2 hA.isSelfAdjoint, cfc_pow_id (R := ℝ) A 4 hA.isSelfAdjoint,
    cfc_id' ℝ A hA.isSelfAdjoint] at hm
  exact hm

theorem matrixRectAbs_fourth_trace (X : CMatrix d) :
    3 * hsNorm X ^ 2 ≤ hsNorm (star X * X) ^ 2 + 2 * (normalizedTrace (matrixRectAbs X)).re := by
  have hm := normalizedTrace_re_mono (matrix_positive_fourth_moment_order (matrixRectAbs X) (matrixRectAbs_nonneg X))
  have hA2 : matrixRectAbs X ^ 2 = star X * X := by
    simpa only [pow_two, Matrix.star_eq_conjTranspose] using matrixRectAbs_mul_self X
  have hA4 : matrixRectAbs X ^ 4 = (star X * X) ^ 2 := by
    rw [show (4 : Nat) = 2 * 2 by norm_num, pow_mul, hA2]
  have hg : (normalizedTrace ((star X * X) ^ 2)).re = hsNorm (star X * X) ^ 2 := by
    simpa only [(star_mul_self_nonneg X).isSelfAdjoint.star_eq, pow_two, Complex.ofReal_re]
      using congrArg Complex.re (normalizedTrace_gram (star X * X))
  change (normalizedTrace ((3 : ℂ) • (matrixRectAbs X ^ 2))).re ≤
    (normalizedTrace (matrixRectAbs X ^ 4 + (2 : ℂ) • matrixRectAbs X)).re at hm
  rw [normalizedTrace_smul, normalizedTrace_add, normalizedTrace_smul, hA2, hA4,
    normalizedTrace_gram, Complex.add_re, Complex.mul_re, Complex.mul_re, hg] at hm
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hm
  norm_num at hm
  exact hm

theorem matrixPolarCompletion_fourth_distance [NeZero d] (X U : CMatrix d)
    (hU : IsStarProjection (star U * U)) (hpair : star U * X = matrixRectAbs X) :
    hsNorm (U - X) ^ 2 ≤ hsNorm (star X * X) ^ 2 - 2 * hsNorm X ^ 2 +
      ((star U * U).rank : ℝ) / d := by
  have he := rectHSNorm_sub_sq d U X
  simp only [rectHSNorm_eq_hsNorm] at he
  have ht (A : CMatrix d) : matrixTraceReal d A = (normalizedTrace A).re := (normalizedTrace_re A).symm
  simp only [ht] at he
  change hsNorm (U - X) ^ 2 = (normalizedTrace (star U * U)).re +
    (normalizedTrace (star X * X)).re - 2 * (normalizedTrace (star U * X)).re at he
  rw [hpair, matrixProjection_trace_eq_rank hU, normalizedTrace_gram, Complex.ofReal_re] at he
  have hb := matrixRectAbs_fourth_trace X
  linarith

end ThomGame.Analysis
