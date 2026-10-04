module

public import ThomGame.Analysis.MatrixEigenvalueDefect
public import ThomGame.Analysis.MatrixALTReconstructionMoments

/-!
# A bad rectangular eigenvalue supplies an actual contraction witness

The scalar error is the actual maximum of corner operator norms.
For rho at most one half, the fourth-moment truncation gives the
constant 1/32 used in ALT's matching argument.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

theorem alt_bad_eigenvalue_gap (rho sigma lam : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 2)
    (hsigma : sigma ≤ rho ^ 4) (hlam : rho < |lam|) :
    0 < lam ^ 2 - sigma ∧ lam ^ 2 / 2 ≤ lam ^ 2 - sigma := by
  have hsq : rho ^ 2 < lam ^ 2 := by
    simpa only [sq_abs] using pow_lt_pow_left₀ hlam hrho.le (by norm_num : 2 ≠ 0)
  have hr : rho ^ 2 ≤ 1 / 4 := by nlinarith
  have hr4 : rho ^ 4 ≤ rho ^ 2 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg rho)]
  constructor <;> nlinarith [sq_nonneg lam]

theorem alt_bad_eigenvalue_polynomial (rho lam : ℝ) (hrho : 0 < rho)
    (hlam : rho < |lam|) (haway : rho < 1 - lam) :
    rho ^ 6 ≤ lam ^ 4 * (1 - lam) ^ 2 := by
  have h4 : rho ^ 4 ≤ lam ^ 4 := by
    simpa only [pow_abs, abs_of_nonneg (by positivity : 0 ≤ lam ^ 4)] using
      pow_le_pow_left₀ hrho.le hlam.le 4
  have h2 : rho ^ 2 ≤ (1 - lam) ^ 2 := pow_le_pow_left₀ hrho.le haway.le 2
  calc
    _ = rho ^ 4 * rho ^ 2 := by ring
    _ ≤ lam ^ 4 * (1 - lam) ^ 2 := mul_le_mul h4 h2 (sq_nonneg rho) (by positivity)

variable {d : Nat} [NeZero d]

theorem matrixALT_bad_eigenvalue_defect (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (hpair : ∀ A B, normalizedTrace (star (F A) * B) = normalizedTrace (star A * F B))
    (X : CMatrix d) (hX : X ≠ 0) (lam sigma rho : ℝ)
    (hrho : 0 < rho) (hsmall : rho ≤ 1 / 2) (hsigma : sigma ≤ rho ^ 4)
    (hlam : rho < |lam|) (haway : rho < 1 - lam)
    (heigen : F X = (lam : ℂ) • X)
    (hmoment : (lam ^ 2 - sigma) * hsNorm (star X * X) ^ 2 ≤ hsNorm X ^ 2) :
    hsNorm X ^ 2 * rho ^ 6 / 32 ≤
      hsNorm (F (F (matrixALTTruncationContraction (lam ^ 2 - sigma) X)) -
        F (matrixALTTruncationContraction (lam ^ 2 - sigma) X)) ^ 2 := by
  obtain ⟨ha, hg⟩ := alt_bad_eigenvalue_gap rho sigma lam hrho hsmall hsigma hlam
  have hd := matrixALTTruncationContraction_defect F hpair X hX lam (lam ^ 2 - sigma) ha heigen hmoment
  have hp := alt_bad_eigenvalue_polynomial rho lam hrho hlam haway
  calc
    _ ≤ hsNorm X ^ 2 * (lam ^ 4 * (1 - lam) ^ 2) / 32 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (sq_nonneg _)) (by norm_num)
    _ = hsNorm X ^ 2 * lam ^ 2 * (1 - lam) ^ 2 * (lam ^ 2 / 2) / 16 := by ring
    _ ≤ hsNorm X ^ 2 * lam ^ 2 * (1 - lam) ^ 2 * (lam ^ 2 - sigma) / 16 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hg (by positivity)
    _ ≤ _ := hd

theorem exists_matrixALT_bad_rectangle_contraction {μ : Type*} [Fintype μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (hpair : ∀ A B, normalizedTrace (star (F A) * B) = normalizedTrace (star A * F B))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (X : CMatrix d) (hX : X ≠ 0) (hl : E i * X = X) (hr : X * E j = X)
    (lam rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 2)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hlam : rho < |lam|) (haway : rho < 1 - lam) (heigen : F X = (lam : ℂ) • X) :
    ∃ Y : CMatrix d, matrixOpNorm Y ≤ 1 ∧ E i * Y = Y ∧ Y * E j = Y ∧
      (((max (E i).rank (E j).rank : Nat) : ℝ) / d) * rho ^ 6 / 32 ≤ hsNorm (F (F Y) - F Y) ^ 2 := by
  let sigma := matrixScalarMixingError E F.toLinearMap
  let M := max (normalizedTrace (E i)).re (normalizedTrace (E j)).re
  have hm : M = ((max (E i).rank (E j).rank : Nat) : ℝ) / d := by
    dsimp only [M]
    rw [matrixProjection_trace_eq_rank (hE i), matrixProjection_trace_eq_rank (hE j),
      max_div_div_right (Nat.cast_nonneg d), Nat.cast_max]
  have hM : 0 < M := by
    rw [hm]
    exact div_pos (Nat.cast_pos.mpr ((matrixProjection_rank_pos (hE i) (hne i)).trans_le
      (le_max_left _ _))) (Nat.cast_pos.mpr (NeZero.pos d))
  obtain ⟨V, hV, hVl, hVr, hVm, hVe⟩ :=
    exists_matrixRectangle_rescaled_eigenvector F.toLinearMap (E i) (E j) X hX hl hr lam M hM heigen
  have hc (k : μ) (Z : CMatrix d) (hzl : E k * Z = Z) (hzr : Z * E k = Z) :
      hsNorm (F Z - (normalizedTrace Z / normalizedTrace (E k)) • E k) ≤ sigma * hsNorm Z :=
    matrixScalarMixingError_hsNorm_le E F.toLinearMap k Z hzl hzr
  have hmoment := (matrixUCP_rectangular_moment_bounds F hF (E i) (E j) (hE i) (hE j) (hne i) (hne j)
    lam sigma (hc i) (hc j) V hV hVl hVr hVm hVe).1
  have ha := (alt_bad_eigenvalue_gap rho sigma lam hrho hsmall hsigma hlam).1
  have hs := matrixALTTruncationContraction_rectangle (lam ^ 2 - sigma) (E i) (E j) V
    (hE j).isSelfAdjoint hVl hVr
  refine ⟨matrixALTTruncationContraction (lam ^ 2 - sigma) V,
    matrixALTTruncationContraction_norm _ ha V, hs.1, hs.2, ?_⟩
  have hb := matrixALT_bad_eigenvalue_defect F.toLinearMap hpair V hV lam sigma rho hrho hsmall hsigma
    hlam haway hVe (hmoment.trans_eq hVm.symm)
  rw [hVm, hm] at hb
  exact hb

end ThomGame.Analysis
