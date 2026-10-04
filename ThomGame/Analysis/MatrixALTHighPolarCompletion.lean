module

public import ThomGame.Analysis.MatrixALTHighPolarBounds
public import ThomGame.Analysis.MatrixALTReconstructionMoments
public import ThomGame.Analysis.MatrixChannelEigenEnergy

/-!
# ALT (5.6) with actual polar completions and absolute constants

A normalized high rectangular eigenvector of the actual channel has a
rank-minimum polar completion. The squared distance and fixing error
are bounded by 4rho and 36rho times its original normalized mass.
The two corner ranks differ by at most the accompanying ratio bound.
The actual channel energy of the completion is at most 18rho times its mass.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem exists_matrixUCP_high_polar_completion (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Y, normalizedTrace (F Y) = normalizedTrace Y)
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (X : CMatrix d) (hX : X ≠ 0) (hl : E i * X = X) (hr : X * E j = X)
    (hnorm : hsNorm X ^ 2 = ((max (E i).rank (E j).rank : Nat) : ℝ) / d)
    (lam rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 4)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (heigen : F X = (lam : ℂ) • X) (hhigh : 1 - rho ≤ lam) :
    ∃ U : CMatrix d, E i * U = U ∧ U * E j = U ∧
      IsStarProjection (star U * U) ∧ IsStarProjection (U * star U) ∧
      star U * U ≤ E j ∧ U * star U ≤ E i ∧
      (star U * U).rank = min (E i).rank (E j).rank ∧
      (U * star U).rank = min (E i).rank (E j).rank ∧
      star U * X = matrixRectAbs X ∧ matrixOpNorm U ≤ 1 ∧
      hsNorm (U - X) ^ 2 ≤ 4 * rho * hsNorm X ^ 2 ∧
      hsNorm (F U - U) ^ 2 ≤ 36 * rho * hsNorm X ^ 2 ∧
      1 - 2 * rho ≤ ((min (E i).rank (E j).rank : Nat) : ℝ) / ((max (E i).rank (E j).rank : Nat) : ℝ) ∧
      matrixChannelEnergy F.toLinearMap U ≤ 18 * rho * hsNorm X ^ 2 := by
  let sigma := matrixScalarMixingError E F.toLinearMap
  have hc (k : μ) (Y : CMatrix d) (hyl : E k * Y = Y) (hyr : Y * E k = Y) :
      hsNorm (F Y - (normalizedTrace Y / normalizedTrace (E k)) • E k) ≤ sigma * hsNorm Y :=
    matrixScalarMixingError_hsNorm_le E F.toLinearMap k Y hyl hyr
  have hm : max (normalizedTrace (E i)).re (normalizedTrace (E j)).re =
      ((max (E i).rank (E j).rank : Nat) : ℝ) / d := by
    rw [matrixProjection_trace_eq_rank (hE i), matrixProjection_trace_eq_rank (hE j),
      max_div_div_right (Nat.cast_nonneg d), Nat.cast_max]
  obtain ⟨hfour, hratio⟩ := matrixUCP_rectangular_moment_bounds F hF (E i) (E j) (hE i) (hE j) (hne i) (hne j)
    lam sigma (hc i) (hc j) X hX hl hr (hnorm.trans hm.symm) heigen
  rw [hm, ← hnorm] at hfour
  rw [matrixProjection_trace_min_max_ratio (E i) (E j) (hE i) (hE j)] at hratio
  obtain ⟨U, hUl, hUr, hUi, hUf, hUiQ, hUfP, hUir, hUfr, hUX, hUn⟩ :=
    exists_matrixPolar_min_rank_completion (E i) (E j) X (hE i) (hE j) hl hr
  have hd := matrixPolarCompletion_high_distance (E i) (E j) X U hUi hUX hUir hnorm lam sigma rho
    hrho hsmall hsigma hhigh hfour
  have hlam : |lam - 1| ≤ rho := by
    have hn := matrixUCP_real_eigenvalue_abs_le_one F hF htrace lam X hX heigen
    have hu := (le_abs_self lam).trans hn
    rw [abs_of_nonpos (by linarith : lam - 1 ≤ 0)]
    linarith
  have hf := matrixUCP_near_eigenvector_fixed_error F hF htrace X U lam rho hrho
    (by linarith) heigen hlam hd
  exact ⟨U, hUl, hUr, hUi, hUf, hUiQ, hUfP, hUir, hUfr, hUX, hUn, hd, hf,
    (alt_high_eigenvalue_gap rho sigma lam hrho hsmall hsigma hhigh).1.trans hratio,
    matrixUCP_high_polar_energy F hF htrace X U lam rho heigen hhigh hd⟩

end ThomGame.Analysis
