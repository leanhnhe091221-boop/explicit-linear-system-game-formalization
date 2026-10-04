module

public import ThomGame.Analysis.MatrixALTBadEigenvalue

/-!
# Diagonal blocks have no bad eigenvalues

Trace preservation forces every eigenvector with eigenvalue different
from one to have zero trace. The actual scalar-corner error controls
all such eigenvalues. Adjoint preservation also reverses rectangles.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixScalarCorner_eigenvalue_dichotomy (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (P : CMatrix d) (sigma : ℝ)
    (hcorner : ∀ Y : CMatrix d, P * Y = Y → Y * P = Y →
      hsNorm (F Y - (normalizedTrace Y / normalizedTrace P) • P) ≤ sigma * hsNorm Y)
    (X : CMatrix d) (hX : X ≠ 0) (hl : P * X = X) (hr : X * P = X)
    (lam : ℝ) (heigen : F X = (lam : ℂ) • X) : lam = 1 ∨ |lam| ≤ sigma := by
  by_cases hlam : lam = 1
  · exact Or.inl hlam
  · right
    have ht := htrace X
    rw [heigen, normalizedTrace_smul] at ht
    have hz : ((lam : ℂ) - 1) * normalizedTrace X = 0 := by rw [sub_mul, one_mul, ht, sub_self]
    have htraceX : normalizedTrace X = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exfalso
        apply hlam
        exact Complex.ofReal_inj.mp (by simpa only [Complex.ofReal_one] using sub_eq_zero.mp h)
      · exact h
    have hb := hcorner X hl hr
    rw [htraceX, zero_div, zero_smul, sub_zero, heigen, hsNorm_smul,
      Complex.norm_real, Real.norm_eq_abs] at hb
    have hn : 0 < hsNorm X := lt_of_le_of_ne (hsNorm_nonneg X)
      (Ne.symm (fun h => hX ((hsNorm_eq_zero_iff X).mp h)))
    exact (mul_le_mul_iff_left₀ hn).mp hb

theorem matrixScalarMixingError_diagonal_eigenvalue {μ : Type*} [Fintype μ]
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (E : μ → CMatrix d) (i : μ) (X : CMatrix d) (hX : X ≠ 0)
    (hl : E i * X = X) (hr : X * E i = X) (lam : ℝ) (heigen : F X = (lam : ℂ) • X) :
    lam = 1 ∨ |lam| ≤ matrixScalarMixingError E F :=
  matrixScalarCorner_eigenvalue_dichotomy F htrace (E i) (matrixScalarMixingError E F)
    (fun Y hyl hyr => matrixScalarMixingError_hsNorm_le E F i Y hyl hyr) X hX hl hr lam heigen

theorem matrixALT_no_bad_diagonal {μ : Type*} [Fintype μ]
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (E : μ → CMatrix d) (i : μ) (X : CMatrix d) (hX : X ≠ 0)
    (hl : E i * X = X) (hr : X * E i = X) (lam rho : ℝ) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / 2) (hsigma : matrixScalarMixingError E F ≤ rho ^ 4)
    (heigen : F X = (lam : ℂ) • X) : ¬ (rho < |lam| ∧ rho < 1 - lam) := by
  intro hbad
  rcases matrixScalarMixingError_diagonal_eigenvalue F htrace E i X hX hl hr lam heigen with h | h
  · rw [h] at hbad
    linarith [hbad.2]
  · have h2 : rho ^ 2 ≤ rho := by nlinarith
    have h4 : rho ^ 4 ≤ rho ^ 2 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg rho) h2 2
    linarith [hbad.1]

omit [NeZero d] in
theorem matrixUCP_rectangular_eigenvector_star (F : CMatrix d →CP CMatrix d)
    (P Q X : CMatrix d) (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hX : X ≠ 0) (hl : P * X = X) (hr : X * Q = X)
    (lam : ℝ) (heigen : F X = (lam : ℂ) • X) :
    star X ≠ 0 ∧ Q * star X = star X ∧ star X * P = star X ∧
      F (star X) = (lam : ℂ) • star X := by
  refine ⟨star_ne_zero.mpr hX, ?_, ?_, ?_⟩
  · simpa only [star_mul, hQ.star_eq] using congrArg star hr
  · simpa only [star_mul, hP.star_eq] using congrArg star hl
  · rw [completelyPositiveMap_star, heigen, star_smul, Complex.star_def, Complex.conj_ofReal]

end ThomGame.Analysis
