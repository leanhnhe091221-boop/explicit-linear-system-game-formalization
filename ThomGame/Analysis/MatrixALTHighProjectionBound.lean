module

public import ThomGame.Analysis.MatrixALTHighSpectralBounds
public import ThomGame.Analysis.MatrixRectangleLineProjection

/-!
# The actual high-eigenvector projection approximates the rectangle

The eigenbasis construction is eliminated from the statement. Any
nonzero high eigenvector spans its unique high direction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem matrixUCP_high_rectangle_projection_bound
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (hinv : ∀ X ∈ matrixRectangleSubmodule (E i) (E j), F X ∈ matrixRectangleSubmodule (E i) (E j))
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hbands : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1))
    (X : CMatrix d) (hX : X ≠ 0) (hXl : E i * X = X) (hXr : X * E j = X)
    (nu : ℝ) (heX : F X = (nu : ℂ) • X) (hhX : 1 - rho ≤ nu) :
    ‖matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv -
      matrixRectangleLineProjection (E i) (E j) X hXl hXr‖ ≤ rho := by
  obtain ⟨b, lam, hb, huniq, hhigh, hlow⟩ :=
    exists_matrixUCP_rectangle_spectral_bounds F hF htrace hpair E hE hne i j hinv rho hrho hsmall hsigma hbands
  let T := matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv
  let v := matrixRectangleVector (E i) (E j) X hXl hXr
  have hv : v ≠ 0 := matrixRectangleVector_ne_zero (E i) (E j) X hXl hXr hX
  have hvE : T v = (nu : ℂ) • v := by
    apply Subtype.ext
    apply (finiteMatrixHilbertEquiv d).symm.injective
    exact heX
  have hex : ∃ k, 1 - rho ≤ lam k := by
    by_contra! hno
    have hnT : ‖T‖ ≤ rho := hlow hno
    have hn := (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hnT (norm_nonneg v))
    rw [hvE, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hn
    have hn' := (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp hn
    have ha := le_abs_self nu
    linarith
  obtain ⟨k, hk⟩ := hex
  let Y := (finiteMatrixHilbertEquiv d).symm (b k).val
  have hY : Y ≠ 0 := by
    intro hz
    apply b.orthonormal.ne_zero k
    apply Subtype.ext
    apply (finiteMatrixHilbertEquiv d).symm.injective
    exact hz
  obtain ⟨_, c, hc⟩ := matrixUCP_high_rectangle_unique F hF htrace hpair E hE hne i j Y X hY hX
    (b k).property.1 (b k).property.2 hXl hXr (lam k) nu rho hrho hsmall hsigma (hb k).2 heX hk hhX
  have hcne : c ≠ 0 := by intro hz; rw [hz, zero_smul] at hc; exact hX hc
  have hvc : v = c • b k := by
    apply Subtype.ext
    apply (finiteMatrixHilbertEquiv d).symm.injective
    exact hc
  have hspan : ℂ ∙ v = ℂ ∙ b k := by
    rw [hvc]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcne) (b k)
  change ‖T - (ℂ ∙ v).starProjection‖ ≤ rho
  simpa only [hspan] using hhigh k hk

end ThomGame.Analysis
