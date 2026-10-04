module

public import ThomGame.Analysis.MatrixALTUnitProjectionBound

/-!
# One operator bound for both matrix-unit and zero rectangles
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixRectangleLineProjection_eq_zero (P Q X : CMatrix d)
    (hl : P * X = X) (hr : X * Q = X) (hX : X = 0) :
    matrixRectangleLineProjection P Q X hl hr = 0 := by
  have hx : matrixRectangleVector P Q X hl hr = 0 := by
    apply Subtype.ext
    change finiteMatrixHilbertEquiv d X = 0
    rw [hX, map_zero]
  have hs : ℂ ∙ matrixRectangleVector P Q X hl hr = ⊥ := Submodule.span_singleton_eq_bot.mpr hx
  simp only [matrixRectangleLineProjection, hs, Submodule.starProjection_bot]

theorem matrixUCP_unit_or_zero_projection_bound {μ : Type*} [Fintype μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ)
    (hinv : ∀ X ∈ matrixRectangleSubmodule (E i) (E j), F X ∈ matrixRectangleSubmodule (E i) (E j))
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hbands : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1))
    (W : CMatrix d) (hWl : E i * W = W) (hWr : W * E j = W)
    (hneiff : W ≠ 0 ↔ matrixRectangleHasHighEigenvalue F.toLinearMap (E i) (E j) rho)
    (hfix : hsNorm (F W - W) ^ 2 ≤ 288 * rho * hsNorm W ^ 2) :
    ‖matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv -
      matrixRectangleLineProjection (E i) (E j) W hWl hWr‖ ≤ 113 * Real.sqrt rho := by
  by_cases hW : W = 0
  · rw [matrixRectangleLineProjection_eq_zero (E i) (E j) W hWl hWr hW, sub_zero]
    have hno : ¬ matrixRectangleHasHighEigenvalue F.toLinearMap (E i) (E j) rho :=
      fun h => (hneiff.mpr h) hW
    have hlow := matrixUCP_no_high_rectangle_norm_le F hF htrace hpair (E i) (E j) hinv
      rho hrho hbands hno
    have hs := Real.sq_sqrt hrho
    have hp : rho ^ 2 ≤ rho := by nlinarith
    have hr : rho ≤ Real.sqrt rho := by nlinarith [Real.sqrt_nonneg rho]
    linarith [Real.sqrt_nonneg rho]
  · exact matrixUCP_high_unit_projection_bound F hF htrace hpair E hE hne i j hinv
      rho hrho hsmall hsigma hbands (hneiff.mp hW) W hW hWl hWr hfix

end ThomGame.Analysis
