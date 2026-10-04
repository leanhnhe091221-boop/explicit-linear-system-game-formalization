module

public import ThomGame.Analysis.LineProjectionFixedError
public import ThomGame.Analysis.MatrixALTClassMatrixUnits

/-!
# The actual rectangular operator is close to its matrix-unit projection

A high polar completion gives the original rank-one approximation.
The matrix unit's relative fixing error replaces its direction with
the actual matrix unit, including on diagonal rectangles.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixRectangle_lineProjection_of_fixed_error (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (P Q : CMatrix d)
    (hinv : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q)
    (U W : CMatrix d) (hUl : P * U = U) (hUr : U * Q = U)
    (hWl : P * W = W) (hWr : W * Q = W) (hW : W ≠ 0)
    (a b : ℝ)
    (hT : ‖matrixRectangleHilbertMap F P Q hinv - matrixRectangleLineProjection P Q U hUl hUr‖ ≤ a)
    (hfix : hsNorm (F W - W) ≤ b * hsNorm W) :
    ‖matrixRectangleHilbertMap F P Q hinv - matrixRectangleLineProjection P Q W hWl hWr‖ ≤
      5 * a + 4 * b := by
  apply operator_lineProjection_of_fixed_error (matrixRectangleHilbertMap F P Q hinv)
    (matrixRectangleVector P Q U hUl hUr) (matrixRectangleVector P Q W hWl hWr)
      (matrixRectangleVector_ne_zero P Q W hWl hWr hW) a b hT
  change ‖finiteMatrixHilbertEquiv d (F W - W)‖ ≤ b * ‖finiteMatrixHilbertEquiv d W‖
  simpa only [finiteMatrixHilbert_norm] using hfix

theorem matrixUCP_high_unit_projection_bound {μ : Type*} [Fintype μ]
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
    (hhigh : matrixRectangleHasHighEigenvalue F.toLinearMap (E i) (E j) rho)
    (W : CMatrix d) (hW : W ≠ 0) (hWl : E i * W = W) (hWr : W * E j = W)
    (hfix : hsNorm (F W - W) ^ 2 ≤ 288 * rho * hsNorm W ^ 2) :
    ‖matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv -
      matrixRectangleLineProjection (E i) (E j) W hWl hWr‖ ≤ 113 * Real.sqrt rho := by
  obtain ⟨U, hUl, hUr, _, _, _, _, _, _, _, _, _, _, happrox⟩ :=
    exists_matrixUCP_high_rectangle_approximation F hF htrace hpair E hE hne i j hinv
      rho hrho hsmall hsigma hbands hhigh
  have hs : hsNorm (F W - W) ≤ (17 * Real.sqrt rho) * hsNorm W := by
    apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 17) (Real.sqrt_nonneg rho)) (hsNorm_nonneg W))).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hrho]
    nlinarith [mul_nonneg hrho (sq_nonneg (hsNorm W))]
  have hh := matrixRectangle_lineProjection_of_fixed_error F.toLinearMap (E i) (E j) hinv
    U W hUl hUr hWl hWr hW (9 * Real.sqrt rho) (17 * Real.sqrt rho) happrox hs
  linarith

end ThomGame.Analysis
