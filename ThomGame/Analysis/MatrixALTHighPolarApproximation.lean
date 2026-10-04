module

public import ThomGame.Analysis.MatrixALTHighProjectionBound

/-!
# ALT (5.8) with an actual rank-minimum polar completion

The genuine rectangle operator is within 9sqrt(rho) of the actual
orthogonal projection onto the completed partial-isometry direction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem exists_matrixUCP_high_polar_approximation
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
    (hXm : hsNorm X ^ 2 = ((max (E i).rank (E j).rank : Nat) : ℝ) / d)
    (nu : ℝ) (heX : F X = (nu : ℂ) • X) (hhX : 1 - rho ≤ nu) :
    ∃ (U : CMatrix d) (hUl : E i * U = U) (hUr : U * E j = U),
      U ≠ 0 ∧ IsStarProjection (star U * U) ∧ IsStarProjection (U * star U) ∧
      star U * U ≤ E j ∧ U * star U ≤ E i ∧
      (star U * U).rank = min (E i).rank (E j).rank ∧
      (U * star U).rank = min (E i).rank (E j).rank ∧ matrixOpNorm U ≤ 1 ∧
      matrixChannelEnergy F.toLinearMap U ≤ 18 * rho * hsNorm X ^ 2 ∧
      1 - 2 * rho ≤ ((min (E i).rank (E j).rank : Nat) : ℝ) / ((max (E i).rank (E j).rank : Nat) : ℝ) ∧
      ‖matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv -
        matrixRectangleLineProjection (E i) (E j) U hUl hUr‖ ≤ 9 * Real.sqrt rho := by
  obtain ⟨U, hUl, hUr, hUi, hUf, hUiQ, hUfP, hUir, hUfr, hUX, hUn, hdU, hfU, hrU, heU⟩ :=
    exists_matrixUCP_high_polar_completion F hF htrace E hE hne i j X hX hXl hXr hXm
      nu rho hrho (by linarith) hsigma heX hhX
  have hUne : U ≠ 0 := by
    intro hz
    rw [hz, zero_sub, hsNorm_neg] at hdU
    have hm : 0 < hsNorm X ^ 2 := sq_pos_of_ne_zero ((hsNorm_eq_zero_iff X).not.mpr hX)
    have he : 1 ≤ 4 * rho := (mul_le_mul_iff_left₀ hm).mp (by simpa only [one_mul] using hdU)
    linarith
  have hspec := matrixUCP_high_rectangle_projection_bound F hF htrace hpair E hE hne i j hinv
    rho hrho hsmall hsigma hbands X hX hXl hXr nu heX hhX
  have hdist : hsNorm (X - U) ^ 2 ≤ (4 * rho) * hsNorm X ^ 2 := by
    simpa only [hsNorm_sub_comm X U] using hdU
  have hp := matrixRectangleLineProjection_distance_sq (E i) (E j) X U hXl hXr hUl hUr hX hUne (4 * rho) hdist
  have hp' : ‖matrixRectangleLineProjection (E i) (E j) X hXl hXr -
      matrixRectangleLineProjection (E i) (E j) U hUl hUr‖ ≤ 8 * Real.sqrt rho := by
    have hnn := norm_nonneg (matrixRectangleLineProjection (E i) (E j) X hXl hXr -
      matrixRectangleLineProjection (E i) (E j) U hUl hUr)
    have hn8 : 0 ≤ 8 * Real.sqrt rho := by positivity
    apply (sq_le_sq₀ hnn hn8).mp
    rw [mul_pow, Real.sq_sqrt hrho]
    nlinarith only [hp]
  have he : matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv -
      matrixRectangleLineProjection (E i) (E j) U hUl hUr =
      (matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv -
        matrixRectangleLineProjection (E i) (E j) X hXl hXr) +
      (matrixRectangleLineProjection (E i) (E j) X hXl hXr -
        matrixRectangleLineProjection (E i) (E j) U hUl hUr) := by abel
  refine ⟨U, hUl, hUr, hUne, hUi, hUf, hUiQ, hUfP, hUir, hUfr, hUn, heU, hrU, ?_⟩
  rw [he]
  have hb := (norm_add_le
    (matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv - matrixRectangleLineProjection (E i) (E j) X hXl hXr)
    (matrixRectangleLineProjection (E i) (E j) X hXl hXr - matrixRectangleLineProjection (E i) (E j) U hUl hUr)).trans
      (add_le_add hspec hp')
  have hr : rho ≤ Real.sqrt rho := Real.le_sqrt_self_iff.mpr (by linarith)
  linarith

end ThomGame.Analysis
