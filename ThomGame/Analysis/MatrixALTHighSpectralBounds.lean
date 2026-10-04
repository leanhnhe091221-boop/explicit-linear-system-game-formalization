module

public import ThomGame.Analysis.MatrixALTHighUniqueness
public import ThomGame.Analysis.OrthonormalOperatorBounds

/-!
# Actual rectangular operator bounds after high-direction uniqueness

The genuine orthonormal eigenbasis has at most one high index. The
operator is rho-close to the projection onto that vector, or has norm
at most rho when no high index exists.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem exists_matrixUCP_rectangle_spectral_bounds
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (hinv : ∀ X ∈ matrixRectangleSubmodule (E i) (E j), F X ∈ matrixRectangleSubmodule (E i) (E j))
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hbands : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ (matrixRectangleHilbert (E i) (E j)))) ℂ
        (matrixRectangleHilbert (E i) (E j)),
      ∃ lam : Fin (Module.finrank ℂ (matrixRectangleHilbert (E i) (E j))) → ℝ,
        (∀ k, |lam k| ≤ 1 ∧ F ((finiteMatrixHilbertEquiv d).symm (b k).val) =
          (lam k : ℂ) • (finiteMatrixHilbertEquiv d).symm (b k).val) ∧
        (∀ k l, 1 - rho ≤ lam k → 1 - rho ≤ lam l → k = l) ∧
        (∀ k, 1 - rho ≤ lam k →
          ‖matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv - (ℂ ∙ b k).starProjection‖ ≤ rho) ∧
        ((∀ k, lam k < 1 - rho) → ‖matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv‖ ≤ rho) := by
  obtain ⟨b, lam, hb⟩ := exists_matrixRectangle_orthonormal_eigenbasis F hF htrace (E i) (E j) hinv hpair
  let X := fun k => (finiteMatrixHilbertEquiv d).symm (b k).val
  have hx k : X k ≠ 0 := by
    intro hz
    apply b.orthonormal.ne_zero k
    apply Subtype.ext
    apply (finiteMatrixHilbertEquiv d).symm.injective
    exact hz
  have hl k : E i * X k = X k := (b k).property.1
  have hr k : X k * E j = X k := (b k).property.2
  have hband k := hbands (lam k) (X k) (hx k) (hl k) (hr k) (hb k).2
  have huniq : ∀ k l, 1 - rho ≤ lam k → 1 - rho ≤ lam l → k = l := by
    intro k l hk hl'
    by_contra hkl
    have hn := matrixUCP_no_orthogonal_high_rectangle F hF htrace E hE hne i j (X k) (X l)
      (hx k) (hx l) (hl k) (hr k) (hl l) (hr l) (lam k) (lam l) rho hrho hsmall hsigma (hb k).2 (hb l).2 hk hl'
    apply hn
    change inner ℂ (b k) (b l) = 0
    exact b.inner_eq_zero hkl
  let T := matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv
  have hT : T.toLinearMap.IsSymmetric := matrixRectangleHilbertMap_isSymmetric F.toLinearMap (E i) (E j) hinv hpair
  have he k : T (b k) = (lam k : ℂ) • b k := by
    apply Subtype.ext
    apply (finiteMatrixHilbertEquiv d).symm.injective
    exact (hb k).2
  refine ⟨b, lam, hb, huniq, ?_, ?_⟩
  · intro k hk
    apply symmetric_eigenbasis_sub_lineProjection_norm_le b T hT lam he k rho hrho
    · have hu := (le_abs_self (lam k)).trans (hb k).1
      rw [abs_of_nonpos (by linarith : lam k - 1 ≤ 0)]
      linarith
    · intro l hlk
      rcases hband l with hbLow | hbHigh
      · exact abs_le.mpr hbLow
      · exact False.elim (hlk (huniq l k hbHigh.1 hk))
  · intro hlow
    apply symmetric_eigenbasis_norm_le b T hT lam he rho hrho
    intro k
    rcases hband k with hbLow | hbHigh
    · exact abs_le.mpr hbLow
    · exact False.elim ((not_lt_of_ge hbHigh.1) (hlow k))

end ThomGame.Analysis
