module

public import ThomGame.Analysis.MatrixALTHighDirections

/-!
# Uniqueness of the high eigendirection of an actual rectangular channel

Trace-pairing symmetry first identifies the eigenvalues. Removing the
component along one eigenvector would otherwise produce a nonzero
orthogonal high eigenvector, already excluded by the polar argument.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem matrixUCP_high_rectangle_unique
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (X Y : CMatrix d) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hXl : E i * X = X) (hXr : X * E j = X) (hYl : E i * Y = Y) (hYr : Y * E j = Y)
    (lam nu rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (heX : F X = (lam : ℂ) • X) (heY : F Y = (nu : ℂ) • Y)
    (hhX : 1 - rho ≤ lam) (hhY : 1 - rho ≤ nu) :
    lam = nu ∧ ∃ c : ℂ, Y = c • X := by
  have hn := matrixUCP_no_orthogonal_high_rectangle F hF htrace E hE hne i j X Y hX hY
    hXl hXr hYl hYr lam nu rho hrho hsmall hsigma heX heY hhX hhY
  have hlam : lam = nu := by
    have he := hpair X Y
    rw [heX, heY, star_smul, smul_mul_assoc, mul_smul_comm,
      normalizedTrace_smul, normalizedTrace_smul, Complex.star_def, Complex.conj_ofReal] at he
    exact Complex.ofReal_injective (mul_right_cancel₀ hn he)
  subst nu
  refine ⟨rfl, ?_⟩
  have hg : normalizedTrace (star X * X) ≠ 0 := by
    rw [normalizedTrace_gram]
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 ((hsNorm_eq_zero_iff X).not.mpr hX))
  let c : ℂ := normalizedTrace (star X * Y) / normalizedTrace (star X * X)
  let Z : CMatrix d := Y - c • X
  have hzpair : normalizedTrace (star X * Z) = 0 := by
    dsimp only [Z, c]
    rw [mul_sub, mul_smul_comm, normalizedTrace_sub, normalizedTrace_smul,
      div_mul_cancel₀ _ hg, sub_self]
  have hzL : E i * Z = Z := by simp only [Z, mul_sub, mul_smul_comm, hYl, hXl]
  have hzR : Z * E j = Z := by simp only [Z, sub_mul, smul_mul_assoc, hYr, hXr]
  have hzE : F Z = (lam : ℂ) • Z := by
    simp only [Z, map_sub, map_smul, heX, heY, smul_sub, smul_comm c (lam : ℂ)]
  have hz : Z = 0 := by
    by_contra hneZ
    exact (matrixUCP_no_orthogonal_high_rectangle F hF htrace E hE hne i j X Z hX hneZ
      hXl hXr hzL hzR lam lam rho hrho hsmall hsigma heX hzE hhX hhX) hzpair
  exact ⟨c, sub_eq_zero.mp hz⟩

end ThomGame.Analysis
