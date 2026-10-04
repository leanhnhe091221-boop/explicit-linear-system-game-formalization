module

public import ThomGame.Analysis.MatrixALTHighPolarApproximation

/-!
# Both branches of ALT (5.8), using the actual high-eigenvalue predicate

The high branch constructs a genuine minimum-rank partial isometry;
the other branch bounds the actual rectangular operator by rho.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat}

def matrixRectangleHasHighEigenvalue (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q : CMatrix d) (rho : ℝ) : Prop :=
  ∃ (lam : ℝ) (X : CMatrix d), X ≠ 0 ∧ P * X = X ∧ X * Q = X ∧ F X = (lam : ℂ) • X ∧ 1 - rho ≤ lam

variable [NeZero d]

theorem matrixUCP_no_high_rectangle_norm_le (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (P Q : CMatrix d) (hinv : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hbands : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → P * X = X → X * Q = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1))
    (hno : ¬ matrixRectangleHasHighEigenvalue F.toLinearMap P Q rho) :
    ‖matrixRectangleHilbertMap F.toLinearMap P Q hinv‖ ≤ rho := by
  obtain ⟨b, lam, hb⟩ := exists_matrixRectangle_orthonormal_eigenbasis F hF htrace P Q hinv hpair
  let T := matrixRectangleHilbertMap F.toLinearMap P Q hinv
  have hT := matrixRectangleHilbertMap_isSymmetric F.toLinearMap P Q hinv hpair
  have he k : T (b k) = (lam k : ℂ) • b k := by
    apply Subtype.ext
    apply (finiteMatrixHilbertEquiv d).symm.injective
    exact (hb k).2
  apply symmetric_eigenbasis_norm_le b T hT lam he rho hrho
  intro k
  let X := (finiteMatrixHilbertEquiv d).symm (b k).val
  have hx : X ≠ 0 := by
    intro hz
    apply b.orthonormal.ne_zero k
    apply Subtype.ext
    apply (finiteMatrixHilbertEquiv d).symm.injective
    exact hz
  rcases hbands (lam k) X hx (b k).property.1 (b k).property.2 (hb k).2 with hl | hh
  · exact abs_le.mpr hl
  · exact False.elim (hno ⟨lam k, X, hx, (b k).property.1, (b k).property.2, (hb k).2, hh.1⟩)

theorem exists_matrixUCP_high_rectangle_approximation {μ : Type*} [Fintype μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (hinv : ∀ X ∈ matrixRectangleSubmodule (E i) (E j), F X ∈ matrixRectangleSubmodule (E i) (E j))
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hbands : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1))
    (hhigh : matrixRectangleHasHighEigenvalue F.toLinearMap (E i) (E j) rho) :
    ∃ (U : CMatrix d) (hUl : E i * U = U) (hUr : U * E j = U),
      U ≠ 0 ∧ IsStarProjection (star U * U) ∧ IsStarProjection (U * star U) ∧
      star U * U ≤ E j ∧ U * star U ≤ E i ∧
      (star U * U).rank = min (E i).rank (E j).rank ∧
      (U * star U).rank = min (E i).rank (E j).rank ∧ matrixOpNorm U ≤ 1 ∧
      matrixChannelEnergy F.toLinearMap U ≤ 18 * rho * (((max (E i).rank (E j).rank : Nat) : ℝ) / d) ∧
      1 - 2 * rho ≤ ((min (E i).rank (E j).rank : Nat) : ℝ) / ((max (E i).rank (E j).rank : Nat) : ℝ) ∧
      ‖matrixRectangleHilbertMap F.toLinearMap (E i) (E j) hinv -
        matrixRectangleLineProjection (E i) (E j) U hUl hUr‖ ≤ 9 * Real.sqrt rho := by
  obtain ⟨lam, X, hX, hXl, hXr, heX, hhX⟩ := hhigh
  change F X = (lam : ℂ) • X at heX
  let M : ℝ := ((max (E i).rank (E j).rank : Nat) : ℝ) / d
  have hM : 0 < M := by
    have hp := matrixProjection_trace_re_pos (hE i) (hne i)
    rw [matrixProjection_trace_eq_rank (hE i)] at hp
    exact hp.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left (E i).rank (E j).rank)
      (Nat.cast_nonneg d))
  obtain ⟨a, ha, hXa⟩ := exists_matrixHS_positive_rescaling X hX M hM
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hx : (a : ℂ) • X ≠ 0 := smul_ne_zero ha' hX
  have hxL : E i * ((a : ℂ) • X) = (a : ℂ) • X := by rw [mul_smul_comm, hXl]
  have hxR : ((a : ℂ) • X) * E j = (a : ℂ) • X := by rw [smul_mul_assoc, hXr]
  have hxE : F ((a : ℂ) • X) = (lam : ℂ) • ((a : ℂ) • X) := by rw [map_smul, heX, smul_comm]
  obtain ⟨U, hUl, hUr, hUne, hUi, hUf, hUiQ, hUfP, hUir, hUfr, hUn, heU, hrU, happrox⟩ :=
    exists_matrixUCP_high_polar_approximation F hF htrace hpair E hE hne i j hinv rho hrho hsmall hsigma
      hbands ((a : ℂ) • X) hx hxL hxR hXa lam hxE hhX
  rw [hXa] at heU
  exact ⟨U, hUl, hUr, hUne, hUi, hUf, hUiQ, hUfP, hUir, hUfr, hUn, heU, hrU, happrox⟩

end ThomGame.Analysis
