module

public import ThomGame.Analysis.MatrixALTHighEquivalence
public import ThomGame.Analysis.MatrixRetainedBlockProjection

/-!
# Spectral pruning with the actual equivalence relation on retained blocks

The retained set and its spectral bands are constructed by pruning;
the high relation is then proved to be an equivalence relation there.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem exists_matrixALT_retained_equivalence {μ : Type*} [Fintype μ] [DecidableEq μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (horth : Pairwise (fun i j => E i * E j = 0)) (hsum : ∑ i, E i = 1)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hdelta : matrixMixedNorm (F.toLinearMap.comp F.toLinearMap - F.toLinearMap) ≤ rho ^ 4) :
    ∃ S : Finset μ, ∃ p : CMatrix d,
      p = matrixRetainedBlockProjection E S ∧ p = ∑ i ∈ Finset.univ \ S, E i ∧ IsStarProjection p ∧
      (normalizedTrace (1 - p)).re ≤ 64 * rho ^ 2 ∧
      (∀ i ∉ S, ∀ j ∉ S, ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
        F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) ∧
      Equivalence (fun i j : {a // a ∉ S} =>
        matrixRectangleHasHighEigenvalue F.toLinearMap (E i.val) (E j.val) rho) := by
  obtain ⟨S, p, hp, hpsum, hproj, hmass, hbands⟩ := exists_matrixALT_retained_projection
    F hF htrace hpair E hE hne horth hsum hbimod rho hrho (by linarith) hsigma hdelta
  exact ⟨S, p, hp, hpsum, hproj, hmass, hbands,
    matrixUCP_retained_high_equivalence F hF htrace hpair E hE hne hbimod
      rho hrho.le hsmall hsigma {a | a ∉ S} hbands⟩

end ThomGame.Analysis
