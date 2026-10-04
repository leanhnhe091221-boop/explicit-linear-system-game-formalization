module

public import ThomGame.Analysis.MatrixALTHighIsometry
public import ThomGame.Analysis.FiniteClassMinimum

/-!
# Coherent minimum-rank representatives and actual class isometries

The high relation on the retained set is proved to be an equivalence
relation. A choice on its quotient supplies one minimum-rank corner
per class, and each actual polar completion fills that corner.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem exists_matrixALT_class_isometries {μ : Type*} [Fintype μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4) (S : Finset μ)
    (hbands : ∀ a ∈ S, ∀ b ∈ S, ∀ (lam : ℝ) (X : CMatrix d),
      X ≠ 0 → E a * X = X → X * E b = X → F X = (lam : ℂ) • X →
      (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) :
    ∃ (o : S → S) (U : S → CMatrix d),
      (∀ i, matrixRectangleHasHighEigenvalue F.toLinearMap (E i.val) (E (o i).val) rho) ∧
      (∀ i j, matrixRectangleHasHighEigenvalue F.toLinearMap (E i.val) (E j.val) rho ↔ o i = o j) ∧
      (∀ i j, o i = o j → (E (o i).val).rank ≤ (E j.val).rank) ∧
      (∀ i, o (o i) = o i) ∧ (∀ i, U (o i) = E (o i).val) ∧
      (∀ i, E i.val * U i = U i ∧ U i * E (o i).val = U i ∧ star (U i) * U i = E (o i).val ∧
        IsStarProjection (U i * star (U i)) ∧ U i * star (U i) ≤ E i.val ∧
        (U i * star (U i)).rank = (E (o i).val).rank ∧ matrixOpNorm (U i) ≤ 1 ∧
        matrixChannelEnergy F.toLinearMap (U i) ≤ 36 * rho * (normalizedTrace (E (o i).val)).re ∧
        (1 - 2 * rho) * (normalizedTrace (E i.val)).re ≤ (normalizedTrace (E (o i).val)).re) := by
  classical
  let r := fun i j : S => matrixRectangleHasHighEigenvalue F.toLinearMap (E i.val) (E j.val) rho
  have he : Equivalence r := matrixUCP_retained_high_equivalence F hF htrace hpair E hE hne hbimod
    rho hrho hsmall hsigma (S : Set μ) hbands
  obtain ⟨o, hrel, hconst, hmin, hid⟩ := exists_finite_class_minimum r he (fun i => (E i.val).rank)
  have hiff i j : r i j ↔ o i = o j := by
    refine ⟨hconst i j, ?_⟩
    intro h
    exact he.trans (hrel i) (h ▸ he.symm (hrel j))
  have hex (i : S) := exists_matrixUCP_high_smaller_isometry F hF htrace hpair E hE hne hbimod
    i.val (o i).val (hmin i i (he.refl i)) rho hrho hsmall hsigma
      (hbands i.val i.property (o i).val (o i).property) (hrel i)
  choose U hU using hex
  refine ⟨o, U, hrel, hiff, ?_, hid, ?_, ?_⟩
  · intro i j hij
    exact hmin i j ((hiff i j).mpr hij)
  · intro i
    obtain ⟨_, _, _, _, _, _, _, _, _, hdiag⟩ := hU (o i)
    exact hdiag (congrArg Subtype.val (hid i).symm)
  · intro i
    obtain ⟨hl, hr, hi, hf, hle, hrank, hnorm, henergy, hmass, _⟩ := hU i
    exact ⟨hl, hr, hi, hf, hle, hrank, hnorm, henergy, hmass⟩

end ThomGame.Analysis
