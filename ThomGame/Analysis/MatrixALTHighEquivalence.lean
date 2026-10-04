module

public import ThomGame.Analysis.MatrixALTHighTransitivity
public import ThomGame.Analysis.MatrixPartitionScalarAlgebra

/-!
# The high-eigenvalue relation is an equivalence relation

Reflexivity uses the actual fixed block projection. Symmetry uses
adjoint preservation, and transitivity uses the two constructed polar
completions. Bimodularity supplies all support invariance premises.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat}

theorem matrixRectangleHasHighEigenvalue_refl (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (P : CMatrix d) (hP : IsStarProjection P) (hne : P ≠ 0) (hfix : F P = P)
    (rho : ℝ) (hrho : 0 ≤ rho) : matrixRectangleHasHighEigenvalue F P P rho := by
  refine ⟨1, P, hne, hP.isIdempotentElem.eq, hP.isIdempotentElem.eq, ?_, ?_⟩
  · simpa only [Complex.ofReal_one, one_smul] using hfix
  · linarith

theorem matrixUCP_high_rectangle_symm (F : CMatrix d →CP CMatrix d)
    (P Q : CMatrix d) (hP : IsStarProjection P) (hQ : IsStarProjection Q) (rho : ℝ)
    (h : matrixRectangleHasHighEigenvalue F.toLinearMap P Q rho) :
    matrixRectangleHasHighEigenvalue F.toLinearMap Q P rho := by
  obtain ⟨lam, X, hX, hl, hr, he, hh⟩ := h
  refine ⟨lam, star X, star_ne_zero.mpr hX, ?_, ?_, ?_, hh⟩
  · simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using congrArg star hr
  · simpa only [star_mul, hP.isSelfAdjoint.star_eq] using congrArg star hl
  · change F (star X) = (lam : ℂ) • star X
    change F X = (lam : ℂ) • X at he
    rw [completelyPositiveMap_star, he, star_smul, Complex.star_def, Complex.conj_ofReal]

theorem matrixBimodule_fixes_projection {μ : Type*}
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (hF : F 1 = 1) (E : μ → CMatrix d)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B) (i : μ) : F (E i) = E i := by
  simpa only [mul_one, hF] using hbimod (E i) 1 1
    (matrixPartitionScalarAlgebra_projection_mem E i) (matrixPartitionScalarAlgebra E).one_mem

theorem matrixUCP_high_rectangle_equivalence [NeZero d] {μ : Type*} [Fintype μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hbands : ∀ a b, ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E a * X = X → X * E b = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) :
    Equivalence (fun i j => matrixRectangleHasHighEigenvalue F.toLinearMap (E i) (E j) rho) := by
  have hinv a b := matrixBimodule_rectangle_invariant (matrixPartitionScalarAlgebra E) F.toLinearMap
    hbimod (E a) (E b) (matrixPartitionScalarAlgebra_projection_mem E a)
      (matrixPartitionScalarAlgebra_projection_mem E b)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact matrixRectangleHasHighEigenvalue_refl F.toLinearMap (E i) (hE i) (hne i)
      (matrixBimodule_fixes_projection F.toLinearMap hF E hbimod i) rho hrho
  · intro i j hij
    exact matrixUCP_high_rectangle_symm F (E i) (E j) (hE i) (hE j) rho hij
  · intro i j k hij hjk
    exact matrixUCP_high_rectangle_trans F hF htrace hpair E hE hne i j k hinv
      rho hrho hsmall hsigma (hbands i j) (hbands j k) (hbands i k) hij hjk

theorem matrixUCP_retained_high_equivalence [NeZero d] {μ : Type*} [Fintype μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4) (S : Set μ)
    (hbands : ∀ a ∈ S, ∀ b ∈ S, ∀ (lam : ℝ) (X : CMatrix d),
      X ≠ 0 → E a * X = X → X * E b = X → F X = (lam : ℂ) • X →
      (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) :
    Equivalence (fun i j : S => matrixRectangleHasHighEigenvalue F.toLinearMap (E i.val) (E j.val) rho) := by
  have hinv a b := matrixBimodule_rectangle_invariant (matrixPartitionScalarAlgebra E) F.toLinearMap
    hbimod (E a) (E b) (matrixPartitionScalarAlgebra_projection_mem E a)
      (matrixPartitionScalarAlgebra_projection_mem E b)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact matrixRectangleHasHighEigenvalue_refl F.toLinearMap (E i.val) (hE i.val) (hne i.val)
      (matrixBimodule_fixes_projection F.toLinearMap hF E hbimod i.val) rho hrho
  · intro i j hij
    exact matrixUCP_high_rectangle_symm F (E i.val) (E j.val) (hE i.val) (hE j.val) rho hij
  · intro i j k hij hjk
    exact matrixUCP_high_rectangle_trans F hF htrace hpair E hE hne i.val j.val k.val hinv
      rho hrho hsmall hsigma (hbands i.val i.property j.val j.property)
        (hbands j.val j.property k.val k.property) (hbands i.val i.property k.val k.property) hij hjk

end ThomGame.Analysis
