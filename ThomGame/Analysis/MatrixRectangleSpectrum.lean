module

public import ThomGame.Analysis.MatrixBimoduleRectangles
public import ThomGame.Analysis.MatrixPartitionScalarAlgebra

/-!
# Actual spectra of rectangular block restrictions

Every spectral point of a finite-dimensional symmetric block operator
comes from a nonzero matrix eigenvector with real eigenvalue. Thus the
matrix eigenvalue bands imply inclusion of the actual operator spectrum.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixRectangleHilbertMap_spectrum_bands (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q : CMatrix d)
    (hinv : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (rho : ℝ)
    (hbands : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → P * X = X → X * Q = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) :
    spectrum ℂ (matrixRectangleHilbertMap F P Q hinv).toLinearMap ⊆
      Complex.ofReal '' (Set.Icc (-rho) rho ∪ Set.Icc (1 - rho) 1) := by
  intro z hz
  let T := (matrixRectangleHilbertMap F P Q hinv).toLinearMap
  have hT : T.IsSymmetric := matrixRectangleHilbertMap_isSymmetric F P Q hinv hpair
  have he : Module.End.HasEigenvalue T z := Module.End.HasEigenvalue.of_mem_spectrum hz
  have hzreal : (z.re : ℂ) = z := RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self he)
  obtain ⟨v, hv, hvne⟩ := he.exists_hasEigenvector
  have hv' : T v = z • v := Module.End.mem_eigenspace_iff.mp hv
  let X := (finiteMatrixHilbertEquiv d).symm v.val
  have hX : X ≠ 0 := by
    intro hzero
    apply hvne
    apply Subtype.ext
    apply (finiteMatrixHilbertEquiv d).symm.injective
    exact hzero
  have hs : P * X = X ∧ X * Q = X := v.property
  have hXe : F X = (z.re : ℂ) • X := by
    rw [hzreal]
    exact congrArg (fun w : matrixRectangleHilbert P Q => (finiteMatrixHilbertEquiv d).symm w.val) hv'
  exact ⟨z.re, hbands z.re X hX hs.1 hs.2 hXe, hzreal⟩

noncomputable def matrixScalarBimoduleRectangleMap {μ : Type*}
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (E : μ → CMatrix d)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B) (i j : μ) :
    matrixRectangleHilbert (E i) (E j) →L[ℂ] matrixRectangleHilbert (E i) (E j) :=
  matrixRectangleHilbertMap F (E i) (E j)
    (matrixBimodule_rectangle_invariant (matrixPartitionScalarAlgebra E) F hbimod (E i) (E j)
      (matrixPartitionScalarAlgebra_projection_mem E i) (matrixPartitionScalarAlgebra_projection_mem E j))

theorem matrixScalarBimoduleRectangleMap_spectrum_bands {μ : Type*}
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (E : μ → CMatrix d)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (i j : μ) (rho : ℝ)
    (hbands : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) :
    spectrum ℂ (matrixScalarBimoduleRectangleMap F E hbimod i j).toLinearMap ⊆
      Complex.ofReal '' (Set.Icc (-rho) rho ∪ Set.Icc (1 - rho) 1) :=
  matrixRectangleHilbertMap_spectrum_bands F (E i) (E j) _ hpair rho hbands

end ThomGame.Analysis
