module

public import ThomGame.Analysis.MatrixUCPTraceBounds
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Actual invariant rectangular Hilbert spaces of bimodular maps

The support equations define the rectangular blocks as subspaces of the
ambient trace Hilbert space. Bimodularity proves invariance, and the
restriction of a trace-self-adjoint channel has a genuine orthonormal
eigenbasis with real eigenvalues in [-1,1].
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat}

def matrixRectangleSubmodule (P Q : CMatrix d) : Submodule ℂ (CMatrix d) where
  carrier := {X | P * X = X ∧ X * Q = X}
  zero_mem' := ⟨mul_zero P, zero_mul Q⟩
  add_mem' := by
    intro X Y hX hY
    exact ⟨by rw [mul_add, hX.1, hY.1], by rw [add_mul, hX.2, hY.2]⟩
  smul_mem' := by
    intro c X hX
    exact ⟨by rw [mul_smul_comm, hX.1], by rw [smul_mul_assoc, hX.2]⟩

def matrixRectangleHilbert (P Q : CMatrix d) : Submodule ℂ (FiniteMatrixHilbert d) :=
  (matrixRectangleSubmodule P Q).comap (finiteMatrixHilbertEquiv d).symm.toLinearMap

@[simp] theorem mem_matrixRectangleHilbert (P Q X : CMatrix d) :
    finiteMatrixHilbertEquiv d X ∈ matrixRectangleHilbert P Q ↔ P * X = X ∧ X * Q = X := Iff.rfl

theorem matrixBimodule_rectangle_invariant (S : StarSubalgebra ℂ (CMatrix d))
    (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (hF : ∀ A X B, A ∈ S → B ∈ S → F (A * X * B) = A * F X * B)
    (P Q : CMatrix d) (hP : P ∈ S) (hQ : Q ∈ S) :
    ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q := by
  intro X hX
  change P * X = X ∧ X * Q = X at hX
  constructor
  · simpa only [mul_one, hX.1] using (hF P X 1 hP S.one_mem).symm
  · simpa only [one_mul, hX.2] using (hF 1 X Q S.one_mem hQ).symm

variable [NeZero d]

theorem matrixRectangleHilbert_invariant (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q : CMatrix d)
    (hF : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q) :
    ∀ ξ ∈ matrixRectangleHilbert P Q, matrixMapHilbert F ξ ∈ matrixRectangleHilbert P Q := by
  intro ξ hξ
  obtain ⟨X, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
  rw [matrixMapHilbert_apply]
  exact hF X hξ

noncomputable def matrixRectangleHilbertMap (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q : CMatrix d)
    (hF : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q) :
    matrixRectangleHilbert P Q →L[ℂ] matrixRectangleHilbert P Q :=
  (matrixMapHilbert F).restrict (matrixRectangleHilbert_invariant F P Q hF)

theorem matrixRectangleHilbertMap_isSymmetric (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q : CMatrix d)
    (hF : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y)) :
    (matrixRectangleHilbertMap F P Q hF).toLinearMap.IsSymmetric := by
  intro ξ η
  exact matrixMapHilbert_isSymmetric F hpair ξ.val η.val

theorem exists_matrixRectangle_orthonormal_eigenbasis (F : CMatrix d →CP CMatrix d)
    (hF : F 1 = 1) (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (P Q : CMatrix d)
    (hinv : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y)) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ (matrixRectangleHilbert P Q))) ℂ (matrixRectangleHilbert P Q),
      ∃ eig : Fin (Module.finrank ℂ (matrixRectangleHilbert P Q)) → ℝ,
        ∀ i, |eig i| ≤ 1 ∧
          F ((finiteMatrixHilbertEquiv d).symm (b i).val) =
            (eig i : ℂ) • (finiteMatrixHilbertEquiv d).symm (b i).val := by
  let R := matrixRectangleHilbertMap F.toLinearMap P Q hinv
  have hR : R.toLinearMap.IsSymmetric := matrixRectangleHilbertMap_isSymmetric F.toLinearMap P Q hinv hpair
  let b := hR.eigenvectorBasis rfl
  let eig := hR.eigenvalues rfl
  refine ⟨b, eig, ?_⟩
  intro i
  have he := hR.apply_eigenvectorBasis rfl i
  have hm : F ((finiteMatrixHilbertEquiv d).symm (b i).val) =
      (eig i : ℂ) • (finiteMatrixHilbertEquiv d).symm (b i).val := by
    exact congrArg (fun ξ : matrixRectangleHilbert P Q => (finiteMatrixHilbertEquiv d).symm ξ.val) he
  have hx : (finiteMatrixHilbertEquiv d).symm (b i).val ≠ 0 := by
    intro hz
    have hb : b i = 0 := by
      apply Subtype.ext
      apply (finiteMatrixHilbertEquiv d).symm.injective
      exact hz
    exact b.orthonormal.ne_zero i hb
  exact ⟨matrixUCP_real_eigenvalue_abs_le_one F hF htrace (eig i) _ hx hm, hm⟩

theorem exists_matrixRectangle_rescaled_eigenvector (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (P Q X : CMatrix d) (hX : X ≠ 0) (hleft : P * X = X) (hright : X * Q = X)
    (lam M : ℝ) (hM : 0 < M) (heigen : F X = (lam : ℂ) • X) :
    ∃ Y : CMatrix d, Y ≠ 0 ∧ P * Y = Y ∧ Y * Q = Y ∧
      hsNorm Y ^ 2 = M ∧ F Y = (lam : ℂ) • Y := by
  have hn : 0 < hsNorm X := lt_of_le_of_ne (hsNorm_nonneg X) (Ne.symm (by
    intro hz
    exact hX ((hsNorm_eq_zero_iff X).mp hz)))
  let a := Real.sqrt M / hsNorm X
  have ha : 0 < a := div_pos (Real.sqrt_pos.mpr hM) hn
  let Y := (a : ℂ) • X
  have hnorm : hsNorm Y = Real.sqrt M := by
    change hsNorm ((a : ℂ) • X) = _
    rw [hsNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact div_mul_cancel₀ (Real.sqrt M) hn.ne'
  have hy : Y ∈ matrixRectangleSubmodule P Q :=
    (matrixRectangleSubmodule P Q).smul_mem (a : ℂ) ⟨hleft, hright⟩
  refine ⟨Y, ?_, hy.1, hy.2, ?_, ?_⟩
  · intro hz
    rw [hz, hsNorm_zero] at hnorm
    exact (Real.sqrt_pos.mpr hM).ne hnorm
  · rw [hnorm, Real.sq_sqrt hM.le]
  · change F ((a : ℂ) • X) = (lam : ℂ) • ((a : ℂ) • X)
    rw [map_smul, heigen, smul_comm]

end ThomGame.Analysis
