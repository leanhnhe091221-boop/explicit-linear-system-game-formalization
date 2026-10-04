module

public import ThomGame.Analysis.CPMapSchwarz
public import ThomGame.Analysis.FiniteMatrixHilbert
public import ThomGame.Analysis.MatrixPositivePartTrace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Trace Hilbert contraction and actual operators of matrix channels

Unital completely positive maps preserving the ambient normalized trace
are contractions in both matrix norms. Trace-pairing self-adjointness
is transported to an actual continuous operator on the trace Hilbert
space. The two Gram matrices have exactly the same second moment.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat}

theorem hsNorm_mul_star_eq_star_mul (X : CMatrix d) :
    hsNorm (X * star X) = hsNorm (star X * X) := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  have he : normalizedTrace (star (X * star X) * (X * star X)) =
      normalizedTrace (star (star X * X) * (star X * X)) := by
    simp only [star_mul, star_star]
    calc
      _ = normalizedTrace (X * (star X * X * star X)) := by simp only [mul_assoc]
      _ = normalizedTrace ((star X * X * star X) * X) := normalizedTrace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]
  simpa only [normalizedTrace_gram, Complex.ofReal_re] using congrArg Complex.re he

theorem matrixUCP_matrixOpNorm_le (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1) (X : CMatrix d) :
    matrixOpNorm (F X) ≤ matrixOpNorm X := completelyPositiveMap_norm_le F hF X

theorem matrixUCP_hsNorm_le (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    hsNorm (F X) ≤ hsNorm X := by
  have he := normalizedTrace_re_mono (completelyPositiveMap_schwarz F hF X)
  rw [htrace, normalizedTrace_gram, normalizedTrace_gram, Complex.ofReal_re, Complex.ofReal_re] at he
  exact (sq_le_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp he

variable [NeZero d]

noncomputable def matrixMapHilbert (F : CMatrix d →ₗ[ℂ] CMatrix d) :
    FiniteMatrixHilbert d →L[ℂ] FiniteMatrixHilbert d :=
  ((finiteMatrixHilbertEquiv d).toLinearMap.comp
    (F.comp (finiteMatrixHilbertEquiv d).symm.toLinearMap)).toContinuousLinearMap

@[simp] theorem matrixMapHilbert_apply (F : CMatrix d →ₗ[ℂ] CMatrix d) (X : CMatrix d) :
    matrixMapHilbert F (finiteMatrixHilbertEquiv d X) = finiteMatrixHilbertEquiv d (F X) := rfl

theorem matrixMapHilbert_isSymmetric (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (hF : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y)) :
    (matrixMapHilbert F).IsSymmetric := by
  intro ξ η
  obtain ⟨X, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
  obtain ⟨Y, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective η
  change inner ℂ (matrixMapHilbert F (finiteMatrixHilbertEquiv d X)) (finiteMatrixHilbertEquiv d Y) =
    inner ℂ (finiteMatrixHilbertEquiv d X) (matrixMapHilbert F (finiteMatrixHilbertEquiv d Y))
  simpa only [matrixMapHilbert_apply, finiteMatrixHilbert_inner] using hF X Y

theorem matrixUCP_hilbert_norm_le (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) :
    ‖matrixMapHilbert F.toLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  obtain ⟨X, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
  rw [matrixMapHilbert_apply, finiteMatrixHilbert_norm, finiteMatrixHilbert_norm, one_mul]
  exact matrixUCP_hsNorm_le F hF htrace X

theorem matrixUCP_real_eigenvalue_abs_le_one (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (lam : ℝ)
    (X : CMatrix d) (hX : X ≠ 0) (heigen : F X = (lam : ℂ) • X) : |lam| ≤ 1 := by
  have hn : 0 < hsNorm X := lt_of_le_of_ne (hsNorm_nonneg X) (Ne.symm (by
    intro hz
    exact hX ((hsNorm_eq_zero_iff X).mp hz)))
  have hb := matrixUCP_hsNorm_le F hF htrace X
  rw [heigen, hsNorm_smul, Complex.norm_real, Real.norm_eq_abs] at hb
  exact (mul_le_mul_iff_left₀ hn).mp (by simpa only [one_mul] using hb)

end ThomGame.Analysis
