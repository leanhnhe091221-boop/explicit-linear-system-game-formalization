module

public import ThomGame.Analysis.MatrixRangeProjectionDerivative
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Range derivatives along commuting exponential directions

The actual range of exp(t(A+sE))Y has tangent
t((1-p)Ep+pE(1-p)). This holds for arbitrary Y and real t and s;
no differentiability of a selected polar factor is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.Frobenius

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
theorem matrixHermitian_real_smul {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) (t : ℝ) :
    Matrix.IsHermitian (t • A) := by
  show (t • A)ᴴ = t • A
  simp only [Matrix.conjTranspose_smul, star_trivial, hA.eq]

theorem matrixRealExp_affine_factor {A E : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hE : Matrix.IsHermitian E) (hAE : Commute A E) (t s : ℝ) :
    matrixRealExp t (A + s • E) = NormedSpace.exp (s • (t • E)) * matrixRealExp t A := by
  rw [matrixRealExp_eq_exp t (hA.add (matrixHermitian_real_smul hE s)), matrixRealExp_eq_exp t hA]
  have he : t • (A + s • E) = s • (t • E) + t • A := by
    simp only [smul_add, smul_smul]
    rw [mul_comm t s, add_comm]
  rw [he]
  exact NormedSpace.exp_add_of_commute (((hAE.symm.smul_left t).smul_left s).smul_right t)

theorem matrixRealExp_affine_hasDerivAt {A E : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hE : Matrix.IsHermitian E) (hAE : Commute A E) (t s : ℝ) :
    HasDerivAt (fun a => matrixRealExp t (A + a • E))
      ((t • E) * matrixRealExp t (A + s • E)) s := by
  have he := (hasDerivAt_exp_smul_const' (t • E) s).mul_const (matrixRealExp t A)
  simpa only [matrixRealExp_affine_factor hA hE hAE, Matrix.mul_assoc] using! he

noncomputable def matrixExponentialRange (t : ℝ) (A : Matrix ι ι ℂ) (Y : Matrix ι κ ℂ) :
    Matrix ι ι ℂ := matrixRangeProjection (matrixRealExp t A * Y)

theorem matrixExponentialRange_eq_polar (t : ℝ) (A : Matrix ι ι ℂ) (Y : Matrix ι κ ℂ) :
    matrixExponentialRange t A Y =
      matrixExponentialPolarTilt t A Y * (matrixExponentialPolarTilt t A Y)ᴴ := rfl

theorem matrixExponentialRange_isStarProjection (t : ℝ) (A : Matrix ι ι ℂ) (Y : Matrix ι κ ℂ) :
    IsStarProjection (matrixExponentialRange t A Y) := matrixRangeProjection_isStarProjection _

theorem matrixExponentialRange_hasDerivAt {A E : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hE : Matrix.IsHermitian E) (hAE : Commute A E)
    (Y : Matrix ι κ ℂ) (t s : ℝ) :
    HasDerivAt (fun a => matrixExponentialRange t (A + a • E) Y)
      (t • ((1 - matrixExponentialRange t (A + s • E) Y) * E * matrixExponentialRange t (A + s • E) Y +
        matrixExponentialRange t (A + s • E) Y * E * (1 - matrixExponentialRange t (A + s • E) Y))) s := by
  have hX : HasDerivAt (fun a => matrixRealExp t (A + a • E) * Y)
      ((t • E) * (matrixRealExp t (A + s • E) * Y)) s := by
    have he := rectangular_mul_hasDerivAt (matrixRealExp_affine_hasDerivAt hA hE hAE t s)
      (hasDerivAt_const s Y)
    simpa only [Matrix.mul_zero, add_zero, Matrix.mul_assoc] using! he
  have hP (a : ℝ) : matrixRealSupport (matrixRectAbs (matrixRealExp t (A + a • E) * Y)) =
      matrixRealSupport (matrixRectAbs Y) :=
    matrix_absSupport_of_left_inverse _ _ Y
      (matrixRealExp_inverse t (hA.add (matrixHermitian_real_smul hE a)))
  have he := matrixRangeProjection_hasDerivAt (matrixHermitian_real_smul hE t) hP hX
  simpa only [matrixExponentialRange, Matrix.mul_smul, Matrix.smul_mul, smul_add] using! he

end ThomGame.Analysis
