module

public import ThomGame.Analysis.RectangularHilbertSchmidt
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Spectral expansion of rectangular matrix intertwiners

The row and column spaces have independent spectral bases. The
normalization remains the explicit original dimension throughout.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def matrixIntertwinerBasis (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  U⁻¹.val * X * V.val

theorem rectHSNorm_intertwiner_basis (r : Nat) (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    rectHSNorm r (matrixIntertwinerBasis U V X) = rectHSNorm r X :=
  rectHSNorm_two_unitaries r U⁻¹ V X

theorem matrixIntertwinerBasis_conjugate (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (D : Matrix ι ι ℂ) (E : Matrix κ κ ℂ)
    (X : Matrix ι κ ℂ) :
    matrixIntertwinerBasis U V
      ((U.val * D * U⁻¹.val) * X - X * (V.val * E * V⁻¹.val)) =
      D * matrixIntertwinerBasis U V X - matrixIntertwinerBasis U V X * E := by
  have hU : U⁻¹.val * U.val = 1 := U.prop.1
  have hV : V⁻¹.val * V.val = 1 := V.prop.1
  simp only [matrixIntertwinerBasis, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U⁻¹.val U.val, hU, Matrix.one_mul, hV, Matrix.mul_one]

theorem rectHSNorm_diagonal_intertwiner_sq (r : Nat) (a : ι → ℝ) (b : κ → ℝ)
    (X : Matrix ι κ ℂ) :
    rectHSNorm r (Matrix.diagonal (fun i => (a i : ℂ)) * X -
      X * Matrix.diagonal (fun j => (b j : ℂ))) ^ 2 =
      (∑ i, ∑ j, ‖X i j‖ ^ 2 * (a i - b j) ^ 2) / r := by
  rw [rectHSNorm_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_comm (X i j), ← sub_mul, ← Complex.ofReal_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]

theorem matrixIntertwinerBasis_cfc {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (f g : ℝ → ℝ) (X : Matrix ι κ ℂ) :
    matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary
      (cfc f A * X - X * cfc g B) =
      Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
        matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X -
      matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X *
        Matrix.diagonal (fun j => (g (hB.eigenvalues j) : ℂ)) := by
  rw [hA.cfc_eq f, hB.cfc_eq g]
  exact matrixIntertwinerBasis_conjugate _ _ _ _ X

theorem rectHSNorm_cfc_intertwiner_sq (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (f g : ℝ → ℝ) (X : Matrix ι κ ℂ) :
    rectHSNorm r (cfc f A * X - X * cfc g B) ^ 2 =
      (∑ i, ∑ j,
        ‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X i j‖ ^ 2 *
        (f (hA.eigenvalues i) - g (hB.eigenvalues j)) ^ 2) / r := by
  rw [← rectHSNorm_intertwiner_basis r hA.eigenvectorUnitary hB.eigenvectorUnitary,
    matrixIntertwinerBasis_cfc hA hB, rectHSNorm_diagonal_intertwiner_sq]

theorem rectHSNorm_intertwiner_spectral_sq (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) (X : Matrix ι κ ℂ) :
    rectHSNorm r (A * X - X * B) ^ 2 =
      (∑ i, ∑ j,
        ‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X i j‖ ^ 2 *
        (hA.eigenvalues i - hB.eigenvalues j) ^ 2) / r := by
  have heA : cfc (fun t : ℝ => t) A = A := cfc_id ℝ A
  have heB : cfc (fun t : ℝ => t) B = B := cfc_id ℝ B
  simpa only [heA, heB] using
    rectHSNorm_cfc_intertwiner_sq r hA hB (fun t => t) (fun t => t) X

end ThomGame.Analysis
