module

public import ThomGame.Analysis.MatrixPolarGap

/-!
# Unitary covariance of the polar map

The actual polar factor respects changes of basis on both rectangular
spaces. Nonzero singular-value bounds are unchanged by these actions.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrixRectAbs_unitary_left (V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι κ ℂ) :
    matrixRectAbs (V.val * X) = matrixRectAbs X := by
  have hV : V.valᴴ * V.val = 1 := V.prop.1
  unfold matrixRectAbs
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V.valᴴ V.val,
    hV, Matrix.one_mul]

theorem matrixRectPolar_unitary_left (V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι κ ℂ) :
    matrixRectPolar (V.val * X) = V.val * matrixRectPolar X := by
  rw [matrixRectPolar, matrixRectAbs_unitary_left, Matrix.mul_assoc]
  rfl

omit [DecidableEq ι] in
theorem matrixRectAbs_unitary_right_intertwine (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    matrixRectAbs X * U.val = U.val * matrixRectAbs (X * U.val) := by
  have hU : U.val * U.valᴴ = 1 := U.prop.2
  rw [matrixRectAbs, matrixRectAbs,
    matrixSqrt_eq_real_cfc (Matrix.posSemidef_conjTranspose_mul_self X).nonneg,
    matrixSqrt_eq_real_cfc (Matrix.posSemidef_conjTranspose_mul_self (X * U.val)).nonneg]
  apply matrix_cfc_intertwine (Matrix.isHermitian_conjTranspose_mul_self X)
    (Matrix.isHermitian_conjTranspose_mul_self (X * U.val)) Real.sqrt U.val
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U.val U.valᴴ, hU, Matrix.one_mul]

omit [DecidableEq ι] in
theorem matrixRectAbs_unitary_right (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    matrixRectAbs (X * U.val) = U.valᴴ * matrixRectAbs X * U.val := by
  have hU : U.valᴴ * U.val = 1 := U.prop.1
  have he := congrArg (fun A => U.valᴴ * A) (matrixRectAbs_unitary_right_intertwine U X)
  rw [← Matrix.mul_assoc U.valᴴ U.val, hU, Matrix.one_mul] at he
  simpa only [Matrix.mul_assoc] using he.symm

omit [DecidableEq ι] in
theorem matrixRectPolar_unitary_right (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    matrixRectPolar (X * U.val) = matrixRectPolar X * U.val := by
  have he := matrix_cfc_intertwine (matrixRectAbs_isHermitian X)
    (matrixRectAbs_isHermitian (X * U.val)) (fun t : ℝ => t⁻¹) U.val
    (matrixRectAbs_unitary_right_intertwine U X)
  change matrixRealInv (matrixRectAbs X) * U.val =
    U.val * matrixRealInv (matrixRectAbs (X * U.val)) at he
  rw [matrixRectPolar, Matrix.mul_assoc, ← he, ← Matrix.mul_assoc]
  rfl

theorem matrixRectPolar_two_unitaries (V : Matrix.unitaryGroup ι ℂ)
    (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    matrixRectPolar (V.val * X * U.val) = V.val * matrixRectPolar X * U.val := by
  rw [matrixRectPolar_unitary_right, matrixRectPolar_unitary_left]

omit [DecidableEq ι] in
theorem matrixRectAbs_spectrum_unitary_right (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    spectrum ℝ (matrixRectAbs (X * U.val)) = spectrum ℝ (matrixRectAbs X) := by
  rw [matrixRectAbs_unitary_right]
  exact Unitary.spectrum_star_left_conjugate

theorem rectHSNorm_polar_intertwiner_le (r : Nat) (V : Matrix.unitaryGroup ι ℂ)
    (U : Matrix.unitaryGroup κ ℂ) {X : Matrix ι κ ℂ} {b : ℝ} (hb : 0 < b)
    (hX : ∀ t ∈ spectrum ℝ (matrixRectAbs X), t = 0 ∨ b ≤ t) :
    rectHSNorm r (V.val * matrixRectPolar X - matrixRectPolar X * U.val) ≤
      b⁻¹ * rectHSNorm r (V.val * X - X * U.val) := by
  rw [← matrixRectPolar_unitary_left, ← matrixRectPolar_unitary_right]
  apply rectHSNorm_polar_sub_le_of_singularValues r hb
  · simpa only [matrixRectAbs_unitary_left] using hX
  · simpa only [matrixRectAbs_spectrum_unitary_right] using hX

end ThomGame.Analysis
