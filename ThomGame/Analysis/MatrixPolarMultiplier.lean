module

public import ThomGame.Analysis.MatrixPolarInitial
public import ThomGame.Analysis.RectangularOperatorBounds
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Polar correction after a bounded injective multiplier

Coercivity gives the nonzero singular-value bound for the actual
product, using operator monotonicity of the square root. Together
with unitary covariance this controls the intertwining energy.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {h : Nat}

theorem matrixRectAbs_left_multiplier_lower (B : Matrix ι ι ℂ) {X : Matrix ι κ ℂ}
    (hX : IsStarProjection (Xᴴ * X)) {b : ℝ} (hb : 0 ≤ b)
    (hB : b ^ 2 • (1 : Matrix ι ι ℂ) ≤ Bᴴ * B) :
    b • (Xᴴ * X) ≤ matrixRectAbs (B * X) := by
  have hg : b ^ 2 • (Xᴴ * X) ≤ (B * X)ᴴ * (B * X) := by
    have he := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hB)).conjTranspose_mul_mul_same X
    apply sub_nonneg.mp
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc] using he.nonneg
  have hsqrt : CFC.sqrt (b ^ 2 • (Xᴴ * X)) = b • (Xᴴ * X) := by
    apply CFC.sqrt_unique
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX.isIdempotentElem.eq, pow_two]
    · exact smul_nonneg hb hX.nonneg
  rw [← hsqrt]
  exact CFC.sqrt_le_sqrt _ _ hg

theorem matrixRectAbs_left_multiplier_singularValues (B C : Matrix ι ι ℂ) {X : Matrix ι κ ℂ}
    (hX : IsStarProjection (Xᴴ * X)) (hCB : C * B = 1) {b : ℝ} (hb : 0 ≤ b)
    (hB : b ^ 2 • (1 : Matrix ι ι ℂ) ≤ Bᴴ * B) :
    ∀ s ∈ spectrum ℝ (matrixRectAbs (B * X)), s = 0 ∨ b ≤ s := by
  apply (matrixRealSupport_lower_iff (matrixRectAbs_nonneg (B * X)) b).mp
  rw [← matrixRectPolar_initial, matrixRectPolar_initial_partial_isometry_left_inverse B C hX hCB]
  exact matrixRectAbs_left_multiplier_lower B hX hb hB

theorem matrixIntertwiningEnergy_polar_mul_le (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (B C : Matrix ι ι ℂ) {X : Matrix ι κ ℂ} (hX : IsStarProjection (Xᴴ * X))
    (hCB : C * B = 1) {b : ℝ} (hb : 0 < b)
    (hB : b ^ 2 • (1 : Matrix ι ι ℂ) ≤ Bᴴ * B)
    (hcomm : ∀ j, (V j).val * B = B * (V j).val) :
    matrixIntertwiningEnergy r U V (matrixRectPolar (B * X)) ≤
      b⁻¹ ^ 2 * ‖B‖ ^ 2 * matrixIntertwiningEnergy r U V X := by
  calc
    _ ≤ b⁻¹ ^ 2 * matrixIntertwiningEnergy r U V (B * X) :=
      matrixIntertwiningEnergy_polar_le r U V hb
        (matrixRectAbs_left_multiplier_singularValues B C hX hCB hb.le hB)
    _ ≤ b⁻¹ ^ 2 * (‖B‖ ^ 2 * matrixIntertwiningEnergy r U V X) :=
      mul_le_mul_of_nonneg_left (matrixIntertwiningEnergy_mul_le r U V B X hcomm) (sq_nonneg _)
    _ = _ := by ring

end ThomGame.Analysis
