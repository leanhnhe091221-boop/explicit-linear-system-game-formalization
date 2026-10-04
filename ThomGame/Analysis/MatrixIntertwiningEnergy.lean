module

public import ThomGame.Analysis.MatrixPolarUnitary

/-!
# Rectangular intertwining energy

This is the quantity I from ALT Section 3.2, with the original Hilbert
space dimension as explicit normalization. The actual polar map has
the inverse-square spectral-gap energy bound.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {h : Nat}

open scoped Matrix.Norms.Frobenius in
omit [DecidableEq ι] [DecidableEq κ] in
theorem rectHSNorm_sub_le (r : Nat) (X Y : Matrix ι κ ℂ) :
    rectHSNorm r (X - Y) ≤ rectHSNorm r X + rectHSNorm r Y := by
  unfold rectHSNorm
  rw [← add_div]
  exact div_le_div_of_nonneg_right (norm_sub_le _ _) (Real.sqrt_nonneg _)

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectHSNorm_add_sq_le (r : Nat) (X Y : Matrix ι κ ℂ) :
    rectHSNorm r (X + Y) ^ 2 ≤ 2 * rectHSNorm r X ^ 2 + 2 * rectHSNorm r Y ^ 2 := by
  have he := mul_self_le_mul_self (rectHSNorm_nonneg r (X + Y)) (rectHSNorm_add_le r X Y)
  nlinarith [sq_nonneg (rectHSNorm r X - rectHSNorm r Y)]

noncomputable def matrixIntertwiningEnergy (r : Nat) (U : Fin h → Matrix.unitaryGroup κ ℂ)
    (V : Fin h → Matrix.unitaryGroup ι ℂ) (X : Matrix ι κ ℂ) : ℝ :=
  lazyMarkovWeight h * ∑ j, rectHSNorm r ((V j).val * X - X * (U j).val) ^ 2

theorem matrixIntertwiningEnergy_nonneg (r : Nat) (U : Fin h → Matrix.unitaryGroup κ ℂ)
    (V : Fin h → Matrix.unitaryGroup ι ℂ) (X : Matrix ι κ ℂ) :
    0 ≤ matrixIntertwiningEnergy r U V X :=
  mul_nonneg (lazyMarkovWeight_nonneg h) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem matrixIntertwiningEnergy_eq_coordinate {d : Nat} (U : Fin h → UnitaryMatrix d)
    (X : CMatrix d) : matrixIntertwiningEnergy d U U X = matrixCoordinateEnergy U X := rfl

theorem matrixIntertwiningEnergy_le_hsNorm_sq [NeZero h] (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X : Matrix ι κ ℂ) : matrixIntertwiningEnergy r U V X ≤ rectHSNorm r X ^ 2 := by
  have hj (j : Fin h) : rectHSNorm r ((V j).val * X - X * (U j).val) ^ 2 ≤
      4 * rectHSNorm r X ^ 2 := by
    have he := rectHSNorm_sub_le r ((V j).val * X) (X * (U j).val)
    rw [rectHSNorm_unitary_mul, rectHSNorm_mul_unitary] at he
    have hs := mul_self_le_mul_self (rectHSNorm_nonneg r _) he
    nlinarith
  calc
    _ ≤ lazyMarkovWeight h * ∑ _j : Fin h, 4 * rectHSNorm r X ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hj j) (lazyMarkovWeight_nonneg h)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, lazyMarkovWeight_mul_card]
      ring

theorem matrixIntertwiningEnergy_add_le (r : Nat) (U : Fin h → Matrix.unitaryGroup κ ℂ)
    (V : Fin h → Matrix.unitaryGroup ι ℂ) (X Y : Matrix ι κ ℂ) :
    matrixIntertwiningEnergy r U V (X + Y) ≤
      2 * matrixIntertwiningEnergy r U V X + 2 * matrixIntertwiningEnergy r U V Y := by
  have hj (j : Fin h) :
      rectHSNorm r ((V j).val * (X + Y) - (X + Y) * (U j).val) ^ 2 ≤
      2 * rectHSNorm r ((V j).val * X - X * (U j).val) ^ 2 +
      2 * rectHSNorm r ((V j).val * Y - Y * (U j).val) ^ 2 := by
    have he : (V j).val * (X + Y) - (X + Y) * (U j).val =
        ((V j).val * X - X * (U j).val) + ((V j).val * Y - Y * (U j).val) := by
      rw [Matrix.mul_add, Matrix.add_mul]
      abel
    rw [he]
    exact rectHSNorm_add_sq_le r _ _
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j) (lazyMarkovWeight_nonneg h)
  simpa only [matrixIntertwiningEnergy, Finset.sum_add_distrib, ← Finset.mul_sum,
    mul_add, mul_left_comm (lazyMarkovWeight h) 2] using he

theorem matrixIntertwiningEnergy_perturb_le [NeZero h] (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X Y : Matrix ι κ ℂ) : matrixIntertwiningEnergy r U V X ≤
      2 * matrixIntertwiningEnergy r U V Y + 2 * rectHSNorm r (X - Y) ^ 2 := by
  have he := matrixIntertwiningEnergy_add_le r U V Y (X - Y)
  have hXY : Y + (X - Y) = X := by abel
  rw [hXY] at he
  exact he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (matrixIntertwiningEnergy_le_hsNorm_sq r U V (X - Y)) (by norm_num)))

theorem matrixIntertwiningEnergy_polar_le (r : Nat) (U : Fin h → Matrix.unitaryGroup κ ℂ)
    (V : Fin h → Matrix.unitaryGroup ι ℂ) {X : Matrix ι κ ℂ} {b : ℝ} (hb : 0 < b)
    (hX : ∀ t ∈ spectrum ℝ (matrixRectAbs X), t = 0 ∨ b ≤ t) :
    matrixIntertwiningEnergy r U V (matrixRectPolar X) ≤ b⁻¹ ^ 2 * matrixIntertwiningEnergy r U V X := by
  have hj (j : Fin h) := mul_self_le_mul_self (rectHSNorm_nonneg r _)
    (rectHSNorm_polar_intertwiner_le r (V j) (U j) hb hX)
  simp only [← pow_two, mul_pow] at hj
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j) (lazyMarkovWeight_nonneg h)
  simpa only [matrixIntertwiningEnergy, ← Finset.mul_sum, mul_left_comm (lazyMarkovWeight h)] using he

end ThomGame.Analysis
