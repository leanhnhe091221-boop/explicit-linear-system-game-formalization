module

public import ThomGame.Analysis.MatrixIntertwiningEnergy

/-!
# Dimension-independent rectangular operator bounds

Columnwise Euclidean operator estimates keep the original HS
normalization when a matrix acts on a larger auxiliary space.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem rectangular_column_square_bound (A : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) (j : κ) :
    (∑ i, ‖(A * X) i j‖ ^ 2) ≤ ‖A‖ ^ 2 * ∑ i, ‖X i j‖ ^ 2 := by
  let x : EuclideanSpace ℂ ι := toLp 2 (fun i => X i j)
  have he := A.l2_opNorm_mulVec x
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr he
  have hv : (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ x.ofLp) =
      (toLp 2 (fun i => (A * X) i j) : EuclideanSpace ℂ ι) := by
    ext i
    rfl
  rw [hv] at hs
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, x] using hs

omit [DecidableEq κ] in
theorem rectHSNorm_mul_le_left (r : Nat) (A : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) :
    rectHSNorm r (A * X) ≤ ‖A‖ * rectHSNorm r X := by
  apply (sq_le_sq₀ (rectHSNorm_nonneg _ _)
    (mul_nonneg (norm_nonneg _) (rectHSNorm_nonneg _ _))).mp
  rw [mul_pow, rectHSNorm_sq, rectHSNorm_sq]
  calc
    _ = (∑ j, ∑ i, ‖(A * X) i j‖ ^ 2) / r := by rw [Finset.sum_comm]
    _ ≤ (∑ j, ‖A‖ ^ 2 * ∑ i, ‖X i j‖ ^ 2) / r :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => rectangular_column_square_bound A X j)
        (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm, mul_div_assoc]

omit [DecidableEq ι] in
theorem rectHSNorm_mul_le_right (r : Nat) (X : Matrix ι κ ℂ) (A : Matrix κ κ ℂ) :
    rectHSNorm r (X * A) ≤ rectHSNorm r X * ‖A‖ := by
  have he := rectHSNorm_mul_le_left r Aᴴ Xᴴ
  simpa only [← Matrix.conjTranspose_mul, rectHSNorm_conjTranspose,
    Matrix.l2_opNorm_conjTranspose, mul_comm] using he

variable {h : Nat}

theorem matrixIntertwiningEnergy_mul_le (r : Nat) (U : Fin h → Matrix.unitaryGroup κ ℂ)
    (V : Fin h → Matrix.unitaryGroup ι ℂ) (B : Matrix ι ι ℂ) (X : Matrix ι κ ℂ)
    (hB : ∀ j, (V j).val * B = B * (V j).val) :
    matrixIntertwiningEnergy r U V (B * X) ≤ ‖B‖ ^ 2 * matrixIntertwiningEnergy r U V X := by
  have hj (j : Fin h) :
      rectHSNorm r ((V j).val * (B * X) - (B * X) * (U j).val) ^ 2 ≤
      ‖B‖ ^ 2 * rectHSNorm r ((V j).val * X - X * (U j).val) ^ 2 := by
    have he : (V j).val * (B * X) - (B * X) * (U j).val =
        B * ((V j).val * X - X * (U j).val) := by
      rw [← Matrix.mul_assoc (V j).val B, hB j, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
    rw [he]
    have hs := mul_self_le_mul_self (rectHSNorm_nonneg r (B * ((V j).val * X - X * (U j).val)))
      (rectHSNorm_mul_le_left r B ((V j).val * X - X * (U j).val))
    simpa only [← pow_two, mul_pow] using hs
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j)
    (lazyMarkovWeight_nonneg h)
  simpa only [matrixIntertwiningEnergy, ← Finset.mul_sum, mul_left_comm (lazyMarkovWeight h)] using he

end ThomGame.Analysis
