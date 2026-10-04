module

public import ThomGame.Analysis.MatrixSelfAdjointDilation

/-!
# The Araki--Yamagami Hilbert--Schmidt inequality

The scalar absolute value is 1-Lipschitz on the real line. Applying
the self-adjoint functional-calculus estimate to the two dilations
controls the sum of the left and right absolute-value distances.
Discarding the first nonnegative summand gives ALT (2.6), including
rectangular matrices with the original normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem rectHSNorm_rectAbs (r : Nat) (X : Matrix ι κ ℂ) :
    rectHSNorm r (matrixRectAbs X) = rectHSNorm r X := by
  have hsa := IsSelfAdjoint.of_nonneg (matrixRectAbs_nonneg X)
  rw [rectHSNorm_eq_sqrt_gram r (matrixRectAbs X), ← Matrix.star_eq_conjTranspose,
    hsa.star_eq, matrixRectAbs_mul_self, ← rectHSNorm_eq_sqrt_gram r X]

theorem matrixSelfAdjointDilation_abs_sub (X Y : Matrix ι κ ℂ) :
    cfc (abs : ℝ → ℝ) (matrixSelfAdjointDilation X) -
      cfc (abs : ℝ → ℝ) (matrixSelfAdjointDilation Y) =
      Matrix.fromBlocks (matrixRectAbs Xᴴ - matrixRectAbs Yᴴ) 0 0
        (matrixRectAbs X - matrixRectAbs Y) := by
  simp [matrixSelfAdjointDilation_cfc_abs, sub_eq_add_neg,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_add]

theorem rectHSNorm_rectAbs_pair_sub_sq_le (r : Nat) (X Y : Matrix ι κ ℂ) :
    rectHSNorm r (matrixRectAbs Xᴴ - matrixRectAbs Yᴴ) ^ 2 +
      rectHSNorm r (matrixRectAbs X - matrixRectAbs Y) ^ 2 ≤
      2 * rectHSNorm r (X - Y) ^ 2 := by
  have hl := rectHSNorm_cfc_abs_sub_le r (matrixSelfAdjointDilation_isHermitian X)
    (matrixSelfAdjointDilation_isHermitian Y)
  have hs := mul_self_le_mul_self (rectHSNorm_nonneg r _) hl
  simp only [← pow_two] at hs
  rw [matrixSelfAdjointDilation_abs_sub, ← matrixSelfAdjointDilation_sub,
    rectHSNorm_selfAdjointDilation_sq, rectHSNorm_fromBlocks_sq] at hs
  simpa only [rectHSNorm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using hs

theorem rectHSNorm_rectAbs_sub_sq_le (r : Nat) (X Y : Matrix ι κ ℂ) :
    rectHSNorm r (matrixRectAbs X - matrixRectAbs Y) ^ 2 ≤
      2 * rectHSNorm r (X - Y) ^ 2 := by
  have hs := rectHSNorm_rectAbs_pair_sub_sq_le r X Y
  nlinarith [sq_nonneg (rectHSNorm r (matrixRectAbs Xᴴ - matrixRectAbs Yᴴ))]

theorem rectHSNorm_rectAbs_sub_le (r : Nat) (X Y : Matrix ι κ ℂ) :
    rectHSNorm r (matrixRectAbs X - matrixRectAbs Y) ≤
      Real.sqrt 2 * rectHSNorm r (X - Y) := by
  have hs := rectHSNorm_rectAbs_sub_sq_le r X Y
  have hn := rectHSNorm_nonneg r (matrixRectAbs X - matrixRectAbs Y)
  have hm := mul_nonneg (Real.sqrt_nonneg 2) (rectHSNorm_nonneg r (X - Y))
  have he : (Real.sqrt 2 * rectHSNorm r (X - Y)) ^ 2 = 2 * rectHSNorm r (X - Y) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

theorem hsNorm_cfcAbs_sub_sq_le {d : Nat} (X Y : CMatrix d) :
    hsNorm (CFC.abs X - CFC.abs Y) ^ 2 ≤ 2 * hsNorm (X - Y) ^ 2 :=
  rectHSNorm_rectAbs_sub_sq_le d X Y

theorem hsNorm_cfcAbs_sub_le {d : Nat} (X Y : CMatrix d) :
    hsNorm (CFC.abs X - CFC.abs Y) ≤ Real.sqrt 2 * hsNorm (X - Y) :=
  rectHSNorm_rectAbs_sub_le d X Y

end ThomGame.Analysis
