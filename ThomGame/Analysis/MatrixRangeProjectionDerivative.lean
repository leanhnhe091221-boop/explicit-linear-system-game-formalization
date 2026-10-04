module

public import ThomGame.Analysis.MatrixFilledGram
public import ThomGame.Analysis.RectangularMatrixDerivative

/-!
# Differentiating the actual range projection

On a curve with fixed initial support, the range projection is
X (X*X + 1 - P) inverse X*. The ordinary inverse product rule gives
the tangent formula for a self-adjoint left action.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.Frobenius

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def matrixRangeProjection (X : Matrix ι κ ℂ) : Matrix ι ι ℂ :=
  matrixRectPolar X * (matrixRectPolar X)ᴴ

omit [DecidableEq ι] in
theorem matrixRangeProjection_isStarProjection (X : Matrix ι κ ℂ) :
    IsStarProjection (matrixRangeProjection X) := matrixRectPolar_final_projection X

omit [DecidableEq ι] in
theorem matrixRangeProjection_mul (X : Matrix ι κ ℂ) : matrixRangeProjection X * X = X :=
  matrixRectPolar_final_mul X

omit [DecidableEq ι] in
theorem matrixRangeProjection_fixed_formula {X : Matrix ι κ ℂ} {P : Matrix κ κ ℂ}
    (hP : matrixRealSupport (matrixRectAbs X) = P) :
    matrixRangeProjection X = X * (Xᴴ * X + (1 - P))⁻¹ * Xᴴ := by
  simpa only [matrixRangeProjection, matrixFilledGram, hP] using! (matrixFilledGram_range_formula X).symm

omit [DecidableEq ι] in
theorem matrixFixedGram_isUnit {X : Matrix ι κ ℂ} {P : Matrix κ κ ℂ}
    (hP : matrixRealSupport (matrixRectAbs X) = P) : IsUnit (Xᴴ * X + (1 - P)) := by
  simpa only [matrixFilledGram, hP] using matrixFilledGram_isUnit X

theorem matrixRangeProjection_hasDerivAt {X : ℝ → Matrix ι κ ℂ} {P : Matrix κ κ ℂ}
    {K : Matrix ι ι ℂ} (hK : Matrix.IsHermitian K)
    (hP : ∀ a, matrixRealSupport (matrixRectAbs (X a)) = P) {s : ℝ}
    (hX : HasDerivAt X (K * X s) s) :
    HasDerivAt (fun a => matrixRangeProjection (X a))
      ((1 - matrixRangeProjection (X s)) * K * matrixRangeProjection (X s) +
        matrixRangeProjection (X s) * K * (1 - matrixRangeProjection (X s))) s := by
  let R (a : ℝ) := ((X a)ᴴ * X a + (1 - P))⁻¹
  have hstar := rectangular_adjoint_hasDerivAt hX
  have hg := (rectangular_mul_hasDerivAt hstar hX).add_const (1 - P)
  have hR := squareMatrix_inverse_hasDerivAt hg (matrixFixedGram_isUnit (hP s))
  have he := rectangular_mul_hasDerivAt (rectangular_mul_hasDerivAt hX hR) hstar
  have hf (a : ℝ) : matrixRangeProjection (X a) = X a * R a * (X a)ᴴ :=
    matrixRangeProjection_fixed_formula (hP a)
  convert! he using 1
  · funext a
    exact hf a
  · rw [hf s]
    dsimp only [R]
    simp only [Matrix.conjTranspose_mul, hK.eq, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel

end ThomGame.Analysis
