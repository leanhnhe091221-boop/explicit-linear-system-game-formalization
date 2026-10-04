module

public import ThomGame.Analysis.MatrixProjectionCutNorm
public import ThomGame.Analysis.RectangularOperatorBounds

/-!+# Support-compression errors with a fixed original normalization

The matrix size and the HS denominator are independent. In particular,
the estimates also apply to corrected spaces of a different dimension,
including zero-dimensional spaces.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem rectHSNorm_projection_sq (r : Nat) {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    rectHSNorm r P ^ 2 = matrixTraceReal r P := by
  rw [← matrixTraceReal_gram, hP.isSelfAdjoint.isHermitian.eq, hP.isIdempotentElem.eq]

theorem rectHSNorm_projection_compression_le (r : Nat) (P X : Matrix ι ι ℂ)
    (hP : IsStarProjection P) : rectHSNorm r (P * X * P) ≤ rectHSNorm r X := by
  have ha := rectHSNorm_mul_projection_sq_le r hP (P * X)
  have hb := rectHSNorm_projection_mul_sq_le r hP X
  nlinarith [rectHSNorm_nonneg r X, rectHSNorm_nonneg r (P * X * P)]

theorem rectHSNorm_projection_compression_loss_sq (r : Nat) (P X : Matrix ι ι ℂ)
    (hP : IsStarProjection P) (hX : ‖X‖ ≤ 1) :
    rectHSNorm r (X - P * X * P) ^ 2 ≤ 2 * matrixTraceReal r (1 - P) := by
  let R := 1 - P
  have hR : IsStarProjection R := hP.one_sub
  have hRP : R * P = 0 := by
    simp only [R, Matrix.sub_mul, Matrix.one_mul, hP.isIdempotentElem.eq, sub_self]
  have hcross : (R * X)ᴴ * (P * X * R) = 0 := by
    calc
      _ = Xᴴ * (R * P) * X * R := by
        simp only [Matrix.conjTranspose_mul, hR.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]
      _ = 0 := by rw [hRP, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have ha : rectHSNorm r (R * X) ≤ rectHSNorm r R :=
    (rectHSNorm_mul_le_right r R X).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hX (rectHSNorm_nonneg r R))
  have hb : rectHSNorm r (X * R) ≤ rectHSNorm r R :=
    (rectHSNorm_mul_le_left r X R).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hX (rectHSNorm_nonneg r R))
  have hc : rectHSNorm r (P * X * R) ^ 2 ≤ rectHSNorm r (X * R) ^ 2 := by
    rw [Matrix.mul_assoc]
    exact rectHSNorm_projection_mul_sq_le r hP (X * R)
  have he : X - P * X * P = R * X + P * X * R := by
    dsimp only [R]
    noncomm_ring
  rw [he, rectHSNorm_add_orthogonal_sq r hcross]
  have ht : rectHSNorm r R ^ 2 = matrixTraceReal r (1 - P) := rectHSNorm_projection_sq r hR
  nlinarith [pow_le_pow_left₀ (rectHSNorm_nonneg r _) ha 2,
    pow_le_pow_left₀ (rectHSNorm_nonneg r _) hb 2]

theorem rectHSNorm_projection_compression_loss (r : Nat) (P X : Matrix ι ι ℂ)
    (hP : IsStarProjection P) (hX : ‖X‖ ≤ 1) :
    rectHSNorm r (X - P * X * P) ≤ Real.sqrt (2 * matrixTraceReal r (1 - P)) := by
  have h := Real.sqrt_le_sqrt (rectHSNorm_projection_compression_loss_sq r P X hP hX)
  simpa only [Real.sqrt_sq (rectHSNorm_nonneg r _)] using h

end ThomGame.Analysis
