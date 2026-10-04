module

public import ThomGame.Analysis.MatrixProjectionDistance
public import ThomGame.Analysis.MatrixResolventEndpoint

/-!
# Ambient Hilbert error from discarding a corner of small trace
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat}

theorem hsNorm_add_sq_of_gram_zero (X Y : CMatrix d) (h : star X * Y = 0) :
    hsNorm (X + Y) ^ 2 = hsNorm X ^ 2 + hsNorm Y ^ 2 := by
  have hyx : star Y * X = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star h
  have ht := normalizedTrace_gram (X + Y)
  rw [star_add, add_mul, mul_add, mul_add, h, hyx, add_zero, zero_add,
    normalizedTrace_add, normalizedTrace_gram, normalizedTrace_gram] at ht
  simpa only [Complex.add_re, Complex.ofReal_re] using (congrArg Complex.re ht).symm

theorem matrixProjection_compression_hsNorm_le (P X : CMatrix d) (hP : IsStarProjection P) :
    hsNorm (P * X * P) ≤ hsNorm X :=
  (hsNorm_mul_projection_le _ hP).trans (hsNorm_projection_mul_le hP X)

theorem matrixProjection_compression_trace_bound (P X : CMatrix d) (hP : IsStarProjection P)
    (hX : matrixOpNorm X ≤ 1) : hsNorm (P * X * P) ≤ Real.sqrt (normalizedTrace P).re := by
  have hb : hsNorm (P * X * P) ≤ hsNorm P :=
    (hsNorm_mul_projection_le _ hP).trans ((hsNorm_mul_le_right P X).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hX (hsNorm_nonneg P)))
  rwa [← hsNorm_projection_sq hP, Real.sqrt_sq (hsNorm_nonneg P)]

theorem matrixProjection_compression_loss_sq (P X : CMatrix d) (hP : IsStarProjection P)
    (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - P * X * P) ^ 2 ≤ 2 * (normalizedTrace (1 - P)).re := by
  let R := 1 - P
  have hR : IsStarProjection R := hP.one_sub
  have hRP : R * P = 0 := by
    simp only [R, sub_mul, one_mul, hP.isIdempotentElem.eq, sub_self]
  have hcross : star (R * X) * (P * X * R) = 0 := by
    calc
      _ = star X * (R * P) * X * R := by
        simp only [star_mul, hR.isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [hRP, mul_zero, zero_mul, zero_mul]
  have ha : hsNorm (R * X) ≤ hsNorm R := (hsNorm_mul_le_right R X).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hX (hsNorm_nonneg R))
  have hb : hsNorm (P * X * R) ≤ hsNorm R := by
    rw [mul_assoc]
    exact (hsNorm_projection_mul_le hP _).trans ((hsNorm_mul_le_left X R).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hX (hsNorm_nonneg R)))
  have he : X - P * X * P = R * X + P * X * R := by
    dsimp [R]
    noncomm_ring
  rw [he, hsNorm_add_sq_of_gram_zero _ _ hcross]
  have ht : hsNorm R ^ 2 = (normalizedTrace (1 - P)).re := hsNorm_projection_sq hR
  nlinarith [pow_le_pow_left₀ (hsNorm_nonneg _) ha 2, pow_le_pow_left₀ (hsNorm_nonneg _) hb 2]

theorem matrixProjection_compression_loss (P X : CMatrix d) (hP : IsStarProjection P)
    (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - P * X * P) ≤ Real.sqrt (2 * (normalizedTrace (1 - P)).re) := by
  have h := Real.sqrt_le_sqrt (matrixProjection_compression_loss_sq P X hP hX)
  simpa only [Real.sqrt_sq (hsNorm_nonneg _)] using h

end ThomGame.Analysis
