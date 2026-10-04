module

public import ThomGame.Analysis.MatrixCornerUnitary

/-!
# Rectangular contractions and projection pullbacks

Multiplication by an actual rectangular contraction decreases the
normalized HS norm. Pulling back projections commuting with a
partial isometry's range preserves products and orthogonality.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] in
theorem matrixTraceReal_finalGram (r : Nat) (X : Matrix ι κ ℂ) :
    matrixTraceReal r (X * Xᴴ) = rectHSNorm r X ^ 2 := by
  rw [matrixTraceReal_mul_comm]
  exact matrixTraceReal_gram r X

omit [DecidableEq ι] in
theorem rectHSNorm_mul_sq_le_of_final_le_one (r : Nat) (A : Matrix ν κ ℂ)
    {B : Matrix κ ι ℂ} (hB : B * Bᴴ ≤ 1) :
    rectHSNorm r (A * B) ^ 2 ≤ rectHSNorm r A ^ 2 := by
  have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hB)).mul_mul_conjTranspose_same A
  have he : (A * B) * (A * B)ᴴ ≤ A * Aᴴ := by
    apply sub_nonneg.mp
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.mul_assoc] using hp.nonneg
  simpa only [matrixTraceReal_finalGram] using matrixTraceReal_mono r he

theorem rectHSNorm_mul_sq_le_of_partialIsometry (r : Nat) (A : Matrix ν κ ℂ)
    {B : Matrix κ ι ℂ} (hB : IsStarProjection (Bᴴ * B)) :
    rectHSNorm r (A * B) ^ 2 ≤ rectHSNorm r A ^ 2 :=
  rectHSNorm_mul_sq_le_of_final_le_one r A (matrixPartialIsometry_final_projection hB).le_one

omit [Fintype ν] [DecidableEq ι] [DecidableEq ν] in
theorem matrixPartialIsometry_pullback_mul {Z : Matrix ι κ ℂ}
    (hZ : IsStarProjection (Zᴴ * Z)) (E F : Matrix ι ι ℂ)
    (hF : Commute (Z * Zᴴ) F) :
    (Zᴴ * E * Z) * (Zᴴ * F * Z) = Zᴴ * (E * F) * Z := by
  have hRZ : (Z * Zᴴ) * Z = Z := by
    rw [Matrix.mul_assoc]
    exact matrixPartialIsometry_mul_initial hZ
  calc
    _ = Zᴴ * E * ((Z * Zᴴ) * F) * Z := by simp only [Matrix.mul_assoc]
    _ = Zᴴ * E * (F * (Z * Zᴴ)) * Z := by rw [hF.eq]
    _ = Zᴴ * (E * F) * ((Z * Zᴴ) * Z) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hRZ]

omit [Fintype ν] [DecidableEq ι] [DecidableEq ν] in
theorem matrixPartialIsometry_pullback_projection {Z : Matrix ι κ ℂ}
    (hZ : IsStarProjection (Zᴴ * Z)) {E : Matrix ι ι ℂ}
    (hE : IsStarProjection E) (hcomm : Commute (Z * Zᴴ) E) :
    IsStarProjection (Zᴴ * E * Z) := by
  constructor
  · show (Zᴴ * E * Z) * (Zᴴ * E * Z) = Zᴴ * E * Z
    rw [matrixPartialIsometry_pullback_mul hZ E E hcomm, hE.isIdempotentElem.eq]
  · show (Zᴴ * E * Z)ᴴ = Zᴴ * E * Z
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hE.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]

omit [Fintype ν] [DecidableEq ι] [DecidableEq ν] in
theorem matrixPartialIsometry_pullback_orthogonal {Z : Matrix ι κ ℂ}
    (hZ : IsStarProjection (Zᴴ * Z)) {E F : Matrix ι ι ℂ}
    (hF : Commute (Z * Zᴴ) F) (hEF : E * F = 0) :
    (Zᴴ * E * Z) * (Zᴴ * F * Z) = 0 := by
  rw [matrixPartialIsometry_pullback_mul hZ E F hF, hEF, Matrix.mul_zero, Matrix.zero_mul]

end ThomGame.Analysis
