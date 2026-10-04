module

public import ThomGame.Analysis.MatrixDoubledCompressionEnergy

/-!
# Orthogonal cut formulas for matrix commutators

All identities hold for arbitrary matrices and retain the given
ambient HS normalization. A compressed commutator is the sum of the
two off-diagonal blocks inside the containing projection.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem rectHSNorm_sub_orthogonal_sq (r : Nat) {X Y : Matrix ι ι ℂ} (hXY : Xᴴ * Y = 0) :
    rectHSNorm r (X - Y) ^ 2 = rectHSNorm r X ^ 2 + rectHSNorm r Y ^ 2 := by
  rw [rectHSNorm_sub_sq, hXY, matrixTraceReal_zero, mul_zero, sub_zero,
    matrixTraceReal_gram, matrixTraceReal_gram]

omit [DecidableEq ι] in
theorem rectHSNorm_add_orthogonal_sq (r : Nat) {X Y : Matrix ι ι ℂ} (hXY : Xᴴ * Y = 0) :
    rectHSNorm r (X + Y) ^ 2 = rectHSNorm r X ^ 2 + rectHSNorm r Y ^ 2 := by
  have hy : Xᴴ * (-Y) = 0 := by rw [Matrix.mul_neg, hXY, neg_zero]
  have hn : rectHSNorm r (-Y) = rectHSNorm r Y := by
    rw [← neg_one_smul ℂ Y, rectHSNorm_smul]
    norm_num
  simpa only [sub_neg_eq_add, hn] using rectHSNorm_sub_orthogonal_sq r hy

theorem rectHSNorm_projection_mul_sq_le (r : Nat) {p : Matrix ι ι ℂ}
    (hp : IsStarProjection p) (X : Matrix ι ι ℂ) : rectHSNorm r (p * X) ^ 2 ≤ rectHSNorm r X ^ 2 := by
  simpa only [matrixTraceReal_gram] using matrixTraceReal_mono r (matrixProjection_compression_gram_le hp X)

theorem rectHSNorm_mul_projection_sq_le (r : Nat) {p : Matrix ι ι ℂ}
    (hp : IsStarProjection p) (X : Matrix ι ι ℂ) : rectHSNorm r (X * p) ^ 2 ≤ rectHSNorm r X ^ 2 := by
  have he := rectHSNorm_projection_mul_sq_le r hp Xᴴ
  rw [← rectHSNorm_conjTranspose r (X * p), Matrix.conjTranspose_mul, hp.isSelfAdjoint.isHermitian.eq]
  simpa only [rectHSNorm_conjTranspose] using he

omit [DecidableEq ι] in
theorem matrixProjection_opposite_cut_orthogonal {p q A : Matrix ι ι ℂ}
    (hq : IsStarProjection q) (hqp : q * p = 0) : (q * A * p)ᴴ * (p * A * q) = 0 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hq.isSelfAdjoint.isHermitian.eq]
  calc
    _ = pᴴ * Aᴴ * (q * p) * A * q := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hqp, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

theorem rectHSNorm_projection_commutator_cut (r : Nat) (A : Matrix ι ι ℂ)
    {p : Matrix ι ι ℂ} (hp : IsStarProjection p) :
    rectHSNorm r (A * p - p * A) ^ 2 =
      rectHSNorm r ((1 - p) * A * p) ^ 2 + rectHSNorm r (p * A * (1 - p)) ^ 2 := by
  have he : A * p - p * A = (1 - p) * A * p - p * A * (1 - p) := by noncomm_ring
  rw [he]
  apply rectHSNorm_sub_orthogonal_sq
  apply matrixProjection_opposite_cut_orthogonal hp.one_sub
  rw [Matrix.sub_mul, Matrix.one_mul, hp.isIdempotentElem.eq, sub_self]

theorem rectHSNorm_compressed_commutator_cut (r : Nat) (A : Matrix ι ι ℂ)
    {p q : Matrix ι ι ℂ} (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p ≤ q) :
    rectHSNorm r ((q * A * q) * p - p * (q * A * q)) ^ 2 =
      rectHSNorm r ((q - p) * A * p) ^ 2 + rectHSNorm r (p * A * (q - p)) ^ 2 := by
  have hqp := (hp.le_iff_mul_eq_right hq).mp hpq
  have hpq' := (hp.le_iff_mul_eq_left hq).mp hpq
  have he : (q * A * q) * p - p * (q * A * q) = (q - p) * A * p - p * A * (q - p) := by
    rw [Matrix.mul_assoc (q * A), hqp, ← Matrix.mul_assoc p, ← Matrix.mul_assoc p, hpq']
    noncomm_ring
  rw [he]
  apply rectHSNorm_sub_orthogonal_sq
  apply matrixProjection_opposite_cut_orthogonal ((hp.le_iff_sub hq).mp hpq)
  rw [Matrix.sub_mul, hqp, hp.isIdempotentElem.eq, sub_self]

end ThomGame.Analysis
