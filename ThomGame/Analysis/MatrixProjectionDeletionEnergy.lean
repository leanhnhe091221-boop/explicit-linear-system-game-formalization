module

public import ThomGame.Analysis.MatrixProjectionCutNorm

/-!
# Deleting a subprojection costs at most its compressed energy

The estimate has constant one. Orthogonal incoming and outgoing cuts
separate the old boundary from the newly deleted part. Every norm and
trace keeps the original ambient normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem rectHSNorm_add_orthogonal_right_sq (r : Nat) {X Y : Matrix ι ι ℂ}
    (hXY : X * Yᴴ = 0) :
    rectHSNorm r (X + Y) ^ 2 = rectHSNorm r X ^ 2 + rectHSNorm r Y ^ 2 := by
  have hh := rectHSNorm_add_orthogonal_sq r
    (show Xᴴᴴ * Yᴴ = 0 by simpa only [Matrix.conjTranspose_conjTranspose] using hXY)
  simpa only [← Matrix.conjTranspose_add, rectHSNorm_conjTranspose] using hh

theorem rectHSNorm_projection_deletion_commutator_le (r : Nat) (A : Matrix ι ι ℂ)
    {p q : Matrix ι ι ℂ} (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p ≤ q) :
    rectHSNorm r (A * (q - p) - (q - p) * A) ^ 2 ≤
      rectHSNorm r (A * q - q * A) ^ 2 +
        rectHSNorm r ((q * A * q) * p - p * (q * A * q)) ^ 2 := by
  let R := q - p
  have hR : IsStarProjection R := (hp.le_iff_sub hq).mp hpq
  have hqp := (hp.le_iff_mul_eq_right hq).mp hpq
  have hpq' := (hp.le_iff_mul_eq_left hq).mp hpq
  have hqR : q * R = R := by
    dsimp [R]
    rw [Matrix.mul_sub, hq.isIdempotentElem.eq, hqp]
  have hRq : R * q = R := by
    dsimp [R]
    rw [Matrix.sub_mul, hq.isIdempotentElem.eq, hpq']
  have hcut : (1 - q) * p = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hqp, sub_self]
  have hin : rectHSNorm r ((1 - R) * A * R) ^ 2 =
      rectHSNorm r ((1 - q) * A * R) ^ 2 + rectHSNorm r (p * A * R) ^ 2 := by
    have he : (1 - R) * A * R = (1 - q) * A * R + p * A * R := by dsimp [R]; noncomm_ring
    rw [he]
    apply rectHSNorm_add_orthogonal_sq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hq.one_sub.isSelfAdjoint.isHermitian.eq]
    calc
      _ = Rᴴ * Aᴴ * ((1 - q) * p) * A * R := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hcut, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hout : rectHSNorm r (R * A * (1 - R)) ^ 2 =
      rectHSNorm r (R * A * (1 - q)) ^ 2 + rectHSNorm r (R * A * p) ^ 2 := by
    have he : R * A * (1 - R) = R * A * (1 - q) + R * A * p := by dsimp [R]; noncomm_ring
    rw [he]
    apply rectHSNorm_add_orthogonal_right_sq
    rw [Matrix.conjTranspose_mul, hp.isSelfAdjoint.isHermitian.eq]
    calc
      _ = R * A * ((1 - q) * p) * (R * A)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hcut, Matrix.mul_zero, Matrix.zero_mul]
  have hleft : rectHSNorm r ((1 - q) * A * R) ^ 2 ≤ rectHSNorm r ((1 - q) * A * q) ^ 2 := by
    have hh := rectHSNorm_mul_projection_sq_le r hR ((1 - q) * A * q)
    simpa only [Matrix.mul_assoc, hqR] using hh
  have hright : rectHSNorm r (R * A * (1 - q)) ^ 2 ≤ rectHSNorm r (q * A * (1 - q)) ^ 2 := by
    have hh := rectHSNorm_projection_mul_sq_le r hR (q * A * (1 - q))
    simpa only [← Matrix.mul_assoc, hRq] using hh
  rw [rectHSNorm_projection_commutator_cut r A hR,
    rectHSNorm_projection_commutator_cut r A hq,
    rectHSNorm_compressed_commutator_cut r A hp hq hpq, hin, hout]
  dsimp [R] at hleft hright ⊢
  linarith only [hleft, hright]

variable {d h : Nat}

theorem matrixCoordinateEnergy_projection_deletion_le (U : Fin h → UnitaryMatrix d)
    {p q : CMatrix d} (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p ≤ q) :
    matrixCoordinateEnergy U (q - p) ≤
      matrixCoordinateEnergy U q + matrixCompressedCoordinateEnergy U q p := by
  have hh (j : Fin h) := rectHSNorm_projection_deletion_commutator_le d (U j).val hp hq hpq
  simp only [rectHSNorm_eq_hsNorm] at hh
  calc
    _ ≤ lazyMarkovWeight h * ∑ j,
        (hsNorm ((U j).val * q - q * (U j).val) ^ 2 +
          hsNorm ((q * (U j).val * q) * p - p * (q * (U j).val * q)) ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hh j) (lazyMarkovWeight_nonneg h)
    _ = _ := by simp only [matrixCoordinateEnergy, matrixCompressedCoordinateEnergy,
      Finset.sum_add_distrib, mul_add]

theorem matrixCoordinateEnergy_eq_zero_of_reducing (U : Fin h → UnitaryMatrix d)
    {P : CMatrix d} (hP : ∀ j, Commute P (U j).val) : matrixCoordinateEnergy U P = 0 := by
  simp only [matrixCoordinateEnergy, ← (hP _).eq, sub_self, hsNorm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, mul_zero]

theorem matrixCoordinateEnergy_reducing_sub (U : Fin h → UnitaryMatrix d)
    {P : CMatrix d} (hP : ∀ j, Commute P (U j).val) (Q : CMatrix d) :
    matrixCoordinateEnergy U (P - Q) = matrixCoordinateEnergy U Q := by
  unfold matrixCoordinateEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he : (U j).val * (P - Q) - (P - Q) * (U j).val = -((U j).val * Q - Q * (U j).val) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, (hP j).eq]
    abel
  rw [he, ← neg_one_smul ℂ ((U j).val * Q - Q * (U j).val), hsNorm_smul]
  norm_num

end ThomGame.Analysis
