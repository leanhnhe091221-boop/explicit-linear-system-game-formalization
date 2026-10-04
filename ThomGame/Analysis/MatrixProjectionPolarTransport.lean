module

public import ThomGame.Analysis.MatrixPolarCompletionDistance
public import ThomGame.Analysis.MatrixPolarMultiplier

/-!
# Polar transport between nearly nested projections

A strict lower Gram bound forces the actual polar factor to have the
prescribed initial projection. For two nearly nested projections, its
compression is the positive square root, with the sharp lower bound
needed in ALT (4.6).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem matrixRectPolar_initial_of_gram_lower {X : Matrix ι κ ℂ} {P : Matrix κ κ ℂ}
    (hP : IsStarProjection P) (hXP : X * P = X) {c : ℝ} (hc : 0 < c)
    (hgap : c • P ≤ Xᴴ * X) : (matrixRectPolar X)ᴴ * matrixRectPolar X = P := by
  let q := matrixRealSupport (matrixRectAbs X)
  have hq : IsStarProjection q := matrixRealSupport_isStarProjection _
  have hqP : q ≤ P := by
    simpa only [matrixRectPolar_initial] using matrixRectPolar_initial_le hP hXP
  have hQ : IsStarProjection (P - q) := (hq.le_iff_sub hP).mp hqP
  have hQP : (P - q) * P = P - q :=
    (hQ.le_iff_mul_eq_left hP).mp (sub_le_self P hq.nonneg)
  have hXQ : X * (P - q) = 0 := by
    rw [Matrix.mul_sub, hXP, matrix_mul_absSupport, sub_self]
  have hGQ : (Xᴴ * X) * (P - q) = 0 := by
    rw [Matrix.mul_assoc, hXQ, Matrix.mul_zero]
  have he := star_right_conjugate_le_conjugate hgap (P - q)
  have hz : c • (P - q) ≤ 0 := by
    simpa only [hQ.isSelfAdjoint.star_eq, Matrix.mul_smul, Matrix.smul_mul, hQP,
      hQ.isIdempotentElem.eq, Matrix.mul_assoc, hGQ, Matrix.mul_zero] using he
  have hzero : P - q = 0 := le_antisymm
    ((smul_le_smul_iff_of_pos_left hc).mp (by simpa only [smul_zero] using hz)) hQ.nonneg
  rw [matrixRectPolar_initial]
  exact (sub_eq_zero.mp hzero).symm

omit [Fintype ι] [DecidableEq ι] in
theorem matrixProjection_gram_lower_of_leakage {P R : Matrix κ κ ℂ}
    (hP : IsStarProjection P) {ε : ℝ} (hleak : P * (1 - R) * P ≤ ε • P) :
    (1 - ε) • P ≤ P * R * P := by
  have he : P - P * R * P ≤ ε • P := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      hP.isIdempotentElem.eq] using hleak
  calc
    _ = P - ε • P := by rw [sub_smul, one_smul]
    _ ≤ P - (P - P * R * P) := sub_le_sub_left he P
    _ = _ := sub_sub_cancel _ _

omit [Fintype ι] [DecidableEq ι] in
theorem matrixProjectionPolar_initial {P R : Matrix κ κ ℂ}
    (hP : IsStarProjection P) (hR : IsStarProjection R) {ε : ℝ} (hε : ε < 1)
    (hleak : P * (1 - R) * P ≤ ε • P) :
    (matrixRectPolar (R * P))ᴴ * matrixRectPolar (R * P) = P := by
  apply matrixRectPolar_initial_of_gram_lower hP
    (by rw [Matrix.mul_assoc, hP.isIdempotentElem.eq]) (sub_pos.mpr hε)
  rw [matrixProjection_compression_gram hR, hP.isSelfAdjoint.isHermitian.eq]
  exact matrixProjection_gram_lower_of_leakage hP hleak

omit [Fintype ι] [DecidableEq ι] in
theorem matrixProjectionPolar_final_le {P R : Matrix κ κ ℂ}
    (hR : IsStarProjection R) :
    matrixRectPolar (R * P) * (matrixRectPolar (R * P))ᴴ ≤ R :=
  matrixRectPolar_final_le hR (by rw [← Matrix.mul_assoc, hR.isIdempotentElem.eq])

omit [DecidableEq ι] in
theorem matrixRectAbs_lower_of_gram_lower {X : Matrix ι κ ℂ} {P : Matrix κ κ ℂ}
    (hP : IsStarProjection P) {c : ℝ} (hc : 0 ≤ c) (hgap : c • P ≤ Xᴴ * X) :
    Real.sqrt c • P ≤ matrixRectAbs X := by
  have he : CFC.sqrt (c • P) = Real.sqrt c • P := by
    apply CFC.sqrt_unique
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP.isIdempotentElem.eq,
        Real.mul_self_sqrt hc]
    · exact smul_nonneg (Real.sqrt_nonneg c) hP.nonneg
  rw [← he]
  exact CFC.sqrt_le_sqrt _ _ hgap

omit [Fintype ι] [DecidableEq ι] in
theorem matrixProjectionPolar_abs_lower {P R : Matrix κ κ ℂ}
    (hP : IsStarProjection P) (hR : IsStarProjection R) {ε : ℝ} (hε : ε ≤ 1)
    (hleak : P * (1 - R) * P ≤ ε • P) :
    Real.sqrt (1 - ε) • P ≤ matrixRectAbs (R * P) := by
  apply matrixRectAbs_lower_of_gram_lower hP (sub_nonneg.mpr hε)
  rw [matrixProjection_compression_gram hR, hP.isSelfAdjoint.isHermitian.eq]
  exact matrixProjection_gram_lower_of_leakage hP hleak

omit [Fintype ι] [DecidableEq ι] in
theorem matrixProjectionPolar_compression {P R : Matrix κ κ ℂ}
    (hP : IsStarProjection P) (hR : IsStarProjection R) :
    P * matrixRectPolar (R * P) * P = matrixRectAbs (R * P) := by
  have hgram : (R * P)ᴴ * (R * P) = P * R * P := by
    rw [matrixProjection_compression_gram hR, hP.isSelfAdjoint.isHermitian.eq]
  have hXP : (R * P) * P = R * P := by rw [Matrix.mul_assoc, hP.isIdempotentElem.eq]
  have hqP := (matrixRectPolar_initial_projection (R * P)).le_iff_mul_eq_left hP
  have hsupport : matrixRealSupport (matrixRectAbs (R * P)) * P =
      matrixRealSupport (matrixRectAbs (R * P)) := by
    simpa only [matrixRectPolar_initial] using hqP.mp (matrixRectPolar_initial_le hP hXP)
  have hAP : matrixRectAbs (R * P) * P = matrixRectAbs (R * P) := by
    calc
      _ = (matrixRectAbs (R * P) * matrixRealSupport (matrixRectAbs (R * P))) * P := by
        rw [mul_matrixRealSupport (matrixRectAbs_isHermitian _)]
      _ = _ := by rw [Matrix.mul_assoc, hsupport, mul_matrixRealSupport (matrixRectAbs_isHermitian _)]
  rw [matrixRectPolar, ← Matrix.mul_assoc P (R * P), ← Matrix.mul_assoc P R P,
    ← hgram, ← matrixRectAbs_mul_self,
    Matrix.mul_assoc (matrixRectAbs (R * P)) (matrixRectAbs (R * P)) (matrixRealInv _),
    mul_matrixRealInv (matrixRectAbs_isHermitian _),
    mul_matrixRealSupport (matrixRectAbs_isHermitian _), hAP]

end ThomGame.Analysis
