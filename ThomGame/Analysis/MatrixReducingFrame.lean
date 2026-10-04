module

public import ThomGame.Analysis.MatrixFrameCompression
public import ThomGame.Analysis.MatrixProjectionRankBounds
public import ThomGame.Analysis.MatrixMarkovPoincare

/-!
# Exact transport through a frame of a reducing corner

The smaller-space unitary is actually constructed. Trace, squared
HS norm and energy all acquire the same dimension ratio n/d.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d n h : Nat}

theorem matrixFrameLift_support {P : CMatrix d} {F : Matrix (Fin d) (Fin n) ℂ}
    (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P) (Y : CMatrix n) :
    P * matrixFrameLift F Y = matrixFrameLift F Y ∧ matrixFrameLift F Y * P = matrixFrameLift F Y := by
  have he : matrixFrameLift F 1 = P := (matrixFrameLift_one F).trans hFf
  constructor
  · rw [← he, matrixFrameLift_mul hFi, Matrix.one_mul]
  · rw [← he, matrixFrameLift_mul hFi, Matrix.mul_one]

theorem matrixFrameLift_isStarProjection {F : Matrix (Fin d) (Fin n) ℂ} (hFi : Fᴴ * F = 1)
    {p : CMatrix n} (hp : IsStarProjection p) : IsStarProjection (matrixFrameLift F p) := by
  constructor
  · change matrixFrameLift F p * matrixFrameLift F p = matrixFrameLift F p
    rw [matrixFrameLift_mul hFi, hp.isIdempotentElem.eq]
  · change (matrixFrameLift F p)ᴴ = matrixFrameLift F p
    rw [matrixFrameLift_star, hp.isSelfAdjoint.isHermitian.eq]

theorem matrixFrameLift_projection_le {P : CMatrix d} (hP : IsStarProjection P)
    {F : Matrix (Fin d) (Fin n) ℂ} (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P)
    {p : CMatrix n} (hp : IsStarProjection p) : matrixFrameLift F p ≤ P := by
  exact ((matrixFrameLift_isStarProjection hFi hp).le_iff_mul_eq_right hP).mpr
    (matrixFrameLift_support hFi hFf p).1

theorem matrixFrameLift_projection_rank {F : Matrix (Fin d) (Fin n) ℂ} (hFi : Fᴴ * F = 1)
    {p : CMatrix n} (hp : IsStarProjection p) : (matrixFrameLift F p).rank = p.rank := by
  have he := matrixFrameLift_trace 1 hFi p
  rw [matrixTraceReal_projection_rank 1 (matrixFrameLift_isStarProjection hFi hp),
    matrixTraceReal_projection_rank 1 hp] at he
  simpa only [Nat.cast_one, div_one, Nat.cast_inj] using he

theorem exists_matrixFrameReducingUnitary {P : CMatrix d} (hP : IsStarProjection P)
    {F : Matrix (Fin d) (Fin n) ℂ} (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P)
    (U : UnitaryMatrix d) (hred : Commute P U.val) :
    ∃ V : UnitaryMatrix n, matrixFrameLift F V.val = P * U.val := by
  have hUi : U.valᴴ * U.val = 1 := U.prop.1
  have hUf : U.val * U.valᴴ = 1 := U.prop.2
  have hi : (P * U.val)ᴴ * (P * U.val) = P := by
    rw [Matrix.conjTranspose_mul, hP.isSelfAdjoint.isHermitian.eq]
    calc
      _ = U.valᴴ * (P * P) * U.val := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hP.isIdempotentElem.eq, Matrix.mul_assoc, hred.eq, ← Matrix.mul_assoc, hUi, Matrix.one_mul]
  have hf : (P * U.val) * (P * U.val)ᴴ = P := by
    rw [Matrix.conjTranspose_mul, hP.isSelfAdjoint.isHermitian.eq]
    calc
      _ = P * (U.val * U.valᴴ) * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hUf, Matrix.mul_one, hP.isIdempotentElem.eq]
  exact exists_matrixCornerUnitary hP hFi hFf hi hf

theorem matrixFrameLift_reducing_commutator {P : CMatrix d}
    {F : Matrix (Fin d) (Fin n) ℂ} (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P)
    {U : CMatrix d} {V : CMatrix n} (hred : Commute P U) (hV : matrixFrameLift F V = P * U)
    (Y : CMatrix n) :
    matrixFrameLift F (V * Y - Y * V) = U * matrixFrameLift F Y - matrixFrameLift F Y * U := by
  rw [matrixFrameLift_sub, ← matrixFrameLift_mul hFi, ← matrixFrameLift_mul hFi, hV]
  have hs := matrixFrameLift_support hFi hFf Y
  rw [hred.eq, Matrix.mul_assoc, hs.1]
  rw [← hred.eq, ← Matrix.mul_assoc, hs.2]

variable [NeZero d] [NeZero n]

theorem hsNorm_frameLift_sq {F : Matrix (Fin d) (Fin n) ℂ} (hFi : Fᴴ * F = 1) (Y : CMatrix n) :
    hsNorm (matrixFrameLift F Y) ^ 2 = (n : ℝ) / d * hsNorm Y ^ 2 := by
  rw [← rectHSNorm_eq_hsNorm, matrixFrameLift_hsNorm d hFi, rectHSNorm_sq, hsNorm_sq]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

theorem matrixTraceReal_frameLift_scale {F : Matrix (Fin d) (Fin n) ℂ}
    (hFi : Fᴴ * F = 1) (Y : CMatrix n) :
    matrixTraceReal d (matrixFrameLift F Y) = (n : ℝ) / d * matrixTraceReal n Y := by
  rw [matrixFrameLift_trace d hFi]
  unfold matrixTraceReal
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

theorem normalizedTrace_frameLift_scale {F : Matrix (Fin d) (Fin n) ℂ}
    (hFi : Fᴴ * F = 1) (Y : CMatrix n) :
    normalizedTrace (matrixFrameLift F Y) = (n : ℂ) / d * normalizedTrace Y := by
  have ht : (matrixFrameLift F Y).trace = Y.trace := by
    rw [matrixFrameLift, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hFi, Matrix.one_mul]
  unfold normalizedTrace
  rw [ht]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

theorem matrixCoordinateEnergy_frameLift {P : CMatrix d}
    {F : Matrix (Fin d) (Fin n) ℂ} (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P)
    (U : Fin h → UnitaryMatrix d) (V : Fin h → UnitaryMatrix n)
    (hred : ∀ j, Commute P (U j).val) (hV : ∀ j, matrixFrameLift F (V j).val = P * (U j).val)
    (Y : CMatrix n) : matrixCoordinateEnergy U (matrixFrameLift F Y) =
      (n : ℝ) / d * matrixCoordinateEnergy V Y := by
  have hj (j : Fin h) : hsNorm ((U j).val * matrixFrameLift F Y - matrixFrameLift F Y * (U j).val) ^ 2 =
      (n : ℝ) / d * hsNorm ((V j).val * Y - Y * (V j).val) ^ 2 := by
    rw [← matrixFrameLift_reducing_commutator hFi hFf (hred j) (hV j), hsNorm_frameLift_sq hFi]
  simp only [matrixCoordinateEnergy, hj, ← Finset.mul_sum]
  ring

end ThomGame.Analysis
