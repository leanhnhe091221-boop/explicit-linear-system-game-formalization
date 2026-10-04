module

public import ThomGame.Analysis.MatrixConditionalExpectation
public import ThomGame.Analysis.MatrixHalfSpectralCut
public import ThomGame.Analysis.MatrixProjectionSubrank

/-!
# Trace expectation and projection rounding at the original normalization

The normalizing dimension r need not equal the matrix size. Positivity,
trace pairing and exact variance identities are preserved with that
denominator, including when the projection and its expectation do not commute.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem matrixTraceReal_eq_of_normalizedTrace_eq (r : Nat) {X Y : CMatrix d}
    (h : normalizedTrace X = normalizedTrace Y) : matrixTraceReal r X = matrixTraceReal r Y := by
  have he : Matrix.trace X = Matrix.trace Y :=
    (div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne d) : (d : ℂ) ≠ 0)).mp h
  exact congrArg (fun z : ℂ => z.re / r) he

theorem matrixTraceProjection_traceReal (r : Nat) (A : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d) :
    matrixTraceReal r (matrixTraceProjection A X) = matrixTraceReal r X :=
  matrixTraceReal_eq_of_normalizedTrace_eq r (matrixTraceProjection_trace A X)

theorem matrixTraceProjection_traceReal_pairing (r : Nat) (A : StarSubalgebra ℂ (CMatrix d))
    (X Y : CMatrix d) (hY : Y ∈ A) :
    matrixTraceReal r (star Y * matrixTraceProjection A X) = matrixTraceReal r (star Y * X) :=
  matrixTraceReal_eq_of_normalizedTrace_eq r (matrixTraceProjection_pairing A X Y hY)

theorem matrixTraceProjection_projection_bounds (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsStarProjection P) :
    0 ≤ matrixTraceProjection A P ∧ matrixTraceProjection A P ≤ 1 := by
  refine ⟨matrixTraceProjection_nonneg A P hP.nonneg, ?_⟩
  have he := matrixTraceProjection_nonneg A (1 - P) hP.one_sub_nonneg
  rw [map_sub, matrixTraceProjection_one] at he
  exact sub_nonneg.mp he

theorem matrixTraceProjection_traceReal_square (r : Nat) (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsSelfAdjoint P) :
    matrixTraceReal r (matrixTraceProjection A P * matrixTraceProjection A P) =
      matrixTraceReal r (P * matrixTraceProjection A P) := by
  have hs := matrixTraceProjection_isSelfAdjoint A P hP
  have he := matrixTraceProjection_traceReal_pairing r A P (matrixTraceProjection A P)
    (matrixTraceProjection_mem A P)
  rw [hs.star_eq, matrixTraceReal_mul_comm r (matrixTraceProjection A P) P] at he
  exact he

theorem matrixTraceProjection_projection_variance (r : Nat) (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsStarProjection P) :
    rectHSNorm r (P - matrixTraceProjection A P) ^ 2 =
      matrixTraceReal r (matrixTraceProjection A P - matrixTraceProjection A P * matrixTraceProjection A P) := by
  rw [rectHSNorm_sub_sq_hermitian r hP.isSelfAdjoint.isHermitian
      (matrixTraceProjection_isSelfAdjoint A P hP.isSelfAdjoint).isHermitian,
    hP.isIdempotentElem.eq, matrixTraceReal_sub, matrixTraceProjection_traceReal,
    matrixTraceProjection_traceReal_square r A hP.isSelfAdjoint]
  ring

theorem matrixTraceProjection_preserves_commutation (A : StarSubalgebra ℂ (CMatrix d))
    (X Y : CMatrix d) (hY : Y ∈ A) (hXY : X * Y = Y * X) :
    matrixTraceProjection A X * Y = Y * matrixTraceProjection A X := by
  rw [← matrixTraceProjection_mul_right A X Y hY, hXY, matrixTraceProjection_mul_left A Y X hY]

theorem matrixHalfProjection_expectation_mem (A : StarSubalgebra ℂ (CMatrix d)) (P : CMatrix d) :
    matrixHalfProjection (matrixTraceProjection A P) ∈ A := by
  let : IsClosed (A : Set (CMatrix d)) := A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  exact cfc_mem (𝕜' := ℂ) (s := A) (spectralStep (1 / 2)) (matrixTraceProjection_mem A P)

theorem matrixHalfProjection_expectation_distance_le (r : Nat) (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsStarProjection P) :
    rectHSNorm r (P - matrixHalfProjection (matrixTraceProjection A P)) ^ 2 ≤
      2 * rectHSNorm r (P - matrixTraceProjection A P) ^ 2 := by
  let h := matrixTraceProjection A P
  let Q := matrixHalfProjection h
  have hQ : IsStarProjection Q := matrixHalfProjection_isStarProjection h
  have hpq := matrixTraceProjection_traceReal_pairing r A P Q (matrixHalfProjection_expectation_mem A P)
  rw [hQ.isSelfAdjoint.star_eq, matrixTraceReal_mul_comm r Q h,
    matrixTraceReal_mul_comm r Q P] at hpq
  have hb := matrixTraceProjection_projection_bounds A hP
  have he := matrixTraceReal_mono r (matrixHalfProjection_order_bounds hb.1 hb.2).2.2
  rw [rectHSNorm_sub_sq_hermitian r hP.isSelfAdjoint.isHermitian hQ.isSelfAdjoint.isHermitian,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, ← hpq,
    matrixTraceProjection_projection_variance r A hP]
  simp only [matrixTraceReal_sub, matrixTraceReal_add, matrixTraceReal_real_smul,
    matrixTraceProjection_traceReal] at he ⊢
  dsimp only [h, Q] at *
  linarith

theorem matrixHalfProjection_expectation_trace_error_le (r : Nat) (A : StarSubalgebra ℂ (CMatrix d))
    {P : CMatrix d} (hP : IsStarProjection P) :
    |matrixTraceReal r (matrixHalfProjection (matrixTraceProjection A P)) - matrixTraceReal r P| ≤
      2 * rectHSNorm r (P - matrixTraceProjection A P) ^ 2 := by
  have hb := matrixTraceProjection_projection_bounds A hP
  have he := matrixHalfProjection_order_bounds hb.1 hb.2
  have hu := matrixTraceReal_mono r he.1
  have hl := matrixTraceReal_mono r he.2.1
  rw [matrixTraceProjection_projection_variance r A hP]
  simp only [matrixTraceReal_sub, matrixTraceReal_real_smul, matrixTraceProjection_traceReal] at hu hl ⊢
  exact abs_le.mpr ⟨by linarith, hu⟩

end ThomGame.Analysis
