module

public import ThomGame.Analysis.MatrixBlockPinching

/-!
# Pinching defect as total projection mixing

The actual squared distance to the block pinching equals both
trace(a-a squared) and the sum of the individual mixing defects.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.Frobenius

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

omit [DecidableEq ι] in
theorem rectHSNorm_sub_sq_hermitian (r : Nat) {X Y : Matrix ι ι ℂ}
    (hX : Matrix.IsHermitian X) (hY : Matrix.IsHermitian Y) :
    rectHSNorm r (X - Y) ^ 2 = matrixTraceReal r (X * X) -
      2 * matrixTraceReal r (X * Y) + matrixTraceReal r (Y * Y) := by
  have he := matrixTraceReal_gram r (X - Y)
  simp only [Matrix.conjTranspose_sub, hX.eq, hY.eq, Matrix.sub_mul, Matrix.mul_sub,
    matrixTraceReal_sub, matrixTraceReal_mul_comm r Y X] at he
  linarith

theorem matrixBlockPinch_projection_bounds (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (hsum : ∑ i, E i = 1)
    {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    0 ≤ matrixBlockPinch E P ∧ matrixBlockPinch E P ≤ 1 := by
  refine ⟨matrixBlockPinch_nonneg E hE hP.nonneg, ?_⟩
  have he := matrixBlockPinch_nonneg E hE hP.one_sub.nonneg
  rw [matrixBlockPinch_sub, matrixBlockPinch_one E hE hsum] at he
  exact sub_nonneg.mp he

omit [DecidableEq ι] in
theorem matrixBlockPinch_trace_square (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (P : Matrix ι ι ℂ) : matrixTraceReal r (matrixBlockPinch E P * matrixBlockPinch E P) =
      matrixTraceReal r (P * matrixBlockPinch E P) := by
  rw [matrixBlockPinch_trace_pairing, matrixBlockPinch_idempotent E hE horth]

theorem rectHSNorm_pinching_defect_eq_trace (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    rectHSNorm r (P - matrixBlockPinch E P) ^ 2 =
      matrixTraceReal r (matrixBlockPinch E P - matrixBlockPinch E P * matrixBlockPinch E P) := by
  rw [rectHSNorm_sub_sq_hermitian r hP.isSelfAdjoint.isHermitian
      (matrixBlockPinch_isHermitian E hE hP.isSelfAdjoint.isHermitian),
    hP.isIdempotentElem.eq, matrixTraceReal_sub, matrixBlockPinch_trace r E hE hsum,
    matrixBlockPinch_trace_square r E hE horth]
  ring

theorem matrixProjectionMixing_sum (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hsum : ∑ i, E i = 1) (P : Matrix ι ι ℂ) :
    (∑ i, matrixProjectionMixing r (E i) P) =
      matrixTraceReal r P - matrixTraceReal r (P * matrixBlockPinch E P) := by
  have hfirst : (∑ i, matrixTraceReal r (E i * P)) = matrixTraceReal r P := by
    rw [← matrixTraceReal_sum, ← Matrix.sum_mul, hsum, Matrix.one_mul]
  have hsecond : (∑ i, matrixTraceReal r (E i * P * E i * P)) =
      matrixTraceReal r (P * matrixBlockPinch E P) := by
    rw [matrixBlockPinch, Matrix.mul_sum, matrixTraceReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [matrixTraceReal_mul_comm r P (E i * P * E i)]
  simp only [matrixProjectionMixing, Finset.sum_sub_distrib, hfirst, hsecond]

theorem rectHSNorm_pinching_defect_eq_mixing_sum (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    rectHSNorm r (P - matrixBlockPinch E P) ^ 2 = ∑ i, matrixProjectionMixing r (E i) P := by
  rw [rectHSNorm_pinching_defect_eq_trace r E hE horth hsum hP, matrixTraceReal_sub,
    matrixBlockPinch_trace r E hE hsum, matrixBlockPinch_trace_square r E hE horth,
    matrixProjectionMixing_sum r E hsum]

end ThomGame.Analysis
