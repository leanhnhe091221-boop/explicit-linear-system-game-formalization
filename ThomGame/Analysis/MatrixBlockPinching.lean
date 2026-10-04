module

public import ThomGame.Analysis.MatrixProjectionMixing

/-!
# Actual pinching by a finite orthogonal projection partition

The map is the finite sum of E_i X E_i. It is positive, unital,
trace preserving, idempotent, and its image commutes with each block.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.Frobenius

variable {ι μ : Type*} [Fintype ι] [Fintype μ]

noncomputable def matrixBlockPinch (E : μ → Matrix ι ι ℂ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ i, E i * X * E i

theorem matrixBlockPinch_sub (E : μ → Matrix ι ι ℂ) (X Y : Matrix ι ι ℂ) :
    matrixBlockPinch E (X - Y) = matrixBlockPinch E X - matrixBlockPinch E Y := by
  simp only [matrixBlockPinch, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem matrixBlockPinch_nonneg (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    {X : Matrix ι ι ℂ} (hX : 0 ≤ X) : 0 ≤ matrixBlockPinch E X := by
  apply Finset.sum_nonneg
  intro i _
  have he := (Matrix.nonneg_iff_posSemidef.mp hX).mul_mul_conjTranspose_same (E i)
  simpa only [(hE i).isSelfAdjoint.isHermitian.eq] using he.nonneg

theorem matrixBlockPinch_isHermitian (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    {X : Matrix ι ι ℂ} (hX : Matrix.IsHermitian X) : Matrix.IsHermitian (matrixBlockPinch E X) := by
  show (matrixBlockPinch E X)ᴴ = matrixBlockPinch E X
  simp only [matrixBlockPinch, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    fun i => (hE i).isSelfAdjoint.isHermitian.eq, hX.eq, Matrix.mul_assoc]

theorem matrixBlockPinch_one [DecidableEq ι] (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (hsum : ∑ i, E i = 1) : matrixBlockPinch E 1 = 1 := by
  simpa only [matrixBlockPinch, Matrix.mul_one, fun i => (hE i).isIdempotentElem.eq] using hsum

theorem matrixBlockPinch_trace [DecidableEq ι] (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (hsum : ∑ i, E i = 1) (X : Matrix ι ι ℂ) :
    matrixTraceReal r (matrixBlockPinch E X) = matrixTraceReal r X := by
  rw [matrixBlockPinch, matrixTraceReal_sum]
  simp_rw [fun i => matrixTraceReal_projection_sandwich r (hE i) X]
  rw [← matrixTraceReal_sum, ← Matrix.sum_mul, hsum, Matrix.one_mul]

theorem matrixBlockPinch_block_left (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : ∀ i j, i ≠ j → E i * E j = 0) (j : μ) (X : Matrix ι ι ℂ) :
    E j * matrixBlockPinch E X = E j * X * E j := by
  rw [matrixBlockPinch, Matrix.mul_sum, Finset.sum_eq_single j]
  · rw [← Matrix.mul_assoc (E j), ← Matrix.mul_assoc (E j), (hE j).isIdempotentElem.eq]
  · intro i _ hij
    rw [← Matrix.mul_assoc (E j), ← Matrix.mul_assoc (E j), horth j i hij.symm,
      Matrix.zero_mul, Matrix.zero_mul]
  · simp

theorem matrixBlockPinch_block_right (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : ∀ i j, i ≠ j → E i * E j = 0) (j : μ) (X : Matrix ι ι ℂ) :
    matrixBlockPinch E X * E j = E j * X * E j := by
  rw [matrixBlockPinch, Matrix.sum_mul, Finset.sum_eq_single j]
  · rw [Matrix.mul_assoc (E j * X), (hE j).isIdempotentElem.eq]
  · intro i _ hij
    rw [Matrix.mul_assoc (E i * X), horth i j hij, Matrix.mul_zero]
  · simp

theorem matrixBlockPinch_commute (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : ∀ i j, i ≠ j → E i * E j = 0) (j : μ) (X : Matrix ι ι ℂ) :
    Commute (E j) (matrixBlockPinch E X) := by
  show E j * matrixBlockPinch E X = matrixBlockPinch E X * E j
  rw [matrixBlockPinch_block_left E hE horth, matrixBlockPinch_block_right E hE horth]

theorem matrixBlockPinch_idempotent (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : ∀ i j, i ≠ j → E i * E j = 0) (X : Matrix ι ι ℂ) :
    matrixBlockPinch E (matrixBlockPinch E X) = matrixBlockPinch E X := by
  change (∑ i, E i * matrixBlockPinch E X * E i) = matrixBlockPinch E X
  simp_rw [matrixBlockPinch_block_left E hE horth]
  simp only [Matrix.mul_assoc, fun i => (hE i).isIdempotentElem.eq]
  simp only [matrixBlockPinch, Matrix.mul_assoc]

theorem matrixBlockPinch_trace_pairing (r : Nat) (E : μ → Matrix ι ι ℂ) (X Y : Matrix ι ι ℂ) :
    matrixTraceReal r (matrixBlockPinch E X * Y) = matrixTraceReal r (X * matrixBlockPinch E Y) := by
  simp only [matrixBlockPinch, Matrix.sum_mul, Matrix.mul_sum, matrixTraceReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = matrixTraceReal r (E i * (X * E i * Y)) := by simp only [Matrix.mul_assoc]
    _ = matrixTraceReal r ((X * E i * Y) * E i) := matrixTraceReal_mul_comm r _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end ThomGame.Analysis
