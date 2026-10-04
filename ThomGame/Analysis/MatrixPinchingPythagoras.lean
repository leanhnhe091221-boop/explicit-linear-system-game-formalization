module

public import ThomGame.Analysis.MatrixOrthogonalCornerSums

/-!
# Exact Pythagoras identities for arbitrary matrix block pinching

The input need not be a projection or self-adjoint. This splits the
unitary-correction error into the off-block error and the individual
corner errors without changing normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ]

theorem matrixBlockPinch_conjTranspose (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (X : Matrix ι ι ℂ) : (matrixBlockPinch E X)ᴴ = matrixBlockPinch E Xᴴ := by
  simp only [matrixBlockPinch, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    fun i => (hE i).isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]

theorem matrixBlockPinch_gram_trace (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (X : Matrix ι ι ℂ) :
    matrixTraceReal r ((matrixBlockPinch E X)ᴴ * matrixBlockPinch E X) =
      matrixTraceReal r (Xᴴ * matrixBlockPinch E X) := by
  rw [matrixBlockPinch_conjTranspose E hE, matrixBlockPinch_trace_pairing,
    matrixBlockPinch_idempotent E hE horth]

theorem rectHSNorm_pinching_defect_gram (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (X : Matrix ι ι ℂ) :
    rectHSNorm r (X - matrixBlockPinch E X) ^ 2 = matrixTraceReal r (Xᴴ * X) -
      matrixTraceReal r ((matrixBlockPinch E X)ᴴ * matrixBlockPinch E X) := by
  rw [rectHSNorm_sub_sq, ← matrixBlockPinch_gram_trace r E hE horth]
  ring

theorem rectHSNorm_pinching_pythagoras (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (X Y : Matrix ι ι ℂ) (hY : matrixBlockPinch E Y = Y) :
    rectHSNorm r (X - Y) ^ 2 = rectHSNorm r (X - matrixBlockPinch E X) ^ 2 +
      rectHSNorm r (matrixBlockPinch E X - Y) ^ 2 := by
  have hp : matrixTraceReal r ((matrixBlockPinch E X)ᴴ * Y) = matrixTraceReal r (Xᴴ * Y) := by
    rw [matrixBlockPinch_conjTranspose E hE, matrixBlockPinch_trace_pairing, hY]
  rw [rectHSNorm_sub_sq, rectHSNorm_sub_sq, rectHSNorm_sub_sq,
    ← matrixBlockPinch_gram_trace r E hE horth, hp]
  ring

theorem rectHSNorm_corner_sum_sq (r : Nat) (E X : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hleft : ∀ i, E i * X i = X i) :
    rectHSNorm r (∑ i, X i) ^ 2 = ∑ i, rectHSNorm r (X i) ^ 2 := by
  rw [← matrixTraceReal_gram, matrixCorner_sum_gram E X hE horth hleft, matrixTraceReal_sum]
  simp only [matrixTraceReal_gram]

theorem matrixBlockPinch_corner_sum (E Y : μ → Matrix ι ι ℂ)
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hleft : ∀ i, E i * Y i = Y i) (hright : ∀ i, Y i * E i = Y i) :
    matrixBlockPinch E (∑ i, Y i) = ∑ i, Y i := by
  unfold matrixBlockPinch
  simp_rw [matrixCorner_sum_block_left E Y horth hleft, hright]

theorem rectHSNorm_corner_correction_pythagoras (r : Nat) (E Y : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hleft : ∀ i, E i * Y i = Y i) (hright : ∀ i, Y i * E i = Y i) (X : Matrix ι ι ℂ) :
    rectHSNorm r ((∑ i, Y i) - X) ^ 2 = rectHSNorm r (X - matrixBlockPinch E X) ^ 2 +
      ∑ i, rectHSNorm r (Y i - E i * X * E i) ^ 2 := by
  rw [rectHSNorm_sub_comm r (∑ i, Y i) X,
    rectHSNorm_pinching_pythagoras r E hE horth X _ (matrixBlockPinch_corner_sum E Y horth hleft hright),
    rectHSNorm_sub_comm r (matrixBlockPinch E X) (∑ i, Y i)]
  congr 1
  change rectHSNorm r ((∑ i, Y i) - ∑ i, E i * X * E i) ^ 2 = _
  rw [← Finset.sum_sub_distrib]
  apply rectHSNorm_corner_sum_sq r E _ hE horth
  intro i
  rw [Matrix.mul_sub, hleft]
  congr 1
  simp only [← Matrix.mul_assoc, (hE i).isIdempotentElem.eq]

end ThomGame.Analysis
