module

public import ThomGame.Analysis.MatrixOrthogonalCornerSums
public import ThomGame.Analysis.MatrixProjectionRankSums

/-!
# Completing an orthogonal projection family to a partition

The additional block, indexed by `none`, is the actual complement
of the sum. Existing blocks keep their indices under `some`.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ]

noncomputable def matrixProjectionCompletion (E : μ → Matrix ι ι ℂ) : Option μ → Matrix ι ι ℂ
  | none => 1 - ∑ i, E i
  | some i => E i

omit [Fintype ι] in
@[simp] theorem matrixProjectionCompletion_none (E : μ → Matrix ι ι ℂ) :
    matrixProjectionCompletion E none = 1 - ∑ i, E i := rfl

omit [Fintype ι] in
@[simp] theorem matrixProjectionCompletion_some (E : μ → Matrix ι ι ℂ) (i : μ) :
    matrixProjectionCompletion E (some i) = E i := rfl

theorem matrixProjectionCompletion_isStarProjection (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (i : Option μ) : IsStarProjection (matrixProjectionCompletion E i) := by
  cases i with
  | none => exact (matrixProjection_sum E hE horth).one_sub
  | some i => exact hE i

theorem matrixProjectionCompletion_orthogonal (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0)) :
    Pairwise (fun i j => matrixProjectionCompletion E i * matrixProjectionCompletion E j = 0) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      change (1 - ∑ i, E i) * E j = 0
      rw [Matrix.sub_mul, Matrix.one_mul,
        matrixCorner_sum_block_right E E horth (fun i => (hE i).isIdempotentElem.eq), sub_self]
  | some i =>
    cases j with
    | none =>
      change E i * (1 - ∑ j, E j) = 0
      rw [Matrix.mul_sub, Matrix.mul_one,
        matrixCorner_sum_block_left E E horth (fun j => (hE j).isIdempotentElem.eq), sub_self]
    | some j => exact horth (fun he => hij (congrArg some he))

omit [Fintype ι] in
theorem matrixProjectionCompletion_sum (E : μ → Matrix ι ι ℂ) :
    ∑ i, matrixProjectionCompletion E i = 1 := by
  rw [Fintype.sum_option]
  simp only [matrixProjectionCompletion_none, matrixProjectionCompletion_some, sub_add_cancel]

end ThomGame.Analysis
