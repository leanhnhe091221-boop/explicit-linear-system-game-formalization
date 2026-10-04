module

public import ThomGame.Analysis.MatrixRandomSignSums
public import ThomGame.Analysis.MatrixBlockPinching

/-!
# Pinching as the average of diagonal sign conjugations

The exact finite average proves contraction in the ambient operator norm,
uniformly in both the dimension and the number of blocks.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} {μ : Type*} [Fintype μ]

theorem matrixSignSum_sandwich (E : μ → CMatrix d) (ε : μ → Bool) (X : CMatrix d) :
    finiteSignSum E ε * X * finiteSignSum E ε =
      ∑ i, ∑ j, (finiteSign (ε i) * finiteSign (ε j)) • (E i * X * E j) := by
  simp only [finiteSignSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem matrix_expect_real_smul [DecidableEq μ] (f : μ → ℝ) (X : CMatrix d) :
    (𝔼 i, f i • X) = (𝔼 i, f i) • X := by
  simp only [Finset.expect, ← Finset.sum_smul, smul_assoc]

theorem matrixSignSum_expect_sandwich [DecidableEq μ] (E : μ → CMatrix d) (X : CMatrix d) :
    (𝔼 ε : μ → Bool, finiteSignSum E ε * X * finiteSignSum E ε) = matrixBlockPinch E X := by
  simp only [matrixSignSum_sandwich, Finset.expect_sum_comm,
    matrix_expect_real_smul, finiteSign_expect_mul]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, matrixBlockPinch]

theorem matrixBlockPinch_matrixOpNorm_le (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (X : CMatrix d) : matrixOpNorm (matrixBlockPinch E X) ≤ matrixOpNorm X := by
  classical
  have hn (q : ℚ≥0) (Y : CMatrix d) : ‖q • Y‖ = q • ‖Y‖ := by
    simpa only [NNRat.cast_smul_eq_nnqsmul, NNRat.smul_def] using
      norm_smul_of_nonneg (NNRat.cast_nonneg (α := ℝ) q) Y
  have havg : ‖𝔼 ε : μ → Bool, finiteSignSum E ε * X * finiteSignSum E ε‖ ≤
      𝔼 ε : μ → Bool, ‖finiteSignSum E ε * X * finiteSignSum E ε‖ :=
    Finset.le_expect_of_subadditive norm_zero norm_add_le (fun n Y => hn (n : ℚ≥0)⁻¹ Y)
  rw [matrixSignSum_expect_sandwich] at havg
  change ‖matrixBlockPinch E X‖ ≤ ‖X‖
  apply havg.trans
  apply Finset.expect_le Finset.univ_nonempty
  intro ε _
  have hs : ‖finiteSignSum E ε‖ ≤ 1 := matrixSignSum_matrixOpNorm_le_one E hE horth ε
  calc
    _ ≤ (‖finiteSignSum E ε‖ * ‖X‖) * ‖finiteSignSum E ε‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖X‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hs (norm_nonneg _)) hs (norm_nonneg _) (by positivity)
    _ = ‖X‖ := by rw [one_mul, mul_one]

end ThomGame.Analysis
