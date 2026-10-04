module

public import ThomGame.Analysis.MatrixCornerUnitaryPair

/-!
# Orthogonal corner sums, exact HS norms and unitary assembly
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

omit [DecidableEq ι] in
theorem matrix_sum_gram_of_orthogonal (X : μ → Matrix ι ι ℂ)
    (horth : Pairwise (fun i j => (X i)ᴴ * X j = 0)) :
    (∑ i, X i)ᴴ * (∑ i, X i) = ∑ i, (X i)ᴴ * X i := by
  classical
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_sum, Finset.sum_eq_single i]
  · intro j _ hji
    exact horth hji.symm
  · simp

omit [DecidableEq ι] in
theorem rectHSNorm_orthogonal_sum_sq (r : Nat) (X : μ → Matrix ι ι ℂ)
    (horth : Pairwise (fun i j => (X i)ᴴ * X j = 0)) :
    rectHSNorm r (∑ i, X i) ^ 2 = ∑ i, rectHSNorm r (X i) ^ 2 := by
  rw [← matrixTraceReal_gram, matrix_sum_gram_of_orthogonal X horth, matrixTraceReal_sum]
  simp only [matrixTraceReal_gram]

omit [Fintype μ] in
theorem matrixCorner_gram_support {q X : Matrix ι ι ℂ} (hq : IsStarProjection q)
    (hi : Xᴴ * X = q) (hf : X * Xᴴ = q) : q * X = X ∧ X * q = X := by
  have hX : IsStarProjection (Xᴴ * X) := hi.symm ▸ hq
  have hr : X * q = X := by rw [← hi]; exact matrixPartialIsometry_mul_initial hX
  exact ⟨by rw [← hf, Matrix.mul_assoc, hi, hr], hr⟩

omit [Fintype μ] [DecidableEq ι] in
theorem matrixCorner_cross_mul {E F X Y : Matrix ι ι ℂ}
    (hX : X * E = X) (hY : F * Y = Y) (hEF : E * F = 0) : X * Y = 0 := by
  calc
    _ = (X * E) * (F * Y) := by rw [hX, hY]
    _ = X * (E * F) * Y := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hEF, Matrix.mul_zero, Matrix.zero_mul]

omit [DecidableEq ι] in
theorem matrixCorner_sum_block_left (E X : μ → Matrix ι ι ℂ)
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hleft : ∀ i, E i * X i = X i) (j : μ) : E j * (∑ i, X i) = X j := by
  classical
  rw [Matrix.mul_sum, Finset.sum_eq_single j, hleft]
  · intro i _ hij
    calc
      _ = E j * (E i * X i) := by rw [hleft]
      _ = 0 := by rw [← Matrix.mul_assoc, horth hij.symm, Matrix.zero_mul]
  · simp

omit [DecidableEq ι] in
theorem matrixCorner_sum_block_right (E X : μ → Matrix ι ι ℂ)
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hright : ∀ i, X i * E i = X i) (j : μ) : (∑ i, X i) * E j = X j := by
  classical
  rw [Matrix.sum_mul, Finset.sum_eq_single j, hright]
  · intro i _ hij
    calc
      _ = (X i * E i) * E j := by rw [hright]
      _ = 0 := by rw [Matrix.mul_assoc, horth hij, Matrix.mul_zero]
  · simp

omit [DecidableEq ι] in
theorem matrixCorner_sum_gram (E X : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hleft : ∀ i, E i * X i = X i) :
    (∑ i, X i)ᴴ * (∑ i, X i) = ∑ i, (X i)ᴴ * X i := by
  apply matrix_sum_gram_of_orthogonal
  intro i j hij
  have hi : (X i)ᴴ * E i = (X i)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, (hE i).isSelfAdjoint.isHermitian.eq] using
      congrArg Matrix.conjTranspose (hleft i)
  exact matrixCorner_cross_mul hi (hleft j) (horth hij)

theorem matrixCorner_sum_mem_unitary (E X : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : Pairwise (fun i j => E i * E j = 0)) (hsum : ∑ i, E i = 1)
    (hi : ∀ i, (X i)ᴴ * X i = E i) (hf : ∀ i, X i * (X i)ᴴ = E i) :
    (∑ i, X i) ∈ Matrix.unitaryGroup ι ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (∑ i, X i)ᴴ * (∑ i, X i) = 1
  rw [matrixCorner_sum_gram E X hE horth (fun i => (matrixCorner_gram_support (hE i) (hi i) (hf i)).1)]
  simpa only [hi] using hsum

end ThomGame.Analysis
