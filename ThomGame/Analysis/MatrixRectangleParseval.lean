module

public import ThomGame.Analysis.MatrixOrthogonalRectangleSums

/-!
# Parseval identities for a two-dimensional family of matrix rectangles

All norms retain the normalization of the original ambient matrix algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {d : Nat}

theorem matrixOrthogonalRectangles_sum_hsNorm_sq_right {μ : Type*} [Fintype μ]
    (Q X : μ → CMatrix d) (hQ : ∀ i, IsStarProjection (Q i))
    (horth : Pairwise (fun i j => Q i * Q j = 0)) (hr : ∀ i, X i * Q i = X i) :
    hsNorm (∑ i, X i) ^ 2 = ∑ i, hsNorm (X i) ^ 2 := by
  have hl i : Q i * star (X i) = star (X i) := by
    simpa only [star_mul, (hQ i).isSelfAdjoint.star_eq] using congrArg star (hr i)
  have h := matrixOrthogonalRectangles_sum_hsNorm_sq Q (fun i => star (X i)) hQ horth hl
  rw [← star_sum] at h
  simpa only [Matrix.star_eq_conjTranspose, hsNorm_conjTranspose] using h

theorem matrixRectangles_sum_hsNorm_sq {μ ν : Type*} [Fintype μ] [Fintype ν]
    (P : μ → CMatrix d) (Q : ν → CMatrix d) (X : μ → ν → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (horthP : Pairwise (fun i j => P i * P j = 0))
    (horthQ : Pairwise (fun i j => Q i * Q j = 0))
    (hl : ∀ i j, P i * X i j = X i j) (hr : ∀ i j, X i j * Q j = X i j) :
    hsNorm (∑ i, ∑ j, X i j) ^ 2 = ∑ i, ∑ j, hsNorm (X i j) ^ 2 := by
  have hrows i : P i * (∑ j, X i j) = ∑ j, X i j := by
    simp only [Finset.mul_sum, hl]
  rw [matrixOrthogonalRectangles_sum_hsNorm_sq P (fun i => ∑ j, X i j) hP horthP hrows]
  exact Finset.sum_congr rfl (fun i _ =>
    matrixOrthogonalRectangles_sum_hsNorm_sq_right Q (X i) hQ horthQ (hr i))

theorem matrixRectangles_sum_compression {μ ν : Type*} [Fintype μ] [Fintype ν]
    (P : μ → CMatrix d) (Q : ν → CMatrix d) (X : CMatrix d) :
    (∑ i, ∑ j, P i * X * Q j) = (∑ i, P i) * X * (∑ j, Q j) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end ThomGame.Analysis
