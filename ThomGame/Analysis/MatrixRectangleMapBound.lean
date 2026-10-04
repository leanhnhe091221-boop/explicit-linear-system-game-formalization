module

public import ThomGame.Analysis.MatrixRectangleParseval
public import ThomGame.Analysis.MatrixRectangleProjectionError

/-!
# Blockwise Hilbert bounds give a bound on the entire retained corner

Orthogonality avoids any dependence on the number of blocks.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {d : Nat} {μ : Type*} [Fintype μ]

theorem matrixRectangles_map_sum_bound
    (T : CMatrix d →ₗ[ℂ] CMatrix d) (E : μ → CMatrix d) (X : μ → μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * X i j = X i j ∧ X i j * E j = X i j)
    (hinv : ∀ i j Y, Y ∈ matrixRectangleSubmodule (E i) (E j) →
      T Y ∈ matrixRectangleSubmodule (E i) (E j))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i j, hsNorm (T (X i j)) ≤ C * hsNorm (X i j)) :
    hsNorm (T (∑ i, ∑ j, X i j)) ≤ C * hsNorm (∑ i, ∑ j, X i j) := by
  have hs := matrixRectangles_sum_hsNorm_sq E E X hE hE horth horth
    (fun i j => (hsupport i j).1) (fun i j => (hsupport i j).2)
  have ht := matrixRectangles_sum_hsNorm_sq E E (fun i j => T (X i j)) hE hE horth horth
    (fun i j => (hinv i j _ (hsupport i j)).1) (fun i j => (hinv i j _ (hsupport i j)).2)
  apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg hC (hsNorm_nonneg _))).mp
  calc
    hsNorm (T (∑ i, ∑ j, X i j)) ^ 2 = ∑ i, ∑ j, hsNorm (T (X i j)) ^ 2 := by
      simpa only [map_sum] using ht
    _ ≤ ∑ i, ∑ j, (C * hsNorm (X i j)) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (hsNorm_nonneg _) (hbound i j) 2))
    _ = (C * hsNorm (∑ i, ∑ j, X i j)) ^ 2 := by
      simp only [mul_pow, hs, Finset.mul_sum]

theorem matrixRectangles_map_corner_bound
    (T : CMatrix d →ₗ[ℂ] CMatrix d) (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hinv : ∀ i j Y, Y ∈ matrixRectangleSubmodule (E i) (E j) →
      T Y ∈ matrixRectangleSubmodule (E i) (E j))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i j Y, Y ∈ matrixRectangleSubmodule (E i) (E j) → hsNorm (T Y) ≤ C * hsNorm Y)
    (X : CMatrix d) (hXl : (∑ i, E i) * X = X) (hXr : X * (∑ i, E i) = X) :
    hsNorm (T X) ≤ C * hsNorm X := by
  have hslice i j : E i * (E i * X * E j) = E i * X * E j ∧
      (E i * X * E j) * E j = E i * X * E j := by
    constructor
    · simp only [← mul_assoc, (hE i).isIdempotentElem.eq]
    · rw [mul_assoc, (hE j).isIdempotentElem.eq]
  have hsum : (∑ i, ∑ j, E i * X * E j) = X := by
    rw [matrixRectangles_sum_compression, hXl, hXr]
  have h := matrixRectangles_map_sum_bound T E (fun i j => E i * X * E j) hE horth
    hslice hinv C hC (fun i j => hbound i j _ (hslice i j))
  simpa only [hsum] using h

theorem matrixUnitSpan_corner_error_bound [NeZero d]
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j)
    (hinv : ∀ i j X, X ∈ matrixRectangleSubmodule (E i) (E j) →
      F X ∈ matrixRectangleSubmodule (E i) (E j))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i j, ‖matrixRectangleHilbertMap F (E i) (E j) (hinv i j) -
      matrixRectangleLineProjection (E i) (E j) (W i j) (hsupport i j).1 (hsupport i j).2‖ ≤ C)
    (X : CMatrix d) (hXl : (∑ i, E i) * X = X) (hXr : X * (∑ i, E i) = X) :
    hsNorm (F X - matrixSubmoduleTraceProjection (matrixUnitSpan W) X) ≤ C * hsNorm X := by
  apply matrixRectangles_map_corner_bound (F - matrixSubmoduleTraceProjection (matrixUnitSpan W))
    E hE horth ?_ C hC ?_ X hXl hXr
  · intro i j Y hY
    exact (matrixRectangleSubmodule (E i) (E j)).sub_mem (hinv i j Y hY)
      (matrixUnitSpan_projection_invariant E W hE horth hsupport i j Y hY)
  · intro i j Y hY
    exact matrixUnitSpan_rectangle_error_bound F E W hE horth hsupport i j (hinv i j)
      C (hbound i j) Y hY.1 hY.2

end ThomGame.Analysis
