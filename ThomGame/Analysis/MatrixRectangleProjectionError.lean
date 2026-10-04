module

public import ThomGame.Analysis.MatrixUnitSpanProjectionRectangles

/-!
# Turning rectangular operator errors into errors for the actual span projection
-/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat} [NeZero d]

theorem matrixRectangle_line_error_bound (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q W : CMatrix d)
    (hinv : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q)
    (hWl : P * W = W) (hWr : W * Q = W) (C : ℝ)
    (hbound : ‖matrixRectangleHilbertMap F P Q hinv - matrixRectangleLineProjection P Q W hWl hWr‖ ≤ C)
    (X : CMatrix d) (hXl : P * X = X) (hXr : X * Q = X) :
    hsNorm (F X - matrixSubmoduleTraceProjection (ℂ ∙ W) X) ≤ C * hsNorm X := by
  let T := matrixRectangleHilbertMap F P Q hinv - matrixRectangleLineProjection P Q W hWl hWr
  have h := T.le_opNorm (matrixRectangleVector P Q X hXl hXr)
  change ‖finiteMatrixHilbertEquiv d (F X - (finiteMatrixHilbertEquiv d).symm
    ((matrixRectangleLineProjection P Q W hWl hWr) (matrixRectangleVector P Q X hXl hXr)).val)‖ ≤
      ‖T‖ * ‖finiteMatrixHilbertEquiv d X‖ at h
  rw [matrixRectangleLineProjection_apply_matrix, finiteMatrixHilbert_norm, finiteMatrixHilbert_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right hbound (hsNorm_nonneg X))

theorem matrixUnitSpan_rectangle_error_bound {μ : Type*}
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j)
    (i j : μ) (hinv : ∀ X ∈ matrixRectangleSubmodule (E i) (E j), F X ∈ matrixRectangleSubmodule (E i) (E j))
    (C : ℝ)
    (hbound : ‖matrixRectangleHilbertMap F (E i) (E j) hinv -
      matrixRectangleLineProjection (E i) (E j) (W i j) (hsupport i j).1 (hsupport i j).2‖ ≤ C)
    (X : CMatrix d) (hXl : E i * X = X) (hXr : X * E j = X) :
    hsNorm (F X - matrixSubmoduleTraceProjection (matrixUnitSpan W) X) ≤ C * hsNorm X := by
  rw [matrixUnitSpan_projection_rectangle E W hE horth hsupport i j X hXl hXr]
  exact matrixRectangle_line_error_bound F (E i) (E j) (W i j) hinv
    (hsupport i j).1 (hsupport i j).2 C hbound X hXl hXr

end ThomGame.Analysis
