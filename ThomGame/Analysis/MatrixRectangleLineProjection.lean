module

public import ThomGame.Analysis.MatrixBimoduleRectangles
public import ThomGame.Analysis.LineProjectionPerturbation

/-!
# Orthogonal projection onto an actual rectangular matrix direction

The Hilbert space and its normalization are the original rectangular
subspace of the ambient normalized trace Hilbert space.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

def matrixRectangleVector (P Q X : CMatrix d) (hl : P * X = X) (hr : X * Q = X) :
    matrixRectangleHilbert P Q := ⟨finiteMatrixHilbertEquiv d X, hl, hr⟩

noncomputable def matrixRectangleLineProjection (P Q X : CMatrix d) (hl : P * X = X) (hr : X * Q = X) :
    matrixRectangleHilbert P Q →L[ℂ] matrixRectangleHilbert P Q :=
  (ℂ ∙ matrixRectangleVector P Q X hl hr).starProjection

omit [NeZero d] in
theorem matrixRectangleVector_ne_zero (P Q X : CMatrix d) (hl : P * X = X) (hr : X * Q = X) (hX : X ≠ 0) :
    matrixRectangleVector P Q X hl hr ≠ 0 := by
  intro hz
  exact hX (congrArg (fun v : matrixRectangleHilbert P Q => (finiteMatrixHilbertEquiv d).symm v.val) hz)

@[simp] theorem matrixRectangleVector_norm (P Q X : CMatrix d) (hl : P * X = X) (hr : X * Q = X) :
    ‖matrixRectangleVector P Q X hl hr‖ = hsNorm X := finiteMatrixHilbert_norm d X

theorem matrixRectangleLineProjection_distance_sq (P Q X Y : CMatrix d)
    (hXl : P * X = X) (hXr : X * Q = X) (hYl : P * Y = Y) (hYr : Y * Q = Y)
    (hX : X ≠ 0) (hY : Y ≠ 0) (epsilon : ℝ) (hdist : hsNorm (X - Y) ^ 2 ≤ epsilon * hsNorm X ^ 2) :
    ‖matrixRectangleLineProjection P Q X hXl hXr - matrixRectangleLineProjection P Q Y hYl hYr‖ ^ 2 ≤
      16 * epsilon := by
  apply lineProjection_distance_sq _ _ (matrixRectangleVector_ne_zero P Q X hXl hXr hX)
    (matrixRectangleVector_ne_zero P Q Y hYl hYr hY) epsilon
  change ‖finiteMatrixHilbertEquiv d (X - Y)‖ ^ 2 ≤ epsilon * ‖finiteMatrixHilbertEquiv d X‖ ^ 2
  simpa only [finiteMatrixHilbert_norm] using hdist

end ThomGame.Analysis
