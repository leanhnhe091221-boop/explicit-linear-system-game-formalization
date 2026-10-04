module

public import ThomGame.Analysis.MatrixRectangleLineProjection

/-!
# Operator norm bounds on the actual rectangular trace Hilbert space
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem matrixRectangleHilbertMap_bound (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q : CMatrix d)
    (hinv : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q)
    (rho : ℝ) (hbound : ‖matrixRectangleHilbertMap F P Q hinv‖ ≤ rho)
    (X : CMatrix d) (hXl : P * X = X) (hXr : X * Q = X) :
    hsNorm (F X) ≤ rho * hsNorm X := by
  have h := (matrixRectangleHilbertMap F P Q hinv).le_opNorm
    (matrixRectangleVector P Q X hXl hXr)
  change ‖finiteMatrixHilbertEquiv d (F X)‖ ≤
    ‖matrixRectangleHilbertMap F P Q hinv‖ * ‖finiteMatrixHilbertEquiv d X‖ at h
  rw [finiteMatrixHilbert_norm, finiteMatrixHilbert_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right hbound (hsNorm_nonneg X))

theorem matrixRectangle_fixed_error_lower (F : CMatrix d →ₗ[ℂ] CMatrix d) (P Q : CMatrix d)
    (hinv : ∀ X ∈ matrixRectangleSubmodule P Q, F X ∈ matrixRectangleSubmodule P Q)
    (rho : ℝ) (hbound : ‖matrixRectangleHilbertMap F P Q hinv‖ ≤ rho)
    (X : CMatrix d) (hXl : P * X = X) (hXr : X * Q = X) :
    (1 - rho) * hsNorm X ≤ hsNorm (F X - X) := by
  have h := matrixRectangleHilbertMap_bound F P Q hinv rho hbound X hXl hXr
  have ht := hsNorm_add_le (X - F X) (F X)
  rw [sub_add_cancel, hsNorm_sub_comm X (F X)] at ht
  linarith

end ThomGame.Analysis
