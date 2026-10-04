module

public import ThomGame.Analysis.MatrixRectangleMapBound
public import ThomGame.Analysis.MatrixSubmoduleProjectionCompression
public import ThomGame.Analysis.MatrixCompressionTraceLoss

/-!
# Global mixed-norm error of the actual completed algebra expectation

The retained-corner estimate and the two discarded trace masses suffice.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem matrixUnitSpan_completed_expectation_bound
    (F : CMatrix d →ₗ[ℂ] CMatrix d) (hF : ∀ X, hsNorm (F X) ≤ hsNorm X)
    (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j)
    (hinv : ∀ i j X, X ∈ matrixRectangleSubmodule (E i) (E j) →
      F X ∈ matrixRectangleSubmodule (E i) (E j))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i j, ‖matrixRectangleHilbertMap F (E i) (E j) (hinv i j) -
      matrixRectangleLineProjection (E i) (E j) (W i j) (hsupport i j).1 (hsupport i j).2‖ ≤ C)
    (Q : CMatrix d) (hQ : IsStarProjection Q) (A : StarSubalgebra ℂ (CMatrix d))
    (hexpect : ∀ X, matrixTraceProjection A X = matrixSubmoduleTraceProjection (matrixUnitSpan W) X +
      (1 - Q) * X * (1 - Q)) :
    matrixMixedNorm (F - matrixTraceProjection A) ≤ C +
      Real.sqrt (2 * (normalizedTrace (1 - ∑ i, E i)).re) + Real.sqrt (normalizedTrace (1 - Q)).re := by
  let P := ∑ i, E i
  let G := matrixSubmoduleTraceProjection (matrixUnitSpan W)
  have hP : IsStarProjection P := matrixProjection_sum E hE horth
  apply matrixMixedNorm_le_of_unit_bound _ _ (by positivity)
  intro X hX
  have hl : P * (P * X * P) = P * X * P := by
    simp only [← mul_assoc, hP.isIdempotentElem.eq]
  have hr : (P * X * P) * P = P * X * P := by rw [mul_assoc, hP.isIdempotentElem.eq]
  have hcorner : hsNorm (F (P * X * P) - G X) ≤ C := by
    have h := matrixUnitSpan_corner_error_bound F E W hE horth hsupport hinv C hC hbound
      (P * X * P) hl hr
    rw [matrixUnitSpan_projection_compression E W hE horth hsupport X] at h
    exact h.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        ((matrixProjection_compression_hsNorm_le P X hP).trans ((hsNorm_le_matrixOpNorm X).trans hX)) hC)
  have hloss : hsNorm (F (X - P * X * P)) ≤ Real.sqrt (2 * (normalizedTrace (1 - P)).re) :=
    (hF _).trans (matrixProjection_compression_loss P X hP hX)
  have hcomp := matrixProjection_compression_trace_bound (1 - Q) X hQ.one_sub hX
  have he : F X - matrixTraceProjection A X = F (X - P * X * P) +
      (F (P * X * P) - G X) + -((1 - Q) * X * (1 - Q)) := by
    rw [hexpect, map_sub]
    dsimp [G]
    abel
  change hsNorm (F X - matrixTraceProjection A X) ≤ _
  rw [he]
  calc
    _ ≤ hsNorm (F (X - P * X * P) + (F (P * X * P) - G X)) +
        hsNorm (-((1 - Q) * X * (1 - Q))) :=
      hsNorm_add_le (F (X - P * X * P) + (F (P * X * P) - G X)) (-((1 - Q) * X * (1 - Q)))
    _ ≤ hsNorm (F (X - P * X * P)) + hsNorm (F (P * X * P) - G X) +
        hsNorm ((1 - Q) * X * (1 - Q)) := by
      exact add_le_add (hsNorm_add_le (F (X - P * X * P)) (F (P * X * P) - G X))
        (le_of_eq (hsNorm_neg ((1 - Q) * X * (1 - Q))))
    _ ≤ Real.sqrt (2 * (normalizedTrace (1 - P)).re) + C +
        Real.sqrt (normalizedTrace (1 - Q)).re := add_le_add (add_le_add hloss hcorner) hcomp
    _ = _ := by dsimp [P]; ring

end ThomGame.Analysis
