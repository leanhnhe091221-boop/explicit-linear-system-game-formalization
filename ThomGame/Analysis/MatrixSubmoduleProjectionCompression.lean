module

public import ThomGame.Analysis.MatrixUnitSpanProjectionRectangles
public import ThomGame.Analysis.MatrixProjectionRankSums

/-!
# Trace projection onto a supported submodule ignores the other rectangles
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat}

theorem matrixSubmoduleTraceProjection_compression [NeZero d]
    (S : Submodule ℂ (CMatrix d)) (P Q : CMatrix d)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hS : S ≤ matrixRectangleSubmodule P Q) (X : CMatrix d) :
    matrixSubmoduleTraceProjection S (P * X * Q) = matrixSubmoduleTraceProjection S X := by
  apply matrixSubmoduleTraceProjection_unique
  · exact matrixSubmoduleTraceProjection_mem S X
  · intro B hB
    rw [mul_sub, normalizedTrace_sub,
      matrixRectangle_pairing_compress_right P Q X B hP hQ (hS hB).1 (hS hB).2,
      ← normalizedTrace_sub, ← mul_sub]
    exact matrixSubmoduleTraceProjection_orthogonal S X B hB

theorem matrixUnitSpan_le_rectangle_sum {μ : Type*} [Fintype μ]
    (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j) :
    matrixUnitSpan W ≤ matrixRectangleSubmodule (∑ i, E i) (∑ i, E i) := by
  have hp := matrixProjection_sum E hE horth
  have hle i : E i ≤ ∑ j, E j := Finset.single_le_sum (fun j _ => (hE j).nonneg) (Finset.mem_univ i)
  apply Submodule.span_le.mpr
  rintro Z ⟨⟨i, j⟩, rfl⟩
  constructor
  · calc
      (∑ k, E k) * W i j = (∑ k, E k) * (E i * W i j) := by rw [(hsupport i j).1]
      _ = W i j := by rw [← mul_assoc, ((hE i).le_iff_mul_eq_right hp).mp (hle i), (hsupport i j).1]
  · calc
      W i j * (∑ k, E k) = (W i j * E j) * (∑ k, E k) := by rw [(hsupport i j).2]
      _ = W i j := by rw [mul_assoc, ((hE j).le_iff_mul_eq_left hp).mp (hle j), (hsupport i j).2]

theorem matrixUnitSpan_projection_compression [NeZero d] {μ : Type*} [Fintype μ]
    (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j) (X : CMatrix d) :
    matrixSubmoduleTraceProjection (matrixUnitSpan W) ((∑ i, E i) * X * (∑ i, E i)) =
      matrixSubmoduleTraceProjection (matrixUnitSpan W) X :=
  matrixSubmoduleTraceProjection_compression (matrixUnitSpan W) _ _
    (matrixProjection_sum E hE horth) (matrixProjection_sum E hE horth)
    (matrixUnitSpan_le_rectangle_sum E W hE horth hsupport) X

end ThomGame.Analysis
