module

public import ThomGame.Analysis.FiniteRectMatrixHilbert
public import ThomGame.Analysis.MatrixSubalgebraCornerUnitBalls
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Actual Hausdorff distances with the original HS normalization

Operator-norm unit balls are viewed in the matrix Hilbert space whose
normalizing denominator is r. The ambient matrix size need not equal r.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {n : Nat}

def matrixHSUnitBall (r : Nat) (A : StarSubalgebra ℂ (CMatrix n)) :
    Set (FiniteRectMatrixHilbert r n n) :=
  (finiteRectMatrixHilbertEquiv r n n) '' {X : CMatrix n | X ∈ A ∧ matrixOpNorm X ≤ 1}

noncomputable def matrixHSUnitBallHausdorff (r : Nat) [NeZero r]
    (A B : StarSubalgebra ℂ (CMatrix n)) : ℝ :=
  Metric.hausdorffDist (matrixHSUnitBall r A) (matrixHSUnitBall r B)

theorem matrixHSUnitBall_nonempty (r : Nat) (A : StarSubalgebra ℂ (CMatrix n)) :
    (matrixHSUnitBall r A).Nonempty := by
  refine ⟨finiteRectMatrixHilbertEquiv r n n 0, 0, ⟨A.zero_mem, ?_⟩, rfl⟩
  simp [matrixOpNorm]

theorem matrixHSUnitBall_dist (r : Nat) [NeZero r] (X Y : CMatrix n) :
    dist (finiteRectMatrixHilbertEquiv r n n X) (finiteRectMatrixHilbertEquiv r n n Y) =
      rectHSNorm r (X - Y) := by
  rw [dist_eq_norm, ← map_sub, finiteRectMatrixHilbert_norm]

theorem matrixHSUnitBallHausdorff_nonneg (r : Nat) [NeZero r]
    (A B : StarSubalgebra ℂ (CMatrix n)) : 0 ≤ matrixHSUnitBallHausdorff r A B :=
  Metric.hausdorffDist_nonneg

theorem matrixHSUnitBall_hausdorffEDist_le (r : Nat) [NeZero r]
    (A B : StarSubalgebra ℂ (CMatrix n)) {ε : ℝ}
    (hAB : ∀ X ∈ A, matrixOpNorm X ≤ 1 →
      ∃ Y ∈ B, matrixOpNorm Y ≤ 1 ∧ rectHSNorm r (X - Y) ≤ ε)
    (hBA : ∀ Y ∈ B, matrixOpNorm Y ≤ 1 →
      ∃ X ∈ A, matrixOpNorm X ≤ 1 ∧ rectHSNorm r (Y - X) ≤ ε) :
    Metric.hausdorffEDist (matrixHSUnitBall r A) (matrixHSUnitBall r B) ≤ ENNReal.ofReal ε := by
  apply Metric.hausdorffEDist_le_of_mem_edist
  · rintro _ ⟨X, ⟨hXA, hn⟩, rfl⟩
    obtain ⟨Y, hYB, hYn, hd⟩ := hAB X hXA hn
    refine ⟨finiteRectMatrixHilbertEquiv r n n Y, ⟨Y, ⟨hYB, hYn⟩, rfl⟩, ?_⟩
    rw [edist_dist, matrixHSUnitBall_dist]
    exact ENNReal.ofReal_le_ofReal hd
  · rintro _ ⟨Y, ⟨hYB, hn⟩, rfl⟩
    obtain ⟨X, hXA, hXn, hd⟩ := hBA Y hYB hn
    refine ⟨finiteRectMatrixHilbertEquiv r n n X, ⟨X, ⟨hXA, hXn⟩, rfl⟩, ?_⟩
    rw [edist_dist, matrixHSUnitBall_dist]
    exact ENNReal.ofReal_le_ofReal hd

theorem matrixHSUnitBallHausdorff_le (r : Nat) [NeZero r]
    (A B : StarSubalgebra ℂ (CMatrix n)) {ε : ℝ} (hε : 0 ≤ ε)
    (hAB : ∀ X ∈ A, matrixOpNorm X ≤ 1 →
      ∃ Y ∈ B, matrixOpNorm Y ≤ 1 ∧ rectHSNorm r (X - Y) ≤ ε)
    (hBA : ∀ Y ∈ B, matrixOpNorm Y ≤ 1 →
      ∃ X ∈ A, matrixOpNorm X ≤ 1 ∧ rectHSNorm r (Y - X) ≤ ε) :
    matrixHSUnitBallHausdorff r A B ≤ ε :=
  ENNReal.toReal_le_of_le_ofReal hε (matrixHSUnitBall_hausdorffEDist_le r A B hAB hBA)

theorem matrixCommonCompression_hausdorffEDist_bound (r : Nat) [NeZero r]
    (A B : StarSubalgebra ℂ (CMatrix n)) (P : CMatrix n) (hP : IsStarProjection P)
    (hAB : ∀ X ∈ A, P * X * P ∈ B) (hBA : ∀ Y ∈ B, P * Y * P ∈ A) :
    Metric.hausdorffEDist (matrixHSUnitBall r A) (matrixHSUnitBall r B) ≤
      ENNReal.ofReal (Real.sqrt (2 * matrixTraceReal r (1 - P))) := by
  apply matrixHSUnitBall_hausdorffEDist_le r A B
  · intro X hX hn
    exact ⟨P * X * P, hAB X hX, (matrixProjection_compression_opNorm_le P X hP).trans hn,
      rectHSNorm_projection_compression_loss r P X hP hn⟩
  · intro Y hY hn
    exact ⟨P * Y * P, hBA Y hY, (matrixProjection_compression_opNorm_le P Y hP).trans hn,
      rectHSNorm_projection_compression_loss r P Y hP hn⟩

theorem matrixCommonCompression_hausdorff_bound (r : Nat) [NeZero r]
    (A B : StarSubalgebra ℂ (CMatrix n)) (P : CMatrix n) (hP : IsStarProjection P)
    (hAB : ∀ X ∈ A, P * X * P ∈ B) (hBA : ∀ Y ∈ B, P * Y * P ∈ A) :
    matrixHSUnitBallHausdorff r A B ≤ Real.sqrt (2 * matrixTraceReal r (1 - P)) := by
  apply matrixHSUnitBallHausdorff_le r A B (Real.sqrt_nonneg _)
  · intro X hX hn
    exact ⟨P * X * P, hAB X hX, (matrixProjection_compression_opNorm_le P X hP).trans hn,
      rectHSNorm_projection_compression_loss r P X hP hn⟩
  · intro Y hY hn
    exact ⟨P * Y * P, hBA Y hY, (matrixProjection_compression_opNorm_le P Y hP).trans hn,
      rectHSNorm_projection_compression_loss r P Y hP hn⟩

end ThomGame.Analysis
