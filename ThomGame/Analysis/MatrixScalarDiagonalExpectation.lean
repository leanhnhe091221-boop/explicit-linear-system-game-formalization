module

public import ThomGame.Analysis.MatrixPartitionScalarAlgebra
public import ThomGame.Analysis.MatrixRankOneCorners
public import ThomGame.Analysis.MatrixConditionalExpectation
public import ThomGame.Analysis.MatrixProjectionExclusion

/-!
# Explicit scalar diagonal conditional expectation

The block trace formula is identified with the actual trace orthogonal
projection. Zero blocks are allowed, and all traces use the ambient
normalization throughout.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {d : Nat} {μ : Type*} [Fintype μ]

noncomputable def matrixPartitionScalarExpectation (E : μ → CMatrix d) (X : CMatrix d) : CMatrix d :=
  matrixPartitionScalarSum E (fun i => normalizedTrace (E i * X) / normalizedTrace (E i))

theorem matrixPartitionScalarExpectation_mem (E : μ → CMatrix d) (X : CMatrix d) :
    matrixPartitionScalarExpectation E X ∈ matrixPartitionScalarAlgebra E :=
  matrixPartitionScalarSum_mem E _

theorem matrixPartitionScalarExpectation_corner (E : μ → CMatrix d)
    (horth : Pairwise (fun i j => E i * E j = 0)) (i : μ) (X : CMatrix d) (hleft : E i * X = X) :
    matrixPartitionScalarExpectation E X = (normalizedTrace X / normalizedTrace (E i)) • E i := by
  classical
  unfold matrixPartitionScalarExpectation matrixPartitionScalarSum
  rw [Finset.sum_eq_single i]
  · dsimp only
    rw [hleft]
  · intro j _ hji
    have hz : E j * X = 0 := by
      calc
        _ = E j * (E i * X) := by rw [hleft]
        _ = 0 := by rw [← Matrix.mul_assoc, horth hji, Matrix.zero_mul]
    dsimp only
    rw [hz, normalizedTrace_zero, zero_div, zero_smul]
  · simp

variable [NeZero d]

theorem matrixPartitionScalarExpectation_block_pairing (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (X : CMatrix d) (i : μ) :
    normalizedTrace (E i * (X - matrixPartitionScalarExpectation E X)) = 0 := by
  by_cases hz : E i = 0
  · rw [hz, Matrix.zero_mul, normalizedTrace_zero]
  · rw [Matrix.mul_sub, normalizedTrace_sub, matrixPartitionScalarExpectation,
      matrixPartitionScalarSum_block_left E hE horth, normalizedTrace_smul,
      div_mul_cancel₀ _ (normalizedTrace_projection_ne_zero (hE i) hz), sub_self]

theorem matrixPartitionScalarExpectation_eq_traceProjection (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (X : CMatrix d) :
    matrixPartitionScalarExpectation E X = matrixTraceProjection (matrixPartitionScalarAlgebra E) X := by
  symm
  apply matrixTraceProjection_unique _ X _ (matrixPartitionScalarExpectation_mem E X)
  intro B hB
  obtain ⟨c, rfl⟩ := (mem_matrixPartitionScalarAlgebra_iff E hE horth hsum B).mp hB
  simp only [matrixPartitionScalarSum, star_sum, star_smul, fun i => (hE i).isSelfAdjoint.star_eq,
    Matrix.sum_mul, Matrix.smul_mul, normalizedTrace_sum, normalizedTrace_smul,
    matrixPartitionScalarExpectation_block_pairing E hE horth, mul_zero, Finset.sum_const_zero]

theorem matrixPartitionScalarExpectation_hsNorm_le (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (X : CMatrix d) :
    hsNorm (matrixPartitionScalarExpectation E X) ≤ hsNorm X := by
  rw [matrixPartitionScalarExpectation_eq_traceProjection E hE horth hsum]
  exact matrixTraceProjection_hsNorm_le _ X

theorem matrixPartitionScalarExpectation_matrixOpNorm_le (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (X : CMatrix d) :
    matrixOpNorm (matrixPartitionScalarExpectation E X) ≤ matrixOpNorm X := by
  rw [matrixPartitionScalarExpectation_eq_traceProjection E hE horth hsum]
  exact matrixTraceProjection_matrixOpNorm_le _ X

end ThomGame.Analysis
