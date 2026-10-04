module

public import ThomGame.Analysis.MatrixCornerMarkovDecay
public import ThomGame.Analysis.MatrixPinchingRounding
public import ThomGame.Analysis.MatrixPinchingPythagoras
public import ThomGame.Analysis.MatrixResolventDissipation

/-!
# Scalar Poincare inequality on the full block diagonal algebra

Orthogonality sums the corner gaps without a factor depending on the
number or sizes of the blocks.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {d h : Nat} {μ : Type*} [Fintype μ]

theorem matrixCoordinateEnergy_corner_sum (U : Fin h → UnitaryMatrix d) (E X : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hred : ∀ i j, Commute (E i) (U j).val) (hleft : ∀ i, E i * X i = X i) :
    matrixCoordinateEnergy U (∑ i, X i) = ∑ i, matrixCoordinateEnergy U (X i) := by
  have hj (j : Fin h) : hsNorm ((U j).val * (∑ i, X i) - (∑ i, X i) * (U j).val) ^ 2 =
      ∑ i, hsNorm ((U j).val * X i - X i * (U j).val) ^ 2 := by
    rw [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
    have he := rectHSNorm_corner_sum_sq d E (fun i => (U j).val * X i - X i * (U j).val) hE horth (by
      intro i
      rw [Matrix.mul_sub, ← Matrix.mul_assoc (E i) (U j).val, (hred i j).eq,
        Matrix.mul_assoc (U j).val (E i), hleft, ← Matrix.mul_assoc (E i) (X i), hleft])
    simpa only [rectHSNorm_eq_hsNorm] using he
  simp only [matrixCoordinateEnergy, hj, ← Finset.mul_sum]
  rw [Finset.sum_comm]

omit [Fintype μ] in
theorem MatrixScalarGapPartition.corner_sum_eq {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (X : CMatrix d) (hX : X ∈ matrixPartitionBlockAlgebra Q.E) :
    (∑ i, Q.E i * X * Q.E i) = X :=
  matrixBlockPinch_eq_of_commute Q.E Q.projection Q.sum_one X
    ((mem_matrixPartitionBlockAlgebra_iff Q.E Q.projection X).mp hX)

omit [Fintype μ] in
theorem MatrixScalarGapPartition.corner_center_sum {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (X : CMatrix d) (hX : X ∈ matrixPartitionBlockAlgebra Q.E) :
    (∑ i, matrixCornerCenter (Q.E i) (Q.E i * X * Q.E i)) = X - matrixPartitionScalarExpectation Q.E X := by
  simp only [matrixCornerCenter, Finset.sum_sub_distrib,
    normalizedTrace_projection_sandwich (Q.projection _).isIdempotentElem.eq,
    Q.corner_sum_eq X hX, matrixPartitionScalarExpectation, matrixPartitionScalarSum]

omit [Fintype μ] in
theorem MatrixScalarGapPartition.block_scalar_gap [NeZero d] {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (hne : ∀ i, Q.E i ≠ 0)
    (X : CMatrix d) (hX : X ∈ matrixPartitionBlockAlgebra Q.E) :
    c * hsNorm (X - matrixPartitionScalarExpectation Q.E X) ^ 2 ≤ matrixCoordinateEnergy U X := by
  let Y := fun i => Q.E i * X * Q.E i
  have hleft (i : Fin Q.n) : Q.E i * Y i = Y i := by
    simp only [Y, ← Matrix.mul_assoc, (Q.projection i).isIdempotentElem.eq]
  have hright (i : Fin Q.n) : Y i * Q.E i = Y i := by
    simp only [Y, Matrix.mul_assoc, (Q.projection i).isIdempotentElem.eq]
  have hnorm : hsNorm (X - matrixPartitionScalarExpectation Q.E X) ^ 2 =
      ∑ i, hsNorm (matrixCornerCenter (Q.E i) (Y i)) ^ 2 := by
    rw [← Q.corner_center_sum X hX]
    exact (rectHSNorm_corner_sum_sq d Q.E _ Q.projection Q.orthogonal (fun i =>
      (matrixCornerCenter_support (Q.projection i) (Y i) (hleft i) (hright i)).1))
  rw [hnorm, Finset.mul_sum]
  calc
    _ ≤ ∑ i, matrixCoordinateEnergy U (Y i) := Finset.sum_le_sum (fun i _ =>
      Q.scalar_gap i (hne i) (Y i) (hleft i) (hright i))
    _ = matrixCoordinateEnergy U X := by
      rw [← matrixCoordinateEnergy_corner_sum U Q.E Y Q.projection Q.orthogonal Q.reducing hleft]
      exact congrArg (matrixCoordinateEnergy U) (Q.corner_sum_eq X hX)

end ThomGame.Analysis
