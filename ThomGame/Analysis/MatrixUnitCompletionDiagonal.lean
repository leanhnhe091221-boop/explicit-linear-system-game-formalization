module

public import ThomGame.Analysis.MatrixUnitCompletionAlgebra

/-!
# The completed matrix-unit algebra contains the original scalar diagonal

This includes original blocks that were removed during spectral pruning.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} {μ : Type*} [Fintype μ] [DecidableEq μ]

omit [Fintype μ] in
theorem matrixUnitCompletionAlgebra_original_projection_mem (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (S : Finset μ) (o : S → S) (W : S → S → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i)
    (hsupport : ∀ i j, E i.val * W i j = W i j ∧ W i j * E j.val = W i j) (a : μ) :
    E a ∈ matrixUnitCompletionAlgebra o W hzero hmul hstar := by
  have hterm (i : S) : W i i * E a ∈ matrixUnitSpan W ∧ W i i * E a = E a * W i i := by
    by_cases hi : i.val = a
    · rw [← hi, (hsupport i i).1, (hsupport i i).2]
      exact ⟨matrixUnitSpan_unit_mem W i i, rfl⟩
    · have hz : W i i * E a = 0 := by
        calc
          W i i * E a = (W i i * E i.val) * E a := by rw [(hsupport i i).2]
          _ = 0 := by rw [mul_assoc, horth hi, mul_zero]
      have hz' : E a * W i i = 0 := by
        simpa only [star_mul, (hE a).isSelfAdjoint.star_eq, hstar i i, star_zero] using congrArg star hz
      rw [hz, hz']
      exact ⟨(matrixUnitSpan W).zero_mem, rfl⟩
  have hmem : (∑ i, W i i) * E a ∈ matrixUnitSpan W := by
    rw [Finset.sum_mul]
    exact (matrixUnitSpan W).sum_mem (fun i _ => (hterm i).1)
  have hcomm : Commute (∑ i, W i i) (E a) := by
    show (∑ i, W i i) * E a = E a * ∑ i, W i i
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (hterm i).2)
  exact matrixCornerCompletionAlgebra_mem_of_commute (matrixUnitSpanAlgebra o W hzero hmul hstar)
    (∑ i, W i i) (matrixUnitSpan_diagonal_projection o W hzero hmul hstar)
    (matrixUnitSpan_diagonal_sum_mem W) (fun _ hX => matrixUnitSpan_diagonal_identity o W hzero hmul hX)
      (E a) hcomm hmem

omit [Fintype μ] in
theorem matrixPartitionScalarAlgebra_le_unitCompletion (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (S : Finset μ) (o : S → S) (W : S → S → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i)
    (hsupport : ∀ i j, E i.val * W i j = W i j ∧ W i j * E j.val = W i j) :
    matrixPartitionScalarAlgebra E ≤ matrixUnitCompletionAlgebra o W hzero hmul hstar := by
  apply StarAlgebra.adjoin_le
  rintro X ⟨a, rfl⟩
  exact matrixUnitCompletionAlgebra_original_projection_mem E hE horth S o W hzero hmul hstar hsupport a

end ThomGame.Analysis
