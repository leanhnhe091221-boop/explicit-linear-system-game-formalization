module

public import ThomGame.Analysis.MatrixCornerComplementAlgebra

/-!
# The concrete completed algebra of an exact block matrix-unit family
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} {μ : Type*} [Fintype μ] [DecidableEq μ]

def matrixUnitCompletionAlgebra (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i) : StarSubalgebra ℂ (CMatrix d) :=
  matrixCornerCompletionAlgebra (matrixUnitSpanAlgebra o W hzero hmul hstar) (∑ i, W i i)
    (matrixUnitSpan_diagonal_projection o W hzero hmul hstar)
    (matrixUnitSpan_diagonal_sum_mem W)
    (fun _ hX => matrixUnitSpan_diagonal_identity o W hzero hmul hX)

theorem mem_matrixUnitCompletionAlgebra_iff (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i) (X : CMatrix d) :
    X ∈ matrixUnitCompletionAlgebra o W hzero hmul hstar ↔
      ∃ A ∈ matrixUnitSpan W, ∃ B : CMatrix d,
        ((1 - ∑ i, W i i) * B = B ∧ B * (1 - ∑ i, W i i) = B) ∧ A + B = X :=
  mem_matrixCornerCompletionAlgebra_iff _ _ _ _ _ X

theorem matrixUnitCompletionAlgebra_unit_mem (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i) (i j : μ) :
    W i j ∈ matrixUnitCompletionAlgebra o W hzero hmul hstar := by
  apply (mem_matrixUnitCompletionAlgebra_iff o W hzero hmul hstar (W i j)).mpr
  exact ⟨W i j, matrixUnitSpan_unit_mem W i j, 0, ⟨mul_zero _, zero_mul _⟩, add_zero _⟩

theorem matrixUnitCompletionAlgebra_complement_mem (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i) (X : CMatrix d) :
    (1 - ∑ i, W i i) * X * (1 - ∑ i, W i i) ∈ matrixUnitCompletionAlgebra o W hzero hmul hstar := by
  let R := 1 - ∑ i, W i i
  have hR : R * R = R := (matrixUnitSpan_diagonal_projection o W hzero hmul hstar).one_sub.isIdempotentElem.eq
  apply (mem_matrixUnitCompletionAlgebra_iff o W hzero hmul hstar _).mpr
  refine ⟨0, (matrixUnitSpan W).zero_mem, R * X * R, ⟨?_, ?_⟩, zero_add _⟩
  · change R * (R * X * R) = R * X * R
    rw [← mul_assoc R (R * X), ← mul_assoc R R X, hR]
  · change (R * X * R) * R = R * X * R
    rw [mul_assoc (R * X), hR]

end ThomGame.Analysis
