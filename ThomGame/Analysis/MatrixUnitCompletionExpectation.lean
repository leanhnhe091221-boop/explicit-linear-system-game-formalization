module

public import ThomGame.Analysis.MatrixUnitCompletionAlgebra
public import ThomGame.Analysis.MatrixCornerCompletionExpectation

/-!
# Exact trace expectation onto the constructed matrix-unit completion
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ] [DecidableEq μ]

theorem matrixUnitCompletionAlgebra_expectation (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i) (X : CMatrix d) :
    matrixTraceProjection (matrixUnitCompletionAlgebra o W hzero hmul hstar) X =
      matrixSubmoduleTraceProjection (matrixUnitSpan W) X + (1 - ∑ i, W i i) * X * (1 - ∑ i, W i i) :=
  matrixCornerCompletion_expectation (matrixUnitSpanAlgebra o W hzero hmul hstar) (∑ i, W i i)
    (matrixUnitSpan_diagonal_projection o W hzero hmul hstar) (matrixUnitSpan_diagonal_sum_mem W)
    (fun _ hX => matrixUnitSpan_diagonal_identity o W hzero hmul hX) X

end ThomGame.Analysis
