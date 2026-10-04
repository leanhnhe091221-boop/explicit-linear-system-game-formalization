module

public import ThomGame.Analysis.MatrixUnitSpanAlgebra

/-!
# The actual support identity of the matrix-unit span

The sum of the diagonal units is a projection and is a two-sided
identity on the entire span.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} {μ : Type*} [Fintype μ] [DecidableEq μ]

omit [DecidableEq μ] in
theorem matrixUnitSpan_diagonal_sum_mem (W : μ → μ → CMatrix d) :
    (∑ i, W i i) ∈ matrixUnitSpan W := by
  exact (matrixUnitSpan W).sum_mem (fun i _ => matrixUnitSpan_unit_mem W i i)

theorem matrixUnitSpan_diagonal_identity (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    {X : CMatrix d} (hX : X ∈ matrixUnitSpan W) :
    (∑ i, W i i) * X = X ∧ X * (∑ i, W i i) = X := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hX
  · rintro Z ⟨⟨i, j⟩, rfl⟩
    change (∑ k, W k k) * W i j = W i j ∧ W i j * (∑ k, W k k) = W i j
    constructor
    · rw [Finset.sum_mul]
      simp only [fun k => hmul k k i j rfl]
      simp
    · by_cases hij : o i = o j
      · rw [Finset.mul_sum]
        simp only [fun k => hmul i j k k hij]
        simp
      · rw [hzero i j hij, zero_mul]
  · simp only [mul_zero, zero_mul, and_self]
  · intro A B _ _ hA hB
    constructor
    · rw [mul_add, hA.1, hB.1]
    · rw [add_mul, hA.2, hB.2]
  · intro c A _ hA
    constructor
    · rw [mul_smul_comm, hA.1]
    · rw [smul_mul_assoc, hA.2]

theorem matrixUnitSpan_diagonal_projection (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i) : IsStarProjection (∑ i, W i i) := by
  refine ⟨(matrixUnitSpan_diagonal_identity o W hzero hmul (matrixUnitSpan_diagonal_sum_mem W)).1, ?_⟩
  change star (∑ i, W i i) = ∑ i, W i i
  simp only [star_sum, fun i => hstar i i]

end ThomGame.Analysis
