module

public import ThomGame.Analysis.MatrixUnitSpanAlgebra

/-!
# Rectangular slices of the actual matrix-unit span
-/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat} {μ : Type*}

theorem matrixUnitSpan_compression_mem_line (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j)
    (i j : μ) {X : CMatrix d} (hX : X ∈ matrixUnitSpan W) :
    E i * X * E j ∈ ℂ ∙ W i j := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hX
  · rintro Z ⟨⟨k, l⟩, rfl⟩
    change E i * W k l * E j ∈ ℂ ∙ W i j
    by_cases hik : i = k
    · subst k
      rw [(hsupport i l).1]
      by_cases hlj : l = j
      · subst l
        rw [(hsupport i j).2]
        exact Submodule.mem_span_singleton_self (W i j)
      · have hz : W i l * E j = 0 := by
          calc
            W i l * E j = (W i l * E l) * E j := by rw [(hsupport i l).2]
            _ = 0 := by rw [mul_assoc, horth hlj, mul_zero]
        rw [hz]
        exact (ℂ ∙ W i j).zero_mem
    · have hz : E i * W k l = 0 := by
        calc
          E i * W k l = E i * (E k * W k l) := by rw [(hsupport k l).1]
          _ = 0 := by rw [← mul_assoc, horth hik, zero_mul]
      rw [hz, zero_mul]
      exact (ℂ ∙ W i j).zero_mem
  · simpa only [mul_zero, zero_mul] using (ℂ ∙ W i j).zero_mem
  · intro A B _ _ hA hB
    rw [mul_add, add_mul]
    exact (ℂ ∙ W i j).add_mem hA hB
  · intro c A _ hA
    rw [mul_smul_comm, smul_mul_assoc]
    exact (ℂ ∙ W i j).smul_mem c hA

theorem matrixUnitSpan_rectangle_eq_line (E : μ → CMatrix d) (W : μ → μ → CMatrix d)
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hsupport : ∀ i j, E i * W i j = W i j ∧ W i j * E j = W i j)
    (i j : μ) : matrixUnitSpan W ⊓ matrixRectangleSubmodule (E i) (E j) = ℂ ∙ W i j := by
  apply le_antisymm
  · intro X hX
    have h := matrixUnitSpan_compression_mem_line E W horth hsupport i j hX.1
    simpa only [hX.2.1, hX.2.2] using h
  · apply (Submodule.span_singleton_le_iff_mem (W i j) _).mpr
    exact ⟨matrixUnitSpan_unit_mem W i j, hsupport i j⟩

end ThomGame.Analysis
