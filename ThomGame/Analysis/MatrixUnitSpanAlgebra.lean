module

public import ThomGame.Analysis.MatrixALTPrunedMatrixUnits
public import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# The actual linear span algebra of a block matrix-unit family

The span is closed under multiplication and adjoint. No abstract
replacement algebra or extra closure assumption is introduced.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} {μ : Type*}

def matrixUnitSpan (W : μ → μ → CMatrix d) : Submodule ℂ (CMatrix d) :=
  Submodule.span ℂ (Set.range (fun ij : μ × μ => W ij.1 ij.2))

theorem matrixUnitSpan_unit_mem (W : μ → μ → CMatrix d) (i j : μ) : W i j ∈ matrixUnitSpan W :=
  Submodule.subset_span ⟨(i, j), rfl⟩

theorem matrixUnitSpan_mul [DecidableEq μ] (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    {X Y : CMatrix d} (hX : X ∈ matrixUnitSpan W) (hY : Y ∈ matrixUnitSpan W) :
    X * Y ∈ matrixUnitSpan W := by
  have hgen (i j : μ) : ∀ Y ∈ matrixUnitSpan W, W i j * Y ∈ matrixUnitSpan W := by
    intro Z hZ
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hZ
    · rintro Z ⟨⟨k, l⟩, rfl⟩
      by_cases hij : o i = o j
      · rw [hmul i j k l hij]
        split_ifs
        · exact matrixUnitSpan_unit_mem W i l
        · exact (matrixUnitSpan W).zero_mem
      · rw [hzero i j hij, zero_mul]
        exact (matrixUnitSpan W).zero_mem
    · simpa only [mul_zero] using (matrixUnitSpan W).zero_mem
    · intro A B _ _ hA hB
      rw [mul_add]
      exact (matrixUnitSpan W).add_mem hA hB
    · intro c A _ hA
      rw [mul_smul_comm]
      exact (matrixUnitSpan W).smul_mem c hA
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hX
  · rintro Z ⟨⟨i, j⟩, rfl⟩
    exact hgen i j Y hY
  · simpa only [zero_mul] using (matrixUnitSpan W).zero_mem
  · intro A B _ _ hA hB
    rw [add_mul]
    exact (matrixUnitSpan W).add_mem hA hB
  · intro c A _ hA
    rw [smul_mul_assoc]
    exact (matrixUnitSpan W).smul_mem c hA

theorem matrixUnitSpan_star (W : μ → μ → CMatrix d) (hstar : ∀ i j, star (W i j) = W j i)
    {X : CMatrix d} (hX : X ∈ matrixUnitSpan W) : star X ∈ matrixUnitSpan W := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hX
  · rintro Z ⟨⟨i, j⟩, rfl⟩
    rw [hstar i j]
    exact matrixUnitSpan_unit_mem W j i
  · simpa only [star_zero] using (matrixUnitSpan W).zero_mem
  · intro A B _ _ hA hB
    rw [star_add]
    exact (matrixUnitSpan W).add_mem hA hB
  · intro c A _ hA
    rw [star_smul]
    exact (matrixUnitSpan W).smul_mem (star c) hA

def matrixUnitSpanAlgebra [DecidableEq μ] (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i) : NonUnitalStarSubalgebra ℂ (CMatrix d) :=
  { matrixUnitSpan W with
    mul_mem' := matrixUnitSpan_mul o W hzero hmul
    star_mem' := matrixUnitSpan_star W hstar }

theorem mem_matrixUnitSpanAlgebra_iff [DecidableEq μ] (o : μ → μ) (W : μ → μ → CMatrix d)
    (hzero : ∀ i j, o i ≠ o j → W i j = 0)
    (hmul : ∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0)
    (hstar : ∀ i j, star (W i j) = W j i) (X : CMatrix d) :
    X ∈ matrixUnitSpanAlgebra o W hzero hmul hstar ↔ X ∈ matrixUnitSpan W := Iff.rfl

end ThomGame.Analysis
