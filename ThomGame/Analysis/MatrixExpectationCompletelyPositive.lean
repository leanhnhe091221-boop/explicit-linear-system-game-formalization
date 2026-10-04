module

public import ThomGame.Analysis.MatrixAmplification
public import ThomGame.Analysis.MatrixKrausRepresentation

/-!
# Complete positivity of the actual trace conditional expectation

Entrywise expectation is the trace orthogonal projection onto the actual
amplified subalgebra. Positivity at every amplification follows without
an assumption about complete positivity or a chosen block decomposition.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d k : Nat} [NeZero d]

theorem matrixTraceProjection_amplified [NeZero k] (A : StarSubalgebra ℂ (CMatrix d))
    (X : CStarMatrix (Fin k) (Fin k) (CMatrix d)) :
    matrixTraceProjection (matrixAmplifiedSubalgebra A) (matrixBlockFlatten k d X) =
      matrixBlockFlatten k d (X.map (matrixTraceProjection A)) := by
  apply matrixTraceProjection_unique _ _ _
    (matrixBlockFlatten_mem_amplified A _ (fun i j => matrixTraceProjection_mem A (X i j)))
  intro Z hZ
  have hz : ∃ Y ∈ matrixBlockSubalgebra A, matrixBlockFlatten k d Y = Z := hZ
  obtain ⟨Y, hY, rfl⟩ := hz
  change normalizedTrace (star (matrixBlockFlatten k d Y) *
    (matrixBlockFlatten k d X - matrixBlockFlatten k d (X.map (matrixTraceProjection A)))) = 0
  rw [← map_sub, ← map_star, ← map_mul, matrixBlockFlatten_normalizedTrace]
  have he (i : Fin k) :
      normalizedTrace ((star Y * (X - X.map (matrixTraceProjection A))) i i) = 0 := by
    change normalizedTrace (∑ j, star (Y j i) * (X j i - matrixTraceProjection A (X j i))) = 0
    have hs : ∀ j : Fin k,
        normalizedTrace (star (Y j i) * (X j i - matrixTraceProjection A (X j i))) = 0 :=
      fun j => matrixTraceProjection_orthogonal A (X j i) (Y j i) (hY j i)
    simpa only [normalizedTrace, Matrix.trace_sum, Finset.sum_div] using Finset.sum_eq_zero
      (s := Finset.univ) (fun j _ => hs j)
  simp only [he, Finset.sum_const_zero, zero_div]

theorem matrixTraceProjection_amplification_nonneg (A : StarSubalgebra ℂ (CMatrix d))
    (k : Nat) (X : CStarMatrix (Fin k) (Fin k) (CMatrix d)) (hX : 0 ≤ X) :
    0 ≤ X.map (matrixTraceProjection A) := by
  by_cases hk : k = 0
  · subst k
    apply le_of_eq
    apply CStarMatrix.ext
    intro i
    exact Fin.elim0 i
  let : NeZero k := ⟨hk⟩
  have hp := matrixTraceProjection_nonneg (matrixAmplifiedSubalgebra A)
    (matrixBlockFlatten k d X) (map_nonneg (matrixBlockFlatten k d) hX)
  rw [matrixTraceProjection_amplified] at hp
  simpa only [StarAlgEquiv.symm_apply_apply] using map_nonneg (matrixBlockFlatten k d).symm hp

noncomputable def matrixConditionalExpectationCP (A : StarSubalgebra ℂ (CMatrix d)) :
    CMatrix d →CP CMatrix d where
  toLinearMap := matrixTraceProjection A
  map_cstarMatrix_nonneg' := matrixTraceProjection_amplification_nonneg A

@[simp] theorem matrixConditionalExpectationCP_apply (A : StarSubalgebra ℂ (CMatrix d))
    (X : CMatrix d) : matrixConditionalExpectationCP A X = matrixTraceProjection A X := rfl

theorem exists_matrixTraceProjection_kraus (A : StarSubalgebra ℂ (CMatrix d)) :
    ∃ a : Fin d × Fin d → CMatrix d,
      (∀ X, matrixTraceProjection A X = ∑ j, star (a j) * X * a j) ∧
      ∑ j, star (a j) * a j = 1 := by
  obtain ⟨a, ha⟩ := exists_matrix_kraus (matrixConditionalExpectationCP A)
  refine ⟨a, ha, ?_⟩
  simpa only [matrixConditionalExpectationCP_apply, matrixTraceProjection_one, mul_one] using
    (ha 1).symm

end ThomGame.Analysis
