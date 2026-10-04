module

public import ThomGame.Analysis.UniformMatrixMapOperators
public import ThomGame.Analysis.PositiveOperatorEstimates

/-!
# Coordinate quadratic forms determine order of the induced Hilbert map

Nonnegative complex quadratic forms pass to the actual trace ultralimit
and then to all vectors by density. Thus coordinate Hilbert positivity
and the bound by the identity hold for the entire induced operator.
-/

@[expose] public section
namespace ThomGame.Analysis.UniformMatrixMap

open Filter
open scoped ComplexOrder

variable {ι : Type*} {dims : ι → Nat} (F : UniformMatrixMap dims)
  (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem hilbertMap_nonneg_of_trace_positive
    (hp : ∀ i (X : CMatrix (dims i)), 0 ≤ normalizedTrace (star (F.toLinearMap i X) * X)) :
    0 ≤ F.hilbertMap hd U := by
  have hq (ξ : MatrixTraceHilbert dims hd U) : 0 ≤ inner ℂ (F.hilbertMap hd U ξ) ξ := by
    refine (matrixHilbertEmbedding_dense dims hd U).induction_on ξ ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro x
      rw [hilbertMap_embedding, matrixHilbertEmbedding_inner]
      obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
      rw [quotientMap_mk, matrixQuotientMk_star, ← map_mul, matrixUltratrace_mk]
      apply ge_of_tendsto' (matrixSequenceUltratrace_tendsto dims hd U (star (F.sequenceMap A) * A))
      intro i
      exact hp i (A.val i)
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro ξ
  simp only [RCLike.re_to_complex]
  have hz := Complex.nonneg_iff.mp (hq ξ)
  exact ⟨Complex.ext rfl hz.2, hz.1⟩

theorem hilbertMap_le_one_of_trace_defect_positive
    (hp : ∀ i (X : CMatrix (dims i)), 0 ≤ normalizedTrace (star (X - F.toLinearMap i X) * X)) :
    F.hilbertMap hd U ≤ 1 := by
  have hq (ξ : MatrixTraceHilbert dims hd U) : 0 ≤ inner ℂ (ξ - F.hilbertMap hd U ξ) ξ := by
    refine (matrixHilbertEmbedding_dense dims hd U).induction_on ξ ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro x
      rw [hilbertMap_embedding, ← map_sub, matrixHilbertEmbedding_inner]
      obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
      rw [quotientMap_mk, ← map_sub, matrixQuotientMk_star, ← map_mul, matrixUltratrace_mk]
      apply ge_of_tendsto' (matrixSequenceUltratrace_tendsto dims hd U (star (A - F.sequenceMap A) * A))
      intro i
      exact hp i (A.val i)
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex]
  intro ξ
  simp only [RCLike.re_to_complex]
  have hz := Complex.nonneg_iff.mp (hq ξ)
  exact ⟨Complex.ext rfl hz.2, hz.1⟩

end ThomGame.Analysis.UniformMatrixMap
