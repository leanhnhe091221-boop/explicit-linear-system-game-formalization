module

public import ThomGame.Analysis.UniformMatrixMaps
public import ThomGame.Analysis.MatrixExactNormRepresentatives
public import ThomGame.Analysis.MatrixTraceMetric
public import ThomGame.Analysis.MatrixFiniteTraceGeometry

/-!
# Operators induced by uniformly bounded matrix maps

The coordinate trace bound extends the quotient map to the trace Hilbert
completion. Exact bounded representatives give the operator norm bound
on the entire finite algebra and its operator-to-trace continuous map.
-/

@[expose] public section
namespace ThomGame.Analysis.UniformMatrixMap

open Filter
open scoped Topology

variable {ι : Type*} {dims : ι → Nat} (F : UniformMatrixMap dims)
  (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem traceSpace_norm_le (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixTraceSpaceEquiv dims hd U (F.quotientMap (U : Filter ι) x)‖ ≤
      F.hilbertBound * ‖matrixTraceSpaceEquiv dims hd U x‖ := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  exact le_of_tendsto_of_tendsto'
    (matrixTraceSpace_norm_tendsto dims hd U (F.sequenceMap A))
    ((matrixTraceSpace_norm_tendsto dims hd U A).const_mul (F.hilbertBound : ℝ))
    (fun i => F.hilbert_le i (A.val i))

noncomputable def traceSpaceMap : MatrixTraceSpace dims hd U →L[ℂ] MatrixTraceSpace dims hd U :=
  ((matrixTraceSpaceEquiv dims hd U).toLinearMap.comp
    ((F.quotientMap (U : Filter ι)).comp (matrixTraceSpaceEquiv dims hd U).symm.toLinearMap)).mkContinuous
      F.hilbertBound (fun x => by
        obtain ⟨y, rfl⟩ := (matrixTraceSpaceEquiv dims hd U).surjective x
        exact F.traceSpace_norm_le hd U y)

noncomputable def hilbertMap : MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U :=
  (F.traceSpaceMap hd U).completion

@[simp] theorem hilbertMap_embedding (x : MatrixTracialQuotient dims (U : Filter ι)) :
    F.hilbertMap hd U (matrixHilbertEmbedding dims hd U x) =
      matrixHilbertEmbedding dims hd U (F.quotientMap (U : Filter ι) x) :=
  ContinuousLinearMap.completion_apply_coe (F.traceSpaceMap hd U) (matrixTraceSpaceEquiv dims hd U x)

theorem hilbertMap_norm_le : ‖F.hilbertMap hd U‖ ≤ F.hilbertBound := by
  apply ContinuousLinearMap.opNorm_le_bound _ F.hilbertBound.2
  intro ξ
  refine (matrixHilbertEmbedding_dense dims hd U).induction_on ξ ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro x
    rw [hilbertMap_embedding, matrixHilbertEmbedding_norm, matrixHilbertEmbedding_norm]
    exact F.traceSpace_norm_le hd U x

section NatIndex

variable {dims : Nat → Nat} (F : UniformMatrixMap dims)
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop)

noncomputable def finiteMap : MatrixFiniteOperatorAlgebra dims hd U →ₗ[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  (matrixFiniteEmbedding dims hd U).toAlgHom.toLinearMap.comp
    ((F.quotientMap (U : Filter Nat)).comp
      (matrixFiniteEquiv dims hd U hU).symm.toAlgEquiv.toLinearEquiv.toLinearMap)

@[simp] theorem finiteMap_embedding (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    F.finiteMap hd U hU (matrixFiniteEmbedding dims hd U x) =
      matrixFiniteEmbedding dims hd U (F.quotientMap (U : Filter Nat) x) := by
  change matrixFiniteEmbedding dims hd U
    (F.quotientMap (U : Filter Nat) ((matrixFiniteEquiv dims hd U hU).symm (matrixFiniteEquiv dims hd U hU x))) = _
  rw [(matrixFiniteEquiv dims hd U hU).symm_apply_apply]

theorem finiteMap_norm_le (T : MatrixFiniteOperatorAlgebra dims hd U) :
    ‖F.finiteMap hd U hU T‖ ≤ F.operatorBound * ‖T‖ := by
  obtain ⟨A, hA, hAT⟩ := exists_matrixFiniteRepresentative_bounded dims hd U hU T ‖T‖ (norm_nonneg _) le_rfl
  have he : F.finiteMap hd U hU T =
      matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) (F.sequenceMap A)) := by
    rw [← hAT, finiteMap_embedding, quotientMap_mk]
  rw [he, matrixFiniteEmbedding_norm]
  exact matrixLeftRepresentation_norm_le dims hd U (F.sequenceMap A) _
    (mul_nonneg F.operatorBound.2 (norm_nonneg _)) (fun i =>
      (F.operator_le i (A.val i)).trans (mul_le_mul_of_nonneg_left (hA i) F.operatorBound.2))

noncomputable def finiteCLM : MatrixFiniteOperatorAlgebra dims hd U →L[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  (F.finiteMap hd U hU).mkContinuous F.operatorBound (F.finiteMap_norm_le hd U hU)

noncomputable def finiteToHilbert : MatrixFiniteOperatorAlgebra dims hd U →L[ℂ] MatrixTraceHilbert dims hd U :=
  ((matrixFiniteVector dims hd U).comp (F.finiteMap hd U hU)).mkContinuous F.operatorBound (by
    intro T
    change ‖(F.finiteMap hd U hU T).val (matrixHilbertEmbedding dims hd U 1)‖ ≤ _
    exact ((F.finiteMap hd U hU T).val.le_opNorm _).trans (by
      rw [matrixUnitVector_norm, mul_one]
      exact F.finiteMap_norm_le hd U hU T))

@[simp] theorem finiteToHilbert_apply (T : MatrixFiniteOperatorAlgebra dims hd U) :
    F.finiteToHilbert hd U hU T = matrixFiniteVector dims hd U (F.finiteMap hd U hU T) := rfl

@[simp] theorem finiteToHilbert_embedding (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    F.finiteToHilbert hd U hU (matrixFiniteEmbedding dims hd U x) =
      matrixHilbertEmbedding dims hd U (F.quotientMap (U : Filter Nat) x) := by
  rw [finiteToHilbert_apply, finiteMap_embedding, matrixFiniteVector_embedding]

theorem finiteToHilbert_vector (T : MatrixFiniteOperatorAlgebra dims hd U) :
    F.finiteToHilbert hd U hU T = F.hilbertMap hd U (matrixFiniteVector dims hd U T) := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [finiteToHilbert_embedding, matrixFiniteVector_embedding, hilbertMap_embedding]

theorem sub_finiteToHilbert (G : UniformMatrixMap dims) :
    (F.sub G).finiteToHilbert hd U hU = F.finiteToHilbert hd U hU - G.finiteToHilbert hd U hU := by
  ext T
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  simp only [finiteToHilbert_embedding, sub_quotientMap, map_sub, _root_.sub_apply]

end NatIndex
end ThomGame.Analysis.UniformMatrixMap
