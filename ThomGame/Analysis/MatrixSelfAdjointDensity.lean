module

public import ThomGame.Analysis.MatrixFiniteTraceGeometry
public import ThomGame.Analysis.MatrixNormControlledRepresentatives

/-!
# Bounded matrix approximation of self-adjoint elements in the WOT closure

Density of the original trace vectors, contraction of the self-adjoint
part, and trace-distance contraction of clipping produce actual matrix
representatives with a fixed operator bound approximating every bounded
self-adjoint element of the generated algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem matrixFinite_selfAdjoint_trace_approximation (T : MatrixFiniteOperatorAlgebra dims hd U)
    (hT : IsSelfAdjoint T) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : MatrixTracialQuotient dims (U : Filter ι), IsSelfAdjoint x ∧
      dist (matrixHilbertEmbedding dims hd U x) (matrixFiniteVector dims hd U T) < ε := by
  obtain ⟨x, hx⟩ := (matrixHilbertEmbedding_dense dims hd U).exists_dist_lt
    (matrixFiniteVector dims hd U T) hε
  refine ⟨realPart x, (realPart x).property, ?_⟩
  have h := matrixFiniteVector_realPart_dist_le dims hd U (matrixFiniteEmbedding dims hd U x) T hT
  rw [← map_realPart (matrixFiniteEmbedding dims hd U) x, matrixFiniteVector_embedding,
    matrixFiniteVector_embedding] at h
  exact h.trans_lt (by simpa only [dist_comm] using hx)

theorem matrixFinite_selfAdjoint_bounded_trace_approximation
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsSelfAdjoint T)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖T‖ ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : BoundedMatrixSequence dims, IsSelfAdjoint B ∧ (∀ i, matrixOpNorm (B.val i) ≤ K) ∧
      dist (matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) B))
        (matrixFiniteVector dims hd U T) < ε := by
  obtain ⟨x, hx, hdist⟩ := matrixFinite_selfAdjoint_trace_approximation dims hd U T hT ε hε
  obtain ⟨A, hAs, _, hAx⟩ := exists_matrixSelfAdjointRepresentative_bounded dims hd U x hx
    ‖matrixLeftRepresentation dims hd U x‖ (norm_nonneg _) le_rfl
  let p := (matrixOperatorProductEquiv dims hd).symm A
  have hp : IsSelfAdjoint p := hAs.map (matrixOperatorProductEquiv dims hd).symm
  let b := cstarNormClamp K p
  let B := matrixOperatorProductEquiv dims hd b
  have hB : IsSelfAdjoint B := (cstarNormClamp_selfAdjoint K p).map (matrixOperatorProductEquiv dims hd)
  have hb : ∀ i, matrixOpNorm (B.val i) ≤ K := fun i =>
    (matrixOperatorProduct_apply_norm_le dims hd b i).trans (cstarNormClamp_norm_le K hK p)
  have hpx : matrixProductToFinite dims hd U p = matrixFiniteEmbedding dims hd U x := by
    rw [matrixProductToFinite_apply, show matrixOperatorProductEquiv dims hd p = A from
      (matrixOperatorProductEquiv dims hd).apply_symm_apply A, hAx]
  have hclip : matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) B) =
      cstarNormClamp K (matrixFiniteEmbedding dims hd U x) := by
    change matrixProductToFinite dims hd U (cstarNormClamp K p) = _
    rw [map_cstarNormClamp _ K p hp, hpx]
  refine ⟨B, hB, hb, ?_⟩
  have hc := matrixFiniteVector_clamp_dist_le dims hd U K hK (matrixFiniteEmbedding dims hd U x) T
    (hx.map (matrixFiniteEmbedding dims hd U)) hT hbound
  rw [← hclip, matrixFiniteVector_embedding, matrixFiniteVector_embedding] at hc
  exact hc.trans_lt hdist

end ThomGame.Analysis
