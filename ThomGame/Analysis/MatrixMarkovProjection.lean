module

public import ThomGame.Analysis.InvariantMeanProjection
public import ThomGame.Analysis.MatrixMarkovCommutant
public import ThomGame.Analysis.MatrixBoundedTraceConvex

/-!
# The Markov fixed-space projection has bounded matrix representatives

The exact operator-bounded trace balls are invariant under the actual
Markov operator. Mean ergodic convergence and their closed convexity
keep the fixed-space projection in the same ball. Thus the projection
of every bounded trace vector is an actual bounded algebra element.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat) {h : Nat} [NeZero h]
  (U : (i : ι) → Fin h → UnitaryMatrix (dims i)) (hd : ∀ i, 0 < dims i) (L : Ultrafilter ι)

noncomputable def matrixMarkovProjection : MatrixTraceHilbert dims hd L →L[ℂ] MatrixTraceHilbert dims hd L :=
  meanProjection ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L)

theorem matrixMarkovProjection_norm_le : ‖matrixMarkovProjection dims U hd L‖ ≤ 1 :=
  meanProjection_norm_le _

theorem matrixMarkovProjection_fixed (ξ : MatrixTraceHilbert dims hd L) :
    (matrixUniformLazyMarkov dims U hd).hilbertMap hd L (matrixMarkovProjection dims U hd L ξ) =
      matrixMarkovProjection dims U hd L ξ := meanProjection_fixed _ ξ

theorem matrixMarkovProjection_eq_self_iff (ξ : MatrixTraceHilbert dims hd L) :
    matrixMarkovProjection dims U hd L ξ = ξ ↔ (matrixUniformLazyMarkov dims U hd).hilbertMap hd L ξ = ξ :=
  meanProjection_eq_self_iff _ ξ

theorem matrixLazyMarkov_mapsTo_boundedTraceBall (K : ℝ) :
    Set.MapsTo ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L)
      (matrixBoundedTraceBall dims hd L K) (matrixBoundedTraceBall dims hd L K) := by
  rintro ξ ⟨A, hA, rfl⟩
  refine ⟨(matrixUniformLazyMarkov dims U hd).sequenceMap A, ?_, ?_⟩
  · intro i
    change matrixOpNorm ((matrixUniformLazyMarkov dims U hd).toLinearMap i (A.val i)) ≤ K
    rw [matrixUniformLazyMarkov_apply]
    exact (matrixLazyMarkov_matrixOpNorm_le (U i) (A.val i)).trans (hA i)
  · rw [UniformMatrixMap.hilbertMap_embedding, UniformMatrixMap.quotientMap_mk]

section NatIndex

variable (dims : Nat → Nat) (U : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)

include hL in
theorem matrixMarkovProjection_mem_boundedTraceBall (K : ℝ) (hK : 0 ≤ K)
    (ξ : MatrixTraceHilbert dims hd L) (hξ : ξ ∈ matrixBoundedTraceBall dims hd L K) :
    matrixMarkovProjection dims U hd L ξ ∈ matrixBoundedTraceBall dims hd L K :=
  meanProjection_mem_invariant_closed_convex _
    (matrixUniformMarkovPower_hilbertNorm_le dims U hd (fun _ => 1) L)
    (matrixBoundedTraceBall dims hd L K) (matrixBoundedTraceBall_isClosed dims hd L hL K hK)
    (matrixBoundedTraceBall_convex dims hd L K) (matrixLazyMarkov_mapsTo_boundedTraceBall dims U hd L K) ξ hξ

include hL in
theorem exists_matrixMarkovProjection_representative (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ∃ B : BoundedMatrixSequence dims,
      (∀ n, matrixOpNorm (B.val n) ≤ ‖matrixLeftRepresentation dims hd L x‖) ∧
      matrixHilbertEmbedding dims hd L (matrixQuotientMk dims (L : Filter Nat) B) =
        matrixMarkovProjection dims U hd L (matrixHilbertEmbedding dims hd L x) := by
  obtain ⟨A, hA, hAx⟩ := exists_matrixRepresentative_bounded_exact dims hd L x _ (norm_nonneg _) le_rfl
  exact matrixMarkovProjection_mem_boundedTraceBall dims U hd L hL _ (norm_nonneg _)
    (matrixHilbertEmbedding dims hd L x) ⟨A, hA, congrArg (matrixHilbertEmbedding dims hd L) hAx⟩

include hL in
theorem exists_matrixMarkovProjection_element (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ∃ y : MatrixTracialQuotient dims (L : Filter Nat),
      matrixHilbertEmbedding dims hd L y = matrixMarkovProjection dims U hd L (matrixHilbertEmbedding dims hd L x) ∧
      matrixQuotientLazyMarkov dims U hd (L : Filter Nat) y = y ∧
      ‖matrixLeftRepresentation dims hd L y‖ ≤ ‖matrixLeftRepresentation dims hd L x‖ := by
  obtain ⟨B, hB, he⟩ := exists_matrixMarkovProjection_representative dims U hd L hL x
  refine ⟨matrixQuotientMk dims (L : Filter Nat) B, he, ?_, ?_⟩
  · apply matrixHilbertEmbedding_injective dims hd L
    change matrixHilbertEmbedding dims hd L ((matrixUniformLazyMarkov dims U hd).quotientMap (L : Filter Nat) _) = _
    rw [← UniformMatrixMap.hilbertMap_embedding, he]
    exact matrixMarkovProjection_fixed dims U hd L (matrixHilbertEmbedding dims hd L x)
  · exact matrixLeftRepresentation_norm_le dims hd L B _ (norm_nonneg _) hB

end NatIndex
end ThomGame.Analysis
