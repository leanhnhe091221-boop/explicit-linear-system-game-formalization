module

public import ThomGame.Analysis.MatrixInternalSequences

/-!
# Norm-controlled representatives in coordinate subalgebras

Functional calculus is performed inside the closed internal product, so
clipping retains every coordinate constraint as well as the quotient class.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat)
  (S : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))
  (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

noncomputable def matrixInternalProductToFinite :
    MatrixInternalProduct dims S hd →⋆ₐ[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  (matrixFiniteEmbedding dims hd U).comp
    (matrixInternalProductToQuotient dims S hd (U : Filter ι))

theorem matrixInternalProductToFinite_apply (A : MatrixInternalProduct dims S hd) :
    matrixInternalProductToFinite dims S hd U A = matrixFiniteEmbedding dims hd U
      (matrixQuotientMk dims (U : Filter ι) (matrixInternalProductToSequences dims S hd A)) := rfl

theorem exists_matrixInternalRepresentative_bounded
    (x : MatrixTracialQuotient dims (U : Filter ι))
    (hx : x ∈ matrixInternalQuotient dims S (U : Filter ι))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖matrixLeftRepresentation dims hd U x‖ ≤ K) :
    ∃ B : BoundedMatrixSequence dims, (∀ i, B.val i ∈ S i) ∧
      (∀ i, matrixOpNorm (B.val i) ≤ 2 * K) ∧ matrixQuotientMk dims (U : Filter ι) B = x := by
  rw [← matrixInternalProductToQuotient_range dims S hd (U : Filter ι)] at hx
  obtain ⟨p, hp⟩ := hx
  have hpx : matrixInternalProductToFinite dims S hd U p = matrixFiniteEmbedding dims hd U x :=
    congrArg (matrixFiniteEmbedding dims hd U) hp
  obtain ⟨b, hb, heq⟩ := exists_cstar_norm_lift (matrixInternalProductToFinite dims S hd U) p K hK
    (by rw [hpx, matrixFiniteEmbedding_norm]; exact hbound)
  refine ⟨matrixInternalProductToSequences dims S hd b,
    matrixInternalProductToSequences_mem dims S hd b, ?_, ?_⟩
  · intro i
    exact (matrixInternalProductToSequences_norm_le dims S hd b i).trans hb
  · apply matrixFiniteEmbedding_injective dims hd U
    exact heq.trans hpx

theorem exists_matrixInternalSelfAdjointRepresentative_bounded
    (x : MatrixTracialQuotient dims (U : Filter ι))
    (hx : x ∈ matrixInternalQuotient dims S (U : Filter ι)) (hxs : IsSelfAdjoint x)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖matrixLeftRepresentation dims hd U x‖ ≤ K) :
    ∃ B : BoundedMatrixSequence dims, (∀ i, B.val i ∈ S i) ∧ IsSelfAdjoint B ∧
      (∀ i, matrixOpNorm (B.val i) ≤ K) ∧ matrixQuotientMk dims (U : Filter ι) B = x := by
  rw [← matrixInternalProductToQuotient_range dims S hd (U : Filter ι)] at hx
  obtain ⟨p, hp⟩ := hx
  let φ := matrixInternalProductToFinite dims S hd U
  have hpx : φ p = matrixFiniteEmbedding dims hd U x :=
    congrArg (matrixFiniteEmbedding dims hd U) hp
  have hreal : φ (realPart p : MatrixInternalProduct dims S hd) = matrixFiniteEmbedding dims hd U x := by
    rw [map_realPart, hpx, (hxs.map (matrixFiniteEmbedding dims hd U)).coe_realPart]
  obtain ⟨b, hbs, hb, heq⟩ := exists_selfAdjoint_norm_lift φ (realPart p) (realPart p).property K hK
    (by rw [hreal, matrixFiniteEmbedding_norm]; exact hbound)
  refine ⟨matrixInternalProductToSequences dims S hd b,
    matrixInternalProductToSequences_mem dims S hd b,
    hbs.map (matrixInternalProductToSequences dims S hd), ?_, ?_⟩
  · intro i
    exact (matrixInternalProductToSequences_norm_le dims S hd b i).trans hb
  · apply matrixFiniteEmbedding_injective dims hd U
    exact heq.trans hreal

end ThomGame.Analysis
