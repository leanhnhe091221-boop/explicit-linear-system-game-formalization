module

public import ThomGame.Analysis.MatrixInternalNormLift
public import ThomGame.Analysis.MatrixFiniteTraceGeometry
public import ThomGame.Analysis.MatrixBoundedWOTBall

/-!
# Internal trace approximation of weak operator limits

Weak operator convergence gives weak convergence at the identity vector.
The internal vector image is convex, so Hahn--Banach identifies its weak
and norm closures. Real parts and functional calculus inside the internal
product then give bounded internal approximations of self-adjoint limits.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat)
  (S : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))
  (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

noncomputable def matrixInternalWOTAlgebra :
    StarSubalgebra ℂ (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) :=
  StarSubalgebra.map (matrixLeftWOTRepresentation dims hd U)
    (matrixInternalQuotient dims S (U : Filter ι))

theorem matrixInternalWOTAlgebra_le : matrixInternalWOTAlgebra dims S hd U ≤ matrixWOTAlgebra dims hd U := by
  rintro T ⟨x, _, rfl⟩
  exact matrixLeftWOTRepresentation_mem dims hd U x

theorem matrixInternalWOTAlgebra_closure_le :
    (matrixInternalWOTAlgebra dims S hd U).topologicalClosure ≤ matrixWOTAlgebra dims hd U :=
  StarSubalgebra.topologicalClosure_minimal (matrixInternalWOTAlgebra_le dims S hd U)
    (matrixWOTAlgebra_isClosed dims hd U)

noncomputable def matrixInternalTraceVectors : Set (MatrixTraceHilbert dims hd U) :=
  Set.range (fun p : MatrixInternalProduct dims S hd =>
    matrixHilbertEmbedding dims hd U (matrixInternalProductToQuotient dims S hd (U : Filter ι) p))

theorem matrixInternalProduct_vector (p : MatrixInternalProduct dims S hd) :
    matrixFiniteVector dims hd U (matrixInternalProductToFinite dims S hd U p) =
      matrixHilbertEmbedding dims hd U (matrixInternalProductToQuotient dims S hd (U : Filter ι) p) :=
  matrixFiniteVector_embedding dims hd U _

theorem matrixInternalTraceVectors_convex : Convex ℝ (matrixInternalTraceVectors dims S hd U) := by
  rintro x ⟨p, rfl⟩ y ⟨q, rfl⟩ a b _ _ _
  refine ⟨(a : ℂ) • p + (b : ℂ) • q, ?_⟩
  simp only [map_add, map_smul]
  simp only [Complex.coe_smul]

theorem matrixInternalWOT_vector_mem_closure
    (T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U)
    (hT : T ∈ (matrixInternalWOTAlgebra dims S hd U).topologicalClosure) :
    T (matrixHilbertEmbedding dims hd U 1) ∈ closure (matrixInternalTraceVectors dims S hd U) := by
  have hw : toWeakSpace ℂ (MatrixTraceHilbert dims hd U) (T (matrixHilbertEmbedding dims hd U 1)) ∈
      closure (toWeakSpace ℂ (MatrixTraceHilbert dims hd U) '' matrixInternalTraceVectors dims S hd U) := by
    apply map_mem_closure (matrixWOT_apply_weak_continuous dims hd U (matrixHilbertEmbedding dims hd U 1)) hT
    rintro R ⟨x, hx, rfl⟩
    rw [← matrixInternalProductToQuotient_range dims S hd (U : Filter ι)] at hx
    obtain ⟨p, rfl⟩ := hx
    change toWeakSpace ℂ (MatrixTraceHilbert dims hd U)
      ((matrixLeftWOTRepresentation dims hd U
        (matrixInternalProductToQuotient dims S hd (U : Filter ι) p))
        (matrixHilbertEmbedding dims hd U 1)) ∈ _
    rw [matrixLeftWOTRepresentation_apply, matrixLeftRepresentation_apply, mul_one]
    exact ⟨_, ⟨p, rfl⟩, rfl⟩
  rw [← (matrixInternalTraceVectors_convex dims S hd U).toWeakSpace_closure ℂ] at hw
  obtain ⟨v, hv, heq⟩ := hw
  exact (toWeakSpace ℂ (MatrixTraceHilbert dims hd U)).injective heq ▸ hv

theorem matrixInternal_selfAdjoint_bounded_trace_approximation
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsSelfAdjoint T)
    (hmem : ContinuousLinearMapWOT.ofCLM T.val ∈ (matrixInternalWOTAlgebra dims S hd U).topologicalClosure)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖T‖ ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : BoundedMatrixSequence dims, (∀ i, B.val i ∈ S i) ∧ IsSelfAdjoint B ∧
      (∀ i, matrixOpNorm (B.val i) ≤ K) ∧
      dist (matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) B))
        (matrixFiniteVector dims hd U T) < ε := by
  have hv : matrixFiniteVector dims hd U T ∈ closure (matrixInternalTraceVectors dims S hd U) :=
    matrixInternalWOT_vector_mem_closure dims S hd U _ hmem
  obtain ⟨v, ⟨p, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp hv ε hε
  let φ := matrixInternalProductToFinite dims S hd U
  let a : MatrixInternalProduct dims S hd := realPart p
  let b := cstarNormClamp K a
  let B := matrixInternalProductToSequences dims S hd b
  have ha : IsSelfAdjoint a := (realPart p).property
  have hclip : matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) B) =
      cstarNormClamp K (realPart (φ p) : MatrixFiniteOperatorAlgebra dims hd U) := by
    change φ (cstarNormClamp K a) = _
    rw [map_cstarNormClamp φ K a ha]
    congr 1
    exact map_realPart φ p
  refine ⟨B, matrixInternalProductToSequences_mem dims S hd b,
    (cstarNormClamp_selfAdjoint K a).map (matrixInternalProductToSequences dims S hd), ?_, ?_⟩
  · intro i
    exact (matrixInternalProductToSequences_norm_le dims S hd b i).trans (cstarNormClamp_norm_le K hK a)
  · have hc := matrixFiniteVector_clamp_dist_le dims hd U K hK (realPart (φ p)) T
      (realPart (φ p)).property hT hbound
    have hr := matrixFiniteVector_realPart_dist_le dims hd U (φ p) T hT
    rw [← hclip, matrixFiniteVector_embedding] at hc
    refine (hc.trans hr).trans_lt ?_
    change dist (matrixFiniteVector dims hd U (matrixInternalProductToFinite dims S hd U p)) _ < ε
    rw [matrixInternalProduct_vector]
    simpa only [dist_comm] using hdist

end ThomGame.Analysis
