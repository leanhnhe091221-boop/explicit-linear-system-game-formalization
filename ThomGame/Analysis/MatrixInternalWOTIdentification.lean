module

public import ThomGame.Analysis.MatrixInternalTraceDensity
public import ThomGame.Analysis.MatrixRestrictedTraceSet

/-!
# Internal matrix subalgebras are weak operator closed

For natural number indices and an ultrafilter finer than `atTop`, the
bounded internal approximations have an internal diagonal representative.
The separating identity vector identifies its operator with the limit.
The conclusion concerns the actual image of the coordinate subalgebras,
without assuming that their vectors are dense in the whole trace Hilbert space.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat)
  (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

theorem matrixInternal_selfAdjoint_vector_mem_traceBall (hU : (U : Filter Nat) ≤ atTop)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsSelfAdjoint T)
    (hmem : ContinuousLinearMapWOT.ofCLM T.val ∈ (matrixInternalWOTAlgebra dims S hd U).topologicalClosure)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖T‖ ≤ K) :
    matrixFiniteVector dims hd U T ∈
      matrixRestrictedTraceSet dims hd U (fun n => (S n : Set (CMatrix (dims n)))) K := by
  rw [← (matrixInternalTraceBall_isClosed dims hd U hU S K hK).closure_eq]
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨B, hS, _, hB, hdist⟩ := matrixInternal_selfAdjoint_bounded_trace_approximation
    dims S hd U T hT hmem K hK hbound ε hε
  exact ⟨matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) B),
    ⟨B, hS, hB, rfl⟩, by simpa only [dist_comm] using hdist⟩

theorem matrixInternal_selfAdjoint_has_preimage (hU : (U : Filter Nat) ≤ atTop)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsSelfAdjoint T)
    (hmem : ContinuousLinearMapWOT.ofCLM T.val ∈ (matrixInternalWOTAlgebra dims S hd U).topologicalClosure) :
    ∃ x ∈ matrixInternalQuotient dims S (U : Filter Nat), matrixFiniteEmbedding dims hd U x = T := by
  obtain ⟨B, hS, _, hB⟩ := matrixInternal_selfAdjoint_vector_mem_traceBall dims S hd U hU
    T hT hmem ‖T‖ (norm_nonneg _) le_rfl
  refine ⟨matrixQuotientMk dims (U : Filter Nat) B, ⟨B, hS, rfl⟩, ?_⟩
  apply matrixFiniteVector_injective dims hd U
  rw [matrixFiniteVector_embedding]
  exact hB

theorem matrixInternal_has_preimage (hU : (U : Filter Nat) ≤ atTop)
    (T : MatrixFiniteOperatorAlgebra dims hd U)
    (hmem : ContinuousLinearMapWOT.ofCLM T.val ∈ (matrixInternalWOTAlgebra dims S hd U).topologicalClosure) :
    ∃ x ∈ matrixInternalQuotient dims S (U : Filter Nat), matrixFiniteEmbedding dims hd U x = T := by
  let C := StarSubalgebra.comap
    ((matrixOperatorToWOT dims hd U).comp (matrixOperatorAlgebra dims hd U).subtype)
    (matrixInternalWOTAlgebra dims S hd U).topologicalClosure
  let a : C := ⟨T, hmem⟩
  have hre : ContinuousLinearMapWOT.ofCLM (realPart T : MatrixFiniteOperatorAlgebra dims hd U).val ∈
      (matrixInternalWOTAlgebra dims S hd U).topologicalClosure := by
    have hm := (realPart a : C).property
    change C.subtype (realPart a) ∈ C at hm
    rw [map_realPart] at hm
    exact hm
  have him : ContinuousLinearMapWOT.ofCLM (imaginaryPart T : MatrixFiniteOperatorAlgebra dims hd U).val ∈
      (matrixInternalWOTAlgebra dims S hd U).topologicalClosure := by
    have hm := (imaginaryPart a : C).property
    change C.subtype (imaginaryPart a) ∈ C at hm
    rw [map_imaginaryPart] at hm
    exact hm
  obtain ⟨x, hx, hxe⟩ := matrixInternal_selfAdjoint_has_preimage dims S hd U hU
    (realPart T) (realPart T).property hre
  obtain ⟨y, hy, hye⟩ := matrixInternal_selfAdjoint_has_preimage dims S hd U hU
    (imaginaryPart T) (imaginaryPart T).property him
  refine ⟨x + Complex.I • y,
    (matrixInternalQuotient dims S (U : Filter Nat)).add_mem hx
      ((matrixInternalQuotient dims S (U : Filter Nat)).smul_mem hy Complex.I), ?_⟩
  rw [map_add, map_smul, hxe, hye, realPart_add_I_smul_imaginaryPart]

theorem matrixInternalWOTAlgebra_closure_eq (hU : (U : Filter Nat) ≤ atTop) :
    (matrixInternalWOTAlgebra dims S hd U).topologicalClosure = matrixInternalWOTAlgebra dims S hd U := by
  apply le_antisymm ?_ (StarSubalgebra.le_topologicalClosure _)
  intro T hT
  let a : MatrixFiniteOperatorAlgebra dims hd U :=
    ⟨T.toCLM, matrixInternalWOTAlgebra_closure_le dims S hd U hT⟩
  obtain ⟨x, hx, hxa⟩ := matrixInternal_has_preimage dims S hd U hU a hT
  exact ⟨x, hx, congrArg (fun R : MatrixFiniteOperatorAlgebra dims hd U =>
    ContinuousLinearMapWOT.ofCLM R.val) hxa⟩

theorem matrixInternalWOTAlgebra_isClosed (hU : (U : Filter Nat) ≤ atTop) :
    IsClosed (matrixInternalWOTAlgebra dims S hd U :
      Set (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U)) := by
  rw [← matrixInternalWOTAlgebra_closure_eq dims S hd U hU]
  exact StarSubalgebra.isClosed_topologicalClosure _

noncomputable def matrixInternalWOTClosureEmbedding :
    matrixInternalQuotient dims S (U : Filter Nat) →⋆ₐ[ℂ]
      (matrixInternalWOTAlgebra dims S hd U).topologicalClosure :=
  ((matrixLeftWOTRepresentation dims hd U).comp
    (matrixInternalQuotient dims S (U : Filter Nat)).subtype).codRestrict _
      (fun x => StarSubalgebra.le_topologicalClosure _ ⟨x.val, x.property, rfl⟩)

theorem matrixInternalWOTClosureEmbedding_injective :
    Function.Injective (matrixInternalWOTClosureEmbedding dims S hd U) := by
  intro x y h
  apply Subtype.ext
  apply matrixLeftRepresentation_injective dims hd U
  exact congrArg (fun R : (matrixInternalWOTAlgebra dims S hd U).topologicalClosure => R.val.toCLM) h

theorem matrixInternalWOTClosureEmbedding_surjective (hU : (U : Filter Nat) ≤ atTop) :
    Function.Surjective (matrixInternalWOTClosureEmbedding dims S hd U) := by
  intro T
  have hT := (matrixInternalWOTAlgebra_closure_eq dims S hd U hU).le T.property
  obtain ⟨x, hx, hxe⟩ := hT
  exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩

noncomputable def matrixInternalWOTEquiv (hU : (U : Filter Nat) ≤ atTop) :
    matrixInternalQuotient dims S (U : Filter Nat) ≃⋆ₐ[ℂ]
      (matrixInternalWOTAlgebra dims S hd U).topologicalClosure :=
  StarAlgEquiv.ofBijective (matrixInternalWOTClosureEmbedding dims S hd U)
    ⟨matrixInternalWOTClosureEmbedding_injective dims S hd U,
      matrixInternalWOTClosureEmbedding_surjective dims S hd U hU⟩

theorem matrixInternalWOTAlgebra_hyperfilter_isClosed :
    IsClosed (matrixInternalWOTAlgebra dims S hd (hyperfilter Nat) :
      Set (MatrixTraceHilbert dims hd (hyperfilter Nat) →WOT[ℂ]
        MatrixTraceHilbert dims hd (hyperfilter Nat))) :=
  matrixInternalWOTAlgebra_isClosed dims S hd (hyperfilter Nat) Nat.hyperfilter_le_atTop

end ThomGame.Analysis
