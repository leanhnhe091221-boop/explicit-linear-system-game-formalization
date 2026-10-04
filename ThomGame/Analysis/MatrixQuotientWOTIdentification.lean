module

public import ThomGame.Analysis.MatrixSelfAdjointDensity
public import ThomGame.Analysis.MatrixRepresentedWOTBounds

/-!
# The original matrix quotient equals its generated WOT algebra

Uniformly bounded self-adjoint matrix approximations converge in the
trace Hilbert space. Completeness of the fixed representative ball gives
an actual representative for the limit. The separating unit vector then
identifies the represented operator with the prescribed closure element.
Real and imaginary parts extend the result to every closure element.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

theorem matrixFinite_selfAdjoint_vector_mem_traceBall (hU : (U : Filter Nat) ≤ atTop)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsSelfAdjoint T)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖T‖ ≤ K) :
    matrixFiniteVector dims hd U T ∈ matrixBoundedTraceBall dims hd U K := by
  rw [← (matrixBoundedTraceBall_isClosed dims hd U hU K hK).closure_eq]
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨B, _, hB, hdist⟩ := matrixFinite_selfAdjoint_bounded_trace_approximation dims hd U T hT K hK hbound ε hε
  exact ⟨matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) B),
    ⟨B, hB, rfl⟩, by simpa only [dist_comm] using hdist⟩

theorem matrixFinite_selfAdjoint_has_preimage (hU : (U : Filter Nat) ≤ atTop)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsSelfAdjoint T) :
    ∃ x : MatrixTracialQuotient dims (U : Filter Nat), matrixFiniteEmbedding dims hd U x = T := by
  obtain ⟨B, _, hB⟩ := matrixFinite_selfAdjoint_vector_mem_traceBall dims hd U hU T hT
    ‖T‖ (norm_nonneg _) le_rfl
  refine ⟨matrixQuotientMk dims (U : Filter Nat) B, ?_⟩
  apply matrixFiniteVector_injective dims hd U
  rw [matrixFiniteVector_embedding]
  exact hB

theorem matrixFiniteEmbedding_surjective (hU : (U : Filter Nat) ≤ atTop) :
    Function.Surjective (matrixFiniteEmbedding dims hd U) := by
  intro T
  obtain ⟨x, hx⟩ := matrixFinite_selfAdjoint_has_preimage dims hd U hU (realPart T) (realPart T).property
  obtain ⟨y, hy⟩ := matrixFinite_selfAdjoint_has_preimage dims hd U hU (imaginaryPart T) (imaginaryPart T).property
  refine ⟨x + Complex.I • y, ?_⟩
  rw [map_add, map_smul, hx, hy, realPart_add_I_smul_imaginaryPart]

noncomputable def matrixFiniteEquiv (hU : (U : Filter Nat) ≤ atTop) :
    MatrixTracialQuotient dims (U : Filter Nat) ≃⋆ₐ[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  StarAlgEquiv.ofBijective (matrixFiniteEmbedding dims hd U)
    ⟨matrixFiniteEmbedding_injective dims hd U, matrixFiniteEmbedding_surjective dims hd U hU⟩

@[simp] theorem matrixFiniteEquiv_apply (hU : (U : Filter Nat) ≤ atTop)
    (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    matrixFiniteEquiv dims hd U hU x = matrixFiniteEmbedding dims hd U x := rfl

theorem matrixFiniteEquiv_trace (hU : (U : Filter Nat) ≤ atTop)
    (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    matrixFiniteTrace dims hd U (matrixFiniteEquiv dims hd U hU x) = matrixUltratrace dims hd U x :=
  matrixFiniteTrace_embedding dims hd U x

theorem matrixWOTEmbedding_surjective (hU : (U : Filter Nat) ≤ atTop) :
    Function.Surjective (matrixWOTEmbedding dims hd U) := by
  intro T
  obtain ⟨x, hx⟩ := matrixFiniteEmbedding_surjective dims hd U hU ((matrixOperatorClosureEquiv dims hd U).symm T)
  refine ⟨x, ?_⟩
  have he := congrArg (matrixOperatorClosureEquiv dims hd U) hx
  rw [(matrixOperatorClosureEquiv dims hd U).apply_symm_apply] at he
  exact he

noncomputable def matrixWOTEquiv (hU : (U : Filter Nat) ≤ atTop) :
    MatrixTracialQuotient dims (U : Filter Nat) ≃⋆ₐ[ℂ] MatrixWOTClosure dims hd U :=
  StarAlgEquiv.ofBijective (matrixWOTEmbedding dims hd U)
    ⟨matrixWOTEmbedding_injective dims hd U, matrixWOTEmbedding_surjective dims hd U hU⟩

@[simp] theorem matrixWOTEquiv_apply (hU : (U : Filter Nat) ≤ atTop)
    (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    matrixWOTEquiv dims hd U hU x = matrixWOTEmbedding dims hd U x := rfl

theorem matrixWOTEquiv_trace (hU : (U : Filter Nat) ≤ atTop)
    (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    matrixWOTTrace dims hd U (matrixWOTEquiv dims hd U hU x) = matrixUltratrace dims hd U x :=
  matrixWOTTrace_embedding dims hd U x

theorem matrixLeftWOTRepresentation_range_eq (hU : (U : Filter Nat) ≤ atTop) :
    (matrixLeftWOTRepresentation dims hd U).range = matrixWOTAlgebra dims hd U := by
  ext T
  constructor
  · rintro ⟨x, rfl⟩
    exact matrixLeftWOTRepresentation_mem dims hd U x
  · intro hT
    obtain ⟨x, hx⟩ := matrixWOTEmbedding_surjective dims hd U hU ⟨T, hT⟩
    exact ⟨x, congrArg (fun S : MatrixWOTClosure dims hd U => S.val) hx⟩

theorem matrixLeftWOTRepresentation_range_isClosed (hU : (U : Filter Nat) ≤ atTop) :
    IsClosed ((matrixLeftWOTRepresentation dims hd U).range :
      Set (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U)) := by
  rw [matrixLeftWOTRepresentation_range_eq dims hd U hU]
  exact matrixWOTAlgebra_isClosed dims hd U

theorem matrixRepresentedAlgebra_eq_operatorAlgebra (hU : (U : Filter Nat) ≤ atTop) :
    matrixRepresentedAlgebra dims hd U = matrixOperatorAlgebra dims hd U := by
  ext T
  constructor
  · rintro ⟨x, rfl⟩
    exact matrixLeftWOTRepresentation_mem dims hd U x
  · intro hT
    change ContinuousLinearMapWOT.ofCLM T ∈ matrixWOTAlgebra dims hd U at hT
    rw [← matrixLeftWOTRepresentation_range_eq dims hd U hU] at hT
    obtain ⟨x, hx⟩ := hT
    exact ⟨x, congrArg ContinuousLinearMapWOT.toCLM hx⟩

theorem matrixFiniteEmbedding_hyperfilter_surjective :
    Function.Surjective (matrixFiniteEmbedding dims hd (hyperfilter Nat)) :=
  matrixFiniteEmbedding_surjective dims hd (hyperfilter Nat) Nat.hyperfilter_le_atTop

end ThomGame.Analysis
