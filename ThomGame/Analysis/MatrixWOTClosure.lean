module

public import ThomGame.Analysis.MatrixTraceRightAction
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# The concrete weak operator closure of the matrix trace representation

This is an actual weakly closed unital star subalgebra of bounded Hilbert
operators. The original matrix quotient embeds into it faithfully.
Commutation with right multiplication survives weak operator closure,
and hence the identity vector separates this entire closed algebra.
Equality of the closure with the original represented quotient is not
asserted here.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

noncomputable def matrixOperatorToWOT :
    (MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U) →⋆ₐ[ℂ]
      (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) where
  toAlgHom := (ContinuousLinearMapWOT.algEquiv ℂ).symm.toAlgHom
  map_star' _ := rfl

noncomputable def matrixLeftWOTRepresentation :
    MatrixTracialQuotient dims (U : Filter ι) →⋆ₐ[ℂ]
      (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) :=
  (matrixOperatorToWOT dims hd U).comp (matrixLeftRepresentation dims hd U)

theorem matrixLeftWOTRepresentation_apply (x : MatrixTracialQuotient dims (U : Filter ι))
    (v : MatrixTraceHilbert dims hd U) :
    matrixLeftWOTRepresentation dims hd U x v = matrixLeftRepresentation dims hd U x v := rfl

noncomputable def matrixWOTAlgebra :
    StarSubalgebra ℂ (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) :=
  (matrixLeftWOTRepresentation dims hd U).range.topologicalClosure

theorem matrixWOTAlgebra_isClosed : IsClosed (matrixWOTAlgebra dims hd U :
    Set (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U)) :=
  StarSubalgebra.isClosed_topologicalClosure _

theorem matrixLeftWOTRepresentation_mem (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixLeftWOTRepresentation dims hd U x ∈ matrixWOTAlgebra dims hd U :=
  StarSubalgebra.le_topologicalClosure _ ⟨x, rfl⟩

noncomputable abbrev MatrixWOTClosure := matrixWOTAlgebra dims hd U

noncomputable def matrixWOTEmbedding :
    MatrixTracialQuotient dims (U : Filter ι) →⋆ₐ[ℂ] MatrixWOTClosure dims hd U :=
  (matrixLeftWOTRepresentation dims hd U).codRestrict (matrixWOTAlgebra dims hd U)
    (matrixLeftWOTRepresentation_mem dims hd U)

theorem matrixWOTEmbedding_injective : Function.Injective (matrixWOTEmbedding dims hd U) := by
  intro x y h
  apply matrixLeftRepresentation_injective dims hd U
  exact congrArg (fun T : MatrixWOTClosure dims hd U => T.val.toCLM) h

theorem matrixWOT_commutes_right
    (T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U)
    (hT : T ∈ matrixWOTAlgebra dims hd U) (x : MatrixTracialQuotient dims (U : Filter ι)) :
    Commute T (ContinuousLinearMapWOT.ofCLM (matrixRightOperator dims hd U x)) := by
  change T ∈ closure ((matrixLeftWOTRepresentation dims hd U).range : Set _) at hT
  apply (closure_minimal (t := {S | Commute S (ContinuousLinearMapWOT.ofCLM
    (matrixRightOperator dims hd U x))}) ?_ ?_) hT
  · rintro _ ⟨a, rfl⟩
    exact congrArg ContinuousLinearMapWOT.ofCLM (matrixLeftRight_commute dims hd U a x).eq
  · exact isClosed_eq (continuous_mul_const _) (continuous_const_mul _)

theorem matrixWOT_separating
    (T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U)
    (hT : T ∈ matrixWOTAlgebra dims hd U)
    (hzero : T (matrixHilbertEmbedding dims hd U 1) = 0) : T = 0 := by
  apply ContinuousLinearMapWOT.toCLM_injective
  apply matrix_commuting_right_separating dims hd U T.toCLM ?_ hzero
  intro x
  exact congrArg ContinuousLinearMapWOT.toCLM (matrixWOT_commutes_right dims hd U T hT x).eq

end ThomGame.Analysis
