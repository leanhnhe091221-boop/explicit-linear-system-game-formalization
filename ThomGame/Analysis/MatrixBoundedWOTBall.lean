module

public import ThomGame.Analysis.MatrixBoundedTraceConvex
public import ThomGame.Analysis.MatrixWOTClosure

/-!
# Weak operator closedness of balls with bounded matrix representatives

An operator in the generated algebra belongs to the represented ball
exactly when its identity vector has a uniformly bounded matrix
representative. The separating vector makes this criterion sufficient.
Convex weak closedness of the trace-vector ball then gives actual WOT
closedness of the represented operator ball.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem matrixLeftRepresentation_norm_le (A : BoundedMatrixSequence dims) (K : ℝ)
    (hK : 0 ≤ K) (hA : ∀ i, matrixOpNorm (A.val i) ≤ K) :
    ‖matrixLeftRepresentation dims hd U (matrixQuotientMk dims (U : Filter ι) A)‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  refine (matrixHilbertEmbedding_dense dims hd U).induction_on v ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro x
    rw [matrixLeftRepresentation_apply, matrixHilbertEmbedding_norm, matrixHilbertEmbedding_norm]
    exact matrixTraceSpace_norm_mul_le dims hd U A K hA x

def matrixBoundedWOTBall (K : ℝ) :
    Set (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) :=
  {T | ∃ A : BoundedMatrixSequence dims, (∀ i, matrixOpNorm (A.val i) ≤ K) ∧
    matrixLeftWOTRepresentation dims hd U (matrixQuotientMk dims (U : Filter ι) A) = T}

theorem matrixBoundedWOTBall_norm_le (K : ℝ) (hK : 0 ≤ K)
    {T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U}
    (hT : T ∈ matrixBoundedWOTBall dims hd U K) : ‖T.toCLM‖ ≤ K := by
  obtain ⟨A, hA, rfl⟩ := hT
  exact matrixLeftRepresentation_norm_le dims hd U A K hK hA

theorem matrixBoundedWOTBall_iff (K : ℝ)
    (T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) :
    T ∈ matrixBoundedWOTBall dims hd U K ↔ T ∈ matrixWOTAlgebra dims hd U ∧
      T (matrixHilbertEmbedding dims hd U 1) ∈ matrixBoundedTraceBall dims hd U K := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨matrixLeftWOTRepresentation_mem dims hd U _, A, hA, ?_⟩
    rw [matrixLeftWOTRepresentation_apply, matrixLeftRepresentation_apply, mul_one]
  · rintro ⟨hT, A, hA, hAx⟩
    let S := matrixLeftWOTRepresentation dims hd U (matrixQuotientMk dims (U : Filter ι) A)
    have hS : S ∈ matrixWOTAlgebra dims hd U := matrixLeftWOTRepresentation_mem dims hd U _
    have hzero : (T - S) (matrixHilbertEmbedding dims hd U 1) = 0 := by
      change T (matrixHilbertEmbedding dims hd U 1) - S (matrixHilbertEmbedding dims hd U 1) = 0
      dsimp [S]
      rw [matrixLeftWOTRepresentation_apply, matrixLeftRepresentation_apply, mul_one, hAx, sub_self]
    have heq := matrixWOT_separating dims hd U (T - S)
      ((matrixWOTAlgebra dims hd U).sub_mem hT hS) hzero
    exact ⟨A, hA, (sub_eq_zero.mp heq).symm⟩

theorem matrixWOT_apply_weak_continuous (v : MatrixTraceHilbert dims hd U) :
    Continuous (fun T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U =>
      toWeakSpace ℂ (MatrixTraceHilbert dims hd U) (T v)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  exact ContinuousLinearMapWOT.continuous_dual_apply v f

theorem matrixBoundedWOTBall_isClosed (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
    (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop) (K : ℝ) (hK : 0 ≤ K) :
    IsClosed (matrixBoundedWOTBall dims hd U K) := by
  have hv : IsClosed {T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U |
      T (matrixHilbertEmbedding dims hd U 1) ∈ matrixBoundedTraceBall dims hd U K} := by
    convert (matrixBoundedTraceBall_weak_isClosed dims hd U hU K hK).preimage
      (matrixWOT_apply_weak_continuous dims hd U (matrixHilbertEmbedding dims hd U 1)) using 1
    ext T
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, heq⟩
      change T (matrixHilbertEmbedding dims hd U 1) ∈ matrixBoundedTraceBall dims hd U K
      exact (toWeakSpace ℂ (MatrixTraceHilbert dims hd U)).injective heq ▸ hx
  have he : matrixBoundedWOTBall dims hd U K = (matrixWOTAlgebra dims hd U : Set _) ∩
      {T | T (matrixHilbertEmbedding dims hd U 1) ∈ matrixBoundedTraceBall dims hd U K} := by
    ext T
    exact matrixBoundedWOTBall_iff dims hd U K T
  rw [he]
  exact (matrixWOTAlgebra_isClosed dims hd U).inter hv

theorem matrixBoundedWOTBall_hyperfilter_isClosed (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
    (K : ℝ) (hK : 0 ≤ K) :
    IsClosed (matrixBoundedWOTBall dims hd (hyperfilter Nat) K) :=
  matrixBoundedWOTBall_isClosed dims hd (hyperfilter Nat) Nat.hyperfilter_le_atTop K hK

end ThomGame.Analysis
