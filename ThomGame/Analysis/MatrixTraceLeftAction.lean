module

public import ThomGame.Analysis.MatrixTraceHilbert
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Bounded left multiplication on the trace Hilbert space

The finite matrix inequality `norm₂ (A B) ≤ normOp A * norm₂ B`
passes to ultralimits. Thus every actual quotient element acts by a
bounded linear map on the 2-norm space and on its Hilbert completion.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem matrixTraceSpace_norm_mul_le (A : BoundedMatrixSequence dims) (K : ℝ)
    (hK : ∀ i, matrixOpNorm (A.val i) ≤ K) (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixTraceSpaceEquiv dims hd U (matrixQuotientMk dims (U : Filter ι) A * x)‖ ≤
      K * ‖matrixTraceSpaceEquiv dims hd U x‖ := by
  obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  rw [← map_mul]
  apply le_of_tendsto_of_tendsto' (matrixTraceSpace_norm_tendsto dims hd U (A * B))
    ((matrixTraceSpace_norm_tendsto dims hd U B).const_mul K)
  intro i
  exact (hsNorm_mul_le_left (A.val i) (B.val i)).trans
    (mul_le_mul_of_nonneg_right (hK i) (hsNorm_nonneg _))

def matrixTraceLeftLinear (x : MatrixTracialQuotient dims (U : Filter ι)) :
    MatrixTraceSpace dims hd U →ₗ[ℂ] MatrixTraceSpace dims hd U where
  toFun y := matrixTraceSpaceEquiv dims hd U (x * (matrixTraceSpaceEquiv dims hd U).symm y)
  map_add' y z := by rw [map_add, mul_add, map_add]
  map_smul' c y := by
    rw [map_smul, mul_smul_comm, map_smul]
    rfl

theorem matrixTraceLeft_bounded (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖matrixTraceLeftLinear dims hd U x y‖ ≤ K * ‖y‖ := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  obtain ⟨K, hK, hA⟩ := BoundedMatrixSequence.bound dims A
  refine ⟨K, hK, ?_⟩
  intro y
  obtain ⟨z, rfl⟩ := (matrixTraceSpaceEquiv dims hd U).surjective y
  exact matrixTraceSpace_norm_mul_le dims hd U A K hA z

noncomputable def matrixTraceLeft (x : MatrixTracialQuotient dims (U : Filter ι)) :
    MatrixTraceSpace dims hd U →L[ℂ] MatrixTraceSpace dims hd U :=
  (matrixTraceLeftLinear dims hd U x).mkContinuous (matrixTraceLeft_bounded dims hd U x).choose
    (matrixTraceLeft_bounded dims hd U x).choose_spec.2

theorem matrixTraceLeft_apply (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixTraceLeft dims hd U x (matrixTraceSpaceEquiv dims hd U y) =
      matrixTraceSpaceEquiv dims hd U (x * y) := rfl

noncomputable def matrixLeftOperator (x : MatrixTracialQuotient dims (U : Filter ι)) :
    MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U :=
  (matrixTraceLeft dims hd U x).completion

theorem matrixLeftOperator_apply (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixLeftOperator dims hd U x (matrixHilbertEmbedding dims hd U y) =
      matrixHilbertEmbedding dims hd U (x * y) := by
  exact ContinuousLinearMap.completion_apply_coe (matrixTraceLeft dims hd U x)
    (matrixTraceSpaceEquiv dims hd U y)

theorem matrixHilbertOperator_ext
    {S T : MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U}
    (h : ∀ x, S (matrixHilbertEmbedding dims hd U x) = T (matrixHilbertEmbedding dims hd U x)) : S = T := by
  apply DFunLike.coe_injective
  apply Continuous.ext_on (matrixHilbertEmbedding_dense dims hd U) S.continuous T.continuous
  rintro _ ⟨x, rfl⟩
  exact h x

theorem matrixLeftOperator_injective : Function.Injective (matrixLeftOperator dims hd U) := by
  intro x y h
  apply matrixHilbertEmbedding_injective dims hd U
  have hv := congrArg (fun T : MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U =>
    T (matrixHilbertEmbedding dims hd U 1)) h
  simpa only [matrixLeftOperator_apply, mul_one] using hv

end ThomGame.Analysis
