module

public import ThomGame.Analysis.MatrixTraceRepresentation

/-!
# Bounded right multiplication and the commuting left/right actions

Right multiplication extends to the same trace Hilbert space as left
multiplication. The extensions commute on all vectors by density. The
identity vector has dense right orbit, which will separate the weak
operator closure of the left algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem matrixTraceSpace_norm_right_mul_le (A : BoundedMatrixSequence dims) (K : ℝ)
    (hK : ∀ i, matrixOpNorm (A.val i) ≤ K) (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixTraceSpaceEquiv dims hd U (x * matrixQuotientMk dims (U : Filter ι) A)‖ ≤
      K * ‖matrixTraceSpaceEquiv dims hd U x‖ := by
  obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  rw [← map_mul]
  apply le_of_tendsto_of_tendsto' (matrixTraceSpace_norm_tendsto dims hd U (B * A))
    ((matrixTraceSpace_norm_tendsto dims hd U B).const_mul K)
  intro i
  calc
    hsNorm (B.val i * A.val i) ≤ hsNorm (B.val i) * matrixOpNorm (A.val i) := hsNorm_mul_le_right _ _
    _ ≤ hsNorm (B.val i) * K := mul_le_mul_of_nonneg_left (hK i) (hsNorm_nonneg _)
    _ = K * hsNorm (B.val i) := mul_comm _ _

def matrixTraceRightLinear (x : MatrixTracialQuotient dims (U : Filter ι)) :
    MatrixTraceSpace dims hd U →ₗ[ℂ] MatrixTraceSpace dims hd U where
  toFun y := matrixTraceSpaceEquiv dims hd U ((matrixTraceSpaceEquiv dims hd U).symm y * x)
  map_add' y z := by rw [map_add, add_mul, map_add]
  map_smul' c y := by
    rw [map_smul, smul_mul_assoc, map_smul]
    rfl

theorem matrixTraceRight_bounded (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖matrixTraceRightLinear dims hd U x y‖ ≤ K * ‖y‖ := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  obtain ⟨K, hK, hA⟩ := BoundedMatrixSequence.bound dims A
  refine ⟨K, hK, ?_⟩
  intro y
  obtain ⟨z, rfl⟩ := (matrixTraceSpaceEquiv dims hd U).surjective y
  exact matrixTraceSpace_norm_right_mul_le dims hd U A K hA z

noncomputable def matrixTraceRight (x : MatrixTracialQuotient dims (U : Filter ι)) :
    MatrixTraceSpace dims hd U →L[ℂ] MatrixTraceSpace dims hd U :=
  (matrixTraceRightLinear dims hd U x).mkContinuous (matrixTraceRight_bounded dims hd U x).choose
    (matrixTraceRight_bounded dims hd U x).choose_spec.2

noncomputable def matrixRightOperator (x : MatrixTracialQuotient dims (U : Filter ι)) :
    MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U :=
  (matrixTraceRight dims hd U x).completion

theorem matrixRightOperator_apply (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixRightOperator dims hd U x (matrixHilbertEmbedding dims hd U y) =
      matrixHilbertEmbedding dims hd U (y * x) := by
  exact ContinuousLinearMap.completion_apply_coe (matrixTraceRight dims hd U x)
    (matrixTraceSpaceEquiv dims hd U y)

theorem matrixLeftRight_commute (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    Commute (matrixLeftOperator dims hd U x) (matrixRightOperator dims hd U y) := by
  apply matrixHilbertOperator_ext dims hd U
  intro z
  simp only [mul_apply_eq_comp, matrixLeftOperator_apply, matrixRightOperator_apply, mul_assoc]

theorem matrixRightOperator_cyclic :
    DenseRange (fun x => matrixRightOperator dims hd U x (matrixHilbertEmbedding dims hd U 1)) := by
  simpa only [matrixRightOperator_apply, one_mul] using matrixHilbertEmbedding_dense dims hd U

theorem matrix_commuting_right_separating
    (T : MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U)
    (hcomm : ∀ x, Commute T (matrixRightOperator dims hd U x))
    (hzero : T (matrixHilbertEmbedding dims hd U 1) = 0) : T = 0 := by
  apply matrixHilbertOperator_ext dims hd U
  intro x
  have hx := congrArg (fun S : MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U =>
    S (matrixHilbertEmbedding dims hd U 1)) (hcomm x).eq
  simpa only [mul_apply_eq_comp, matrixRightOperator_apply, one_mul, hzero, map_zero, zero_apply] using hx

end ThomGame.Analysis
