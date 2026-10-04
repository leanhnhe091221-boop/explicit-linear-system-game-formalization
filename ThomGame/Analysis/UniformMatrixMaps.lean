module

public import ThomGame.Analysis.MatrixTracialAlgebra

/-!
# Matrix maps uniformly bounded in the operator and trace norms

The two explicit bounds serve different purposes: the operator bound
preserves bounded sequences, and the trace bound preserves the null
ideal. The induced quotient map is constructed from those facts.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology NNReal

variable {ι : Type*} (dims : ι → Nat)

structure UniformMatrixMap where
  toLinearMap : (i : ι) → CMatrix (dims i) →ₗ[ℂ] CMatrix (dims i)
  operatorBound : ℝ≥0
  hilbertBound : ℝ≥0
  operator_le : ∀ i X, matrixOpNorm (toLinearMap i X) ≤ operatorBound * matrixOpNorm X
  hilbert_le : ∀ i X, hsNorm (toLinearMap i X) ≤ hilbertBound * hsNorm X

namespace UniformMatrixMap

variable {dims}

noncomputable def sequenceMap (F : UniformMatrixMap dims) :
    BoundedMatrixSequence dims →ₗ[ℂ] BoundedMatrixSequence dims where
  toFun A := ⟨fun i => F.toLinearMap i (A.val i), by
    obtain ⟨K, hK, hA⟩ := BoundedMatrixSequence.bound dims A
    refine ⟨F.operatorBound * K, mul_nonneg F.operatorBound.2 hK, fun i => ?_⟩
    exact (F.operator_le i (A.val i)).trans (mul_le_mul_of_nonneg_left (hA i) F.operatorBound.2)⟩
  map_add' A B := Subtype.ext (funext fun i => (F.toLinearMap i).map_add _ _)
  map_smul' c A := Subtype.ext (funext fun i => (F.toLinearMap i).map_smul c _)

@[simp] theorem sequenceMap_apply (F : UniformMatrixMap dims) (A : BoundedMatrixSequence dims) (i : ι) :
    (F.sequenceMap A).val i = F.toLinearMap i (A.val i) := rfl

theorem sequenceMap_null (F : UniformMatrixMap dims) (L : Filter ι) (A : BoundedMatrixSequence dims)
    (hA : A ∈ matrixNullIdeal dims L) : F.sequenceMap A ∈ matrixNullIdeal dims L := by
  have h := hA.const_mul (F.hilbertBound : ℝ)
  rw [mul_zero] at h
  exact squeeze_zero (fun _ => hsNorm_nonneg _) (fun i => F.hilbert_le i (A.val i)) h

noncomputable def quotientMap (F : UniformMatrixMap dims) (L : Filter ι) :
    MatrixTracialQuotient dims L →ₗ[ℂ] MatrixTracialQuotient dims L where
  toFun := Quotient.lift (fun A => matrixQuotientMk dims L (F.sequenceMap A)) (by
    intro A B h
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact F.sequenceMap_null L (A - B) ((Submodule.quotientRel_def _).mp h))
  map_add' x y := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims L y
    change matrixQuotientMk dims L (F.sequenceMap (A + B)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c x := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    change matrixQuotientMk dims L (F.sequenceMap (c • A)) = _
    rw [map_smul]
    exact (matrixQuotientStarAlgHom dims L).toAlgHom.toLinearMap.map_smul c _

@[simp] theorem quotientMap_mk (F : UniformMatrixMap dims) (L : Filter ι) (A : BoundedMatrixSequence dims) :
    F.quotientMap L (matrixQuotientMk dims L A) = matrixQuotientMk dims L (F.sequenceMap A) := rfl

def sub (F G : UniformMatrixMap dims) : UniformMatrixMap dims where
  toLinearMap i := F.toLinearMap i - G.toLinearMap i
  operatorBound := F.operatorBound + G.operatorBound
  hilbertBound := F.hilbertBound + G.hilbertBound
  operator_le i X := by
    change matrixOpNorm (F.toLinearMap i X - G.toLinearMap i X) ≤ _
    rw [sub_eq_add_neg]
    exact (matrixOpNorm_add_le _ _).trans (by
      rw [matrixOpNorm_neg, NNReal.coe_add, add_mul]
      exact add_le_add (F.operator_le i X) (G.operator_le i X))
  hilbert_le i X := by
    change hsNorm (F.toLinearMap i X - G.toLinearMap i X) ≤ _
    rw [sub_eq_add_neg]
    exact (hsNorm_add_le _ _).trans (by
      rw [hsNorm_neg, NNReal.coe_add, add_mul]
      exact add_le_add (F.hilbert_le i X) (G.hilbert_le i X))

@[simp] theorem sub_apply (F G : UniformMatrixMap dims) (i : ι) (X : CMatrix (dims i)) :
    (F.sub G).toLinearMap i X = F.toLinearMap i X - G.toLinearMap i X := rfl

theorem sub_sequenceMap (F G : UniformMatrixMap dims) (A : BoundedMatrixSequence dims) :
    (F.sub G).sequenceMap A = F.sequenceMap A - G.sequenceMap A := rfl

theorem sub_quotientMap (F G : UniformMatrixMap dims) (L : Filter ι) (x : MatrixTracialQuotient dims L) :
    (F.sub G).quotientMap L x = F.quotientMap L x - G.quotientMap L x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
  rw [quotientMap_mk, sub_sequenceMap, map_sub, quotientMap_mk, quotientMap_mk]

def comp (F G : UniformMatrixMap dims) : UniformMatrixMap dims where
  toLinearMap i := (F.toLinearMap i).comp (G.toLinearMap i)
  operatorBound := F.operatorBound * G.operatorBound
  hilbertBound := F.hilbertBound * G.hilbertBound
  operator_le i X := by
    change matrixOpNorm (F.toLinearMap i (G.toLinearMap i X)) ≤ _
    exact (F.operator_le i _).trans (by
      rw [NNReal.coe_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (G.operator_le i X) F.operatorBound.2)
  hilbert_le i X := by
    change hsNorm (F.toLinearMap i (G.toLinearMap i X)) ≤ _
    exact (F.hilbert_le i _).trans (by
      rw [NNReal.coe_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (G.hilbert_le i X) F.hilbertBound.2)

theorem comp_quotientMap (F G : UniformMatrixMap dims) (L : Filter ι) (x : MatrixTracialQuotient dims L) :
    (F.comp G).quotientMap L x = F.quotientMap L (G.quotientMap L x) := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
  rfl

end UniformMatrixMap
end ThomGame.Analysis
