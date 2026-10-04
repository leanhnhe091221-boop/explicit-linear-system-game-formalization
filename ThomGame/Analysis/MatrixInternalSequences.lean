module

public import ThomGame.Analysis.MatrixNormControlledRepresentatives
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Bounded sequences in coordinate matrix subalgebras

The coordinate constraints define a closed star subalgebra of the actual
supremum operator norm product. Its image in the tracial quotient consists
exactly of the classes having a representative in every prescribed
coordinate subalgebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped ENNReal Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat)
  (S : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))

def matrixInternalSequences : StarSubalgebra ℂ (BoundedMatrixSequence dims) where
  carrier := {A | ∀ i, A.val i ∈ S i}
  zero_mem' := fun i => (S i).zero_mem
  one_mem' := fun i => (S i).one_mem
  add_mem' := fun hA hB i => (S i).add_mem (hA i) (hB i)
  mul_mem' := fun hA hB i => (S i).mul_mem (hA i) (hB i)
  algebraMap_mem' := fun c i => (S i).algebraMap_mem c
  star_mem' := fun hA i => (S i).star_mem' (hA i)

@[simp] theorem mem_matrixInternalSequences (A : BoundedMatrixSequence dims) :
    A ∈ matrixInternalSequences dims S ↔ ∀ i, A.val i ∈ S i := Iff.rfl

variable (hd : ∀ i, 0 < dims i)

noncomputable def matrixInternalProduct : StarSubalgebra ℂ (MatrixOperatorProduct dims hd) :=
  StarSubalgebra.comap (matrixOperatorProductEquiv dims hd).toStarAlgHom
    (matrixInternalSequences dims S)

@[simp] theorem mem_matrixInternalProduct (A : MatrixOperatorProduct dims hd) :
    A ∈ matrixInternalProduct dims S hd ↔ ∀ i, A i ∈ S i := Iff.rfl

theorem matrixOperatorProduct_eval_continuous (i : ι) :
    Continuous (fun A : MatrixOperatorProduct dims hd => A i) := by
  exact (lp.evalCLM (𝕜 := ℂ) (E := fun i => CMatrix (dims i)) (p := ∞) i).continuous

instance matrixInternalProduct_isClosed :
    IsClosed (matrixInternalProduct dims S hd : Set (MatrixOperatorProduct dims hd)) := by
  change IsClosed {A : MatrixOperatorProduct dims hd | ∀ i, A i ∈ S i}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact (S i).toSubalgebra.toSubmodule.closed_of_finiteDimensional.preimage
    (matrixOperatorProduct_eval_continuous dims hd i)

noncomputable abbrev MatrixInternalProduct := matrixInternalProduct dims S hd

noncomputable def matrixInternalProductToSequences :
    MatrixInternalProduct dims S hd →⋆ₐ[ℂ] BoundedMatrixSequence dims :=
  (matrixOperatorProductEquiv dims hd).toStarAlgHom.comp
    (matrixInternalProduct dims S hd).subtype

@[simp] theorem matrixInternalProductToSequences_apply
    (A : MatrixInternalProduct dims S hd) (i : ι) :
    (matrixInternalProductToSequences dims S hd A).val i = A.val i := rfl

theorem matrixInternalProductToSequences_mem (A : MatrixInternalProduct dims S hd) (i : ι) :
    (matrixInternalProductToSequences dims S hd A).val i ∈ S i := A.property i

theorem matrixInternalProductToSequences_norm_le (A : MatrixInternalProduct dims S hd) (i : ι) :
    matrixOpNorm ((matrixInternalProductToSequences dims S hd A).val i) ≤ ‖A‖ :=
  matrixOperatorProduct_apply_norm_le dims hd A.val i

variable (L : Filter ι)

noncomputable def matrixInternalQuotient : StarSubalgebra ℂ (MatrixTracialQuotient dims L) :=
  StarSubalgebra.map (matrixQuotientStarAlgHom dims L) (matrixInternalSequences dims S)

theorem mem_matrixInternalQuotient (x : MatrixTracialQuotient dims L) :
    x ∈ matrixInternalQuotient dims S L ↔
      ∃ A : BoundedMatrixSequence dims, (∀ i, A.val i ∈ S i) ∧ matrixQuotientMk dims L A = x :=
  Iff.rfl

noncomputable def matrixInternalProductToQuotient :
    MatrixInternalProduct dims S hd →⋆ₐ[ℂ] MatrixTracialQuotient dims L :=
  (matrixQuotientStarAlgHom dims L).comp (matrixInternalProductToSequences dims S hd)

theorem matrixInternalProductToQuotient_range :
    (matrixInternalProductToQuotient dims S hd L).range = matrixInternalQuotient dims S L := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨matrixInternalProductToSequences dims S hd A, A.property, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    refine ⟨⟨(matrixOperatorProductEquiv dims hd).symm A, hA⟩, ?_⟩
    change matrixQuotientMk dims L
      (matrixOperatorProductEquiv dims hd ((matrixOperatorProductEquiv dims hd).symm A)) = _
    rw [(matrixOperatorProductEquiv dims hd).apply_symm_apply]
    rfl

end ThomGame.Analysis
