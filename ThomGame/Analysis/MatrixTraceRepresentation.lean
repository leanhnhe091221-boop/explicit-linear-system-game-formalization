module

public import ThomGame.Analysis.MatrixTraceLeftAction
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A faithful star-algebra representation by bounded Hilbert-space operators

Left multiplication extends to the trace Hilbert space, preserving all
algebra operations and adjoints. The vector represented by the identity
is cyclic, separates the represented algebra, and realizes its trace.
Weak/strong operator closure is not identified with the original quotient.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

@[simp] theorem matrixLeftOperator_zero : matrixLeftOperator dims hd U 0 = 0 := by
  apply matrixHilbertOperator_ext dims hd U
  intro x
  simp only [matrixLeftOperator_apply, zero_mul, map_zero, zero_apply]

@[simp] theorem matrixLeftOperator_one : matrixLeftOperator dims hd U 1 = 1 := by
  apply matrixHilbertOperator_ext dims hd U
  intro x
  simp only [matrixLeftOperator_apply, one_mul, one_apply_eq_self]

theorem matrixLeftOperator_add (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixLeftOperator dims hd U (x + y) = matrixLeftOperator dims hd U x + matrixLeftOperator dims hd U y := by
  apply matrixHilbertOperator_ext dims hd U
  intro z
  simp only [add_apply, matrixLeftOperator_apply, add_mul, map_add]

theorem matrixLeftOperator_mul (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixLeftOperator dims hd U (x * y) = matrixLeftOperator dims hd U x * matrixLeftOperator dims hd U y := by
  apply matrixHilbertOperator_ext dims hd U
  intro z
  simp only [mul_apply_eq_comp, matrixLeftOperator_apply, mul_assoc]

theorem matrixLeftOperator_algebraMap (c : ℂ) :
    matrixLeftOperator dims hd U (algebraMap ℂ (MatrixTracialQuotient dims (U : Filter ι)) c) =
      algebraMap ℂ (MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U) c := by
  apply matrixHilbertOperator_ext dims hd U
  intro x
  rw [matrixLeftOperator_apply, ContinuousLinearMap.algebraMap_apply,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul]

theorem matrixLeftOperator_star (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixLeftOperator dims hd U (star x) = star (matrixLeftOperator dims hd U x) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  have he :
      (fun p : MatrixTraceHilbert dims hd U × MatrixTraceHilbert dims hd U =>
        inner ℂ (matrixLeftOperator dims hd U (star x) p.1) p.2) =
      (fun p : MatrixTraceHilbert dims hd U × MatrixTraceHilbert dims hd U =>
        inner ℂ p.1 (matrixLeftOperator dims hd U x p.2)) := by
    apply Continuous.ext_on ((matrixHilbertEmbedding_dense dims hd U).prodMap
      (matrixHilbertEmbedding_dense dims hd U)) (by fun_prop) (by fun_prop)
    rintro _ ⟨⟨a, b⟩, rfl⟩
    simp only [Prod.map_apply, matrixLeftOperator_apply, matrixHilbertEmbedding_inner,
      star_mul, star_star, mul_assoc]
  intro a b
  exact congrFun he (a, b)

noncomputable def matrixLeftRepresentation :
    MatrixTracialQuotient dims (U : Filter ι) →⋆ₐ[ℂ]
      (MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U) where
  toFun := matrixLeftOperator dims hd U
  map_one' := matrixLeftOperator_one dims hd U
  map_mul' := matrixLeftOperator_mul dims hd U
  map_zero' := matrixLeftOperator_zero dims hd U
  map_add' := matrixLeftOperator_add dims hd U
  commutes' := matrixLeftOperator_algebraMap dims hd U
  map_star' := matrixLeftOperator_star dims hd U

theorem matrixLeftRepresentation_injective : Function.Injective (matrixLeftRepresentation dims hd U) :=
  matrixLeftOperator_injective dims hd U

theorem matrixLeftRepresentation_apply (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixLeftRepresentation dims hd U x (matrixHilbertEmbedding dims hd U y) =
      matrixHilbertEmbedding dims hd U (x * y) := matrixLeftOperator_apply dims hd U x y

theorem matrixLeftRepresentation_vector_trace (x : MatrixTracialQuotient dims (U : Filter ι)) :
    inner ℂ (matrixHilbertEmbedding dims hd U 1)
      (matrixLeftRepresentation dims hd U x (matrixHilbertEmbedding dims hd U 1)) =
        matrixUltratrace dims hd U x := by
  rw [matrixLeftRepresentation_apply, matrixHilbertEmbedding_inner, star_one, mul_one, one_mul]

theorem matrixLeftRepresentation_cyclic :
    DenseRange (fun x => matrixLeftRepresentation dims hd U x (matrixHilbertEmbedding dims hd U 1)) := by
  simpa only [matrixLeftRepresentation_apply, mul_one] using matrixHilbertEmbedding_dense dims hd U

theorem matrixLeftRepresentation_separating (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixLeftRepresentation dims hd U x (matrixHilbertEmbedding dims hd U 1) = 0 ↔ x = 0 := by
  rw [matrixLeftRepresentation_apply, mul_one]
  exact map_eq_zero_iff (matrixHilbertEmbedding dims hd U) (matrixHilbertEmbedding_injective dims hd U)

end ThomGame.Analysis
