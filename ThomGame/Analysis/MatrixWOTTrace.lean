module

public import ThomGame.Analysis.MatrixWOTClosure

/-!
# The faithful tracial vector functional on the weak operator closure

The identity vector defines a weak-operator-continuous functional.
Separate continuity of multiplication extends its tracial identity from
the original matrix quotient to the whole weak operator closure. The
right-action separation theorem makes this positive trace faithful.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

noncomputable def matrixVectorTrace :
    (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) →ₗ[ℂ] ℂ where
  toFun T := inner ℂ (matrixHilbertEmbedding dims hd U 1) (T (matrixHilbertEmbedding dims hd U 1))
  map_add' S T := by
    rw [ContinuousLinearMapWOT.add_apply, inner_add_right]
  map_smul' c T := by
    simp only [ContinuousLinearMapWOT.smul_apply, inner_smul_right, RingHom.id_apply, smul_eq_mul]

theorem matrixVectorTrace_continuous : Continuous (matrixVectorTrace dims hd U) := by
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id
    (matrixHilbertEmbedding dims hd U 1) (matrixHilbertEmbedding dims hd U 1)

theorem matrixVectorTrace_representation (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixVectorTrace dims hd U (matrixLeftWOTRepresentation dims hd U x) =
      matrixUltratrace dims hd U x := matrixLeftRepresentation_vector_trace dims hd U x

@[simp] theorem matrixVectorTrace_one : matrixVectorTrace dims hd U 1 = 1 := by
  rw [← map_one (matrixLeftWOTRepresentation dims hd U), matrixVectorTrace_representation,
    matrixUltratrace_one]

theorem matrixVectorTrace_star
    (T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) :
    matrixVectorTrace dims hd U (star T) = star (matrixVectorTrace dims hd U T) := by
  change inner ℂ _ ((star T.toCLM) _) = star (inner ℂ _ (T.toCLM _))
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

theorem matrixVectorTrace_gram
    (T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) :
    matrixVectorTrace dims hd U (star T * T) =
      inner ℂ (T (matrixHilbertEmbedding dims hd U 1)) (T (matrixHilbertEmbedding dims hd U 1)) := by
  change inner ℂ _ ((star T.toCLM) (T.toCLM _)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem matrixVectorTrace_mul_comm
    (S T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U)
    (hS : S ∈ matrixWOTAlgebra dims hd U) (hT : T ∈ matrixWOTAlgebra dims hd U) :
    matrixVectorTrace dims hd U (S * T) = matrixVectorTrace dims hd U (T * S) := by
  change S ∈ closure ((matrixLeftWOTRepresentation dims hd U).range : Set _) at hS
  change T ∈ closure ((matrixLeftWOTRepresentation dims hd U).range : Set _) at hT
  have hc := matrixVectorTrace_continuous dims hd U
  apply (closure_minimal (t := {S | matrixVectorTrace dims hd U (S * T) =
    matrixVectorTrace dims hd U (T * S)}) ?_
      (isClosed_eq (hc.comp (continuous_mul_const T)) (hc.comp (continuous_const_mul T)))) hS
  rintro _ ⟨a, rfl⟩
  apply (closure_minimal (t := {T | matrixVectorTrace dims hd U
      (matrixLeftWOTRepresentation dims hd U a * T) =
    matrixVectorTrace dims hd U (T * matrixLeftWOTRepresentation dims hd U a)}) ?_
      (isClosed_eq (hc.comp (continuous_const_mul _)) (hc.comp (continuous_mul_const _)))) hT
  rintro _ ⟨b, rfl⟩
  change matrixVectorTrace dims hd U
    (matrixLeftWOTRepresentation dims hd U a * matrixLeftWOTRepresentation dims hd U b) =
      matrixVectorTrace dims hd U
        (matrixLeftWOTRepresentation dims hd U b * matrixLeftWOTRepresentation dims hd U a)
  rw [← map_mul, ← map_mul, matrixVectorTrace_representation, matrixVectorTrace_representation,
    matrixUltratrace_mul_comm]

noncomputable def matrixWOTTrace : MatrixWOTClosure dims hd U →L[ℂ] ℂ where
  toFun T := matrixVectorTrace dims hd U T.val
  map_add' S T := (matrixVectorTrace dims hd U).map_add S.val T.val
  map_smul' c T := (matrixVectorTrace dims hd U).map_smul c T.val
  cont := (matrixVectorTrace_continuous dims hd U).comp continuous_subtype_val

@[simp] theorem matrixWOTTrace_one : matrixWOTTrace dims hd U 1 = 1 := matrixVectorTrace_one dims hd U

theorem matrixWOTTrace_embedding (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixWOTTrace dims hd U (matrixWOTEmbedding dims hd U x) = matrixUltratrace dims hd U x :=
  matrixVectorTrace_representation dims hd U x

theorem matrixWOTTrace_star (T : MatrixWOTClosure dims hd U) :
    matrixWOTTrace dims hd U (star T) = star (matrixWOTTrace dims hd U T) :=
  matrixVectorTrace_star dims hd U T.val

theorem matrixWOTTrace_mul_comm (S T : MatrixWOTClosure dims hd U) :
    matrixWOTTrace dims hd U (S * T) = matrixWOTTrace dims hd U (T * S) :=
  matrixVectorTrace_mul_comm dims hd U S.val T.val S.property T.property

theorem matrixWOTTrace_gram_nonneg (T : MatrixWOTClosure dims hd U) :
    0 ≤ (matrixWOTTrace dims hd U (star T * T)).re := by
  change 0 ≤ (matrixVectorTrace dims hd U (star T.val * T.val)).re
  rw [matrixVectorTrace_gram]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem matrixWOTTrace_gram_im (T : MatrixWOTClosure dims hd U) :
    (matrixWOTTrace dims hd U (star T * T)).im = 0 := by
  change (matrixVectorTrace dims hd U (star T.val * T.val)).im = 0
  rw [matrixVectorTrace_gram]
  exact inner_self_im (𝕜 := ℂ) (T.val (matrixHilbertEmbedding dims hd U 1))

theorem matrixWOTTrace_faithful (T : MatrixWOTClosure dims hd U) :
    matrixWOTTrace dims hd U (star T * T) = 0 ↔ T = 0 := by
  constructor
  · intro hT
    change matrixVectorTrace dims hd U (star T.val * T.val) = 0 at hT
    rw [matrixVectorTrace_gram, inner_self_eq_zero] at hT
    exact Subtype.ext (matrixWOT_separating dims hd U T.val T.property hT)
  · rintro rfl
    simp only [mul_zero, map_zero]

end ThomGame.Analysis
