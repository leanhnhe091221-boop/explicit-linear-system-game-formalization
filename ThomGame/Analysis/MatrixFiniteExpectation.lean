module

public import ThomGame.Analysis.TraceProjectionPositivity
public import ThomGame.Analysis.MatrixHilbertExpectation
public import ThomGame.Analysis.MatrixInternalFiniteAlgebra
public import ThomGame.Analysis.MatrixQuotientWOTIdentification

/-!
# Conditional expectations on the concrete finite operator algebra

The proved matrix quotient equivalence transports the coordinate map to
the entire generated finite algebra. Its range is the actual internal
subalgebra. Trace pairing, positivity, Schwarz, and operator norm
contraction are proved for this concrete operator-algebra map.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable (dims : Nat → Nat) (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop)

noncomputable def matrixFiniteExpectation :
    MatrixFiniteOperatorAlgebra dims hd U →ₗ[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  (matrixFiniteEmbedding dims hd U).toAlgHom.toLinearMap.comp
    ((matrixQuotientExpectation dims S hd (U : Filter Nat)).comp
      (matrixFiniteEquiv dims hd U hU).symm.toAlgEquiv.toLinearEquiv.toLinearMap)

@[simp] theorem matrixFiniteExpectation_embedding (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    matrixFiniteExpectation dims S hd U hU (matrixFiniteEmbedding dims hd U x) =
      matrixFiniteEmbedding dims hd U (matrixQuotientExpectation dims S hd (U : Filter Nat) x) := by
  change matrixFiniteEmbedding dims hd U
    (matrixQuotientExpectation dims S hd (U : Filter Nat)
      ((matrixFiniteEquiv dims hd U hU).symm (matrixFiniteEquiv dims hd U hU x))) = _
  rw [(matrixFiniteEquiv dims hd U hU).symm_apply_apply]

theorem matrixFiniteEmbedding_mem_internal_iff (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    matrixFiniteEmbedding dims hd U x ∈ matrixInternalFiniteAlgebra dims S hd U ↔
      x ∈ matrixInternalQuotient dims S (U : Filter Nat) := by
  constructor
  · rintro ⟨y, hy, heq⟩
    exact matrixFiniteEmbedding_injective dims hd U heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem matrixFiniteExpectation_mem (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteExpectation dims S hd U hU T ∈ matrixInternalFiniteAlgebra dims S hd U := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [matrixFiniteExpectation_embedding, matrixFiniteEmbedding_mem_internal_iff]
  exact matrixQuotientExpectation_mem dims S hd (U : Filter Nat) x

theorem matrixFiniteExpectation_eq_self (T : MatrixFiniteOperatorAlgebra dims hd U)
    (hT : T ∈ matrixInternalFiniteAlgebra dims S hd U) : matrixFiniteExpectation dims S hd U hU T = T := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [matrixFiniteExpectation_embedding, matrixQuotientExpectation_eq_self dims S hd (U : Filter Nat) x
    ((matrixFiniteEmbedding_mem_internal_iff dims S hd U x).mp hT)]

theorem matrixFiniteExpectation_eq_self_iff (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteExpectation dims S hd U hU T = T ↔ T ∈ matrixInternalFiniteAlgebra dims S hd U :=
  ⟨fun h => h ▸ matrixFiniteExpectation_mem dims S hd U hU T,
    matrixFiniteExpectation_eq_self dims S hd U hU T⟩

theorem matrixFiniteExpectation_range :
    LinearMap.range (matrixFiniteExpectation dims S hd U hU) =
      (matrixInternalFiniteAlgebra dims S hd U).toSubalgebra.toSubmodule := by
  ext T
  constructor
  · rintro ⟨X, rfl⟩
    exact matrixFiniteExpectation_mem dims S hd U hU X
  · intro hT
    exact ⟨T, matrixFiniteExpectation_eq_self dims S hd U hU T hT⟩

@[simp] theorem matrixFiniteExpectation_one : matrixFiniteExpectation dims S hd U hU 1 = 1 :=
  matrixFiniteExpectation_eq_self dims S hd U hU 1 (matrixInternalFiniteAlgebra dims S hd U).one_mem

@[simp] theorem matrixFiniteExpectation_idem (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteExpectation dims S hd U hU (matrixFiniteExpectation dims S hd U hU T) =
      matrixFiniteExpectation dims S hd U hU T :=
  matrixFiniteExpectation_eq_self dims S hd U hU _ (matrixFiniteExpectation_mem dims S hd U hU T)

@[simp] theorem matrixFiniteExpectation_star (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteExpectation dims S hd U hU (star T) = star (matrixFiniteExpectation dims S hd U hU T) := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [← map_star, matrixFiniteExpectation_embedding, matrixQuotientExpectation_star, map_star,
    matrixFiniteExpectation_embedding]

theorem matrixFiniteExpectation_mul_left (A T : MatrixFiniteOperatorAlgebra dims hd U)
    (hA : A ∈ matrixInternalFiniteAlgebra dims S hd U) :
    matrixFiniteExpectation dims S hd U hU (A * T) = A * matrixFiniteExpectation dims S hd U hU T := by
  obtain ⟨a, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU A
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [← map_mul, matrixFiniteExpectation_embedding,
    matrixQuotientExpectation_mul_left dims S hd (U : Filter Nat) a x
      ((matrixFiniteEmbedding_mem_internal_iff dims S hd U a).mp hA),
    map_mul, matrixFiniteExpectation_embedding]

theorem matrixFiniteExpectation_mul_right (T A : MatrixFiniteOperatorAlgebra dims hd U)
    (hA : A ∈ matrixInternalFiniteAlgebra dims S hd U) :
    matrixFiniteExpectation dims S hd U hU (T * A) = matrixFiniteExpectation dims S hd U hU T * A := by
  obtain ⟨a, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU A
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [← map_mul, matrixFiniteExpectation_embedding,
    matrixQuotientExpectation_mul_right dims S hd (U : Filter Nat) x a
      ((matrixFiniteEmbedding_mem_internal_iff dims S hd U a).mp hA),
    map_mul, matrixFiniteExpectation_embedding]

theorem matrixFiniteExpectation_bimodule (A T B : MatrixFiniteOperatorAlgebra dims hd U)
    (hA : A ∈ matrixInternalFiniteAlgebra dims S hd U) (hB : B ∈ matrixInternalFiniteAlgebra dims S hd U) :
    matrixFiniteExpectation dims S hd U hU (A * T * B) = A * matrixFiniteExpectation dims S hd U hU T * B := by
  rw [matrixFiniteExpectation_mul_right dims S hd U hU _ B hB,
    matrixFiniteExpectation_mul_left dims S hd U hU A T hA]

theorem matrixFiniteExpectation_trace (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteTrace dims hd U (matrixFiniteExpectation dims S hd U hU T) = matrixFiniteTrace dims hd U T := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [matrixFiniteExpectation_embedding, matrixFiniteTrace_embedding, matrixFiniteTrace_embedding,
    matrixQuotientExpectation_trace]

theorem matrixFiniteExpectation_pairing (T B : MatrixFiniteOperatorAlgebra dims hd U)
    (hB : B ∈ matrixInternalFiniteAlgebra dims S hd U) :
    matrixFiniteTrace dims hd U (star B * matrixFiniteExpectation dims S hd U hU T) =
      matrixFiniteTrace dims hd U (star B * T) := by
  rw [← matrixFiniteExpectation_mul_left dims S hd U hU (star B) T
    ((matrixInternalFiniteAlgebra dims S hd U).star_mem' hB), matrixFiniteExpectation_trace]

theorem matrixFiniteExpectation_vector (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteVector dims hd U (matrixFiniteExpectation dims S hd U hU T) =
      matrixHilbertExpectation dims S hd U (matrixFiniteVector dims hd U T) := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [matrixFiniteExpectation_embedding, matrixFiniteVector_embedding, matrixFiniteVector_embedding,
    matrixHilbertExpectation_embedding]

theorem matrixFiniteRealTrace_faithful (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRealTrace dims hd U (star T * T) = 0 ↔ T = 0 := by
  rw [matrixFiniteRealTrace_gram, sq_eq_zero_iff, norm_eq_zero, matrixFiniteVector_eq_zero_iff]

theorem matrixFiniteExpectation_nonneg (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : 0 ≤ T) :
    0 ≤ matrixFiniteExpectation dims S hd U hU T := by
  let : IsClosed (matrixInternalFiniteAlgebra dims S hd U : Set (MatrixFiniteOperatorAlgebra dims hd U)) :=
    matrixInternalFiniteAlgebra_isClosed dims S hd U hU
  exact trace_projection_nonneg (matrixFiniteRealTrace dims hd U)
    (matrixFiniteRealTrace_nonneg dims hd U) (matrixFiniteRealTrace_mul_comm dims hd U)
    (fun a => (matrixFiniteRealTrace_faithful dims hd U a).mp)
    (matrixInternalFiniteAlgebra dims S hd U) (matrixFiniteExpectation dims S hd U hU)
    (matrixFiniteExpectation_mem dims S hd U hU) (matrixFiniteExpectation_star dims S hd U hU)
    (fun a b hb => congrArg Complex.re (matrixFiniteExpectation_pairing dims S hd U hU a b hb)) T hT

noncomputable def matrixFinitePositiveExpectation :
    MatrixFiniteOperatorAlgebra dims hd U →ₚ[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  PositiveLinearMap.mk₀ (matrixFiniteExpectation dims S hd U hU) (matrixFiniteExpectation_nonneg dims S hd U hU)

theorem matrixFiniteExpectation_monotone : Monotone (matrixFiniteExpectation dims S hd U hU) :=
  (matrixFinitePositiveExpectation dims S hd U hU).monotone

set_option maxHeartbeats 800000 in
theorem matrixFiniteExpectation_schwarz (T : MatrixFiniteOperatorAlgebra dims hd U) :
    star (matrixFiniteExpectation dims S hd U hU T) * matrixFiniteExpectation dims S hd U hU T ≤
      matrixFiniteExpectation dims S hd U hU (star T * T) := by
  have hp := matrixFiniteExpectation_nonneg dims S hd U hU _
    (star_mul_self_nonneg (T - matrixFiniteExpectation dims S hd U hU T))
  have hm := matrixFiniteExpectation_mem dims S hd U hU T
  rw [star_sub, sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub,
    matrixFiniteExpectation_mul_right dims S hd U hU _ _ hm,
    matrixFiniteExpectation_mul_left dims S hd U hU _ _ ((matrixInternalFiniteAlgebra dims S hd U).star_mem' hm),
    matrixFiniteExpectation_eq_self dims S hd U hU _
      ((matrixInternalFiniteAlgebra dims S hd U).mul_mem ((matrixInternalFiniteAlgebra dims S hd U).star_mem' hm) hm),
    matrixFiniteExpectation_star] at hp
  simpa only [sub_self, sub_zero, sub_nonneg] using hp

theorem matrixFiniteExpectation_norm_le (T : MatrixFiniteOperatorAlgebra dims hd U) :
    ‖matrixFiniteExpectation dims S hd U hU T‖ ≤ ‖T‖ :=
  norm_le_of_unital_schwarz (matrixFinitePositiveExpectation dims S hd U hU)
    (matrixFiniteExpectation_one dims S hd U hU) (matrixFiniteExpectation_schwarz dims S hd U hU) T

noncomputable def matrixFiniteExpectationCLM :
    MatrixFiniteOperatorAlgebra dims hd U →L[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  (matrixFiniteExpectation dims S hd U hU).mkContinuous 1
    (fun T => by simpa only [one_mul] using matrixFiniteExpectation_norm_le dims S hd U hU T)

@[simp] theorem matrixFiniteExpectationCLM_apply (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteExpectationCLM dims S hd U hU T = matrixFiniteExpectation dims S hd U hU T := rfl

theorem matrixFiniteExpectationCLM_norm : ‖matrixFiniteExpectationCLM dims S hd U hU‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun T => by simpa only [matrixFiniteExpectationCLM_apply, one_mul] using
        matrixFiniteExpectation_norm_le dims S hd U hU T)
  · have h := (matrixFiniteExpectationCLM dims S hd U hU).le_opNorm (1 : MatrixFiniteOperatorAlgebra dims hd U)
    simpa only [matrixFiniteExpectationCLM_apply, matrixFiniteExpectation_one, norm_one, mul_one] using h

end ThomGame.Analysis
