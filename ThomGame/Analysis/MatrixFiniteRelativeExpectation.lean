module

public import ThomGame.Analysis.MatrixRelativeExpectation
public import ThomGame.Analysis.MatrixFiniteExpectation

/-!
# The relative-commutant conditional expectation on the finite algebra

The actual quotient expectation transports to the entire generated
finite operator algebra. Its range is the common commutant of the
specified tuple, a closed star subalgebra. Trace pairing proves
positivity; bimodularity gives Schwarz and norm-one continuity.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable (dims : Nat → Nat) {h : Nat} [NeZero h]
  (V : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop)

omit [NeZero h] in
noncomputable def matrixFiniteRelativeCommutant : StarSubalgebra ℂ (MatrixFiniteOperatorAlgebra dims hd U) :=
  StarSubalgebra.centralizer ℂ (Set.range (matrixFiniteEmbedding dims hd U ∘ matrixTupleClass dims V (U : Filter Nat)))

omit [NeZero h] in
instance matrixFiniteRelativeCommutant_isClosed :
    IsClosed (matrixFiniteRelativeCommutant dims V hd U : Set (MatrixFiniteOperatorAlgebra dims hd U)) :=
  Set.isClosed_centralizer _

noncomputable def matrixFiniteRelativeExpectation :
    MatrixFiniteOperatorAlgebra dims hd U →ₗ[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  (matrixFiniteEmbedding dims hd U).toAlgHom.toLinearMap.comp
    ((matrixRelativeExpectation dims V hd U hU).comp
      (matrixFiniteEquiv dims hd U hU).symm.toAlgEquiv.toLinearEquiv.toLinearMap)

@[simp] theorem matrixFiniteRelativeExpectation_embedding (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    matrixFiniteRelativeExpectation dims V hd U hU (matrixFiniteEmbedding dims hd U x) =
      matrixFiniteEmbedding dims hd U (matrixRelativeExpectation dims V hd U hU x) := by
  change matrixFiniteEmbedding dims hd U
    (matrixRelativeExpectation dims V hd U hU
      ((matrixFiniteEquiv dims hd U hU).symm (matrixFiniteEquiv dims hd U hU x))) = _
  rw [(matrixFiniteEquiv dims hd U hU).symm_apply_apply]

omit [NeZero h] in
theorem matrixFiniteEmbedding_mem_relativeCommutant_iff (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    matrixFiniteEmbedding dims hd U x ∈ matrixFiniteRelativeCommutant dims V hd U ↔
      x ∈ matrixRelativeCommutant dims V (U : Filter Nat) := by
  simp only [matrixFiniteRelativeCommutant, matrixRelativeCommutant,
    StarSubalgebra.mem_centralizer_iff, Set.forall_mem_range, Function.comp_apply,
    ← map_star, ← map_mul, (matrixFiniteEmbedding_injective dims hd U).eq_iff]

theorem matrixFiniteRelativeExpectation_mem (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRelativeExpectation dims V hd U hU T ∈ matrixFiniteRelativeCommutant dims V hd U := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [matrixFiniteRelativeExpectation_embedding, matrixFiniteEmbedding_mem_relativeCommutant_iff]
  exact matrixRelativeExpectation_mem dims V hd U hU x

theorem matrixFiniteRelativeExpectation_eq_self (T : MatrixFiniteOperatorAlgebra dims hd U)
    (hT : T ∈ matrixFiniteRelativeCommutant dims V hd U) : matrixFiniteRelativeExpectation dims V hd U hU T = T := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [matrixFiniteRelativeExpectation_embedding, matrixRelativeExpectation_eq_self dims V hd U hU x
    ((matrixFiniteEmbedding_mem_relativeCommutant_iff dims V hd U x).mp hT)]

theorem matrixFiniteRelativeExpectation_eq_self_iff (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRelativeExpectation dims V hd U hU T = T ↔ T ∈ matrixFiniteRelativeCommutant dims V hd U :=
  ⟨fun h => h ▸ matrixFiniteRelativeExpectation_mem dims V hd U hU T,
    matrixFiniteRelativeExpectation_eq_self dims V hd U hU T⟩

theorem matrixFiniteRelativeExpectation_range :
    LinearMap.range (matrixFiniteRelativeExpectation dims V hd U hU) =
      (matrixFiniteRelativeCommutant dims V hd U).toSubalgebra.toSubmodule := by
  ext T
  constructor
  · rintro ⟨X, rfl⟩
    exact matrixFiniteRelativeExpectation_mem dims V hd U hU X
  · intro hT
    exact ⟨T, matrixFiniteRelativeExpectation_eq_self dims V hd U hU T hT⟩

@[simp] theorem matrixFiniteRelativeExpectation_one : matrixFiniteRelativeExpectation dims V hd U hU 1 = 1 :=
  matrixFiniteRelativeExpectation_eq_self dims V hd U hU 1 (matrixFiniteRelativeCommutant dims V hd U).one_mem

@[simp] theorem matrixFiniteRelativeExpectation_idem (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRelativeExpectation dims V hd U hU (matrixFiniteRelativeExpectation dims V hd U hU T) =
      matrixFiniteRelativeExpectation dims V hd U hU T :=
  matrixFiniteRelativeExpectation_eq_self dims V hd U hU _ (matrixFiniteRelativeExpectation_mem dims V hd U hU T)

@[simp] theorem matrixFiniteRelativeExpectation_star (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRelativeExpectation dims V hd U hU (star T) = star (matrixFiniteRelativeExpectation dims V hd U hU T) := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [← map_star, matrixFiniteRelativeExpectation_embedding, matrixRelativeExpectation_star, map_star,
    matrixFiniteRelativeExpectation_embedding]

theorem matrixFiniteRelativeExpectation_mul_left (A T : MatrixFiniteOperatorAlgebra dims hd U)
    (hA : A ∈ matrixFiniteRelativeCommutant dims V hd U) :
    matrixFiniteRelativeExpectation dims V hd U hU (A * T) = A * matrixFiniteRelativeExpectation dims V hd U hU T := by
  obtain ⟨a, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU A
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [← map_mul, matrixFiniteRelativeExpectation_embedding,
    matrixRelativeExpectation_mul_left dims V hd U hU a x
      ((matrixFiniteEmbedding_mem_relativeCommutant_iff dims V hd U a).mp hA),
    map_mul, matrixFiniteRelativeExpectation_embedding]

theorem matrixFiniteRelativeExpectation_mul_right (T A : MatrixFiniteOperatorAlgebra dims hd U)
    (hA : A ∈ matrixFiniteRelativeCommutant dims V hd U) :
    matrixFiniteRelativeExpectation dims V hd U hU (T * A) = matrixFiniteRelativeExpectation dims V hd U hU T * A := by
  obtain ⟨a, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU A
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [← map_mul, matrixFiniteRelativeExpectation_embedding,
    matrixRelativeExpectation_mul_right dims V hd U hU x a
      ((matrixFiniteEmbedding_mem_relativeCommutant_iff dims V hd U a).mp hA),
    map_mul, matrixFiniteRelativeExpectation_embedding]

theorem matrixFiniteRelativeExpectation_bimodule (A T B : MatrixFiniteOperatorAlgebra dims hd U)
    (hA : A ∈ matrixFiniteRelativeCommutant dims V hd U) (hB : B ∈ matrixFiniteRelativeCommutant dims V hd U) :
    matrixFiniteRelativeExpectation dims V hd U hU (A * T * B) = A * matrixFiniteRelativeExpectation dims V hd U hU T * B := by
  rw [matrixFiniteRelativeExpectation_mul_right dims V hd U hU _ B hB,
    matrixFiniteRelativeExpectation_mul_left dims V hd U hU A T hA]

theorem matrixFiniteRelativeExpectation_trace (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteTrace dims hd U (matrixFiniteRelativeExpectation dims V hd U hU T) = matrixFiniteTrace dims hd U T := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [matrixFiniteRelativeExpectation_embedding, matrixFiniteTrace_embedding, matrixFiniteTrace_embedding,
    matrixRelativeExpectation_trace]

theorem matrixFiniteRelativeExpectation_pairing (T B : MatrixFiniteOperatorAlgebra dims hd U)
    (hB : B ∈ matrixFiniteRelativeCommutant dims V hd U) :
    matrixFiniteTrace dims hd U (star B * matrixFiniteRelativeExpectation dims V hd U hU T) =
      matrixFiniteTrace dims hd U (star B * T) := by
  rw [← matrixFiniteRelativeExpectation_mul_left dims V hd U hU (star B) T
    ((matrixFiniteRelativeCommutant dims V hd U).star_mem' hB), matrixFiniteRelativeExpectation_trace]

theorem matrixFiniteRelativeExpectation_vector (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteVector dims hd U (matrixFiniteRelativeExpectation dims V hd U hU T) =
      matrixMarkovProjection dims V hd U (matrixFiniteVector dims hd U T) := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [matrixFiniteRelativeExpectation_embedding, matrixFiniteVector_embedding, matrixFiniteVector_embedding,
    matrixRelativeExpectation_embedding]

theorem matrixFiniteRelativeExpectation_nonneg (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : 0 ≤ T) :
    0 ≤ matrixFiniteRelativeExpectation dims V hd U hU T := by
  exact trace_projection_nonneg (matrixFiniteRealTrace dims hd U)
    (matrixFiniteRealTrace_nonneg dims hd U) (matrixFiniteRealTrace_mul_comm dims hd U)
    (fun a => (matrixFiniteRealTrace_faithful dims hd U a).mp)
    (matrixFiniteRelativeCommutant dims V hd U) (matrixFiniteRelativeExpectation dims V hd U hU)
    (matrixFiniteRelativeExpectation_mem dims V hd U hU) (matrixFiniteRelativeExpectation_star dims V hd U hU)
    (fun a b hb => congrArg Complex.re (matrixFiniteRelativeExpectation_pairing dims V hd U hU a b hb)) T hT

noncomputable def matrixFiniteRelativePositiveExpectation :
    MatrixFiniteOperatorAlgebra dims hd U →ₚ[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  PositiveLinearMap.mk₀ (matrixFiniteRelativeExpectation dims V hd U hU) (matrixFiniteRelativeExpectation_nonneg dims V hd U hU)

theorem matrixFiniteRelativeExpectation_monotone : Monotone (matrixFiniteRelativeExpectation dims V hd U hU) :=
  (matrixFiniteRelativePositiveExpectation dims V hd U hU).monotone

set_option maxHeartbeats 800000 in
theorem matrixFiniteRelativeExpectation_schwarz (T : MatrixFiniteOperatorAlgebra dims hd U) :
    star (matrixFiniteRelativeExpectation dims V hd U hU T) * matrixFiniteRelativeExpectation dims V hd U hU T ≤
      matrixFiniteRelativeExpectation dims V hd U hU (star T * T) := by
  have hp := matrixFiniteRelativeExpectation_nonneg dims V hd U hU _
    (star_mul_self_nonneg (T - matrixFiniteRelativeExpectation dims V hd U hU T))
  have hm := matrixFiniteRelativeExpectation_mem dims V hd U hU T
  rw [star_sub, sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub,
    matrixFiniteRelativeExpectation_mul_right dims V hd U hU _ _ hm,
    matrixFiniteRelativeExpectation_mul_left dims V hd U hU _ _ ((matrixFiniteRelativeCommutant dims V hd U).star_mem' hm),
    matrixFiniteRelativeExpectation_eq_self dims V hd U hU _
      ((matrixFiniteRelativeCommutant dims V hd U).mul_mem ((matrixFiniteRelativeCommutant dims V hd U).star_mem' hm) hm),
    matrixFiniteRelativeExpectation_star] at hp
  simpa only [sub_self, sub_zero, sub_nonneg] using hp

theorem matrixFiniteRelativeExpectation_norm_le (T : MatrixFiniteOperatorAlgebra dims hd U) :
    ‖matrixFiniteRelativeExpectation dims V hd U hU T‖ ≤ ‖T‖ :=
  norm_le_of_unital_schwarz (matrixFiniteRelativePositiveExpectation dims V hd U hU)
    (matrixFiniteRelativeExpectation_one dims V hd U hU) (matrixFiniteRelativeExpectation_schwarz dims V hd U hU) T

noncomputable def matrixFiniteRelativeExpectationCLM :
    MatrixFiniteOperatorAlgebra dims hd U →L[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  (matrixFiniteRelativeExpectation dims V hd U hU).mkContinuous 1
    (fun T => by simpa only [one_mul] using matrixFiniteRelativeExpectation_norm_le dims V hd U hU T)

@[simp] theorem matrixFiniteRelativeExpectationCLM_apply (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRelativeExpectationCLM dims V hd U hU T = matrixFiniteRelativeExpectation dims V hd U hU T := rfl

theorem matrixFiniteRelativeExpectationCLM_norm : ‖matrixFiniteRelativeExpectationCLM dims V hd U hU‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun T => by simpa only [matrixFiniteRelativeExpectationCLM_apply, one_mul] using
        matrixFiniteRelativeExpectation_norm_le dims V hd U hU T)
  · have h := (matrixFiniteRelativeExpectationCLM dims V hd U hU).le_opNorm (1 : MatrixFiniteOperatorAlgebra dims hd U)
    simpa only [matrixFiniteRelativeExpectationCLM_apply, matrixFiniteRelativeExpectation_one, norm_one, mul_one] using h

end ThomGame.Analysis
