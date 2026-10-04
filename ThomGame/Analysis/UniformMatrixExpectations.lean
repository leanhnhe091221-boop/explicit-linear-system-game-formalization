module

public import ThomGame.Analysis.UniformMatrixNormTransfer
public import ThomGame.Analysis.MatrixFiniteExpectation

/-!
# Uniform maps and internal conditional expectations

Coordinate trace projections have both uniform bounds equal to one.
Their induced maps agree with the concrete expectations already built.
Consequently the vanishing mixed norm criterion applies to expectations
and, for a trace-orthogonal projection, characterizes its internal range.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat)
  (S : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (hd : ∀ i, 0 < dims i)

noncomputable def matrixUniformExpectation : UniformMatrixMap dims := by
  let : ∀ i, NeZero (dims i) := fun i => ⟨Nat.ne_of_gt (hd i)⟩
  exact {
    toLinearMap i := matrixTraceProjection (S i)
    operatorBound := 1
    hilbertBound := 1
    operator_le i X := by simpa only [NNReal.coe_one, one_mul] using
      matrixTraceProjection_matrixOpNorm_le (S i) X
    hilbert_le i X := by simpa only [NNReal.coe_one, one_mul] using
      matrixTraceProjection_hsNorm_le (S i) X }

@[simp] theorem matrixUniformExpectation_apply (i : ι) [NeZero (dims i)] (X : CMatrix (dims i)) :
    (matrixUniformExpectation dims S hd).toLinearMap i X = matrixTraceProjection (S i) X := rfl

theorem matrixUniformExpectation_sequenceMap :
    (matrixUniformExpectation dims S hd).sequenceMap = matrixSequenceExpectation dims S hd := by
  apply LinearMap.ext
  intro A
  rfl

theorem matrixUniformExpectation_quotientMap (L : Filter ι) :
    (matrixUniformExpectation dims S hd).quotientMap L = matrixQuotientExpectation dims S hd L := by
  apply LinearMap.ext
  intro x
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
  rfl

theorem matrixUniformExpectation_hilbertMap (U : Ultrafilter ι) :
    (matrixUniformExpectation dims S hd).hilbertMap hd U = matrixHilbertExpectation dims S hd U := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (matrixHilbertEmbedding_dense dims hd U).induction_on ξ ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x
    rw [UniformMatrixMap.hilbertMap_embedding, matrixUniformExpectation_quotientMap,
      matrixHilbertExpectation_embedding]

section NatIndex

variable (dims : Nat → Nat) (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop)

theorem matrixUniformExpectation_finiteMap :
    (matrixUniformExpectation dims S hd).finiteMap hd U hU = matrixFiniteExpectation dims S hd U hU := by
  apply LinearMap.ext
  intro T
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  rw [UniformMatrixMap.finiteMap_embedding, matrixUniformExpectation_quotientMap,
    matrixFiniteExpectation_embedding]

theorem matrixUniformExpectation_finiteCLM :
    (matrixUniformExpectation dims S hd).finiteCLM hd U hU = matrixFiniteExpectationCLM dims S hd U hU := by
  apply ContinuousLinearMap.ext
  intro T
  exact congrArg (fun P => P T) (matrixUniformExpectation_finiteMap dims S hd U hU)

include hU in
theorem quotientMap_eq_expectation_iff_mixedNorm_tendsto_zero (F : UniformMatrixMap dims) :
    F.quotientMap (U : Filter Nat) = matrixQuotientExpectation dims S hd (U : Filter Nat) ↔
      Tendsto ((F.sub (matrixUniformExpectation dims S hd)).coordinateMixedNorm hd)
        (U : Filter Nat) (𝓝 0) := by
  rw [← matrixUniformExpectation_quotientMap]
  exact F.quotientMap_eq_iff_mixedNorm_sub_tendsto_zero hd U hU _

theorem finiteMap_eq_expectation_iff_mixedNorm_tendsto_zero (F : UniformMatrixMap dims) :
    F.finiteMap hd U hU = matrixFiniteExpectation dims S hd U hU ↔
      Tendsto ((F.sub (matrixUniformExpectation dims S hd)).coordinateMixedNorm hd)
        (U : Filter Nat) (𝓝 0) := by
  rw [← quotientMap_eq_expectation_iff_mixedNorm_tendsto_zero dims S hd U hU F]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply matrixFiniteEmbedding_injective dims hd U
    have he := congrArg (fun P => P (matrixFiniteEmbedding dims hd U x)) h
    simpa only [UniformMatrixMap.finiteMap_embedding, matrixFiniteExpectation_embedding] using he
  · intro h
    apply LinearMap.ext
    intro T
    obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
    rw [UniformMatrixMap.finiteMap_embedding, h, matrixFiniteExpectation_embedding]

include hU in
/-- Trace orthogonality is stated against the map's own range, without
assuming that this range is internal. -/
theorem quotientRange_eq_internal_iff_mixedNorm_tendsto_zero (F : UniformMatrixMap dims)
    (hpair : ∀ x y : MatrixTracialQuotient dims (U : Filter Nat),
      matrixUltratrace dims hd U
        (star (F.quotientMap (U : Filter Nat) y) * F.quotientMap (U : Filter Nat) x) =
      matrixUltratrace dims hd U (star (F.quotientMap (U : Filter Nat) y) * x)) :
    LinearMap.range (F.quotientMap (U : Filter Nat)) =
        (matrixInternalQuotient dims S (U : Filter Nat)).toSubalgebra.toSubmodule ↔
      Tendsto ((F.sub (matrixUniformExpectation dims S hd)).coordinateMixedNorm hd)
        (U : Filter Nat) (𝓝 0) := by
  rw [← quotientMap_eq_expectation_iff_mixedNorm_tendsto_zero dims S hd U hU F]
  constructor
  · intro hrange
    apply LinearMap.ext
    intro x
    symm
    apply matrixQuotientExpectation_unique dims S hd U x
    · change F.quotientMap (U : Filter Nat) x ∈
        (matrixInternalQuotient dims S (U : Filter Nat)).toSubalgebra.toSubmodule
      rw [← hrange]
      exact ⟨x, rfl⟩
    · intro b hb
      have hb' : b ∈ LinearMap.range (F.quotientMap (U : Filter Nat)) := by
        rw [hrange]
        exact hb
      obtain ⟨y, rfl⟩ := hb'
      exact hpair x y
  · intro h
    rw [h, matrixQuotientExpectation_range]

end NatIndex
end ThomGame.Analysis
