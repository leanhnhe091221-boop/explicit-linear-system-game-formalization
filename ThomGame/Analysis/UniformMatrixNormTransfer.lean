module

public import ThomGame.Analysis.MatrixMixedNorm
public import ThomGame.Analysis.UniformMatrixMapOperators

/-!
# Uniform transfer of the operator-to-trace norm

The actual induced map's infinity-to-two norm equals the ultralimit of
the coordinate mixed norms. Exact contraction representatives give one
inequality; coordinate maximizing contractions give the other.
-/

@[expose] public section
namespace ThomGame.Analysis.UniformMatrixMap

open Filter
open scoped Topology

variable {ι : Type*} {dims : ι → Nat} (F : UniformMatrixMap dims)
  (hd : ∀ i, 0 < dims i)

noncomputable def coordinateMixedNorm (i : ι) : ℝ := by
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixMixedNorm (F.toLinearMap i)

theorem coordinateMixedNorm_nonneg (i : ι) : 0 ≤ F.coordinateMixedNorm hd i := by
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixMixedNorm_nonneg (F.toLinearMap i)

theorem coordinateMixedNorm_le (i : ι) : F.coordinateMixedNorm hd i ≤ F.operatorBound := by
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixMixedNorm_le (F.toLinearMap i) F.operatorBound F.operatorBound.2
    (fun X => (hsNorm_le_matrixOpNorm _).trans (F.operator_le i X))

theorem hsNorm_apply_le_coordinateMixedNorm (i : ι) (X : CMatrix (dims i)) :
    hsNorm (F.toLinearMap i X) ≤ F.coordinateMixedNorm hd i * matrixOpNorm X := by
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact hsNorm_apply_le_matrixMixedNorm (F.toLinearMap i) X

theorem exists_maximizingSequence : ∃ A : BoundedMatrixSequence dims,
    (∀ i, matrixOpNorm (A.val i) ≤ 1) ∧
    (∀ i, hsNorm (F.toLinearMap i (A.val i)) = F.coordinateMixedNorm hd i) := by
  classical
  have hx (i : ι) : ∃ X : CMatrix (dims i), matrixOpNorm X ≤ 1 ∧
      hsNorm (F.toLinearMap i X) = F.coordinateMixedNorm hd i := by
    let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
    exact exists_matrixMixedNorm_maximizer (F.toLinearMap i)
  choose X hX hFX using hx
  exact ⟨⟨X, 1, zero_le_one, hX⟩, hX, hFX⟩

noncomputable def mixedNormLimit (U : Ultrafilter ι) : ℝ :=
  limUnder (U : Filter ι) (F.coordinateMixedNorm hd)

theorem coordinateMixedNorm_tendsto (U : Ultrafilter ι) :
    Tendsto (F.coordinateMixedNorm hd) (U : Filter ι) (𝓝 (F.mixedNormLimit hd U)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨z, _, hz⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (F.operatorBound : ℝ))).ultrafilter_le_nhds
    (U.map (F.coordinateMixedNorm hd)) (le_principal_iff.mpr (by
      change ∀ᶠ i in (U : Filter ι), F.coordinateMixedNorm hd i ∈ Set.Icc 0 (F.operatorBound : ℝ)
      exact Eventually.of_forall (fun i => ⟨F.coordinateMixedNorm_nonneg hd i, F.coordinateMixedNorm_le hd i⟩)))
  exact ⟨z, hz⟩

theorem mixedNormLimit_nonneg (U : Ultrafilter ι) : 0 ≤ F.mixedNormLimit hd U :=
  ge_of_tendsto' (F.coordinateMixedNorm_tendsto hd U) (F.coordinateMixedNorm_nonneg hd)

theorem mixedNormLimit_le (U : Ultrafilter ι) : F.mixedNormLimit hd U ≤ F.operatorBound :=
  le_of_tendsto' (F.coordinateMixedNorm_tendsto hd U) (F.coordinateMixedNorm_le hd)

section NatIndex

variable {dims : Nat → Nat} (F : UniformMatrixMap dims)
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop)

theorem finiteToHilbert_apply_norm_le_limit (T : MatrixFiniteOperatorAlgebra dims hd U) :
    ‖F.finiteToHilbert hd U hU T‖ ≤ F.mixedNormLimit hd U * ‖T‖ := by
  obtain ⟨A, hA, hAT⟩ := exists_matrixFiniteRepresentative_bounded dims hd U hU T ‖T‖ (norm_nonneg _) le_rfl
  have he : F.finiteToHilbert hd U hU T =
      matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) (F.sequenceMap A)) := by
    rw [← hAT, finiteToHilbert_embedding, quotientMap_mk]
  rw [he]
  apply le_of_tendsto_of_tendsto' (matrixHilbertEmbedding_norm_tendsto dims hd U (F.sequenceMap A))
    ((F.coordinateMixedNorm_tendsto hd U).mul_const ‖T‖)
  intro i
  exact (F.hsNorm_apply_le_coordinateMixedNorm hd i (A.val i)).trans
    (mul_le_mul_of_nonneg_left (hA i) (F.coordinateMixedNorm_nonneg hd i))

theorem finiteToHilbert_norm_eq_limit : ‖F.finiteToHilbert hd U hU‖ = F.mixedNormLimit hd U := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (F.mixedNormLimit_nonneg hd U)
      (F.finiteToHilbert_apply_norm_le_limit hd U hU)
  · obtain ⟨A, hA, hFA⟩ := F.exists_maximizingSequence hd
    have he : F.mixedNormLimit hd U =
        ‖F.finiteToHilbert hd U hU (matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) A))‖ := by
      rw [finiteToHilbert_embedding, quotientMap_mk]
      apply tendsto_nhds_unique (F.coordinateMixedNorm_tendsto hd U)
      have ht := matrixHilbertEmbedding_norm_tendsto dims hd U (F.sequenceMap A)
      change Tendsto (fun i => hsNorm (F.toLinearMap i (A.val i))) _ _ at ht
      simpa only [hFA] using ht
    have hunit : ‖matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) A)‖ ≤ 1 := by
      rw [matrixFiniteEmbedding_norm]
      exact matrixLeftRepresentation_norm_le dims hd U A 1 zero_le_one hA
    rw [he]
    exact ((F.finiteToHilbert hd U hU).le_opNorm _).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit (norm_nonneg (F.finiteToHilbert hd U hU)))

theorem coordinateMixedNorm_tendsto_norm :
    Tendsto (F.coordinateMixedNorm hd) (U : Filter Nat) (𝓝 ‖F.finiteToHilbert hd U hU‖) := by
  rw [finiteToHilbert_norm_eq_limit]
  exact F.coordinateMixedNorm_tendsto hd U

include hU in
theorem quotientMap_eq_zero_iff_mixedNorm_tendsto_zero :
    F.quotientMap (U : Filter Nat) = 0 ↔ Tendsto (F.coordinateMixedNorm hd) (U : Filter Nat) (𝓝 0) := by
  have hzero : F.quotientMap (U : Filter Nat) = 0 ↔ F.finiteToHilbert hd U hU = 0 := by
    constructor
    · intro h
      apply ContinuousLinearMap.ext
      intro T
      obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
      simp only [finiteToHilbert_embedding, h, LinearMap.zero_apply, map_zero, _root_.zero_apply]
    · intro h
      apply LinearMap.ext
      intro x
      apply matrixHilbertEmbedding_injective dims hd U
      have he := congrArg (fun P : MatrixFiniteOperatorAlgebra dims hd U →L[ℂ] MatrixTraceHilbert dims hd U =>
        P (matrixFiniteEmbedding dims hd U x)) h
      simpa only [finiteToHilbert_embedding, _root_.zero_apply, LinearMap.zero_apply, map_zero] using he
  rw [hzero]
  constructor
  · intro h
    simpa only [h, ContinuousLinearMap.opNorm_zero] using F.coordinateMixedNorm_tendsto_norm hd U hU
  · intro h
    exact (ContinuousLinearMap.opNorm_zero_iff _).mp
      (tendsto_nhds_unique (F.coordinateMixedNorm_tendsto_norm hd U hU) h)

include hU in
theorem quotientMap_eq_iff_mixedNorm_sub_tendsto_zero (G : UniformMatrixMap dims) :
    F.quotientMap (U : Filter Nat) = G.quotientMap (U : Filter Nat) ↔
      Tendsto ((F.sub G).coordinateMixedNorm hd) (U : Filter Nat) (𝓝 0) := by
  have he : (F.sub G).quotientMap (U : Filter Nat) =
      F.quotientMap (U : Filter Nat) - G.quotientMap (U : Filter Nat) := by
    apply LinearMap.ext
    intro x
    exact F.sub_quotientMap G (U : Filter Nat) x
  rw [← (F.sub G).quotientMap_eq_zero_iff_mixedNorm_tendsto_zero hd U hU, he, sub_eq_zero]

end NatIndex
end ThomGame.Analysis.UniformMatrixMap
