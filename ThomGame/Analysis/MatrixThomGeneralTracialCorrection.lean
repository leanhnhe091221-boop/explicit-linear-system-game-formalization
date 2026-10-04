module

public import ThomGame.Analysis.MatrixThomGeneralHausdorff

/-!
# General relative tracial correction on the original index set

Only convergence of the nonnegative near-inclusion error is required.
The actual modified Stinespring data give positive corrected dimensions,
exact inclusions, (3.4), a single trace-preserving ambient equivalence,
and the relative assertion for the original common algebra on a large set.
The finite block decomposition and multiplicity estimate (3.3) are separate.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixThomModified_source_support_mem_eventually {ι : Type*}
    (dims : ι → Nat) [∀ i, NeZero (dims i)]
    {A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))} {ε : ι → ℝ}
    (S : MatrixThomModifiedData dims A B D ε) (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) :
    ∀ᶠ i in L, (S i).stableSupport ∈ (S i).stableOriginalAlgebra (A i) := by
  apply (matrixSmallError_eventually_lt_half ε L hε).mono
  intro i hi
  have h := (S i).stableSupport_source_mem
  have hA := congrArg (fun C : StarSubalgebra ℂ (CMatrix (dims i)) => (S i).stableOriginalAlgebra C)
    (matrixSmallErrorAlgebra_eq dims A ε hi)
  rwa [hA] at h

theorem exists_matrixThomGeneralTracialCorrection {ι : Type*}
    (dims : ι → Nat) [∀ i, NeZero (dims i)]
    (A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))
    (hDA : ∀ i, D i ≤ A i) (hDB : ∀ i, D i ≤ B i)
    (U : Ultrafilter ι) {ε : ι → ℝ} (hε : Tendsto ε (U : Filter ι) (𝓝 0))
    (hε0 : ∀ i, 0 ≤ ε i) (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) :
    ∃ S : MatrixThomModifiedData dims A B D ε,
      ∃ hm : ∀ i, 0 < (S i).cut.rank,
      ∃ e : MatrixTracialQuotient dims (U : Filter ι) ≃⋆ₐ[ℂ]
        MatrixTracialQuotient (fun i => (S i).cut.rank) (U : Filter ι),
      (∀ i, (S i).correctedSourceAlgebra ≤ (S i).correctedTargetAlgebra) ∧
      Tendsto (fun i => ((S i).cut.rank : ℝ) / dims i) (U : Filter ι) (𝓝 1) ∧
      Tendsto (fun i => ((S i).stableDim : ℝ) / dims i) (U : Filter ι) (𝓝 1) ∧
      Tendsto (fun i => matrixTraceReal (dims i) (1 - (S i).stableSupport)) (U : Filter ι) (𝓝 0) ∧
      Tendsto (fun i =>
        matrixHSUnitBallHausdorff (dims i) ((S i).stableOriginalAlgebra (B i))
            ((S i).stableCorrectedAlgebra (S i).correctedSourceAlgebra) +
          matrixHSUnitBallHausdorff (dims i) ((S i).stableOriginalAlgebra (A i))
            ((S i).stableCorrectedAlgebra (S i).correctedTargetAlgebra)) (U : Filter ι) (𝓝 0) ∧
      (∀ x, e x ∈ matrixInternalQuotient (fun i => (S i).cut.rank)
          (fun i => (S i).correctedTargetAlgebra) (U : Filter ι) ↔
        x ∈ matrixInternalQuotient dims A (U : Filter ι)) ∧
      (∀ x, e x ∈ matrixInternalQuotient (fun i => (S i).cut.rank)
          (fun i => (S i).correctedSourceAlgebra) (U : Filter ι) ↔
        x ∈ matrixInternalQuotient dims B (U : Filter ι)) ∧
      (∀ x, matrixUltratrace (fun i => (S i).cut.rank) hm U (e x) =
        matrixUltratrace dims (fun i => NeZero.pos (dims i)) U x) ∧
      (∀ i, IsStarProjection (S i).stableSupport ∧
        (S i).stableSupport ∈ (S i).stableCorrectedAlgebra (S i).correctedTargetAlgebra) ∧
      ∀ᶠ i in (U : Filter ι),
        (S i).stableSupport ∈ (S i).stableOriginalAlgebra (A i) ∧
        ∃ π : D i →⋆ₐ[ℂ] CMatrix (S i).cut.rank,
          π.range ≤ (S i).correctedSourceAlgebra ∧ ∀ X : D i,
          (S i).stableSupport * matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) =
              matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) * (S i).stableSupport ∧
          (S i).stableSupport * matrixFrameLift (S i).stableTargetFrame (π X) =
              matrixFrameLift (S i).stableTargetFrame (π X) * (S i).stableSupport ∧
          (S i).stableSupport * matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) * (S i).stableSupport =
            (S i).stableSupport * matrixFrameLift (S i).stableTargetFrame (π X) * (S i).stableSupport := by
  obtain ⟨S⟩ := exists_matrixThomModifiedData dims A B D ε hDA hDB hε0 hBA
  let hm := matrixThomModified_cut_rank_pos dims S hε0
  refine ⟨S, hm, matrixThomGeneralQuotientEquiv dims S (U : Filter ι) hε hε0,
    fun i => (S i).correctedSourceAlgebra_le_target,
    matrixThomModified_dimension_ratio_tendsto dims S (U : Filter ι) hε,
    matrixThom_stable_dimension_ratio_tendsto dims S (matrixSmallError_tendsto ε (U : Filter ι) hε),
    matrixThomModified_support_trace_tendsto dims S (U : Filter ι) hε,
    matrixThomModified_AB_hausdorff_tendsto dims S (U : Filter ι) hε hε0 hBA,
    matrixThomGeneralQuotientEquiv_A_iff dims S (U : Filter ι) hε hε0,
    matrixThomGeneralQuotientEquiv_B_iff dims S (U : Filter ι) hε hε0 hBA, ?_,
    fun i => ⟨(S i).stableSupport_projection, (S i).stableSupport_target_mem⟩, ?_⟩
  · exact matrixThomGeneralQuotientEquiv_trace dims S hε0 U hε
  · exact (matrixThomModified_source_support_mem_eventually dims S (U : Filter ι) hε).and
      (matrixThomModified_relative_eventually dims S hDB (U : Filter ι) hε)

end ThomGame.Analysis
