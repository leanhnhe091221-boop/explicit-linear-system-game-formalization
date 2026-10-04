module

public import ThomGame.Analysis.MatrixThomQuotientIdentification

/-!
# The tracial correction on Thom's small-error range

From the original near inclusion and epsilon < 1/2 at each coordinate,
construct positive corrected dimensions, exact inclusions and a single
trace-preserving ambient star equivalence identifying both internal
algebras. No block decomposition or multiplicity estimate is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem exists_matrixThomTracialCorrection_of_small_error {ι : Type*}
    (dims : ι → Nat) [∀ i, NeZero (dims i)]
    (A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))
    (hDA : ∀ i, D i ≤ A i) (hDB : ∀ i, D i ≤ B i)
    (U : Ultrafilter ι) {ε : ι → ℝ} (hε : Tendsto ε (U : Filter ι) (𝓝 0))
    (hε0 : ∀ i, 0 ≤ ε i) (hsmall : ∀ i, ε i < 1 / 2)
    (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) :
    ∃ S : (i : ι) → MatrixThomSpectralData (A i) (B i) (D i) (ε i),
      ∃ hm : ∀ i, 0 < (S i).cut.rank,
      ∃ e : MatrixTracialQuotient dims (U : Filter ι) ≃⋆ₐ[ℂ]
        MatrixTracialQuotient (fun i => (S i).cut.rank) (U : Filter ι),
      (∀ i, (S i).correctedSourceAlgebra ≤ (S i).correctedTargetAlgebra) ∧
      Tendsto (fun i => ((S i).cut.rank : ℝ) / dims i) (U : Filter ι) (𝓝 1) ∧
      (∀ x, e x ∈ matrixInternalQuotient (fun i => (S i).cut.rank)
          (fun i => (S i).correctedTargetAlgebra) (U : Filter ι) ↔
        x ∈ matrixInternalQuotient dims A (U : Filter ι)) ∧
      (∀ x, e x ∈ matrixInternalQuotient (fun i => (S i).cut.rank)
          (fun i => (S i).correctedSourceAlgebra) (U : Filter ι) ↔
        x ∈ matrixInternalQuotient dims B (U : Filter ι)) ∧
      (∀ x, matrixUltratrace (fun i => (S i).cut.rank) hm U (e x) =
        matrixUltratrace dims (fun i => NeZero.pos (dims i)) U x) ∧
      ∀ i (X : D i),
        (S i).stableSupport * matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) *
            (S i).stableSupport =
          (S i).stableSupport * matrixFrameLift (S i).stableTargetFrame
            ((S i).cutSourceRepresentation ⟨X, hDB i X.property⟩) * (S i).stableSupport := by
  let S i := Classical.choice (exists_matrixThomSpectralData (A i) (B i) (D i)
    (hDA i) (hDB i) (hε0 i) (hBA i))
  have hm : ∀ i, 0 < (S i).cut.rank := fun i => (S i).cut_rank_pos (hε0 i) (hsmall i)
  refine ⟨S, hm, matrixThomQuotientEquiv dims S (U : Filter ι) hε hm,
    fun i => (S i).correctedSourceAlgebra_le_target,
    matrixThom_cut_dimension_ratio_tendsto dims S hε,
    matrixThomQuotientEquiv_A_iff dims S (U : Filter ι) hε hm hε0,
    matrixThomQuotientEquiv_B_iff dims S (U : Filter ι) hε hm hε0 hBA, ?_,
    fun i => (S i).stable_common_corner_agreement (hDB i)⟩
  exact matrixThomQuotientEquiv_trace dims S hm U hε

end ThomGame.Analysis
