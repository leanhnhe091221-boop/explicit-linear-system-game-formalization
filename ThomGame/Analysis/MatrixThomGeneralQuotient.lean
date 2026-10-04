module

public import ThomGame.Analysis.MatrixThomModifiedData

/-!
# The original A and B ultraproducts are identified without a pointwise error bound

A single actual trace-preserving ambient equivalence identifies both
original internal algebras with the exact corrected ones. Exceptional
input coordinates were removed using the proved large-set invariance.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ i, NeZero (dims i)]
    {A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))} {ε : ι → ℝ}
    (S : MatrixThomModifiedData dims A B D ε) (L : Filter ι)
    (hε : Tendsto ε L (𝓝 0)) (hε0 : ∀ i, 0 ≤ ε i)

noncomputable def matrixThomGeneralQuotientEquiv :
    MatrixTracialQuotient dims L ≃⋆ₐ[ℂ] MatrixTracialQuotient (fun i => (S i).cut.rank) L :=
  matrixThomQuotientEquiv dims S L (matrixSmallError_tendsto ε L hε)
    (matrixThomModified_cut_rank_pos dims S hε0)

theorem matrixThomGeneralQuotientEquiv_A_iff (x : MatrixTracialQuotient dims L) :
    matrixThomGeneralQuotientEquiv dims S L hε hε0 x ∈
        matrixInternalQuotient (fun i => (S i).cut.rank) (fun i => (S i).correctedTargetAlgebra) L ↔
      x ∈ matrixInternalQuotient dims A L := by
  have h := matrixThomQuotientEquiv_A_iff dims S L (matrixSmallError_tendsto ε L hε)
    (matrixThomModified_cut_rank_pos dims S hε0) (matrixSmallError_nonneg ε hε0) x
  rwa [matrixSmallErrorAlgebra_internal_eq dims A ε L hε] at h

theorem matrixThomGeneralQuotientEquiv_B_iff
    (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) (x : MatrixTracialQuotient dims L) :
    matrixThomGeneralQuotientEquiv dims S L hε hε0 x ∈
        matrixInternalQuotient (fun i => (S i).cut.rank) (fun i => (S i).correctedSourceAlgebra) L ↔
      x ∈ matrixInternalQuotient dims B L := by
  have h := matrixThomQuotientEquiv_B_iff dims S L (matrixSmallError_tendsto ε L hε)
    (matrixThomModified_cut_rank_pos dims S hε0) (matrixSmallError_nonneg ε hε0)
    (matrixSmallError_nearInclusion dims A B ε hBA) x
  rwa [matrixSmallErrorAlgebra_internal_eq dims B ε L hε] at h

theorem matrixThomGeneralQuotientEquiv_trace (U : Ultrafilter ι)
    (hεU : Tendsto ε (U : Filter ι) (𝓝 0)) (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace (fun i => (S i).cut.rank) (matrixThomModified_cut_rank_pos dims S hε0) U
        (matrixThomGeneralQuotientEquiv dims S (U : Filter ι) hεU hε0 x) =
      matrixUltratrace dims (fun i => NeZero.pos (dims i)) U x :=
  matrixThomQuotientEquiv_trace dims S (matrixThomModified_cut_rank_pos dims S hε0) U
    (matrixSmallError_tendsto ε (U : Filter ι) hεU) x

end ThomGame.Analysis
