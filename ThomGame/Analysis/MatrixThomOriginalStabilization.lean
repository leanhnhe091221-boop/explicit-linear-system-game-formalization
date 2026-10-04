module

public import ThomGame.Analysis.MatrixFrameInternalEquivalence
public import ThomGame.Analysis.MatrixThomStableCorrection

/-!
# Thom's original matrix quotient inside the same stable ambient model

The single source-frame equivalence simultaneously transports all original
coordinate subalgebras. Its images of A and B are the corrected stable
internal algebras, using the proved (3.4) equalities.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ i, NeZero (dims i)]
    {A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))} {ε : ι → ℝ}
    (S : (i : ι) → MatrixThomSpectralData (A i) (B i) (D i) (ε i))
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0))

noncomputable def matrixThomOriginalQuotientEquiv :
    MatrixTracialQuotient dims L ≃⋆ₐ[ℂ] MatrixTracialQuotient (fun i => (S i).stableDim) L :=
  matrixFrameQuotientEquiv dims (fun i => (S i).stableDim) (fun i => (S i).stableSourceFrame)
    (fun i => (S i).stableSourceFrame_initial) (fun i => NeZero.pos (dims i))
    (fun i => (NeZero.pos (dims i)).trans_le (S i).le_stableDim) L
    (matrixThom_stable_dimension_ratio_tendsto dims S hε)

theorem matrixThomOriginalQuotientEquiv_internal_map
    (C : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) :
    (matrixInternalQuotient dims C L).map (matrixThomOriginalQuotientEquiv dims S L hε).toStarAlgHom =
      matrixInternalQuotient (fun i => (S i).stableDim) (fun i => (S i).stableOriginalAlgebra (C i)) L :=
  matrixFrameQuotientHom_internal_map dims (fun i => (S i).stableDim) (fun i => (S i).stableSourceFrame)
    (fun i => (S i).stableSourceFrame_initial) (fun i => NeZero.pos (dims i))
    (fun i => (NeZero.pos (dims i)).trans_le (S i).le_stableDim) L
    (matrixThom_stable_dimension_ratio_tendsto dims S hε) C

theorem matrixThomOriginalQuotientEquiv_A_map (hε0 : ∀ i, 0 ≤ ε i) :
    (matrixInternalQuotient dims A L).map (matrixThomOriginalQuotientEquiv dims S L hε).toStarAlgHom =
      matrixInternalQuotient (fun i => (S i).stableDim)
        (fun i => (S i).stableCorrectedAlgebra (S i).correctedTargetAlgebra) L := by
  rw [matrixThomOriginalQuotientEquiv_internal_map]
  exact matrixThom_stable_A_internal_eq dims S hε hε0

theorem matrixThomOriginalQuotientEquiv_B_map (hε0 : ∀ i, 0 ≤ ε i)
    (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) :
    (matrixInternalQuotient dims B L).map (matrixThomOriginalQuotientEquiv dims S L hε).toStarAlgHom =
      matrixInternalQuotient (fun i => (S i).stableDim)
        (fun i => (S i).stableCorrectedAlgebra (S i).correctedSourceAlgebra) L := by
  rw [matrixThomOriginalQuotientEquiv_internal_map]
  exact matrixThom_stable_B_internal_eq dims S hε hε0 hBA

theorem matrixThomOriginalQuotientEquiv_trace (U : Ultrafilter ι)
    (hεU : Tendsto ε (U : Filter ι) (𝓝 0)) (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace (fun i => (S i).stableDim)
        (fun i => (NeZero.pos (dims i)).trans_le (S i).le_stableDim) U
        (matrixThomOriginalQuotientEquiv dims S (U : Filter ι) hεU x) =
      matrixUltratrace dims (fun i => NeZero.pos (dims i)) U x :=
  matrixFrameQuotientEquiv_trace dims (fun i => (S i).stableDim) (fun i => (S i).stableSourceFrame)
    (fun i => (S i).stableSourceFrame_initial) (fun i => NeZero.pos (dims i))
    (fun i => (NeZero.pos (dims i)).trans_le (S i).le_stableDim) U
    (matrixThom_stable_dimension_ratio_tendsto dims S hεU) x

end ThomGame.Analysis
