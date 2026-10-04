module

public import ThomGame.Analysis.MatrixThomGeneralQuotient

/-!
# The relative assertion for the original common algebra on a large set

On every original small-error coordinate, construct the genuine
representation of the original D. Its stable image and the original
image commute with the same support and agree on its corner.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ i, NeZero (dims i)]
    {A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))} {ε : ι → ℝ}
    (S : MatrixThomModifiedData dims A B D ε) (hDB : ∀ i, D i ≤ B i)

noncomputable def matrixThomModifiedCommonRepresentation (i : ι) (hi : ε i < 1 / 2) :
    D i →⋆ₐ[ℂ] CMatrix (S i).cut.rank :=
  (S i).cutSourceRepresentation.comp (StarSubalgebra.inclusion (show D i ≤ matrixSmallErrorAlgebra dims B ε i by
    rw [matrixSmallErrorAlgebra_eq dims B ε hi]
    exact hDB i))

theorem matrixThomModifiedCommonRepresentation_apply (i : ι) (hi : ε i < 1 / 2) (X : D i) :
    matrixThomModifiedCommonRepresentation dims S hDB i hi X =
      (S i).cutFrameᴴ * (S i).sourceRep (X : CMatrix (dims i)) * (S i).cutFrame := rfl

theorem matrixThomModifiedCommonRepresentation_range_le (i : ι) (hi : ε i < 1 / 2) :
    (matrixThomModifiedCommonRepresentation dims S hDB i hi).range ≤
      (S i).correctedSourceAlgebra := by
  rintro Y ⟨X, rfl⟩
  refine ⟨⟨X, ?_⟩, rfl⟩
  rw [matrixSmallErrorAlgebra_eq dims B ε hi]
  exact hDB i X.property

theorem matrixThomModified_common_corner_of_small (i : ι) (hi : ε i < 1 / 2) (X : D i) :
    (S i).stableSupport * matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) * (S i).stableSupport =
      (S i).stableSupport * matrixFrameLift (S i).stableTargetFrame
        (matrixThomModifiedCommonRepresentation dims S hDB i hi X) * (S i).stableSupport := by
  let X' : matrixSmallErrorAlgebra dims D ε i := ⟨X, by
    rw [matrixSmallErrorAlgebra_eq dims D ε hi]
    exact X.property⟩
  exact (S i).stable_common_corner_agreement (matrixSmallErrorAlgebra_mono dims D B ε hDB i) X'

theorem matrixThomModified_common_commutes_of_small (i : ι) (hi : ε i < 1 / 2) (X : D i) :
    (S i).stableSupport * matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) =
        matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) * (S i).stableSupport ∧
      (S i).stableSupport * matrixFrameLift (S i).stableTargetFrame
          (matrixThomModifiedCommonRepresentation dims S hDB i hi X) =
        matrixFrameLift (S i).stableTargetFrame
          (matrixThomModifiedCommonRepresentation dims S hDB i hi X) * (S i).stableSupport := by
  let X' : matrixSmallErrorAlgebra dims D ε i := ⟨X, by
    rw [matrixSmallErrorAlgebra_eq dims D ε hi]
    exact X.property⟩
  exact ⟨(S i).stableSupport_commutes_original_common (matrixSmallErrorAlgebra_mono dims D B ε hDB i) X',
    (S i).stableSupport_commutes_corrected_common (matrixSmallErrorAlgebra_mono dims D B ε hDB i) X'⟩

include hDB in
theorem matrixThomModified_relative_eventually (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) :
    ∀ᶠ i in L, ∃ π : D i →⋆ₐ[ℂ] CMatrix (S i).cut.rank,
      π.range ≤ (S i).correctedSourceAlgebra ∧ ∀ X : D i,
        (S i).stableSupport * matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) =
            matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) * (S i).stableSupport ∧
        (S i).stableSupport * matrixFrameLift (S i).stableTargetFrame (π X) =
            matrixFrameLift (S i).stableTargetFrame (π X) * (S i).stableSupport ∧
        (S i).stableSupport * matrixFrameLift (S i).stableSourceFrame (X : CMatrix (dims i)) * (S i).stableSupport =
          (S i).stableSupport * matrixFrameLift (S i).stableTargetFrame (π X) * (S i).stableSupport := by
  apply (matrixSmallError_eventually_lt_half ε L hε).mono
  intro i hi
  refine ⟨matrixThomModifiedCommonRepresentation dims S hDB i hi,
    matrixThomModifiedCommonRepresentation_range_le dims S hDB i hi, fun X => ?_⟩
  exact ⟨(matrixThomModified_common_commutes_of_small dims S hDB i hi X).1,
    (matrixThomModified_common_commutes_of_small dims S hDB i hi X).2,
    matrixThomModified_common_corner_of_small dims S hDB i hi X⟩

end ThomGame.Analysis
