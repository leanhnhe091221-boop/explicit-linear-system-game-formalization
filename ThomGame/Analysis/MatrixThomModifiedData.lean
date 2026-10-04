module

public import ThomGame.Analysis.MatrixSmallErrorModification
public import ThomGame.Analysis.MatrixThomTracialCorrection

/-!
# Actual Thom data after modification on the exceptional coordinates

The original dimensions and index set are retained. The modified input
has small error at every coordinate and equals the original input on a
filter-large set. Hence every actual spectral range is positive.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ i, NeZero (dims i)]
    (A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ)

abbrev MatrixThomModifiedData :=
  (i : ι) → MatrixThomSpectralData (matrixSmallErrorAlgebra dims A ε i)
    (matrixSmallErrorAlgebra dims B ε i) (matrixSmallErrorAlgebra dims D ε i) (matrixSmallError ε i)

theorem exists_matrixThomModifiedData (hDA : ∀ i, D i ≤ A i) (hDB : ∀ i, D i ≤ B i)
    (hε0 : ∀ i, 0 ≤ ε i) (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) :
    Nonempty (MatrixThomModifiedData dims A B D ε) := by
  refine ⟨fun i => Classical.choice (exists_matrixThomSpectralData
    (matrixSmallErrorAlgebra dims A ε i) (matrixSmallErrorAlgebra dims B ε i)
    (matrixSmallErrorAlgebra dims D ε i) ?_ ?_ ?_ ?_)⟩
  · exact matrixSmallErrorAlgebra_mono dims D A ε hDA i
  · exact matrixSmallErrorAlgebra_mono dims D B ε hDB i
  · exact matrixSmallError_nonneg ε hε0 i
  · exact matrixSmallError_nearInclusion dims A B ε hBA i

variable {A B D ε}

theorem matrixThomModified_cut_rank_pos (S : MatrixThomModifiedData dims A B D ε)
    (hε0 : ∀ i, 0 ≤ ε i) (i : ι) : 0 < (S i).cut.rank :=
  (S i).cut_rank_pos (matrixSmallError_nonneg ε hε0 i) (matrixSmallError_lt_half ε i)

theorem matrixThomModified_dimension_ratio_tendsto (S : MatrixThomModifiedData dims A B D ε)
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) :
    Tendsto (fun i => ((S i).cut.rank : ℝ) / dims i) L (𝓝 1) :=
  matrixThom_cut_dimension_ratio_tendsto dims S (matrixSmallError_tendsto ε L hε)

theorem matrixThomModified_support_trace_tendsto (S : MatrixThomModifiedData dims A B D ε)
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) :
    Tendsto (fun i => matrixTraceReal (dims i) (1 - (S i).stableSupport)) L (𝓝 0) :=
  matrixThom_stable_complement_trace_tendsto dims S (matrixSmallError_tendsto ε L hε)

end ThomGame.Analysis
