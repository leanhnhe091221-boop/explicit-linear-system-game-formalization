module

public import ThomGame.Analysis.MatrixThomOriginalStabilization
public import ThomGame.Analysis.MatrixThomCompressedLimits

/-!
# Thom's corrected matrix quotient inside the same stable ambient model

For positive spectral-range dimensions, the target-frame equivalence uses
N/m tending to one. Positivity follows on the paper's epsilon < 1/2 range;
it is kept explicit here instead of silently assuming a nonzero cutoff.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ i, NeZero (dims i)]
    {A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))} {ε : ι → ℝ}
    (S : (i : ι) → MatrixThomSpectralData (A i) (B i) (D i) (ε i))
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) (hm : ∀ i, 0 < (S i).cut.rank)

include hε hm in
theorem matrixThom_stable_to_cut_ratio_tendsto :
    Tendsto (fun i => ((S i).stableDim : ℝ) / (S i).cut.rank) L (𝓝 1) := by
  have he : (fun i => ((S i).stableDim : ℝ) / (S i).cut.rank) =
      (fun i => (((S i).stableDim : ℝ) / dims i) / (((S i).cut.rank : ℝ) / dims i)) := by
    funext i
    have hd' : (dims i : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (dims i)
    have hm' : ((S i).cut.rank : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hm i)
    field_simp
  rw [he]
  simpa only [Pi.div_def, div_self one_ne_zero] using (matrixThom_stable_dimension_ratio_tendsto dims S hε).div
    (matrixThom_cut_dimension_ratio_tendsto dims S hε) one_ne_zero

noncomputable def matrixThomCorrectedQuotientEquiv :
    MatrixTracialQuotient (fun i => (S i).cut.rank) L ≃⋆ₐ[ℂ]
      MatrixTracialQuotient (fun i => (S i).stableDim) L :=
  matrixFrameQuotientEquiv (fun i => (S i).cut.rank) (fun i => (S i).stableDim)
    (fun i => (S i).stableTargetFrame) (fun i => (S i).stableTargetFrame_initial) hm
    (fun i => (NeZero.pos (dims i)).trans_le (S i).le_stableDim) L
    (matrixThom_stable_to_cut_ratio_tendsto dims S L hε hm)

theorem matrixThomCorrectedQuotientEquiv_internal_map
    (C : (i : ι) → StarSubalgebra ℂ (CMatrix (S i).cut.rank)) :
    (matrixInternalQuotient (fun i => (S i).cut.rank) C L).map
        (matrixThomCorrectedQuotientEquiv dims S L hε hm).toStarAlgHom =
      matrixInternalQuotient (fun i => (S i).stableDim) (fun i => (S i).stableCorrectedAlgebra (C i)) L :=
  matrixFrameQuotientHom_internal_map (fun i => (S i).cut.rank) (fun i => (S i).stableDim)
    (fun i => (S i).stableTargetFrame) (fun i => (S i).stableTargetFrame_initial) hm
    (fun i => (NeZero.pos (dims i)).trans_le (S i).le_stableDim) L
    (matrixThom_stable_to_cut_ratio_tendsto dims S L hε hm) C

theorem matrixThomCorrectedQuotientEquiv_trace (U : Ultrafilter ι)
    (hεU : Tendsto ε (U : Filter ι) (𝓝 0))
    (x : MatrixTracialQuotient (fun i => (S i).cut.rank) (U : Filter ι)) :
    matrixUltratrace (fun i => (S i).stableDim)
        (fun i => (NeZero.pos (dims i)).trans_le (S i).le_stableDim) U
        (matrixThomCorrectedQuotientEquiv dims S (U : Filter ι) hεU hm x) =
      matrixUltratrace (fun i => (S i).cut.rank) hm U x :=
  matrixFrameQuotientEquiv_trace (fun i => (S i).cut.rank) (fun i => (S i).stableDim)
    (fun i => (S i).stableTargetFrame) (fun i => (S i).stableTargetFrame_initial) hm
    (fun i => (NeZero.pos (dims i)).trans_le (S i).le_stableDim) U
    (matrixThom_stable_to_cut_ratio_tendsto dims S (U : Filter ι) hεU hm) x

end ThomGame.Analysis
