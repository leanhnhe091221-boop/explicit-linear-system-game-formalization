module

public import ThomGame.Analysis.MatrixCanonicalCornerFrame
public import ThomGame.Analysis.MatrixFrameInternalEquivalence

/-!
# Canonical identification for arbitrary negligible dimension changes

Both matrix spaces include by their first coordinates in dimension
max(m,d). The resulting trace-preserving equivalence depends on dimensions
only, and applies even when their order changes from index to index.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (source target : ι → Nat)
    (hs : ∀ i, 0 < source i) (ht : ∀ i, 0 < target i)
    (L : Filter ι) (hratio : Tendsto (fun i => (source i : ℝ) / target i) L (𝓝 1))

include ht hratio in
theorem matrixDimensionRatio_max_target_tendsto :
    Tendsto (fun i => ((max (source i) (target i) : Nat) : ℝ) / target i) L (𝓝 1) := by
  have h := hratio.max (tendsto_const_nhds (x := (1 : ℝ)))
  simp only [max_self] at h
  apply h.congr'
  exact Eventually.of_forall fun i => by
    change max ((source i : ℝ) / target i) 1 = (max (source i) (target i) : Nat) / (target i : ℝ)
    rw [Nat.cast_max, ← max_div_div_right (Nat.cast_nonneg (target i)),
      div_self (by exact_mod_cast Nat.ne_of_gt (ht i))]

include hs hratio in
theorem matrixDimensionRatio_max_source_tendsto :
    Tendsto (fun i => ((max (source i) (target i) : Nat) : ℝ) / source i) L (𝓝 1) := by
  simpa only [max_comm] using matrixDimensionRatio_max_target_tendsto target source hs L
    (matrixDimensionRatio_inverse_tendsto target source L hratio)

noncomputable def matrixCanonicalSourceToCommon :
    MatrixTracialQuotient source L ≃⋆ₐ[ℂ]
      MatrixTracialQuotient (fun i => max (source i) (target i)) L :=
  matrixFrameQuotientEquiv source (fun i => max (source i) (target i))
    (fun i => matrixCanonicalCornerFrame (Nat.le_max_left (source i) (target i)))
    (fun i => matrixCanonicalCornerFrame_initial (Nat.le_max_left (source i) (target i)))
    hs (fun i => (hs i).trans_le (Nat.le_max_left _ _)) L
    (matrixDimensionRatio_max_source_tendsto source target hs L hratio)

noncomputable def matrixCanonicalTargetToCommon :
    MatrixTracialQuotient target L ≃⋆ₐ[ℂ]
      MatrixTracialQuotient (fun i => max (source i) (target i)) L :=
  matrixFrameQuotientEquiv target (fun i => max (source i) (target i))
    (fun i => matrixCanonicalCornerFrame (Nat.le_max_right (source i) (target i)))
    (fun i => matrixCanonicalCornerFrame_initial (Nat.le_max_right (source i) (target i)))
    ht (fun i => (ht i).trans_le (Nat.le_max_right _ _)) L
    (matrixDimensionRatio_max_target_tendsto source target ht L hratio)

noncomputable def matrixCanonicalDimensionEquiv :
    MatrixTracialQuotient source L ≃⋆ₐ[ℂ] MatrixTracialQuotient target L :=
  (matrixCanonicalSourceToCommon source target hs L hratio).trans
    (matrixCanonicalTargetToCommon source target ht L hratio).symm

theorem matrixCanonicalDimensionEquiv_to_common (x : MatrixTracialQuotient source L) :
    matrixCanonicalTargetToCommon source target ht L hratio
      (matrixCanonicalDimensionEquiv source target hs ht L hratio x) =
      matrixCanonicalSourceToCommon source target hs L hratio x := by
  simp only [matrixCanonicalDimensionEquiv, StarAlgEquiv.trans_apply, StarAlgEquiv.apply_symm_apply]

theorem matrixCanonicalDimensionEquiv_mk (A : BoundedMatrixSequence source) :
    matrixCanonicalDimensionEquiv source target hs ht L hratio (matrixQuotientMk source L A) =
      matrixQuotientMk target L
        (matrixFrameSequenceCompression target (fun i => max (source i) (target i))
          (fun i => matrixCanonicalCornerFrame (Nat.le_max_right (source i) (target i)))
          (fun i => matrixCanonicalCornerFrame_initial (Nat.le_max_right (source i) (target i)))
          (matrixFrameSequenceLift source (fun i => max (source i) (target i))
            (fun i => matrixCanonicalCornerFrame (Nat.le_max_left (source i) (target i)))
            (fun i => matrixCanonicalCornerFrame_initial (Nat.le_max_left (source i) (target i))) A)) := by
  rw [matrixCanonicalDimensionEquiv, StarAlgEquiv.trans_apply, matrixCanonicalSourceToCommon,
    matrixFrameQuotientEquiv_mk, matrixCanonicalTargetToCommon, matrixFrameQuotientEquiv_symm_mk]

theorem matrixCanonicalDimensionEquiv_trace (U : Ultrafilter ι)
    (hr : Tendsto (fun i => (source i : ℝ) / target i) (U : Filter ι) (𝓝 1))
    (x : MatrixTracialQuotient source (U : Filter ι)) :
    matrixUltratrace target ht U (matrixCanonicalDimensionEquiv source target hs ht (U : Filter ι) hr x) =
      matrixUltratrace source hs U x := by
  have h1 := matrixFrameQuotientEquiv_trace source (fun i => max (source i) (target i))
    (fun i => matrixCanonicalCornerFrame (Nat.le_max_left (source i) (target i)))
    (fun i => matrixCanonicalCornerFrame_initial (Nat.le_max_left (source i) (target i)))
    hs (fun i => (hs i).trans_le (Nat.le_max_left _ _)) U
    (matrixDimensionRatio_max_source_tendsto source target hs (U : Filter ι) hr) x
  have h2 := matrixFrameQuotientEquiv_trace target (fun i => max (source i) (target i))
    (fun i => matrixCanonicalCornerFrame (Nat.le_max_right (source i) (target i)))
    (fun i => matrixCanonicalCornerFrame_initial (Nat.le_max_right (source i) (target i)))
    ht (fun i => (ht i).trans_le (Nat.le_max_right _ _)) U
    (matrixDimensionRatio_max_target_tendsto source target ht (U : Filter ι) hr)
    (matrixCanonicalDimensionEquiv source target hs ht (U : Filter ι) hr x)
  change matrixUltratrace _ _ U
    (matrixCanonicalTargetToCommon source target ht (U : Filter ι) hr
      (matrixCanonicalDimensionEquiv source target hs ht (U : Filter ι) hr x)) = _ at h2
  rw [matrixCanonicalDimensionEquiv_to_common] at h2
  exact h2.symm.trans h1

end ThomGame.Analysis
