module

public import ThomGame.Analysis.MatrixNearInclusionContractions
public import ThomGame.Analysis.MatrixThomStableBApproximation
public import ThomGame.Analysis.MatrixThomCompressedLimits

/-!
# Returning corrected reverse near inclusion to the original algebras

Push an original contraction through the actual polar correction, apply
the corrected near inclusion, and lift the resulting contraction through
the actual source representation. Both errors are compared in the same
stable space, with the original denominator throughout. No corrected
dimension is assumed positive.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε δ : ℝ}

theorem MatrixThomSpectralData.reverse_nearInclusion_transfer
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε)
    (hBA : MatrixNearInclusion B A ε)
    (hrev : MatrixNearInclusion S.correctedTargetAlgebra S.correctedSourceAlgebra δ) :
    MatrixNearInclusion A B
      ((8 + 3 * Real.sqrt 2) * ε + Real.sqrt ((S.cut.rank : ℝ) / d) * δ) := by
  intro X hXA hX
  let Y := S.cutPolar * X * S.cutPolarᴴ
  have hY := S.cutPolar_push_contraction X hXA hX
  obtain ⟨Z, hZ, hZn, hYZ⟩ := matrixNearInclusion_contraction _ _ hrev Y hY.1.1 hY.2
  obtain ⟨V, hV, hVZ⟩ := matrixStarRepresentation_contraction_lift B S.cutSourceRepresentation Z hZ hZn
  refine ⟨(V : CMatrix d), V.property, ?_⟩
  have ha : rectHSNorm d
      (matrixFrameLift S.stableSourceFrame X - matrixFrameLift S.stableTargetFrame Y) ≤ 2 * ε := by
    have he := matrixStableFrames_source_corner S.cutPolar S.cutPolar_partialIsometry.1 X
    change matrixFrameLift S.stableSourceFrame _ = matrixFrameLift S.stableTargetFrame Y at he
    rw [← he, ← matrixFrameLift_sub, matrixFrameLift_hsNorm d S.stableSourceFrame_initial]
    exact S.cutPolar_source_compression_loss hε X hX
  have hb : rectHSNorm d
      (matrixFrameLift S.stableTargetFrame Y - matrixFrameLift S.stableTargetFrame Z) ≤
      Real.sqrt ((S.cut.rank : ℝ) / d) * δ := by
    rw [← matrixFrameLift_sub, matrixFrameLift_hsNorm d S.stableTargetFrame_initial,
      rectHSNorm_dimension_rescale (NeZero.pos d)]
    exact mul_le_mul_of_nonneg_left hYZ (Real.sqrt_nonneg _)
  have hc := S.stable_B_lift_distance hε hBA V hV
  rw [hVZ, rectHSNorm_sub_comm] at hc
  have he : matrixFrameLift S.stableSourceFrame (X - (V : CMatrix d)) =
      (matrixFrameLift S.stableSourceFrame X - matrixFrameLift S.stableTargetFrame Y) +
      (matrixFrameLift S.stableTargetFrame Y - matrixFrameLift S.stableTargetFrame Z) +
      (matrixFrameLift S.stableTargetFrame Z - matrixFrameLift S.stableSourceFrame (V : CMatrix d)) := by
    rw [matrixFrameLift_sub]
    abel
  rw [← rectHSNorm_eq_hsNorm, ← matrixFrameLift_hsNorm d S.stableSourceFrame_initial, he]
  let a := matrixFrameLift S.stableSourceFrame X - matrixFrameLift S.stableTargetFrame Y
  let b := matrixFrameLift S.stableTargetFrame Y - matrixFrameLift S.stableTargetFrame Z
  let c := matrixFrameLift S.stableTargetFrame Z - matrixFrameLift S.stableSourceFrame (V : CMatrix d)
  have ht1 := rectHSNorm_add_le d (a + b) c
  have ht2 := rectHSNorm_add_le d a b
  have hbound := add_le_add (add_le_add ha hb) hc
  have hconst : 2 * ε + Real.sqrt ((S.cut.rank : ℝ) / d) * δ + (6 + 3 * Real.sqrt 2) * ε =
      (8 + 3 * Real.sqrt 2) * ε + Real.sqrt ((S.cut.rank : ℝ) / d) * δ := by ring
  rw [hconst] at hbound
  exact ht1.trans ((add_le_add ht2 (le_refl (rectHSNorm d c))).trans hbound)

theorem matrixThom_reverse_nearInclusion_tendsto {ι : Type*} (dims : ι → Nat)
    [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε δ : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) (hδ : Tendsto δ L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n))
    (hrev : ∀ n, MatrixNearInclusion (S n).correctedTargetAlgebra (S n).correctedSourceAlgebra (δ n)) :
    Tendsto (fun n => matrixNearInclusionError (A n) (B n)) L (𝓝 0) := by
  have hr := (matrixThom_cut_dimension_ratio_tendsto dims S hε).sqrt
  have hb := (hε.const_mul (8 + 3 * Real.sqrt 2)).add (hr.mul hδ)
  exact squeeze_zero (fun n => matrixNearInclusionError_nonneg _ _)
    (fun n => (matrixNearInclusion_iff_error_le _ _ _).mp
      ((S n).reverse_nearInclusion_transfer (hε0 n) (hBA n) (hrev n)))
    (by simpa only [mul_zero, add_zero] using hb)

end ThomGame.Analysis
