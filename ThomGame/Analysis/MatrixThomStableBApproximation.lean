module

public import ThomGame.Analysis.MatrixRepresentationUnitBalls
public import ThomGame.Analysis.MatrixStableIntertwiningDistance
public import ThomGame.Analysis.MatrixThomStableCompression
public import ThomGame.Analysis.MatrixThomCornerApproximation

/-!
# Both contraction witnesses for Thom's stable B algebras

The forward witness uses the actual representation. The reverse witness
uses its exact contraction lift. Scalars on either added corner are
removed by the uniformly small compression error.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.stable_B_lift_distance
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε)
    (X : B) (hX : matrixOpNorm (X : CMatrix d) ≤ 1) :
    rectHSNorm d (matrixFrameLift S.stableSourceFrame (X : CMatrix d) -
      matrixFrameLift S.stableTargetFrame (S.cutSourceRepresentation X)) ≤
        (6 + 3 * Real.sqrt 2) * ε := by
  have hY := matrixStarRepresentation_contraction B S.cutSourceRepresentation X hX
  have he : rectHSNorm d (matrixFrameLift S.stableSourceFrame (X : CMatrix d) -
      matrixFrameLift S.stableTargetFrame (S.cutSourceRepresentation X)) ≤
      rectHSNorm d ((X : CMatrix d) - (S.cutPolarᴴ * S.cutPolar) *
        (X : CMatrix d) * (S.cutPolarᴴ * S.cutPolar)) +
      rectHSNorm d (S.cutSourceRepresentation X - (S.cutPolar * S.cutPolarᴴ) *
        S.cutSourceRepresentation X * (S.cutPolar * S.cutPolarᴴ)) +
      rectHSNorm d (S.cutSourceRepresentation X * S.cutPolar - S.cutPolar * (X : CMatrix d)) :=
    matrixStableFrames_distance_bound d S.cutPolar S.cutPolar_partialIsometry.1
      (X : CMatrix d) (S.cutSourceRepresentation X)
  have ha := S.cutPolar_source_compression_loss hε (X : CMatrix d) hX
  have hb := S.cutPolar_target_compression_loss hε (S.cutSourceRepresentation X) hY
  have hc := S.cutPolar_intertwining_bound hε hBA X hX
  linarith

theorem MatrixThomSpectralData.stable_B_forward_contraction
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε)
    (Z : CMatrix S.stableDim) (hZ : Z ∈ S.stableOriginalAlgebra B) (hn : matrixOpNorm Z ≤ 1) :
    ∃ Y ∈ S.stableCorrectedAlgebra S.correctedSourceAlgebra,
      matrixOpNorm Y ≤ 1 ∧ rectHSNorm d (Z - Y) ≤ (6 + 5 * Real.sqrt 2) * ε := by
  let X : B := ⟨S.stableSourceFrameᴴ * Z * S.stableSourceFrame,
    matrixFrameScalarAlgebra_compression_mem B S.stableSourceFrame S.stableSourceFrame_initial Z hZ⟩
  have hX : matrixOpNorm (X : CMatrix d) ≤ 1 :=
    (matrixFrameCompression_opNorm_le S.stableSourceFrame S.stableSourceFrame_initial Z).trans hn
  let Y := S.cutSourceRepresentation X
  have hY : Y ∈ S.correctedSourceAlgebra := ⟨X, rfl⟩
  refine ⟨matrixFrameLift S.stableTargetFrame Y,
    matrixFrameScalarAlgebra_lift_mem _ _ S.stableTargetFrame_initial Y hY, ?_, ?_⟩
  · rw [matrixFrameLift_opNorm _ S.stableTargetFrame_initial]
    exact matrixStarRepresentation_contraction B S.cutSourceRepresentation X hX
  · have he : Z - matrixFrameLift S.stableTargetFrame Y =
        (Z - matrixFrameLift S.stableSourceFrame (X : CMatrix d)) +
        (matrixFrameLift S.stableSourceFrame (X : CMatrix d) - matrixFrameLift S.stableTargetFrame Y) := by abel
    rw [he]
    have ha := S.stableSourceFrame_compression_loss hε Z hn
    have hb := S.stable_B_lift_distance hε hBA X hX
    exact (rectHSNorm_add_le d _ _).trans (by dsimp only [X, Y] at *; linarith)

theorem MatrixThomSpectralData.stable_B_reverse_contraction
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε)
    (Z : CMatrix S.stableDim) (hZ : Z ∈ S.stableCorrectedAlgebra S.correctedSourceAlgebra)
    (hn : matrixOpNorm Z ≤ 1) :
    ∃ X ∈ S.stableOriginalAlgebra B,
      matrixOpNorm X ≤ 1 ∧ rectHSNorm d (Z - X) ≤ (6 + 5 * Real.sqrt 2) * ε := by
  let Y := S.stableTargetFrameᴴ * Z * S.stableTargetFrame
  have hY : Y ∈ S.correctedSourceAlgebra :=
    matrixFrameScalarAlgebra_compression_mem _ _ S.stableTargetFrame_initial Z hZ
  have hYn : matrixOpNorm Y ≤ 1 :=
    (matrixFrameCompression_opNorm_le S.stableTargetFrame S.stableTargetFrame_initial Z).trans hn
  obtain ⟨X, hX, hXY⟩ := matrixStarRepresentation_contraction_lift B S.cutSourceRepresentation Y hY hYn
  refine ⟨matrixFrameLift S.stableSourceFrame (X : CMatrix d),
    matrixFrameScalarAlgebra_lift_mem B _ S.stableSourceFrame_initial (X : CMatrix d) X.property, ?_, ?_⟩
  · rw [matrixFrameLift_opNorm _ S.stableSourceFrame_initial]
    exact hX
  · have he : Z - matrixFrameLift S.stableSourceFrame (X : CMatrix d) =
        (Z - matrixFrameLift S.stableTargetFrame Y) +
        (matrixFrameLift S.stableTargetFrame Y - matrixFrameLift S.stableSourceFrame (X : CMatrix d)) := by abel
    rw [he]
    have ha := S.stableTargetFrame_compression_loss hε Z hn
    have hb := S.stable_B_lift_distance hε hBA X hX
    rw [hXY, rectHSNorm_sub_comm] at hb
    have hs : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    exact (rectHSNorm_add_le d _ _).trans (by dsimp only [Y] at *; nlinarith)

end ThomGame.Analysis
