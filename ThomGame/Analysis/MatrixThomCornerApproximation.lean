module

public import ThomGame.Analysis.MatrixThomCornerIdentification
public import ThomGame.Analysis.MatrixSubalgebraCornerUnitBalls

/-!
# Uniform support-compression bounds for Thom's actual correction

Both spaces use the original denominator d. The canonical push and pull
maps preserve contraction bounds and recover the original matrices up to
the two uniformly small support-compression errors.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.cutPolar_source_compression_loss_sq
    (S : MatrixThomSpectralData A B D ε) (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    rectHSNorm d (X - (S.cutPolarᴴ * S.cutPolar) * X * (S.cutPolarᴴ * S.cutPolar)) ^ 2 ≤
      4 * ε ^ 2 := by
  have he := rectHSNorm_projection_compression_loss_sq d
    (S.cutPolarᴴ * S.cutPolar) X S.cutPolar_partialIsometry.1 hX
  have ht := S.cutPolar_complement_trace_bounds.1
  linarith

theorem MatrixThomSpectralData.cutPolar_target_compression_loss_sq
    (S : MatrixThomSpectralData A B D ε) (Y : CMatrix S.cut.rank) (hY : matrixOpNorm Y ≤ 1) :
    rectHSNorm d (Y - (S.cutPolar * S.cutPolarᴴ) * Y * (S.cutPolar * S.cutPolarᴴ)) ^ 2 ≤
      8 * ε ^ 2 := by
  have he := rectHSNorm_projection_compression_loss_sq d
    (S.cutPolar * S.cutPolarᴴ) Y S.cutPolar_partialIsometry.2 hY
  have ht := S.cutPolar_complement_trace_bounds.2
  linarith

theorem MatrixThomSpectralData.cutPolar_source_compression_loss
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    rectHSNorm d (X - (S.cutPolarᴴ * S.cutPolar) * X * (S.cutPolarᴴ * S.cutPolar)) ≤ 2 * ε := by
  have he := S.cutPolar_source_compression_loss_sq X hX
  nlinarith [rectHSNorm_nonneg d (X - (S.cutPolarᴴ * S.cutPolar) * X * (S.cutPolarᴴ * S.cutPolar))]

theorem MatrixThomSpectralData.cutPolar_target_compression_loss
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε)
    (Y : CMatrix S.cut.rank) (hY : matrixOpNorm Y ≤ 1) :
    rectHSNorm d (Y - (S.cutPolar * S.cutPolarᴴ) * Y * (S.cutPolar * S.cutPolarᴴ)) ≤
      2 * Real.sqrt 2 * ε := by
  have he := S.cutPolar_target_compression_loss_sq Y hY
  have hs : (2 * Real.sqrt 2 * ε) ^ 2 = 8 * ε ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hp : 0 ≤ 2 * Real.sqrt 2 * ε := mul_nonneg (by positivity) hε
  nlinarith [rectHSNorm_nonneg d (Y - (S.cutPolar * S.cutPolarᴴ) * Y * (S.cutPolar * S.cutPolarᴴ))]

theorem MatrixThomSpectralData.cutPolar_push_contraction
    (S : MatrixThomSpectralData A B D ε) (X : CMatrix d) (hXA : X ∈ A) (hX : matrixOpNorm X ≤ 1) :
    S.cutPolar * X * S.cutPolarᴴ ∈ matrixSubalgebraCorner S.correctedTargetAlgebra
      (S.cutPolar * S.cutPolarᴴ) S.cutPolar_partialIsometry.2 ∧
      matrixOpNorm (S.cutPolar * X * S.cutPolarᴴ) ≤ 1 :=
  ⟨matrixCommutantIntertwiner_push_corner A S.cutCommutantRepresentation S.cutPolar
    S.cutPolar_partialIsometry.1 S.cutPolar_commutant_intertwines X hXA,
    (matrixPartialIsometry_sandwich_norm_le S.cutPolar S.cutPolar_partialIsometry.1 X).trans hX⟩

theorem MatrixThomSpectralData.cutPolar_pull_contraction
    (S : MatrixThomSpectralData A B D ε) (Y : CMatrix S.cut.rank)
    (hYA : Y ∈ S.correctedTargetAlgebra) (hY : matrixOpNorm Y ≤ 1) :
    S.cutPolarᴴ * Y * S.cutPolar ∈ matrixSubalgebraCorner A
      (S.cutPolarᴴ * S.cutPolar) S.cutPolar_partialIsometry.1 ∧
      matrixOpNorm (S.cutPolarᴴ * Y * S.cutPolar) ≤ 1 := by
  have hi : IsStarProjection (S.cutPolarᴴᴴ * S.cutPolarᴴ) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using S.cutPolar_partialIsometry.2
  refine ⟨matrixCommutantIntertwiner_pull_corner A S.cutCommutantRepresentation S.cutPolar
    S.cutPolar_partialIsometry.1 S.cutPolar_commutant_intertwines Y hYA, ?_⟩
  change ‖S.cutPolarᴴ * Y * S.cutPolar‖ ≤ 1
  simpa only [Matrix.conjTranspose_conjTranspose] using
    (matrixPartialIsometry_sandwich_norm_le S.cutPolarᴴ hi Y).trans hY

theorem MatrixThomSpectralData.cutPolar_source_roundtrip_bound
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    rectHSNorm d (X - S.cutPolarᴴ * (S.cutPolar * X * S.cutPolarᴴ) * S.cutPolar) ≤ 2 * ε := by
  simpa only [Matrix.mul_assoc] using S.cutPolar_source_compression_loss hε X hX

theorem MatrixThomSpectralData.cutPolar_target_roundtrip_bound
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε)
    (Y : CMatrix S.cut.rank) (hY : matrixOpNorm Y ≤ 1) :
    rectHSNorm d (Y - S.cutPolar * (S.cutPolarᴴ * Y * S.cutPolar) * S.cutPolarᴴ) ≤
      2 * Real.sqrt 2 * ε := by
  simpa only [Matrix.mul_assoc] using S.cutPolar_target_compression_loss hε Y hY

end ThomGame.Analysis
