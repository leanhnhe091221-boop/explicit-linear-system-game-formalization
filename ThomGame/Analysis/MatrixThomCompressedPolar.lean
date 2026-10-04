module

public import ThomGame.Analysis.MatrixThomCompressedAlgebras
public import ThomGame.Analysis.MatrixThomIntertwiningCorrection
public import ThomGame.Analysis.MatrixFrameRectangularTransport

/-!
# Thom's polar correction on the actual spectral range

The compressed polar matrix has exactly the same rank and initial support.
It satisfies (3.1) and the uniform bound (3.2) in its actual codomain.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

noncomputable def MatrixThomSpectralData.cutPolar (S : MatrixThomSpectralData A B D ε) :
    Matrix (Fin S.cut.rank) (Fin d) ℂ :=
  S.cutFrameᴴ * matrixRectPolar (S.cut * S.isometry)

theorem MatrixThomSpectralData.cutPolar_lift (S : MatrixThomSpectralData A B D ε) :
    S.cutFrame * S.cutPolar = matrixRectPolar (S.cut * S.isometry) := by
  apply matrixFrame_supported_lift
  rw [S.cutFrame_final]
  exact matrixCutIsometry_polar_support S.isometry S.cut_projection

theorem MatrixThomSpectralData.cutPolar_gram (S : MatrixThomSpectralData A B D ε) :
    S.cutPolarᴴ * S.cutPolar =
      (matrixRectPolar (S.cut * S.isometry))ᴴ * matrixRectPolar (S.cut * S.isometry) := by
  apply matrixFrame_supported_gram
  rw [S.cutFrame_final]
  exact matrixCutIsometry_polar_support S.isometry S.cut_projection

theorem MatrixThomSpectralData.cutPolar_partialIsometry (S : MatrixThomSpectralData A B D ε) :
    IsStarProjection (S.cutPolarᴴ * S.cutPolar) ∧ IsStarProjection (S.cutPolar * S.cutPolarᴴ) := by
  have hi : IsStarProjection (S.cutPolarᴴ * S.cutPolar) := by
    rw [S.cutPolar_gram]
    exact matrixRectPolar_initial_projection _
  exact ⟨hi, matrixPartialIsometry_final_projection hi⟩

theorem MatrixThomSpectralData.cutPolar_rank (S : MatrixThomSpectralData A B D ε) :
    S.cutPolar.rank = (matrixRectPolar (S.cut * S.isometry)).rank := by
  apply matrixFrame_supported_rank
  rw [S.cutFrame_final]
  exact matrixCutIsometry_polar_support S.isometry S.cut_projection

theorem MatrixThomSpectralData.cutPolar_rank_lower (S : MatrixThomSpectralData A B D ε) :
    (d : ℝ) - 2 * ε ^ 2 * d ≤ S.cutPolar.rank := by
  rw [S.cutPolar_rank]
  exact S.polar_rank_lower

theorem MatrixThomSpectralData.cutPolar_distance (S : MatrixThomSpectralData A B D ε) :
    rectHSNorm d (S.cutFrame * S.cutPolar - S.isometry) ^ 2 ≤ 4 * ε ^ 2 := by
  rw [S.cutPolar_lift]
  have he := matrixCutIsometry_polar_distance_le d S.isometry S.isometry_gram S.cut_projection
  linarith [S.deleted_mass_le]

theorem MatrixThomSpectralData.cutPolar_common_intertwines
    (S : MatrixThomSpectralData A B D ε) (hDB : D ≤ B) (X : D) :
    S.cutSourceRepresentation ⟨X, hDB X.property⟩ * S.cutPolar = S.cutPolar * (X : CMatrix d) := by
  apply matrixFrame_supported_exact_intertwining
  · rw [S.cutFrame_final]
    exact matrixCutIsometry_polar_support S.isometry S.cut_projection
  · obtain ⟨W, hW, _, _, _, _, _, hD, _⟩ := S.polar_correction
    simpa only [hW] using hD X X.property

theorem MatrixThomSpectralData.cutPolar_commutant_intertwines
    (S : MatrixThomSpectralData A B D ε) (X : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) :
    S.cutCommutantRepresentation X * S.cutPolar = S.cutPolar * (X : CMatrix d) := by
  apply matrixFrame_supported_exact_intertwining
  · rw [S.cutFrame_final]
    exact matrixCutIsometry_polar_support S.isometry S.cut_projection
  · obtain ⟨W, hW, _, _, _, _, _, _, hC⟩ := S.polar_correction
    simpa only [hW] using hC X X.property

theorem MatrixThomSpectralData.cutPolar_intertwining_error
    (S : MatrixThomSpectralData A B D ε) (X : B) :
    rectHSNorm d (S.cutSourceRepresentation X * S.cutPolar - S.cutPolar * (X : CMatrix d)) =
      rectHSNorm d (S.sourceRep X * matrixRectPolar (S.cut * S.isometry) -
        matrixRectPolar (S.cut * S.isometry) * (X : CMatrix d)) := by
  apply matrixFrame_supported_intertwining_norm d S.cutFrame_initial
  · rw [S.cutFrame_final]
    exact matrixCutIsometry_polar_support S.isometry S.cut_projection
  · rw [S.cutFrame_final]
    exact S.cut_commutes_source X X.property

theorem MatrixThomSpectralData.cutPolar_intertwining_bound
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε)
    (X : B) (hX : matrixOpNorm (X : CMatrix d) ≤ 1) :
    rectHSNorm d (S.cutSourceRepresentation X * S.cutPolar - S.cutPolar * (X : CMatrix d)) ≤
      (4 + Real.sqrt 2) * ε := by
  rw [S.cutPolar_intertwining_error]
  exact S.polar_intertwining_bound hε hBA X X.property hX

end ThomGame.Analysis
