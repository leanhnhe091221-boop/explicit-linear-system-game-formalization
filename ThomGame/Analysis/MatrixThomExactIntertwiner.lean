module

public import ThomGame.Analysis.MatrixThomCompressedCorrection
public import ThomGame.Analysis.MatrixRectangularAveragingSupport
public import ThomGame.Analysis.MatrixIsometryRankDistance

/-!
# The exact B-intertwiner in Thom Proposition 3.1

Average the actual cut isometry under the unitary action. The result
remains in the spectral range, is within 2 sqrt(2) epsilon of V, and
has rank at least d - 8 epsilon^2 d. The same matrix is then compressed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}

theorem MatrixThomSpectralData.cut_isometry_distance
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) :
    rectHSNorm d (S.cut * S.isometry - S.isometry) ≤ Real.sqrt 2 * ε := by
  have he : S.isometry - S.cut * S.isometry = (1 - S.cut) * S.isometry := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  rw [rectHSNorm_sub_comm, he]
  apply (sq_le_sq₀ (rectHSNorm_nonneg d _) (mul_nonneg (Real.sqrt_nonneg _) hε)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact S.deleted_mass_le

theorem MatrixThomSpectralData.cut_unitary_orbit_distance
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε)
    (U : unitary B) :
    rectHSNorm d (matrixRectangularUnitaryAction (S.sourceRep.comp B.subtype) U
      (S.cut * S.isometry) - S.isometry) ≤ 2 * Real.sqrt 2 * ε := by
  have hn : matrixOpNorm (U.val : CMatrix d) ≤ 1 :=
    le_of_eq (CStarRing.norm_coe_unitary (matrixSubalgebraUnitary B U))
  have hi := matrixStinespring_expectation_nearInclusion_bound A B hε hBA
    S.sourceRep S.isometry S.isometry_gram S.expectation U.val U.val.property hn
  have hd := matrixRectangularUnitaryAction_displacement_le d (S.sourceRep.comp B.subtype) U
    (S.cut * S.isometry) S.isometry
  have hc := S.cut_isometry_distance hε
  change rectHSNorm d (matrixRectangularUnitaryAction (S.sourceRep.comp B.subtype) U
    (S.cut * S.isometry) - S.isometry) ≤
      rectHSNorm d (S.cut * S.isometry - S.isometry) +
        rectHSNorm d (S.sourceRep (U.val : CMatrix d) * S.isometry - S.isometry * (U.val : CMatrix d)) at hd
  linarith

theorem MatrixThomSpectralData.exists_exact_intertwiner_in_dilation
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    ∃ T : Matrix (Fin (d * (d * d))) (Fin d) ℂ,
      T ∈ closedConvexHull ℝ (Set.range (fun U : unitary B =>
        matrixRectangularUnitaryAction (S.sourceRep.comp B.subtype) U (S.cut * S.isometry))) ∧
      S.cut * T = T ∧
      (∀ b : B, S.sourceRep (b : CMatrix d) * T = T * (b : CMatrix d)) ∧
      rectHSNorm d (T - S.isometry) ≤ 2 * Real.sqrt 2 * ε ∧
      (d : ℝ) - 8 * ε ^ 2 * d ≤ T.rank := by
  obtain ⟨T, hT, hB, hd⟩ := exists_matrixRectangular_average d (S.sourceRep.comp B.subtype)
    (S.cut * S.isometry) S.isometry (2 * Real.sqrt 2 * ε) (S.cut_unitary_orbit_distance hε hBA)
  have hQT : S.cut * T = T := by
    apply matrix_closedConvexHull_preserves_range S.cut _ _ T hT
    rintro X ⟨U, rfl⟩
    apply matrixRectangularUnitaryAction_preserves_range
    · rw [← Matrix.mul_assoc, S.cut_projection.isIdempotentElem.eq]
    · intro b
      exact S.cut_commutes_source b b.property
  have hs : rectHSNorm d (T - S.isometry) ^ 2 ≤ 8 * ε ^ 2 := by
    have hsq := (sq_le_sq₀ (rectHSNorm_nonneg d _) (by positivity : 0 ≤ 2 * Real.sqrt 2 * ε)).mpr hd
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq
    nlinarith
  exact ⟨T, hT, hQT, hB, hd, matrixIsometry_rank_lower_of_distance S.isometry T S.isometry_gram hs⟩

theorem MatrixThomSpectralData.exists_exact_intertwiner
    (S : MatrixThomSpectralData A B D ε) (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    ∃ T : Matrix (Fin S.cut.rank) (Fin d) ℂ,
      (∀ b : B, S.cutSourceRepresentation b * T = T * (b : CMatrix d)) ∧
      rectHSNorm d (S.cutFrame * T - S.isometry) ≤ 2 * Real.sqrt 2 * ε ∧
      (d : ℝ) - 8 * ε ^ 2 * d ≤ T.rank := by
  obtain ⟨T, _, hQT, hB, hd, hr⟩ := S.exists_exact_intertwiner_in_dilation hε hBA
  have hFT : (S.cutFrame * S.cutFrameᴴ) * T = T := by rwa [S.cutFrame_final]
  refine ⟨S.cutFrameᴴ * T, ?_, ?_, ?_⟩
  · intro b
    exact matrixFrame_supported_exact_intertwining S.cutFrame T hFT (S.sourceRep b) b (hB b)
  · rwa [matrixFrame_supported_lift S.cutFrame T hFT]
  · rwa [matrixFrame_supported_rank S.cutFrame T hFT]

end ThomGame.Analysis
