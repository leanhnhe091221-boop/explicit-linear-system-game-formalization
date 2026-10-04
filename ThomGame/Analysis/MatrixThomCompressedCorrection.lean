module

public import ThomGame.Analysis.MatrixThomCompressedSupports

/-!
# Relative spectral-range correction from the original near inclusion

All objects below come from the actual trace expectation and spectral cut.
This is the finite-dimensional construction through (3.2), with support
bounds; multiplicity and Hausdorff comparisons are separate further steps.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem exists_matrixThomCompressedCorrection (A B D : StarSubalgebra ℂ (CMatrix d))
    (hDA : D ≤ A) (hDB : D ≤ B) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hBA : MatrixNearInclusion B A ε) :
    ∃ S : MatrixThomSpectralData A B D ε,
      0 < S.cut.rank ∧
      |(S.cut.rank : ℝ) - d| ≤ 2 * ε ^ 2 * d ∧
      S.correctedSourceAlgebra ≤ S.correctedTargetAlgebra ∧
      IsStarProjection (S.cutPolarᴴ * S.cutPolar) ∧
      IsStarProjection (S.cutPolar * S.cutPolarᴴ) ∧
      S.cutPolar * S.cutPolarᴴ ∈ S.correctedTargetAlgebra ∧
      ((1 - S.cutPolarᴴ * S.cutPolar).rank : ℝ) ≤ 2 * ε ^ 2 * d ∧
      ((1 - S.cutPolar * S.cutPolarᴴ).rank : ℝ) ≤ 4 * ε ^ 2 * d ∧
      rectHSNorm d (S.cutFrame * S.cutPolar - S.isometry) ^ 2 ≤ 4 * ε ^ 2 ∧
      (∀ X : D, S.cutSourceRepresentation ⟨X, hDB X.property⟩ * S.cutPolar =
        S.cutPolar * (X : CMatrix d)) ∧
      (∀ X : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)),
        S.cutCommutantRepresentation X * S.cutPolar = S.cutPolar * (X : CMatrix d)) ∧
      ∀ X : B, matrixOpNorm (X : CMatrix d) ≤ 1 →
        rectHSNorm d (S.cutSourceRepresentation X * S.cutPolar - S.cutPolar * (X : CMatrix d)) ≤
          (4 + Real.sqrt 2) * ε := by
  obtain ⟨S⟩ := exists_matrixThomSpectralData A B D hDA hDB hε0 hBA
  exact ⟨S, S.cut_rank_pos hε0 hε, S.dimension_error_absolute,
    S.correctedSourceAlgebra_le_target, S.cutPolar_partialIsometry.1, S.cutPolar_partialIsometry.2,
    S.cutPolar_final_mem_target, S.cutPolar_initial_complement_rank, S.cutPolar_final_complement_rank,
    S.cutPolar_distance, S.cutPolar_common_intertwines hDB, S.cutPolar_commutant_intertwines,
    S.cutPolar_intertwining_bound hε0 hBA⟩

end ThomGame.Analysis
