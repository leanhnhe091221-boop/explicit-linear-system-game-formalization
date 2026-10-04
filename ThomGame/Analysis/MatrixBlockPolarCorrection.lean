module

public import ThomGame.Analysis.MatrixPolarCompletionDistance

/-!
# Correcting a partial isometry to a block commuting range

Half spectral rounding, actual blockwise rank correction, and actual
polar completion give squared distance at most four times the
original pinching defect, with the initial projection unchanged.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ]

theorem exists_matrixPartialIsometry_block_correction (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y)) :
    ∃ Z : Matrix ι κ ℂ, Zᴴ * Z = Yᴴ * Y ∧ (∀ i, Commute (Z * Zᴴ) (E i)) ∧
      rectHSNorm r (Z - Y) ^ 2 ≤ 4 * rectHSNorm r
        (Y * Yᴴ - matrixBlockPinch E (Y * Yᴴ)) ^ 2 := by
  obtain ⟨R, hR, hrank, hcomm, hdist⟩ := exists_matrixPinching_rank_corrected r E hE horth hsum
    (matrixPartialIsometry_final_projection hY)
  obtain ⟨Z, hZi, hZf, hZdist⟩ := exists_matrixPartialIsometry_close_to_projection r hY hR hrank
  exact ⟨Z, hZi, fun i => hZf.symm ▸ (hcomm i).symm, hZdist.trans hdist⟩

end ThomGame.Analysis
