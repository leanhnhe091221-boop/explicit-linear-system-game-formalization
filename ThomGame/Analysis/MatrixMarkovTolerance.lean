module

public import ThomGame.Analysis.MatrixMarkovUniformDefect

/-!
# Positive vanishing tolerances for projection improvement

The uniform defect supplies the concrete positive tolerance used by
ALT's projection-improvement step. It dominates the defect and the
reciprocal diagonal depth, and its square controls the defect with
constant 64. The reciprocal depth makes it positive even at index zero.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) {h : Nat} [NeZero h]
  (U : (n : Nat) → Fin h → UnitaryMatrix (dims n)) (hd : ∀ n, 0 < dims n) (κ : ℝ)

noncomputable def matrixMarkovTolerance (n : Nat) : ℝ :=
  8 * Real.sqrt (matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n) +
    (matrixMarkovDiagonalPower dims U hd κ n : ℝ)⁻¹ + (n : ℝ)⁻¹

theorem matrixMarkovTolerance_pos (n : Nat) : 0 < matrixMarkovTolerance dims U hd κ n := by
  unfold matrixMarkovTolerance
  exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (inv_pos.mpr (Nat.cast_pos.mpr (matrixMarkovDiagonalPower_pos dims U hd κ n))))
    (inv_nonneg.mpr (Nat.cast_nonneg n))

theorem matrixMarkovTolerance_sqrt_bound (n : Nat) :
    8 * Real.sqrt (matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n) ≤
      matrixMarkovTolerance dims U hd κ n := by
  unfold matrixMarkovTolerance
  have he : 0 ≤ (n : ℝ)⁻¹ := by positivity
  linarith [inv_nonneg.mpr (Nat.cast_nonneg (matrixMarkovDiagonalPower dims U hd κ n) : (0 : ℝ) ≤ _)]

theorem matrixMarkovTolerance_depth_bound (n : Nat) :
    (matrixMarkovDiagonalPower dims U hd κ n : ℝ)⁻¹ ≤ matrixMarkovTolerance dims U hd κ n := by
  unfold matrixMarkovTolerance
  have he : 0 ≤ (n : ℝ)⁻¹ := by positivity
  linarith [Real.sqrt_nonneg (matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n)]

theorem matrixMarkovTolerance_index_bound (n : Nat) :
    (n : ℝ)⁻¹ ≤ matrixMarkovTolerance dims U hd κ n := by
  unfold matrixMarkovTolerance
  have h₁ := Real.sqrt_nonneg (matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n)
  have h₂ := inv_nonneg.mpr (Nat.cast_nonneg (matrixMarkovDiagonalPower dims U hd κ n) : (0 : ℝ) ≤ _)
  linarith

theorem matrixMarkovTolerance_defect_sq_bound (n : Nat) :
    matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n ≤
      matrixMarkovTolerance dims U hd κ n ^ 2 / 64 := by
  have he := matrixMarkovTolerance_sqrt_bound dims U hd κ n
  have hb := matrixUniformMarkovDefect_nonneg dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n
  have hs := Real.sq_sqrt hb
  have hsq := (sq_le_sq₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (Real.sqrt_nonneg _))
    (matrixMarkovTolerance_pos dims U hd κ n).le).mpr he
  nlinarith

theorem matrixMarkovTolerance_defect_bound (n : Nat) :
    matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n ≤
      matrixMarkovTolerance dims U hd κ n := by
  have he := matrixMarkovTolerance_sqrt_bound dims U hd κ n
  have hb := matrixUniformMarkovDefect_nonneg dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n
  have htwo := matrixUniformMarkovDefect_le_two dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n
  have hs := Real.sq_sqrt hb
  have hroot : Real.sqrt (matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  nlinarith [Real.sqrt_nonneg (matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n)]

variable (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
  (hgap : MatrixMarkovSpectralGap dims U hd L κ)

include hL hgap in
theorem matrixMarkovTolerance_tendsto_zero :
    Tendsto (matrixMarkovTolerance dims U hd κ) (L : Filter Nat) (𝓝 0) := by
  have hb := Real.continuous_sqrt.continuousAt.tendsto.comp
    (matrixUniformMarkovDefect_diagonal_tendsto_zero dims U hd L hL κ hgap)
  rw [Real.sqrt_zero] at hb
  have hd' : Tendsto (fun n => (matrixMarkovDiagonalPower dims U hd κ n : ℝ)⁻¹) (L : Filter Nat) (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat.comp (matrixMarkovDiagonalPower_tendsto dims U hd L hL κ hgap)
  have hn : Tendsto (fun n : Nat => (n : ℝ)⁻¹) (L : Filter Nat) (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat.mono_left hL
  change Tendsto (fun n =>
    8 * Real.sqrt (matrixUniformMarkovDefect dims U hd κ (matrixMarkovDiagonalPower dims U hd κ) n) +
      (matrixMarkovDiagonalPower dims U hd κ n : ℝ)⁻¹ + (n : ℝ)⁻¹) (L : Filter Nat) (𝓝 0)
  simpa only [Function.comp_def, mul_zero, add_zero] using ((hb.const_mul 8).add hd').add hn

end ThomGame.Analysis
