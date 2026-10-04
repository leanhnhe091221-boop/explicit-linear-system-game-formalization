module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Scalar constants from the explicit game gap calculation

These are arithmetic facts about the specified positive numbers. In particular,
this module does not assert that either number bounds a game value or a relator
defect: those assertions require the separate quantitative analytic estimates.
The nested powers are retained symbolically throughout the proofs.
-/

@[expose] public section
namespace ThomGame.Construction

/-- The relator tolerance specified in the explicit gap calculation. -/
noncomputable def paperExplicitDefect : ℝ := (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ)

/-- The final positive rational lower bound proposed in the gap calculation. -/
noncomputable def paperExplicitGap : ℝ := (1 / 2 : ℝ) ^ (2 ^ 50003 : ℕ)

theorem paperExplicitDefect_pos : 0 < paperExplicitDefect :=
  pow_pos (by norm_num) _

theorem paperExplicitGap_pos : 0 < paperExplicitGap :=
  pow_pos (by norm_num) _

theorem paperExplicitDefect_le_one : paperExplicitDefect ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem paperExplicitGap_le_one : paperExplicitGap ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem paperExplicitGap_eq_defect_pow_eight :
    paperExplicitGap = paperExplicitDefect ^ 8 := by
  unfold paperExplicitGap paperExplicitDefect
  rw [show (50003 : ℕ) = 50000 + 3 from rfl, pow_add]
  rw [show (2 : ℕ) ^ 3 = 8 from rfl]
  exact pow_mul _ _ _

theorem paperExplicitDefect_le_reduction_reciprocal :
    paperExplicitDefect ≤ 1 / 2755200 := by
  have hexponent : (22 : ℕ) ≤ 2 ^ 50000 :=
    (show (22 : ℕ) ≤ 2 ^ 5 by norm_num).trans
      (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : (5 : ℕ) ≤ 50000))
  have hpower : paperExplicitDefect ≤ (1 / 2 : ℝ) ^ 22 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexponent
  exact hpower.trans (by norm_num)

/-- The final scalar comparison in the game-to-double reduction. -/
theorem paperExplicitGap_le_reduction_bound :
    paperExplicitGap ≤ (paperExplicitDefect / 2755200) ^ 4 := by
  have hbase : paperExplicitDefect ^ 2 ≤ paperExplicitDefect / 2755200 := by
    calc
      paperExplicitDefect ^ 2 = paperExplicitDefect * paperExplicitDefect := pow_two _
      _ ≤ paperExplicitDefect * (1 / 2755200) :=
        mul_le_mul_of_nonneg_left paperExplicitDefect_le_reduction_reciprocal
          paperExplicitDefect_pos.le
      _ = paperExplicitDefect / 2755200 := by ring
  rw [paperExplicitGap_eq_defect_pow_eight,
    show (8 : ℕ) = 2 * 4 from rfl, pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) hbase _

theorem paperExplicitGap_le_incidence_reciprocal :
    paperExplicitGap ≤ 1 / 4251456 := by
  have hexponent : (23 : ℕ) ≤ 2 ^ 50003 :=
    (show (23 : ℕ) ≤ 2 ^ 5 by norm_num).trans
      (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : (5 : ℕ) ≤ 50003))
  have hpower : paperExplicitGap ≤ (1 / 2 : ℝ) ^ 23 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexponent
  exact hpower.trans (by norm_num)

end ThomGame.Construction
