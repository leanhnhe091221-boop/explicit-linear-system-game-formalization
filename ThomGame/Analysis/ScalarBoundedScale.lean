module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# Scalar bounded scales and Thom's uniform perturbation estimate

The regularizing parameter may be arbitrarily small or large.
The squared difference estimate is uniform in that parameter.
-/

@[expose] public section
namespace ThomGame.Analysis

noncomputable def boundedScaleScalar (a s : ℝ) : ℝ := a / (a + s)

theorem boundedScaleScalar_pos {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    0 < boundedScaleScalar a s := div_pos ha (add_pos_of_pos_of_nonneg ha hs)

theorem boundedScaleScalar_le_one {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    boundedScaleScalar a s ≤ 1 :=
  (div_le_one (add_pos_of_pos_of_nonneg ha hs)).mpr (by linarith)

theorem boundedScaleScalar_lt_one {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    boundedScaleScalar a s < 1 := (div_lt_one (add_pos ha hs)).mpr (by linarith)

theorem boundedScaleScalar_zero {a : ℝ} (ha : 0 < a) : boundedScaleScalar a 0 = 1 := by
  simp only [boundedScaleScalar, add_zero, div_self (ne_of_gt ha)]

theorem boundedScaleScalar_le_half {a s : ℝ} (ha : 0 < a) (has : a ≤ s) :
    boundedScaleScalar a s ≤ 1 / 2 := by
  rw [boundedScaleScalar, div_le_iff₀ (by linarith : 0 < a + s)]
  linarith

theorem boundedScaleScalar_strictAnti {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (boundedScaleScalar a) (Set.Ici 0) := by
  intro s hs t _ hst
  exact div_lt_div_of_pos_left ha (add_pos_of_pos_of_nonneg ha hs) (by linarith)

theorem boundedScaleScalar_monotone {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    boundedScaleScalar a s ≤ boundedScaleScalar b s := by
  rw [boundedScaleScalar, boundedScaleScalar,
    div_le_div_iff₀ (add_pos_of_pos_of_nonneg ha hs) (by linarith : 0 < b + s)]
  nlinarith

theorem boundedScaleScalar_continuousOn {a : ℝ} (ha : 0 < a) :
    ContinuousOn (boundedScaleScalar a) (Set.Ici 0) := by
  apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
  intro s hs
  exact ne_of_gt (add_pos_of_pos_of_nonneg ha hs)

theorem boundedScaleScalar_sub {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    boundedScaleScalar a s - boundedScaleScalar b s =
      (a / b - 1) * (b * s / ((a + s) * (b + s))) := by
  unfold boundedScaleScalar
  field_simp
  ring

theorem boundedScaleScalar_abs_sub_le_ratio {a b s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    |boundedScaleScalar a s - boundedScaleScalar b s| ≤ |a / b - 1| := by
  have hn : 0 ≤ b * s / ((a + s) * (b + s)) := by positivity
  have hu : b * s / ((a + s) * (b + s)) ≤ 1 := by
    apply (div_le_one (mul_pos (add_pos ha hs) (add_pos hb hs))).mpr
    nlinarith [mul_pos ha hb, mul_pos ha hs, sq_nonneg s]
  rw [boundedScaleScalar_sub ha hb hs, abs_mul, abs_of_nonneg hn]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (abs_nonneg (a / b - 1))

theorem boundedScaleScalar_abs_sub_sq_le_ratio {a b s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    |boundedScaleScalar a s - boundedScaleScalar b s| ^ 2 ≤ |a / b - 1| := by
  have h₁ := boundedScaleScalar_pos ha hs.le
  have h₂ := boundedScaleScalar_le_one ha hs.le
  have h₃ := boundedScaleScalar_pos hb hs.le
  have h₄ := boundedScaleScalar_le_one hb hs.le
  have hbound : |boundedScaleScalar a s - boundedScaleScalar b s| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hn := abs_nonneg (boundedScaleScalar a s - boundedScaleScalar b s)
  have hratio := boundedScaleScalar_abs_sub_le_ratio ha hb hs
  nlinarith

end ThomGame.Analysis
