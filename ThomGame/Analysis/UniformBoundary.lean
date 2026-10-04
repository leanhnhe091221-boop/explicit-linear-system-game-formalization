module

public import ThomGame.Analysis.UniformCube

/-!
# Boundary strips for uniform cube parameters

The two strips outside [-1+epsilon,1-epsilon] have total probability
epsilon. A pointwise weighted bound separates the interior and strips.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped ENNReal

noncomputable def uniformBoundaryWeight (ε : ℝ) : ℝ → ℝ :=
  (Icc (ε - 1) (1 - ε))ᶜ.indicator (fun _ => 1)

theorem uniformBoundaryWeight_measurable (ε : ℝ) : Measurable (uniformBoundaryWeight ε) :=
  measurable_const.indicator measurableSet_Icc.compl

theorem uniformBoundaryWeight_integrable (ε : ℝ) :
    Integrable (uniformBoundaryWeight ε) uniformIntervalMeasure :=
  (integrable_const 1).indicator measurableSet_Icc.compl

theorem uniformIntervalMeasure_interior {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    uniformIntervalMeasure.real (Icc (ε - 1) (1 - ε)) = 1 - ε := by
  have hs : Icc (ε - 1) (1 - ε) ⊆ Icc (-1 : ℝ) 1 :=
    Icc_subset_Icc (by linarith) (by linarith)
  rw [Measure.real, uniformIntervalMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hs, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith)]
  norm_num
  ring

theorem uniformBoundaryWeight_integral {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ a, uniformBoundaryWeight ε a ∂uniformIntervalMeasure) = ε := by
  rw [uniformBoundaryWeight, integral_indicator_const _ measurableSet_Icc.compl,
    smul_eq_mul, mul_one, measureReal_compl measurableSet_Icc,
    uniformIntervalMeasure_interior hε hε1]
  simp

variable {μ : Type*} [Fintype μ]

theorem uniformCube_boundary_integrable (ε : ℝ) (j : μ) :
    Integrable (fun s : μ → ℝ => uniformBoundaryWeight ε (s j)) uniformCubeMeasure :=
  integrable_comp_eval (uniformBoundaryWeight_integrable ε)

theorem uniformCube_boundary_integral {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (j : μ) :
    (∫ s : μ → ℝ, uniformBoundaryWeight ε (s j) ∂uniformCubeMeasure) = ε := by
  change (∫ s : μ → ℝ, uniformBoundaryWeight ε (s j) ∂Measure.pi (fun _ => uniformIntervalMeasure)) = ε
  rw [integral_comp_eval (uniformBoundaryWeight_measurable ε).aestronglyMeasurable]
  exact uniformBoundaryWeight_integral hε hε1

theorem uniformBoundary_weighted_bound {ε s m M : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hs : |s| ≤ 1) (hm : 0 ≤ m) (hM : m ≤ M) :
    m ≤ ε⁻¹ * ((1 - s ^ 2) * m) + M * uniformBoundaryWeight ε s := by
  by_cases hi : s ∈ Icc (ε - 1) (1 - ε)
  · have habs : |s| ≤ 1 - ε := abs_le.mpr ⟨by linarith [hi.1], hi.2⟩
    have hw : ε ≤ 1 - s ^ 2 := by
      have he := sq_le_sq₀ (abs_nonneg s) (by linarith : 0 ≤ 1 - ε) |>.mpr habs
      rw [sq_abs] at he
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)]
    have he := mul_le_mul_of_nonneg_right hw hm
    have hf := (le_inv_mul_iff₀ hε).mpr he
    simpa [uniformBoundaryWeight, hi] using hf
  · have hw : 0 ≤ 1 - s ^ 2 := by
      have he := (sq_le_sq₀ (abs_nonneg s) (by norm_num : (0 : ℝ) ≤ 1)).mpr hs
      rw [sq_abs] at he
      nlinarith
    have he : 0 ≤ ε⁻¹ * ((1 - s ^ 2) * m) := mul_nonneg (inv_nonneg.mpr hε.le) (mul_nonneg hw hm)
    simpa [uniformBoundaryWeight, hi] using (hM.trans (le_add_of_nonneg_left he))

end ThomGame.Analysis
