module

public import ThomGame.Analysis.IntegerTorusShearBands

/-! A quantitative packing obstruction for almost shear-invariant torus measures. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

open Set MeasureTheory
open scoped BigOperators

theorem coneImage_mass_sum_le (μ : Measure Torus) [IsFiniteMeasure μ] :
    (∑ i : Bool × Bool, μ.real (shearMap i '' cone i.1)) ≤ μ.real univ := by
  rw [← measureReal_iUnion_fintype coneImages_pairwise_disjoint coneImage_measurable]
  exact measureReal_mono (Set.subset_univ _)

theorem cone_masses_of_origin_null (μ : Measure Torus) [IsFiniteMeasure μ]
    (h0 : μ.real {(0 : Torus)} = 0) : μ.real (cone false) + μ.real (cone true) = μ.real smallSquare := by
  rw [← measureReal_union cones_disjoint (cone_measurable true), cones_union,
    measureReal_sdiff_null h0]

theorem packing_bound (μ : Measure Torus) [IsProbabilityMeasure μ] (ε : ℝ)
    (h0 : μ.real {(0 : Torus)} = 0)
    (hmove : ∀ i : Bool × Bool, μ.real (cone i.1) ≤
      μ.real (shearMap i '' cone i.1) + 2 * ((shift i.2 : ℤ) : ℝ) * ε) :
    2 * μ.real smallSquare ≤ 1 + 36 * ε := by
  have hsum := coneImage_mass_sum_le μ
  have hcones := cone_masses_of_origin_null μ h0
  have h₁ := hmove (false, false)
  have h₂ := hmove (false, true)
  have h₃ := hmove (true, false)
  have h₄ := hmove (true, true)
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, probReal_univ] at hsum
  norm_num only [shift, Bool.false_eq_true, ↓reduceIte, Int.cast_ofNat] at h₁ h₂ h₃ h₄
  linarith

theorem outside_mass_lower_bound (μ : Measure Torus) [IsProbabilityMeasure μ] (ε : ℝ)
    (h0 : μ.real {(0 : Torus)} = 0)
    (hmove : ∀ i : Bool × Bool, μ.real (cone i.1) ≤
      μ.real (shearMap i '' cone i.1) + 2 * ((shift i.2 : ℤ) : ℝ) * ε) :
    (1 - 36 * ε) / 2 ≤ μ.real smallSquareᶜ := by
  have h := packing_bound μ ε h0 hmove
  have hc := measureReal_add_measureReal_compl (μ := μ) smallSquare_measurable
  rw [probReal_univ] at hc
  linarith

end ThomGame.Analysis.IntegerTorus
