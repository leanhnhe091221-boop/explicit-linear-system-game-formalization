module

public import ThomGame.Analysis.IntegerTorusCharacterEnergy
public import ThomGame.Analysis.IntegerTorusShearMeasureControl

/-! A quantitative measure criterion; constructing the spectral measure is a separate step. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerTorus

open Set MeasureTheory

theorem measure_energy_defect_bound (μ : Measure Torus) [IsProbabilityMeasure μ] (ε : ℝ)
    (h0 : μ.real {(0 : Torus)} = 0)
    (hmove : ∀ (b : Bool) (s : Set Torus), MeasurableSet s →
      μ.real s ≤ μ.real (integerShear b 1 '' s) + 2 * ε) :
    1 ≤ 36 * ε + 32 * ∫ x, coordinateEnergy x ∂μ := by
  have hl := outside_mass_lower_bound μ ε h0 (cone_measure_errors_of_unit_shears μ ε hmove)
  have hu := outside_mass_le_energy μ
  linarith

theorem measure_quadratic_defect_bound (μ : Measure Torus) [IsProbabilityMeasure μ] (ε : ℝ)
    (h0 : μ.real {(0 : Torus)} = 0)
    (hmove : ∀ (b : Bool) (s : Set Torus), MeasurableSet s →
      μ.real s ≤ μ.real (integerShear b 1 '' s) + 2 * ε)
    (henergy : (∫ x, coordinateEnergy x ∂μ) ≤ 2 * ε ^ 2) :
    1 ≤ 36 * ε + 64 * ε ^ 2 := by
  have h := measure_energy_defect_bound μ ε h0 hmove
  linarith

theorem no_almost_invariant_measure (μ : Measure Torus) [IsProbabilityMeasure μ] (ε : ℝ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 100)
    (h0 : μ.real {(0 : Torus)} = 0)
    (hmove : ∀ (b : Bool) (s : Set Torus), MeasurableSet s →
      μ.real s ≤ μ.real (integerShear b 1 '' s) + 2 * ε)
    (henergy : (∫ x, coordinateEnergy x ∂μ) ≤ 2 * ε ^ 2) : False := by
  have h := measure_quadratic_defect_bound μ ε h0 hmove henergy
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hεsmall)]

end ThomGame.Analysis.IntegerTorus
