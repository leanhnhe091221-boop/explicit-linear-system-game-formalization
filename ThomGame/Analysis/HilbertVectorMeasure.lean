module

public import ThomGame.Analysis.HilbertContinuousVectorState
public import Mathlib.Analysis.Complex.Basic

/-! Actual regular measures representing Hilbert vector states on continuous functions. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Set MeasureTheory
open scoped CompactlySupported

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertVectorMeasure (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : Measure X :=
  RealRMK.rieszMeasure (hilbertCompactVectorState π ξ)

instance hilbertVectorMeasure_finite (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    IsFiniteMeasure (hilbertVectorMeasure π ξ) :=
  inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure (hilbertCompactVectorState π ξ)))

instance hilbertVectorMeasure_regular (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    (hilbertVectorMeasure π ξ).Regular :=
  inferInstanceAs (RealRMK.rieszMeasure (hilbertCompactVectorState π ξ)).Regular

theorem hilbertVectorMeasure_integral (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (f : C(X, ℝ)) : (∫ x, f x ∂hilbertVectorMeasure π ξ) = hilbertContinuousVectorState π ξ f := by
  exact RealRMK.integral_rieszMeasure (hilbertCompactVectorState π ξ)
    (⟨f, HasCompactSupport.of_compactSpace f⟩ : C_c(X, ℝ))

theorem hilbertVectorMeasure_mass (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    (hilbertVectorMeasure π ξ).real univ = ‖ξ‖ ^ 2 := by
  have h := hilbertVectorMeasure_integral π ξ (1 : C(X, ℝ))
  rw [hilbertContinuousVectorState_one] at h
  simpa using h

theorem hilbertVectorMeasure_probability (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ : ‖ξ‖ = 1) : IsProbabilityMeasure (hilbertVectorMeasure π ξ) := by
  constructor
  have h := congrArg ENNReal.ofReal (hilbertVectorMeasure_mass π ξ)
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _), hξ, one_pow,
    ENNReal.ofReal_one] using h

def continuousNormSq (f : C(X, ℂ)) : C(X, ℝ) :=
  ⟨fun x => ‖f x‖ ^ 2, f.continuous.norm.pow 2⟩

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem continuousComplexify_normSq (f : C(X, ℂ)) :
    continuousComplexify (continuousNormSq f) = star f * f := by
  ext x
  change ((‖f x‖ ^ 2 : ℝ) : ℂ) = star (f x) * f x
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

theorem hilbertVectorMeasure_integral_normSq (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (f : C(X, ℂ)) :
    (∫ x, ‖f x‖ ^ 2 ∂hilbertVectorMeasure π ξ) = ‖π f ξ‖ ^ 2 := by
  change (∫ x, continuousNormSq f x ∂hilbertVectorMeasure π ξ) = _
  rw [hilbertVectorMeasure_integral, hilbertContinuousVectorState_apply,
    continuousComplexify_normSq, map_mul, map_star]
  change (inner ℂ ξ ((π f).adjoint (π f ξ))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

end ThomGame.Analysis
