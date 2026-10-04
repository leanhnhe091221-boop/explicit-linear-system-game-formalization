module

public import ThomGame.Analysis.HilbertVectorMeasure
public import ThomGame.Analysis.HilbertVectorStatePerturbation
public import ThomGame.Analysis.RegularMeasureTestBounds
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! Borel-set perturbation of genuine vector measures, without a projection-valued measure axiom. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Set MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem continuousComplexify_norm_le_one (f : C(X, ℝ)) (hf : ∀ x, f x ∈ Icc 0 1) :
    ‖continuousComplexify f‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro x
  rw [continuousComplexify_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf x).1]
  exact (hf x).2

theorem hilbertVectorMeasure_borel_le (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ η : H) (s : Set X) (hs : MeasurableSet s) :
    (hilbertVectorMeasure π ξ).real s ≤ (hilbertVectorMeasure π η).real s +
      (‖ξ‖ + ‖η‖) * ‖ξ - η‖ := by
  apply measureReal_borel_le_of_continuous_integral_le _ _ ((‖ξ‖ + ‖η‖) * ‖ξ - η‖)
    (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) _ s hs
  intro f hf
  have hπ : ‖π (continuousComplexify f)‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le π _).trans (continuousComplexify_norm_le_one f hf)
  have hb := hilbertVectorState_re_sub_abs_le (π (continuousComplexify f)) ξ η
  have hb' : |(inner ℂ ξ (π (continuousComplexify f) ξ)).re -
      (inner ℂ η (π (continuousComplexify f) η)).re| ≤ (‖ξ‖ + ‖η‖) * ‖ξ - η‖ := by
    calc
      _ ≤ ‖π (continuousComplexify f)‖ * (‖ξ‖ + ‖η‖) * ‖ξ - η‖ := hb
      _ ≤ 1 * (‖ξ‖ + ‖η‖) * ‖ξ - η‖ := by gcongr
      _ = _ := by rw [one_mul]
  rw [hilbertVectorMeasure_integral, hilbertVectorMeasure_integral,
    hilbertContinuousVectorState_apply, hilbertContinuousVectorState_apply]
  have hle := le_trans (le_abs_self _) hb'
  linarith

theorem hilbertVectorMeasure_borel_sub_abs_le (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ η : H) (s : Set X) (hs : MeasurableSet s) :
    |(hilbertVectorMeasure π ξ).real s - (hilbertVectorMeasure π η).real s| ≤
      (‖ξ‖ + ‖η‖) * ‖ξ - η‖ := by
  have h₁ := hilbertVectorMeasure_borel_le π ξ η s hs
  have h₂ := hilbertVectorMeasure_borel_le π η ξ s hs
  rw [norm_sub_rev η ξ, add_comm ‖η‖ ‖ξ‖] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem hilbertVectorMeasure_unit_borel_sub_abs_le (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (s : Set X) (hs : MeasurableSet s) :
    |(hilbertVectorMeasure π ξ).real s - (hilbertVectorMeasure π η).real s| ≤ 2 * ‖ξ - η‖ := by
  simpa only [hξ, hη, show (1 : ℝ) + 1 = 2 by norm_num]
    using hilbertVectorMeasure_borel_sub_abs_le π ξ η s hs

end ThomGame.Analysis
