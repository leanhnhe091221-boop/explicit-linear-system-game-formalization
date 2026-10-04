module

public import ThomGame.Analysis.HilbertVectorMeasurePerturbation

/-! Unitary covariance of continuous functional calculus gives exact pushforward identities. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Set MeasureTheory
open scoped CompactlySupported

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hilbertVectorMeasure_map_of_covariant
    (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : H ≃ₗᵢ[ℂ] H) (e : X ≃ₜ X)
    (hcov : ∀ f : C(X, ℂ), π (f.comp ⟨e, e.continuous⟩) = S.conjStarAlgEquiv (π f))
    (ξ : H) : (hilbertVectorMeasure π (S ξ)).map e = hilbertVectorMeasure π ξ := by
  let := Measure.Regular.map (μ := hilbertVectorMeasure π (S ξ)) e
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂(hilbertVectorMeasure π (S ξ)).map e) =
    ∫ x, f.toContinuousMap x ∂hilbertVectorMeasure π ξ
  rw [integral_map e.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  change (∫ x, (f.toContinuousMap.comp ⟨e, e.continuous⟩) x ∂hilbertVectorMeasure π (S ξ)) =
    ∫ x, f.toContinuousMap x ∂hilbertVectorMeasure π ξ
  rw [hilbertVectorMeasure_integral, hilbertVectorMeasure_integral,
    hilbertContinuousVectorState_apply, hilbertContinuousVectorState_apply]
  change (inner ℂ (S ξ) (π ((continuousComplexify f.toContinuousMap).comp
    ⟨e, e.continuous⟩) (S ξ))).re = _
  rw [hcov]
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, S.symm_apply_apply, S.inner_map_map]

theorem hilbertVectorMeasure_image_of_covariant
    (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : H ≃ₗᵢ[ℂ] H) (e : X ≃ₜ X)
    (hcov : ∀ f : C(X, ℂ), π (f.comp ⟨e, e.continuous⟩) = S.conjStarAlgEquiv (π f))
    (ξ : H) (s : Set X) (hs : MeasurableSet s) :
    (hilbertVectorMeasure π (S ξ)).real s = (hilbertVectorMeasure π ξ).real (e '' s) := by
  have h := congrArg (fun μ : Measure X => μ (e '' s)) (hilbertVectorMeasure_map_of_covariant π S e hcov ξ)
  rw [Measure.map_apply e.continuous.measurable (e.measurableEmbedding.measurableSet_image' hs),
    Set.preimage_image_eq _ e.injective] at h
  exact congrArg ENNReal.toReal h

theorem hilbertVectorMeasure_shear_bound_of_covariant
    (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : H ≃ₗᵢ[ℂ] H) (e : X ≃ₜ X)
    (hcov : ∀ f : C(X, ℂ), π (f.comp ⟨e, e.continuous⟩) = S.conjStarAlgEquiv (π f))
    (ξ : H) (hξ : ‖ξ‖ = 1) (s : Set X) (hs : MeasurableSet s) :
    (hilbertVectorMeasure π ξ).real s ≤
      (hilbertVectorMeasure π ξ).real (e '' s) + 2 * ‖S ξ - ξ‖ := by
  have h := hilbertVectorMeasure_unit_borel_sub_abs_le π ξ (S ξ) hξ
    ((S.norm_map ξ).trans hξ) s hs
  rw [hilbertVectorMeasure_image_of_covariant π S e hcov ξ s hs, norm_sub_rev ξ (S ξ)] at h
  have hle := (le_abs_self _).trans h
  linarith

end ThomGame.Analysis
